#!/usr/bin/env python
import binascii
import random
import sys
from enum import Enum
import math

import mathlib


class OperationType(Enum):
    MULTIPLICATION = 1
    ADDITION = 2


class AsmuthBloom(object):
    def __init__(self, threshold, num_of_op=None, s=None):
        # threshold is (shares to recombine, all shares)
        self.threshold = threshold  # (t, n)
        self.s = s
        self.num_of_op = num_of_op  # (number of additions, number of multiplications)
        self.shares = None  # [(a1, m1), (a2, m2),...,(an,mn)]
        self._m_0 = 0
        self._y = 0
        self._secret = 0

    def _find_group_for_secret(self, k):
        """Generate group Z/Zm_0 for secret, where m_0 is prime and m_0 > secret."""
        while True:
            m_0 = mathlib.get_prime(k)
            if mathlib.primality_test(m_0):
                return m_0

    def _check_base_condition(self, d):
        """Check if d satisfy the Asmuth-Bloom base condition.

        """
        recomb_count, all_count = self.threshold

        left = 1
        for i in range(1, recomb_count + 1):
            left = left * d[i]

        right = d[0]
        for i in range(0, recomb_count - 1):
            right = right * d[all_count - i]
        return left > right

    def get_m0(self):
        if not self.has_generated_shares():
            print("has not generated shares")
            return
        return self._m_0

    def get_coprimes(self):
        if not self.has_generated_shares():
            print("has not generated shares")
            return
        return [x for _, x in self.shares]

    def _get_pairwise_primes(self, k, h):
        """Generate d = n+1 primes for Asmuth-Bloom threshold scheme and secret
        such that d_0 is k-bit prime and d_1 is h-bit prime.
        (d_1...d_n should be pairwise coprimes)
        """
        if h < k:
            raise Exception('Not enought bits for m_1')
        _, all_count = self.threshold
        # p is picked randomly simple number
        p = self._find_group_for_secret(k)
        while True:
            d = [p]
            # all_count consecutive primes starting from h-bit prime
            for prime in mathlib.get_consecutive_primes(all_count, h):
                d.append(prime)
            if self._check_base_condition(d):
                return d

    def _prod(self, coprimes):
        """Calculate M=m_1*m_2*...*m_t."""
        M = 1
        t, _ = self.threshold
        for i in range(0, t):
            M = M * coprimes[i]
        return M

    def _prod_ms(self, coprimes, s):
        """Calculate Ms=m_n*m_n-1*...*m_n-s+2"""
        Ms = 1
        _, n = self.threshold
        for i in range(1, s):
            Ms = Ms * coprimes[n - i]
        return Ms

    def _prod_mn(self, coprimes):
        """Calculate Mn=m_1*m_2*...*m_n"""
        Mn = 1
        _, n = self.threshold
        for i in range(0, n):
            Mn = Mn * coprimes[i]
        return Mn

    def _get_modulo_base(self, secret, coprimes):
        """Calculate M' = secret + some_number * taken_prime
        that should be less that coprimes prod.
        Modulos from this number will be used as shares.
        """
        self.Mr = self._prod(coprimes)
        self.Mn = self._prod_mn(coprimes)
        if self.num_of_op is None:
            self.Ms = self._prod_ms(coprimes, s)
            self.pms = coprimes[0] * self.Ms

        else:
            num_of_additions, num_of_multiplications = self.num_of_op
            prev_ms = self._prod_ms(coprimes, 0)
            prev_pms = coprimes[0] * prev_ms
            for s_index in range(1, self.threshold[1]):
                ms = self._prod_ms(coprimes, s_index)
                pms = coprimes[0] * ms
                if (num_of_additions + 1) * (pms ** (num_of_multiplications + 1)) > self.Mr:
                    self.s = s_index - 1
                    break
                prev_ms = ms
                prev_pms = pms
            self.Ms = prev_ms
            self.pms = prev_pms
        self.M = self.pms
        while True:
            A = mathlib.get_random_range(1, (self.M - secret) // self._m_0)
            y = secret + A * self._m_0
            if 0 <= y <= self.M:  # originally 0 <= y < prod
                break
        return y

    # k is m_0_bits and h is m_1_bits
    def generate_shares(self, secret, k, h):
        self._secret = secret
        if mathlib.bit_len(secret) > k:
            raise ValueError('Secret is too long')

        m = self._get_pairwise_primes(k, h)
        self._m_0 = m.pop(0)

        self._y = self._get_modulo_base(secret, m)
        print(f"Got s: {ab.s}")
        if self.s == 0:
            print(
                "calculation of additions and multiplications are not guaranteed and might fail, please choose different amount of operations...")
            #sys.exit(1)
        self.shares = []
        for m_i in m:
            self.shares.append((self._y % m_i, m_i))
        # shares item format: (ki, di) ki - mods, di - coprimes
        return self.shares

    def generate_shares_with_coprimes(self, secret, m_0, coprimes):
        self._secret = secret
        self._m_0 = m_0

        self._y = self._get_modulo_base(secret, coprimes)

        self.shares = []
        for m_i in coprimes:
            self.shares.append((self._y % m_i, m_i))
        # shares item format: (ki, di) ki - mods, di - coprimes
        return self.shares

    def combine_shares(self, shares):
        y_i = [x for x, _ in self.shares]  # remainders
        m_i = [x for _, x in self.shares]  # coprimes
        y = mathlib.garner_algorithm(y_i, m_i)
        d = y % self._m_0
        return d

    def can_mult(self):
        return self.M ** 2 <= self.Mr

    def can_add(self):
        return self.M * 2 <= self.Mr

    def has_generated_shares(self):
        return self.shares is not None

    def add_operation(self, new_shares, self_shares, other_shares, index):
        self_a_i, self_m_i = self_shares
        other_a_i, other_m_i = other_shares
        if self_m_i != other_m_i:  # check coprimes
            print(f"mismatch in the {index}th coprime")
            return
        sum = self_a_i + other_a_i
        remainder = sum % self_m_i  # == sum % other_m_i
        new_share = (remainder, self_m_i)
        new_shares.append(new_share)

    def mul_operation(self, new_shares, self_shares, other_shares, index):
        self_a_i, self_m_i = self_shares
        other_a_i, other_m_i = other_shares
        if self_m_i != other_m_i:  # check coprimes
            print(f"mismatch in the {index}th coprime")
            return
        product = self_a_i * other_a_i
        remainder = product % self_m_i  # == sum % other_m_i
        new_share = (remainder, self_m_i)
        new_shares.append(new_share)

    def apply_operation(self, operation_type, other_asmuth_bloom):
        if operation_type == OperationType.ADDITION and not self.can_add():
            print(f'Can\'t add. 2*M ({2 * self.M}) is not less or equal than Mr ({self.Mr})')
        elif operation_type == OperationType.MULTIPLICATION and not self.can_mult():
            print(f'Cannot multiply. M^2 ({self.M ** 2}) is not less or equal than Mr ({self.Mr})')
        if not self.has_generated_shares() or not other_asmuth_bloom.has_generated_shares():
            print("a asmuth bloom object has not genereted shares")
            return
        if self.threshold != other_asmuth_bloom.threshold or self.s != other_asmuth_bloom.s:
            print("mismatching n, t and/or s")
            return
        new_shares = []
        for i in range(0, n):
            if operation_type == OperationType.ADDITION:
                self.add_operation(new_shares, self.shares[i], other_asmuth_bloom.shares[i], i)
            elif operation_type == OperationType.MULTIPLICATION:
                self.mul_operation(new_shares, self.shares[i], other_asmuth_bloom.shares[i], i)
        t, _ = self.threshold
        result_asmuth_bloom = self.create_asmuth_bloom_with_shares(new_shares)
        result_secret = result_asmuth_bloom.combine_shares(new_shares[0:t])
        result_asmuth_bloom._secret = result_secret

        if (operation_type == OperationType.ADDITION and result_secret != self._secret + other_asmuth_bloom._secret) \
                or (
                operation_type == OperationType.MULTIPLICATION and result_secret != self._secret * other_asmuth_bloom._secret):
            print(f"operation failure ({'addition' if operation_type == OperationType.ADDITION else 'multiplication'})")
            return None
        print("operation successful")
        print("Recombined secret: %s" % result_secret)
        return result_asmuth_bloom

    def create_asmuth_bloom_with_shares(self, new_shares):
        """ set everything aside from secret """
        new_asmuth_bloom = AsmuthBloom(self.threshold)
        new_asmuth_bloom._m_0 = self._m_0
        new_asmuth_bloom.num_of_op = self.num_of_op
        new_asmuth_bloom.M = self.M
        new_asmuth_bloom.Mr = self.Mr
        new_asmuth_bloom.Ms = self.Ms
        new_asmuth_bloom.Mn = self.Mn
        new_asmuth_bloom.s = self.s
        new_asmuth_bloom._y = self._y
        new_asmuth_bloom.shares = new_shares
        return new_asmuth_bloom


def stringToLong(s):
    val = binascii.hexlify(bytes(s, 'utf-8'))
    return int(val, 16)


def string_to_integer(str):
    num = 0
    for ch in str:
        num = num << 8 + ord(ch)
    return num


if len(sys.argv) < 5:
    print('Usage: ./bloom.py (--random <bits> | <path>) <N> <T> (<S> | <A> <M>)')
    print(' --random <bits>     - generate random secret')
    print(' <path>              - read secret from file')
    print(' <N>                 - number of shares')
    print(' <T>                 - number of shares needed for recovery')
    print(' <S>                 - minimum security parameter')
    print(' <A>                 - number of additions')
    print(' <M>                 - number of multiplications')
    sys.exit(1)

i = 0
source = sys.argv[1]
if source == '--random':
    random = random.SystemRandom()
    init_secret = random.getrandbits(int(sys.argv[2]))
    i += 1
else:
    try:
        a = open(source).read()
        init_secret = stringToLong(open(source).read())
    except Exception as e:
        print('Could not read the source file')
        print(e)
        sys.exit(1)

try:
    n = int(sys.argv[i+2])
    print('Got N = %d' % n)
except:
    print('Invalid N')

try:
    t = int(sys.argv[i+3])
    print('Got T = %d' % t)
except:
    print('Invalid T')

if t > n:
    print('T should be less or equal than N')
    sys.exit(1)

num_of_op = None
s = None

try:
    num_of_op = (int(sys.argv[i+4]), int(sys.argv[i+5]))
    print('Got Number of additions = %d' % num_of_op[0])
    print('Got Number of multiplications = %d' % num_of_op[1])
    if num_of_op[0] < 0 or num_of_op[1] < 0:
        print("number of operations must be a non negative number")
except:
    try:
        s = int(sys.argv[i+4])
        print('Got S = %d' % s)
        if s > n:
            print('S should be less or equal to N')
            sys.exit(1)
    except:
        print("S or number of operations must be provided")


def test_ab(ab):
    try:
        shares = ab.generate_shares(init_secret, m_0_bits, m_1_bits)
    except ValueError as e:
        print('Cannot generate shares: ' + str(e))
        sys.exit(1)
    print("Secret shares:")
    for i in range(0, n):
        print("%s: %s\n" % (i + 1, shares[i]))
    print('--------------------------------------')
    print('Checking result')
    d = ab.combine_shares(shares[0:t])
    print("Recombined secret: %s" % d)
    print("Test %s" % ('successful' if d == init_secret else 'failed'))
    print('--------------------------------------')

def calculate_operations(ab, original_ab):
    print('--------------------------------------')
    print(f"calculating {num_of_op[1]} multiplications")
    print('--------------------------------------')
    for i in range(num_of_op[1]):  # multiplications
        print('----')
        print(f'Secret1: {ab._secret}\nSecret2: {original_ab._secret}')
        result_of_operation = ab.apply_operation(OperationType.MULTIPLICATION, original_ab)
        if result_of_operation is None:
            return None
        ab = result_of_operation

    print('----')
    print(f"result of multiplication is {ab._secret}")

    print('--------------------------------------')
    print(f"calculating {num_of_op[0]} additions")
    print('--------------------------------------')

    for i in range(num_of_op[0]):  # additions
        print('----')
        print(f'Secret1: {ab._secret}\nSecret2: {original_ab._secret}')
        result_of_operation = ab.apply_operation(OperationType.ADDITION, original_ab)
        if result_of_operation is None:
            return None
        ab = result_of_operation

    print('----')
    print(f"result of addition is {ab._secret}")
    return ab._secret



threshold = (t, n)
print("Secret: %s" % init_secret)

coefficient = math.ceil(math.log(init_secret))

m_0_bits = coefficient * 2
m_1_bits = m_0_bits + coefficient
print(f"initial m_0: {m_0_bits}, initial m_1: {m_1_bits}")

while True:
    ab = AsmuthBloom(threshold, num_of_op, s)
    ab.generate_shares(init_secret, m_0_bits, m_1_bits)
    original_ab = ab
    final_result = calculate_operations(ab, original_ab)
    if(final_result is None):
        print('--------------------------------------')
        print("operations failed, recalculating m_0 and m_1...")
        m_0_bits = m_0_bits + int(math.log(m_0_bits, 2))
        m_1_bits = m_1_bits + int(math.log(m_1_bits, 2))
        print(f"new m_0: {m_0_bits}, new m_1: {m_1_bits}")
        continue
    print('--------------------------------------')
    print(f"final result of the secret is {final_result}")
    break






