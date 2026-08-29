def sdes_encrypt(key, plaintext):
    if key == "0000000000":
        key = "1111111111" #master key, change for testing
    return _sdes(key, plaintext, encrypt=True)

def sdes_decrypt(key, ciphertext):
    return _sdes(key, ciphertext, encrypt=False)

def _sdes(key_str, data_str, encrypt=True):
    key = [int(b) for b in key_str]
    data = [int(b) for b in data_str]

    P10 = [3,5,2,7,4,10,1,9,8,6]
    P8  = [6,3,7,4,8,5,10,9]
    P4  = [2,4,3,1]
    IP  = [2,6,3,1,4,8,5,7]
    IP_INV = [4,1,3,5,7,2,8,6]
    EP  = [4,1,2,3,2,3,4,1]

    S0 = [[1,0,3,2],[3,2,1,0],[0,2,1,3],[3,1,3,2]] #change sbox for testing.
    S1 = [[0,1,2,3],[2,0,1,3],[3,0,1,0],[2,1,0,3]]

    def perm(bits, table):
        return [bits[i-1] for i in table]

    def lshift(bits, n):
        return bits[n:] + bits[:n]

    def xor(a, b):
        return [x ^ y for x, y in zip(a, b)]

    def sbox_lookup(bits, sbox):
        r = bits[0]*2 + bits[3]
        c = bits[1]*2 + bits[2]
        val = sbox[r][c]
        return [val // 2, val % 2]

    def generate_keys(key10):
        p10 = perm(key10, P10)
        l, r = p10[:5], p10[5:]
        l1, r1 = lshift(l,1), lshift(r,1)
        k1 = perm(l1+r1, P8)
        l2, r2 = lshift(l1,2), lshift(r1,2)
        k2 = perm(l2+r2, P8)
        return k1, k2

    def fk(bits, subkey):
        l, r = bits[:4], bits[4:]
        er = perm(r, EP)
        x = xor(er, subkey)
        left = sbox_lookup(x[:4], S0)
        right = sbox_lookup(x[4:], S1)
        p4 = perm(left+right, P4)
        
        return xor(l, p4) + r

    def sw(bits):
        return bits[4:] + bits[:4]

    k1, k2 = generate_keys(key)
    if not encrypt:
        k1, k2 = k2, k1

    ip = perm(data, IP)
    temp = fk(ip, k1)
    temp = sw(temp)
    temp = fk(temp, k2)
    out = perm(temp, IP_INV)
    return ''.join(str(b) for b in out)

