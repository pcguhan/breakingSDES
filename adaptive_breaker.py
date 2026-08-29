from sdes_enc_dec import sdes_encrypt

def xor(a, b):
    return '1' if a != b else '0'

def int_to_bits4(x):
    return f"{x:04b}"

def make_pt(l_val, r_val):
    L = int_to_bits4(l_val)
    R = int_to_bits4(r_val)
    p = ['0'] * 8
    
    p[1] = L[0]
    p[5] = L[1]
    p[2] = L[2]
    p[0] = L[3]
    
    p[3] = R[0]
    p[7] = R[1]
    p[4] = R[2]
    p[6] = R[3]
    
    return ''.join(p)

R1_S0 = {}
R1_S1 = {}
R2_S0 = {}
R2_S1 = {}

query_count = 0

def extract_and_store(pt):
    global query_count
    
    ct = sdes_encrypt("0000000000", pt)
    print(pt, ct)
    query_count += 1
    
    p = list(pt)
    c = list(ct)

    t00 = xor(c[0], p[6])
    t01 = xor(c[1], p[3])
    t10 = xor(c[2], p[4])
    s01 = xor(c[3], p[1])
    s10 = xor(c[4], p[2])
    t11 = xor(c[5], p[7])
    s00 = xor(c[6], p[0])
    s11 = xor(c[7], p[5])

    idx1 = p[6] + p[3] + p[7] + p[4]  
    idx2 = p[7] + p[4] + p[6] + p[3]  

    R1_S0[idx1] = s00 + s01
    R1_S1[idx2] = s10 + s11

    r2_idx0 = (
        xor(p[0], s00) +  
        xor(p[1], s01) +  
        xor(p[5], s11) +  
        xor(p[2], s10)    
    )

    r2_idx1 = (
        xor(p[5], s11) +  
        xor(p[2], s10) +  
        xor(p[0], s00) +  
        xor(p[1], s01)    
    )

    R2_S0[r2_idx0] = t00 + t01
    R2_S1[r2_idx1] = t10 + t11
    
    return s00, s01, s10, s11

s_out_for_r0_is_0 = None

for r in range(16):
    pt = make_pt(0, r)
    s00, s01, s10, s11 = extract_and_store(pt)
    
    if r == 0:
        s_out_for_r0_is_0 = (s00, s01, s10, s11)

print(f"Discovered {len(R2_S0)}/16 Round 2 states.")

all_states = [f"{i:04b}" for i in range(16)]
missing_targets = [state for state in all_states if state not in R2_S0]

s00_0, s01_0, s10_0, s11_0 = s_out_for_r0_is_0


for target in missing_targets:

    p1 = str(int(target[0]) ^ int(s00_0)) 
    p2 = str(int(target[1]) ^ int(s01_0)) 
    p6 = str(int(target[2]) ^ int(s11_0)) 
    p3 = str(int(target[3]) ^ int(s10_0)) 
    
    l_int = int(p2 + p6 + p3 + p1, 2)

    pt = make_pt(l_int, 0)
    extract_and_store(pt)

print(f"Total exact queries used: {query_count}\n")

def emulate_cipher(plaintext):
    p = list(plaintext)
    idx1 = p[6] + p[3] + p[7] + p[4]  
    idx2 = p[7] + p[4] + p[6] + p[3]  
    
    s00, s01 = R1_S0[idx1]
    s10, s11 = R1_S1[idx2]

    r2_idx0 = (xor(p[0], s00) + xor(p[1], s01) + xor(p[5], s11) + xor(p[2], s10))
    r2_idx1 = (xor(p[5], s11) + xor(p[2], s10) + xor(p[0], s00) + xor(p[1], s01))
    
    t00, t01 = R2_S0[r2_idx0]
    t10, t11 = R2_S1[r2_idx1]

    out = [
        xor(p[6], t00), xor(p[3], t01), xor(p[4], t10), xor(p[1], s01),
        xor(p[2], s10), xor(p[7], t11), xor(p[0], s00), xor(p[5], s11)
    ]
    return ''.join(out)


def verify_all_plaintexts(test_key="0000000000"):
    print("Verifying all 256 plaintexts against the emulator...")
    matches = 0
    mismatches = 0
    
    for i in range(256):
        pt = f"{i:08b}"
        
        expected = emulate_cipher(pt)
        actual = sdes_encrypt(test_key, pt)
        
        if expected == actual:
            matches += 1
        else:
            mismatches += 1
            print(f"Mismatch at PT: {pt} | Expected: {expected} | Actual: {actual}")
            
    print(f"Verification complete: {matches}/256 plaintexts matched.")

        
    return matches == 256

verify_all_plaintexts()

while True:
    inp = input("Enter plaintext to be predicted: (q to quit): ")
    if inp != "q":
        expected = emulate_cipher(inp)
        actual = sdes_encrypt("0000000000", inp)

        print("Expected cipher: ", expected)
        print("Actual cipher:   ", actual)
    else:
        break
