from sdes_enc_dec import sdes_encrypt

# Secret key. if key is 0000000000, it resorts to default key, can be changed in sdes_enc_dec.py. Else you can change it here
ORACLE_KEY = "0000000000"

# Tables recovered by the attack
R1_S0 = {}
R1_S1 = {}
R2_S0 = {}
R2_S1 = {}

query_count = 0

# Oracle and bit helpers
def oracle(pt):
    """Black-box encryption oracle (the only place the secret key is used)."""
    return sdes_encrypt(ORACLE_KEY, pt)

def xor(a, b):
    return '1' if a != b else '0'

def int_to_bits4(x):
    return f"{x:04b}"

def is_bits(s, n):
    return len(s) == n and all(ch in "01" for ch in s)

def make_pt(l_val, r_val):
    """Build the 8-bit plaintext whose IP-halves are L0 = l_val and R0 = r_val."""
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

def reset_tables():
    global query_count
    R1_S0.clear()
    R1_S1.clear()
    R2_S0.clear()
    R2_S1.clear()
    query_count = 0

def extract_and_store(pt, verbose=True):
    """Query the oracle once and store the S-box outputs it reveals."""
    global query_count

    ct = oracle(pt)
    query_count += 1
    if verbose:
        print(f"  query {query_count:2d}: {pt} -> {ct}")

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

    r2_idx0 = xor(p[0], s00) + xor(p[1], s01) + xor(p[5], s11) + xor(p[2], s10)
    r2_idx1 = xor(p[5], s11) + xor(p[2], s10) + xor(p[0], s00) + xor(p[1], s01)

    R2_S0[r2_idx0] = t00 + t01
    R2_S1[r2_idx1] = t10 + t11

    return s00, s01, s10, s11

def phase1_sweep(verbose=True):
    """Phase 1: fix L0 = 0000 and sweep all 16 values of R0."""
    baseline = None
    for r in range(16):
        outputs = extract_and_store(make_pt(0, r), verbose)
        if r == 0:
            baseline = outputs
    return baseline

def phase2_forge(baseline, verbose=True):
    """Phase 2: forge L0 to hit every Round-2 index missed by Phase 1."""
    all_states = [f"{i:04b}" for i in range(16)]
    missing_targets = [s for s in all_states if s not in R2_S0]
    s00_0, s01_0, s10_0, s11_0 = baseline

    for target in missing_targets:
        p1 = str(int(target[0]) ^ int(s00_0))
        p2 = str(int(target[1]) ^ int(s01_0))
        p6 = str(int(target[2]) ^ int(s11_0))
        p3 = str(int(target[3]) ^ int(s10_0))

        l_int = int(p2 + p6 + p3 + p1, 2)
        extract_and_store(make_pt(l_int, 0), verbose)

    return len(missing_targets)

def run_attack(verbose=True):
    """Run both phases. Returns the total number of oracle queries used."""
    reset_tables()

    print("Phase 1: sweeping R0 (16 queries)")
    baseline = phase1_sweep(verbose)
    print(f"Phase 1 done. Round-2 states discovered: {len(R2_S0)}/16")

    print("Phase 2: forging L0 for missing Round-2 states")
    missing = phase2_forge(baseline, verbose)
    print(f"Phase 2 done. Forged queries: {missing}")

    print(f"Attack complete. Total oracle queries: {query_count}\n")
    return query_count

# Emulator and codebook (no oracle queries from here on)
def emulate_cipher(plaintext):
    """Predict the ciphertext of an 8-bit plaintext using only the recovered tables."""
    p = list(plaintext)
    idx1 = p[6] + p[3] + p[7] + p[4]
    idx2 = p[7] + p[4] + p[6] + p[3]

    s00, s01 = R1_S0[idx1]
    s10, s11 = R1_S1[idx2]

    r2_idx0 = xor(p[0], s00) + xor(p[1], s01) + xor(p[5], s11) + xor(p[2], s10)
    r2_idx1 = xor(p[5], s11) + xor(p[2], s10) + xor(p[0], s00) + xor(p[1], s01)

    t00, t01 = R2_S0[r2_idx0]
    t10, t11 = R2_S1[r2_idx1]

    out = [
        xor(p[6], t00), xor(p[3], t01), xor(p[4], t10), xor(p[1], s01),
        xor(p[2], s10), xor(p[7], t11), xor(p[0], s00), xor(p[5], s11)
    ]
    return ''.join(out)

def build_codebook():
    forward = {}
    reverse = {}
    for i in range(256):
        pt = f"{i:08b}"
        ct = emulate_cipher(pt)
        forward[pt] = ct
        reverse.setdefault(ct, []).append(pt)

    collisions = {ct: pts for ct, pts in reverse.items() if len(pts) > 1}
    return forward, reverse, collisions

# User-facing actions
def verify_bruteforce(forward, reverse, collisions):
    """Check the emulator against the real oracle on all 256 plaintexts."""
    print("Brute-force verification against the oracle (validation only, not part of the attack)")
    mismatches = 0
    for pt, predicted in forward.items():
        actual = oracle(pt)
        if predicted != actual:
            mismatches += 1
            print(f"  Mismatch at PT {pt}: predicted {predicted}, actual {actual}")
    print(f"  Encryption: {256 - mismatches}/256 plaintexts matched.")

    round_trip_ok = all(reverse[forward[pt]] == [pt] for pt in forward)
    print(f"  Distinct ciphertexts: {len(reverse)}/256")
    print(f"  Decryption table round-trips for all plaintexts: {round_trip_ok}")
    print(f"  Ciphertext collisions found: {len(collisions)}")

    ok = mismatches == 0 and round_trip_ok and not collisions
    print("  Result: attack VALID\n" if ok else "  Result: attack INVALID\n")
    return ok

def predict_ciphertext(forward):
    """Ask for an 8-bit plaintext and print the predicted ciphertext."""
    pt = input("Enter 8-bit plaintext (e.g. 10101010): ").strip()
    if not is_bits(pt, 8):
        print("  Invalid input: enter exactly 8 bits (0/1).\n")
        return
    print(f"  Predicted ciphertext: {forward[pt]}\n")

def recover_plaintext(reverse):
    """Ask for an 8-bit ciphertext and print the recovered plaintext(s)."""
    ct = input("Enter 8-bit ciphertext (e.g. 01010101): ").strip()
    if not is_bits(ct, 8):
        print("  Invalid input: enter exactly 8 bits (0/1).\n")
        return
    candidates = reverse.get(ct, [])
    if len(candidates) == 1:
        print(f"  Recovered plaintext: {candidates[0]}\n")
    elif len(candidates) > 1:
        print(f"  COLLISION: {len(candidates)} plaintexts encrypt to {ct}: {', '.join(candidates)}\n")
    else:
        print("  No plaintext found for this ciphertext.\n")

def show_collisions(collisions):
    if not collisions:
        print("  No ciphertext collisions: the recovered cipher is a permutation of all 256 blocks.\n")
        return
    print(f"  {len(collisions)} colliding ciphertext(s):")
    for ct, pts in sorted(collisions.items()):
        print(f"    {ct} <- {', '.join(pts)}")
    print()

def main():
    run_attack()
    forward, reverse, collisions = build_codebook()
    if collisions:
        print(f"WARNING: {len(collisions)} ciphertext collision(s) in the recovered codebook.\n")

    menu = (
        "Options:\n"
        "  1  Brute-force verify the attack (256 extra oracle queries)\n"
        "  2  Enter a plaintext, predict the ciphertext\n"
        "  3  Enter a ciphertext, recover the plaintext\n"
        "  4  Show codebook collisions\n"
        "  q  Quit"
    )
    while True:
        print(menu)
        choice = input("Select: ").strip().lower()
        print()
        if choice == "1":
            verify_bruteforce(forward, reverse, collisions)
        elif choice == "2":
            predict_ciphertext(forward)
        elif choice == "3":
            recover_plaintext(reverse)
        elif choice == "4":
            show_collisions(collisions)
        elif choice == "q":
            break
        else:
            print("  Unknown option.\n")


if __name__ == "__main__":
    main()