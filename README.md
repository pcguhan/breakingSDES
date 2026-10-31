# S-DES Global Deduction Attack

Reference implementation of Simplified DES (S-DES) and an adaptive chosen-plaintext attack that fully determinizes the cipher's input–output behavior without recovering the secret key. This repository accompanies the preprint available at [10.13140/RG.2.2.12444.04485](https://doi.org/10.13140/RG.2.2.12444.04485) *"Key-Independent Structural Recovery of the S-DES Cipher via Adaptive Chosen-Plaintext Queries."*

## Overview

The attack exploits the fact that every S-DES ciphertext bit is the XOR of a specific plaintext bit and a single S-box output bit. This allows an attacker to extract effective S-box lookup tables for both rounds using far fewer queries than a full 256-plaintext codebook or a 1024-key brute force:

- **Phase 1 (16 queries):** A linear sweep of `R0` (with `L0` fixed to `0000`) fully maps both Round-1 S-boxes.
- **Phase 2 (up to 15 queries):** An adaptive forge of `L0` deterministically targets any Round-2 index left unobserved due to S-box collisions in Phase 1.

The result is a complete emulator that reproduces the cipher's behavior on all 256 plaintexts, without ever recovering the subkeys `K1`, `K2`.

## Files

| File | Description |
|---|---|
| `sdes_enc_dec.py` | Reference S-DES implementation (key schedule, Feistel rounds, encryption/decryption). |
| `adaptive_breaker.py` | The attack: Phase 1 sweep, Phase 2 adaptive forge, emulator construction, and full 256-plaintext verification. |
| `leanProof.lean` | Lean model and symbolic proof of attack correctness for arbitrary S-box functions and explicit eight-bit subkeys. |

## Requirements

- Python 3.8 or later
- No external dependencies

## Usage

Run the attack directly:

```bash
python adaptive_breaker.py
```

This will:

1. Execute the 16-query Phase 1 sweep and report how many Round-2 states were discovered.
2. Execute the Phase 2 adaptive forge to fill any remaining Round-2 states, and report the total query count.
3. Verify the resulting emulator against the reference implementation across all 256 plaintexts and report the match count.
4. Prompt for interactive plaintext input, comparing the emulator's predicted ciphertext against the reference implementation's actual output. Enter `q` to quit.

## Notes on the Reference Implementation

- Encryption and decryption use the supplied key directly, including the all-zero key. The attack demonstration queries the all-zero key.
- The Lean proof applies to the Lean cipher and attack models; correspondence with the Python implementation is not formally proved. The Python and Lean cipher implementations both use the supplied master key directly, but that alignment alone is not a proof that the implementations agree.
- The `S0` and `S1` tables in `sdes_enc_dec.py` can be freely modified. The attack is agnostic to the specific S-box values used; it recovers the *effective* table for whatever S-boxes are configured, standard or otherwise.

## Reproducing the Paper's Complexity Claims

- With the standard S-DES S-boxes, empirical testing across all 1024 possible keys shows an average query count of **≈19.8** with a worst case of **21**.
- Across randomized S-box configurations, the average is **≈22** with a theoretical worst case of **31**, occurring when both effective Round-1 S-boxes collapse to a constant output.

To reproduce these figures across the full key space or across randomized S-box tables, modify `sdes_enc_dec.py` accordingly and re-run `adaptive_breaker.py`, or wrap it in an external script that iterates over keys/S-box configurations and aggregates `query_count`.

## License

MIT License. See `LICENSE` for details.

## Citation

If you use this code, please cite the accompanying preprint:

```
PC Guhan. "Key-Independent Structural Recovery of S-DES via Adaptive Chosen-Plaintext Queries" Preprint.
```
