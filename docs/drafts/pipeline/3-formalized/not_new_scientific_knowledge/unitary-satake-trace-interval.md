# Unitary Satake trace interval

- **ID:** unitary-satake-trace-interval
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/explicit-formula-as-constraint.md` §3 prime-block input and `../2-fully-proven/g4-over-fq-deligne-katz.md` §2 angle/unit-circle split; Lean file `formal/GaloisForLFunctions/RHTower/SatakeInterval.lean`
- **Statement:** If a rank-two Satake parameter is unitary, `|z|=1`, then its trace `z+z^{-1}` is the real number `2*Re(z)` and has real part in `[-2,2]`; more generally the `Sym^k` unitary trace has norm at most `k+1`.

## Goal
This banks the exact finite Satake compactness floor cited as the prime-block positivity input in the explicit-formula constraint card and as the unit-circle angle skeleton in the function-field G4 card. It does not formalize Sato-Tate equidistribution, Ramanujan, the Weil explicit formula, `Q_W`, the DeWitt signature, or RH positivity.

## Paper Proof
Assume `|z|=1`. Then `z^{-1}=conj(z)`, so
```
z + z^{-1} = z + conj(z) = 2*Re(z),
```
which is real. Since `|Re(z)| <= |z| = 1`, the real trace satisfies
`-2 <= 2*Re(z) <= 2`, hence `(z+z^{-1}).re` lies in `[-2,2]`.

For the symmetric-power trace, every term `z^(k-2j)` has norm one because `|z|=1`. The triangle inequality gives
```
|sum_{j=0}^k z^(k-2j)| <= sum_{j=0}^k |z^(k-2j)| = k+1.
```
Thus the `Sym^k` trace lies in the closed disk of radius `k+1`.

## Gates
- [x] 0 -> 1  in-progress: exact unitary Satake trace floor extracted from the explicit-formula prime-block input and G4 angle split.
- [x] 1 -> 2  fully-proven: paper proof above, using only `z^{-1}=conj(z)` on the unit circle and the triangle inequality.
- [x] 2 -> 3  formalized: Lean theorems `satake_trace_eq_two_mul_re`, `satake_trace_im`, `satake_trace_re_mem_Icc`, and `symPower_trace_norm_le`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: cite as the formal certificate for the finite Satake compactness floor.

## Log
- 2026-06-19 — Leaner split this exact unitary Satake interval lemma from `explicit-formula-as-constraint` and `g4-over-fq-deligne-katz`. The parent cards remain in `2-fully-proven` because the explicit-formula identification, DeWitt pairing, Deligne-Katz imports, and global positivity/equidistribution layers are not fully Lean-formalized.
