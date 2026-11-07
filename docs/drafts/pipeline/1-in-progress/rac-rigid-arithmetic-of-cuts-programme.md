# Rigid Arithmetic of Cuts (RAC) programme

- **ID:** RAC
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0611/obstacles-summary.md §2.6, §2.9
- **Statement:** how the exact statement `N(x) = ⌊x⌋` forces its zeros by operations with no sign that are not linear floor identities.

## Goal
Lean folder `formal/GaloisForLFunctions/RigidArithmeticOfCuts/`, umbrella `RigidArithmeticOfCuts.lean`, foundational `README.md`.
Answer the questions of §2.9, build the tools of §2.9, meet the criteria of §2.9.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Research map

Questions of §2.9 and §2.6, with the target theorem for each:

| Q | Target |
|---|---|
| Fake closest to the true one | at infinite level there is exactly one fake: pronic; finite level: window radius is the rate |
| Single off-line zero against `⌊x⌋` | power-law kernel of the cut system = zeros; `ℓ¹` kernel trivial; every exact ledger holomorphic at zeros |
| Nonlinear functional that sees a zero | `ζ A^k` has pole order `k − m`; only `k = 1` is blind; Selberg ledger separates the twin at scale `x` |
| What replaces Frobenius | Frobenius defect of `⌊⌋` is the carry; quantized norms make the cut system triangular with finite kernel |
| Primes recur at a zero | effective Kronecker; torus surjection; bounded returns carry a spike |
| Rotated relation | oriented extremal modulus [paper]; arithmetic coefficients must be nonzero at zeros; unrestricted balanced coefficients are vacuous [Lean] |

Tools: nonblind ledgers; parity ledger reduction; effective Kronecker; Beurling metric (Hamming exponent, count exponent, FE defect).

## Mathematics found

**Cut identity.** For `U(r) = T(r) − T(r+1)`, `Σ_{r ≤ kJ} U(r)(r mod k) = Σ_{r ≤ kJ} T(r) − k Σ_{j ≤ J} T(kj)`.

**Uniqueness of the fake.** `W = 1/r − T(r)`. Upper side: Hecke dilates of producers give `T(j) ≤ (1+ε)/j`, so `W ≥ 0`. `W − 1/r` is nondecreasing, so `k W(kj) ≤ Σ_{block} W + 1/j²`, and the cut identity gives `Z(k−1) ≤ 2`: `W` is summable. Then `W(kℕ) = S/k`, which forces `W = 0`.

**`ℓ¹` kernel trivial.** `m(A(n,P)) = (S/n) Π_{p∈P}(1 − 1/p)` where `A(n,P)` = multiples `nt` with `t` prime to `P`. With `P` = primes `≤ X`, `A = {n} ∪` far points.

**Finite level.** Translating an atom by `L = lcm(1..K)` keeps every moment, so window mass has infimum `0`: only the upper radius is meaningful without a tail bound.

**Ledger hierarchy.** `ζ A^k`, `A = −ζ′/ζ`: order `m − k` at a zero of multiplicity `m`, so `k = 1` is the unique blind level.

**Twin at second order.** `a = Λ − 2Λ_□` for `−λΛ`. The quadratic reading differs from `Λ∗Λ` by `−4 Λ∗Λ_□ + 4 Λ_□∗Λ_□`, of size `x`.

**Integer systems.** A fake `ζ·G` with `G` a Dirichlet polynomial has no new zero on `Re s > 0`. New zeros at `β` need exchange mass of exponent `≥ β`.

**Extremal angle [paper].** `Q(α²) = XiC α`, zeros near the positive axis. Under ¬RH a maximal positive angle is attained. With `u = w_k/w_n` and `|q|=1`, `Im q>0`, the factors compare in the required direction. The exact identity `|1−qu|²−|1−q̄u|²=4 Im(q) Im(u)` is Lean verified.

**Coefficient boundary [Lean].** Balanced coefficients in a rotated identity at a zero either both vanish or enforce equal rotated moduli. The choice `a=b=F` makes the unrestricted identity universal, even with origin normalization. The quantitative residual bound and unit-coefficient converse are formalized in `RotatedRelationsNeedNonvanishingCoefficients`; [scoped refutation](../5-failed/rotated-relations-with-unrestricted-balanced-coefficients.md). The repaired arithmetic construction remains open.

## Log
- 2026-11-07 — created in 1-in-progress
