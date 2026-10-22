# The near-null conditioning constant exceeds 2π

- **ID:** C608-E (HCF ledger row 612)
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper sketch; Lean not started)
- **Source:** HCF ledger rows 611–612; MUST-1319, MUST-1302, CANNOT-507; corpus
  `TruncatedRiemannKernelWeilEnergy`, `WeilNearRadicalDimension`.
- **Statement:** Let `Y = 2πe^{2A}`, `m = ⌊Y/14⌋`, `p(s) = (s² − Y²)^m` and `f_A = (p(D)Φ)·χ_{[−A,A]}`.
  For all large `A`, `f_A` is even, real, supported in `[−A, A]`, and
  `Re W(f_A, f_A) ≤ e^{−2π(1+1/24)e^{2A}}·∫f_A²`. So the radical truncation `Φχ_A`, whose energy is
  exactly `e^{−2πe^{2A}+O(A)}` (MUST-1319), is not the near-null ground state, and the conditioning
  constant `c*` in `−log m(A) ~ c*e^{2A}` is `> 2π`.

## Goal
Sharpen CANNOT-507 (constant `π/e`) and MUST-1319 (constant `2π`, one direction) to a constant strictly
above `2π`.

Relation to the corpus:
- The corpus already owns the near-radical family `Σ a_iΦ^{(i)}χ_L` with `K ≈ e^{2a−2}/10` derivatives,
  and its dimension `≥ e^{2a−2}/20`, at energy `≤ exp(−e^{2a−2})` (`zeta_weil_near_radical_dimension`).
- The only new content here is the per-direction constant beyond `2π`.

## Gates
- [x] 0 → 1  in-progress: well-posed; attack idea below
- [ ] 1 → 2  fully-proven: write out steps 5–8 with explicit constants
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach (paper proof)
1. **Radical identity.** `(p(D)Φ)^ = p(−it)Ξ`, which vanishes at every zero, so `W(f_A) = W(T)` with
   `T = p(D)Φ·(1 − χ_{[−A,A]})`. The corpus has the matching identity (`paperFT_nearRadicalTest_eq`).
2. **Bulk.** `|p(−it)| = (t² + Y²)^m ≥ Y^{2m}`, so `‖p(D)Φ‖ ≥ Y^{2m}‖Φ‖`.
3. **Cauchy–Laplace kernel.** For `F` analytic on `|w − u| ≤ ρ` and `q = Σ b_k s^k`:
   `|q(D)F(u)| ≤ max_{|z|=ρ}|F(u+z)|·∫_0^∞ e^{−t} q₊(t/ρ) dt`, where `q₊` has the coefficients `|b_k|`.
   Conjugating, `p(D)(e^{−Yu}H) = e^{−Yu}·s^m(s − 2Y)^m(D)H` with `H = e^{Yw}Φ`.
4. **Kernel bound.** `K := ∫e^{−t}(t/ρ)^m(t/ρ + 2Y)^m dt`. Using `(t/ρ + 2Y)^m ≤ (2Y)^m e^{βt}` with
   `β = 5/28`, and `ρ = 1/5`:
   `K ≤ Y^{2m}·(e√m/(1−β))·(20/(23e))^m ≤ Y^{2m}·poly(Y)·e^{−0.0807Y}`.
5. **Strip envelope.** For `|Im w| ≤ ρ`:
   `|Φ(w)| ≤ C e^{(9/2)Re w} exp(−πe^{2Re w}cos(2 Im w))`, with the `n ≥ 2` theta terms dominated.
   At `u = A` the circle exponent is `Y(ψ(θ) − ½)`, where `ψ = ρc − ½(e^{2ρc}cos(2ρs) − 1)`.
   For `u > A` there is an extra factor `≤ e^{−0.6Y(u−A)}`, since `Re e^{2z} ≥ e^{−2ρ}cos 2ρ > 0.6`.
6. **ψ bound.** `e^x ≥ 1 + x + x²/2 + x³/6` and `cos y ≥ 1 − y²/2` give
   `ψ ≤ ρ² + 2ρ³ + 4ρ⁴ ≤ 0.0571` (the sharp value is ≈ 0.0408).
7. **Tail.** `|T(A + x)| ≤ Y^{2m}·poly(Y)·E(A)·e^{−0.0236Y}·e^{−(0.6Y − 9/2)x}`, and `T` is even.
8. **Weil upper bound for signed tails.**
   - `|pole| ≤ 2(∫|T|e^{|u|/2})²`;
   - `arch ≤ (C + s/2)∫T² + ∫T'²/(2s)`;
   - `|prime| ≤ poly(Y)‖T‖_∞²`.
   Hence `Re W(f_A)/∫f_A² ≤ poly(Y)e^{9A}e^{−Y(1+0.0472)} ≤ e^{−2π(1+1/24)e^{2A}}`.

Optimizing over `(ρ, m/Y)` inside this method gives at best `c ≈ 2π·1.085`.

## Related open questions
- **C608-P (positivity of these directions without RH).** The Mellin saddle at
  `s − ½ = Y ± iβY` (`β = √(2m/Y)`) should give the edge law
  `T(A+x) ≈ 2|S|e^{−(Y + Re w)x}cos(Θ₀ − βYx)` for `x ≲ log Y/Y`. With it, the prime sum sees only
  `O(A)` integers near `e^{2A}`, so the archimedean term dominates. The edge law (complex Stirling at
  real part ≈ `Y/2` plus steepest descent) is open.
- **C609 (refuted).** Certifying the near-radical subspace separately does not remove the conditioning
  wall. In the Schur complement, `arch(g,T)²/W(T) → arch(g)`, which leaves `pole − prime`.
- **[OPEN CORE].** The exact value of `c*` under RH.

## No-go closure (mandatory when falsified)
Not falsified. A one-sided variant `(D+Y)^mΦ` was FALSE as an even test, because it amplifies the left
tail by `2^m`. The survivor is the even multiplier above.

## Log
- 2026-10-12 — created in 1-in-progress from the ledger row 612 audit.
