# XiC order-one growth: the cornerstone of the explicit-formula organ

**Stage:** 1 — in progress
**Claim (exact):** [CONJECTURE → target theorem] There is `B ≥ 0` with
`∀ z : ℂ, ‖XiC z‖ ≤ Real.exp (B * (1 + ‖z‖) * Real.log (2 + ‖z‖))`
(equivalently the same bound for `xi` on `ℂ`), unconditional Lean.

**Why this card exists (the synergy audit conclusion, 2026-08-11):** four live lanes (C1/Gauss
deviation-mass, Route O restricted-Weil, Route U hard-edge boundary, Route T prime side) all
terminate against the missing Guinand–Weil explicit formula. The zero-side half of that organ is
the Hadamard product; the corpus already owns `xiHadamardQuotient * xiCanonicalProduct = XiC`
and the conditional constancy theorem `xiHadamardQuotient_constant_of_log_reBound`, whose ONLY
missing input is this growth bound (plus, for full constancy, a Cartan lower bound on the
canonical product — a separate later card). Mathlib meanwhile owns Jensen's formula
(`MeromorphicOn.circleAverage_log_norm`), so growth ⇒ zero-counting `N(r) ≪ r log r` is also
unlocked by this card.

**Immediate capstone reachable from this card alone (no Cartan needed):**
[CONJECTURE] `∃ ρ : ℂ, xi ρ = 0` — the first formal existence of a nontrivial zeta zero.
Proof route: if the divisor is empty, `XiZeroCopy` is empty, `xiCanonicalProduct ≡ 1`
(empty tprod), so `xiHadamardQuotient = XiC` by the corpus product identity; `XiC = exp g`
(`xiHadamardQuotient_has_log`), `Re g = log ‖XiC‖ ≤` growth bound, so
`xiHadamardQuotient_constant_of_log_reBound` forces `XiC` constant; but
`xi 0 = 1/2` and `xi 2 = π/6` (mathlib `riemannZeta_two`), and `π ≠ 3`
(`Real.pi_gt_three`), contradiction.

**Proof plan for the growth bound (no Stirling, no Phragmén–Lindelöf):**
1. `completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2` and
   `WeakFEPair.Λ₀ = mellin f_modif` (mathlib `AbstractFuncEq`). Hence
   `‖Λ₀(s)‖ ≤ ∫₀^∞ t^(Re s − 1) ‖f_modif t‖ dt`.
2. Majorant for `f_modif` (both ends rapid):
   - on `(1,∞)`: `f_modif = θ − 1 = 2Σ_{n≥1} e^{−πn²t} ≤ 2 e^{−πt}/(1−e^{−π})`;
   - on `(0,1)`: FE transport `hf_modif_FE`: `‖f_modif t‖ = t^(−1/2)·‖g_modif(1/t)‖ ≤
     C t^(−1/2) e^(−π/t)`; substitution `u = 1/t` folds this onto `∫₁^∞ u^(−σ−1/2) e^{−πu}`.
3. Elementary Gamma-type bound: `G a := ∫₁^∞ t^a e^{−πt} dt ≤ exp(K(1+a)·log(2+a))` by
   splitting at `M = 2a² + 9`: on `[1,M]` bound by `M^(a+1)`; on `[M,∞)` use
   `log t ≤ 2(√t − 1)` to get `t^a e^{−πt/2} ≤ 1`, leaving `∫ e^{−πt/2} = 2/π·e^{−π/2}`.
4. Assemble: `‖completedRiemannZeta₀ s‖ ≤ exp(K'(1+|Re s|)log(2+|Re s|))`; then
   `xi s = s(s−1)/2·Λ₀(s) + 1/2` gives the polynomial factor (absorbed), and
   `XiC z = xi(1/2 + z·I)` finishes.

**Downstream (later cards):** Cartan minimum-modulus for `xiCanonicalProduct` → Hadamard
constancy → partial fractions of `XiC'/XiC` over the divisor → glue with prime side
(mathlib/PNTPlus `−ζ'/ζ = Σ Λ(n) n^{−s}` on `Re > 1`) → the log-derivative explicit formula →
Weil-type formulas for band-limited tests → the producer sockets of C1/Gauss, O, U, T.

**Dead/closed context:** the O ↔ xiWeilPolarization "dictionary" splice is NOT definitional —
O's matrix is prime-side, the polarization is zero-side; their identification IS this organ.
Recorded 2026-08-11 after hostile check.

## Log
- 2026-08-11 — card opened after the frontier-map synergy audit. Mathlib interface points
  verified: `WeakFEPair.Λ₀ = mellin f_modif` (`Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`),
  `hf_modif_FE`/`hf_modif_top`, `hurwitzEvenFEPair`, Jensen (`Mathlib/Analysis/Complex/
  JensenFormula.lean`), corpus receivers `xiHadamardQuotient_constant_of_log_reBound`,
  `entire_reBound_imp_affine`, `xiHadamardQuotient_has_log`,
  `xiHadamardQuotient_mul_canonicalProduct`. `riemannZeta_two` and `Real.pi_gt_three` confirm
  the nonconstancy witness needs no computation.
