# Inverse-theory Lean batch — 2026-08-09 (Claude)

User lifted the no-Lean directive (rules: unconditional, foreground, batched, no computations,
lake env lean per file + lake build module for audit, wire umbrellas, clean up processes).
Three new modules, all green, all axioms exactly [propext, Classical.choice, Quot.sound]:

1. `RHTower/XiWeilSourceInvolution.lean` (wired into RHTower umbrella, 8937-job build):
   - sourceInvolution f = conj ∘ f ∘ neg; involutive.
   - sourceFourier = the corpus e^{-izx} normalization; defeq to hedenmalmThetaEigenTransform
     on the Volterra flow.
   - MAIN, hypothesis-free: sourceFourier (sourceInvolution f) z = xiWeilSharp (sourceFourier f) z
     (integral_conj + integral_neg_eq_self are junk-value exact — NO integrability premises).
   - Certifies the N8 involution-existence half (ULF-INV-11 §4); ledger ID ULF-INV-N8-J.

2. `RHTower/ThetaCuspSeedZeroMean.lean` (wired, 9051-job build):
   - thetaCuspSeed_neg (evenness, simp); integrableOn_pow_mul_exp_neg_pi_sq;
   - cold-moment recursion values: coldGaussianHalfMoment π 0 = 1/2, π 1 = 1/(4π),
     π 2 = 3/(8π²) (only special-function input: Gamma_one_half_eq at the base);
   - MAIN: integral_thetaCuspSeed_Ioi_eq_zero — the D4a cancellation of ULF-INV-10 certified.
   - Ledger ID ULF-INV-D4A.

3. `HTGeometry/FiniteAmplifierPatternCap.lean` (wired into HTGeometry umbrella, 1941-job build):
   - twoPoint_pattern_cap: |b| ≤ a from nonnegativity at ±1 (Page's rho(Z/2) = 1) + tightness;
   - circle_pattern_nonneg: 3 + 4cosθ + cos2θ ≥ 0 (nlinarith on (1+cos)²); ratio 4/3 > 1;
   - width_cap: exclusion inequality ⟹ w < c·m/(c₁/a + K) − a (the 1/L shape forced) —
     minimal hypotheses (c, m positivity dropped as unnecessary).
   - The ULF-INV-7 algebraic core; ledger ID ULF-INV-7-CORE.

Lint: repo lint passed earlier this session (only pre-existing large-file warnings). Index
regenerated after each batch. One live lake process observed belonging to ANOTHER session
(building HTGeometry.UniversalLawField) — left untouched.

## Next Lean targets (queued)

- ULF-INV-10 contour theorem: the large certification target; approach through pieces
  (the pinned conventions are recorded in the promoted card; D4a now certified).
- ULF-INV-1's Lemma 2.1 + cross-system limit algebra (abstract, feasible).
- GAS-layer targets (GAS 2.1/3.1/5.1, GAS.12) remain from the earlier queue.
