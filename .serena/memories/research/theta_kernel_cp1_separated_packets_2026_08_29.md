# CP-1 separated-packet positivity — LEAN-PROVED (2026-08-29)

Card: `docs/drafts/pipeline/1-in-progress/theta-kernel-cp-deficit-domination.md`.
Module: `formal/GaloisForLFunctions/RHTower/ThetaTailSeparatedPacketPositivity.lean`
(umbrella-wired, axioms propext/Classical.choice/Quot.sound on all 10 public theorems).

## The theorem

`thetaTailFirstMomentKernel_separatedPacket_quadraticForm_nonneg`: for every
σ ≥ `thetaTailPacketSeparation` (= 2·log(1+2K), K = 3C_u²e^{8π}/(2πC_l²)), every packet
x : ℕ → ℝ with x 0 ≥ 1 and steps ≥ σ, every n, a: the quadratic form of
`thetaTailFirstMomentKernel` is ≥ 0. First unconditional off-diagonal PSD stratum of the
live Bezoutian RH endpoint (`riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`).
The RH burden now lives entirely below the separation threshold (close pairs — the HCF
displacement regime).

## Proof architecture (reusable envelope calculus)

- Corpus envelopes (`HedenmalmThetaKernelEnergy`, namespace `RHTower.HedenmalmThetaSource`):
  `thetaEnvelope y = e^{9y/2}e^{−πe^{2y}}`, `thetaCuspFullSource_le_envelope` (x ≥ 0),
  `_ge_envelope` (x > 0), `thetaEnvelope_le_shift` (1 ≤ x ≤ y: E(y) ≤ E(x)e^{−πe^{2x}(y−x)}).
- Diagonal floor: one slab of width δ = e^{−2y}; loss factor e^{−4π} via
  e^{2δ}−1 ≤ 2δe^{2δ} ≤ 4δ (needs only 2 ≤ e ≤ 4: `Real.add_one_le_exp`, `exp_one_lt_d9`).
  `k(y,y) ≥ 2C_l²e^{−8π}·y·e^{−2y}·E(y)²`.
- Ceiling: `k(x,t) ≤ (C_u²/π)(x+t+1)E(x)E(t)e^{−2t}` via shift law + affine Laplace values
  (`integral_Ioi_id_mul_exp_neg_mul` : ∫s·e^{−cs} = 1/c², from
  `Real.integral_rpow_mul_exp_neg_mul_Ioi` a=2 + `Real.Gamma_two`; the
  `Integrable.of_integral_ne_zero` trick gives integrability from a nonzero value).
- Ratio: `poly_vs_exp` ((x+t+1)² ≤ 9xt·e^{t−x} via `Real.log_le_sub_one_of_pos`), squared
  master `k(x,t)² ≤ (Ke^{−(t−x)/2})²k_xxk_tt`.
- Gershgorin: b i := |a i|·√k_ii scaling, AM–GM per pair, `Nat.dist` + `Finset.sum_comm'`
  double-count swap, geometric row sums ≤ 2q/(1−q), threshold ⟺ q(1+2K) ≤ 1.

## Traps hit (add to Lean playbook)

- `positivity` CANNOT certify opaque project constants (thetaEnvelopeLower/Upper,
  thetaEnvelope y) even with positivity facts in context — write mul_pos/mul_nonneg chains
  explicitly everywhere such atoms appear.
- `Integrable.add` unfolds IntegrableOn to an And — dot `.congr_fun` resolves to
  `And.congr_fun`; use full `MeasureTheory.IntegrableOn.congr_fun` (known trap, re-hit).
- Exp-constant bookkeeping (e^{8π} vs e^{−8π} cancellations through divisions): do NOT fight
  field_simp+linear_combination on the concrete goal. Abstract the exponentials into fresh
  variables with their relations as hypotheses (`ratio_identity_abstract` pattern:
  m8 := e8⁻¹ eliminates one relation; the balance relation enters once via rw), prove the
  division-free identity by field_simp+ring, instantiate. Robust on first try.
- `setIntegral_ge_of_const_le` returns `volume.real s • c`; convert via
  `measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal, sub_zero, smul_eq_mul, mul_comm`.
- `div_le_div_iff` gone; `pow_le_pow_left` → `pow_le_pow_left₀`;
  `HasSubset.Subset.eventuallyLE` → `LE.le.eventuallyLE`;
  `Finset.sum_Ico_eq_sum_range` takes f first; `geom_sum_eq` + `neg_div_neg_eq` for
  (1−q^m)/(1−q); `Real.exp_lt_one_iff` unreliable — use exp_lt_exp with exp_zero.
- `exp_neg_integrableOn_Ioi` integrand is `exp(-b*x)` (neg_mul shape) — congr with
  `simp only [neg_mul]`.
- Name collision: corpus already owns `thetaTailFirstMomentKernel_nonneg` — mine is
  `thetaTailKernel_nonneg_of_one_le`.

## Open next

Shrink threshold; extend below x = 1 (reflection seam); the close-pair regime (true CP-1
frontier); coincident jets parked (razor-thin at x≈0, would need certified numerics — the
2×2 jet inequality at x=0 is `2∫yΦ'² ≥ Φ(0)²`-borderline, possibly encodes central-value
margins).
