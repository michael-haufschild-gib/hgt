import GaloisForLFunctions.HTGeometry.CriticalClockSourceUniversality
import GaloisForLFunctions.RHTower.MobiusCriticalFisherLowerBoundaryBudget

/-!
# The CCM four-unit source budget is blind to the strict-right divisor

`CriticalClockSourceUniversality.lean` proves that the critical clock Laplace transform of a
nonnegative Mellin source depends only on the simple pole of its Mellin transform at `σ=1`, and
that the whole rank-two cutoff Ward profile is a functional of the resulting `Exp(1)` law.  Hence
the CCM four-unit budget, its one-corner profile, and the pointed-Fisher curvature are *class
invariants* of

```text
𝓢 = { nonnegative measures dN on [1,∞) whose Mellin transform has a simple pole at σ = 1 }.
```

The squarefree Möbius source of the RH tower lies in `𝓢`, and for it the vanishing of the
strict-right divisor is exactly RH.

This module constructs an explicit second member of `𝓢` whose strict-right divisor is nonempty:

```text
dN₀ = Lebesgue on (1,∞)  +  m·δ_X,        Z₀(s) = (s-1)⁻¹ + m·X^{-s},
```

with `X = exp L > 1` and `m > 0` chosen so that `Z₀` vanishes at a prescribed `θ ± ia`,
`1/2 < θ < 1`.  Its Schwarz-paired Cauchy (Ward) energy already exceeds **eight**, so it violates
the corner-lift law at every admissible threshold `c ∈ [0,8]`.

Consequence: no implication of the form "four-unit source budget ⟹ Ward energy `≤ 4` (or `≤ 8`)"
can be valid, because its hypothesis is constant on `𝓢` while its conclusion is not.  Every
source-to-target transport whose only source input is a critical clock functional is therefore
excluded, independently of its operator shape.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The witness source -/

/-- The witness measure: Lebesgue measure on `(1,∞)` plus one positive atom at `exp L`. -/
def blindWitnessMeasure (m L : ℝ) : Measure ℝ :=
  volume.restrict (Ioi 1) + (ENNReal.ofReal m) • Measure.dirac (Real.exp L)

/-- Mellin transform of the witness measure, as a real function of `σ > 1`. -/
def blindWitnessMellinReal (m L σ : ℝ) : ℝ :=
  (σ - 1)⁻¹ + m * Real.exp (-σ * L)

/-- Meromorphic continuation of the witness Mellin transform. -/
def blindWitnessMellin (m L : ℝ) (s : ℂ) : ℂ :=
  (s - 1)⁻¹ + (m : ℂ) * Complex.exp (-s * (L : ℂ))

/-- The declared real function really is the Mellin transform of the nonnegative witness
measure. -/
theorem blindWitnessMellinReal_eq_integral {m L σ : ℝ} (hm : 0 ≤ m) (hσ : 1 < σ) :
    blindWitnessMellinReal m L σ = ∫ x, x ^ (-σ) ∂(blindWitnessMeasure m L) := by
  have hlt : (-σ : ℝ) < -1 := by linarith
  have hint1 : Integrable (fun t : ℝ => t ^ (-σ)) (volume.restrict (Ioi 1)) :=
    integrableOn_Ioi_rpow_of_lt hlt one_pos
  have hint2 : Integrable (fun t : ℝ => t ^ (-σ))
      ((ENNReal.ofReal m) • Measure.dirac (Real.exp L)) := by
    refine Integrable.smul_measure ?_ (by simp)
    exact integrable_dirac (by simp [enorm_eq_nnnorm])
  rw [blindWitnessMeasure, integral_add_measure hint1 hint2, integral_smul_measure,
    integral_dirac, integral_Ioi_rpow_of_lt hlt one_pos, ENNReal.toReal_ofReal hm,
    Real.one_rpow, Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp]
  rw [blindWitnessMellinReal]
  have h1 : -(1 : ℝ) / (-σ + 1) = (σ - 1)⁻¹ := by
    rw [inv_eq_one_div]
    rw [div_eq_div_iff (by intro hc; linarith) (by intro hc; linarith)]
    ring
  rw [h1, smul_eq_mul, show L * -σ = -σ * L from mul_comm L (-σ)]

/-! ## The simple pole: the witness lies in the critical clock class -/

/-- The witness source has a simple pole at `σ = 1` with residue one, exactly like the squarefree
Möbius partition function. -/
theorem tendsto_blindWitnessMellinReal_simplePole (m L : ℝ) :
    Tendsto (fun σ : ℝ => (σ - 1) * blindWitnessMellinReal m L σ) (𝓝[>] 1) (𝓝 1) := by
  have hmain : Tendsto (fun σ : ℝ => 1 + (σ - 1) * (m * Real.exp (-σ * L)))
      (𝓝[>] 1) (𝓝 1) := by
    have hc : Continuous (fun σ : ℝ => 1 + (σ - 1) * (m * Real.exp (-σ * L))) := by fun_prop
    have h := (hc.continuousAt (x := (1 : ℝ))).tendsto
    simp only [sub_self, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ1 : σ - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hσ)
  rw [blindWitnessMellinReal, mul_add, mul_inv_cancel₀ hσ1]

/-- Consequently the witness has exactly the unit-rate exponential critical clock — the same
critical clock as the squarefree Möbius source, hence the same truncated Gram triple, the same
rank-two Ward profile, the same one-corner profile, and the same four-unit budget. -/
theorem tendsto_blindWitness_criticalClockLaplace (m L : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (criticalClockLaplace (blindWitnessMellinReal m L) u) (𝓝[>] 1)
      (𝓝 (1 / (1 + u))) :=
  tendsto_criticalClockLaplace_of_simplePole one_ne_zero
    (tendsto_blindWitnessMellinReal_simplePole m L) hu

/-! ## The Möbius Ward profile is the exponential-clock functional -/

/-- The closed critical Ward profile of the squarefree Möbius source **is** the rank-two cutoff
Gram of the three truncated `Exp(1)` moments.  Nothing about the primes survives in it. -/
theorem squarefreeMobiusCriticalFisherCutoffWardLimit_eq_exponentialClockWardProfile (u : ℝ) :
    squarefreeMobiusCriticalFisherCutoffWardLimit u = exponentialClockWardProfile u := rfl

/-- The same statement for the one-corner (four-unit) profile. -/
theorem squarefreeMobiusCriticalFisherLowerBoundaryLimit_eq_exponentialClockWardProfile (u : ℝ) :
    squarefreeMobiusCriticalFisherLowerBoundaryLimit u = exponentialClockWardProfile u / 2 := rfl

/-- Hence the four-unit budget of the Möbius source is the rank-two cutoff Gram of the truncated
`Exp(1)` moments, and is therefore shared by every source with the same critical clock. -/
theorem squarefreeMobiusCriticalFisherLowerBoundaryLimit_eq_gram (u : ℝ) :
    squarefreeMobiusCriticalFisherLowerBoundaryLimit u =
      fisherCutoffWardGram (exponentialCutMass u) (exponentialCutEnergy u)
        (exponentialCutOverlap u) / 2 := by
  rw [squarefreeMobiusCriticalFisherLowerBoundaryLimit_eq_exponentialClockWardProfile,
    fisherCutoffWardGram_exponentialClock]

/-! ## The off-critical zero -/

/-- Log-position of the atom realizing a prescribed off-critical zero. -/
def blindWitnessPhase (θ a : ℝ) : ℝ :=
  (2 * Real.pi - ((1 - ((θ : ℂ) + (a : ℂ) * I))⁻¹).arg) / a

/-- Atom mass realizing a prescribed off-critical zero. -/
def blindWitnessMass (θ a : ℝ) : ℝ :=
  ‖(1 - ((θ : ℂ) + (a : ℂ) * I))⁻¹‖ * Real.exp (θ * blindWitnessPhase θ a)

theorem blindWitnessPhase_pos {θ a : ℝ} (ha : 0 < a) : 0 < blindWitnessPhase θ a := by
  have harg := Complex.arg_le_pi ((1 - ((θ : ℂ) + (a : ℂ) * I))⁻¹)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  unfold blindWitnessPhase
  apply div_pos _ ha
  linarith

theorem blindWitness_w_ne_zero {θ a : ℝ} (ha : 0 < a) :
    (1 - ((θ : ℂ) + (a : ℂ) * I))⁻¹ ≠ 0 := by
  apply inv_ne_zero
  intro h
  have him : (1 - ((θ : ℂ) + (a : ℂ) * I)).im = 0 := by rw [h]; simp
  simp at him
  exact absurd him (ne_of_gt ha)

theorem blindWitnessMass_pos {θ a : ℝ} (ha : 0 < a) : 0 < blindWitnessMass θ a := by
  unfold blindWitnessMass
  exact mul_pos (norm_pos_iff.mpr (blindWitness_w_ne_zero ha)) (Real.exp_pos _)

/-- The atom term of the witness at the prescribed node reproduces `(1-ρ)⁻¹` exactly. -/
theorem blindWitness_atom_eq {θ a : ℝ} (ha : 0 < a) :
    ((blindWitnessMass θ a : ℝ) : ℂ) *
        Complex.exp (-((θ : ℂ) + (a : ℂ) * I) * ((blindWitnessPhase θ a : ℝ) : ℂ))
      = (1 - ((θ : ℂ) + (a : ℂ) * I))⁻¹ := by
  set L : ℝ := blindWitnessPhase θ a with hLdef
  set w : ℂ := (1 - ((θ : ℂ) + (a : ℂ) * I))⁻¹ with hwdef
  have haL : a * L = 2 * Real.pi - w.arg := by
    rw [hLdef, blindWitnessPhase, ← hwdef]
    field_simp
  have hsplit : -((θ : ℂ) + (a : ℂ) * I) * (L : ℂ)
      = ((-(θ * L) : ℝ) : ℂ) + ((-(a * L) : ℝ) : ℂ) * I := by
    push_cast; ring
  have hphase : Complex.exp (((-(a * L) : ℝ) : ℂ) * I) = Complex.exp ((w.arg : ℂ) * I) := by
    rw [haL]
    have hrw : ((-(2 * Real.pi - w.arg) : ℝ) : ℂ) * I
        = (w.arg : ℂ) * I + -(2 * (Real.pi : ℂ) * I) := by
      push_cast; ring
    rw [hrw, Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I]
    simp
  have hmassR : blindWitnessMass θ a * Real.exp (-(θ * L)) = ‖w‖ := by
    rw [blindWitnessMass, ← hLdef, ← hwdef, mul_assoc, ← Real.exp_add]
    simp
  have hmass : ((blindWitnessMass θ a : ℝ) : ℂ) * Complex.exp (((-(θ * L) : ℝ) : ℂ))
      = ((‖w‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, hmassR]
  calc ((blindWitnessMass θ a : ℝ) : ℂ) *
        Complex.exp (-((θ : ℂ) + (a : ℂ) * I) * ((L : ℝ) : ℂ))
      = ((blindWitnessMass θ a : ℝ) : ℂ) *
          (Complex.exp (((-(θ * L) : ℝ) : ℂ)) * Complex.exp (((-(a * L) : ℝ) : ℂ) * I)) := by
        rw [hsplit, Complex.exp_add]
    _ = (((blindWitnessMass θ a : ℝ) : ℂ) * Complex.exp (((-(θ * L) : ℝ) : ℂ))) *
          Complex.exp ((w.arg : ℂ) * I) := by rw [hphase]; ring
    _ = ((‖w‖ : ℝ) : ℂ) * Complex.exp ((w.arg : ℂ) * I) := by rw [hmass]
    _ = w := Complex.norm_mul_exp_arg_mul_I w

/-- **The witness has a prescribed off-critical zero.** -/
theorem blindWitnessMellin_eq_zero {θ a : ℝ} (ha : 0 < a) :
    blindWitnessMellin (blindWitnessMass θ a) (blindWitnessPhase θ a)
      ((θ : ℂ) + (a : ℂ) * I) = 0 := by
  rw [blindWitnessMellin, blindWitness_atom_eq ha]
  have hneg : ((θ : ℂ) + (a : ℂ) * I) - 1 = -(1 - ((θ : ℂ) + (a : ℂ) * I)) := by ring
  rw [hneg, inv_neg]
  ring

/-- The witness is real on the real axis, so its zeros come in conjugate pairs. -/
theorem blindWitnessMellin_conj (m L : ℝ) (s : ℂ) :
    blindWitnessMellin m L (starRingEnd ℂ s) = starRingEnd ℂ (blindWitnessMellin m L s) := by
  rw [blindWitnessMellin, blindWitnessMellin]
  rw [map_add, map_mul, map_inv₀, map_sub, ← Complex.exp_conj]
  simp

theorem blindWitnessMellin_eq_zero_conj {θ a : ℝ} (ha : 0 < a) :
    blindWitnessMellin (blindWitnessMass θ a) (blindWitnessPhase θ a)
      ((θ : ℂ) - (a : ℂ) * I) = 0 := by
  have h := blindWitnessMellin_eq_zero (θ := θ) ha
  have hc := blindWitnessMellin_conj (blindWitnessMass θ a) (blindWitnessPhase θ a)
    ((θ : ℂ) + (a : ℂ) * I)
  have hstar : (starRingEnd ℂ) ((θ : ℂ) + (a : ℂ) * I) = (θ : ℂ) - (a : ℂ) * I := by
    simp [Complex.ext_iff]
  rw [hstar, h] at hc
  simpa using hc

/-! ## Cauchy energy of one strict-right Schwarz pair -/

/-- Schwarz-paired Cauchy (Ward) energy of a single strict-right divisor point with centred
coordinate `lam`.  This is `‖2·k_{conj lam} + 2·k_{lam}‖²` in the right half-plane Hardy space
with Szegő kernel `k_v(w) = (w + conj v)⁻¹`. -/
def schwarzPairCauchyEnergy (lam : ℂ) : ℝ :=
  4 * (1 / lam.re + lam.re / (lam.re ^ 2 + lam.im ^ 2))

/-- Gram expansion of the Schwarz-paired Cauchy energy: the three Szegő kernel values of the pair
`{lam, conj lam}` assemble exactly into `schwarzPairCauchyEnergy`. -/
theorem schwarzPairCauchyEnergy_eq_gram {lam : ℂ} (h : 0 < lam.re) :
    4 * (((lam + (starRingEnd ℂ) lam)⁻¹).re + ((lam + (starRingEnd ℂ) lam)⁻¹).re
        + 2 * ((lam + lam)⁻¹).re) = schwarzPairCauchyEnergy lam := by
  have hsq : 0 < lam.re ^ 2 := pow_pos h 2
  have hns : lam.re ^ 2 + lam.im ^ 2 ≠ 0 := by nlinarith [sq_nonneg lam.im]
  have hd1 : (lam.re + lam.re) * (lam.re + lam.re) + (lam.im + lam.im) * (lam.im + lam.im)
      ≠ 0 := by nlinarith [sq_nonneg lam.im]
  have hd2 : (2 : ℝ) * (lam.re ^ 2 + lam.im ^ 2) ≠ 0 := by
    intro hc; apply hns; linarith
  have hA : ((lam + (starRingEnd ℂ) lam)⁻¹).re = 1 / (2 * lam.re) := by
    rw [Complex.add_conj, ← Complex.ofReal_inv, Complex.ofReal_re]
    field_simp
  have hB : ((lam + lam)⁻¹).re = lam.re / (2 * (lam.re ^ 2 + lam.im ^ 2)) := by
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im]
    rw [div_eq_div_iff hd1 hd2]
    ring
  rw [hA, hB, schwarzPairCauchyEnergy]
  field_simp
  ring

/-- **One strict-right pair already overspends the two-quantum budget.**  A divisor point whose
centred abscissa `Re lam = Re ρ - 1/2` lies in `(0, 1/2)` contributes more than eight units, so it
violates the corner-lift law at every admissible threshold `c ∈ [0,8]`. -/
theorem schwarzPairCauchyEnergy_gt_eight {lam : ℂ} (h0 : 0 < lam.re) (h1 : lam.re < 1 / 2) :
    8 < schwarzPairCauchyEnergy lam := by
  rw [schwarzPairCauchyEnergy]
  have h2 : 2 < 1 / lam.re := by
    rw [lt_div_iff₀ h0]; linarith
  have h3 : 0 ≤ lam.re / (lam.re ^ 2 + lam.im ^ 2) := by
    apply div_nonneg (le_of_lt h0)
    nlinarith [sq_nonneg lam.re, sq_nonneg lam.im]
  linarith

/-! ## The packaged no-go -/

/-- **CCM critical-clock divisor blindness.**

For every prescribed off-critical abscissa `θ ∈ (1/2,1)` and ordinate `a > 0` there is a
nonnegative Mellin source whose Mellin transform

* is the Mellin transform of an explicit nonnegative measure on `(1,∞)`;
* has a simple pole at `σ = 1` with residue one, hence exactly the same critical clock, the same
  `Exp(1)` law, the same truncated Gram triple, the same rank-two Ward profile, the same one-corner
  profile and the same four-unit budget as the squarefree Möbius source;
* nevertheless vanishes at `θ ± i a`, whose Schwarz-paired Cauchy energy exceeds eight.

Therefore no valid implication can lead from any critical clock functional of the source (in
particular from the four-unit or the eight-unit budget) to a bound on the strict-right Ward
energy: the hypothesis is a class invariant and the conclusion is not. -/
theorem ccm_criticalClock_divisor_blindness {θ a : ℝ}
    (hθ0 : 1 / 2 < θ) (hθ1 : θ < 1) (ha : 0 < a) :
    ∃ m L : ℝ, 0 < m ∧ 0 < L ∧
      (∀ σ : ℝ, 1 < σ →
        blindWitnessMellinReal m L σ = ∫ x, x ^ (-σ) ∂(blindWitnessMeasure m L)) ∧
      Tendsto (fun σ : ℝ => (σ - 1) * blindWitnessMellinReal m L σ) (𝓝[>] 1) (𝓝 1) ∧
      (∀ u : ℝ, 0 ≤ u →
        Tendsto (criticalClockLaplace (blindWitnessMellinReal m L) u) (𝓝[>] 1)
          (𝓝 (1 / (1 + u)))) ∧
      blindWitnessMellin m L ((θ : ℂ) + (a : ℂ) * I) = 0 ∧
      blindWitnessMellin m L ((θ : ℂ) - (a : ℂ) * I) = 0 ∧
      8 < schwarzPairCauchyEnergy ((θ - 1 / 2 : ℝ) + (a : ℝ) * I) := by
  have hmpos := blindWitnessMass_pos (θ := θ) ha
  refine ⟨blindWitnessMass θ a, blindWitnessPhase θ a, hmpos,
    blindWitnessPhase_pos ha,
    fun σ hσ => blindWitnessMellinReal_eq_integral (le_of_lt hmpos) hσ,
    tendsto_blindWitnessMellinReal_simplePole _ _,
    fun u hu => tendsto_blindWitness_criticalClockLaplace _ _ hu,
    blindWitnessMellin_eq_zero ha, blindWitnessMellin_eq_zero_conj ha, ?_⟩
  apply schwarzPairCauchyEnergy_gt_eight
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith

/-- **Headline form.**  The one-corner four-unit source profile of the squarefree Möbius source is
literally the rank-two cutoff Gram of the three truncated `Exp(1)` moments, while the strict-right
divisor is not determined by that clock: an explicit nonnegative Mellin source with the very same
simple pole, hence the very same critical clock, has a zero at `θ ± i a` whose Schwarz-paired
Cauchy energy exceeds eight.

So the four-unit (and eight-unit) source budget is a class invariant of the critical clock, while
the quantity it is asked to bound is not.  No transport, of any operator shape, can derive the
Ward bound from that budget alone. -/
theorem fourUnitBudget_classInvariant_but_divisor_not {θ a : ℝ}
    (hθ0 : 1 / 2 < θ) (hθ1 : θ < 1) (ha : 0 < a) :
    (∀ u : ℝ, squarefreeMobiusCriticalFisherLowerBoundaryLimit u =
        fisherCutoffWardGram (exponentialCutMass u) (exponentialCutEnergy u)
          (exponentialCutOverlap u) / 2) ∧
    ∃ m L : ℝ, 0 < m ∧ 0 < L ∧
      (∀ σ : ℝ, 1 < σ →
        blindWitnessMellinReal m L σ = ∫ x, x ^ (-σ) ∂(blindWitnessMeasure m L)) ∧
      Tendsto (fun σ : ℝ => (σ - 1) * blindWitnessMellinReal m L σ) (𝓝[>] 1) (𝓝 1) ∧
      (∀ u : ℝ, 0 ≤ u →
        Tendsto (criticalClockLaplace (blindWitnessMellinReal m L) u) (𝓝[>] 1)
          (𝓝 (1 / (1 + u)))) ∧
      blindWitnessMellin m L ((θ : ℂ) + (a : ℂ) * I) = 0 ∧
      blindWitnessMellin m L ((θ : ℂ) - (a : ℂ) * I) = 0 ∧
      8 < schwarzPairCauchyEnergy ((θ - 1 / 2 : ℝ) + (a : ℝ) * I) :=
  ⟨squarefreeMobiusCriticalFisherLowerBoundaryLimit_eq_gram,
    ccm_criticalClock_divisor_blindness hθ0 hθ1 ha⟩

end RHTower
