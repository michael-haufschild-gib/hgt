import GaloisForLFunctions.RHTower.XiWardCubicLogMomentHellingerCauchySeparator
import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthKreinXiLanding
import GaloisForLFunctions.HTGeometry.BohrParseval

/-!
# Cubic holomorphic height dephasing and the source-translation obstruction

The genuine cubic Laplace kernel has signed cross entries at distinct ordinates.  Exact Bohr
dephasing removes those entries and retains equal-ordinate fibres, where every entry is positive.
The retained diagonal charges each strict-right multiplicity copy by at least two units, uniformly
as its horizontal displacement tends to zero.  This gives the exact `75%` receiver once a
pre-divisor Euler--Gamma trace supplies budget `N/4`.

The same module records the interface obstruction: pure ordinate phases are unitary, whereas
genuine holomorphic translation has modulus `exp (-tau * a)`.  No scalar independent of horizontal
depth can normalize even depths one and two simultaneously.  Thus the Bohr identity is a valid
finite-divisor theorem, but not by itself a source-faithful landing.
-/

open scoped BigOperators
open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-! ## Exact Krein translation dichotomy -/

/-- Common vertical translation of a source parameter. -/
def kreinCommonVerticalShift (tau : ℝ) (z : ℂ) : ℂ :=
  z + (tau : ℂ) * I

theorem kreinCommonVerticalShift_re (tau : ℝ) (z : ℂ) :
    (kreinCommonVerticalShift tau z).re = z.re := by
  simp [kreinCommonVerticalShift, Complex.mul_re]

/-- Conjugate codiagonal erases a common vertical translation completely. -/
theorem kreinCommonVerticalShift_codiagonal (tau : ℝ) (w v : ℂ) :
    kreinCommonVerticalShift tau w +
        star (kreinCommonVerticalShift tau v) =
      w + star v := by
  simp [kreinCommonVerticalShift]
  ring

/-- Every scalar observable factoring through the literal source codiagonal is invariant under
common vertical translation.  Thus an invariant Krein codiagonal cannot also provide ordinate
dephasing. -/
theorem kreinCodiagonalObservable_commonVerticalShift_invariant
    {α : Type*} (F : ℂ → α) (tau : ℝ) (w v : ℂ) :
    F (kreinCommonVerticalShift tau w +
        star (kreinCommonVerticalShift tau v)) =
      F (w + star v) := by
  rw [kreinCommonVerticalShift_codiagonal]

/-- The actual joint-depth Krein coefficient is invariant under common vertical translation. -/
theorem xiGammaEulerPrimitiveJointDepthKreinPair_commonVerticalShift
    (tau : ℝ) (w v : ℂ) (hw : 0 < w.re) (hv : 0 < v.re) :
    xiGammaEulerPrimitiveJointDepthKreinPair
        (xiGammaEulerPrimitiveJointDepthKreinCoSourceLeg
          (kreinCommonVerticalShift tau v) (by
            simpa [kreinCommonVerticalShift_re] using hv))
        (xiGammaEulerPrimitiveJointDepthKreinSourceLeg
          (kreinCommonVerticalShift tau w) (by
            simpa [kreinCommonVerticalShift_re] using hw)) =
      xiGammaEulerPrimitiveJointDepthKreinPair
        (xiGammaEulerPrimitiveJointDepthKreinCoSourceLeg v hv)
        (xiGammaEulerPrimitiveJointDepthKreinSourceLeg w hw) := by
  rw [xiGammaEulerPrimitiveJointDepthKreinPair_coSource_source_eq,
    xiGammaEulerPrimitiveJointDepthKreinPair_coSource_source_eq,
    kreinCommonVerticalShift_codiagonal]

/-- Opposite shifts retain source visibility, but move the scalar spectral parameter by
`2 i tau`; they do not multiply a fixed zero fibre by a unitary ordinate character. -/
theorem kreinOppositeVerticalShift_codiagonal (tau : ℝ) (w v : ℂ) :
    kreinCommonVerticalShift tau w +
        star (kreinCommonVerticalShift (-tau) v) =
      w + star v + 2 * (tau : ℂ) * I := by
  simp [kreinCommonVerticalShift]
  ring

theorem xiGammaEulerPrimitiveJointDepthKreinPair_oppositeVerticalShift
    (tau : ℝ) (w v : ℂ) (hw : 0 < w.re) (hv : 0 < v.re) :
    xiGammaEulerPrimitiveJointDepthKreinPair
        (xiGammaEulerPrimitiveJointDepthKreinCoSourceLeg
          (kreinCommonVerticalShift (-tau) v) (by
            simpa [kreinCommonVerticalShift_re] using hv))
        (xiGammaEulerPrimitiveJointDepthKreinSourceLeg
          (kreinCommonVerticalShift tau w) (by
            simpa [kreinCommonVerticalShift_re] using hw)) =
      vonMangoldtPrimeLaplaceChannelComplex
        (w + star v + 2 * (tau : ℂ) * I) := by
  rw [xiGammaEulerPrimitiveJointDepthKreinPair_coSource_source_eq,
    kreinOppositeVerticalShift_codiagonal]

/-- Genuine one-variable cubic Laplace Gram entry. -/
def holomorphicCubicLaplaceKernel (x delta : ℝ) : ℂ :=
  2 / ((x : ℂ) + (delta : ℂ) * I) ^ 3

/-- Holomorphic translation character of a right-half-plane point `a+i gamma`. -/
def holomorphicHeightTranslate (tau a gamma : ℝ) : ℂ :=
  Complex.exp (-(tau : ℂ) * ((a : ℂ) + (gamma : ℂ) * I))

/-- Pure ordinate phase required by exact height dephasing. -/
def ordinateUnitaryPhase (tau gamma : ℝ) : ℂ :=
  Complex.exp (-((tau * gamma : ℝ) : ℂ) * I)

theorem norm_holomorphicHeightTranslate (tau a gamma : ℝ) :
    ‖holomorphicHeightTranslate tau a gamma‖ = Real.exp (-tau * a) := by
  rw [holomorphicHeightTranslate, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem norm_ordinateUnitaryPhase (tau gamma : ℝ) :
    ‖ordinateUnitaryPhase tau gamma‖ = 1 := by
  simpa [ordinateUnitaryPhase] using
    Complex.norm_exp_ofReal_mul_I (-(tau * gamma))

/-- No scalar normalization independent of horizontal depth can turn genuine holomorphic
translation into the unitary ordinate phase, already at depths `1` and `2`. -/
theorem not_exists_scalar_normalizer_holomorphicHeightTranslate
    {tau : ℝ} (htau : 0 < tau) :
    ¬ ∃ c : ℂ,
      ‖c * holomorphicHeightTranslate tau 1 0‖ = 1 ∧
        ‖c * holomorphicHeightTranslate tau 2 0‖ = 1 := by
  rintro ⟨c, h1, h2⟩
  rw [norm_mul, norm_holomorphicHeightTranslate] at h1 h2
  have hc : 0 < ‖c‖ := by
    by_contra h
    have hc0 : ‖c‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hc0, zero_mul] at h1
    norm_num at h1
  have hexp : Real.exp (-tau * 2) < Real.exp (-tau * 1) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  nlinarith

theorem holomorphicCubicLaplaceKernel_zero_gap (x : ℝ) :
    holomorphicCubicLaplaceKernel x 0 = (2 / x ^ 3 : ℝ) := by
  rw [holomorphicCubicLaplaceKernel]
  norm_num

/-- Phase-modulated finite cubic Gram trace. -/
def finiteHolomorphicCubicPhaseTrace {ι : Type*}
    (s : Finset ι) (a gamma : ι → ℝ) (m : ι → ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ s.product s,
    ((m p.1 : ℝ) * (m p.2 : ℝ) : ℂ) *
      holomorphicCubicLaplaceKernel (a p.1 + a p.2) (gamma p.1 - gamma p.2) *
        bohrChar (gamma p.1 - gamma p.2) t

/-- Equal-ordinate cubic energy retained after exact height dephasing. -/
def finiteHolomorphicCubicOrdinateFiberEnergy {ι : Type*}
    (s : Finset ι) (a gamma : ι → ℝ) (m : ι → ℕ) : ℝ :=
  ∑ p ∈ s.product s with gamma p.1 = gamma p.2,
    (m p.1 : ℝ) * (m p.2 : ℝ) * (2 / (a p.1 + a p.2) ^ 3)

/-- Bohr mean deletes every distinct-ordinate cubic cross entry and retains the complete
equal-ordinate fibre. -/
theorem bohrMean_finiteHolomorphicCubicPhaseTrace {ι : Type*}
    (s : Finset ι) (a gamma : ι → ℝ) (m : ι → ℕ) :
    bohrMean (finiteHolomorphicCubicPhaseTrace s a gamma m) =
      (finiteHolomorphicCubicOrdinateFiberEnergy s a gamma m : ℂ) := by
  classical
  change bohrMean (fun t => ∑ p ∈ s.product s,
    ((m p.1 : ℝ) * (m p.2 : ℝ) : ℂ) *
      holomorphicCubicLaplaceKernel (a p.1 + a p.2) (gamma p.1 - gamma p.2) *
        bohrChar (gamma p.1 - gamma p.2) t) = _
  rw [bohrMean_sum]
  · rw [finiteHolomorphicCubicOrdinateFiberEnergy, Complex.ofReal_sum]
    simp only [Finset.sum_filter, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro p hp
    rw [bohrMean_const_mul _ (continuous_bohrChar _)
      (isBohrAlmostPeriodic_bohrChar _)]
    rw [bohrMean_bohrChar]
    by_cases hgamma : gamma p.1 = gamma p.2
    · rw [if_pos hgamma, if_pos (sub_eq_zero.mpr hgamma), mul_one]
      simp only [hgamma, sub_self, holomorphicCubicLaplaceKernel_zero_gap]
      norm_num
    · rw [if_neg hgamma, if_neg (sub_ne_zero.mpr hgamma), mul_zero]
  · intro p hp
    exact continuous_const.mul (continuous_bohrChar _)
  · intro p hp
    exact isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_bohrChar _)

/-- On strict-right depths at most `1/2`, retained equal-ordinate energy is at least twice total
multiplicity.  Mixed terms inside each height fibre are positive. -/
theorem two_mul_sum_multiplicity_le_finiteHolomorphicCubicOrdinateFiberEnergy
    {ι : Type*} (s : Finset ι) (a gamma : ι → ℝ) (m : ι → ℕ)
    (ha0 : ∀ i ∈ s, 0 < a i) (ha : ∀ i ∈ s, a i ≤ 1 / 2) :
    2 * ∑ i ∈ s, (m i : ℝ) ≤
      finiteHolomorphicCubicOrdinateFiberEnergy s a gamma m := by
  classical
  rw [finiteHolomorphicCubicOrdinateFiberEnergy]
  let diag : Finset (ι × ι) := s.image fun i => (i, i)
  have hdiag_sub : diag ⊆ (s.product s).filter fun p => gamma p.1 = gamma p.2 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hi⟩, rfl⟩
  have hterm_nonneg : ∀ p ∈ (s.product s).filter fun p => gamma p.1 = gamma p.2,
      0 ≤ (m p.1 : ℝ) * (m p.2 : ℝ) * (2 / (a p.1 + a p.2) ^ 3) := by
    intro p hp
    have hp' := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have hden : 0 < (a p.1 + a p.2) ^ 3 := by
      positivity [ha0 p.1 hp'.1, ha0 p.2 hp'.2]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (by norm_num) hden.le)
  calc
    2 * ∑ i ∈ s, (m i : ℝ) ≤
        ∑ i ∈ s, (m i : ℝ) * (m i : ℝ) * (2 / (a i + a i) ^ 3) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i hi
          have hmi : (m i : ℝ) ≤ (m i : ℝ) ^ 2 := by
            have hm : (m i : ℝ) = 0 ∨ 1 ≤ (m i : ℝ) := by
              exact_mod_cast (Nat.eq_zero_or_pos (m i))
            rcases hm with hm | hm
            · simp [hm]
            · nlinarith
          have hself : 2 ≤ 2 / (a i + a i) ^ 3 := by
            have hai := ha i hi
            have hai0 := ha0 i hi
            rw [show a i + a i = 2 * a i by ring]
            rw [le_div_iff₀ (by positivity : 0 < (2 * a i) ^ 3)]
            nlinarith [sq_nonneg (a i), mul_self_nonneg (a i - 1 / 2)]
          calc
            2 * (m i : ℝ) ≤ 2 * (m i : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hmi (by norm_num)
            _ = (m i : ℝ) ^ 2 * 2 := by ring
            _ ≤ (m i : ℝ) ^ 2 * (2 / (a i + a i) ^ 3) :=
              mul_le_mul_of_nonneg_left hself (sq_nonneg _)
            _ = (m i : ℝ) * (m i : ℝ) * (2 / (a i + a i) ^ 3) := by ring
    _ = ∑ p ∈ diag,
        (m p.1 : ℝ) * (m p.2 : ℝ) * (2 / (a p.1 + a p.2) ^ 3) := by
          have hinj : Set.InjOn (fun i : ι => (i, i)) s := by
            intro i hi j hj hij
            exact (Prod.mk.inj hij).1
          dsimp only [diag]
          rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ (s.product s).filter fun p => gamma p.1 = gamma p.2,
        (m p.1 : ℝ) * (m p.2 : ℝ) * (2 / (a p.1 + a p.2) ^ 3) :=
          Finset.sum_le_sum_of_subset_of_nonneg hdiag_sub
            (fun p hp _ => hterm_nonneg p hp)

/-- Exact `75%` receiver after height dephasing: if the cubic ordinate-fibre energy has
budget `N/4`, strict-right multiplicity consumes at most one eighth of the full census. -/
theorem three_quarters_line_of_holomorphicCubicOrdinateFiberEnergy
    {N N0 R E : ℝ} (hcount : N = N0 + 2 * R)
    (hcharge : 2 * R ≤ E) (hbudget : E ≤ N / 4) :
    3 * N / 4 ≤ N0 := by
  linarith

end

end RHTower
