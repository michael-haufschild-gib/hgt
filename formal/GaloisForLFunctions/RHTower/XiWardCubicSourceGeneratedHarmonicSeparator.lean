import GaloisForLFunctions.RHTower.XiWardCubicTranslationEnergySeparator
import GaloisForLFunctions.RHTower.XiWardCubicIntegerHarmonicDephasing

/-!
# Source-generated cubic harmonic separator

The horizontal cubic Hellinger feature is the energy difference of fixed normalized real source
translations at scales `r / 2` and `r`.  The vertical projector is the logarithmic harmonic
correlation of fixed normalized integer translations.  Their finite product trace converges to
the equal-ordinate Hellinger fibre, excludes critical-line displacement, and charges every
strict-right multiplicity copy by at least `115 / 108`.

Each scalar factor has an exact pre-divisor source construction.  This module does not identify
their nonlinear product with a completed Euler--Gamma trace or prove its height-local upper bound.
-/

open scoped BigOperators
open Complex Filter Topology Finset

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Finite cubic Hellinger trace with source-native integer-harmonic ordinate dephasing. -/
def finiteSourceGeneratedCubicHarmonicTrace {ι : Type*}
    (s : Finset ι) (a gamma : ι → ℝ) (m : ι → ℕ) (N : ℕ) : ℂ :=
  ∑ p ∈ s.product s,
    ((m p.1 : ℝ) * (m p.2 : ℝ) : ℂ) *
      (cubicLogMomentHellingerHorizontalKernel (a p.1) (a p.2) : ℂ) *
        integerHarmonicOrdinateKernel (gamma p.1 - gamma p.2) N

/-- Equal-ordinate cubic Hellinger energy retained by the source-generated projector. -/
def finiteSourceGeneratedCubicOrdinateFiberEnergy {ι : Type*}
    (s : Finset ι) (a gamma : ι → ℝ) (m : ι → ℕ) : ℝ :=
  ∑ p ∈ s.product s with gamma p.1 = gamma p.2,
    (m p.1 : ℝ) * (m p.2 : ℝ) *
      cubicLogMomentHellingerHorizontalKernel (a p.1) (a p.2)

/-- The combined fixed-source trace converges to exact equal-ordinate multiplicity fibres. -/
theorem tendsto_finiteSourceGeneratedCubicHarmonicTrace {ι : Type*}
    (s : Finset ι) (a gamma : ι → ℝ) (m : ι → ℕ) :
    Tendsto (finiteSourceGeneratedCubicHarmonicTrace s a gamma m) atTop
      (nhds (finiteSourceGeneratedCubicOrdinateFiberEnergy s a gamma m : ℂ)) := by
  classical
  rw [finiteSourceGeneratedCubicOrdinateFiberEnergy, Complex.ofReal_sum]
  simp only [Finset.sum_filter, Complex.ofReal_mul]
  unfold finiteSourceGeneratedCubicHarmonicTrace
  apply tendsto_finsetSum
  intro p hp
  have hphase := tendsto_integerHarmonicOrdinateKernel (gamma p.1 - gamma p.2)
  have hscaled := hphase.const_mul
    (((m p.1 : ℝ) * (m p.2 : ℝ) : ℂ) *
      (cubicLogMomentHellingerHorizontalKernel (a p.1) (a p.2) : ℂ))
  by_cases hgamma : gamma p.1 = gamma p.2
  · have hzero : gamma p.1 - gamma p.2 = 0 := sub_eq_zero.mpr hgamma
    rw [hzero] at hscaled
    rw [if_pos hgamma, hzero]
    push_cast at hscaled ⊢
    simpa using hscaled
  · rw [if_neg hgamma]
    have hne : gamma p.1 - gamma p.2 ≠ 0 := sub_ne_zero.mpr hgamma
    simp only [if_neg hne, mul_zero] at hscaled
    simpa only [if_neg hne, mul_zero] using hscaled

/-- Equal-ordinate mixed entries are nonnegative on positive horizontal displacements. -/
theorem finiteSourceGeneratedCubicOrdinateFiberEnergy_nonneg {ι : Type*}
    (s : Finset ι) {a gamma : ι → ℝ} (m : ι → ℕ)
    (ha : ∀ i ∈ s, 0 < a i) :
    0 ≤ finiteSourceGeneratedCubicOrdinateFiberEnergy s a gamma m := by
  classical
  rw [finiteSourceGeneratedCubicOrdinateFiberEnergy]
  apply Finset.sum_nonneg
  intro p hp
  have hp' := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (cubicLogMomentHellingerHorizontalKernel_pos
      (ha p.1 hp'.1) (ha p.2 hp'.2)).le

/-- The source-generated equal-ordinate fibre retains the uniform cubic self-charge. -/
theorem cubic_mass_le_finiteSourceGeneratedCubicOrdinateFiberEnergy {ι : Type*}
    (s : Finset ι) {a gamma : ι → ℝ} (m : ι → ℕ)
    (ha0 : ∀ i ∈ s, 0 < a i) (ha : ∀ i ∈ s, a i ≤ 1 / 2) :
    (115 / 108) * ∑ i ∈ s, (m i : ℝ) ≤
      finiteSourceGeneratedCubicOrdinateFiberEnergy s a gamma m := by
  classical
  rw [finiteSourceGeneratedCubicOrdinateFiberEnergy]
  let diag : Finset (ι × ι) := s.image fun i => (i, i)
  have hdiag_sub : diag ⊆ (s.product s).filter fun p => gamma p.1 = gamma p.2 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hi⟩, rfl⟩
  have hterm_nonneg : ∀ p ∈ (s.product s).filter fun p => gamma p.1 = gamma p.2,
      0 ≤ (m p.1 : ℝ) * (m p.2 : ℝ) *
        cubicLogMomentHellingerHorizontalKernel (a p.1) (a p.2) := by
    intro p hp
    have hp' := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (cubicLogMomentHellingerHorizontalKernel_pos
        (ha0 p.1 hp'.1) (ha0 p.2 hp'.2)).le
  calc
    (115 / 108) * ∑ i ∈ s, (m i : ℝ) ≤
        ∑ i ∈ s, (m i : ℝ) * (m i : ℝ) *
          cubicLogMomentHellingerHorizontalKernel (a i) (a i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hm : (m i : ℝ) ≤ (m i : ℝ) ^ (2 : ℕ) := by
        by_cases hm0 : m i = 0
        · simp [hm0]
        · have hm1 : (1 : ℝ) ≤ m i := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
          have hmnonneg : (0 : ℝ) ≤ m i := Nat.cast_nonneg _
          nlinarith
      have hkernel := cubicLogMomentHellingerHorizontalKernel_self_ge
        (ha0 i hi) (ha i hi)
      calc
        (115 / 108) * (m i : ℝ) ≤ (115 / 108) * (m i : ℝ) ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hm (by norm_num)
        _ ≤ (m i : ℝ) ^ (2 : ℕ) *
            cubicLogMomentHellingerHorizontalKernel (a i) (a i) := by
          nlinarith [sq_nonneg (m i : ℝ)]
        _ = (m i : ℝ) * (m i : ℝ) *
            cubicLogMomentHellingerHorizontalKernel (a i) (a i) := by ring
    _ = ∑ p ∈ diag, (m p.1 : ℝ) * (m p.2 : ℝ) *
        cubicLogMomentHellingerHorizontalKernel (a p.1) (a p.2) := by
      have hinj : Set.InjOn (fun i : ι => (i, i)) s := by
        intro i hi j hj hij
        exact (Prod.mk.inj hij).1
      dsimp only [diag]
      rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ (s.product s).filter fun p => gamma p.1 = gamma p.2,
        (m p.1 : ℝ) * (m p.2 : ℝ) *
          cubicLogMomentHellingerHorizontalKernel (a p.1) (a p.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hdiag_sub
        (fun p hp _ => hterm_nonneg p hp)

/-- Exact three-quarters receiver for the fully source-generated finite separator. -/
theorem three_quarters_line_of_sourceGeneratedCubicOrdinateFiberEnergy
    {N N0 R E : ℝ} (hsplit : N = N0 + 2 * R)
    (hcharge : (115 / 108) * R ≤ E)
    (hbudget : (108 / 115) * E ≤ N / 8) :
    3 * N / 4 ≤ N0 := by
  nlinarith

end

end RHTower
