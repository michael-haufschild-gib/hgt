import GaloisForLFunctions.RHTower.XiMassHeightTransfer
import GaloisForLFunctions.RHTower.XiOrdinateBandCopies
import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision

/-!
# The Riemann–von Mangoldt asymptotic

The symmetric divisor mass counts the `ξ`-zeros of ordinate modulus at most `T`.  Conjugation is a
multiplicity-preserving involution of the divisor with no fixed point — `ξ` has no real zero — so the
mass splits into two equal halves, and the upper half is exactly the counting function `N(T)`.
Combined with the sharp mass asymptotic this gives

```text
N(T) = (1/2π)·T log T·(1 + o(1)),
```

unconditionally.
-/

open Complex Set


noncomputable section

namespace RHTower

/-- The `ξ`-divisor supports with ordinate in `(0, T]`. -/
def xiSupportsPos (T : ℝ) : Finset XiDivisorSupport :=
  (xiSupportsUpTo_finite T).toFinset.filter (fun ρ : XiDivisorSupport => 0 < (ρ : ℂ).im)

theorem mem_xiSupportsPos {T : ℝ} {ρ : XiDivisorSupport} :
    ρ ∈ xiSupportsPos T ↔ |(ρ : ℂ).im| ≤ T ∧ 0 < (ρ : ℂ).im := by
  classical
  rw [xiSupportsPos, Finset.mem_filter, Set.Finite.mem_toFinset]
  rfl

/-- No `ξ`-divisor support is real. -/
theorem xiSupport_im_ne_zero (ρ : XiDivisorSupport) : (ρ : ℂ).im ≠ 0 := by
  intro him
  have hzero : xi (ρ : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support ρ
  have hreal : (ρ : ℂ) = (((ρ : ℂ).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hreal] at hzero
  exact xi_ne_zero_of_ofReal _ hzero

/-- Conjugation of a divisor support. -/
def xiSupportConj (ρ : XiDivisorSupport) : XiDivisorSupport :=
  ⟨(starRingEnd ℂ) (ρ : ℂ), by
    apply Function.mem_support.mpr
    rw [xi_divisor_conj]
    exact Function.mem_support.mp ρ.2⟩

theorem xiSupportConj_coe (ρ : XiDivisorSupport) :
    ((xiSupportConj ρ : XiDivisorSupport) : ℂ) = (starRingEnd ℂ) (ρ : ℂ) := rfl

theorem xiSupportMultiplicity_conj (ρ : XiDivisorSupport) :
    xiSupportMultiplicity (xiSupportConj ρ) = xiSupportMultiplicity ρ := by
  rw [xiSupportMultiplicity, xiSupportMultiplicity, xiSupportConj_coe, xi_divisor_conj]

/-- The symmetric mass splits into two equal halves. -/
theorem xiSymmetricMass_eq_two_mul_pos {T : ℝ} (hT : 0 ≤ T) :
    xiSymmetricMass T = 2 * ∑ ρ ∈ xiSupportsPos T, (xiSupportMultiplicity ρ : ℤ) := by
  classical
  rw [xiSymmetricMass_eq_support_sum hT]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((xiSupportsUpTo_finite T).toFinset) (fun ρ : XiDivisorSupport => 0 < (ρ : ℂ).im)
    (fun ρ : XiDivisorSupport => (xiSupportMultiplicity ρ : ℤ))
  have hbij : ∑ ρ ∈ (xiSupportsUpTo_finite T).toFinset.filter
        (fun ρ : XiDivisorSupport => ¬ 0 < (ρ : ℂ).im),
      (xiSupportMultiplicity ρ : ℤ)
      = ∑ ρ ∈ xiSupportsPos T, (xiSupportMultiplicity ρ : ℤ) := by
    refine Finset.sum_nbij' (i := fun ρ : XiDivisorSupport => xiSupportConj ρ)
      (j := fun ρ : XiDivisorSupport => xiSupportConj ρ) ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
      have hne : (ρ : ℂ).im ≠ 0 := xiSupport_im_ne_zero ρ
      have hneg : (ρ : ℂ).im < 0 := lt_of_le_of_ne (not_lt.mp hρ.2) hne
      rw [mem_xiSupportsPos]
      have hc : ((xiSupportConj ρ : XiDivisorSupport) : ℂ).im = -(ρ : ℂ).im := by
        rw [xiSupportConj_coe, Complex.conj_im]
      constructor
      · rw [hc, abs_neg]; exact hρ.1
      · rw [hc]; linarith
    · intro ρ hρ
      rw [mem_xiSupportsPos] at hρ
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      have hc : ((xiSupportConj ρ : XiDivisorSupport) : ℂ).im = -(ρ : ℂ).im := by
        rw [xiSupportConj_coe, Complex.conj_im]
      refine ⟨?_, ?_⟩
      · show |((xiSupportConj ρ : XiDivisorSupport) : ℂ).im| ≤ T
        rw [hc, abs_neg]; exact hρ.1
      · rw [hc]; linarith [hρ.2]
    · intro ρ _
      exact Subtype.ext (by simp [xiSupportConj_coe])
    · intro ρ _
      exact Subtype.ext (by simp [xiSupportConj_coe])
    · intro ρ _
      rw [xiSupportMultiplicity_conj]
  rw [← hsplit, hbij, ← xiSupportsPos]
  ring

/-! ## The positive-ordinate count -/

theorem mem_xiCountingBox_of_xiSupportsPos {T : ℝ} {ρ : XiDivisorSupport}
    (hρ : ρ ∈ xiSupportsPos T) : (ρ : ℂ) ∈ xiCountingBox T := by
  rw [mem_xiSupportsPos] at hρ
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support ρ)
  refine ⟨⟨h0.le, h1.le⟩, ⟨hρ.2.le, ?_⟩⟩
  have := (abs_le.mp hρ.1).2
  linarith

theorem xiZeroCount_eq_pos_sum {T : ℝ} (_hT : 0 ≤ T) :
    xiZeroCount T = ∑ ρ ∈ xiSupportsPos T, (xiSupportMultiplicity ρ : ℤ) := by
  classical
  set S : Finset XiDivisorSupport := xiSupportsPos T with hSdef
  have hinj : Set.InjOn (fun ρ : XiDivisorSupport => (ρ : ℂ)) ↑S :=
    fun a _ b _ h => Subtype.ext h
  have hsupp : Function.support (fun u : ℂ => (MeromorphicOn.divisor xi (xiCountingBox T) u : ℤ))
      ⊆ ↑(S.image (fun ρ : XiDivisorSupport => (ρ : ℂ))) := by
    intro u hu
    rw [Function.mem_support] at hu
    have humem : u ∈ xiCountingBox T := by
      by_contra hmem
      exact hu (xi_divisor_apply_of_notMem hmem)
    have hord : analyticOrderAt xi u ≠ 0 := by
      intro h0
      refine hu ?_
      rw [xi_divisor_apply_of_mem humem, h0]
      rfl
    have hzero : xi u = 0 := by
      by_contra hne
      exact hord (analyticOrderAt_eq_zero.mpr (Or.inr hne))
    have hdivne : (MeromorphicOn.divisor xi Set.univ) u ≠ 0 := by
      rw [xi_divisor_apply_of_mem (Set.mem_univ u)]
      intro h
      refine hord ?_
      have hz : (analyticOrderAt xi u).toNat = 0 := by exact_mod_cast h
      rw [← ENat.coe_toNat (xi_orderAt_ne_top u), hz]
      rfl
    have hρmem : u ∈ (MeromorphicOn.divisor xi Set.univ).support := Function.mem_support.mpr hdivne
    set ρ : XiDivisorSupport := ⟨u, hρmem⟩ with hρdef
    have hne : (ρ : ℂ).im ≠ 0 := xiSupport_im_ne_zero ρ
    have hpos : 0 < u.im := lt_of_le_of_ne humem.2.1 (Ne.symm hne)
    have habs : |u.im| ≤ T := by
      rw [abs_of_nonneg humem.2.1]
      exact humem.2.2
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ρ, ?_, rfl⟩)
    rw [hSdef, mem_xiSupportsPos]
    exact ⟨habs, hpos⟩
  rw [xiZeroCount, xiRegionOrderSum, finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun a ha b hb h => hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h)]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [xi_divisor_apply_of_mem (mem_xiCountingBox_of_xiSupportsPos (hSdef ▸ hρ)),
    xiSupportMultiplicity_eq_analyticOrderAt_toNat]

/-- **The symmetric mass is twice the zero count.** -/
theorem xiSymmetricMass_eq_two_mul_xiZeroCount {T : ℝ} (hT : 0 ≤ T) :
    xiSymmetricMass T = 2 * xiZeroCount T := by
  rw [xiSymmetricMass_eq_two_mul_pos hT, xiZeroCount_eq_pos_sum hT]

/-- **The Riemann–von Mangoldt asymptotic.**  `N(T) = (1/2π)·T log T·(1 + o(1))`. -/
theorem exists_xiZeroCount_close (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |(xiZeroCount T : ℝ) - (1 / (2 * Real.pi)) * (T * Real.log T)|
        ≤ ε * (T * Real.log T) := by
  obtain ⟨T₀, hT₀, hclose⟩ := exists_xiSymmetricMass_close (2 * ε) (by linarith)
  refine ⟨T₀, hT₀, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hb := hclose T hT
  have heq : (xiSymmetricMass T : ℝ) = 2 * (xiZeroCount T : ℝ) := by
    have := xiSymmetricMass_eq_two_mul_xiZeroCount hT0
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) this
  rw [heq] at hb
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hrw : 2 * (xiZeroCount T : ℝ) - 1 / Real.pi * (T * Real.log T)
      = 2 * ((xiZeroCount T : ℝ) - (1 / (2 * Real.pi)) * (T * Real.log T)) := by
    field_simp
  rw [hrw, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hb
  linarith

end RHTower

end
