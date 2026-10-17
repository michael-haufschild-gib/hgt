import GaloisForLFunctions.BiScaleUncertainty.CappedSupportComparison

/-!
# Exact activation of signed capped support

The two largest low-weight fractions decide whether the paired constraints
reduce the independent support. Zero blocks impose no constraint. An attained
disk point also gives a quadratic deficit, without an optimizer premise.
-/

set_option autoImplicit false
open Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
variable {ι : Type*}

/-- The support deficit is the squared distance from its uncapped extremal ray. -/
theorem cappedBlockSupport_deficit_attained (L H : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ x z : ℝ, 0 ≤ x ∧ x ≤ t ∧ 0 ≤ z ∧ x ^ 2 + z ^ 2 = 1 ∧
      2 * Real.sqrt (L ^ 2 + H ^ 2) *
        (Real.sqrt (L ^ 2 + H ^ 2) - cappedBlockSupport L H t) =
      (Real.sqrt (L ^ 2 + H ^ 2) * x - L) ^ 2 +
        (Real.sqrt (L ^ 2 + H ^ 2) * z - H) ^ 2 := by
  obtain ⟨x, z, hx, hxt, hz, hunit, hval⟩ := cappedBlockSupport_disk_attained L H ht
  refine ⟨x, z, hx, hxt, hz, hunit, ?_⟩
  have hD := Real.sq_sqrt (show 0 ≤ L ^ 2 + H ^ 2 by positivity)
  have hu := congrArg (fun q : ℝ => (Real.sqrt (L ^ 2 + H ^ 2)) ^ 2 * q) hunit
  rw [← hval]
  nlinarith

/-- A cap is inactive exactly when it contains the uncapped extremal ray. -/
theorem cappedBlockSupport_eq_norm_iff {L H t : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    cappedBlockSupport L H t = Real.sqrt (L ^ 2 + H ^ 2) ↔
      L ≤ t * Real.sqrt (L ^ 2 + H ^ 2) := by
  constructor
  · intro he
    obtain ⟨x, z, _, hxt, _, _, hd⟩ := cappedBlockSupport_deficit_attained L H ht
    rw [he, sub_self, mul_zero] at hd
    have hx : Real.sqrt (L ^ 2 + H ^ 2) * x - L = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (L ^ 2 + H ^ 2) * z - H)]
    have h := mul_le_mul_of_nonneg_left hxt (Real.sqrt_nonneg (L ^ 2 + H ^ 2))
    nlinarith
  · exact cappedBlockSupport_eq_norm hL hH ht

/-- Binding a cap produces a certified quadratic support loss. -/
theorem cappedBlockSupport_quadratic_deficit {L H t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hbind : t * Real.sqrt (L ^ 2 + H ^ 2) ≤ L) :
    (L - t * Real.sqrt (L ^ 2 + H ^ 2)) ^ 2 ≤
      2 * Real.sqrt (L ^ 2 + H ^ 2) *
        (Real.sqrt (L ^ 2 + H ^ 2) - cappedBlockSupport L H t) := by
  obtain ⟨x, z, _, hxt, _, _, hd⟩ := cappedBlockSupport_deficit_attained L H ht
  have h := mul_le_mul_of_nonneg_left hxt (Real.sqrt_nonneg (L ^ 2 + H ^ 2))
  have hsq : (L - t * Real.sqrt (L ^ 2 + H ^ 2)) ^ 2 ≤
      (Real.sqrt (L ^ 2 + H ^ 2) * x - L) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (Real.sqrt (L ^ 2 + H ^ 2) * z - H)]

/-- Zero blocks have zero low fraction by total real division. -/
def cappedLowFraction (L H : ℝ) : ℝ := L / Real.sqrt (L ^ 2 + H ^ 2)

theorem cappedLowFraction_mem {L H : ℝ} (hL : 0 ≤ L) :
    cappedLowFraction L H ∈ Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg hL (Real.sqrt_nonneg _), ?_⟩
  by_cases hD : Real.sqrt (L ^ 2 + H ^ 2) = 0
  · simp [cappedLowFraction, hD]
  · have hDp := lt_of_le_of_ne (Real.sqrt_nonneg (L ^ 2 + H ^ 2)) (Ne.symm hD)
    exact (div_le_one hDp).2 (Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg H]))

theorem cappedLowFraction_le_iff {L H t : ℝ} (ht : 0 ≤ t) :
    cappedLowFraction L H ≤ t ↔ L ≤ t * Real.sqrt (L ^ 2 + H ^ 2) := by
  by_cases hD : Real.sqrt (L ^ 2 + H ^ 2) = 0
  · have hsq := Real.sq_sqrt (show 0 ≤ L ^ 2 + H ^ 2 by positivity)
    have hL : L = 0 := by rw [hD] at hsq; nlinarith [sq_nonneg H]
    simp only [cappedLowFraction, hD, div_zero, mul_zero]
    simp [hL, ht]
  · exact div_le_iff₀ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hD))

/-- The largest low fraction on one sign; physical grids are nonempty. -/
def cappedSignLowFraction (M : Finset ι) (hM : M.Nonempty)
    (L H : Bool → ι → ℝ) (σ : Bool) : ℝ :=
  M.sup' hM (fun m => cappedLowFraction (L σ m) (H σ m))

theorem cappedSignLowFraction_mem (M : Finset ι) (hM : M.Nonempty)
    (L H : Bool → ι → ℝ) (hL : ∀ σ, ∀ m ∈ M, 0 ≤ L σ m) (σ : Bool) :
    cappedSignLowFraction M hM L H σ ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup' hM
    (fun m => cappedLowFraction (L σ m) (H σ m))
  change M.sup' hM _ ∈ Icc (0 : ℝ) 1
  rw [he]
  exact cappedLowFraction_mem (hL σ m hm)

theorem cappedSignLowFraction_le_iff (M : Finset ι) (hM : M.Nonempty)
    (L H : Bool → ι → ℝ) (σ : Bool) {t : ℝ} (ht : 0 ≤ t) :
    cappedSignLowFraction M hM L H σ ≤ t ↔
      ∀ m ∈ M, L σ m ≤ t * Real.sqrt ((L σ m) ^ 2 + (H σ m) ^ 2) := by
  unfold cappedSignLowFraction
  rw [Finset.sup'_le_iff]
  exact forall_congr' fun m => forall_congr' fun _ => cappedLowFraction_le_iff ht

/-- Equality in the compact angular maximum requires every block to be inactive. -/
theorem cappedCosetSupport_eq_independent_iff_caps (M : Finset ι)
    (L H : Bool → ι → ℝ) (hL : ∀ σ, ∀ m ∈ M, 0 ≤ L σ m)
    (hH : ∀ σ, ∀ m ∈ M, 0 ≤ H σ m) :
    cappedCosetSupport M L H =
        ∑ σ : Bool, ∑ m ∈ M, Real.sqrt ((L σ m) ^ 2 + (H σ m) ^ 2) ↔
      ∃ t ∈ Icc (0 : ℝ) 1, ∀ σ, ∀ m ∈ M,
        L σ m ≤ pairedCap t σ * Real.sqrt ((L σ m) ^ 2 + (H σ m) ^ 2) := by
  constructor
  · intro he
    obtain ⟨t, ht, htval, _⟩ := cappedCosetSupport_attained M L H
    refine ⟨t, ht, ?_⟩
    have hle (σ : Bool) (m : ι) (_ : m ∈ M) :=
      cappedBlockSupport_le_norm (L σ m) (H σ m) (pairedCap_mem ht σ)
    have hsign := (Finset.sum_eq_sum_iff_of_le
      (fun σ (_ : σ ∈ Finset.univ) => Finset.sum_le_sum (hle σ))).1 (htval.symm.trans he)
    intro σ m hm
    have hblock := (Finset.sum_eq_sum_iff_of_le (hle σ)).1 (hsign σ (Finset.mem_univ σ)) m hm
    exact (cappedBlockSupport_eq_norm_iff (hL σ m hm) (hH σ m hm) (pairedCap_mem ht σ)).1 hblock
  · rintro ⟨t, ht, hfit⟩
    apply le_antisymm (cappedCosetSupport_le_independent M L H)
    obtain ⟨_, _, _, hmax⟩ := cappedCosetSupport_attained M L H
    have he : (∑ σ : Bool, ∑ m ∈ M, cappedBlockSupport (L σ m) (H σ m) (pairedCap t σ)) =
        ∑ σ : Bool, ∑ m ∈ M, Real.sqrt ((L σ m) ^ 2 + (H σ m) ^ 2) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact Finset.sum_congr rfl fun m hm =>
        cappedBlockSupport_eq_norm (hL σ m hm) (hH σ m hm) (pairedCap_mem ht σ) (hfit σ m hm)
    exact he ▸ hmax t ht

/-- Exact activation boundary, including arbitrary zero low or high blocks. -/
theorem cappedCosetSupport_eq_independent_iff (M : Finset ι) (hM : M.Nonempty)
    (L H : Bool → ι → ℝ) (hL : ∀ σ, ∀ m ∈ M, 0 ≤ L σ m)
    (hH : ∀ σ, ∀ m ∈ M, 0 ≤ H σ m) :
    cappedCosetSupport M L H =
        ∑ σ : Bool, ∑ m ∈ M, Real.sqrt ((L σ m) ^ 2 + (H σ m) ^ 2) ↔
      cappedSignLowFraction M hM L H false ^ 2 + cappedSignLowFraction M hM L H true ^ 2 ≤ 1 := by
  rw [cappedCosetSupport_eq_independent_iff_caps M L H hL hH]
  have hf := cappedSignLowFraction_mem M hM L H hL false
  have hg := cappedSignLowFraction_mem M hM L H hL true
  constructor
  · rintro ⟨t, ht, hfit⟩
    have h₀ := (cappedSignLowFraction_le_iff M hM L H false (pairedCap_mem ht false).1).2 (hfit false)
    have h₁ := (cappedSignLowFraction_le_iff M hM L H true (pairedCap_mem ht true).1).2 (hfit true)
    have hsq := pairedCap_sq ht
    have hcf := (pairedCap_mem ht false).1
    have hcg := (pairedCap_mem ht true).1
    nlinarith [hf.1, hg.1]
  · intro hsq
    let t := cappedSignLowFraction M hM L H false
    refine ⟨t, hf, fun σ => ?_⟩
    apply (cappedSignLowFraction_le_iff M hM L H σ (pairedCap_mem hf σ).1).1
    cases σ
    · exact le_rfl
    · exact Real.le_sqrt_of_sq_le (by linarith)

theorem cappedCosetSupport_lt_independent_iff (M : Finset ι) (hM : M.Nonempty)
    (L H : Bool → ι → ℝ) (hL : ∀ σ, ∀ m ∈ M, 0 ≤ L σ m)
    (hH : ∀ σ, ∀ m ∈ M, 0 ≤ H σ m) :
    cappedCosetSupport M L H <
        ∑ σ : Bool, ∑ m ∈ M, Real.sqrt ((L σ m) ^ 2 + (H σ m) ^ 2) ↔
      1 < cappedSignLowFraction M hM L H false ^ 2 + cappedSignLowFraction M hM L H true ^ 2 := by
  have he := cappedCosetSupport_eq_independent_iff M hM L H hL hH
  constructor
  · intro hlt
    by_contra hn
    exact (ne_of_lt hlt) (he.2 (le_of_not_gt hn))
  · intro hlt
    exact lt_of_le_of_ne (cappedCosetSupport_le_independent M L H)
      (fun heq => (not_le_of_gt hlt) (he.1 heq))

end
end GaloisForLFunctions.BiScaleUncertainty
