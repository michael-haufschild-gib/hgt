import GaloisForLFunctions.RHTower.SelbergMaassCurvatureTransport
import GaloisForLFunctions.Bottcher.Gamma2ProperAction

/-!
# Compact modular orbit sums and normalized weights

Proper discontinuity makes full integral modular orbit sums locally finite and
compact mutual overlaps globally finite. A nonnegative compact majorant divided
by max(1, its orbit sum) gives a compact weight whose full periodization is one
on any prescribed compact region. All kernel and stabilizer repetitions remain
in the literal sum; no fundamental-domain boundary is removed.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergCompactPeriodization
noncomputable section

/-- The full integral modular orbit sum, with all stabilizer multiplicities retained. -/
def periodize (g : ℍ → ℝ) (z : ℍ) : ℝ := ∑' A : SL2Z, g (A • z)

/-- The full orbit sum is invariant under each modular action. -/
theorem periodize_invariant (g : ℍ → ℝ) (A : SL2Z) (z : ℍ) :
    periodize g (A • z) = periodize g z := by
  unfold periodize
  simp only [← mul_smul]
  exact (Equiv.mulRight A).tsum_eq (fun B : SL2Z => g (B • z))

/-- Compact tests have finitely supported orbit sums at every point. -/
theorem orbit_summable {g : ℍ → ℝ} (hg : HasCompactSupport g) (z : ℍ) :
    Summable (fun A : SL2Z => g (A • z)) := by
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := SL2Z)
    (isCompact_singleton (x := z)) hg
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro A hA
  exact ⟨A • z, ⟨z, mem_singleton z, rfl⟩, subset_tsupport g hA⟩

/-- Every compact test has a fixed finite orbit expansion near each point. -/
theorem periodize_locally_finite {g : ℍ → ℝ} (hg : HasCompactSupport g) (z : ℍ) :
    ∃ s : Finset SL2Z, ∀ᶠ w in 𝓝 z, periodize g w = ∑ A ∈ s, g (A • w) := by
  classical
  obtain ⟨K, hK, hz⟩ := exists_compact_mem_nhds z
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := SL2Z) hK hg
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [hz] with w hw
  apply tsum_eq_sum
  intro A hA
  by_contra hn
  apply hA
  simp only [Set.Finite.mem_toFinset]
  exact ⟨A • w, ⟨w, hw, rfl⟩, subset_tsupport g hn⟩

/-- Continuous compact tests have continuous full periodizations across all modular seams. -/
theorem periodize_continuous (g : C_c(ℍ, ℝ)) : Continuous (periodize g) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨s, hs⟩ := periodize_locally_finite g.hasCompactSupport z
  have hc : Continuous (fun w : ℍ => ∑ A ∈ s, g (A • w)) := by
    apply continuous_finsetSum
    intro A hA
    exact g.continuous.comp (Homeomorph.smul (A : GL (Fin 2) ℝ)).continuous
  have he : periodize g =ᶠ[𝓝 z] (fun w => ∑ A ∈ s, g (A • w)) := hs
  exact hc.continuousAt.congr_of_eventuallyEq he

/-- Two compact tests have only finitely many nonzero mutual modular overlaps. -/
theorem overlap_finite (g h : C_c(ℍ, ℝ)) :
    ∃ s : Finset SL2Z, ∀ A ∉ s, ∀ z : ℍ, g z * h (A • z) = 0 := by
  classical
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := SL2Z)
    g.hasCompactSupport h.hasCompactSupport
  refine ⟨hfin.toFinset, ?_⟩
  intro A hA z
  by_contra hn
  have hg : g z ≠ 0 := fun hz => hn (by rw [hz, zero_mul])
  have hh : h (A • z) ≠ 0 := fun hz => hn (by rw [hz, mul_zero])
  apply hA
  simp only [Set.Finite.mem_toFinset]
  exact ⟨A • z, ⟨z, subset_tsupport g hg, rfl⟩, subset_tsupport h hh⟩

/-- Multiplying a compact test by any continuous real field retains compact support. -/
def mulContinuous (g : C_c(ℍ, ℝ)) (F : ℍ → ℝ) (hF : Continuous F) : C_c(ℍ, ℝ) where
  toFun z := g z * F z
  continuous_toFun := g.continuous.mul hF
  hasCompactSupport' := g.hasCompactSupport.mul_right

/-- The compact product has its literal pointwise value. -/
theorem mulContinuous_apply (g : C_c(ℍ, ℝ)) (F : ℍ → ℝ) (hF : Continuous F) (z : ℍ) :
    mulContinuous g F hF z = g z * F z := rfl

/-- Nonnegative fields have nonnegative full orbit sums. -/
theorem periodize_nonneg {g : ℍ → ℝ} (hg : ∀ z, 0 ≤ g z) (z : ℍ) : 0 ≤ periodize g z :=
  tsum_nonneg (fun _ => hg _)

/-- A nonnegative compact test is bounded by its own full orbit sum. -/
theorem self_le_periodize (g : C_c(ℍ, ℝ)) (hg : ∀ z, 0 ≤ g z) (z : ℍ) :
    g z ≤ periodize g z := by
  have h := (orbit_summable g.hasCompactSupport z).le_tsum (1 : SL2Z) (fun A hA => hg (A • z))
  simpa only [one_smul, periodize] using h

/-- Every compact half-plane region has a nonnegative compact continuous test equal to one there. -/
theorem exists_compact_majorant {K : Set ℍ} (hK : IsCompact K) :
    ∃ b : C_c(ℍ, ℝ), (∀ z, 0 ≤ b z) ∧ ∀ z ∈ K, b z = 1 := by
  have himg := hK.image UpperHalfPlane.continuous_coe
  have hs : UpperHalfPlane.coe '' K ⊆ {z : ℂ | 0 < z.im} := by
    rintro z ⟨w, hw, rfl⟩
    exact w.im_pos
  obtain ⟨phi, hp, hc, ht, hn, hone⟩ := SelbergLocalTestGreen.exists_nonnegative_cutoff himg hs
  refine ⟨SelbergUpperHalfPlaneCompactTests.restrictCompact phi hp.continuous hc ht, ?_, ?_⟩
  · intro z
    exact hn z
  · intro z hz
    exact hone z ⟨z, hz, rfl⟩

/-- Normalize a compact test by a globally positive invariant denominator. -/
def normalize (b : C_c(ℍ, ℝ)) : C_c(ℍ, ℝ) where
  toFun z := b z / max 1 (periodize b z)
  continuous_toFun := b.continuous.div (continuous_const.max (periodize_continuous b))
    (fun z => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  hasCompactSupport' := b.hasCompactSupport.mono (by
    intro z hz hb
    exact hz (by dsimp only; rw [hb, zero_div]))

/-- Normalization is literal division by the full orbit sum truncated below at one. -/
theorem normalize_apply (b : C_c(ℍ, ℝ)) (z : ℍ) :
    normalize b z = b z / max 1 (periodize b z) := rfl

/-- The normalized orbit sum has its exact scalar value, including all stabilizer repetitions. -/
theorem periodize_normalize (b : C_c(ℍ, ℝ)) (z : ℍ) :
    periodize (normalize b) z = periodize b z / max 1 (periodize b z) := by
  change (∑' A : SL2Z, normalize b (A • z)) = _
  simp only [normalize_apply, periodize_invariant]
  exact tsum_div_const

/-- Normalization preserves positivity. -/
theorem normalize_nonneg (b : C_c(ℍ, ℝ)) (hb : ∀ z, 0 ≤ b z) (z : ℍ) :
    0 ≤ normalize b z := div_nonneg (hb z) (zero_le_one.trans (le_max_left _ _))

/-- A normalized nonnegative orbit sum never exceeds one. -/
theorem periodize_normalize_le_one (b : C_c(ℍ, ℝ)) (z : ℍ) :
    periodize (normalize b) z ≤ 1 := by
  rw [periodize_normalize]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr (le_max_right _ _)

/-- Every compact region admits an actual compact weight whose full orbit sum is one there. -/
theorem exists_normalized_weight {K : Set ℍ} (hK : IsCompact K) :
    ∃ w : C_c(ℍ, ℝ), (∀ z, 0 ≤ w z) ∧ (∀ z, periodize w z ≤ 1) ∧
      ∀ z ∈ K, periodize w z = 1 := by
  obtain ⟨b, hb, hbone⟩ := exists_compact_majorant hK
  refine ⟨normalize b, normalize_nonneg b hb, periodize_normalize_le_one b, ?_⟩
  intro z hz
  have hB : 1 ≤ periodize b z := by
    rw [← hbone z hz]
    exact self_le_periodize b hb z
  rw [periodize_normalize, max_eq_right hB, div_self (ne_of_gt (zero_lt_one.trans_le hB))]

end
end GaloisForLFunctions.RHTower.SelbergCompactPeriodization
