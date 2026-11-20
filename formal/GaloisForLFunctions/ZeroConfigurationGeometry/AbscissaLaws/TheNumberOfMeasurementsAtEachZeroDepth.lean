import GaloisForLFunctions.ExceptionalLayerTheory.TheLandingLawForZeta
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Exact linear information required at each zero depth

On a finite set of distinct zeros, assign arbitrary real amplitudes and
multiply each by the positive part of its displacement to the right of
the critical line. A linear encoder followed by any decoder attains
sup-norm error h on the unit ball using k measurements exactly when at
most k sample locations have displacement exceeding h. As in the
superlevel criterion for possibility measures of Ho, Truong, Ke, Quoc
and Luan, the values on shallow layers can be discarded at the chosen
precision. Uniformity over finite samples detects the full outer layer.
-/

noncomputable section
open Finset Zeta23 GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
open GaloisForLFunctions.ZeroConfigurationGeometry.ZetaAbscissa
open RHTower RHTower.BacklundConverse RHTower.DeBruijn
namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

/-- Positive displacement from the critical line. -/
def rightDisplacement (z : ℂ) : ℝ := max (z.re-1/2) 0

/-- Every assignment of amplitudes to the sample can be measured linearly
and reconstructed to the specified relative error. The decoder is unrestricted. -/
def sampleReconstructible (S : Finset ℂ) (h : ℝ) (k : ℕ) : Prop :=
  ∃ m ≤ k, ∃ A : (S → ℝ) →ₗ[ℝ] (Fin m → ℝ), ∃ D : (Fin m → ℝ) → S → ℝ,
    ∀ (u : S → ℝ) (i : S), |rightDisplacement i*u i-D (A u) i| ≤ h*‖u‖

/-- Absolute coordinate error on the unit ball, with no homogeneity
or linearity requirement on the decoder. -/
def unitBallReconstructible (S : Finset ℂ) (h : ℝ) (k : ℕ) : Prop :=
  ∃ m ≤ k, ∃ A : (S → ℝ) →ₗ[ℝ] (Fin m → ℝ), ∃ D : (Fin m → ℝ) → S → ℝ,
    ∀ u : S → ℝ, ‖u‖ ≤ 1 → ∀ i : S, |rightDisplacement i*u i-D (A u) i| ≤ h

private theorem relative_gives_unit_ball {S : Finset ℂ} {h : ℝ} (hh : 0 ≤ h) {k : ℕ}
    (ha : sampleReconstructible S h k) : unitBallReconstructible S h k := by
  obtain ⟨m,hm,A,D,H⟩ := ha
  exact ⟨m,hm,A,D,fun u hu i => (H u i).trans (mul_le_of_le_one_right hh hu)⟩

private theorem high_sample_needs_every_coordinate {S : Finset ℂ} {h : ℝ}
    (hS : ∀ z ∈ S, h < rightDisplacement z) {k : ℕ} (ha : unitBallReconstructible S h k) : S.card ≤ k := by
  classical
  obtain ⟨m,hm,A,D,hd⟩ := ha
  have hinj : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    by_contra hv'
    obtain ⟨j,hj⟩ : ∃ j : S, v j ≠ 0 := by
      by_contra! he
      exact hv' (funext he)
    obtain ⟨i,_,hi⟩ := (univ : Finset S).exists_max_image (fun t => |v t|) ⟨j,mem_univ _⟩
    have hvnorm : ‖v‖ ≤ |v i| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      (fun j => by simpa only [Real.norm_eq_abs] using hi j (mem_univ _))
    have hpos : 0 < |v i| := (abs_pos.mpr hj).trans_le (hi j (mem_univ _))
    -- Opposite normalized kernel vectors yield the same observation.
    let w := (v i)⁻¹ • v
    have hwi : w i = 1 := inv_mul_cancel₀ (abs_pos.mp hpos)
    have hw : ‖w‖ ≤ 1 := by
      calc ‖w‖ = |v i|⁻¹ * ‖v‖ := by rw [show w=(v i)⁻¹ • v from rfl,norm_smul,Real.norm_eq_abs,abs_inv]
        _ ≤ |v i|⁻¹ * |v i| := mul_le_mul_of_nonneg_left hvnorm (inv_nonneg.mpr hpos.le)
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    have hAw : A w = 0 := by simp only [w,map_smul,hv,smul_zero]
    have hp := (abs_le.mp (hd w hw i)).2
    have hn := (abs_le.mp (hd (-w) (by rwa [norm_neg]) i)).1
    rw [hAw,hwi,mul_one] at hp
    rw [map_neg,hAw,neg_zero,Pi.neg_apply,hwi,mul_neg,mul_one] at hn
    linarith only [hp,hn,hS i i.property]
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe,Fintype.card_fin] at h
  exact h.trans hm

private theorem sample_from_high_coordinates (S : Finset ℂ) {h : ℝ} (hh : 0 ≤ h) {k : ℕ}
    (hk : (S.filter fun z => h < rightDisplacement z).card ≤ k) : sampleReconstructible S h k := by
  classical
  let T := S.filter fun z => h < rightDisplacement z
  let e : T ≃ Fin T.card := (Fintype.equivFin T).trans (finCongr (Fintype.card_coe T))
  let j (i : T) : S := ⟨i,(filter_subset _ _) i.property⟩
  let A : (S → ℝ) →ₗ[ℝ] (Fin T.card → ℝ) := LinearMap.pi (fun n => LinearMap.proj (j (e.symm n)))
  let D (v : Fin T.card → ℝ) (i : S) := if hi : i.val ∈ T then rightDisplacement i*v (e ⟨i.val,hi⟩) else 0
  refine ⟨T.card,hk,A,D,fun u i => ?_⟩
  by_cases hi : i.val ∈ T
  · simp [D,hi,A,j,mul_nonneg hh (norm_nonneg u)]
  · have hw : rightDisplacement i ≤ h := le_of_not_gt (fun hlt => hi (mem_filter.mpr ⟨i.property,hlt⟩))
    simp only [D,dif_neg hi,sub_zero,abs_mul,abs_of_nonneg (show 0 ≤ rightDisplacement i from le_max_right _ _)]
    exact mul_le_mul hw (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i) (abs_nonneg _) hh

private theorem restrict_unit_ball {S T : Finset ℂ} {h : ℝ} {k : ℕ} (hT : T ⊆ S)
    (hs : unitBallReconstructible S h k) : unitBallReconstructible T h k := by
  classical
  let j (i : T) : S := ⟨i,hT i.property⟩
  let E : (T → ℝ) →ₗ[ℝ] (S → ℝ) := LinearMap.pi (fun i =>
    if hi : i.val ∈ T then LinearMap.proj (⟨i.val,hi⟩ : T) else 0)
  have hE (u : T → ℝ) (i : T) : E u (j i) = u i := by simp [E,j,i.property]
  have hnorm (u : T → ℝ) : ‖E u‖ ≤ ‖u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
    intro i
    by_cases hi : i.val ∈ T
    · simpa [E,hi] using norm_le_pi_norm u (⟨i.val,hi⟩ : T)
    · simp [E,hi]
  obtain ⟨m,hm,A,D,H⟩ := hs
  refine ⟨m,hm,A.comp E,fun v i => D v (j i),fun u hu i => ?_⟩
  have he := H (E u) ((hnorm u).trans hu) (j i)
  simpa only [hE,LinearMap.comp_apply] using he

/-- On the unit ball an arbitrary decoder needs one real measurement
for each displacement above the tolerance. Keeping those coordinates suffices. -/
theorem unit_ball_measurements_iff (S : Finset ℂ) {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    unitBallReconstructible S h k ↔ (S.filter fun z => h < rightDisplacement z).card ≤ k :=
  ⟨fun H => high_sample_needs_every_coordinate (fun _ hi => (mem_filter.mp hi).2)
    (restrict_unit_ball (filter_subset _ _) H), fun hc => relative_gives_unit_ball hh (sample_from_high_coordinates S hh hc)⟩

/-- The same budget reconstructs arbitrary amplitudes to relative error h. -/
theorem sample_measurements_iff (S : Finset ℂ) {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    sampleReconstructible S h k ↔ (S.filter fun z => h < rightDisplacement z).card ≤ k :=
  ⟨fun H => (unit_ball_measurements_iff S hh k).mp (relative_gives_unit_ball hh H),sample_from_high_coordinates S hh⟩

/-- A uniform budget applies to all finite samples from the configuration. -/
def depthMeasurementBudget (Z : ZeroConfig) (h : ℝ) (k : ℕ) : Prop :=
  ∀ S : Finset ℂ, (↑S : Set ℂ) ⊆ Z.carrier → sampleReconstructible S h k

/-- The exact minimum number of measurements is the number of distinct
points strictly deeper than the error tolerance. -/
theorem depth_budget_iff_layer (Z : ZeroConfig) {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    depthMeasurementBudget Z h k ↔
      ∃ T : Finset ℂ, (↑T : Set ℂ) = rightOf Z h ∧ T.card ≤ k := by
  classical
  have hd (z : ℂ) : h < rightDisplacement z ↔ 1/2+h < z.re := by
    rw [rightDisplacement,lt_max_iff,or_iff_left (not_lt.mpr hh)]
    constructor <;> intro H <;> linarith only [H]
  constructor
  · intro H
    have hsize (S : Finset ℂ) (hS : (↑S : Set ℂ) ⊆ rightOf Z h) : S.card ≤ k :=
      high_sample_needs_every_coordinate (fun z hz => (hd z).mpr (hS hz).2)
        (relative_gives_unit_ball hh (H S (fun _ hz => (hS hz).1)))
    have hfin : (rightOf Z h).Finite := by
      by_contra hinf
      obtain ⟨T,hT,hf,hc⟩ := (show (rightOf Z h).Infinite from hinf).exists_subset_ncard_eq (k+1)
      have ha := hsize hf.toFinset (by simpa using hT)
      rw [←Set.ncard_eq_toFinset_card T hf,hc] at ha
      omega
    exact ⟨hfin.toFinset,hfin.coe_toFinset,hsize _ (by simp)⟩
  · rintro ⟨T,hT,hk⟩ S hS
    apply sample_from_high_coordinates S hh
    refine (card_le_card ?_).trans hk
    intro z hz
    obtain ⟨hs,he⟩ := mem_filter.mp hz
    change z ∈ (T : Set ℂ)
    rw [hT]
    exact ⟨hS hs,(hd z).mp he⟩

theorem finite_layer_iff_depth_budget (Z : ZeroConfig) {h : ℝ} (hh : 0 ≤ h) :
    (rightOf Z h).Finite ↔ ∃ k, depthMeasurementBudget Z h k := by
  classical
  constructor
  · intro hf
    exact ⟨_,(depth_budget_iff_layer Z hh _).mpr ⟨hf.toFinset,hf.coe_toFinset,le_rfl⟩⟩
  · rintro ⟨k,hk⟩
    obtain ⟨T,hT,_⟩ := (depth_budget_iff_layer Z hh k).mp hk
    exact hT ▸ T.finite_toSet

/-- High zeros approach the line exactly when every positive precision
requires only finitely many linear readings across all finite zero samples. -/
theorem actual_approach_iff_finite_measurements : ZerosApproachLine ↔
    ∀ h : ℝ, 0 < h → ∃ k, depthMeasurementBudget zetaZeroConfig h k := by
  rw [←zetaZeroConfig_approachesLine_iff,ApproachesLine]
  exact forall₂_congr fun _ hh => finite_layer_iff_depth_budget _ hh.le

/-- Budget zero suffices precisely when the layer is empty. -/
theorem zero_measurements_iff (Z : ZeroConfig) {h : ℝ} (hh : 0 ≤ h) :
    depthMeasurementBudget Z h 0 ↔ ∀ z ∈ Z.carrier, z.re ≤ 1/2+h := by
  classical
  rw [depth_budget_iff_layer Z hh]
  constructor
  · rintro ⟨T,hT,hc⟩ z hz
    have ht : T = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hc)
    apply le_of_not_gt
    intro hlt
    have hm : z ∈ (T : Set ℂ) := hT.symm ▸ (show z ∈ rightOf Z h from ⟨hz,hlt⟩)
    simp [ht] at hm
  · intro H
    have he : rightOf Z h = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun z hz =>
      (not_lt.mpr (H z hz.1)) hz.2)
    exact ⟨∅,by simpa only [Finset.coe_empty] using he.symm,by simp⟩

/-- At each precision the abscissa law rules out a positive finite minimum
number of readings. Zero and unbounded budgets are the two possibilities. -/
theorem actual_abscissa_iff_measurement_dichotomy : AsymptoticAbscissaLaw ↔
    ∀ h : ℝ, 0 ≤ h → (∃ k, depthMeasurementBudget zetaZeroConfig h k) →
      depthMeasurementBudget zetaZeroConfig h 0 := by
  rw [←zetaZeroConfig_abscissaLaw_iff,AbscissaLaw]
  exact forall₂_congr fun h hh => by
    rw [AbscissaLawAt,←finite_layer_iff_depth_budget _ hh,zero_measurements_iff _ hh]

/-- Landing asks whether finite measurement at every positive precision
forces exact reconstruction with a finite number of readings. -/
theorem actual_landing_iff_exact_measurements :
    GaloisForLFunctions.ExceptionalLayerTheory.ZetaLandingLaw ↔
      ((∀ h : ℝ, 0 < h → ∃ k, depthMeasurementBudget zetaZeroConfig h k) →
        ∃ k, depthMeasurementBudget zetaZeroConfig 0 k) := by
  rw [←actual_approach_iff_finite_measurements,←finite_layer_iff_depth_budget _ le_rfl,
    GaloisForLFunctions.ExceptionalLayerTheory.rightOf_zetaZeroConfig_finite_iff]
  rfl

#print axioms unit_ball_measurements_iff
#print axioms sample_measurements_iff
#print axioms depth_budget_iff_layer
#print axioms actual_approach_iff_finite_measurements
#print axioms actual_abscissa_iff_measurement_dichotomy
#print axioms actual_landing_iff_exact_measurements

end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
