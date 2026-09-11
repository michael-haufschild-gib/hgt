import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAbsoluteSynthesis
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyStrictConvexity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Convex.StrictConvexSpace
open Complex Set Filter
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section AbsoluteRigidity
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [StrictConvexSpace ℝ E]

private theorem biorthogonal_pair_strict [DecidableEq I]
    (v : I → E) (hv : ∀ i, ‖v i‖ = 1) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (i j : I) (hij : i ≠ j) (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    ‖α • v i + β • v j‖ < ‖α‖ + ‖β‖ := by
  have hn : ¬SameRay ℝ (α • v i) (β • v j) := by
    intro hr
    have hr' := sameRay_iff_norm_smul_eq.mp hr
    have h := congrArg ((a i).restrictScalars ℝ) hr'
    rw [((a i).restrictScalars ℝ).map_smul ‖α • v i‖ (β • v j),
      ((a i).restrictScalars ℝ).map_smul ‖β • v j‖ (α • v i)] at h
    change ‖α • v i‖ • a i (β • v j) = ‖β • v j‖ • a i (α • v i) at h
    have hz : (‖β‖ : ℝ) • α = (0 : ℂ) := by
      simpa [map_smul, hd, hij, norm_smul, hv] using h.symm
    exact (smul_ne_zero (norm_ne_zero_iff.mpr hβ) hα) hz
  simpa only [norm_smul, hv, mul_one] using norm_add_lt_of_not_sameRay hn

private theorem lp_non_single_two_coordinates [DecidableEq I] (i₀ : I)
    (c : lp (fun _ : I => ℂ) 1)
    (hc : ¬∃ i z, c = lp.single 1 i z) :
    ∃ i j, i ≠ j ∧ c i ≠ 0 ∧ c j ≠ 0 := by
  classical
  have hi : ∃ i, c i ≠ 0 := by
    by_contra h
    apply hc
    refine ⟨i₀, 0, ?_⟩
    apply lp.ext
    funext i
    have hz : c i = 0 := by simpa using not_exists.mp h i
    simp [hz]
  obtain ⟨i, hi⟩ := hi
  have hj : ∃ j, i ≠ j ∧ c j ≠ 0 := by
    by_contra h
    apply hc
    refine ⟨i, c i, ?_⟩
    apply lp.ext
    funext j
    by_cases hji : j = i
    · subst j; simp
    · have hz : c j = 0 := by
        by_contra hn
        exact h ⟨j, Ne.symm hji, hn⟩
      exact hz.trans (lp.single_apply_ne (E := fun _ : I => ℂ) 1 i (c i) hji).symm
  obtain ⟨j, hij, hj⟩ := hj
  exact ⟨i, j, hij, hi, hj⟩

private theorem lp1_synthesis_strict_of_two [DecidableEq I]
    (v : I → E) (hv : ∀ i, ‖v i‖ = 1) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (S : lp (fun _ : I => ℂ) 1 →L[ℂ] E)
    (hS : ∀ c, ‖S c‖ ≤ ‖c‖) (hs : ∀ i z, S (lp.single 1 i z) = z • v i)
    (c : lp (fun _ : I => ℂ) 1) (i j : I) (hij : i ≠ j)
    (hi : c i ≠ 0) (hj : c j ≠ 0) : ‖S c‖ < ‖c‖ := by
  classical
  let d : lp (fun _ : I => ℂ) 1 := lp.single 1 i (c i) + lp.single 1 j (c j)
  let r := c - d
  have hrec : c = d + r := by dsimp [r]; abel
  have hr : ‖r‖ = ‖c‖ - (‖c i‖ + ‖c j‖) := by
    have h := lp.norm_compl_sum_single (by norm_num : 0 < (1 : ENNReal).toReal) c {i, j}
    simpa [d, r, Finset.sum_pair hij] using h
  have hd' : ‖S d‖ < ‖c i‖ + ‖c j‖ := by
    simpa only [d, map_add, hs] using biorthogonal_pair_strict v hv a hd i j hij (c i) (c j) hi hj
  calc
    ‖S c‖ = ‖S d + S r‖ := by rw [← map_add, ← hrec]
    _ ≤ ‖S d‖ + ‖S r‖ := norm_add_le _ _
    _ < (‖c i‖ + ‖c j‖) + ‖r‖ := add_lt_add_of_lt_of_le hd' (hS r)
    _ = ‖c‖ := by rw [hr]; ring

private theorem lp1_synthesis_norm_eq_iff_single [DecidableEq I]
    (i₀ : I) (v : I → E) (hv : ∀ i, ‖v i‖ = 1) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (S : lp (fun _ : I => ℂ) 1 →L[ℂ] E)
    (hS : ∀ c, ‖S c‖ ≤ ‖c‖) (hs : ∀ i z, S (lp.single 1 i z) = z • v i)
    (c : lp (fun _ : I => ℂ) 1) :
    ‖S c‖ = ‖c‖ ↔ ∃ i z, c = lp.single 1 i z := by
  classical
  constructor
  · intro h
    by_contra hn
    obtain ⟨i, j, hij, hi, hj⟩ := lp_non_single_two_coordinates i₀ c hn
    exact (lp1_synthesis_strict_of_two v hv a hd S hS hs c i j hij hi hj).ne h
  · rintro ⟨i, z, rfl⟩
    rw [hs, norm_smul, hv, mul_one, lp.norm_single (by norm_num : (0 : ENNReal) < 1)]
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [StrictConvexSpace ℝ E] in
private theorem synthesis_single_from_hasSum [DecidableEq I]
    (v : I → E) (S : lp (fun _ : I => ℂ) 1 → E)
    (hS : ∀ c, HasSum (fun i => c i • v i) (S c)) (i : I) (z : ℂ) :
    S (lp.single 1 i z) = z • v i := by
  calc
    S (lp.single 1 i z) = ∑' j, (lp.single (E := fun _ : I => ℂ) 1 i z) j • v j :=
      (hS (lp.single 1 i z)).tsum_eq.symm
    _ = z • v i := by
      rw [tsum_eq_single i]
      · rw [lp.single_apply_self]
      · intro j hj
        rw [lp.single_apply_ne _ _ _ hj, zero_smul]

end AbsoluteRigidity

private theorem actual_absolute_synthesis_single (b ω : ℝ) (z : ℂ) :
    causalFrequencyAbsoluteSynthesis b (lp.single 1 ω z) = z • causalFrequencyMode b ω := by
  exact synthesis_single_from_hasSum (causalFrequencyMode b)
    (fun c => causalFrequencyAbsoluteSynthesis b c)
    (causalFrequencyAbsoluteSynthesis_hasSum b) ω z

/-- Absolute synthesis lies between the lp2 amplitude norm and the lp1 mass,
with both bounds valid on every actual absolutely summable frequency family. -/
theorem causalFrequencyAbsoluteSynthesis_norm_bounds (b : ℝ)
    (c : lp (fun _ : ℝ => ℂ) 1) :
    ‖lp.linearMapOfLE ℂ (fun _ : ℝ => ℂ) (by norm_num : (1 : ENNReal) ≤ 2) c‖ ≤
      ‖causalFrequencyAbsoluteSynthesis b c‖ ∧
    ‖causalFrequencyAbsoluteSynthesis b c‖ ≤ ‖c‖ := by
  constructor
  · have h := (causalFrequencyAmplitudeMap b).le_opNorm (causalFrequencyAbsoluteSynthesis b c)
    simpa only [causalFrequencyAmplitudeMap_absoluteSynthesis,
      norm_causalFrequencyAmplitudeMap, one_mul] using h
  · have h := (causalFrequencyAbsoluteSynthesis b).le_opNorm c
    simpa only [norm_causalFrequencyAbsoluteSynthesis, one_mul] using h

/-- The sharp lp1 synthesis bound is attained exactly by single-frequency
amplitude families; zero is included by allowing its scalar amplitude to vanish. -/
theorem causalFrequencyAbsoluteSynthesis_norm_eq_iff_single (b : ℝ)
    (c : lp (fun _ : ℝ => ℂ) 1) :
    ‖causalFrequencyAbsoluteSynthesis b c‖ = ‖c‖ ↔
      ∃ ω z, c = lp.single 1 ω z := by
  letI : StrictConvexSpace ℝ (causalFrequencySpace b) := causalFrequencySpace_strictConvex b
  exact lp1_synthesis_norm_eq_iff_single 0 (causalFrequencyMode b)
    (norm_causalBoundedUnitEigenchain b) (causalFrequencyCoefficient b)
    (causalFrequencyCoefficient_mode b) (causalFrequencyAbsoluteSynthesis b)
    (fun d => (causalFrequencyAbsoluteSynthesis_norm_bounds b d).2)
    (actual_absolute_synthesis_single b) c

end RHTower.FokasLenells
