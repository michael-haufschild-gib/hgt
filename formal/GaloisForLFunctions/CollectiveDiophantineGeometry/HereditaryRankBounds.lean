import GaloisForLFunctions.CollectiveDiophantineGeometry.BoundedCoordinateElimination
import GaloisForLFunctions.CollectiveDiophantineGeometry.ReciprocalRankBounds

/-!
# Hereditary rank bounds for small prime-logarithm forms

Bounded elimination localizes a small-form span to every coordinate set.
Strict majority rank then uses root degree one in the simultaneous
logarithm bound. One explicit floor therefore bounds the rank of every
coordinate intersection by half its support size.
-/

noncomputable section
namespace GaloisForLFunctions.CollectiveDiophantineGeometry
open Finset Real Matrix
open RHTower.Matveev TranscendenceTheoryOfThePrimeOrbit

set_option autoImplicit false

/-- Coefficient height after clearing a coordinate-elimination determinant. -/
def hereditaryHeight (k : ℕ) (H : ℝ) : ℝ := (k.factorial : ℝ) * H ^ k

/-- Maximum loss in value when a small-form span is restricted to coordinates. -/
def hereditaryValueLoss (k : ℕ) (H : ℝ) : ℝ := (k.factorial : ℝ) * H ^ (k - 1)

/-- A single threshold for half-rank bounds on every coordinate intersection. -/
def hereditaryDepthFloor (k W : ℕ) (H : ℝ) : ℝ :=
  collectiveDepthFloor k 0 W (hereditaryHeight k H) / hereditaryValueLoss k H

theorem hereditaryDepthFloor_pos {k W : ℕ} (hk : 1 ≤ k) {H : ℝ} (hH : 0 < H) :
    0 < hereditaryDepthFloor k W H := by
  apply div_pos (collectiveDepthFloor_pos hk ?_) ?_
  · unfold hereditaryHeight; positivity
  · unfold hereditaryValueLoss; positivity

/-- Strict majority rank in any smaller coordinate set has a floor at least
as large as the full-dimension root-degree-one floor. -/
theorem collectiveDepthFloor_le_of_majority {r d k W V : ℕ}
    (hr : 1 ≤ r) (hdr : d < r) (hdk : d + r ≤ k) (hWV : W ≤ V)
    {H : ℝ} (hH : 1 ≤ H) :
    collectiveDepthFloor k 0 V H ≤ collectiveDepthFloor r d W H := by
  have hrk : r ≤ k := by omega
  have hk : 1 ≤ k := by omega
  have hfac : (r.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hrk
  have harg : (r.factorial : ℝ) * H ^ r ≤ (k.factorial : ℝ) * H ^ k :=
    mul_le_mul hfac (pow_le_pow_right₀ hH hrk) (by positivity) (by positivity)
  have harg1 : (1 : ℝ) ≤ (r.factorial : ℝ) * H ^ r :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast r.factorial_pos) (one_le_pow₀ hH)
  have hlog : log ((r.factorial : ℝ) * H ^ r) + 2 ≤
      log ((k.factorial : ℝ) * H ^ k) + 2 :=
    add_le_add_right (Real.log_le_log (by positivity) harg) _
  have hlog0 : 0 ≤ log ((r.factorial : ℝ) * H ^ r) + 2 := by
    linarith only [Real.log_nonneg harg1]
  have hbase : collectiveBase (d + r) W ≤ collectiveBase k V := by
    unfold collectiveBase
    gcongr
  have hbase1 : (1 : ℝ) ≤ collectiveBase k V := by
    exact_mod_cast (show 1 ≤ collectiveBase k V by unfold collectiveBase; positivity)
  have hC : collectiveExponent r d W ≤ collectiveExponent k 0 V := by
    rw [collectiveExponent_of_large_rank hdr,
      collectiveExponent_of_large_rank (show 0 < k by omega), zero_add]
    calc
      _ ≤ (collectiveBase k V : ℝ) ^ (100 * (d + r + 1)) := by
        gcongr
        exact_mod_cast hbase
      _ ≤ _ := pow_le_pow_right₀ hbase1 (by omega)
  have hnum : exp (-(collectiveExponent k 0 V *
      (log ((k.factorial : ℝ) * H ^ k) + 2))) ≤
      exp (-(collectiveExponent r d W * (log ((r.factorial : ℝ) * H ^ r) + 2))) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact mul_le_mul hC hlog hlog0 (by unfold collectiveExponent; positivity)
  have hden : (r : ℝ) * (r.factorial : ℝ) * H ^ (r - 1) ≤
      (k : ℝ) * (k.factorial : ℝ) * H ^ (k - 1) := by
    apply mul_le_mul
    · exact mul_le_mul (by exact_mod_cast hrk) hfac (by positivity) (by positivity)
    · exact pow_le_pow_right₀ hH (by omega)
    · positivity
    · positivity
  have hden0 : 0 < (r : ℝ) * (r.factorial : ℝ) * H ^ (r - 1) := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  unfold collectiveDepthFloor
  exact (div_le_div_of_nonneg_left (exp_nonneg _) hden0 hden).trans
    (div_le_div_of_nonneg_right hnum hden0.le)

private theorem independent_coordinate_restriction {r k l : ℕ}
    (M : Fin r → Fin k → ℚ) (J : Finset (Fin k)) (e : Fin l ≃ J)
    (hind : LinearIndependent ℚ M) (hsupp : ∀ i j, j ∉ J → M i j = 0) :
    LinearIndependent ℚ (fun i j => M i (e j)) := by
  let f := LinearMap.funLeft ℚ ℚ (fun j : Fin l => (e j : Fin k))
  change LinearIndependent ℚ (f ∘ M)
  apply hind.map_injOn f
  have hspan : Submodule.span ℚ (Set.range M) ≤ coordinateSubspace J := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact hsupp i
  intro v hv w hw heq
  ext j
  by_cases hj : j ∈ J
  · have h := congrFun heq (e.symm ⟨j, hj⟩)
    change v (e (e.symm ⟨j, hj⟩)) = w (e (e.symm ⟨j, hj⟩)) at h
    simpa only [Equiv.apply_symm_apply] using h
  · rw [hspan hv j hj, hspan hw j hj]

private theorem sum_coordinate_restriction {k l : ℕ}
    (J : Finset (Fin k)) (e : Fin l ≃ J) (f : Fin k → ℝ)
    (hsupp : ∀ j, j ∉ J → f j = 0) :
    (∑ j, f (e j)) = ∑ j, f j := by
  classical
  calc
    _ = ∑ j : J, f j := e.sum_comp (fun j : J => f j)
    _ = ∑ j ∈ J, f j := Finset.sum_coe_sort J f
    _ = ∑ j, f j := Finset.sum_subset (Finset.subset_univ J) (fun j _ hj => hsupp j hj)

private theorem collectiveLogBound_comp_le {m n : ℕ}
    (p : Fin (m + 1) → ℕ) (hprime : ∀ j, (p j).Prime)
    (f : Fin (n + 1) → Fin (m + 1)) (hf : Function.Injective f) :
    collectiveLogBound (p ∘ f) ≤ collectiveLogBound p := by
  classical
  have hmass : totalLogSum (p ∘ f) ≤ totalLogSum p := by
    unfold totalLogSum
    change (∑ j, log (p (f j))) ≤ ∑ j, log (p j)
    calc
      _ = ∑ j ∈ univ.image f, log (p j) :=
        (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => Real.log_nonneg (by exact_mod_cast (hprime j).one_lt.le))
  exact Nat.add_le_add_right (Nat.ceil_mono hmass) 1

end GaloisForLFunctions.CollectiveDiophantineGeometry
