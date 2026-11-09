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
    add_le_add (Real.log_le_log (by positivity) harg) (le_refl 2)
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

/-- Every coordinate intersection of the small-form span has at most half
its support dimension. All restrictions share one explicit arithmetic floor. -/
theorem hereditary_small_forms_finrank_le {k : ℕ}
    (p : Fin (k + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (S : Finset (Fin (k + 1) → ℤ)) {H : ℝ} (hH : 1 ≤ H)
    (hheight : ∀ v ∈ S, ∀ j, |(v j : ℝ)| ≤ H)
    (hvalue : ∀ v ∈ S, |primeLogForm p v| <
      hereditaryDepthFloor (k + 1) (collectiveLogBound p) H)
    (J : Finset (Fin (k + 1))) :
    2 * Module.finrank ℚ ↥(integerRowSpan S ⊓ coordinateSubspace J) ≤ J.card := by
  classical
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hε := hereditaryDepthFloor_pos (W := collectiveLogBound p) (by omega : 1 ≤ k + 1) hH0
  have hH' : 1 ≤ hereditaryHeight (k + 1) H :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast (k + 1).factorial_pos)
      (one_le_pow₀ hH)
  obtain ⟨r, M, hr, hind, -, hsupp, hM, hsmall⟩ :=
    exists_bounded_coordinate_basis S J (fun j => log (p j)) hH hε hheight hvalue
  by_contra hbad
  rw [← hr] at hbad
  have hrpos : 0 < r := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  let e₀ : Fin J.card ≃ J := Fintype.equivOfCardEq (by simp)
  have hrat : ∀ a j, j ∉ J → (M a j : ℚ) = 0 := by
    intro a j hj
    rw [hsupp a j hj, Int.cast_zero]
  have hind₀ := independent_coordinate_restriction (fun a j => (M a j : ℚ)) J e₀ hind hrat
  have hrle : n + 1 ≤ J.card := by
    have h := hind₀.fintype_card_le_finrank
    simpa using h
  let d := J.card - (n + 1)
  have hd : d + n + 1 = J.card := by dsimp [d]; omega
  have hdr : d < n + 1 := by dsimp [d]; omega
  have hJle : J.card ≤ k + 1 := by simpa using Finset.card_le_univ J
  let e : Fin (d + n + 1) ≃ J := Fintype.equivOfCardEq (by simpa using hd)
  let f : Fin (d + n + 1) → Fin (k + 1) := fun j => e j
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hind' := independent_coordinate_restriction (fun a j => (M a j : ℚ)) J e hind hrat
  obtain ⟨a, ha⟩ := exists_large_collective_form d n (p ∘ f) (hp.comp hf)
    (fun j => hprime (f j)) (fun i j => M i (f j)) hind' hH' (fun i j => hM i (f j))
  have hfloor : collectiveDepthFloor (k + 1) 0 (collectiveLogBound p)
      (hereditaryHeight (k + 1) H) ≤ collectiveDepthFloor (n + 1) d
        (collectiveLogBound (p ∘ f)) (hereditaryHeight (k + 1) H) :=
    collectiveDepthFloor_le_of_majority (by omega) hdr (by omega)
      (collectiveLogBound_comp_le p hprime f hf) hH'
  have heval : (∑ j, (M a (f j) : ℝ) * log ((p ∘ f) j)) =
      ∑ j, (M a j : ℝ) * log (p j) := by
    apply sum_coordinate_restriction J e
    intro j hj
    rw [hsupp a j hj, Int.cast_zero, zero_mul]
  rw [heval] at ha
  have hK : hereditaryValueLoss (k + 1) H ≠ 0 := by
    unfold hereditaryValueLoss
    positivity
  have hsmall' : |∑ j, (M a j : ℝ) * log (p j)| <
      collectiveDepthFloor (k + 1) 0 (collectiveLogBound p) (hereditaryHeight (k + 1) H) := by
    have h := hsmall a
    change _ < hereditaryValueLoss (k + 1) H *
      (collectiveDepthFloor (k + 1) 0 (collectiveLogBound p) (hereditaryHeight (k + 1) H) /
        hereditaryValueLoss (k + 1) H) at h
    simpa only [mul_div_assoc, mul_comm (hereditaryValueLoss (k + 1) H),
      mul_div_cancel₀ _ hK] using h
  exact (not_lt_of_ge (hfloor.trans ha)) hsmall'

/-- The entire integer approximation body has hereditary coordinate density
at most one half below the explicit threshold. -/
theorem nearRelationBox_hereditary_finrank_le {k H : ℕ}
    (p : Fin (k + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hH : 1 ≤ H) {ε : ℝ}
    (hε : ε ≤ hereditaryDepthFloor (k + 1) (collectiveLogBound p) H)
    (J : Finset (Fin (k + 1))) :
    2 * Module.finrank ℚ ↥(integerRowSpan (nearRelationBox p H ε) ⊓ coordinateSubspace J) ≤ J.card := by
  apply hereditary_small_forms_finrank_le p hp hprime (nearRelationBox p H ε)
    (by exact_mod_cast hH)
  · intro v hv j
    have h := ((mem_nearRelationBox p H ε v).mp hv).1 j
    exact_mod_cast h
  · intro v hv
    exact ((mem_nearRelationBox p H ε v).mp hv).2.trans_le hε

end GaloisForLFunctions.CollectiveDiophantineGeometry
