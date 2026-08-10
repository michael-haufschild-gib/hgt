import GaloisForLFunctions.HTGeometry.SignedCancellationQuotient

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-!
# Positive observer overlap defect

Finite observational aggregation preserves addition but is only lax for pointwise meet.  The
resulting nonnegative defect composes exactly and its total mass is precisely the total-variation
distinguishability lost by observation.
-/

def finiteProfileMeet {P : Type*} (u v : P → ℝ) : P → ℝ :=
  fun p => min (u p) (v p)

def finiteOverlapDefect {P K : Type*} [Fintype P] [DecidableEq K]
    (u v : P → ℝ) (kappa : P → K) (k : K) : ℝ :=
  min (finiteSignedFiberMass u kappa k) (finiteSignedFiberMass v kappa k) -
    finiteSignedFiberMass (finiteProfileMeet u v) kappa k

theorem finiteSignedFiberMass_comp
    {P K L : Type*} [Fintype P] [Fintype K]
    [DecidableEq K] [DecidableEq L]
    (mu : P → ℝ) (kappa : P → K) (lambda : K → L) (l : L) :
    finiteSignedFiberMass mu (lambda ∘ kappa) l =
      finiteSignedFiberMass (fun k => finiteSignedFiberMass mu kappa k) lambda l := by
  classical
  simp only [finiteSignedFiberMass, Function.comp_apply]
  symm
  calc
    (∑ x : K, if lambda x = l then ∑ p, if kappa p = x then mu p else 0 else 0) =
        ∑ x : K, ∑ p : P,
          if lambda x = l then (if kappa p = x then mu p else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxl : lambda x = l <;> simp [hxl]
    _ = ∑ p : P, ∑ x : K,
          if lambda x = l then (if kappa p = x then mu p else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p : P, if lambda (kappa p) = l then mu p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        (∑ x : K,
            if lambda x = l then (if kappa p = x then mu p else 0) else 0) =
            if lambda (kappa p) = l then
              (if kappa p = kappa p then mu p else 0) else 0 := by
          apply Finset.sum_eq_single (kappa p)
          · intro x hx hxp
            simp [Ne.symm hxp]
          · simp
        _ = if lambda (kappa p) = l then mu p else 0 := by simp

theorem finiteSignedFiberMass_sub
    {P K : Type*} [Fintype P] [DecidableEq K]
    (u v : P → ℝ) (kappa : P → K) (k : K) :
    finiteSignedFiberMass (fun p => u p - v p) kappa k =
      finiteSignedFiberMass u kappa k - finiteSignedFiberMass v kappa k := by
  classical
  simp only [finiteSignedFiberMass]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : kappa p = k <;> simp [h]

theorem finiteProfileMeet_fiberMass_le_left
    {P K : Type*} [Fintype P] [DecidableEq K]
    (u v : P → ℝ) (kappa : P → K) (k : K) :
    finiteSignedFiberMass (finiteProfileMeet u v) kappa k ≤
      finiteSignedFiberMass u kappa k := by
  classical
  apply Finset.sum_le_sum
  intro p hp
  by_cases h : kappa p = k <;> simp [finiteProfileMeet, h]

theorem finiteProfileMeet_fiberMass_le_right
    {P K : Type*} [Fintype P] [DecidableEq K]
    (u v : P → ℝ) (kappa : P → K) (k : K) :
    finiteSignedFiberMass (finiteProfileMeet u v) kappa k ≤
      finiteSignedFiberMass v kappa k := by
  classical
  apply Finset.sum_le_sum
  intro p hp
  by_cases h : kappa p = k <;> simp [finiteProfileMeet, h]

theorem finiteOverlapDefect_nonneg
    {P K : Type*} [Fintype P] [DecidableEq K]
    (u v : P → ℝ) (kappa : P → K) (k : K) :
    0 ≤ finiteOverlapDefect u v kappa k := by
  rw [finiteOverlapDefect]
  exact sub_nonneg.mpr (le_min
    (finiteProfileMeet_fiberMass_le_left u v kappa k)
    (finiteProfileMeet_fiberMass_le_right u v kappa k))

theorem finiteOverlapDefect_comp
    {P K L : Type*} [Fintype P] [Fintype K]
    [DecidableEq K] [DecidableEq L]
    (u v : P → ℝ) (kappa : P → K) (lambda : K → L) (l : L) :
    finiteOverlapDefect u v (lambda ∘ kappa) l =
      finiteOverlapDefect
          (fun k => finiteSignedFiberMass u kappa k)
          (fun k => finiteSignedFiberMass v kappa k) lambda l +
        finiteSignedFiberMass (fun k => finiteOverlapDefect u v kappa k) lambda l := by
  classical
  rw [finiteOverlapDefect,
    finiteSignedFiberMass_comp u kappa lambda l,
    finiteSignedFiberMass_comp v kappa lambda l,
    finiteSignedFiberMass_comp (finiteProfileMeet u v) kappa lambda l,
    finiteOverlapDefect]
  simp only [finiteOverlapDefect]
  rw [finiteSignedFiberMass_sub]
  have hmeet :
      finiteProfileMeet
          (fun k => finiteSignedFiberMass u kappa k)
          (fun k => finiteSignedFiberMass v kappa k) =
        fun k => min (finiteSignedFiberMass u kappa k)
          (finiteSignedFiberMass v kappa k) := rfl
  rw [hmeet]
  ring

def finiteProfileTotalVariation {P : Type*} [Fintype P]
    (u v : P → ℝ) : ℝ :=
  (∑ p, |u p - v p|) / 2

def finiteOverlapDefectMass {P K : Type*} [Fintype P] [Fintype K]
    [DecidableEq K] (u v : P → ℝ) (kappa : P → K) : ℝ :=
  ∑ k, finiteOverlapDefect u v kappa k

theorem abs_sub_eq_add_sub_two_min (a b : ℝ) :
    |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem finiteProfileTotalVariation_eq
    {P : Type*} [Fintype P] (u v : P → ℝ) :
    finiteProfileTotalVariation u v =
      ((∑ p, u p) + (∑ p, v p)) / 2 - ∑ p, finiteProfileMeet u v p := by
  classical
  rw [finiteProfileTotalVariation]
  simp_rw [abs_sub_eq_add_sub_two_min]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (∑ x, 2 * min (u x) (v x)) = 2 * ∑ x, min (u x) (v x) by
    rw [Finset.mul_sum]]
  unfold finiteProfileMeet
  ring

theorem finiteOverlapDefectMass_eq_totalVariation_loss
    {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (u v : P → ℝ) (kappa : P → K) :
    finiteOverlapDefectMass u v kappa =
      finiteProfileTotalVariation u v -
        finiteProfileTotalVariation
          (fun k => finiteSignedFiberMass u kappa k)
          (fun k => finiteSignedFiberMass v kappa k) := by
  classical
  rw [finiteOverlapDefectMass, finiteProfileTotalVariation_eq,
    finiteProfileTotalVariation_eq]
  simp_rw [finiteOverlapDefect]
  rw [Finset.sum_sub_distrib]
  have hu := finiteSignedCharge_eq_sum_fiberMass u kappa
  have hv := finiteSignedCharge_eq_sum_fiberMass v kappa
  have hm := finiteSignedCharge_eq_sum_fiberMass (finiteProfileMeet u v) kappa
  simp only [finiteSignedCharge] at hu hv hm
  rw [← hu, ← hv, ← hm]
  unfold finiteProfileMeet
  ring

theorem finiteSignedFiberMass_eq_zero_of_not_mem_range
    {P K : Type*} [Fintype P] [DecidableEq K]
    (mu : P → ℝ) (kappa : P → K) {k : K} (hk : k ∉ Set.range kappa) :
    finiteSignedFiberMass mu kappa k = 0 := by
  classical
  rw [finiteSignedFiberMass]
  apply Finset.sum_eq_zero
  intro p hp
  simp only [ite_eq_right_iff]
  intro hpk
  exact (hk ⟨p, hpk⟩).elim

theorem finiteOverlapDefect_eq_zero_of_injective
    {P K : Type*} [Fintype P] [DecidableEq K]
    (u v : P → ℝ) {kappa : P → K} (hkappa : Function.Injective kappa) (k : K) :
    finiteOverlapDefect u v kappa k = 0 := by
  classical
  rcases em (k ∈ Set.range kappa) with ⟨p, rfl⟩ | hk
  · rw [finiteOverlapDefect,
      finiteSignedFiberMass_eq_single_of_injective u hkappa p,
      finiteSignedFiberMass_eq_single_of_injective v hkappa p,
      finiteSignedFiberMass_eq_single_of_injective (finiteProfileMeet u v) hkappa p]
    simp [finiteProfileMeet]
  · rw [finiteOverlapDefect,
      finiteSignedFiberMass_eq_zero_of_not_mem_range u kappa hk,
      finiteSignedFiberMass_eq_zero_of_not_mem_range v kappa hk,
      finiteSignedFiberMass_eq_zero_of_not_mem_range (finiteProfileMeet u v) kappa hk]
    simp

theorem finiteOverlapDefect_universal_zero_iff_injective
    {P K : Type*} [Fintype P] [DecidableEq P] [DecidableEq K]
    (kappa : P → K) :
    (∀ (u v : P → ℝ) (k : K), finiteOverlapDefect u v kappa k = 0) ↔
      Function.Injective kappa := by
  constructor
  · intro h p q hpq
    by_contra hpqne
    let u : P → ℝ := fun x => if x = p then 1 else 0
    let v : P → ℝ := fun x => if x = q then 1 else 0
    have hzero := h u v (kappa p)
    have hmeet : finiteProfileMeet u v = 0 := by
      funext x
      by_cases hxp : x = p <;> by_cases hxq : x = q <;>
        simp [finiteProfileMeet, u, v, hxp, hxq, hpqne, Ne.symm hpqne]
    have hu : finiteSignedFiberMass u kappa (kappa p) = 1 := by
      classical
      rw [finiteSignedFiberMass]
      calc
        (∑ x, if kappa x = kappa p then u x else 0) =
            ∑ x, if x = p then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxp : x = p <;> simp [u, hxp]
        _ = 1 := by simp
    have hv : finiteSignedFiberMass v kappa (kappa p) = 1 := by
      classical
      rw [finiteSignedFiberMass]
      calc
        (∑ x, if kappa x = kappa p then v x else 0) =
            ∑ x, if x = q then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxq : x = q <;> simp [v, hxq, hpq]
        _ = 1 := by simp
    rw [finiteOverlapDefect, hu, hv, hmeet] at hzero
    norm_num [finiteSignedFiberMass] at hzero
  · intro hkappa u v k
    exact finiteOverlapDefect_eq_zero_of_injective u v hkappa k

def boolLeftProfile : Bool → ℝ := fun b => if b then 0 else 1

def boolRightProfile : Bool → ℝ := fun b => if b then 1 else 0

theorem bool_constantObserver_falseOverlap :
    finiteOverlapDefect boolLeftProfile boolRightProfile (fun _ : Bool => ()) () = 1 := by
  simp [finiteOverlapDefect, finiteSignedFiberMass, finiteProfileMeet,
    boolLeftProfile, boolRightProfile]

end

end HTGeometry
