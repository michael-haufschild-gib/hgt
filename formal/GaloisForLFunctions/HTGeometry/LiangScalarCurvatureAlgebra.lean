import Mathlib

/-!
# Liang scalar-curvature algebra

Finite-dimensional algebra from Liang's shifted semiconvex quadratic-form argument: Newton weights,
the exact D_k projection constant, its sharp constrained inequality, and an explicit maximizing
vector. These results are independent of the scalar-curvature PDE and require no RH hypothesis.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Liang

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sigmaOne (κ : ι → ℝ) : ℝ := ∑ i, κ i

def sigmaTwo (κ : ι → ℝ) : ℝ :=
  (sigmaOne κ ^ 2 - ∑ i, κ i ^ 2) / 2

/-- Ordered off-diagonal pair product. Its value is twice the second elementary symmetric sum. -/
def orderedPairProduct (κ : ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, κ i * κ j

def shiftedTrace (κ : ι → ℝ) (i : ι) : ℝ := sigmaOne κ - κ i

def sumSqAway (κ : ι → ℝ) (k : ι) : ℝ := ∑ i ∈ Finset.univ.erase k, κ i ^ 2

def sumAway (κ : ι → ℝ) (k : ι) : ℝ := ∑ i ∈ Finset.univ.erase k, κ i

def sigmaTwoAway (κ : ι → ℝ) (k : ι) : ℝ :=
  (shiftedTrace κ k ^ 2 - sumSqAway κ k) / 2

def dQuadratic (k : ι) (z : ι → ℝ) : ℝ :=
  z k ^ 2 + 3 * sumSqAway z k

def dInvPair (k : ι) (x y : ι → ℝ) : ℝ :=
  x k * y k + (1 / 3 : ℝ) * ∑ i ∈ Finset.univ.erase k, x i * y i

def dot (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

omit [DecidableEq ι] in
theorem sum_sq_eq_sigmaOne_sq_sub_two_sigmaTwo (κ : ι → ℝ) :
    ∑ i, κ i ^ 2 = sigmaOne κ ^ 2 - 2 * sigmaTwo κ := by
  simp [sigmaTwo]
  ring

theorem sigmaOne_sq_eq_sum_sq_add_orderedPairProduct (κ : ι → ℝ) :
    sigmaOne κ ^ 2 = (∑ i, κ i ^ 2) + orderedPairProduct κ := by
  have hprod : sigmaOne κ ^ 2 = ∑ i, ∑ j, κ i * κ j := by
    simp only [sigmaOne, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hprod]
  simp only [orderedPairProduct]
  calc
    ∑ i, ∑ j, κ i * κ j =
        ∑ i, ((∑ j ∈ Finset.univ.erase i, κ i * κ j) + κ i * κ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.sum_erase_add (s := Finset.univ)
        (f := fun j => κ i * κ j) (Finset.mem_univ i)).symm
    _ = (∑ i, κ i ^ 2) + ∑ i, ∑ j ∈ Finset.univ.erase i, κ i * κ j := by
      rw [Finset.sum_add_distrib]
      have hdiag : ∑ i, κ i * κ i = ∑ i, κ i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hdiag, add_comm]

theorem two_mul_sigmaTwo_eq_orderedPairProduct (κ : ι → ℝ) :
    2 * sigmaTwo κ = orderedPairProduct κ := by
  have hsplit := sigmaOne_sq_eq_sum_sq_add_orderedPairProduct κ
  simp only [sigmaTwo]
  nlinarith

theorem sigmaTwo_nonneg_of_nonneg (κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    0 ≤ sigmaTwo κ := by
  have hpairs : 0 ≤ orderedPairProduct κ := by
    exact Finset.sum_nonneg fun i hi =>
      Finset.sum_nonneg fun j hj => mul_nonneg (hκ i) (hκ j)
  have htwo := two_mul_sigmaTwo_eq_orderedPairProduct κ
  nlinarith

omit [DecidableEq ι] in
theorem sum_sq_le_sigmaOne_sq_of_sigmaTwo_nonneg
    (κ : ι → ℝ) (hσ₂ : 0 ≤ sigmaTwo κ) :
    ∑ i, κ i ^ 2 ≤ sigmaOne κ ^ 2 := by
  rw [sum_sq_eq_sigmaOne_sq_sub_two_sigmaTwo]
  linarith

theorem sum_sq_le_sigmaOne_sq_of_nonneg (κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∑ i, κ i ^ 2 ≤ sigmaOne κ ^ 2 :=
  sum_sq_le_sigmaOne_sq_of_sigmaTwo_nonneg κ (sigmaTwo_nonneg_of_nonneg κ hκ)

omit [DecidableEq ι] in
theorem sum_shiftedTrace (κ : ι → ℝ) :
    ∑ i, shiftedTrace κ i =
      ((Fintype.card ι : ℝ) - 1) * sigmaOne κ := by
  simp [shiftedTrace, sigmaOne, Finset.sum_sub_distrib]
  ring

omit [DecidableEq ι] in
theorem sum_sq_shiftedTrace (κ : ι → ℝ) :
    ∑ i, shiftedTrace κ i ^ 2 =
      ((Fintype.card ι : ℝ) - 1) * sigmaOne κ ^ 2 - 2 * sigmaTwo κ := by
  have hs : ∑ i, κ i ^ 2 = sigmaOne κ ^ 2 - 2 * sigmaTwo κ :=
    sum_sq_eq_sigmaOne_sq_sub_two_sigmaTwo κ
  simp only [shiftedTrace]
  calc
    ∑ i, (sigmaOne κ - κ i) ^ 2 =
        ∑ i, (sigmaOne κ ^ 2 - 2 * sigmaOne κ * κ i + κ i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (Fintype.card ι : ℝ) * sigmaOne κ ^ 2 -
        2 * sigmaOne κ * sigmaOne κ + ∑ i, κ i ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul]
      have hlin : ∑ i, 2 * sigmaOne κ * κ i =
          2 * sigmaOne κ * sigmaOne κ := by
        rw [← Finset.mul_sum]
        rfl
      rw [hlin]
      norm_num
    _ = ((Fintype.card ι : ℝ) - 1) * sigmaOne κ ^ 2 - 2 * sigmaTwo κ := by
      rw [hs]
      ring

theorem sumSqAway_add (κ : ι → ℝ) (k : ι) :
    sumSqAway κ k + κ k ^ 2 = ∑ i, κ i ^ 2 := by
  rw [sumSqAway]
  exact (Finset.sum_erase_add (s := Finset.univ)
    (f := fun i => κ i ^ 2) (Finset.mem_univ k))

theorem sumAway_add (κ : ι → ℝ) (k : ι) :
    sumAway κ k + κ k = sigmaOne κ := by
  exact Finset.sum_erase_add (s := Finset.univ) (f := κ) (Finset.mem_univ k)

theorem shiftedTrace_eq_sumAway (κ : ι → ℝ) (k : ι) :
    shiftedTrace κ k = sumAway κ k := by
  have h := sumAway_add κ k
  simp only [shiftedTrace]
  linarith

omit [Fintype ι] in
theorem entry_le_sum_add_complement_card_mul
    (κ : ι → ℝ) (s : Finset ι) {i : ι} (hi : i ∈ s) (K : ℝ)
    (hlower : ∀ j ∈ s, -K ≤ κ j) :
    κ i ≤ (∑ j ∈ s, κ j) + ((s.erase i).card : ℝ) * K := by
  have htail : ∑ j ∈ s.erase i, -K ≤ ∑ j ∈ s.erase i, κ j := by
    exact Finset.sum_le_sum fun j hj => hlower j (Finset.mem_of_mem_erase hj)
  have hsplit := Finset.sum_erase_add s κ hi
  simp only [Finset.sum_const, nsmul_eq_mul] at htail
  rw [← hsplit]
  linarith

/-- Pointwise tail estimate used in the large-trace lemma: a component is at most the tail sum
plus one copy of `K` for every other tail component. -/
theorem tail_entry_le_sumAway_add_card_mul
    (κ : ι → ℝ) (k i : ι) (hik : i ≠ k) (K : ℝ)
    (hlower : ∀ j, j ≠ k → -K ≤ κ j) :
    κ i ≤ sumAway κ k +
      ((((Finset.univ.erase k).erase i).card : ℕ) : ℝ) * K := by
  have hi : i ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩
  simpa only [sumAway] using
    entry_le_sum_add_complement_card_mul κ (Finset.univ.erase k) hi K
      (fun j hj => hlower j (Finset.mem_erase.mp hj).1)

theorem sigmaTwo_split_at (κ : ι → ℝ) (k : ι) :
    sigmaTwo κ = κ k * shiftedTrace κ k + sigmaTwoAway κ k := by
  have hs := sumSqAway_add κ k
  simp only [sigmaTwo, sigmaTwoAway, shiftedTrace]
  nlinarith

theorem sumAway_sq_le_card_mul_sumSqAway (κ : ι → ℝ) (k : ι) :
    sumAway κ k ^ 2 ≤
      ((Finset.univ.erase k).card : ℝ) * sumSqAway κ k := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase k)
    κ (fun _ : ι => (1 : ℝ))
  simpa [sumAway, sumSqAway, Finset.sum_const, nsmul_eq_mul, mul_comm] using h

theorem sigmaTwoAway_cauchy_upper (κ : ι → ℝ) (k : ι) :
    2 * ((Finset.univ.erase k).card : ℝ) * sigmaTwoAway κ k ≤
      (((Finset.univ.erase k).card : ℝ) - 1) * shiftedTrace κ k ^ 2 := by
  have hcs := sumAway_sq_le_card_mul_sumSqAway κ k
  rw [← shiftedTrace_eq_sumAway] at hcs
  simp only [sigmaTwoAway]
  nlinarith

theorem newton_weight_identity (κ : ι → ℝ) (k : ι) :
    shiftedTrace κ k * sigmaOne κ - sigmaTwo κ =
      (shiftedTrace κ k ^ 2 + sumSqAway κ k) / 2 := by
  have hs := sumSqAway_add κ k
  simp only [sigmaTwo, shiftedTrace]
  nlinarith

theorem sumSqAway_nonneg (κ : ι → ℝ) (k : ι) : 0 ≤ sumSqAway κ k := by
  exact Finset.sum_nonneg fun i hi => sq_nonneg _

theorem newton_weight_mul_sigmaOne_ge_sigmaTwo (κ : ι → ℝ) (k : ι) :
    sigmaTwo κ ≤ shiftedTrace κ k * sigmaOne κ := by
  have hid := newton_weight_identity κ k
  have haway := sumSqAway_nonneg κ k
  nlinarith [sq_nonneg (shiftedTrace κ k)]

theorem sigmaTwo_div_sigmaOne_le_shiftedTrace
    (κ : ι → ℝ) (k : ι) (hσ₁ : 0 < sigmaOne κ) :
    sigmaTwo κ / sigmaOne κ ≤ shiftedTrace κ k := by
  rw [div_le_iff₀ hσ₁]
  simpa [mul_comm] using newton_weight_mul_sigmaOne_ge_sigmaTwo κ k

def InGammaTwo (κ : ι → ℝ) : Prop :=
  0 < sigmaOne κ ∧ 0 < sigmaTwo κ

theorem shiftedTrace_pos_of_gammaTwo
    (κ : ι → ℝ) (hκ : InGammaTwo κ) (k : ι) :
    0 < shiftedTrace κ k := by
  have hdiv : 0 < sigmaTwo κ / sigmaOne κ := div_pos hκ.2 hκ.1
  exact lt_of_lt_of_le hdiv
    (sigmaTwo_div_sigmaOne_le_shiftedTrace κ k hκ.1)

omit [DecidableEq ι] in
theorem sigmaOne_div_card_le_max_entry
    (κ : ι → ℝ) (k : ι) (hmax : ∀ i, κ i ≤ κ k) :
    sigmaOne κ / (Fintype.card ι : ℝ) ≤ κ k := by
  letI : Nonempty ι := ⟨k⟩
  have hsum : sigmaOne κ ≤ ∑ _i : ι, κ k := by
    exact Finset.sum_le_sum fun i hi => hmax i
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hcard]
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum

/-- First line of the large-trace spectral structure theorem, isolated from its threshold
estimates: a maximal component lies between the average and the positive total trace. -/
theorem gammaTwo_max_entry_bounds
    (κ : ι → ℝ) (hκ : InGammaTwo κ) (k : ι) (hmax : ∀ i, κ i ≤ κ k) :
    sigmaOne κ / (Fintype.card ι : ℝ) ≤ κ k ∧ κ k < sigmaOne κ := by
  refine ⟨sigmaOne_div_card_le_max_entry κ k hmax, ?_⟩
  have hshift := shiftedTrace_pos_of_gammaTwo κ hκ k
  simpa [shiftedTrace] using hshift

theorem dInvPair_one_one (k : ι) :
    dInvPair k (fun _ => 1) (fun _ => 1) = ((Fintype.card ι : ℝ) + 2) / 3 := by
  letI : Nonempty ι := ⟨k⟩
  simp [dInvPair]
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  rw [Nat.cast_sub hcard]
  push_cast
  ring

theorem dInvPair_one_shiftedTrace (κ : ι → ℝ) (k : ι) :
    dInvPair k (fun _ => 1) (shiftedTrace κ) =
      (((Fintype.card ι : ℝ) - 1) * sigmaOne κ + 2 * shiftedTrace κ k) / 3 := by
  have hsum := sum_shiftedTrace κ
  have herase : ∑ i ∈ Finset.univ.erase k, shiftedTrace κ i =
      ((Fintype.card ι : ℝ) - 1) * sigmaOne κ - shiftedTrace κ k := by
    rw [← hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    ring
  simp only [dInvPair, one_mul]
  rw [herase]
  ring

theorem dInvPair_shiftedTrace_self (κ : ι → ℝ) (k : ι) :
    dInvPair k (shiftedTrace κ) (shiftedTrace κ) =
      (((Fintype.card ι : ℝ) - 1) * sigmaOne κ ^ 2 - 2 * sigmaTwo κ +
        2 * shiftedTrace κ k ^ 2) / 3 := by
  have hsum := sum_sq_shiftedTrace κ
  have herase : ∑ i ∈ Finset.univ.erase k, shiftedTrace κ i ^ 2 =
      ((Fintype.card ι : ℝ) - 1) * sigmaOne κ ^ 2 - 2 * sigmaTwo κ -
        shiftedTrace κ k ^ 2 := by
    rw [← hsum, ← Finset.sum_erase_add _ (fun i => shiftedTrace κ i ^ 2)
      (Finset.mem_univ k)]
    ring
  simp only [dInvPair]
  have herase' : ∑ i ∈ Finset.univ.erase k,
      shiftedTrace κ i * shiftedTrace κ i =
      ((Fintype.card ι : ℝ) - 1) * sigmaOne κ ^ 2 - 2 * sigmaTwo κ -
        shiftedTrace κ k ^ 2 := by
    simpa [pow_two] using herase
  rw [herase']
  ring

def dWeight (k i : ι) : ℝ := if i = k then 1 else 3

omit [Fintype ι] in
theorem dWeight_pos (k i : ι) : 0 < dWeight k i := by
  by_cases h : i = k <;> simp [dWeight, h]

theorem sum_dWeight_mul_sq_eq_dQuadratic (k : ι) (z : ι → ℝ) :
    ∑ i, dWeight k i * z i ^ 2 = dQuadratic k z := by
  calc
    ∑ i, dWeight k i * z i ^ 2 =
        (∑ i ∈ Finset.univ.erase k, dWeight k i * z i ^ 2) +
          dWeight k k * z k ^ 2 :=
      (Finset.sum_erase_add Finset.univ
        (fun i => dWeight k i * z i ^ 2) (Finset.mem_univ k)).symm
    _ = (∑ i ∈ Finset.univ.erase k, 3 * z i ^ 2) + z k ^ 2 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hik : i ≠ k := (Finset.mem_erase.mp hi).1
        simp [dWeight, hik]
      · simp [dWeight]
    _ = dQuadratic k z := by
      simp only [dQuadratic, sumSqAway]
      rw [Finset.mul_sum]
      ring

theorem sum_sq_div_dWeight_eq_dInvPair_self (k : ι) (x : ι → ℝ) :
    ∑ i, x i ^ 2 / dWeight k i = dInvPair k x x := by
  calc
    ∑ i, x i ^ 2 / dWeight k i =
        (∑ i ∈ Finset.univ.erase k, x i ^ 2 / dWeight k i) +
          x k ^ 2 / dWeight k k :=
      (Finset.sum_erase_add Finset.univ
        (fun i => x i ^ 2 / dWeight k i) (Finset.mem_univ k)).symm
    _ = (∑ i ∈ Finset.univ.erase k, x i ^ 2 / 3) + x k ^ 2 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hik : i ≠ k := (Finset.mem_erase.mp hi).1
        simp [dWeight, hik]
      · simp [dWeight]
    _ = dInvPair k x x := by
      simp only [dInvPair, pow_two]
      rw [Finset.mul_sum]
      have hsum : ∑ i ∈ Finset.univ.erase k, x i * x i / 3 =
          ∑ i ∈ Finset.univ.erase k, 1 / 3 * (x i * x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsum]
      ring

theorem weighted_cauchy (k : ι) (x z : ι → ℝ) :
    dot x z ^ 2 ≤ dInvPair k x x * dQuadratic k z := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ) (r := fun i => x i * z i)
    (f := fun i => x i ^ 2 / dWeight k i)
    (g := fun i => dWeight k i * z i ^ 2)
    (fun i hi => div_nonneg (sq_nonneg _) (le_of_lt (dWeight_pos k i)))
    (fun i hi => mul_nonneg (le_of_lt (dWeight_pos k i)) (sq_nonneg _))
    (fun i hi => by
      have hn : dWeight k i ≠ 0 := ne_of_gt (dWeight_pos k i)
      field_simp
      exact le_rfl)
  have h' : (∑ i, x i * z i) ^ 2 ≤
      (∑ i, x i ^ 2 / dWeight k i) * ∑ i, dWeight k i * z i ^ 2 := by
    simpa using h
  rw [sum_sq_div_dWeight_eq_dInvPair_self,
    sum_dWeight_mul_sq_eq_dQuadratic] at h'
  exact h'

theorem weighted_cauchy_dForm (k : ι) (x z : ι → ℝ) :
    dot x z ^ 2 ≤ dInvPair k x x * dQuadratic k z := by
  have h := weighted_cauchy k x z
  exact h

noncomputable def dInvForm (k : ι) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (dInvPair k)
    (by
      intro x y z
      simp only [dInvPair, Pi.add_apply]
      have hsum : ∑ i ∈ Finset.univ.erase k, (x i + y i) * z i =
          (∑ i ∈ Finset.univ.erase k, x i * z i) +
            ∑ i ∈ Finset.univ.erase k, y i * z i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsum]
      ring)
    (by
      intro a x y
      simp only [dInvPair, Pi.smul_apply, smul_eq_mul]
      have hsum : ∑ i ∈ Finset.univ.erase k, a * x i * y i =
          a * ∑ i ∈ Finset.univ.erase k, x i * y i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsum]
      ring)
    (by
      intro x y z
      simp only [dInvPair, Pi.add_apply]
      have hsum : ∑ i ∈ Finset.univ.erase k, x i * (y i + z i) =
          (∑ i ∈ Finset.univ.erase k, x i * y i) +
            ∑ i ∈ Finset.univ.erase k, x i * z i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsum]
      ring)
    (by
      intro a x y
      simp only [dInvPair, Pi.smul_apply, smul_eq_mul]
      have hsum : ∑ i ∈ Finset.univ.erase k, x i * (a * y i) =
          a * ∑ i ∈ Finset.univ.erase k, x i * y i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsum]
      ring)

@[simp] theorem dInvForm_apply (k : ι) (x y : ι → ℝ) :
    dInvForm k x y = dInvPair k x y := rfl

theorem dInvPair_symm (k : ι) (x y : ι → ℝ) :
    dInvPair k x y = dInvPair k y x := by
  simp only [dInvPair]
  congr 1
  · ring
  · apply congrArg ((1 / 3 : ℝ) * ·)
    apply Finset.sum_congr rfl
    intro i hi
    ring

def oneVector : ι → ℝ := fun _ => 1

def projectedOne (k : ι) (ell : ι → ℝ) : ι → ℝ :=
  oneVector - (dInvPair k oneVector ell / dInvPair k ell ell) • ell

def projectionBound (k : ι) (ell : ι → ℝ) : ℝ :=
  dInvPair k oneVector oneVector -
    dInvPair k oneVector ell ^ 2 / dInvPair k ell ell

theorem projection_scalar_identity (A B C : ℝ) (hC : C ≠ 0) :
    A - 2 * (B / C) * B + (B / C) ^ 2 * C = A - B ^ 2 / C := by
  field_simp [hC]
  ring

theorem dInvPair_projectedOne_self (k : ι) (ell : ι → ℝ)
    (hC : dInvPair k ell ell ≠ 0) :
    dInvPair k (projectedOne k ell) (projectedOne k ell) =
      projectionBound k ell := by
  calc
    dInvPair k (projectedOne k ell) (projectedOne k ell) =
        dInvPair k oneVector oneVector -
          2 * (dInvPair k oneVector ell / dInvPair k ell ell) *
            dInvPair k oneVector ell +
          (dInvPair k oneVector ell / dInvPair k ell ell) ^ 2 *
            dInvPair k ell ell := by
      change dInvForm k (projectedOne k ell) (projectedOne k ell) = _
      simp only [projectedOne, map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, dInvForm_apply]
      rw [dInvPair_symm k ell oneVector]
      ring
    _ = projectionBound k ell := by
      rw [projectionBound]
      exact projection_scalar_identity _ _ _ hC

theorem dot_projectedOne_of_constraint (k : ι) (ell z : ι → ℝ)
    (hz : dot ell z = 0) :
    dot (projectedOne k ell) z = sigmaOne z := by
  simp only [dot, projectedOne, oneVector, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have hmul : ∑ i, dInvPair k (fun _ => 1) ell / dInvPair k ell ell * ell i * z i =
      dInvPair k (fun _ => 1) ell / dInvPair k ell ell * dot ell z := by
    rw [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    ∑ i, (1 - dInvPair k (fun _ => 1) ell / dInvPair k ell ell * ell i) * z i =
        (∑ i, z i) -
          ∑ i, dInvPair k (fun _ => 1) ell / dInvPair k ell ell * ell i * z i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, z i) -
        dInvPair k (fun _ => 1) ell / dInvPair k ell ell * dot ell z := by
      rw [hmul]
    _ = sigmaOne z := by simp [hz, sigmaOne]

theorem constrained_projection_bound (k : ι) (ell z : ι → ℝ)
    (hC : dInvPair k ell ell ≠ 0) (hz : dot ell z = 0) :
    sigmaOne z ^ 2 ≤ projectionBound k ell * dQuadratic k z := by
  have h := weighted_cauchy k (projectedOne k ell) z
  rw [dot_projectedOne_of_constraint k ell z hz,
    dInvPair_projectedOne_self k ell hC] at h
  exact h

def shiftedProjectionFormula (k : ι) (κ : ι → ℝ) : ℝ :=
  (1 / 3 : ℝ) * ((Fintype.card ι : ℝ) + 2 -
    (((Fintype.card ι : ℝ) - 1) * sigmaOne κ + 2 * shiftedTrace κ k) ^ 2 /
      (((Fintype.card ι : ℝ) - 1) * sigmaOne κ ^ 2 - 2 * sigmaTwo κ +
        2 * shiftedTrace κ k ^ 2))

theorem projectionBound_shiftedTrace (k : ι) (κ : ι → ℝ)
    (hC : dInvPair k (shiftedTrace κ) (shiftedTrace κ) ≠ 0) :
    projectionBound k (shiftedTrace κ) = shiftedProjectionFormula k κ := by
  rw [projectionBound]
  change dInvPair k (fun _ : ι => 1) (fun _ : ι => 1) -
      dInvPair k (fun _ : ι => 1) (shiftedTrace κ) ^ 2 /
        dInvPair k (shiftedTrace κ) (shiftedTrace κ) = _
  rw [dInvPair_one_one,
    dInvPair_one_shiftedTrace, dInvPair_shiftedTrace_self]
  have hden : ((Fintype.card ι : ℝ) - 1) * sigmaOne κ ^ 2 -
      2 * sigmaTwo κ + 2 * shiftedTrace κ k ^ 2 ≠ 0 := by
    intro hzero
    apply hC
    rw [dInvPair_shiftedTrace_self, hzero]
    norm_num
  simp only [shiftedProjectionFormula]
  field_simp

theorem shiftedTrace_constrained_bound (k : ι) (κ z : ι → ℝ)
    (hC : dInvPair k (shiftedTrace κ) (shiftedTrace κ) ≠ 0)
    (hz : dot (shiftedTrace κ) z = 0) :
    sigmaOne z ^ 2 ≤ shiftedProjectionFormula k κ * dQuadratic k z := by
  rw [← projectionBound_shiftedTrace k κ hC]
  exact constrained_projection_bound k (shiftedTrace κ) z hC hz

def dInvApply (k : ι) (x : ι → ℝ) : ι → ℝ :=
  fun i => x i / dWeight k i

theorem sum_mul_div_dWeight_eq_dInvPair (k : ι) (x y : ι → ℝ) :
    ∑ i, x i * y i / dWeight k i = dInvPair k x y := by
  calc
    ∑ i, x i * y i / dWeight k i =
        (∑ i ∈ Finset.univ.erase k, x i * y i / dWeight k i) +
          x k * y k / dWeight k k :=
      (Finset.sum_erase_add Finset.univ
        (fun i => x i * y i / dWeight k i) (Finset.mem_univ k)).symm
    _ = (∑ i ∈ Finset.univ.erase k, x i * y i / 3) + x k * y k := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hik : i ≠ k := (Finset.mem_erase.mp hi).1
        simp [dWeight, hik]
      · simp [dWeight]
    _ = dInvPair k x y := by
      simp only [dInvPair]
      rw [Finset.mul_sum]
      have hsum : ∑ i ∈ Finset.univ.erase k, x i * y i / 3 =
          ∑ i ∈ Finset.univ.erase k, 1 / 3 * (x i * y i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hsum]
      ring

theorem dot_dInvApply (k : ι) (x y : ι → ℝ) :
    dot x (dInvApply k y) = dInvPair k x y := by
  rw [dot]
  calc
    ∑ i, x i * dInvApply k y i = ∑ i, x i * y i / dWeight k i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [dInvApply]
      ring
    _ = dInvPair k x y := sum_mul_div_dWeight_eq_dInvPair k x y

theorem dQuadratic_dInvApply (k : ι) (x : ι → ℝ) :
    dQuadratic k (dInvApply k x) = dInvPair k x x := by
  rw [← sum_dWeight_mul_sq_eq_dQuadratic,
    ← sum_sq_div_dWeight_eq_dInvPair_self]
  apply Finset.sum_congr rfl
  intro i hi
  have hw : dWeight k i ≠ 0 := ne_of_gt (dWeight_pos k i)
  simp only [dInvApply]
  field_simp

theorem dInvPair_ell_projectedOne (k : ι) (ell : ι → ℝ)
    (hC : dInvPair k ell ell ≠ 0) :
    dInvPair k ell (projectedOne k ell) = 0 := by
  change dInvForm k ell (projectedOne k ell) = 0
  simp only [projectedOne, map_sub, map_smul, smul_eq_mul, dInvForm_apply]
  rw [dInvPair_symm k ell oneVector]
  field_simp [hC]
  ring

theorem dInvPair_one_projectedOne (k : ι) (ell : ι → ℝ)
    (hC : dInvPair k ell ell ≠ 0) :
    dInvPair k oneVector (projectedOne k ell) = projectionBound k ell := by
  change dInvForm k oneVector (projectedOne k ell) = _
  simp only [projectedOne, map_sub, map_smul, smul_eq_mul, dInvForm_apply,
    projectionBound]
  field_simp [hC]

theorem dQuadratic_pos (k : ι) {z : ι → ℝ} (hz : z ≠ 0) :
    0 < dQuadratic k z := by
  rw [← sum_dWeight_mul_sq_eq_dQuadratic]
  have hex : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (le_of_lt (dWeight_pos k j)) (sq_nonneg _)
  · exact ⟨i, Finset.mem_univ i,
      mul_pos (dWeight_pos k i) (sq_pos_of_ne_zero hi)⟩

theorem exists_exact_constrained_maximizer (k : ι) (ell : ι → ℝ)
    (hC : dInvPair k ell ell ≠ 0) (hR : 0 < projectionBound k ell) :
    ∃ z : ι → ℝ, z ≠ 0 ∧ dot ell z = 0 ∧
      sigmaOne z ^ 2 / dQuadratic k z = projectionBound k ell ∧
      ∀ w : ι → ℝ, w ≠ 0 → dot ell w = 0 →
        sigmaOne w ^ 2 / dQuadratic k w ≤ projectionBound k ell := by
  let z := dInvApply k (projectedOne k ell)
  have hzConstraint : dot ell z = 0 := by
    change dot ell (dInvApply k (projectedOne k ell)) = 0
    rw [dot_dInvApply, dInvPair_ell_projectedOne k ell hC]
  have hzD : dQuadratic k z = projectionBound k ell := by
    change dQuadratic k (dInvApply k (projectedOne k ell)) = projectionBound k ell
    rw [dQuadratic_dInvApply,
      dInvPair_projectedOne_self k ell hC]
  have hzSum : sigmaOne z = projectionBound k ell := by
    change sigmaOne (dInvApply k (projectedOne k ell)) = projectionBound k ell
    rw [← dInvPair_one_projectedOne k ell hC, ← dot_dInvApply]
    simp [sigmaOne, dot, oneVector]
  have hzNe : z ≠ 0 := by
    intro hz
    rw [hz] at hzD
    simp [dQuadratic, sumSqAway] at hzD
    linarith
  refine ⟨z, hzNe, hzConstraint, ?_, ?_⟩
  · rw [hzSum, hzD]
    field_simp [ne_of_gt hR]
  · intro w hwNe hwConstraint
    rw [div_le_iff₀ (dQuadratic_pos k hwNe)]
    simpa [mul_comm] using constrained_projection_bound k ell w hC hwConstraint

end GaloisForLFunctions.HTGeometry.Liang
