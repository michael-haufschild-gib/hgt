import GaloisForLFunctions.CompletedArithmeticForms.DivisorCovariance

/-!
# Terminal completion of finite accumulated source packets

Completing the constant-prefix tail replaces the maximum-index bridge by its
full covariance kernel. The weighted dual coupling has a free terminal value;
its local variation therefore pays only the initial boundary edge.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower.DeletionAveragedDivisor

/-- Finite accumulated source energy with its exact constant-prefix tail mass. -/
def finiteSourceEnergy (c : ℕ → ℝ) (T : ℕ) : ℝ :=
  cumulativeEnergy c T + (∑ j ∈ Icc 1 T, c j) ^ 2 / ((T : ℝ) + 1)

/-- The completed covariance contains every unequal pair at the full maximum-index kernel. -/
theorem finiteSourceEnergy_eq_covariance (c : ℕ → ℝ) (T : ℕ) :
    finiteSourceEnergy c T = ∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T,
      c j * c k / (max j k : ℕ) := by
  have hm : (∑ j ∈ Icc 1 T, c j) ^ 2 / ((T : ℝ) + 1) =
      ∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, c j * c k / ((T : ℝ) + 1) := by
    simp only [pow_two, sum_mul, mul_sum, sum_div]
    rw [sum_comm]
  rw [finiteSourceEnergy, cumulativeEnergy_eq_covariance, hm, ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  unfold cumulativeKernel
  ring

theorem finiteSourceEnergy_nonneg (c : ℕ → ℝ) (T : ℕ) : 0 ≤ finiteSourceEnergy c T := by
  unfold finiteSourceEnergy cumulativeEnergy
  exact add_nonneg (sum_nonneg fun n hn => div_nonneg (sq_nonneg _) (by positivity))
    (div_nonneg (sq_nonneg _) (by positivity))

/-- One further source increment completes a square in the total prefix mass. -/
theorem finiteSourceEnergy_succ (c : ℕ → ℝ) (T : ℕ) :
    finiteSourceEnergy c (T + 1) = cumulativeEnergy c T +
      ((∑ j ∈ Icc 1 T, c j) + c (T + 1)) ^ 2 / ((T : ℝ) + 1) := by
  have hp : (∑ j ∈ Icc 1 (T + 1), c j) = (∑ j ∈ Icc 1 T, c j) + c (T + 1) :=
    sum_Icc_succ_top (by omega) c
  have hc : cumulativeEnergy c (T + 1) = cumulativeEnergy c T +
      ((∑ j ∈ Icc 1 T, c j) + c (T + 1)) ^ 2 /
        (((T + 1 : ℕ) : ℝ) * (((T + 1 : ℕ) : ℝ) + 1)) := by
    unfold cumulativeEnergy
    rw [sum_Icc_succ_top (by omega), hp]
  rw [finiteSourceEnergy, hc, hp]
  push_cast
  field_simp [show (T : ℝ) + 1 ≠ 0 by positivity, show (T : ℝ) + 2 ≠ 0 by positivity]
  ring

/-- Source truncation changes the full energy by the signed terminal mass-square difference. -/
theorem finiteSourceEnergy_succ_sub (c : ℕ → ℝ) (T : ℕ) :
    finiteSourceEnergy c (T + 1) - finiteSourceEnergy c T =
      c (T + 1) * (2 * (∑ j ∈ Icc 1 T, c j) + c (T + 1)) / ((T : ℝ) + 1) := by
  rw [finiteSourceEnergy_succ, finiteSourceEnergy]
  ring

/-- A new source coordinate increases complete energy exactly on the terminal mass-sign domain. -/
theorem finiteSourceEnergy_le_succ_iff (c : ℕ → ℝ) (T : ℕ) :
    finiteSourceEnergy c T ≤ finiteSourceEnergy c (T + 1) ↔
      0 ≤ c (T + 1) * (2 * (∑ j ∈ Icc 1 T, c j) + c (T + 1)) := by
  rw [← sub_nonneg, finiteSourceEnergy_succ_sub]
  constructor
  · intro h
    have he := (le_div_iff₀ (by positivity : (0 : ℝ) < (T : ℝ) + 1)).mp h
    simpa only [zero_mul] using he
  · intro h
    exact div_nonneg h (by positivity)

/-- Weighted coupling with constant continuation beyond the last source coordinate. -/
def freeBoundaryCoupling (T : ℕ) (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i ≤ T then (i : ℝ) * b i else (T : ℝ) * b T

/-- The zero-boundary representative after removal of the affine endpoint trace. -/
def centeredBoundaryCoupling (T : ℕ) (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  freeBoundaryCoupling T b i - (i : ℝ) / ((T : ℝ) + 1) * ((T : ℝ) * b T)

/-- Local weighted variation with the terminal Dirichlet edge removed. -/
def finiteSourceDualCost (b : ℕ → ℝ) (T : ℕ) : ℝ :=
  dirichletEnergy T (fun i => (i : ℝ) * b i)

theorem freeBoundaryCoupling_zero (T : ℕ) (b : ℕ → ℝ) : freeBoundaryCoupling T b 0 = 0 := by
  simp only [freeBoundaryCoupling, Nat.zero_le, if_true, Nat.cast_zero, zero_mul]

theorem freeBoundaryCoupling_of_le (T : ℕ) (b : ℕ → ℝ) {i : ℕ} (hi : i ≤ T) :
    freeBoundaryCoupling T b i = (i : ℝ) * b i := by
  simp only [freeBoundaryCoupling, if_pos hi]

theorem freeBoundaryCoupling_endpoint (T : ℕ) (b : ℕ → ℝ) :
    freeBoundaryCoupling T b (T + 1) = (T : ℝ) * b T := by
  simp only [freeBoundaryCoupling, if_neg (by omega : ¬ T + 1 ≤ T)]

theorem centeredBoundaryCoupling_zero (T : ℕ) (b : ℕ → ℝ) :
    centeredBoundaryCoupling T b 0 = 0 := by
  simp only [centeredBoundaryCoupling, freeBoundaryCoupling_zero, Nat.cast_zero, zero_div,
    zero_mul, sub_self]

theorem centeredBoundaryCoupling_endpoint (T : ℕ) (b : ℕ → ℝ) :
    centeredBoundaryCoupling T b (T + 1) = 0 := by
  rw [centeredBoundaryCoupling, freeBoundaryCoupling_endpoint]
  simp only [Nat.cast_add, Nat.cast_one, div_self (by positivity : (T : ℝ) + 1 ≠ 0),
    one_mul, sub_self]

private theorem dirichletEnergy_remove_endpoint {Q : ℕ} (hQ : 0 < Q)
    (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    dirichletEnergy Q (fun i => f i - (i : ℝ) / Q * f Q) =
      dirichletEnergy Q f - f Q ^ 2 / Q := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have he (i : ℕ) :
      ((f (i + 1) - ((i + 1 : ℕ) : ℝ) / Q * f Q) -
        (f i - (i : ℝ) / Q * f Q)) ^ 2 =
      (f (i + 1) - f i) ^ 2 - 2 * (f Q / Q) * (f (i + 1) - f i) + (f Q / Q) ^ 2 := by
    push_cast
    ring
  simp only [dirichletEnergy, he, sum_add_distrib, sum_sub_distrib]
  rw [← mul_sum, Finset.sum_range_sub]
  simp only [hf0, sub_zero, sum_const, card_range, nsmul_eq_mul]
  field_simp [hQr]
  ring

/-- Constant continuation makes the last edge carry zero energy. -/
theorem freeBoundaryCoupling_energy (T : ℕ) (b : ℕ → ℝ) :
    dirichletEnergy (T + 1) (freeBoundaryCoupling T b) = finiteSourceDualCost b T := by
  unfold dirichletEnergy finiteSourceDualCost
  rw [Finset.sum_range_succ, freeBoundaryCoupling_endpoint, freeBoundaryCoupling_of_le T b le_rfl]
  simp only [sub_self, zero_pow (by omega : (2 : ℕ) ≠ 0), add_zero]
  apply sum_congr rfl
  intro i hi
  rw [freeBoundaryCoupling_of_le T b (by have := mem_range.mp hi; omega),
    freeBoundaryCoupling_of_le T b (by have := mem_range.mp hi; omega)]

/-- The affine trace has exactly its endpoint square divided by conductor as energy. -/
theorem centeredBoundaryCoupling_energy (T : ℕ) (b : ℕ → ℝ) :
    dirichletEnergy (T + 1) (centeredBoundaryCoupling T b) =
      finiteSourceDualCost b T - ((T : ℝ) * b T) ^ 2 / ((T : ℝ) + 1) := by
  have h := dirichletEnergy_remove_endpoint (Nat.succ_pos T) (freeBoundaryCoupling T b)
    (freeBoundaryCoupling_zero T b)
  rw [freeBoundaryCoupling_endpoint, freeBoundaryCoupling_energy] at h
  unfold centeredBoundaryCoupling
  simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using h

private theorem centeredBoundaryCoupling_eq_extension {T i : ℕ} (b : ℕ → ℝ) (hi : i ≤ T + 1) :
    centeredBoundaryCoupling T b i =
      interiorExtension (T + 1) (fun j => (j : ℝ) * (b j - ((T : ℝ) * b T) / ((T : ℝ) + 1))) i := by
  by_cases hm : i ∈ Ico 1 (T + 1)
  · rw [interiorExtension, if_pos hm, centeredBoundaryCoupling,
      freeBoundaryCoupling_of_le T b (by have := (mem_Ico.mp hm).2; omega)]
    ring
  · have he : i = 0 ∨ i = T + 1 := by
      simp only [mem_Ico] at hm
      omega
    rw [interiorExtension, if_neg hm]
    rcases he with rfl | rfl
    · exact centeredBoundaryCoupling_zero T b
    · exact centeredBoundaryCoupling_endpoint T b

private theorem centeredBoundaryCoupling_extension_energy (T : ℕ) (b : ℕ → ℝ) :
    dirichletEnergy (T + 1)
      (interiorExtension (T + 1) (fun j => (j : ℝ) * (b j - ((T : ℝ) * b T) / ((T : ℝ) + 1)))) =
      finiteSourceDualCost b T - ((T : ℝ) * b T) ^ 2 / ((T : ℝ) + 1) := by
  rw [← centeredBoundaryCoupling_energy]
  unfold dirichletEnergy
  apply sum_congr rfl
  intro i hi
  rw [centeredBoundaryCoupling_eq_extension b (by have := mem_range.mp hi; omega),
    centeredBoundaryCoupling_eq_extension b (by have := mem_range.mp hi; omega)]

/-- Completing the source tail pays the terminal trace and exposes its remaining mass discrepancy. -/
theorem finiteSourceEnergy_schur_bound_with_mass (c b : ℕ → ℝ) (T : ℕ) :
    2 * (∑ j ∈ Icc 1 T, c j * b j) - finiteSourceEnergy c T ≤
      finiteSourceDualCost b T -
        ((∑ j ∈ Icc 1 T, c j) - (T : ℝ) * b T) ^ 2 / ((T : ℝ) + 1) := by
  have h := cumulativeEnergy_schur_bound c
    (fun j => b j - ((T : ℝ) * b T) / ((T : ℝ) + 1)) T
  rw [centeredBoundaryCoupling_extension_energy] at h
  have hs : (∑ j ∈ Icc 1 T, c j * (b j - ((T : ℝ) * b T) / ((T : ℝ) + 1))) =
      (∑ j ∈ Icc 1 T, c j * b j) -
        (((T : ℝ) * b T) / ((T : ℝ) + 1)) * ∑ j ∈ Icc 1 T, c j := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    ring
  rw [hs] at h
  have he : 2 * (∑ j ∈ Icc 1 T, c j * b j) - finiteSourceEnergy c T -
      (finiteSourceDualCost b T -
        ((∑ j ∈ Icc 1 T, c j) - (T : ℝ) * b T) ^ 2 / ((T : ℝ) + 1)) =
      (2 * ((∑ j ∈ Icc 1 T, c j * b j) -
        (((T : ℝ) * b T) / ((T : ℝ) + 1)) * ∑ j ∈ Icc 1 T, c j) - cumulativeEnergy c T) -
      (finiteSourceDualCost b T - ((T : ℝ) * b T) ^ 2 / ((T : ℝ) + 1)) := by
    unfold finiteSourceEnergy
    ring
  linarith only [h, he]

/-- Finite source support has no terminal Dirichlet edge in its dual payment. -/
theorem finiteSourceEnergy_schur_bound (c b : ℕ → ℝ) (T : ℕ) :
    2 * (∑ j ∈ Icc 1 T, c j * b j) - finiteSourceEnergy c T ≤ finiteSourceDualCost b T :=
  (finiteSourceEnergy_schur_bound_with_mass c b T).trans
    (sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity)))

private theorem Ico_one_succ (T : ℕ) : Ico 1 (T + 1) = Icc 1 T := by
  ext i
  simp only [mem_Ico, mem_Icc]
  omega

private theorem divisorGramEnergy_congr_interior (Q : ℕ) (a b : ℕ → ℝ)
    (hab : ∀ i ∈ Ico 1 Q, a i = b i) : divisorGramEnergy Q a = divisorGramEnergy Q b := by
  unfold divisorGramEnergy
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [hab i hi, hab j hj]

theorem cumulativeEnergy_weightedCoefficients (a : ℕ → ℝ) (T : ℕ) :
    cumulativeEnergy (fun j => (j : ℝ) * a j) T = divisorGramEnergy (T + 1) a / ((T : ℝ) + 1) := by
  have he := divisorGramEnergy_eq_cumulativeEnergy (fun j => (j : ℝ) * a j) T
  have hc : divisorGramEnergy (T + 1) (fun j => ((j : ℝ) * a j) / j) =
      divisorGramEnergy (T + 1) a := by
    apply divisorGramEnergy_congr_interior
    intro j hj
    have hj0 : (j : ℝ) ≠ 0 := by
      exact_mod_cast (show j ≠ 0 by have := (mem_Ico.mp hj).1; omega)
    field_simp [hj0]
  rw [hc] at he
  rw [he, mul_div_cancel_left₀ _ (by positivity)]

/-- The exact optimizing packet for the completed finite source domain. -/
def finiteSourceMaximizer (b : ℕ → ℝ) (T : ℕ) (j : ℕ) : ℝ :=
  (j : ℝ) * bridgeInverse (T + 1)
    (fun i => ((T : ℝ) + 1) * centeredBoundaryCoupling T b i) j

private theorem interiorExtension_eq_of_boundary (Q : ℕ) (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (hfQ : f Q = 0) (i : ℕ) (hi : i ≤ Q) :
    interiorExtension Q f i = f i := by
  by_cases hm : i ∈ Ico 1 Q
  · exact if_pos hm
  · have h : i = 0 ∨ i = Q := by
      simp only [mem_Ico] at hm
      omega
    rw [interiorExtension, if_neg hm]
    rcases h with rfl | rfl
    · exact hf0.symm
    · exact hfQ.symm

private theorem interiorExtension_energy_of_boundary (Q : ℕ) (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (hfQ : f Q = 0) :
    dirichletEnergy Q (interiorExtension Q f) = dirichletEnergy Q f := by
  unfold dirichletEnergy
  apply sum_congr rfl
  intro i hi
  rw [interiorExtension_eq_of_boundary Q f hf0 hfQ (i + 1) (by have := mem_range.mp hi; omega),
    interiorExtension_eq_of_boundary Q f hf0 hfQ i (by have := mem_range.mp hi; omega)]

/-- The optimizer is the local second difference with a free terminal edge. -/
theorem finiteSourceMaximizer_eq_localDifference (b : ℕ → ℝ) (T : ℕ)
    {j : ℕ} (hj : j ∈ Icc 1 T) :
    finiteSourceMaximizer b T j = (j : ℝ) * dirichletDifference (freeBoundaryCoupling T b) j := by
  have he := interiorExtension_eq_of_boundary (T + 1)
    (fun i => ((T : ℝ) + 1) * centeredBoundaryCoupling T b i)
    (by rw [centeredBoundaryCoupling_zero, mul_zero])
    (by rw [centeredBoundaryCoupling_endpoint, mul_zero])
  unfold finiteSourceMaximizer bridgeInverse dirichletDifference
  rw [he j (by have := (mem_Icc.mp hj).2; omega),
    he (j - 1) (by have := (mem_Icc.mp hj).2; omega),
    he (j + 1) (by have := (mem_Icc.mp hj).2; omega)]
  simp only [centeredBoundaryCoupling, Nat.cast_sub (mem_Icc.mp hj).1,
    Nat.cast_add, Nat.cast_one]
  field_simp [show (T : ℝ) + 1 ≠ 0 by positivity]
  ring

private theorem centeredBoundaryCoupling_bridgeCost (T : ℕ) (b : ℕ → ℝ) :
    bridgeSchurCost (T + 1) (fun i => ((T : ℝ) + 1) * centeredBoundaryCoupling T b i) =
      ((T : ℝ) + 1) * dirichletEnergy (T + 1) (centeredBoundaryCoupling T b) := by
  rw [bridgeSchurCost, interiorExtension_energy_of_boundary _ _
    (by rw [centeredBoundaryCoupling_zero, mul_zero])
    (by rw [centeredBoundaryCoupling_endpoint, mul_zero]), dirichletEnergy_mul]
  push_cast
  field_simp [show (T : ℝ) + 1 ≠ 0 by positivity]

/-- The optimizer's total increment is exactly the free terminal weighted coupling. -/
theorem finiteSourceMaximizer_mass (b : ℕ → ℝ) (T : ℕ) :
    (∑ j ∈ Icc 1 T, finiteSourceMaximizer b T j) = (T : ℝ) * b T := by
  by_cases hT : T = 0
  · subst T
    simp
  have hT0 : 0 < T := Nat.pos_of_ne_zero hT
  let B := fun i => ((T : ℝ) + 1) * centeredBoundaryCoupling T b i
  have hp := bridgePotential_bridgeInverse (Nat.succ_pos T) B
    (i := T) (mem_Ico.mpr ⟨hT0, by omega⟩)
  have hs : bridgePotential (T + 1) (bridgeInverse (T + 1) B) T =
      ∑ j ∈ Icc 1 T, finiteSourceMaximizer b T j := by
    rw [bridgePotential, Ico_one_succ]
    apply sum_congr rfl
    intro j hj
    have hk : bridgeKernel (T + 1) T j = (j : ℝ) := by
      rw [bridgeKernel, min_eq_right (mem_Icc.mp hj).2]
      push_cast
      ring
    rw [hk]
    rfl
  rw [hs] at hp
  rw [hp]
  dsimp only [B]
  rw [centeredBoundaryCoupling, freeBoundaryCoupling_of_le T b le_rfl]
  field_simp [show (T : ℝ) + 1 ≠ 0 by positivity]
  ring

private theorem finiteSourceMaximizer_cumulative (b : ℕ → ℝ) (T : ℕ) :
    cumulativeEnergy (finiteSourceMaximizer b T) T =
      dirichletEnergy (T + 1) (centeredBoundaryCoupling T b) := by
  change cumulativeEnergy (fun j => (j : ℝ) * bridgeInverse (T + 1)
    (fun i => ((T : ℝ) + 1) * centeredBoundaryCoupling T b i) j) T = _
  rw [cumulativeEnergy_weightedCoefficients, divisorGramEnergy_bridgeInverse (Nat.succ_pos T),
    centeredBoundaryCoupling_bridgeCost, mul_div_cancel_left₀ _ (by positivity)]

/-- The maximizing packet has exactly the local weighted variation as complete source energy. -/
theorem finiteSourceMaximizer_energy (b : ℕ → ℝ) (T : ℕ) :
    finiteSourceEnergy (finiteSourceMaximizer b T) T = finiteSourceDualCost b T := by
  rw [finiteSourceEnergy, finiteSourceMaximizer_cumulative, finiteSourceMaximizer_mass,
    centeredBoundaryCoupling_energy]
  ring

/-- Terminal completion retains the exact full covariance norm of the optimizer residual. -/
theorem finiteSourceEnergy_completion (c b : ℕ → ℝ) (T : ℕ) :
    finiteSourceEnergy c T - 2 * (∑ j ∈ Icc 1 T, c j * b j) + finiteSourceDualCost b T =
      finiteSourceEnergy (fun j => c j - finiteSourceMaximizer b T j) T := by
  let B := fun i => ((T : ℝ) + 1) * centeredBoundaryCoupling T b i
  let a := fun j => c j / (j : ℝ)
  have hQ : (T : ℝ) + 1 ≠ 0 := by positivity
  have hb := bridgeSchur_completion (Nat.succ_pos T) a B
  have hleft : divisorGramEnergy (T + 1) a = ((T : ℝ) + 1) * cumulativeEnergy c T :=
    divisorGramEnergy_eq_cumulativeEnergy c T
  have hright : divisorGramEnergy (T + 1) (fun j => a j - bridgeInverse (T + 1) B j) =
      ((T : ℝ) + 1) * cumulativeEnergy (fun j => c j - finiteSourceMaximizer b T j) T := by
    rw [← divisorGramEnergy_eq_cumulativeEnergy]
    apply divisorGramEnergy_congr_interior
    intro j hj
    have hj0 : (j : ℝ) ≠ 0 := by
      exact_mod_cast (show j ≠ 0 by have := (mem_Ico.mp hj).1; omega)
    change c j / j - bridgeInverse (T + 1) B j =
      (c j - (j : ℝ) * bridgeInverse (T + 1) B j) / j
    field_simp [hj0]
  have hpair : (∑ j ∈ Ico 1 (T + 1), a j * B j) =
      ((T : ℝ) + 1) * (∑ j ∈ Icc 1 T, c j * b j) -
        ((T : ℝ) * b T) * (∑ j ∈ Icc 1 T, c j) := by
    rw [Ico_one_succ, mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    have hj0 : (j : ℝ) ≠ 0 := by
      exact_mod_cast (show j ≠ 0 by have := (mem_Icc.mp hj).1; omega)
    dsimp only [a, B]
    rw [centeredBoundaryCoupling, freeBoundaryCoupling_of_le T b (mem_Icc.mp hj).2]
    field_simp [hj0, hQ]
  have hcost : bridgeSchurCost (T + 1) B =
      ((T : ℝ) + 1) * (finiteSourceDualCost b T - ((T : ℝ) * b T) ^ 2 / ((T : ℝ) + 1)) := by
    rw [show B = (fun i => ((T : ℝ) + 1) * centeredBoundaryCoupling T b i) from rfl,
      centeredBoundaryCoupling_bridgeCost, centeredBoundaryCoupling_energy]
  apply mul_left_cancel₀ hQ
  calc
    _ = (divisorGramEnergy (T + 1) a - 2 * (∑ j ∈ Ico 1 (T + 1), a j * B j) +
        bridgeSchurCost (T + 1) B) +
          ((∑ j ∈ Icc 1 T, c j) - (T : ℝ) * b T) ^ 2 := by
      rw [hleft, hpair, hcost, finiteSourceEnergy]
      field_simp [hQ]
      ring
    _ = _ := by
      rw [hb, hright, finiteSourceEnergy, sum_sub_distrib, finiteSourceMaximizer_mass]
      field_simp [hQ]

/-- Full maximum-index covariance has no nonzero radical on its finite source coordinates. -/
theorem finiteSourceEnergy_eq_zero_iff (c : ℕ → ℝ) (T : ℕ) :
    finiteSourceEnergy c T = 0 ↔ ∀ j ∈ Icc 1 T, c j = 0 := by
  have hC : 0 ≤ cumulativeEnergy c T :=
    sum_nonneg fun n hn => div_nonneg (sq_nonneg _) (by positivity)
  have hmass : 0 ≤ (∑ j ∈ Icc 1 T, c j) ^ 2 / ((T : ℝ) + 1) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have hbridge := divisorGramEnergy_eq_cumulativeEnergy c T
  constructor
  · intro h
    have hz : cumulativeEnergy c T = 0 := by
      unfold finiteSourceEnergy at h
      linarith only [h, hC, hmass]
    rw [hz, mul_zero] at hbridge
    have hc := (divisorGramEnergy_eq_zero_iff (Nat.succ_pos T) _).mp hbridge
    intro j hj
    have he := hc j (by rw [Ico_one_succ]; exact hj)
    have hj0 : (j : ℝ) ≠ 0 := by
      exact_mod_cast (show j ≠ 0 by have := (mem_Icc.mp hj).1; omega)
    exact (div_eq_zero_iff).mp he |>.resolve_right hj0
  · intro hc
    have hz : divisorGramEnergy (T + 1) (fun j => c j / j) = 0 := by
      apply (divisorGramEnergy_eq_zero_iff (Nat.succ_pos T) _).mpr
      intro j hj
      rw [hc j (by rw [Ico_one_succ] at hj; exact hj), zero_div]
    have hcum : cumulativeEnergy c T = 0 := by
      rw [hz] at hbridge
      exact (mul_eq_zero.mp hbridge.symm).resolve_left (by positivity)
    rw [finiteSourceEnergy, hcum, sum_eq_zero hc]
    simp

/-- Equality in the sharp free-terminal payment determines every source coordinate. -/
theorem finiteSourceEnergy_schur_equality_iff (c b : ℕ → ℝ) (T : ℕ) :
    2 * (∑ j ∈ Icc 1 T, c j * b j) - finiteSourceEnergy c T = finiteSourceDualCost b T ↔
      ∀ j ∈ Icc 1 T, c j = finiteSourceMaximizer b T j := by
  have he := finiteSourceEnergy_completion c b T
  have hz : (2 * (∑ j ∈ Icc 1 T, c j * b j) - finiteSourceEnergy c T = finiteSourceDualCost b T) ↔
      finiteSourceEnergy (fun j => c j - finiteSourceMaximizer b T j) T = 0 := by
    constructor <;> intro h <;> linarith only [he, h]
  rw [hz, finiteSourceEnergy_eq_zero_iff]
  simp only [sub_eq_zero]

/-- The free-terminal variation is the sharp attained dual norm of the completed source packet. -/
theorem finiteSourceDualCost_isGreatest (b : ℕ → ℝ) (T : ℕ) :
    IsGreatest {r : ℝ | ∃ c : ℕ → ℝ,
      r = 2 * (∑ j ∈ Icc 1 T, c j * b j) - finiteSourceEnergy c T} (finiteSourceDualCost b T) := by
  constructor
  · refine ⟨finiteSourceMaximizer b T, ?_⟩
    exact ((finiteSourceEnergy_schur_equality_iff _ b T).mpr (fun _ _ => rfl)).symm
  · rintro r ⟨c, rfl⟩
    exact finiteSourceEnergy_schur_bound c b T

#print axioms finiteSourceEnergy_eq_covariance
#print axioms centeredBoundaryCoupling_energy
#print axioms finiteSourceEnergy_schur_bound_with_mass
#print axioms finiteSourceEnergy_schur_bound
#print axioms finiteSourceMaximizer_mass
#print axioms finiteSourceMaximizer_energy
#print axioms finiteSourceDualCost_isGreatest
#print axioms finiteSourceMaximizer_eq_localDifference
#print axioms finiteSourceEnergy_completion
#print axioms finiteSourceEnergy_schur_equality_iff

end GaloisForLFunctions.CompletedArithmeticForms
