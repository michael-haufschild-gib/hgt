import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.NewtonExtrapolationOfTheModularEnergy
import GaloisForLFunctions.HTGeometry.DiscreteMomentHankel

/-!
# Strict moment geometry in both radiation coordinates

Positive energy beyond every time forces nonzero release on infinitely
many unit intervals, despite possible stalls. The Laplace and difference
indices of a signed Newton reading are moments in the complementary
nodes x and 1-x. Every arithmetic subsequence in either coordinate has
strictly positive Hankel matrices of all orders.
-/

open Finset HTGeometry Polynomial
namespace GaloisForLFunctions.BlackHoleRingdown

noncomputable section

/-- Positive-time releases of a nonzero pulse have unbounded support. -/
theorem exists_late_positive_release (h : CompactPulse) (hne : ∃ t : ℝ, h t ≠ 0) (N : ℕ) :
    ∃ i : ℕ, N < i ∧ 0 < stepDecrement h i 1 := by
  by_contra! H
  have hs := shifted_releases_have_sum h (N+1)
  have hz (i : ℕ) : stepDecrement h (i+(N+1):ℕ) 1 = 0 :=
    le_antisymm (H _ (by omega)) (stepDecrement_nonneg _ _ _)
  simp only [hz,tsum_zero] at hs
  have ht : tailEnergy h (N+1:ℕ) = 0 := by rw [← hs.tsum_eq]; simp [hz]
  exact (tailEnergy_pos h hne _).ne' ht

/-- Signed difference of order d at the kth Laplace sample. -/
def radiationReading (h : CompactPulse) (k d : ℕ) :=
  (-1 : ℝ)^d * (fwdDiff 1)^[d] (radiationSample h) k

private def mass (h : CompactPulse) (a b i : ℕ) :=
  radiationNode i^a*(1-radiationNode i)^b*stepDecrement h i 1

private theorem mass_nn (h : CompactPulse) (a b i : ℕ) : 0 ≤ mass h a b i :=
  mul_nonneg (mul_nonneg (pow_nonneg (radiationNode_pos i).le _)
    (pow_nonneg (sub_nonneg.mpr (radiationNode_le_one i)) _)) (stepDecrement_nonneg _ _ _)

private theorem radiationNode_injective : Function.Injective radiationNode := by
  intro i j h
  have he := Real.exp_injective h
  change -(i:ℝ) = -(j:ℝ) at he
  exact Nat.cast_injective (neg_inj.mp he)

private theorem weighted_hankel (h : CompactPulse) (hne : ∃ t : ℝ, h t ≠ 0) (a b n : ℕ)
    (x : ℕ → ℝ) (hx : Function.Injective x) (hlo : ∀ i, 0 ≤ x i) (hhi : ∀ i, x i ≤ 1) :
    (momentHankelMatrix (fun k => ∑' i, mass h a b i*x i^k) n).PosDef := by
  classical
  apply discreteMomentHankel_posDef _ _ (mass_nn h a b)
  · intro k
    apply (summable_radiation_kernel h a b).of_nonneg_of_le
    · intro i
      exact mul_nonneg (mass_nn _ _ _ _) (pow_nonneg (abs_nonneg _) _)
    · intro i
      rw [abs_of_nonneg (hlo i)]
      exact mul_le_of_le_one_right (mass_nn _ _ _ _) (pow_le_one₀ (hlo i) (hhi i))
  · intro F
    obtain ⟨N,hN⟩ := (F.finite_toSet.preimage hx.injOn).bddAbove
    obtain ⟨i,hi,hi'⟩ := exists_late_positive_release h hne N
    refine ⟨i,fun hf => hi.not_ge (hN (show i ∈ x ⁻¹' (F:Set ℝ) from hf)),?_⟩
    have hlt : radiationNode i < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr
      (Nat.cast_pos.mpr (Nat.zero_le N |>.trans_lt hi)))
    exact mul_pos (mul_pos (pow_pos (radiationNode_pos i) _) (pow_pos (sub_pos.mpr hlt) _)) hi'

private theorem power_nodes {x : ℕ → ℝ} (hx : Function.Injective x) (hlo : ∀ i, 0 ≤ x i)
    {q : ℕ} (hq : 0 < q) : Function.Injective (fun i => x i^q) := by
  intro i j he
  exact hx ((pow_left_inj₀ (hlo i) (hlo j) hq.ne').mp he)

/-- Every shifted and decimated Laplace grid is strictly positive definite after
any order of differencing. -/
theorem radiationReading_sample_hankel_posDef (h : CompactPulse) (hne : ∃ t : ℝ, h t ≠ 0)
    (a b n : ℕ) {q : ℕ} (hq : 0 < q) :
    (momentHankelMatrix (fun k => radiationReading h (a+q*k) b) n).PosDef := by
  have he (k : ℕ) : radiationReading h (a+q*k) b = ∑' i, mass h a b i*(radiationNode i^q)^k := by
    rw [radiationReading,radiationSample_signed_difference]
    exact tsum_congr fun i => by simp only [mass,pow_add,pow_mul]; ring
  simp_rw [he]
  exact weighted_hankel h hne a b n _ (power_nodes radiationNode_injective
    (fun i => (radiationNode_pos i).le) hq) (fun i => pow_nonneg (radiationNode_pos i).le _)
    (fun i => pow_le_one₀ (radiationNode_pos i).le (radiationNode_le_one i))

/-- The difference-order coordinate itself has strictly positive Hankel matrices
on every arithmetic grid, including at positive starting orders. -/
theorem radiationReading_order_hankel_posDef (h : CompactPulse) (hne : ∃ t : ℝ, h t ≠ 0)
    (a b n : ℕ) {q : ℕ} (hq : 0 < q) :
    (momentHankelMatrix (fun k => radiationReading h a (b+q*k)) n).PosDef := by
  let x (i : ℕ) := 1-radiationNode i
  have hx : Function.Injective x := fun i j he => radiationNode_injective (sub_right_inj.mp he)
  have hlo (i : ℕ) : 0 ≤ x i := sub_nonneg.mpr (radiationNode_le_one i)
  have hhi (i : ℕ) : x i ≤ 1 := sub_le_self _ (radiationNode_pos i).le
  have he (k : ℕ) : radiationReading h a (b+q*k) = ∑' i, mass h a b i*(x i^q)^k := by
    rw [radiationReading,radiationSample_signed_difference]
    exact tsum_congr fun i => by simp only [x,mass,pow_add,pow_mul]; ring
  simp_rw [he]
  exact weighted_hankel h hne a b n _ (power_nodes hx hlo hq)
    (fun i => pow_nonneg (hlo i) _) (fun i => pow_le_one₀ (hlo i) (hhi i))

private theorem shifts_independent {s : ℕ → ℝ} {n : ℕ}
    (h : (momentHankelMatrix s n).PosDef) (v : Fin n → ℝ) :
    (∀ i : Fin n, ∑ j : Fin n, s (i.val+j.val)*v j = 0) ↔ v = 0 := by
  constructor
  · intro H
    by_contra hv
    have Hz : (momentHankelMatrix s n).mulVec v = 0 := funext H
    simpa only [Hz,dotProduct_zero,lt_self_iff_false] using h.dotProduct_mulVec_pos hv
  · rintro rfl i
    simp

/-- No nontrivial finite constant-coefficient recurrence can hold even on as many
successive shifted rows as coefficients, on either arithmetic grid. -/
theorem radiationReading_no_recurrence (h : CompactPulse) (hne : ∃ t : ℝ, h t ≠ 0)
    (a b n : ℕ) {q : ℕ} (hq : 0 < q) (v : Fin n → ℝ) :
    ((∀ i : Fin n, ∑ j : Fin n, radiationReading h (a+q*(i.val+j.val)) b*v j = 0) ↔ v = 0) ∧
    ((∀ i : Fin n, ∑ j : Fin n, radiationReading h a (b+q*(i.val+j.val))*v j = 0) ↔ v = 0) :=
  ⟨shifts_independent (radiationReading_sample_hankel_posDef h hne a b n hq) v,
   shifts_independent (radiationReading_order_hankel_posDef h hne a b n hq) v⟩

#print axioms exists_late_positive_release
#print axioms radiationReading_sample_hankel_posDef
#print axioms radiationReading_order_hankel_posDef
#print axioms radiationReading_no_recurrence

end

end GaloisForLFunctions.BlackHoleRingdown
