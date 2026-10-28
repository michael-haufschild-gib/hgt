import GaloisForLFunctions.ArithmeticIndexDescent.SourceWorkIncrementsPayForNewZeros
import GaloisForLFunctions.ArithmeticIndexDescent.TheSourceWorkHasAClosedQuantumThreshold
import GaloisForLFunctions.ArithmeticIndexDescent.VanishingScaleIncrementsCharacterizeFiniteSupport

/-!
# A strict scale quantum from an entire off-line quartet

The four conjugate and critical-line-reflected copies have equal absolute height.
Their sixteen ordered pair works have no unequal-weight mixed term. Their exact
contribution is twice the damping increment times one plus the positive diagonal
angle. At the zero's own height this exceeds the closed quantum `39/50`.
All other ordered pairs have nonnegative increments and remain in the source work.
-/

noncomputable section

open Filter Finset Set RHTower
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open scoped Topology

namespace GaloisForLFunctions.ArithmeticIndexDescent

private def quartetVertex (j : XiDivisorSupport) (ab : Bool × Bool) : XiZeroCopy :=
  let p := firstZeroCopy (if ab.1 then xiSupportConj j else j)
  if ab.2 then xiZeroCopyLineConjEquiv p else p

private theorem quartetVertex_depth (j : XiDivisorSupport) (ab : Bool × Bool) :
    xiSignedDepth (quartetVertex j ab) =
      if ab.2 then -((j : ℂ).re - 1 / 2) else (j : ℂ).re - 1 / 2 := by
  rcases ab with ⟨a, b⟩
  cases a <;> cases b
  · rfl
  · change xiSignedDepth (xiZeroCopyLineConjEquiv (firstZeroCopy j)) = _
    rw [xiSignedDepth_lineConj]
    rfl
  · rfl
  · change xiSignedDepth (xiZeroCopyLineConjEquiv (firstZeroCopy (xiSupportConj j))) = _
    rw [xiSignedDepth_lineConj]
    rfl

private theorem quartetVertex_height (j : XiDivisorSupport) (ab : Bool × Bool) :
    xiZeroHeight (quartetVertex j ab) =
      if ab.1 then -(j : ℂ).im else (j : ℂ).im := by
  rcases ab with ⟨a, b⟩
  cases a <;> cases b
  · rfl
  · change xiZeroHeight (xiZeroCopyLineConjEquiv (firstZeroCopy j)) = _
    rw [xiZeroHeight_lineConj]
    rfl
  · rfl
  · change xiZeroHeight (xiZeroCopyLineConjEquiv (firstZeroCopy (xiSupportConj j))) = _
    rw [xiZeroHeight_lineConj]
    rfl

private theorem sign_choice_injective {x : ℝ} (hx : x ≠ 0) :
    Function.Injective (fun b : Bool => if b then -x else x) := by
  intro b c h
  cases b <;> cases c
  · rfl
  · simp only [Bool.false_eq_true, if_false, if_true] at h
    exact False.elim (hx (by linarith only [h]))
  · simp only [Bool.false_eq_true, if_false, if_true] at h
    exact False.elim (hx (by linarith only [h]))
  · rfl

private theorem quartetVertex_injective {j : XiDivisorSupport}
    (hj : (j : ℂ).re ≠ 1 / 2) : Function.Injective (quartetVertex j) := by
  intro ab cd h
  apply Prod.ext
  · apply sign_choice_injective (xiSupport_im_ne_zero j)
    simpa only [quartetVertex_height] using congrArg xiZeroHeight h
  · apply sign_choice_injective (sub_ne_zero.mpr hj)
    simpa only [quartetVertex_depth] using congrArg xiSignedDepth h

private theorem reflectedEnergy_sign_choices (x d : ℝ) (b c : Bool) :
    reflectedEnergy ((if b then -x else x) - (if c then -x else x))
      ((if b then -x else x) + (if c then -x else x)) d =
      transverseAngular (2 * x) d := by
  have hz : transverseAngular 0 d = 0 := by simp [transverseAngular]
  cases b <;> cases c <;>
    simp only [Bool.false_eq_true, if_false, if_true, reflectedEnergy, sub_self,
      add_neg_cancel, neg_add_cancel, hz, zero_add, add_zero] <;>
    unfold transverseAngular <;> congr 1 <;> ring

private theorem quartet_pair_work {j : XiDivisorSupport} (hj : (j : ℂ).re ≠ 1 / 2)
    (R : ℝ) (ab cd : Bool × Bool) :
    xiDampedPairWork R (quartetVertex j ab) (quartetVertex j cd) =
      heightDamping R (j : ℂ).im *
        (if ab.1 = cd.1 then 1 else reflectionDiagonalAngle j) := by
  have hdamp (b : Bool) :
      heightDamping R (if b then -(j : ℂ).im else (j : ℂ).im) =
        heightDamping R (j : ℂ).im := by
    cases b <;> simp [heightDamping]
  rw [xiDampedPairWork, quartetVertex_depth, quartetVertex_depth,
    quartetVertex_height, quartetVertex_height, hdamp, hdamp]
  have heq (x y d v : ℝ) : reflectedWork x y d v v = v * reflectedEnergy x y d := by
    unfold reflectedWork
    ring
  rw [heq, reflectedEnergy_sign_choices]
  congr 1
  have hx : 2 * ((j : ℂ).re - 1 / 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hj)
  rcases ab with ⟨a, b⟩
  rcases cd with ⟨c, d⟩
  cases a <;> cases c
  · change transverseAngular (2 * ((j : ℂ).re - 1 / 2))
      ((j : ℂ).im - (j : ℂ).im) = 1
    simp only [sub_self, transverseAngular, zero_pow (by decide : 2 ≠ 0), add_zero,
      div_self (pow_ne_zero 2 hx)]
  · change transverseAngular (2 * ((j : ℂ).re - 1 / 2))
      ((j : ℂ).im - -(j : ℂ).im) = reflectionDiagonalAngle j
    unfold transverseAngular reflectionDiagonalAngle
    congr 1 <;> ring
  · change transverseAngular (2 * ((j : ℂ).re - 1 / 2))
      (-(j : ℂ).im - (j : ℂ).im) = reflectionDiagonalAngle j
    unfold transverseAngular reflectionDiagonalAngle
    congr 1 <;> ring
  · change transverseAngular (2 * ((j : ℂ).re - 1 / 2))
      (-(j : ℂ).im - -(j : ℂ).im) = 1
    simp only [sub_self, transverseAngular, zero_pow (by decide : 2 ≠ 0), add_zero,
      div_self (pow_ne_zero 2 hx)]

private theorem quartet_sum_work {j : XiDivisorSupport} (hj : (j : ℂ).re ≠ 1 / 2)
    (R : ℝ) :
    (∑ ab : Bool × Bool, ∑ cd : Bool × Bool,
      xiDampedPairWork R (quartetVertex j ab) (quartetVertex j cd)) =
      8 * heightDamping R (j : ℂ).im * (1 + reflectionDiagonalAngle j) := by
  simp only [quartet_pair_work hj]
  simp [Fintype.sum_prod_type]
  ring

/-- All sixteen ordered interactions of one off-line quartet are paid by the full source increment. -/
theorem offLineQuartet_increment_payment {j : XiDivisorSupport}
    (hj : (j : ℂ).re ≠ 1 / 2) {R S : ℝ} (hR : 4 ≤ R) (hRS : R ≤ S) :
    2 * (heightDamping S (j : ℂ).im - heightDamping R (j : ℂ).im) *
      (1 + reflectionDiagonalAngle j) ≤
      xiDampedSourceWork S - xiDampedSourceWork R := by
  classical
  let v := quartetVertex j
  let e : ((Bool × Bool) × (Bool × Bool)) → XiZeroCopy × XiZeroCopy :=
    fun pq => (v pq.1, v pq.2)
  have he : Function.Injective e := by
    intro p q h
    exact Prod.ext (quartetVertex_injective hj (congrArg Prod.fst h))
      (quartetVertex_injective hj (congrArg Prod.snd h))
  have hS := hR.trans hRS
  let F : XiZeroCopy × XiZeroCopy → ℝ :=
    fun pq => xiDampedPairWork S pq.1 pq.2 - xiDampedPairWork R pq.1 pq.2
  have hF : Summable F := (xiDampedPairWork_summable hS).sub (xiDampedPairWork_summable hR)
  have hF0 (pq : XiZeroCopy × XiZeroCopy) : 0 ≤ F pq :=
    sub_nonneg.mpr (xiDampedPairWork_monotoneOn pq.1 pq.2
      (show 0 ≤ R by linarith only [hR]) (show 0 ≤ S by linarith only [hS]) hRS)
  have hle := hF.sum_le_tsum (univ.image e) (fun pq _ => hF0 pq)
  rw [Finset.sum_image he.injOn] at hle
  have hpacket (T : ℝ) :
      (∑ pq : (Bool × Bool) × (Bool × Bool),
        xiDampedPairWork T (e pq).1 (e pq).2) =
        8 * heightDamping T (j : ℂ).im * (1 + reflectionDiagonalAngle j) := by
    change (∑ pq : (Bool × Bool) × (Bool × Bool),
      xiDampedPairWork T (quartetVertex j pq.1) (quartetVertex j pq.2)) = _
    rw [Fintype.sum_prod_type]
    exact quartet_sum_work hj T
  change (∑ pq, (xiDampedPairWork S (e pq).1 (e pq).2 -
    xiDampedPairWork R (e pq).1 (e pq).2)) ≤ ∑' pq, F pq at hle
  rw [Finset.sum_sub_distrib, hpacket S, hpacket R] at hle
  have htotal : (∑' pq, F pq) = 4 * (xiDampedSourceWork S - xiDampedSourceWork R) := by
    rw [(xiDampedPairWork_summable hS).tsum_sub (xiDampedPairWork_summable hR)]
    unfold xiDampedSourceWork
    ring
  rw [htotal] at hle
  nlinarith only [hle]

private theorem heightDamping_own_height_gap {t : ℝ} (ht : t ≠ 0) :
    heightDamping (2 * |t|) t - heightDamping |t| t = 39 / 100 := by
  have hfour : |t| ^ 4 = t ^ 4 := by
    calc
      |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
      _ = (t ^ 2) ^ 2 := by rw [sq_abs]
      _ = t ^ 4 := by ring
  have ht2 := sq_pos_of_ne_zero ht
  have hA : t ^ 2 + t ^ 2 ≠ 0 := ne_of_gt (add_pos ht2 ht2)
  have hB : 4 * t ^ 2 + t ^ 2 ≠ 0 := by positivity
  simp only [heightDamping, mul_pow, sq_abs, hfour]
  norm_num only
  field_simp [hA, hB]
  ring

/-- An actual off-line zero forces a strict doubled-scale quantum at its own absolute height. -/
theorem offLineQuartet_strict_increment {j : XiDivisorSupport}
    (hj : (j : ℂ).re ≠ 1 / 2) :
    (39 / 50 : ℝ) < xiDampedSourceWork (2 * |(j : ℂ).im|) -
      xiDampedSourceWork |(j : ℂ).im| := by
  have hR : 4 ≤ |(j : ℂ).im| := four_le_abs_xiZeroHeight (firstZeroCopy j)
  have h := offLineQuartet_increment_payment hj hR
    (show |(j : ℂ).im| ≤ 2 * |(j : ℂ).im| by linarith only [hR])
  rw [heightDamping_own_height_gap (xiSupport_im_ne_zero j)] at h
  nlinarith only [h, reflectionDiagonalAngle_pos hj]

/-- Infinite off-line support crosses the closed quartet quantum at arbitrarily high scales. -/
theorem finite_offLineSupport_or_arbitrarily_high_strict_quantum_increments :
    offLineSupport.Finite ∨ ∀ T : ℝ, ∃ R : ℝ, T ≤ R ∧ 4 ≤ R ∧
      (39 / 50 : ℝ) < doubledSourceWorkIncrement R := by
  by_cases hfin : offLineSupport.Finite
  · exact Or.inl hfin
  right
  intro T
  have hM : 0 ≤ max 4 T := le_trans (by norm_num) (le_max_left 4 T)
  obtain ⟨j, hj, hhigh⟩ : ∃ j ∈ offLineSupport, max 4 T < |(j : ℂ).im| := by
    by_contra! h
    apply hfin
    apply (finite_xiDivisorSupport_band 0 hM).subset
    intro j hj
    simpa only [Set.mem_setOf_eq, sub_zero] using h j hj
  refine ⟨|(j : ℂ).im|, (le_max_right 4 T).trans hhigh.le,
    (le_max_left 4 T).trans hhigh.le, ?_⟩
  exact offLineQuartet_strict_increment (show (j : ℂ).re ≠ 1 / 2 from hj)

/-- Eventual control at the closed quartet quantum characterizes finite exceptions. -/
theorem eventually_closed_quantum_increment_iff :
    (∀ᶠ R : ℝ in atTop, doubledSourceWorkIncrement R ≤ 39 / 50) ↔
      offLineSupport.Finite := by
  constructor
  · intro h
    rcases finite_offLineSupport_or_arbitrarily_high_strict_quantum_increments with hfin | hhigh
    · exact hfin
    obtain ⟨T, hT⟩ := eventually_atTop.mp h
    obtain ⟨R, hR, _, hquantum⟩ := hhigh T
    exact False.elim ((not_lt_of_ge (hT R hR)) hquantum)
  · intro hfin
    exact ((doubledSourceWorkIncrement_tendsto_zero_of_finite hfin).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 39 / 50))).mono fun _ h => h.le

/-- Every-scale control at the closed local quantum excludes isolated exceptions as well. -/
theorem riemannHypothesis_iff_all_scale_increments_le_quantum :
    RiemannHypothesis ↔ ∀ R : ℝ, 4 ≤ R →
      xiDampedSourceWork (2 * R) - xiDampedSourceWork R ≤ 39 / 50 := by
  constructor
  · intro h R _
    rw [xiDampedSourceWork_eq_zero_of_riemannHypothesis h,
      xiDampedSourceWork_eq_zero_of_riemannHypothesis h]
    norm_num
  · intro h
    refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun j => ?_
    by_contra hj
    exact (not_lt_of_ge (h |(j : ℂ).im| (four_le_abs_xiZeroHeight (firstZeroCopy j))))
      (offLineQuartet_strict_increment hj)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.offLineQuartet_increment_payment
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.offLineQuartet_strict_increment
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_closed_quantum_increment_iff
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.riemannHypothesis_iff_all_scale_increments_le_quantum
