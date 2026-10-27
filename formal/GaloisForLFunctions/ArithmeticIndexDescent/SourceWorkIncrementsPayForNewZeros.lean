import GaloisForLFunctions.ArithmeticIndexDescent.DampingIncrementPositivity
import GaloisForLFunctions.ArithmeticIndexDescent.TheArithmeticSourcePaysTheIndex
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros

/-!
# New off-line zeros are paid by increments of arithmetic source work

The unconditional zero-free height gap makes every reflected pair-work monotone
in the damping scale. Four ordered pairs attached to each right-hand zero copy
then give an exact lower bound on the increment of the full arithmetic source
work. A doubled height annulus receives a uniform quantum, with multiplicities
and all exterior interactions retained.
-/

noncomputable section

open Filter Finset Set RHTower
open scoped Topology
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.ArithmeticCorrespondencePositivity

namespace GaloisForLFunctions.ArithmeticIndexDescent

theorem four_le_abs_xiZeroHeight (p : XiZeroCopy) : 4 ≤ |xiZeroHeight p| := by
  have h := (xiDivisorZetaCarrierEquiv p.1).property
  exact four_le_abs_im_of_zeta_zero h.2.1 h.2.2 h.1

/-- Pairwise monotonicity retains the reflected mixed term. -/
theorem xiDampedPairWork_monotoneOn (p q : XiZeroCopy) :
    MonotoneOn (fun R => xiDampedPairWork R p q) (Ici 0) :=
  reflectedWork_monotoneOn_scale _ _ _ _ (xiSignedDepth_pair_bound p q)
    (four_le_abs_xiZeroHeight p) (four_le_abs_xiZeroHeight q)

/-- The completed arithmetic source work increases with scale. -/
theorem xiDampedSourceWork_monotoneOn : MonotoneOn xiDampedSourceWork (Ici 4) := by
  intro R hR S hS hRS
  apply div_le_div_of_nonneg_right ?_ (by norm_num : (0 : ℝ) ≤ 4)
  exact Summable.tsum_le_tsum (fun pq => xiDampedPairWork_monotoneOn pq.1 pq.2
    (show 0 ≤ R by linarith only [hR]) (show 0 ≤ S by linarith only [hS]) hRS)
    (xiDampedPairWork_summable hR) (xiDampedPairWork_summable hS)

/-- Analytic-multiplicity copies strictly right of the critical line. -/
abbrev RightXiZeroCopy := {p : XiZeroCopy // 0 < xiSignedDepth p}

/-- The two vertices of a critical-line reflection pair. -/
def rightCopyVertex (p : RightXiZeroCopy) (b : Bool) : XiZeroCopy :=
  if b then xiZeroCopyLineConjEquiv p.1 else p.1

theorem rightCopyVertex_injective :
    Function.Injective (fun pb : RightXiZeroCopy × Bool => rightCopyVertex pb.1 pb.2) := by
  rintro ⟨p, b⟩ ⟨q, c⟩ h
  cases b <;> cases c
  · exact Prod.ext (Subtype.ext h) rfl
  · have hd := congrArg xiSignedDepth h
    simp only [rightCopyVertex, Bool.false_eq_true, if_false, if_true,
      xiSignedDepth_lineConj] at hd
    linarith only [p.2, q.2, hd]
  · have hd := congrArg xiSignedDepth h
    simp only [rightCopyVertex, Bool.false_eq_true, if_false, if_true,
      xiSignedDepth_lineConj] at hd
    linarith only [p.2, q.2, hd]
  · exact Prod.ext (Subtype.ext (xiZeroCopyLineConjEquiv.injective h)) rfl

private def rightCopyQuartet (pbc : RightXiZeroCopy × (Bool × Bool)) :
    XiZeroCopy × XiZeroCopy :=
  (rightCopyVertex pbc.1 pbc.2.1, rightCopyVertex pbc.1 pbc.2.2)

private theorem rightCopyQuartet_injective : Function.Injective rightCopyQuartet := by
  rintro ⟨p, b, c⟩ ⟨q, d, e⟩ h
  have h1 := rightCopyVertex_injective (a₁ := (p, b)) (a₂ := (q, d))
    (show rightCopyVertex p b = rightCopyVertex q d from
    congrArg Prod.fst h)
  have h2 := rightCopyVertex_injective (a₁ := (p, c)) (a₂ := (q, e))
    (show rightCopyVertex p c = rightCopyVertex q e from
    congrArg Prod.snd h)
  exact Prod.ext (congrArg Prod.fst h1)
    (Prod.ext (congrArg Prod.snd h1) (congrArg Prod.snd h2))

/-- Every ordered pair in one off-line reflection quartet has exactly one damping weight. -/
theorem xiDampedPairWork_rightCopyVertex (R : ℝ) (p : RightXiZeroCopy) (b c : Bool) :
    xiDampedPairWork R (rightCopyVertex p b) (rightCopyVertex p c) =
      heightDamping R (xiZeroHeight p.1) := by
  have hp : xiSignedDepth p.1 ≠ 0 := ne_of_gt p.2
  have hp2 : 2 * xiSignedDepth p.1 ≠ 0 := mul_ne_zero (by norm_num) hp
  cases b <;> cases c <;>
    simp only [rightCopyVertex, Bool.false_eq_true, if_false, if_true, xiDampedPairWork,
      xiSignedDepth_lineConj, xiZeroHeight_lineConj, sub_self, reflectedWork,
      reflectedEnergy, reflectedCross, transverseAngular] <;>
    (try ring_nf) <;> field_simp [hp] <;> ring

/-- The entire reflection quartet, including both diagonal pairs, pays a unit damping increment. -/
theorem sum_damping_increment_le_sourceWork_increment (s : Finset RightXiZeroCopy)
    {R S : ℝ} (hR : 4 ≤ R) (hRS : R ≤ S) :
    (∑ p ∈ s, (heightDamping S (xiZeroHeight p.1) - heightDamping R (xiZeroHeight p.1))) ≤
      xiDampedSourceWork S - xiDampedSourceWork R := by
  classical
  have hS : 4 ≤ S := hR.trans hRS
  let F : XiZeroCopy × XiZeroCopy → ℝ := fun pq =>
    xiDampedPairWork S pq.1 pq.2 - xiDampedPairWork R pq.1 pq.2
  have hF : Summable F := (xiDampedPairWork_summable hS).sub (xiDampedPairWork_summable hR)
  have hF0 (pq : XiZeroCopy × XiZeroCopy) : 0 ≤ F pq :=
    sub_nonneg.mpr (xiDampedPairWork_monotoneOn pq.1 pq.2
      (show 0 ≤ R by linarith only [hR]) (show 0 ≤ S by linarith only [hS]) hRS)
  have hle := hF.sum_le_tsum ((s ×ˢ (univ : Finset (Bool × Bool))).image rightCopyQuartet)
    (fun pq _ => hF0 pq)
  rw [Finset.sum_image rightCopyQuartet_injective.injOn, Finset.sum_product] at hle
  have hquartet (p : RightXiZeroCopy) :
      (∑ bc : Bool × Bool, F (rightCopyQuartet (p, bc))) =
        4 * (heightDamping S (xiZeroHeight p.1) - heightDamping R (xiZeroHeight p.1)) := by
    simp [F, rightCopyQuartet, xiDampedPairWork_rightCopyVertex, nsmul_eq_mul, mul_comm]
  simp_rw [hquartet] at hle
  rw [← Finset.mul_sum] at hle
  have htotal : (∑' pq, F pq) = 4 * (xiDampedSourceWork S - xiDampedSourceWork R) := by
    rw [(xiDampedPairWork_summable hS).tsum_sub (xiDampedPairWork_summable hR)]
    unfold xiDampedSourceWork
    ring
  rw [htotal] at hle
  linarith only [hle]

/-- Each right-hand zero copy in a doubled height annulus costs at least `21/100`
of new completed arithmetic work. No bound on total work is assumed. -/
theorem annular_zero_copies_paid_by_sourceWork_increment (s : Finset RightXiZeroCopy)
    {R : ℝ} (hR : 4 ≤ R)
    (hs : ∀ p ∈ s, R ≤ |xiZeroHeight p.1| ∧ |xiZeroHeight p.1| ≤ 2 * R) :
    (21 / 100 : ℝ) * s.card ≤ xiDampedSourceWork (2 * R) - xiDampedSourceWork R := by
  have hR0 : 0 < R := by linarith only [hR]
  calc
    (21 / 100 : ℝ) * s.card = ∑ _p ∈ s, (21 / 100 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ p ∈ s, (heightDamping (2 * R) (xiZeroHeight p.1) -
        heightDamping R (xiZeroHeight p.1)) :=
      Finset.sum_le_sum (fun p hp => heightDamping_doubling_gap hR0 (hs p hp).1 (hs p hp).2)
    _ ≤ xiDampedSourceWork (2 * R) - xiDampedSourceWork R :=
      sum_damping_increment_le_sourceWork_increment s hR (by linarith only [hR0])

/-- Removing the compact taper preserves the difference between two scales. -/
theorem xiTaperedSourceWork_increment_tendsto {R S : ℝ} (hR : 4 ≤ R) (hS : 4 ≤ S) :
    Tendsto (fun N : ℕ => xiTaperedSourceWork S N - xiTaperedSourceWork R N) atTop
      (𝓝 (xiDampedSourceWork S - xiDampedSourceWork R)) :=
  (xiTaperedSourceWork_tendsto hS).sub (xiTaperedSourceWork_tendsto hR)

/-- The annular payment is visible in finite work of the completed Laurent source;
the taper never removes the exterior interaction rows. -/
theorem eventually_annular_payment_in_finite_sourceWork (s : Finset RightXiZeroCopy)
    {R : ℝ} (hR : 4 ≤ R)
    (hs : ∀ p ∈ s, R ≤ |xiZeroHeight p.1| ∧ |xiZeroHeight p.1| ≤ 2 * R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (21 / 100 : ℝ) * s.card - ε <
      xiTaperedSourceWork (2 * R) N - xiTaperedSourceWork R N := by
  have h := annular_zero_copies_paid_by_sourceWork_increment s hR hs
  exact (xiTaperedSourceWork_increment_tendsto hR (by linarith only [hR])).eventually
    (lt_mem_nhds (by linarith only [h, hε]))

/-- Infinite off-line support forces fixed-size work increments at arbitrarily high scales.
Thus escape cannot hide in an everywhere vanishing scale increment. -/
theorem finite_offLineSupport_or_arbitrarily_high_quantum_increments :
    offLineSupport.Finite ∨ ∀ T : ℝ, ∃ R : ℝ, T ≤ R ∧ 4 ≤ R ∧
      (21 / 100 : ℝ) ≤ xiDampedSourceWork (2 * R) - xiDampedSourceWork R := by
  classical
  by_cases hfin : offLineSupport.Finite
  · exact Or.inl hfin
  right
  intro T
  have hM : 0 ≤ max 4 T := le_trans (by norm_num) (le_max_left 4 T)
  obtain ⟨j, hj, hjhigh⟩ : ∃ j ∈ offLineSupport, max 4 T < |(j : ℂ).im| := by
    by_contra! h
    apply hfin
    apply (finite_xiDivisorSupport_band 0 hM).subset
    intro j hj
    simpa only [Set.mem_setOf_eq, sub_zero] using h j hj
  have hR : 4 ≤ |(j : ℂ).im| := (le_max_left 4 T).trans hjhigh.le
  have hp0 : xiSignedDepth (firstZeroCopy j) ≠ 0 := by
    exact sub_ne_zero.mpr (show (j : ℂ).re ≠ 1 / 2 from hj)
  obtain ⟨p, hpheight⟩ : ∃ p : RightXiZeroCopy, xiZeroHeight p.1 = (j : ℂ).im := by
    by_cases hp : 0 < xiSignedDepth (firstZeroCopy j)
    · exact ⟨⟨firstZeroCopy j, hp⟩, rfl⟩
    · have hn : xiSignedDepth (firstZeroCopy j) < 0 := lt_of_le_of_ne (le_of_not_gt hp) hp0
      refine ⟨⟨xiZeroCopyLineConjEquiv (firstZeroCopy j), ?_⟩, ?_⟩
      · rw [xiSignedDepth_lineConj]
        exact neg_pos.mpr hn
      · exact xiZeroHeight_lineConj (firstZeroCopy j)
  refine ⟨|(j : ℂ).im|, (le_max_right 4 T).trans hjhigh.le, hR, ?_⟩
  have h := annular_zero_copies_paid_by_sourceWork_increment ({p} : Finset RightXiZeroCopy)
    hR (by
      intro q hq
      obtain rfl := Finset.mem_singleton.mp hq
      rw [hpheight]
      exact ⟨le_rfl, by linarith only [hR]⟩)
  simpa only [Finset.card_singleton, Nat.cast_one, mul_one] using h

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.xiDampedSourceWork_monotoneOn
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.sum_damping_increment_le_sourceWork_increment
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.annular_zero_copies_paid_by_sourceWork_increment
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_annular_payment_in_finite_sourceWork
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.finite_offLineSupport_or_arbitrarily_high_quantum_increments
