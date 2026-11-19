import GaloisForLFunctions.ArithmeticPositiveDuality.OneSidedHigherDifferencesOnTheIntegerLine
import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.RegularityAndReceiverEquivalence
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Sign changes of every higher receiver difference

Tail energy decreases strictly somewhere on every full arithmetic sampling
grid. Its second and all higher differences take both signs on each grid,
regardless of phase or mesh. The same obstruction holds for derivatives on
the whole time axis.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff
open GaloisForLFunctions.ArithmeticPositiveDuality
namespace GaloisForLFunctions.BlackHoleRingdown

private theorem reflected_iterated_deriv (h : CompactPulse) (n : ℕ) :
    iteratedDeriv n (pulseReflected h) = pulseReflected (CompactPulse.iterD n h) := by
  induction n with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun t => (hasDerivAt_pulseReflected _ t).deriv

/-- Smoothness of the full receiver tail, including the incident wavefront. -/
theorem smooth_receiver_tail (h : CompactPulse) : ContDiff ℝ ∞ (tailEnergy h) := by
  have hs : ContDiff ℝ ∞ (pulseReflected h) := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro n _
    rw [reflected_iterated_deriv]
    exact fun t => (hasDerivAt_pulseReflected _ t).differentiableAt
  refine contDiff_infty_iff_deriv.mpr ⟨fun t => (hasDerivAt_tailEnergy h t).differentiableAt,?_⟩
  rw [show deriv (tailEnergy h)=(fun t => -(‖pulseReflected h t‖^2)) from
    funext fun t => (hasDerivAt_tailEnergy h t).deriv]
  exact hs.norm_sq.neg

/-- At every nonzero order above the first, both signs occur on *each*
bi-infinite sampling lattice for every nonzero compact input. -/
theorem receiver_lattice_higher_difference_signs (h : CompactPulse) (hne : ∃ t : ℝ, h t ≠ 0)
    (n : ℕ) (a : ℝ) {s : ℝ} (hs : 0 < s) :
    (∃ z : ℤ, (fwdDiff s)^[n+2] (tailEnergy h) (a+z*s) < 0) ∧
      ∃ z : ℤ, 0 < (fwdDiff s)^[n+2] (tailEnergy h) (a+z*s) := by
  let f := fun z : ℤ => tailEnergy h (a+z*s)
  have hb (z : ℤ) : |f z| ≤ ∫ u : ℝ, ‖h u‖^2 := by
    rw [abs_of_nonneg (tailEnergy_nonneg h _)]
    exact tailEnergy_le_initial h _
  have hn : ¬ ∀ z, f z=f 0 := by
    intro hc
    have ht : Tendsto (fun k : ℕ => a+(k:ℝ)*s) atTop atTop :=
      tendsto_atTop_add_const_left _ a (tendsto_natCast_atTop_atTop.atTop_mul_const hs)
    have hl := ((tendsto_tailEnergy_atTop h).comp ht).eventually
      (gt_mem_nhds (tailEnergy_pos h hne a))
    obtain ⟨k,hk⟩ := hl.exists
    have he := hc (k:ℤ)
    simp only [f,Int.cast_natCast,Int.cast_zero,zero_mul,add_zero] at he
    exact hk.ne he
  have he (z : ℤ) := sample_higher_difference (n+2) (tailEnergy h) a s z
  constructor
  · by_contra! hh
    exact hn (bounded_int_higher_difference_rigidity n f ⟨_,hb⟩ fun z => (he z).symm ▸ hh z)
  · by_contra! hh
    have hf : ∀ z, |((-1:ℝ) • f) z| ≤ ∫ u : ℝ, ‖h u‖^2 := by simpa using hb
    have hc := bounded_int_higher_difference_rigidity n ((-1:ℝ) • f) ⟨_,hf⟩ (fun z => by
      rw [fwdDiff_iter_const_smul]
      simpa only [Pi.smul_apply,smul_eq_mul,neg_one_mul,neg_nonneg] using
        (show (fwdDiff 1)^[n+2] f z ≤ 0 from (he z).symm ▸ hh z))
    exact hn fun z => by simpa using hc z

/-- Each higher time derivative of the actual tail has a strict positive
and a strict negative reading. No spectral or rate hypothesis enters. -/
theorem receiver_higher_derivative_signs (h : CompactPulse) (hne : ∃ t : ℝ, h t ≠ 0) (n : ℕ) :
    (∃ t, iteratedDeriv (n+2) (tailEnergy h) t < 0) ∧
      ∃ t, 0 < iteratedDeriv (n+2) (tailEnergy h) t := by
  obtain ⟨⟨z,hz⟩,⟨w,hw⟩⟩ := receiver_lattice_higher_difference_signs h hne n 0 zero_lt_one
  constructor
  · by_contra! hh
    exact hz.not_ge (higher_difference_nonneg_of_derivative _ zero_le_one _ (smooth_receiver_tail h) hh _)
  · by_contra! hh
    have hd (t : ℝ) : 0 ≤ iteratedDeriv (n+2) (-(tailEnergy h)) t := by
      rw [iteratedDeriv_neg,neg_nonneg]
      exact hh t
    have hp := higher_difference_nonneg_of_derivative _ zero_le_one _ (smooth_receiver_tail h).neg hd
      (0+(w:ℝ)*1)
    rw [show -(tailEnergy h)=(-1:ℝ) • tailEnergy h by simp,fwdDiff_iter_const_smul] at hp
    exact hw.not_ge (by simpa only [Pi.smul_apply,smul_eq_mul,neg_one_mul,neg_nonneg] using hp)

#print axioms receiver_lattice_higher_difference_signs
#print axioms receiver_higher_derivative_signs

end GaloisForLFunctions.BlackHoleRingdown
