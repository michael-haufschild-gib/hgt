import GaloisForLFunctions.ArithmeticPositiveDuality.OneSidedHigherDifferencesOnTheIntegerLine
import GaloisForLFunctions.ArithmeticPositiveDuality.AOneDimensionalIndefinitePolyharmonicLaw
import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.NoDifferentialEquationAnnihilatesALateReceiver
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

/-- Smoothness of the full receiver tail, including the incident wavefront. -/
theorem smooth_receiver_tail (h : CompactPulse) : ContDiff ℝ ∞ (tailEnergy h) := by
  have hs : ContDiff ℝ ∞ (pulseReflected h) := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro n _
    rw [receiver_iterated_deriv]
    exact fun t => (hasDerivAt_pulseReflected _ t).differentiableAt
  refine contDiff_infty_iff_deriv.mpr ⟨fun t => (hasDerivAt_tailEnergy h t).differentiableAt,?_⟩
  rw [show deriv (tailEnergy h)=(fun t => -(‖pulseReflected h t‖^2)) from
    funext fun t => (hasDerivAt_tailEnergy h t).deriv]
  exact (hs.norm_sq ℂ).neg

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
    change 0 ≤ (fwdDiff (1:ℝ))^[n+2] (-(tailEnergy h)) (0+(w:ℝ)*1) at hp
    rw [show -(tailEnergy h)=(-1:ℝ) • tailEnergy h by simp,fwdDiff_iter_const_smul] at hp
    exact hw.not_ge (by simpa only [Pi.smul_apply,smul_eq_mul,neg_one_mul,neg_nonneg] using hp)

#print axioms receiver_lattice_higher_difference_signs
#print axioms receiver_higher_derivative_signs

/-- From third order onward no single threshold separates the derivative
signs in either orientation. This holds for every phase of the input pulse. -/
theorem receiver_derivative_straddles_every_affine_cut (h : CompactPulse)
    (hh : ∃ x : ℝ, h x≠0) (n : ℕ) (c : ℝ) :
    (∃ x, (x-c)*iteratedDeriv (n+3) (tailEnergy h) x<0) ∧
      ∃ x, 0<(x-c)*iteratedDeriv (n+3) (tailEnergy h) x := by
  have hb : ∃ M : ℝ, ∀ x, |tailEnergy h x|≤M := ⟨_,fun x => by
    rw [abs_of_nonneg (tailEnergy_nonneg h x)]
    exact tailEnergy_le_initial h x⟩
  have hn : ¬∀ x, tailEnergy h x=tailEnergy h 0 := by
    intro hc
    have hl := tendsto_tailEnergy_atTop h
    rw [show tailEnergy h=(fun _ : ℝ => tailEnergy h 0) from funext hc] at hl
    exact (tailEnergy_pos h hh 0).ne' (tendsto_nhds_unique tendsto_const_nhds hl)
  have hf := contDiff_infty.mp (smooth_receiver_tail h) (n+3)
  constructor
  · by_contra! he
    exact hn (bounded_profile_single_crossing n c hf hb he)
  · by_contra! he
    have hneg : ∀ x, 0≤(x-c)*iteratedDeriv (n+3) (-(tailEnergy h)) x := by
      intro x
      rw [iteratedDeriv_neg,mul_neg,neg_nonneg]
      exact he x
    have hc := bounded_profile_single_crossing n c hf.neg
      (by simpa only [Pi.neg_apply,abs_neg] using hb) hneg
    exact hn fun x => neg_injective (hc x)

#print axioms receiver_derivative_straddles_every_affine_cut

/-- The m-th time derivative of the receiver tail has at least m ordered
strict readings of alternating sign, beginning with a negative reading.
This supplies m−1 disjoint intervals containing distinct zeros. -/
theorem ordered_receiver_tail_derivatives (h : CompactPulse) (hh : ∃ x : ℝ, h x≠0) (n : ℕ) :
    ∃ t : ℕ → ℝ, (∀ j<n, t j<t (j+1)) ∧
      ∀ j≤n, 0<(-1:ℝ)^(j+1)*iteratedDeriv (n+1) (tailEnergy h) (t j) := by
  obtain ⟨x,hx,hpos⟩ := (((tendsto_tailEnergy_atTop h).eventually_lt_const (tailEnergy_pos h hh 0)).and
    (eventually_gt_atTop (0:ℝ))).exists
  have hb : ∃ M : ℝ, ∀ y, |(-(tailEnergy h)) y|≤M := ⟨_,fun y => by
    rw [Pi.neg_apply,abs_neg,abs_of_nonneg (tailEnergy_nonneg h y)]
    exact tailEnergy_le_initial h y⟩
  obtain ⟨t,ht,hs⟩ := ordered_derivative_signs_of_rising_secant (f:=-(tailEnergy h))
    hpos (neg_lt_neg hx) hb n (contDiff_infty.mp (smooth_receiver_tail h).neg (n+1))
  refine ⟨t,ht,fun j hj => ?_⟩
  simpa only [pow_succ,iteratedDeriv_neg,mul_neg_one,neg_mul,mul_neg,mul_one] using hs j hj

#print axioms ordered_receiver_tail_derivatives

end GaloisForLFunctions.BlackHoleRingdown
