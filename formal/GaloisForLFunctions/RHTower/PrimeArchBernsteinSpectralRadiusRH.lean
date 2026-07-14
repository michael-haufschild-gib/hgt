import GaloisForLFunctions.RHTower.PrimeArchBernsteinExponentialPhase
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare

/-!
# Spectral-radius obstruction for the prime--Gamma Bernstein pencil

An off-critical Xi zero gives a nonreal centered reciprocal-square value. A unit-circle phase then
moves its affine Bernstein base outside the unit disk. Since the entire multiplicity-bearing Xi
family tends to the unit base off finite sets, there is a finite packet of globally maximal modes.
The packet cannot cancel: equal affine bases have the same nonzero reciprocal-square coefficient,
so exact multiplicity copies add. The finite mean-square theorem then survives the summable tail.

This is the cancellation-resistant divisor half of the subexponential Bernstein criterion for RH.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One affine mode in the Xi Bernstein pencil. -/
def xiCentralBernsteinBase (R : ℝ) (w : ℂ) (q : XiZeroCopy) : ℂ :=
  1 - xiZeroCopyReciprocalSquare q / (R : ℂ) +
    (xiZeroCopyReciprocalSquare q / (R : ℂ)) * w

/-- The Xi Bernstein bases tend to the unit mode off finite subsets of the divisor. -/
theorem tendsto_xiCentralBernsteinBase_cofinite_one (R : ℝ) (w : ℂ) :
    Tendsto (xiCentralBernsteinBase R w) cofinite (nhds 1) := by
  have hzero : Tendsto xiZeroCopyReciprocalSquare cofinite (nhds 0) :=
    summable_xiZeroCopyReciprocalSquare.tendsto_cofinite_zero
  have hdiv := hzero.div_const (R : ℂ)
  have hconst : Tendsto (fun _ : XiZeroCopy => (1 : ℂ)) cofinite (nhds 1) :=
    tendsto_const_nhds
  have h := (hconst.sub hdiv).add (hdiv.mul_const w)
  simpa only [xiCentralBernsteinBase, zero_div, zero_mul, sub_zero, add_zero] using h

/-- Away from the trivial phase, equality of affine Bernstein bases is exactly equality of their
reciprocal-square coordinates. -/
theorem xiCentralBernsteinBase_eq_iff_reciprocalSquare_eq
    {R : ℝ} (hR : R ≠ 0) {w : ℂ} (hw : w ≠ 1) (p q : XiZeroCopy) :
    xiCentralBernsteinBase R w p = xiCentralBernsteinBase R w q ↔
      xiZeroCopyReciprocalSquare p = xiZeroCopyReciprocalSquare q := by
  constructor
  · intro hbase
    have hmul :
        (xiZeroCopyReciprocalSquare p / (R : ℂ)) * (w - 1) =
          (xiZeroCopyReciprocalSquare q / (R : ℂ)) * (w - 1) := by
      calc
        (xiZeroCopyReciprocalSquare p / (R : ℂ)) * (w - 1) =
            xiCentralBernsteinBase R w p - 1 := by
              rw [xiCentralBernsteinBase]
              ring
        _ = xiCentralBernsteinBase R w q - 1 := by rw [hbase]
        _ = (xiZeroCopyReciprocalSquare q / (R : ℂ)) * (w - 1) := by
              rw [xiCentralBernsteinBase]
              ring
    have hdiv := mul_right_cancel₀ (sub_ne_zero.mpr hw) hmul
    exact (div_left_inj' (by exact_mod_cast hR)).mp hdiv
  · intro h
    simp only [xiCentralBernsteinBase, h]

/-- **Off-line exponential obstruction.** Every nonreal multiplicity-bearing Xi
reciprocal-square coordinate produces a unit phase and a radius `r > 1` for which the complete
countable Bernstein pencil, normalized by `r^n`, cannot decay to zero. This includes the infinite
tail and every exact divisor-multiplicity collision. -/
theorem exists_unit_xiCentralBernsteinPencil_exponential_obstruction
    {R : ℝ} (hR : 0 < R) {q0 : XiZeroCopy}
    (hq0 : (xiZeroCopyReciprocalSquare q0).im ≠ 0) :
    ∃ w : ℂ, ∃ r : ℝ,
      ‖w‖ = 1 ∧ 1 < r ∧
        ¬ Tendsto
          (fun n : ℕ => ∑' q : XiZeroCopy,
            xiZeroCopyReciprocalSquare q *
              (xiCentralBernsteinBase R w q / (r : ℂ)) ^ n)
          atTop (nhds 0) := by
  have huim : (xiZeroCopyReciprocalSquare q0 / (R : ℂ)).im ≠ 0 := by
    simpa [Complex.div_im] using (div_ne_zero hq0 hR.ne')
  obtain ⟨w, hw, _halign, houtside⟩ :=
    exists_unit_bernsteinBase_norm_gt_one_of_im_ne_zero huim
  have hwne : w ≠ 1 := by
    intro heq
    subst w
    norm_num at houtside
  let b : XiZeroCopy → ℂ := xiCentralBernsteinBase R w
  have houtside' : 1 < ‖b q0‖ := by
    simpa only [b, xiCentralBernsteinBase] using houtside
  obtain ⟨D, r, hr1, hDne, hdom, hsub⟩ :=
    exists_finite_maximal_norm_packet_of_tendsto_cofinite_one b
      (tendsto_xiCentralBernsteinBase_cofinite_one R w) houtside'
  have hr : 0 < r := lt_trans zero_lt_one hr1
  obtain ⟨q, hqD⟩ := hDne
  let z : XiZeroCopy → ℂ := fun i => b i / (r : ℂ)
  let u : ℂ := z q
  let F : Finset XiZeroCopy := D.filter (fun i => z i = u)
  have hqF : q ∈ F := by simp [F, u, hqD]
  have hFne : F.Nonempty := ⟨q, hqF⟩
  have hsame (i : XiZeroCopy) (hi : i ∈ F) :
      xiZeroCopyReciprocalSquare i = xiZeroCopyReciprocalSquare q := by
    have hz : z i = z q := by
      simpa only [F, Finset.mem_filter, u] using (Finset.mem_filter.mp hi).2
    have hb : b i = b q := (div_left_inj' (by exact_mod_cast hr.ne')).mp hz
    exact (xiCentralBernsteinBase_eq_iff_reciprocalSquare_eq hR.ne' hwne i q).mp hb
  have hqne : xiZeroCopyReciprocalSquare q ≠ 0 := by
    rw [xiZeroCopyReciprocalSquare_eq]
    exact xiCentralReciprocalSquare_ne_zero q.1
  have hcoeff :
      finiteExponentialFiberCoefficient D xiZeroCopyReciprocalSquare z u ≠ 0 := by
    rw [finiteExponentialFiberCoefficient]
    change (∑ i ∈ F, xiZeroCopyReciprocalSquare i) ≠ 0
    rw [Finset.sum_eq_card_nsmul hsame, nsmul_eq_mul]
    exact mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Finset.card_pos.mpr hFne))) hqne
  have hfiber : ∃ v ∈ D.image z,
      finiteExponentialFiberCoefficient D xiZeroCopyReciprocalSquare z v ≠ 0 := by
    refine ⟨u, Finset.mem_image.mpr ⟨q, hqD, rfl⟩, hcoeff⟩
  refine ⟨w, r, hw, hr1, ?_⟩
  simpa only [b, z] using
    not_tendsto_tsum_normalizedExponentialPencil_zero_of_dominantFinset
      xiZeroCopyReciprocalSquare b summable_xiZeroCopyReciprocalSquare D hr
      hdom hsub hfiber

end

end RHTower
