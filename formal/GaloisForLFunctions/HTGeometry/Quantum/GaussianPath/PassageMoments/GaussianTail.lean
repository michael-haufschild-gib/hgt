import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.CutoffClock
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! # Removing the coupling cutoff from the upper first-passage tail -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PassageMoments
noncomputable section
open PrescribedTimes

/-- At a cutoff R≥1 and risk R⁻ᴸ, the phase deadline grows by at most
R to the power LD!+D!−1 relative to the unit cutoff and unit risk. -/
private theorem clock_growth (k L : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    let e := prefixPhaseEnergyEquiv k
    let d := (2^(k+3):ℕ).factorial
    gaussianPhaseClock e (1/80) R (R^L)⁻¹ ≤ gaussianPhaseClock e (1/80) 1 1 * R^(L*d+(d-1)) := by
  intro e d
  let S := phaseClockModes e (1/80)
  let M : ℝ := ∑ m ∈ S, ∑ i, |(m i:ℝ)|
  let c : ℝ := 8*((nonconstantPacketIndexSet (phaseCubeFourierCutoff (2^(k+3)-1) (1/80)) (2^(k+3)-1)).card+1)
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hp := zero_lt_one.trans_le hR
  change c/(((R^L)⁻¹)^d/(1+R*M)^(d-1)) ≤ c/((1:ℝ)^d/(1+1*M)^(d-1))*R^(L*d+(d-1))
  rw [div_div_eq_mul_div,div_div_eq_mul_div,one_pow,div_one,one_mul,inv_pow,div_inv_eq_mul,←pow_mul,pow_add]
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1+R*M)
    (by linarith only [hR] : 1+R*M ≤ R*(1+M)) (d-1)
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hc) (pow_nonneg hp.le _)).trans_eq
  rw [mul_pow]
  ring

private theorem coupling_tail (n L : ℕ) :
    let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
    ∃ C : ℝ, ∀ R : ℝ, 0 < R → μ.real {x | R < couplingMass x} ≤ C*(R^L)⁻¹ := by
  intro μ
  have oneCoord (i : PrefixIndex n) : MemLp (fun x : PrefixIndex n → ℝ => x i) L μ := by
    exact (IsGaussian.memLp_id (gaussianReal 0 1) (L:ℝ≥0∞) (by simp)).comp_measurePreserving
      (measurePreserving_eval (fun _ : PrefixIndex n => gaussianReal 0 1) i)
  have hm : MemLp (fun x : PrefixIndex n → ℝ => couplingMass x) L μ := by
    simpa only [couplingMass,Real.norm_eq_abs] using memLp_finsetSum Finset.univ
      (fun i _ => (oneCoord i).norm)
  have hpos (x : PrefixIndex n → ℝ) : 0 ≤ couplingMass x := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hint : Integrable (fun x => couplingMass x ^ L) μ := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos _)] using hm.integrable_norm_pow'
  refine ⟨∫ x, couplingMass x^L ∂μ,fun R hR => ?_⟩
  have he := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ fun x => pow_nonneg (hpos x) L) hint (R^L)
  rw [←div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hR L)).mpr
  rw [mul_comm]
  apply le_trans _ he
  exact mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) (fun _ hx => pow_le_pow_left₀ hR.le hx.le L))
    (pow_nonneg hR.le _)

/-- For all return budgets simultaneously the same exponent controls the
tail of the larger of the onset and the first post-crossing wait. The
constant may depend on the prefix and on the chosen moment order L. -/
theorem gaussian_dyadic_passage_tail :
    ∀ᶠ k : ℕ in atTop, ∀ L : ℕ,
      let d := (2^(k+3):ℕ).factorial
      let μ := Measure.pi (fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
      ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, ∀ s u : ℕ,
        μ.real {x | A*((2:ℝ)^(L*d+(d-1)))^u < passageMax k s x} ≤ C*((2:ℝ)^L)⁻¹^u := by
  filter_upwards [gaussian_cutoff_first_passage] with k hk
  intro L d μ
  let e := prefixPhaseEnergyEquiv k
  let S := phaseClockModes e (1/80)
  let A := gaussianPhaseClock e (1/80) 1 1
  have hA : 0 < A := by
    dsimp only [A,gaussianPhaseClock,phaseClockDetuning]
    have h : 0 ≤ ∑ m ∈ S, ∑ i, |(m i:ℝ)| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  obtain ⟨C,hC⟩ := coupling_tail (k+1) L
  let c := (S.card:ℝ)*(2*d)
  refine ⟨A,hA,C+c,fun s u => ?_⟩
  let R := (2:ℝ)^u
  let r := (R^L)⁻¹
  let G := gaussianPhaseClock e (1/80) R r
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hp := zero_lt_one.trans_le hR
  have hr : 0 < r := inv_pos.mpr (pow_pos hp L)
  have hr' : r ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hR)
  have hG : G ≤ A*((2:ℝ)^(L*d+(d-1)))^u := by
    calc
      G ≤ A*R^(L*d+(d-1)) := clock_growth k L hR
      _ = _ := by dsimp only [R]; rw [←pow_mul,←pow_mul,Nat.mul_comm u]
  let B := {x | couplingMass x ≤ R ∧ G < passageMax k s x}
  have hb := hk s R r hp.le hr hr'
  have hb' : μ.real B ≤ c*r := by
    have h := ENNReal.toReal_mono (by finiteness) hb
    change (μ B).toReal ≤ (↑S.card*ENNReal.ofReal (2*(d:ℝ)*r)).toReal at h
    rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (mul_nonneg (by positivity) hr.le)] at h
    simpa only [Measure.real,c,mul_assoc] using h
  have inc : {x | A*((2:ℝ)^(L*d+(d-1)))^u < passageMax k s x} ⊆ {x | R < couplingMass x} ∪ B := by
    intro x hx
    exact (lt_or_ge R (couplingMass x)).imp id (fun h => ⟨h,hG.trans_lt hx⟩)
  calc
    _ ≤ μ.real {x | R < couplingMass x} + μ.real B := (measureReal_mono inc).trans (measureReal_union_le _ _)
    _ ≤ C*r+c*r := add_le_add (hC R hp) hb'
    _ = _ := by rw [←add_mul]; congr 1; dsimp only [r,R]; rw [inv_pow,←pow_mul,Nat.mul_comm u,pow_mul]

#print axioms gaussian_dyadic_passage_tail
end
end GaloisForLFunctions.HTGeometry.PassageMoments
