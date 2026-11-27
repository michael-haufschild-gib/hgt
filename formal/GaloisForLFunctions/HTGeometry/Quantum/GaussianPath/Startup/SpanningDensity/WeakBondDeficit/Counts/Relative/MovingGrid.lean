import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.Relative.GaussianRows
import Mathlib.Analysis.PSeries
import Mathlib.Probability.BorelCantelli

/-! # Relative bond counts on simultaneous moving grids -/
open Set Finset MeasureTheory Filter Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BlockDilations.AdaptiveCuts
noncomputable section

/-- On a grid of j radii and arbitrary deterministic prefix lengths, all
counts with mean at least 16 log j stay within a factor four of the mean.
On dyadic size grids this is a doubly logarithmic rank threshold. -/
theorem gaussian_relative_box_grid (s d : ℕ) (hd : 0<d) (m : ℕ→ℕ) (h : ∀ j, Fin j→ℝ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop, ∀ i : Fin j,
      let M := bondLaw.real (weakBond (h j i))*(m j:ℝ)
      16*log j≤M → M/4<(boxCount ω s d (m j) (h j i):ℝ) ∧ (boxCount ω s d (m j) (h j i):ℝ)<4*M := by
  classical
  let M (j : ℕ) (i : Fin j) := bondLaw.real (weakBond (h j i))*(m j:ℝ)
  let A (j : ℕ) (i : Fin j) := {ω | 16*log j≤M j i ∧
    ((boxCount ω s d (m j) (h j i):ℝ)≤M j i/4 ∨ 4*M j i≤(boxCount ω s d (m j) (h j i):ℝ))}
  let E (j : ℕ) := ⋃ i : Fin j, A j i
  let μ := pathPauliDisorderLaw
  letI : IsProbabilityMeasure μ := by dsimp only [μ,pathPauliDisorderLaw]; infer_instance
  have htail (j : ℕ) (hj : 0<j) (i : Fin j) : μ.real (A j i)≤2/(j:ℝ)^4 := by
    have hJ : (0:ℝ)<j := Nat.cast_pos.mpr hj
    by_cases hb : 16*log j≤M j i
    · have ht := relative_box_tail s d (m j) hd (h j i)
      have hsub := measureReal_mono (μ:=μ)
        (s₂:={ω | (boxCount ω s d (m j) (h j i):ℝ)≤M j i/4 ∨ 4*M j i≤(boxCount ω s d (m j) (h j i):ℝ)})
        (fun ω (hw : ω∈A j i) => hw.2) (measure_ne_top _ _)
      apply (hsub.trans ht).trans
      change 2*exp (-(M j i)/4)≤_
      have hpow : exp (4*log (j:ℝ))=(j:ℝ)^4 := calc
        _ = exp (log ((j:ℝ)^4)) := by simp only [Real.log_pow,Nat.cast_ofNat]
        _ = _ := Real.exp_log (pow_pos hJ 4)
      rw [show 2/(j:ℝ)^4=2*exp (-(4*log (j:ℝ))) by rw [exp_neg,hpow,div_eq_mul_inv]]
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) zero_le_two
      linarith only [hb]
    · have hempty : A j i=∅ := Set.eq_empty_iff_forall_notMem.mpr fun _ hw => hb hw.1
      rw [hempty,measureReal_empty]
      positivity
  have hsum : Summable fun j => μ.real (E j) := by
    apply ((Real.summable_one_div_nat_pow.mpr (by decide : 1<3)).mul_left 2).of_norm_bounded_eventually_nat
    filter_upwards [eventually_gt_atTop (0:ℕ)] with j hj
    rw [Real.norm_of_nonneg measureReal_nonneg]
    apply (measureReal_iUnion_fintype_le _).trans ((sum_le_sum fun i _ => htail j hj i).trans_eq _)
    rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [show (j:ℝ)≠0 from (Nat.cast_pos.mpr hj).ne']
  have hrare : ∀ᵐ ω ∂μ, ∀ᶠ j : ℕ in atTop, ω∉E j := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top _ _)] using hsum.tsum_ofReal_ne_top
  filter_upwards [hrare] with ω hw
  filter_upwards [hw] with j hj
  intro i v hbig
  have hh : ω∉A j i := fun hx => hj (mem_iUnion.mpr ⟨i,hx⟩)
  exact ⟨lt_of_not_ge (fun hle => hh ⟨hbig,Or.inl hle⟩),lt_of_not_ge (fun hle => hh ⟨hbig,Or.inr hle⟩)⟩

#print axioms gaussian_relative_box_grid
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
