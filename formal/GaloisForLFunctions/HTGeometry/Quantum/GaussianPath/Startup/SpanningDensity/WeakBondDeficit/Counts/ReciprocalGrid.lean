import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.BoxTails
import Mathlib.Analysis.PSeries

/-! # Almost-sure box counts simultaneously at moving reciprocal radii -/

open Set Finset MeasureTheory Filter Real
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BlockDilations.AdaptiveCuts
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

private def cbox : ℝ := (2*gaussianDensityFloor)^9
private theorem cbox_pos : 0<cbox := pow_pos (mul_pos two_pos gaussianDensityFloor_pos) _

/-- The twentieth-power cutoff leaves enough samples to pay for every
test radius at every prefix. Only integral powers enter this estimate. -/
private theorem grid_risk {m j : ℕ} (hj : 0<j) (hjm : j^20 ≤ m) :
    let h := 1/(j:ℝ)
    let p := bondLaw.real (weakBond h)
    exp (-2*(p/2)^2*m) ≤ ((40:ℕ).factorial:ℝ)/(cbox^2/2)^40/(m:ℝ)^4 := by
  intro h p
  have hJ : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have hM : (0:ℝ) < m := Nat.cast_pos.mpr ((pow_pos hj 20).trans_le hjm)
  have h₁ : h≤1 := (div_le_one hJ).mpr (by exact_mod_cast hj)
  have hp := (box_probability (by dsimp only [h]; positivity) h₁).1
  change cbox*h^9≤p at hp
  let d := cbox^2/2
  have hd : 0<d := half_pos (sq_pos_of_pos cbox_pos)
  let x := d*(m:ℝ)/(j:ℝ)^18
  have hx : 0<x := div_pos (mul_pos hd hM) (pow_pos hJ _)
  have hbase : x≤2*(p/2)^2*m := by
    have hp' := pow_le_pow_left₀ (mul_nonneg cbox_pos.le (pow_nonneg (by positivity : 0≤h) 9)) hp 2
    have he : x=((cbox*h^9)^2/2)*m := by dsimp only [x,d,h]; field_simp
    rw [he]
    apply mul_le_mul_of_nonneg_right _ hM.le
    linarith only [hp']
  have hJM : (j:ℝ)^20 ≤ m := by exact_mod_cast hjm
  have hpow : d^40*(m:ℝ)^4≤x^40 := by
    dsimp only [x]
    rw [div_pow (d*(m:ℝ)) ((j:ℝ)^18) 40,mul_pow d (m:ℝ) 40,
      le_div_iff₀ (pow_pos (pow_pos hJ _) _)]
    have hjump : ((j:ℝ)^18)^40≤(m:ℝ)^36 := calc
      _ = ((j:ℝ)^20)^36 := by ring
      _ ≤ _ := pow_le_pow_left₀ (pow_nonneg hJ.le 20) hJM 36
    calc _ ≤ (d^40*(m:ℝ)^4)*(m:ℝ)^36 :=
            mul_le_mul_of_nonneg_left hjump (by positivity)
         _ = _ := by ring
  have hfact : (0:ℝ)<(40:ℕ).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hexp := (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp x hx.le 40)
  apply (exp_le_exp.mpr (by linarith only [hbase] : -2*(p/2)^2*m≤ -x)).trans
  rw [exp_neg,div_div,inv_eq_one_div,div_le_div_iff₀ (exp_pos x) (mul_pos (pow_pos hd _) (pow_pos hM _))]
  simpa only [one_mul,mul_comm (exp x)] using hpow.trans hexp

private def bad (s d m : ℕ) : Set PathPauliDisorder := ⋃ i : Fin m,
  let j := i.val+1
  let p := bondLaw.real (weakBond (1/(j:ℝ)))
  if j^20 ≤ m then {ω | (boxCount ω s d m (1/(j:ℝ)):ℝ)≤p*m/2 ∨
    (3:ℝ)/2*p*m≤boxCount ω s d m (1/(j:ℝ))} else ∅

/-- For each arithmetic progression, relative error at most one half
holds almost surely at all large sample sizes and all reciprocal radii
1/j with j²⁰ ≤ m. -/
theorem gaussian_reciprocal_counts (s d : ℕ) (hd : 0<d) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m : ℕ in atTop, ∀ j : ℕ, 0<j → j^20 ≤ m →
      let p := bondLaw.real (weakBond (1/(j:ℝ)))
      p*m/2<(boxCount ω s d m (1/(j:ℝ)):ℝ) ∧ (boxCount ω s d m (1/(j:ℝ)):ℝ)<3/2*p*m := by
  let B := 2*((40:ℕ).factorial:ℝ)/(cbox^2/2)^40
  have hB : 0≤B := by dsimp only [B]; positivity
  have hr (m : ℕ) (hm : 0 < m) : pathPauliDisorderLaw.real (bad s d m)≤B/(m:ℝ)^3 := by
    letI : NeZero m := ⟨hm.ne'⟩
    have hM : (0:ℝ) < m := Nat.cast_pos.mpr hm
    unfold bad
    apply (measureReal_iUnion_fintype_le _).trans
    calc
      _ ≤ ∑ _i : Fin m, B/(m:ℝ)^4 := by
        apply sum_le_sum
        intro i _
        dsimp only
        split_ifs with h
        · have ht := physical_box_count_tails (m:=m) s d hd (1/((i.val+1:ℕ):ℝ))
          exact (ht.trans (mul_le_mul_of_nonneg_left (grid_risk (Nat.succ_pos _) h) zero_le_two)).trans_eq (by dsimp only [B]; ring)
        · rw [measureReal_empty]; positivity
      _ = B/(m:ℝ)^3 := by
        rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        field_simp
  have hs : Summable fun m => pathPauliDisorderLaw.real (bad s d m) := by
    apply ((Real.summable_one_div_nat_pow.mpr (by decide : 1<3)).mul_left B).of_norm_bounded_eventually_nat
    filter_upwards [eventually_gt_atTop 0] with m hm
    simpa only [Real.norm_of_nonneg measureReal_nonneg,mul_one_div] using hr m hm
  have he : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ m in atTop, ω∉bad s d m := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top _ _)] using hs.tsum_ofReal_ne_top
  filter_upwards [he] with ω hw
  filter_upwards [hw] with m hm
  rintro (_|j) hj hpow
  · omega
  have hjm : j < m := (Nat.le_pow (by decide : 0<20)).trans hpow
  let i : Fin m := ⟨j,hjm⟩
  have hh : ω∉(let p := bondLaw.real (weakBond (1/((j+1:ℕ):ℝ)))
        {z | (boxCount z s d m (1/((j+1:ℕ):ℝ)):ℝ)≤p*m/2 ∨
          (3:ℝ)/2*p*m≤boxCount z s d m (1/((j+1:ℕ):ℝ))}) := by
    intro hz
    apply hm
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    simpa only [i,if_pos hpow] using hz
  exact ⟨lt_of_not_ge (fun h => hh (Or.inl h)),lt_of_not_ge (fun h => hh (Or.inr h))⟩

#print axioms gaussian_reciprocal_counts
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
