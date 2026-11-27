import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.DelayedExcursions.Increment
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.DelayedExcursions.JointMass

/-! # An all-time cap and a long interval of cheap increments on one draw -/
open Set MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open DiagonalSynthesis.CommutatorBounds
noncomputable section

/-- Gaussian price of the chosen two-block event. The positive constants
are uniform in the size, duration and imbalance of the balanced split. -/
private theorem joint_window_price {b : ℝ} (hb : b ∈ Ioc (0:ℝ) 1) :
    ∃ A > (0:ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ l r : ℕ, 2 ≤ l → l ≤ r → r ≤ l+1 → ∀ T ≥ (1:ℝ),
      let K := l+r+4
      A*exp (-C*(K:ℝ)*((Nat.clog 2 K:ℝ)+1)) ≤ T^9*(standardLaw (PathLabel (l+r+2))).real
        (joinedCaps l r (1/400) (gapScale K/20*(b/T))) := by
  obtain ⟨ρ,hρ,hjoin⟩ := joined_caps_mass
  obtain ⟨a,ha,c,hc,hchildren⟩ := hierarchical_gap_cap_mass
  let a₀ := a*(1/400:ℝ)^9
  have ha₀ : 0 < a₀ := mul_pos ha.1 (by norm_num)
  let C := 2*c-log ρ
  have hlog : log ρ ≤ 0 := log_nonpos hρ.1.le hρ.2
  refine ⟨a₀^2*b^9,mul_pos (pow_pos ha₀ _) (pow_pos hb.1 _),C,by dsimp only [C]; linarith only [hc,hlog],?_⟩
  intro l r hl hlr hr T hT K
  let d := (Nat.clog 2 K:ℝ)+1
  let e := exp (-c*(K:ℝ)*d)
  have hd : 1 ≤ d := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hT₀ := zero_lt_one.trans_le hT
  have hz : b/T ∈ Ioc (0:ℝ) 1 := ⟨div_pos hb.1 hT₀,(div_le_one hT₀).mpr (hb.2.trans hT)⟩
  have hparts (s : ℕ) (hs : 2 ≤ s) (hK : s+2 ≤ K) :
      a₀*e ≤ (standardLaw (PathLabel s)).real (separatedCap s (1/400)) := by
    apply le_trans _ (hchildren s hs (1/400) (by constructor <;> norm_num))
    apply mul_le_mul_of_nonneg_left _ ha₀.le
    apply exp_le_exp.mpr
    have hprod : ((s+2:ℕ):ℝ)*((Nat.clog 2 (s+2):ℝ)+1) ≤ (K:ℝ)*d :=
      mul_le_mul (Nat.cast_le.mpr hK) (add_le_add (Nat.cast_le.mpr (Nat.clog_mono_right 2 hK)) le_rfl)
        (by positivity) (Nat.cast_nonneg _)
    simpa only [mul_assoc] using mul_le_mul_of_nonpos_left hprod (neg_nonpos.mpr hc)
  have hL := hparts l hl (by dsimp only [K]; omega)
  have hR := hparts r (by omega) (by dsimp only [K]; omega)
  have hchildren' := mul_le_mul hL hR (mul_nonneg ha₀.le (exp_pos _).le) measureReal_nonneg
  have hexp : exp (-C*(K:ℝ)*d) ≤ ρ^K*e^2 := by
    have hrho : ρ^K=exp (log ρ*(K:ℝ)) := by rw [mul_comm,exp_nat_mul,exp_log hρ.1]
    rw [hrho,pow_two,←exp_add,←exp_add]
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonpos_left hd (mul_nonpos_of_nonpos_of_nonneg hlog (Nat.cast_nonneg K))
    dsimp only [C]
    linarith only [hh]
  have hj := hjoin l r hlr hr (1/400) (b/T) hz
  have hcost : 0 ≤ ρ^K*(b/T)^9 := mul_nonneg (pow_nonneg hρ.1.le _) (pow_nonneg hz.1.le _)
  have h₁ := (mul_le_mul_of_nonneg_left hchildren' hcost).trans (by simpa only [mul_assoc] using hj)
  have h₂ := mul_le_mul_of_nonneg_left h₁ (pow_nonneg hT₀.le 9)
  apply le_trans _ h₂
  apply (mul_le_mul_of_nonneg_left hexp (mul_nonneg (sq_nonneg a₀) (pow_nonneg hb.1.le _))).trans_eq
  rw [div_pow]
  field_simp

/-- Through T the half registers cost only O(√D) gates, while every
time on the restored register costs at most 213D at error one tenth. -/
theorem physical_block_window :
    ∃ A > (0:ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ l r : ℕ, 2 ≤ l → l ≤ r → r ≤ l+1 → ∀ T ≥ (1:ℝ),
      let n := l+r+2
      let K := n+2
      ∃ E : Set (PathLabel n→ℝ), MeasurableSet E ∧
        A*exp (-C*(K:ℝ)*((Nat.clog 2 K:ℝ)+1)) ≤ T^9*(standardLaw (PathLabel n)).real E ∧
        ∀ x ∈ E, x ∈ capEvent n (1/10) ∧ ∀ t : ℝ, |t| ≤ T →
          HasProjectiveCircuitApproximation K (1/100) (213*2^(l+2)+213*2^(r+2))
            (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t) := by
  let p := sqrt packConstant
  let b := 1/(1000*(1+p))
  have hp : 0 ≤ p := sqrt_nonneg _
  have hden : 0 < 1000*(1+p) := by linarith only [hp]
  have hb : b ∈ Ioc (0:ℝ) 1 := ⟨one_div_pos.mpr hden,(div_le_one hden).mpr (by linarith only [hp])⟩
  obtain ⟨A,hA,C,hC,hprice⟩ := joint_window_price hb
  refine ⟨A,hA,C,hC,?_⟩
  intro l r hl hlr hr T hT n K
  let g := gapScale K
  let δ := g/20*(b/T)
  have hg : 0 < g := gapScale_pos K
  have hg₁ : g ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hT₀ := zero_lt_one.trans_le hT
  have hz : b/T ≤ b := div_le_self hb.1.le hT
  have hb' : b ≤ 1/1000 := one_div_le_one_div_of_le (by norm_num) (by linarith only [hp])
  have hd₁ : δ ≤ 1/(1800*T) := by
    rw [show δ=(g*b/20)/T by dsimp only [δ]; ring,show 1/(1800*T)=(1/1800)/T by ring]
    apply div_le_div_of_nonneg_right _ hT₀.le
    have hh := mul_le_mul hg₁ hb' hb.1.le zero_le_one
    linarith only [hh]
  have hd₂ : 4*p/(2*g)*(9*δ) ≤ 1/10 := by
    have he : 4*p/(2*g)*(9*δ)=(9/10:ℝ)*p*(b/T) := by
      dsimp only [δ]
      field_simp [hg.ne',hT₀.ne']
      ring
    rw [he]
    apply (mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ (9/10:ℝ)*p)).trans
    change (9/10:ℝ)*p*(1/(1000*(1+p))) ≤ 1/10
    rw [mul_one_div,div_le_iff₀ hden]
    linarith only [hp]
  refine ⟨_,measurable_joinedCaps l r (1/400) δ,hprice l r hl hlr hr T hT,?_⟩
  intro x hx
  have hs i : |(extractBlocks l r x).2 i| ≤ δ := abs_le.mpr (hx.2 i (mem_univ _))
  have hc := final_seam_cap l r hlr hr x (mul_pos two_pos hg) hx.1.2 hd₂ hs
  refine ⟨?_,capped_increment l r x hT₀ hx.1.1 (fun i => (hs i).trans hd₁)⟩
  intro t
  let u : PathShell n := WithLp.toLp 2 x
  change PrescribedTimes.pathGateDistance n _ (fun i => u (pathCoeffEquiv n i)) t ≤ _
  rw [PrescribedTimes.pathGateDistance,PrescribedTimes.numberedGenerator_shell]
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp (hc t)

#print axioms physical_block_window
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
