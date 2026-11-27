import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.Outliers.MergeBudget

/-! # Eighth-power allowance for lost component mergers -/
open Finset Filter Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit FixedHorizon RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
noncomputable section

/-- Weak bonds, exceptional coefficients and the finite packet loss
together cost less than any fixed multiple of K t⁸ from the polynomial
onset up to a positive date. The estimate retains every nonmerging call. -/
theorem eventual_eighth_merger_slack {c A D : ℝ} (hc : 0<c) (hD : 0≤D) :
    ∃ T>0, T≤1 ∧ ∀ᶠ j : ℕ in atTop, ∀ (n : ℕ) (ω : PathPauliDisorder) (t : ℝ),
      let u := pathPauliDisorderShell ω n
      let h := (1/(j:ℝ))^11
      4*(j:ℝ)^256≤((n+1:ℕ):ℝ) → (1/(j:ℝ))^12≤t → t≤T →
      ((weakEdges u h).card:ℝ)≤A*(j:ℝ)^157 →
      ((exceptionalEdges u (1/(3348*t))).card:ℝ)≤D*((n+2:ℕ):ℝ)*t^10 →
      missedBonds n (j^100) (h/1024) ω=∅ →
      ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ), ‖z‖=1 →
        ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4 →
        ((n+1:ℕ):ℝ)+(redundant (circuitWord C):ℝ)+1<(C.gateCount:ℝ)+c/2*((n+1:ℕ):ℝ)*t^8 := by
  let T := min 1 (c/(8*(D+1)))
  have hden : 0<8*(D+1) := by linarith only [hD]
  obtain ⟨J,hJ⟩ := exists_nat_gt ((A+5000)/c)
  refine ⟨T,lt_min zero_lt_one (div_pos hc hden),min_le_left ..,?_⟩
  filter_upwards [eventually_ge_atTop J,eventually_gt_atTop (0:ℕ)] with j hjJ hj
  intro n ω t u h hK hstart ht hw hbad hseam C z hz he
  let N : ℝ := (n+1:ℕ)
  let K : ℝ := (n+2:ℕ)
  let s := (1/(j:ℝ))^12
  have hjp : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have hj₁ : 1≤(j:ℝ) := by exact_mod_cast hj
  have h₀ : 0<h := pow_pos (one_div_pos.mpr hjp) _
  have hs : 0<s := pow_pos (one_div_pos.mpr hjp) _
  change s≤t at hstart
  have htp := hs.trans_le hstart
  have hfitB : 0<3348*t := mul_pos (by norm_num) htp
  have hpack : 16<((17*j^23:ℕ):ℝ)*(t*h) := by
    have heq : ((17*j^23:ℕ):ℝ)*(s*h)=17 := by
      push_cast
      dsimp only [h,s]
      field_simp [hjp.ne']
    have h' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstart h₀.le)
      (show (0:ℝ)≤(17*j^23:ℕ) from Nat.cast_nonneg _)
    linarith only [heq,h']
  have hse : 36* |t| * (h/1024)≤(t*h)/16 := by
    rw [abs_of_pos htp]
    linarith only [mul_nonneg htp.le h₀.le]
  have hp := merge_budget_with_outliers ω C htp h₀ (one_div_pos.mpr hfitB).le
    (by rw [mul_one_div,div_self hfitB.ne']) (j^100) (17*j^23) hpack hse z hz he
  dsimp only at hp
  rw [hseam,Finset.card_empty,add_zero] at hp
  have hpc := (Nat.cast_le (α:=ℝ)).mpr hp
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat] at hpc
  have hmult := mul_le_mul hK (pow_le_pow_left₀ hs.le hstart 8) (pow_nonneg hs.le 8) (Nat.cast_nonneg _)
  have hscl : 4*(j:ℝ)^256*s^8=4*(j:ℝ)^160 := by dsimp only [s]; field_simp [hjp.ne']
  change 4*(j:ℝ)^256*s^8≤N*t^8 at hmult
  rw [hscl] at hmult
  have hcoef := (div_lt_iff₀ hc).mp (hJ.trans_le (Nat.cast_le.mpr hjJ))
  have hdom : (A+5000)*(j:ℝ)^157<c*(N*t^8)/4 := calc
    _ < ((j:ℝ)*c)*(j:ℝ)^157 := mul_lt_mul_of_pos_right hcoef (pow_pos hjp _)
    _ = c*(j:ℝ)^158 := by ring
    _ ≤ c*(j:ℝ)^160 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hj₁ (by decide : 158≤160)) hc.le
    _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left hmult hc.le]
  have hT₀ := (le_div_iff₀ hden).mp (ht.trans (min_le_right ..))
  have ht₁ : t≤1 := ht.trans (min_le_left ..)
  have hdt : D*t^2≤c/8 := by
    have hx := mul_le_mul_of_nonneg_left ht₁ htp.le
    linarith only [hT₀,mul_le_mul_of_nonneg_left hx hD,htp.le]
  have hNK : K≤2*N := by
    dsimp only [K,N]
    exact_mod_cast (show n+2≤2*(n+1) by omega)
  have hde : D*K*t^10≤c*(N*t^8)/4 := by
    have h₁ := mul_le_mul_of_nonneg_right hdt (mul_nonneg (show 0≤K from Nat.cast_nonneg _) (pow_nonneg htp.le 8))
    have h₂ := mul_le_mul_of_nonneg_right hNK (mul_nonneg hc.le (pow_nonneg htp.le 8))
    linarith only [h₁,h₂]
  have hpw (p : ℕ) (hp : p≤157) := pow_le_pow_right₀ hj₁ hp
  have hu : 1≤(j:ℝ)^157 := one_le_pow₀ hj₁
  change ((exceptionalEdges u (1/(3348*t))).card:ℝ)≤D*K*t^10 at hbad
  change N+_+1<(C.gateCount:ℝ)+c/2*N*t^8
  have hNeq : (n:ℝ)+1=N := by dsimp only [N]; rw [Nat.cast_add,Nat.cast_one]
  linarith only [hpc,hw,hbad,hde,hdom,hNeq,hu,hpw 146 (by decide),hpw 46 (by decide),hpw 100 (by decide)]

#print axioms eventual_eighth_merger_slack
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
