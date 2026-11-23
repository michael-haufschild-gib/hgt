import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.OptimalError.FiniteCover
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.ThreeGateMatch

/-! # Sharp chord error of a clock at any prescribed gate budget -/
open Real Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ClockSpectrum
noncomputable section

private theorem half_bin_chord {M : ℕ} (hM : 0<M) {x y : ℝ} (h : |x-y|≤1/(2*M)) :
    ‖expTurns x-expTurns y‖≤clockRadius M := by
  let a := 2*π*x
  let b := 2*π*y
  have hp : 0<(M:ℝ) := Nat.cast_pos.mpr hM
  have hm : (1:ℝ)≤M := by exact_mod_cast hM
  have hd := circDist_le a b 0
  simp only [Int.cast_zero,mul_zero,add_zero] at hd
  have he : |a-b|=2*π*|x-y| := by dsimp only [a,b]; rw [←mul_sub,abs_mul,abs_of_pos two_pi_pos]
  rw [he] at hd
  have hangle : circDist a b/2 ≤ π/(2*M) := by
    have hh := mul_le_mul_of_nonneg_left h two_pi_pos.le
    calc _ ≤ (2*π*(1/(2*M)))/2 := by linarith only [hd,hh]
         _ = _ := by ring
  have hu : π/(2*M)≤π/2 := div_le_div_of_nonneg_left pi_pos.le (by norm_num) (by linarith only [hm])
  change ‖Complex.exp ((a:ℂ)*Complex.I)-Complex.exp ((b:ℂ)*Complex.I)‖≤_
  rw [norm_expI_sub_eq_sin_circDist]
  apply mul_le_mul_of_nonneg_left _ zero_le_two
  apply Real.strictMonoOn_sin.monotoneOn _ _ hangle
  · exact ⟨by linarith only [circDist_nonneg a b,pi_pos],hangle.trans hu⟩
  · exact ⟨(by linarith only [pi_pos] : -(π/2)≤0).trans (by positivity),hu⟩

private theorem remainder_in_bin (b M F : ℕ) (hm : 0<M) (hf : 0<F) :
    |(b:ℝ)/(M*F)-(((b/F:ℕ):ℝ)/M+1/(2*M))|≤1/(2*M) := by
  have hM : 0<(M:ℝ) := Nat.cast_pos.mpr hm
  have hF : 0<(F:ℝ) := Nat.cast_pos.mpr hf
  have he : ((b%F:ℕ):ℝ)+(F:ℝ)*((b/F:ℕ):ℝ)=b := by exact_mod_cast Nat.mod_add_div b F
  have hr : ((b%F:ℕ):ℝ)<F := by exact_mod_cast Nat.mod_lt b hf
  rw [abs_le]
  constructor <;> field_simp [hM.ne',hF.ne'] <;> linarith only [he,hr,Nat.cast_nonneg (α:=ℝ) (b%F)]

/-- At budget s the limiting chord error is 2 sin(π/(2·4^s)).
Finite grid discrepancy contributes at most four pi divided by the
number of fine bins. The matching respects all clock multiplicities. -/
theorem clock_fit_of_grid (s r v : ℕ) (x : (Fin ((s+s)+(r+v))→Bool) → ℝ)
    (hx : ∀ i, x i∈Icc (0:ℝ) 1)
    (hc : let Q := 2^(s+s)*2^r; ∀ b : ℕ, b≤Q →
      b*2^v≤countBelow x (b/(Q:ℝ))+2^v ∧ countBelow x (b/(Q:ℝ))≤b*2^v+2^v) :
    ∃ p : Equiv.Perm (Fin ((s+s)+(r+v))→Bool), HasProjectiveCircuitApproximation _
      (clockRadius (2^(s+s))+4*π/(2^(s+s)*2^r)) s (diagonal fun j => expTurns (x (p j))) := by
  let M := 2^(s+s)
  let F := 2^r
  let Q := M*F
  have hM : 0<M := Nat.two_pow_pos _
  have hF : 0<F := Nat.two_pow_pos _
  have hQ := Nat.mul_pos hM hF
  let e₀ := clockOrder s (r+v)
  have hdim : M*2^(r+v)=Q*2^v := by dsimp only [M,F,Q]; rw [pow_add 2 r v,mul_assoc]
  let e := e₀.trans (finCongr hdim)
  obtain ⟨σ,hσ⟩ := match_repeated_clock hQ (Nat.two_pow_pos v) (x ∘ e.symm)
    (fun j => hx _) (fun b hb => by rw [countBelow_comp_equiv]; exact hc b hb)
  let p := e.trans (σ.trans e.symm)
  let d (j : Fin ((s+s)+(r+v))→Bool) := (e₀ j).val/2^(r+v)
  let θ := 2*π/M
  let G (j : Fin ((s+s)+(r+v))→Bool) := Complex.exp (Complex.I*(θ:ℂ)*(d j:ℂ))
  obtain ⟨z,hz,C,hC,hG⟩ := realizes_repeated_clock s (r+v) θ
  change diagonal G=z • C.eval.val at hG
  let u := expTurns (1/(2*M))
  have hu := norm_expTurns (1/(2*M))
  have he (j) : u*G j=expTurns (((d j:ℕ):ℝ)/M+1/(2*M)) := by
    dsimp only [u,G,expTurns,θ]
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  have htol (j) : ‖expTurns (x (p j))-u*G j‖ ≤ clockRadius M+4*π/(Q:ℝ) := by
    let b := (e j).val/2^v
    have hb : b/F=d j := by
      change (e₀ j).val/2^v/2^r=(e₀ j).val/2^(r+v)
      rw [Nat.div_div_eq_div_mul,pow_add 2 r v,Nat.mul_comm (2^r)]
    have hs : |x (p j)-(b:ℝ)/Q|≤2/Q := hσ (e j)
    have hd := remainder_in_bin b M F hM hF
    rw [hb] at hd
    have hc := half_bin_chord hM hd
    rw [←Nat.cast_mul] at hc
    rw [he]
    have h₁ := (expTurns_lip (x (p j)) (b/Q)).trans (mul_le_mul_of_nonneg_left hs two_pi_pos.le)
    exact (norm_sub_le_norm_sub_add_norm_sub _ (expTurns (b/Q)) _).trans
      ((add_le_add h₁ hc).trans_eq (by dsimp only [Q]; ring))
  refine ⟨p,u*z,by rw [norm_mul,hu,hz,one_mul],C,hC,?_⟩
  rw [←smul_smul,←hG,←Matrix.diagonal_smul,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  have hp : 0≤clockRadius M+4*π/(Q:ℝ) := (norm_nonneg _).trans (htol (fun _ => false))
  have hh := (pi_norm_le_iff_of_nonneg hp).mpr htol
  simpa only [Q,F,M,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hh

#print axioms clock_fit_of_grid
end
end GaloisForLFunctions.HTGeometry.ClockSpectrum
