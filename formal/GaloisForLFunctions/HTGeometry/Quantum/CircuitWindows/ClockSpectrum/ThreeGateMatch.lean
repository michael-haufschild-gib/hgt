import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.QuantileMatching
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.PairedClock
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.AngularMetric

/-! # A three-gate match to an approximately uniform spectrum -/
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ClockSpectrum
noncomputable section

private theorem coarse_error (b : ℕ) : |(b:ℝ)/512-((b/8:ℕ):ℝ)/64-1/128| ≤ 1/128 := by
  have hi : b%8 < 8 := Nat.mod_lt _ (by decide)
  have he : ((b%8:ℕ):ℝ)+8*((b/8:ℕ):ℝ)=b := by exact_mod_cast Nat.mod_add_div b 8
  have hb : ((b%8:ℕ):ℝ) < 8 := by exact_mod_cast hi
  rw [abs_le]
  constructor <;> linarith only [he,hb,Nat.cast_nonneg (b%8) (α:=ℝ)]

/-- Three disjoint pairs suffice when the cumulative eigenphase counts
on a 512-point grid differ from a uniform grid by at most one bin.
The matching permutation is free and need not be a cheap physical circuit. -/
theorem three_gate_sorted_clock (v : ℕ) (x : (Fin ((3+3)+(3+v)) → Bool) → ℝ)
    (hx : ∀ i, x i ∈ Icc 0 1)
    (hc : ∀ b : ℕ, b ≤ 512 → b*2^v ≤ countBelow x (b/512)+2^v ∧ countBelow x (b/512) ≤ b*2^v+2^v) :
    ∃ p : Equiv.Perm (Fin ((3+3)+(3+v)) → Bool),
      HasProjectiveCircuitApproximation _ (1/10) 3 (diagonal fun j => expTurns (x (p j))) := by
  let I := Fin ((3+3)+(3+v)) → Bool
  let e₀ := clockOrder 3 (3+v)
  have hdim : 2^(3+3)*2^(3+v)=512*2^v := by rw [pow_add 2 3 v]; ring
  let e : I ≃ Fin (512*2^v) := e₀.trans (finCongr hdim)
  obtain ⟨σ,hσ⟩ := match_repeated_clock (Q:=512) (m:=2^v) (by decide) (by positivity) (x ∘ e.symm)
    (fun j => hx _) (fun b hb => by rw [countBelow_comp_equiv]; exact hc b hb)
  let p := e.trans (σ.trans e.symm)
  let d (j : I) := (e₀ j).val/2^(3+v)
  let θ := 2*Real.pi/64
  let F (j : I) := Complex.exp (Complex.I*(θ:ℂ)*(d j:ℂ))
  obtain ⟨z,hz,C,hC,hF⟩ := realizes_repeated_clock 3 (3+v) θ
  change diagonal F=z • C.eval.val at hF
  let s := expTurns (1/128)
  have hs : ‖s‖=1 := norm_expTurns _
  have he (j : I) : s*F j=expTurns (((d j:ℕ):ℝ)/64+1/128) := by
    dsimp only [s,F,expTurns,θ]
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  have hbound (j : I) : ‖expTurns (x (p j))-s*F j‖ ≤ 1/10 := by
    let b := (e j).val/2^v
    have hbj : b/8=d j := by
      change (e₀ j).val/2^v/8=(e₀ j).val/2^(3+v)
      rw [Nat.div_div_eq_div_mul]
      exact congrArg ((e₀ j).val / ·) ((Nat.mul_comm (2^v) 8).trans (pow_add 2 3 v).symm)
    have hf : |x (p j)-(b:ℝ)/512| ≤ 2/512 := hσ (e j)
    have hg := coarse_error b
    rw [hbj] at hg
    have hdiff : |x (p j)-(((d j:ℕ):ℝ)/64+1/128)| ≤ 2/512+1/128 := by
      rw [abs_le] at hg hf ⊢
      constructor <;> linarith only [hg.1,hg.2,hf.1,hf.2]
    rw [he]
    apply (expTurns_lip ..).trans ((mul_le_mul_of_nonneg_left hdiff (by positivity)).trans ?_)
    linarith only [Real.pi_lt_four]
  refine ⟨p,s*z,by rw [norm_mul,hs,hz,one_mul],C,hC,?_⟩
  rw [←smul_smul,←hF,←Matrix.diagonal_smul,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1/10)).mpr hbound

#print axioms three_gate_sorted_clock

/-- A uniform error of one bin in the normalized angular distribution
function suffices at every register size of at least nine qubits. -/
theorem three_gate_of_cdf {N : ℕ} (hN : 9 ≤ N) (x : (Fin N → Bool) → ℝ)
    (hx : ∀ i, x i ∈ Icc 0 1) (hc : ∀ j : Fin 513,
      |(countBelow x (j.val/512):ℝ)/(2:ℝ)^N-j.val/512|<1/512) :
    ∃ p : Equiv.Perm (Fin N → Bool), HasProjectiveCircuitApproximation N (1/10) 3
      (diagonal fun j => expTurns (x (p j))) := by
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hN
  have he : N=(3+3)+(3+v) := by omega
  clear hv
  subst N
  apply three_gate_sorted_clock v x hx
  intro b hb
  let m := 2^v
  let c := countBelow x (b/512)
  have hm : (0:ℝ) < m := by dsimp only [m]; positivity
  have h := abs_lt.mp (hc ⟨b,by omega⟩)
  have hdim : (2:ℝ)^((3+3)+(3+v))=512*(m:ℝ) := by
    simp only [m,Nat.cast_pow,Nat.cast_ofNat,pow_add]
    ring
  change -(1/512:ℝ) < (c:ℝ)/2^((3+3)+(3+v))-b/512 ∧
    (c:ℝ)/2^((3+3)+(3+v))-b/512 < 1/512 at h
  rw [hdim] at h
  obtain ⟨hl,hu⟩ := h
  field_simp [hm.ne'] at hl hu
  change b*m ≤ c+m ∧ c ≤ b*m+m
  constructor
  · exact_mod_cast (show (b:ℝ)*m ≤ c+m by linarith only [hl])
  · exact_mod_cast (show (c:ℝ) ≤ (b:ℝ)*m+m by linarith only [hu])

#print axioms three_gate_of_cdf
end
end GaloisForLFunctions.HTGeometry.ClockSpectrum
