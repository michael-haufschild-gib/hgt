import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.MergerCount

/-! # A reciprocal bound on the loss of component mergers -/
open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
noncomputable section
variable {n : ℕ}

/-- The number of strong-bond mergers that may be lost in a fit is
at most 2/(th)+2. The variance condition is linear in t/h because
the coherent echo uses only ceil(1/(th)) test bonds. -/
theorem echo_reciprocal_allowance (u : PathShell n) (C : TwoQubitCircuit (n+2)) {t B h : ℝ}
    (ht : 0<t) (hh : 0<h) (hB : 0≤B) (cap : ∀ l, |u l|≤B)
    (hth : t*h≤1) (hvar : 2000000*(43*B)^2*t≤h)
    (z : ℂ) (hz : ‖z‖=1) (hf : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4) :
    ((n+1:ℕ):ℝ)+(redundant (circuitWord C):ℝ)≤(C.gateCount:ℝ)+(weakEdges u h).card+2/(t*h)+2 := by
  let k := ⌈1/(t*h)⌉₊
  let M := 43*B
  have hpos := mul_pos ht hh
  have hlo : 1≤(k:ℝ)*(t*h) := (div_le_iff₀ hpos).mp (Nat.le_ceil _)
  have hhi : (k:ℝ)≤1/(t*h)+1 := (Nat.ceil_lt_add_one (one_div_pos.mpr hpos).le).le
  have hk : (k:ℝ)*(t*h)≤2 := calc
    _ ≤ (1/(t*h)+1)*(t*h) := mul_le_mul_of_nonneg_right hhi hpos.le
    _ = 1+t*h := by rw [add_mul,one_div_mul_cancel hpos.ne',one_mul]
    _ ≤ _ := by linarith only [hth]
  have hv : (k:ℝ)*M^2*t^2≤1/1000000 := by
    apply (le_of_mul_le_mul_right (a:=h) (by
      have he := mul_le_mul_of_nonneg_right hk (mul_nonneg (sq_nonneg M) ht.le)
      change 2000000*M^2*t≤h at hvar
      linarith only [he,hvar]) hh)
  have hs : t*M≤1/100 := by
    have hmass := mul_le_mul_of_nonneg_right hvar ht.le
    change 2000000*M^2*t*t≤h*t at hmass
    apply (sq_le_sq₀ (mul_nonneg ht.le (mul_nonneg (by norm_num) hB)) (by norm_num : (0:ℝ)≤1/100)).mp
    linarith only [hmass,hth]
  have hg := echo_merge_budget u C k (h:=h) ht hB cap
    (by linarith only [hlo,Real.pi_lt_four]) hs hv z hz hf
  have hcount := (Nat.cast_le (α:=ℝ)).mpr hg
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at hcount
  have heq : 2/(t*h)=2*(1/(t*h)) := by ring
  rw [heq]
  rw [Nat.cast_add,Nat.cast_one]
  linarith only [hcount,hhi]

#print axioms echo_reciprocal_allowance
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
