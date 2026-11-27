import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.HalfTurn

/-! # Linear cost of coherently testing crossed strong bonds -/
open Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open LocalEcho
noncomputable section
variable {n : ℕ}

/-- A common coordinate cap B bounds the square root of the two-step
local mass by 43B. Each overlap neighborhood has at most 43 labels. -/
theorem echo_local_mass (u : PathShell n) {B : ℝ} (cap : ∀ l, |u l|≤B) (e : Fin (n+1)) :
    localMass u e≤(43*B)^2 := by
  have sum_cap (l : PathLabel n) {v : PathLabel n→ℝ} {b : ℝ} (hb : 0≤b)
      (h : ∀ q∈ball l, v q≤b) : ∑ q∈ball l, v q≤43*b := by
    calc
      _ ≤ ∑ _q∈ball l, b := sum_le_sum h
      _ = ((ball l).card:ℝ)*b := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast ball_card l) hb
  have hi (l : PathLabel n) : ∑ q∈ball l, (u q)^2≤43*B^2 := sum_cap l (sq_nonneg B) (fun q _ => by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u q)) (cap q) 2)
  exact (sum_cap (zz e) (by positivity) (fun l _ => hi l)).trans_eq (by ring)

/-- A fit rules out k crossed longitudinal couplings of size at least h
as soon as 4kth≥π. The variance only depends on the selected k bonds. -/
theorem echo_strong_count (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (G : Finset (Fin (n+1))) (hG : G⊆crossed c) (k : ℕ) {M t h : ℝ}
    (ht : 0<t) (hM : 0≤M) (hm : ∀ e∈G, localMass u e≤M^2)
    (hh : ∀ e∈G, h≤|u (zz e)|) (hphase : π≤4*t*((k:ℝ)*h))
    (hs : t*M≤1/100) (hv : (k:ℝ)*M^2*t^2≤1/1000000) (z : ℂ) (hz : ‖z‖=1)
    (fit : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4) : G.card<k := by
  by_contra! hlarge
  obtain ⟨Q,hQ,hcard⟩ := exists_subset_card_eq hlarge
  have hsum : (k:ℝ)*h≤∑ e∈Q, |u (zz e)| := by
    simpa only [sum_const,nsmul_eq_mul,hcard] using sum_le_sum (s:=Q) (fun e he => hh e (hQ he))
  exact (no_cut_fit u C c Q (hQ.trans hG) M t hM ht (fun e he => hm e (hQ he))
    (hphase.trans (mul_le_mul_of_nonneg_left hsum (by positivity))) hs (hcard ▸ hv) z hz).not_ge fit

#print axioms echo_strong_count
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
