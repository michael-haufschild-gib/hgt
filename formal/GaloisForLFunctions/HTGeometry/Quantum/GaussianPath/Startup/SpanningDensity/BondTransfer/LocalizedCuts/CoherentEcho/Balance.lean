import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.Reciprocal

/-! # Balancing weak bonds and coherent cut phases against a quartic signal -/
open Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
noncomputable section

/-- At time y⁹ and weak radius a y⁴ the weak count is proportional to
N y³⁶. The coherent loss 2/(a y¹³) is payable from the same charge
exactly when N y⁴⁹ is large. All constants are independent of N. -/
theorem coherent_quartic_balance {c C : ℝ} (hc : 0<c) (hC : 0<C) :
    ∃ a∈Set.Ioc (0:ℝ) 1, ∃ D>0, ∀ {n : ℕ} (u : PathShell n) (y B : ℝ) (A : TwoQubitCircuit (n+2)) (z : ℂ),
      let N : ℝ := (n+1:ℕ)
      let h := a*y^4
      0<y → y≤1 → 0≤B → (∀ l, |u l|≤B) → D≤N*y^49 → 2000000*(43*B)^2*y^5≤a →
      ((weakEdges u h).card:ℝ)≤C*N*h^9 → ‖z‖=1 →
      ‖unitaryEvolution (pathHamiltonian u) (y^9)-z • A.eval.val‖≤1/4 →
      c*N*(y^9)^4≤(redundant (circuitWord A):ℝ)+1 →
      (1+c/2*(y^9)^4)*N<(A.gateCount:ℝ) := by
  let a := min 1 (c/(8*C))
  have ha : 0<a := lt_min zero_lt_one (div_pos hc (mul_pos (by norm_num) hC))
  have ha₁ : a≤1 := min_le_left ..
  let D := 64/(a*c)
  refine ⟨a,⟨ha,ha₁⟩,D,div_pos (by norm_num) (mul_pos ha hc),?_⟩
  intro n u y B A z N h hy hy₁ hB hcap hsize hvar hweak hz hf hr
  have hh : 0<h := mul_pos ha (pow_pos hy 4)
  have hN : 0≤N := Nat.cast_nonneg _
  have hth : y^9*h≤1 := by
    have h₁ : h≤1 := (mul_le_mul ha₁ (pow_le_one₀ hy.le hy₁) (pow_nonneg hy.le 4) zero_le_one).trans_eq (one_mul 1)
    exact (mul_le_mul (pow_le_one₀ hy.le hy₁) h₁ hh.le zero_le_one).trans_eq (one_mul 1)
  have hv := mul_le_mul_of_nonneg_right hvar (pow_nonneg hy.le 4)
  have hg := echo_reciprocal_allowance u A (pow_pos hy 9) hh hB hcap hth (by
    dsimp only [h]; linarith only [hv]) z hz hf
  have haC := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<8) hC)).mp (min_le_right 1 (c/(8*C)))
  have hp : a^9≤a := by simpa only [pow_one] using pow_le_pow_of_le_one ha.le ha₁ (by decide : 1≤9)
  have hwp : ((weakEdges u h).card:ℝ)≤c/8*N*y^36 := by
    have hh' := mul_le_mul_of_nonneg_left hp hC.le
    have ha' : C*a^9≤c/8 := by change a*(8*C)≤c at haC; linarith only [hh',haC]
    have hh'' := mul_le_mul_of_nonneg_right ha' (mul_nonneg hN (pow_nonneg hy.le 36))
    dsimp only [h] at hweak
    rw [mul_pow] at hweak
    linarith only [hh'',hweak]
  have h₆₄ := (div_le_iff₀ (mul_pos ha hc)).mp hsize
  have hden : 0<y^9*h := mul_pos (pow_pos hy 9) hh
  have herror : 2/(y^9*h)≤c/16*N*y^36 := (div_le_iff₀ hden).mpr (by
    dsimp only [h]; linarith only [h₆₄])
  have hunit : 1≤1/(y^9*h) := (le_div_iff₀ hden).mpr (by simpa only [one_mul] using hth)
  change N+_≤(A.gateCount:ℝ)+_+2/(y^9*h)+2 at hg
  have heq : 2/(y^9*h)=2*(1/(y^9*h)) := by ring
  rw [heq] at herror hg
  linarith only [hg,hr,hwp,herror,hunit]

#print axioms coherent_quartic_balance
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
