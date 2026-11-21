import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # From integer-resolution deadlines to an all-precision first-wait bound -/
open Matrix Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section
open PrecisionReturns

/-- A visit to accuracy B/m² by τ m^d at each integer resolution bounds
the attained first visit throughout the continuum by v(ε)² ε^d ≤ τ²(4B)^d. -/
theorem uniform_first_deadline {n s d : ℕ} (H : selfAdjoint (Register n))
    {A B τ : ℝ} (ha : 0<A) (hB : 0<B) (hτ : 0<τ)
    (h : ∀ m : ℕ, 0<m → ∃ t : ℝ, A<t ∧ t ≤ τ*(m:ℝ)^d ∧
      HasProjectiveCircuitApproximation n (B/(m:ℝ)^2) s (unitaryEvolution H.val t)) :
    ∀ ε ∈ Ioc 0 B, (firstVisit H A s ε)^2*ε^d ≤ τ^2*(4*B)^d := by
  intro ε hε
  let r := sqrt (B/ε)
  have hepos := hε.1
  have hr2 : r^2=B/ε := Real.sq_sqrt (div_nonneg hB.le hε.1.le)
  have hr : 1≤r := by
    have h1 : 1≤B/ε := (one_le_div hε.1).mpr hε.2
    nlinarith only [hr2,h1,Real.sqrt_nonneg (B/ε)]
  let m := ⌈r⌉₊
  have hmr : r≤(m:ℝ) := Nat.le_ceil _
  have hm : 0<m := Nat.cast_pos.mp (by linarith only [hmr,hr] : (0:ℝ)<m)
  have hm' : 0<(m:ℝ) := Nat.cast_pos.mpr hm
  have hmr' : (m:ℝ)≤2*r := by linarith only [Nat.ceil_lt_add_one (zero_le_one.trans hr),hr]
  have hle : B/(m:ℝ)^2 ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    have hh := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (zero_le_one.trans hr) hm'.le).mpr hmr) hε.1.le
    rwa [hr2,mul_div_cancel₀ _ hε.1.ne'] at hh
  have hscale : (m:ℝ)^2*ε ≤ 4*B := by
    have hh := mul_le_mul_of_nonneg_right ((sq_le_sq₀ hm'.le (by positivity :
      0≤2*r)).mpr hmr') hε.1.le
    calc
      _ ≤ _ := hh
      _ = _ := by rw [mul_pow,hr2]; field_simp; ring
  obtain ⟨t,hA,ht,c,hc,C,hC,he⟩ := h m hm
  have hvisit := firstVisit_isLeast H A s hε.1
  have hv : firstVisit H A s ε ≤ τ*(m:ℝ)^d := (hvisit.2 ⟨hA.le,c,hc,C,hC,he.trans hle⟩).trans ht
  calc
    _ ≤ (τ*(m:ℝ)^d)^2*ε^d := mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (ha.le.trans hvisit.1.1) (by positivity)).mpr hv) (pow_nonneg hε.1.le _)
    _ = τ^2*((m:ℝ)^2*ε)^d := by rw [mul_pow,mul_pow,←pow_mul,←pow_mul,Nat.mul_comm d 2]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale d) (sq_nonneg τ)

#print axioms uniform_first_deadline
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
