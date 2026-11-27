import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.RHTower.Sieve.VinogradovBertrandReservoir

/-! # First waits at all errors from arbitrary-order pulse deadlines -/
open Set
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
open PrecisionReturns RHTower.Sieve
noncomputable section

/-- A discrete deadline of order m^d at accuracy B/m^p yields an
attained first-wait bound of precision exponent d/p. Rounding the least
integer p-th root keeps the constant independent of the accuracy. -/
theorem pulse_precision {n s p d : ℕ} (hp : 0 < p) (H : selfAdjoint (Register n))
    {A B T : ℝ} (hA : 0 < A) (hB : 0 < B) (hT : 0 < T)
    (h : ∀ m : ℕ, 0 < m → ∃ t : ℝ, A < t ∧ t ≤ T*(m:ℝ)^d ∧
      HasProjectiveCircuitApproximation n (B/(m:ℝ)^p) s (unitaryEvolution H.val t)) :
    ∀ ε ∈ Ioc 0 B, (firstVisit H A s ε-A)^p*ε^d ≤ T^p*((2:ℝ)^p*(2*B))^d := by
  intro ε hε
  let N := ⌈B/ε⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (div_pos hB hε.1)
  let m := vinogradovCeilRoot p N
  have hm : 0 < m := vinogradovCeilRoot_pos hp.ne' hN.ne'
  have hmp : 0<(m:ℝ)^p := pow_pos (Nat.cast_pos.mpr hm) _
  have hlow : (N:ℝ) ≤ (m:ℝ)^p := by exact_mod_cast le_vinogradovCeilRoot_pow (N:=N) hp.ne'
  have hhi : (m:ℝ)^p ≤ (2:ℝ)^p*N := by exact_mod_cast vinogradovCeilRoot_pow_le hp.ne' hN.ne'
  have htol : B/(m:ℝ)^p ≤ ε := by
    apply (div_le_iff₀ hmp).mpr
    rw [mul_comm ε]
    exact (div_le_iff₀ hε.1).mp ((Nat.le_ceil _).trans hlow)
  have hNε : (N:ℝ)*ε ≤ 2*B := by
    have hx := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_pos hB hε.1).le).le hε.1.le
    rw [add_mul,one_mul,div_mul_cancel₀ _ hε.1.ne'] at hx
    linarith only [hx,hε.2]
  have hscale : (m:ℝ)^p*ε ≤ (2:ℝ)^p*(2*B) :=
    (mul_le_mul_of_nonneg_right hhi hε.1.le).trans ((mul_assoc ..).le.trans
      (mul_le_mul_of_nonneg_left hNε (by positivity)))
  obtain ⟨t,ht,ht',z,hz,C,hC,he⟩ := h m hm
  have hv := firstVisit_isLeast H A s hε.1
  have hwait : firstVisit H A s ε-A ≤ T*(m:ℝ)^d :=
    (sub_le_self _ hA.le).trans ((hv.2 ⟨ht.le,z,hz,C,hC,he.trans htol⟩).trans ht')
  calc
    _ ≤ (T*(m:ℝ)^d)^p*ε^d := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (sub_nonneg.mpr hv.1.1) hwait p) (pow_nonneg hε.1.le _)
    _ = T^p*((m:ℝ)^p*ε)^d := by rw [mul_pow,mul_pow,←pow_mul,←pow_mul,Nat.mul_comm d p]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale d) (pow_nonneg hT.le _)

#print axioms pulse_precision
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
