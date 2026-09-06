import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairRigidity

/-!
# Polynomial recovery constrained by the physical scaling law

One half-scaling separates all total polynomial weights and already implies
the full scaling law. In the observation cusp, its weight-one eigenspace consists
exactly of real multiples of the first lost mode. Thus every polynomial recovery
that scales like the missing gap belongs to this one-dimensional family.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


theorem cubicPolynomialFlow_bicoefficient (q : ℝ) (P : Polynomial (Polynomial ℝ)) (m n : ℕ) :
    ((cubicPolynomialFlow q P).coeff m).coeff n=(P.coeff m).coeff n*q^(m+n) := by
  rw [cubicPolynomialFlow_coefficient,Polynomial.coeff_mul_C,
    cubicInnerPolynomialFlow_coefficient,pow_add]
  ring

theorem cubicPolynomialFlow_halfWeight (P : Polynomial (Polynomial ℝ)) (k : ℕ) :
    cubicPolynomialFlow (1/2) P=(1/2:ℝ)^k • P ↔
      ∀ m n : ℕ, m+n ≠ k → (P.coeff m).coeff n=0 := by
  constructor
  · intro h m n hmn
    have hc := congrArg (fun Q : Polynomial (Polynomial ℝ) => (Q.coeff m).coeff n) h
    rw [cubicPolynomialFlow_bicoefficient,Polynomial.coeff_smul,
      Polynomial.coeff_smul,smul_eq_mul] at hc
    have hpow : (1/2:ℝ)^(m+n) ≠ (1/2:ℝ)^k := by
      intro he
      exact hmn (pow_right_injective₀ (by positivity : (0:ℝ)<1/2)
        (by linarith : (1/2:ℝ) ≠ 1) he)
    have hp : (P.coeff m).coeff n*((1/2:ℝ)^(m+n)-(1/2:ℝ)^k)=0 := by
      linear_combination hc
    exact (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hpow)
  · intro h
    ext m n
    rw [cubicPolynomialFlow_bicoefficient,Polynomial.coeff_smul,
      Polynomial.coeff_smul,smul_eq_mul]
    by_cases he : m+n=k
    · rw [he,mul_comm]
    · rw [h m n he,zero_mul,mul_zero]

theorem cubicPolynomialFlow_halfWeight_fullFlow (P : Polynomial (Polynomial ℝ)) (k : ℕ) :
    cubicPolynomialFlow (1/2) P=(1/2:ℝ)^k • P ↔
      ∀ q : ℝ, cubicPolynomialFlow q P=q^k • P := by
  constructor
  · intro h q
    have hc := (cubicPolynomialFlow_halfWeight P k).mp h
    ext m n
    rw [cubicPolynomialFlow_bicoefficient,Polynomial.coeff_smul,
      Polynomial.coeff_smul,smul_eq_mul]
    by_cases he : m+n=k
    · rw [he,mul_comm]
    · rw [hc m n he,zero_mul,mul_zero]
  · intro h
    exact h (1/2)

def cubicEquivariantRecoveries : Set (Polynomial (Polynomial ℝ)) :=
  {P | P ∈ cubicCuspAlgebra ∧ cubicPolynomialFlow (1/2) P=(1/2:ℝ) • P}

theorem cubicEquivariantRecoveries_classification (P : Polynomial (Polynomial ℝ)) :
    P ∈ cubicEquivariantRecoveries ↔ ∃ α : ℝ, P=α • Polynomial.C Polynomial.X := by
  constructor
  · rintro ⟨hA,hflow⟩
    have hc := (cubicPolynomialFlow_halfWeight P 1).mp (by simpa using hflow)
    refine ⟨(P.coeff 0).coeff 1,?_⟩
    ext m n
    by_cases hm : m=0
    · subst m
      by_cases hn : n=1
      · subst n; simp
      · have hz := hc 0 n (by simpa using hn)
        simp [hz,Polynomial.coeff_X,Ne.symm hn]
    · by_cases hm1 : m=1
      · subst m
        change P.coeff 1=0 at hA
        simp [hA]
      · have hz := hc m n (by omega)
        simp [hz,Polynomial.coeff_C,hm]
  · rintro ⟨α,rfl⟩
    refine ⟨cubicCuspAlgebra.smul_mem (cubicCuspAlgebra_constant _) α,?_⟩
    have h : cubicPolynomialFlow (1/2) (α • Polynomial.C Polynomial.X)=
        (1/2:ℝ)^1 • (α • Polynomial.C Polynomial.X) := by
      rw [cubicPolynomialFlow_halfWeight]
      intro m n hmn
      by_cases hm : m=0
      · subst m
        have hn : n ≠ 1 := by simpa using hmn
        simp [Polynomial.coeff_X,Ne.symm hn]
      · simp [Polynomial.coeff_C,hm]
    simpa using h

theorem cubicEquivariantRecoveries_fullFlow :
    cubicEquivariantRecoveries=
      {P | P ∈ cubicCuspAlgebra ∧ ∀ q : ℝ, cubicPolynomialFlow q P=q • P} := by
  ext P
  change (P ∈ cubicCuspAlgebra ∧ cubicPolynomialFlow (1/2) P=(1/2:ℝ) • P) ↔
    (P ∈ cubicCuspAlgebra ∧ ∀ q : ℝ, cubicPolynomialFlow q P=q • P)
  have h := cubicPolynomialFlow_halfWeight_fullFlow P 1
  simpa only [pow_one] using and_congr_right (fun _ => h)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
