import GaloisForLFunctions.HTGeometry.RadicalDifferentialAdjoin

namespace GaloisForLFunctions.HTGeometry

open scoped Differential
open GaloisForLFunctions

noncomputable section

variable {C T : Type*} [Field C] [Field T] [Algebra C T]
  [Differential C] [Differential T] [DifferentialAlgebra C T] [CharZero T]

/-- Logarithmic coefficient of a finite radical generator over its power field. -/
def scalarRadicalCoefficient (q : T) (N : ℕ) :
    differentialAdjoin C ({q ^ N} : Set T) := by
  let L := differentialAdjoin C ({q ^ N} : Set T)
  have hpow : q ^ N ∈ L := subset_differentialAdjoin C ({q ^ N} : Set T) rfl
  have hderiv : (q ^ N)′ ∈ L := derivationClosed_differentialAdjoin C _ hpow
  have hN : (N : T) ∈ L := L.natCast_mem N
  exact ⟨(q ^ N)′ / ((N : T) * q ^ N), L.div_mem hderiv (L.mul_mem hN hpow)⟩

/-- A finite radical generator satisfies its rank-one linear differential equation over the power
field. -/
theorem scalar_deriv_eq_radicalCoefficient_mul
    (q : T) (hq0 : q ≠ 0) {N : ℕ} (hN : 0 < N) :
    q′ = algebraMap (differentialAdjoin C ({q ^ N} : Set T)) T
      (scalarRadicalCoefficient q N) * q := by
  change q′ = ((q ^ N)′ / ((N : T) * q ^ N)) * q
  have hpow : (q ^ N)′ = (N : T) * q ^ (N - 1) * q′ := by
    have h := Differential.deriv.leibniz_pow (a := q) N
    simp only [nsmul_eq_mul, smul_eq_mul] at h
    rw [h]
    ring
  rw [hpow]
  have hN0 : (N : T) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  field_simp [hN0, hq0]
  conv_lhs =>
    rw [show N = (N - 1) + 1 by omega, pow_succ]
  ring

end

end GaloisForLFunctions.HTGeometry
