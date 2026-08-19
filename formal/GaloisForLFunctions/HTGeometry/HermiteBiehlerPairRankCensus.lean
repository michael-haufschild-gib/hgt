import GaloisForLFunctions.HTGeometry.PolynomialQuotientMultiplicationRank
import GaloisForLFunctions.HTGeometry.GcdDerivativeDistinctRoots
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The de Branges pair reads the distinct-root census

For a divisor polynomial `W`, a cofactor `H` coprime to `W`, and `F = W * H`, the de Branges value
`E = F + i F'` is congruent to `i H F'` modulo `W`.  Hence multiplication by `E` on the finite
local algebra `C[X]/(W)` has

`rank = #{distinct roots of W}`,  `nullity = deg W - #{distinct roots of W}`.

Schwarz reflection `E# = F - i F'` recovers the two generators through `E + E# = 2F` and
`E - E# = 2i F'`, and `gcd (F, E)`, `gcd (F, F')`, `gcd (E, E#)` are associated.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- The de Branges value attached to an entire real pair, in polynomial form. -/
def deBrangesValue (F : ℂ[X]) : ℂ[X] := F + C Complex.I * derivative F

/-- Its Schwarz reflection. -/
def deBrangesReflection (F : ℂ[X]) : ℂ[X] := F - C Complex.I * derivative F

theorem deBrangesValue_add_reflection (F : ℂ[X]) :
    deBrangesValue F + deBrangesReflection F = 2 * F := by
  simp only [deBrangesValue, deBrangesReflection]; ring

theorem deBrangesValue_sub_reflection (F : ℂ[X]) :
    deBrangesValue F - deBrangesReflection F = 2 * C Complex.I * derivative F := by
  simp only [deBrangesValue, deBrangesReflection]; ring

theorem isUnit_C_I : IsUnit (C Complex.I) :=
  isUnit_C.2 (isUnit_iff_ne_zero.2 Complex.I_ne_zero)

variable {K : Type*}

/-- Adding a multiple of `W` does not change the gcd with `W`, up to associates. -/
theorem associated_gcd_add_mul (W R S : ℂ[X]) :
    Associated (EuclideanDomain.gcd W (W * S + R)) (EuclideanDomain.gcd W R) := by
  classical
  refine associated_of_dvd_dvd ?_ ?_
  · refine EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) ?_
    have h1 := EuclideanDomain.gcd_dvd_left W (W * S + R)
    have h2 := EuclideanDomain.gcd_dvd_right W (W * S + R)
    have hsub := dvd_sub h2 (h1.mul_right S)
    have hR : (W * S + R) - W * S = R := by ring
    rwa [hR] at hsub
  · refine EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) ?_
    exact dvd_add ((EuclideanDomain.gcd_dvd_left W R).mul_right S)
      (EuclideanDomain.gcd_dvd_right W R)

/-- A coprime unit-scaled cofactor does not change the gcd with `W`, up to associates. -/
theorem associated_gcd_unit_coprime_mul (W H R : ℂ[X]) (hcop : IsCoprime W H) :
    Associated (EuclideanDomain.gcd W (C Complex.I * H * R)) (EuclideanDomain.gcd W R) := by
  classical
  refine associated_of_dvd_dvd ?_ ?_
  · refine EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) ?_
    set d := EuclideanDomain.gcd W (C Complex.I * H * R) with hd
    have hdW : d ∣ W := EuclideanDomain.gcd_dvd_left _ _
    have hdT : d ∣ C Complex.I * H * R := EuclideanDomain.gcd_dvd_right _ _
    have hdcop : IsCoprime d H := IsCoprime.of_isCoprime_of_dvd_left hcop hdW
    have hdT' : d ∣ (C Complex.I * R) * H := by
      have : C Complex.I * H * R = (C Complex.I * R) * H := by ring
      rwa [this] at hdT
    have hdIR : d ∣ C Complex.I * R := hdcop.dvd_of_dvd_mul_right hdT'
    have := hdIR.mul_left (C Complex.I⁻¹)
    have heq : C Complex.I⁻¹ * (C Complex.I * R) = R := by
      rw [← mul_assoc, ← map_mul]
      rw [inv_mul_cancel₀ Complex.I_ne_zero, map_one, one_mul]
    rwa [heq] at this
  · refine EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) ?_
    exact (EuclideanDomain.gcd_dvd_right W R).mul_left _

theorem gcd_ne_zero_left {W R : ℂ[X]} (hW : W ≠ 0) :
    EuclideanDomain.gcd W R ≠ 0 := by
  classical
  intro h
  rw [EuclideanDomain.gcd_eq_zero_iff] at h
  exact hW h.1

theorem natDegree_eq_of_associated {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : Associated p q) : p.natDegree = q.natDegree :=
  le_antisymm (natDegree_le_of_dvd h.dvd hq) (natDegree_le_of_dvd h.symm.dvd hp)

/-- **The de Branges value reduces to the derivative gcd.** -/
theorem associated_gcd_deBrangesValue (W H : ℂ[X]) (hcop : IsCoprime W H) :
    Associated (EuclideanDomain.gcd W (deBrangesValue (W * H)))
      (EuclideanDomain.gcd W (derivative W)) := by
  classical
  have hsplit : deBrangesValue (W * H) =
      W * (H + C Complex.I * derivative H) + C Complex.I * H * derivative W := by
    simp only [deBrangesValue, derivative_mul]
    ring
  have h1 : Associated (EuclideanDomain.gcd W (deBrangesValue (W * H)))
      (EuclideanDomain.gcd W (C Complex.I * H * derivative W)) := by
    rw [hsplit]; exact associated_gcd_add_mul W _ _
  exact h1.trans (associated_gcd_unit_coprime_mul W H (derivative W) hcop)

/-- **Rank census.**  Multiplication by the de Branges value on the finite local algebra of the
divisor polynomial has rank exactly the number of distinct roots. -/
theorem finrank_range_polyQuotMul_deBrangesValue (W H : ℂ[X]) (hW : W ≠ 0)
    (hcop : IsCoprime W H) :
    Module.finrank ℂ (LinearMap.range (polyQuotMul W (deBrangesValue (W * H)))) =
      W.roots.toFinset.card := by
  classical
  have hgcdE := finrank_range_polyQuotMul_add_natDegree_gcd W (deBrangesValue (W * H)) hW
  have hdeg : (EuclideanDomain.gcd W (deBrangesValue (W * H))).natDegree =
      (EuclideanDomain.gcd W (derivative W)).natDegree :=
    natDegree_eq_of_associated (gcd_ne_zero_left hW) (gcd_ne_zero_left hW)
      (associated_gcd_deBrangesValue W H hcop)
  have hcensus := natDegree_gcd_derivative_add_card_roots (K := ℂ) W hW
  omega

/-- **Nullity census.** -/
theorem finrank_ker_polyQuotMul_deBrangesValue (W H : ℂ[X]) (hW : W ≠ 0)
    (hcop : IsCoprime W H) :
    Module.finrank ℂ (LinearMap.ker (polyQuotMul W (deBrangesValue (W * H)))) =
      W.natDegree - W.roots.toFinset.card := by
  classical
  have hker := finrank_ker_polyQuotMul W (deBrangesValue (W * H)) hW
  have hdeg : (EuclideanDomain.gcd W (deBrangesValue (W * H))).natDegree =
      (EuclideanDomain.gcd W (derivative W)).natDegree :=
    natDegree_eq_of_associated (gcd_ne_zero_left hW) (gcd_ne_zero_left hW)
      (associated_gcd_deBrangesValue W H hcop)
  have hcensus := natDegree_gcd_derivative_add_card_roots (K := ℂ) W hW
  omega

/-- The dimension of the finite local algebra is the total multiplicity. -/
theorem finrank_polyQuot (W : ℂ[X]) (hW : W ≠ 0) :
    Module.finrank ℂ (polyQuot W) = W.natDegree :=
  finrank_polynomialQuotient hW

/-- **Single-fibre form.**  On the local Artin algebra of one zero of order `m`, multiplication by
the de Branges value has rank one and nullity `m - 1`. -/
theorem finrank_range_polyQuotMul_deBrangesValue_local (rho : ℂ) (m : ℕ) (hm : 0 < m)
    (H : ℂ[X]) (hcop : IsCoprime ((X - C rho) ^ m) H) :
    Module.finrank ℂ
        (LinearMap.range (polyQuotMul ((X - C rho) ^ m)
          (deBrangesValue ((X - C rho) ^ m * H)))) = 1 := by
  classical
  have hW : ((X - C rho) ^ m : ℂ[X]) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero rho)
  rw [finrank_range_polyQuotMul_deBrangesValue _ H hW hcop]
  have hroots : ((X - C rho) ^ m : ℂ[X]).roots = m • ({rho} : Multiset ℂ) := by
    rw [roots_pow, roots_X_sub_C]
  rw [hroots]
  simp [Multiset.toFinset_nsmul _ m hm.ne']

theorem finrank_ker_polyQuotMul_deBrangesValue_local (rho : ℂ) (m : ℕ) (hm : 0 < m)
    (H : ℂ[X]) (hcop : IsCoprime ((X - C rho) ^ m) H) :
    Module.finrank ℂ
        (LinearMap.ker (polyQuotMul ((X - C rho) ^ m)
          (deBrangesValue ((X - C rho) ^ m * H)))) = m - 1 := by
  classical
  have hW : ((X - C rho) ^ m : ℂ[X]) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero rho)
  rw [finrank_ker_polyQuotMul_deBrangesValue _ H hW hcop]
  have hroots : ((X - C rho) ^ m : ℂ[X]).roots = m • ({rho} : Multiset ℂ) := by
    rw [roots_pow, roots_X_sub_C]
  rw [hroots, natDegree_pow, natDegree_X_sub_C, mul_one]
  simp [Multiset.toFinset_nsmul _ m hm.ne']

end

end GaloisForLFunctions.HTGeometry
