import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Complex.Basic

open Polynomial LaurentPolynomial
open scoped LaurentPolynomial

namespace RHTower

noncomputable section

abbrev DeningerGammaSixCofaceCoefficientRing := LaurentPolynomial ℂ

def deningerGammaSixForwardCofaceRoot :
    DeningerGammaSixCofaceCoefficientRing :=
  LaurentPolynomial.C (1 / 6 : ℂ) * LaurentPolynomial.T 1

def deningerGammaSixReflectedCofaceRoot :
    DeningerGammaSixCofaceCoefficientRing :=
  LaurentPolynomial.C (1 / 6 : ℂ) * LaurentPolynomial.T (-1)

theorem deningerGammaSixForwardCofaceRoot_ne_reflected :
    deningerGammaSixForwardCofaceRoot ≠
      deningerGammaSixReflectedCofaceRoot := by
  intro h
  unfold deningerGammaSixForwardCofaceRoot
    deningerGammaSixReflectedCofaceRoot at h
  rw [← LaurentPolynomial.single_eq_C_mul_T,
    ← LaurentPolynomial.single_eq_C_mul_T] at h
  have hcoeff := (AddMonoidAlgebra.coeff_inj).2 h
  rw [AddMonoidAlgebra.coeff_single,
    AddMonoidAlgebra.coeff_single] at hcoeff
  have hone := DFunLike.congr_fun hcoeff (1 : ℤ)
  norm_num [Finsupp.single_apply] at hone

def deningerGammaSixCommonCofacePolynomial :
    Polynomial DeningerGammaSixCofaceCoefficientRing :=
  (Polynomial.X - Polynomial.C deningerGammaSixForwardCofaceRoot) *
    (Polynomial.X - Polynomial.C deningerGammaSixReflectedCofaceRoot)

theorem deningerGammaSixCommonCofacePolynomial_expansion :
    deningerGammaSixCommonCofacePolynomial =
      Polynomial.X ^ 2 -
        Polynomial.C
          (deningerGammaSixForwardCofaceRoot +
            deningerGammaSixReflectedCofaceRoot) * Polynomial.X +
        Polynomial.C
          (deningerGammaSixForwardCofaceRoot *
            deningerGammaSixReflectedCofaceRoot) := by
  unfold deningerGammaSixCommonCofacePolynomial
  rw [Polynomial.C_add, Polynomial.C_mul]
  ring

theorem deningerGammaSixForward_mul_reflected_eq :
    deningerGammaSixForwardCofaceRoot *
        deningerGammaSixReflectedCofaceRoot =
      LaurentPolynomial.C (1 / 36 : ℂ) := by
  unfold deningerGammaSixForwardCofaceRoot
    deningerGammaSixReflectedCofaceRoot
  rw [mul_mul_mul_comm, ← LaurentPolynomial.T_add]
  norm_num [← map_mul]

/-- **Classification of finite source-valued Gamma-six cofaces.**  A finite
shift polynomial kills both literal Laurent-character normals exactly when
it is divisible by their monic quadratic product. -/
theorem deningerGammaSix_commonCoface_annihilator_iff
    (P : Polynomial DeningerGammaSixCofaceCoefficientRing) :
    P.eval deningerGammaSixForwardCofaceRoot = 0 ∧
        P.eval deningerGammaSixReflectedCofaceRoot = 0 ↔
      deningerGammaSixCommonCofacePolynomial ∣ P := by
  constructor
  · rintro ⟨hforward, hreflected⟩
    have hforwardDvd :
        Polynomial.X - Polynomial.C deningerGammaSixForwardCofaceRoot ∣ P :=
      Polynomial.dvd_iff_isRoot.mpr hforward
    obtain ⟨Q, hQ⟩ := hforwardDvd
    have hfactorNe :
        deningerGammaSixReflectedCofaceRoot -
            deningerGammaSixForwardCofaceRoot ≠ 0 :=
      sub_ne_zero.mpr deningerGammaSixForwardCofaceRoot_ne_reflected.symm
    have hQroot : Q.eval deningerGammaSixReflectedCofaceRoot = 0 := by
      rw [hQ, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C] at hreflected
      exact (mul_eq_zero.mp hreflected).resolve_left hfactorNe
    have hreflectedDvd :
        Polynomial.X - Polynomial.C deningerGammaSixReflectedCofaceRoot ∣ Q :=
      Polynomial.dvd_iff_isRoot.mpr hQroot
    obtain ⟨R, hR⟩ := hreflectedDvd
    refine ⟨R, ?_⟩
    rw [deningerGammaSixCommonCofacePolynomial, hQ, hR]
    ring
  · rintro ⟨Q, hQ⟩
    rw [hQ, deningerGammaSixCommonCofacePolynomial]
    constructor
    · simp
    · simp

/-- The common quadratic is monic. -/
theorem deningerGammaSixCommonCofacePolynomial_monic :
    deningerGammaSixCommonCofacePolynomial.Monic := by
  unfold deningerGammaSixCommonCofacePolynomial
  exact (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _)

/-- No common annihilator has smaller degree than the canonical quadratic. -/
theorem deningerGammaSixCommonCofacePolynomial_degree_le_of_commonAnnihilator
    {P : Polynomial DeningerGammaSixCofaceCoefficientRing}
    (hP : P ≠ 0)
    (hforward : P.eval deningerGammaSixForwardCofaceRoot = 0)
    (hreflected : P.eval deningerGammaSixReflectedCofaceRoot = 0) :
    deningerGammaSixCommonCofacePolynomial.degree ≤ P.degree := by
  exact Polynomial.degree_le_of_dvd
    ((deningerGammaSix_commonCoface_annihilator_iff P).mp
      ⟨hforward, hreflected⟩) hP

/-- The canonical quadratic is the unique monic common annihilator of
minimal degree. -/
theorem deningerGammaSixCommonCofacePolynomial_unique_monic_minimal
    (P : Polynomial DeningerGammaSixCofaceCoefficientRing)
    (hPmonic : P.Monic)
    (hforward : P.eval deningerGammaSixForwardCofaceRoot = 0)
    (hreflected : P.eval deningerGammaSixReflectedCofaceRoot = 0)
    (hdegree : P.natDegree ≤
      deningerGammaSixCommonCofacePolynomial.natDegree) :
    P = deningerGammaSixCommonCofacePolynomial := by
  have hdvd : deningerGammaSixCommonCofacePolynomial ∣ P :=
    (deningerGammaSix_commonCoface_annihilator_iff P).mp
      ⟨hforward, hreflected⟩
  have heq : deningerGammaSixCommonCofacePolynomial = P :=
    Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff
      hdvd hdegree (by
        rw [deningerGammaSixCommonCofacePolynomial_monic.leadingCoeff,
          hPmonic.leadingCoeff])
  exact heq.symm

end

end RHTower
