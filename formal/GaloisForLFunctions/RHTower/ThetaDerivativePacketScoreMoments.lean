import GaloisForLFunctions.RHTower.ThetaDerivativePacketLogConcavity
import GaloisForLFunctions.RHTower.ThetaScoreFloorCompactTailStability
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Raw score moment identities for actual theta derivative packets

The raw packet moments retain normalization `R_j = 2 ∫_{x>0} x^{2j} k_t(x) dx`.
Integration by parts gives the exact score gap
`(32j + 17) R_j - 303 R_{j+1} = 2 ∫_{x>0} x^{2j} Lk_t(x) dx`.
Every finite signed coefficient quadratic form is the integral of its polynomial square
against this same score. All identities and integrability statements hold for every real
packet parameter, without a sign premise.
-/

open MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower
noncomputable section

/-- The raw even moment of an actual theta derivative packet. -/
def thetaDerivativePacketRawEvenMoment (m : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  2 * ∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaDerivativePacket m t x

/-- The raw moment defect selected by the theta score operator. -/
def thetaDerivativePacketRawScoreGap (m : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  (32 * (j : ℝ) + 17) * thetaDerivativePacketRawEvenMoment m t j -
    303 * thetaDerivativePacketRawEvenMoment m t (j + 1)

/-- The finite signed coefficient quadratic form of packet score gaps. -/
def thetaDerivativePacketFiniteScoreGap {N : ℕ} (m : ℕ) (t : ℝ) (a : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * a j * thetaDerivativePacketRawScoreGap m t ((i : ℕ) + (j : ℕ))

/-- Polynomial form of the raw packet score-gap quadratic form. -/
def thetaDerivativePacketPolynomialScoreGap (m : ℕ) (t : ℝ) (P : ℝ[X]) : ℝ :=
  thetaDerivativePacketFiniteScoreGap m t (fun i : Fin (P.natDegree + 1) => P.coeff i)

private theorem packet_deriv (m : ℕ) (t x : ℝ) :
    deriv (thetaDerivativePacket m t) x =
      iteratedDeriv 1 thetaCuspFullSource x +
        t * iteratedDeriv (4 * m + 1) thetaCuspFullSource x := by
  have h := (hasDerivAt_thetaDerivativePacket_iteratedDeriv m t 0 x).deriv
  change deriv (fun y => thetaCuspFullSource y + t * iteratedDeriv (4 * m) thetaCuspFullSource y) x = _
  simpa only [iteratedDeriv_zero, zero_add, Nat.add_comm] using h

private theorem packet_pow_deriv_integrable (m j : ℕ) (t : ℝ) :
    Integrable (fun x : ℝ => x ^ j * deriv (thetaDerivativePacket m t) x) := by
  have h := (integrable_pow_mul_iteratedDeriv_thetaCuspFullSource 1 j).add
    ((integrable_pow_mul_iteratedDeriv_thetaCuspFullSource (4 * m + 1) j).const_mul t)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  rw [packet_deriv]
  ring

private theorem packet_pow_deriv_integral (m j : ℕ) (t : ℝ) :
    (∫ x : ℝ, x ^ (j + 1) * deriv (thetaDerivativePacket m t) x) =
      -((j + 1 : ℕ) : ℝ) * (∫ x : ℝ, x ^ j * thetaDerivativePacket m t x) := by
  have hd : (fun x : ℝ => x ^ (j + 1) * deriv (thetaDerivativePacket m t) x) =
      (fun x => x ^ (j + 1) * iteratedDeriv 1 thetaCuspFullSource x) +
      (fun x => t * (x ^ (j + 1) * iteratedDeriv (4 * m + 1) thetaCuspFullSource x)) := by
    funext x
    simp only [Pi.add_apply]
    rw [packet_deriv]
    ring
  rw [hd]
  change (∫ x : ℝ, x ^ (j + 1) * iteratedDeriv 1 thetaCuspFullSource x +
    t * (x ^ (j + 1) * iteratedDeriv (4 * m + 1) thetaCuspFullSource x)) = _
  rw [integral_add (integrable_pow_mul_iteratedDeriv_thetaCuspFullSource 1 (j + 1))
    ((integrable_pow_mul_iteratedDeriv_thetaCuspFullSource (4 * m + 1) (j + 1)).const_mul t),
    integral_const_mul]
  have h0 := integral_pow_mul_iteratedDeriv_succ_thetaCuspFullSource 0 (j + 1)
  have hm := integral_pow_mul_iteratedDeriv_succ_thetaCuspFullSource (4 * m) (j + 1)
  simp only [zero_add, Nat.add_sub_cancel, iteratedDeriv_zero] at h0 hm
  rw [h0, hm, integral_pow_mul_thetaDerivativePacket]
  ring

private theorem even_integral_eq_twice_Ioi {f : ℝ → ℝ}
    (heven : ∀ x, f (-x) = f x) (hint : Integrable f) :
    (∫ x : ℝ, f x) = 2 * ∫ x : ℝ in Ioi 0, f x := by
  have hrefl : ∫ x : ℝ in Ioi 0, f x = ∫ x : ℝ in Iic 0, f x := by
    have h := integral_comp_neg_Ioi (0 : ℝ) f
    simpa [heven] using h
  have hsplit : (∫ x : ℝ in Iic 0, f x) + ∫ x : ℝ in Ioi 0, f x = ∫ x : ℝ, f x := by
    have h := integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hint
    simpa [Set.compl_Iic] using h
  rw [← hrefl] at hsplit
  linarith

/-- Evenness identifies the raw half-line normalization with the complete-source moment. -/
theorem thetaDerivativePacketRawEvenMoment_eq_integral (m j : ℕ) (t : ℝ) :
    thetaDerivativePacketRawEvenMoment m t j =
      ∫ x : ℝ, x ^ (2 * j) * thetaDerivativePacket m t x := by
  symm
  exact even_integral_eq_twice_Ioi
    (fun x => by simp [pow_mul, thetaDerivativePacket_neg])
    (integrable_pow_mul_thetaDerivativePacket m (2 * j) t)

private theorem score_monomial_expansion (m j : ℕ) (t : ℝ) :
    (fun x : ℝ => x ^ (2 * j) * thetaScoreFloorOperator (thetaDerivativePacket m t) x) =
      fun x => x ^ (2 * j) * thetaDerivativePacket m t x -
        303 * (x ^ (2 * j + 2) * thetaDerivativePacket m t x) -
        16 * (x ^ (2 * j + 1) * deriv (thetaDerivativePacket m t) x) := by
  funext x
  simp only [thetaScoreFloorOperator, pow_add]
  ring

private theorem score_monomial_integrable (m j : ℕ) (t : ℝ) :
    Integrable (fun x : ℝ => x ^ (2 * j) *
      thetaScoreFloorOperator (thetaDerivativePacket m t) x) := by
  rw [score_monomial_expansion]
  exact ((integrable_pow_mul_thetaDerivativePacket m (2 * j) t).sub
    ((integrable_pow_mul_thetaDerivativePacket m (2 * j + 2) t).const_mul 303)).sub
    ((packet_pow_deriv_integrable m (2 * j + 1) t).const_mul 16)

/-- Every even monomial times the actual packet score is integrable on the half-line. -/
theorem integrableOn_pow_mul_thetaDerivativePacket_score (m j : ℕ) (t : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * j) *
      thetaScoreFloorOperator (thetaDerivativePacket m t) x) (Ioi 0) :=
  (score_monomial_integrable m j t).integrableOn

private theorem score_monomial_even (m j : ℕ) (t x : ℝ) :
    (-x) ^ (2 * j) * thetaScoreFloorOperator (thetaDerivativePacket m t) (-x) =
      x ^ (2 * j) * thetaScoreFloorOperator (thetaDerivativePacket m t) x := by
  have hodd : deriv (thetaDerivativePacket m t) (-x) = -deriv (thetaDerivativePacket m t) x := by
    simpa only [iteratedDeriv_one, pow_one, neg_one_mul] using
      iteratedDeriv_thetaDerivativePacket_neg m t 1 x
  simp [thetaScoreFloorOperator, thetaDerivativePacket_neg, hodd, pow_mul]

/-- The exact all-order Ward identity, retaining the raw factor `2`. -/
theorem thetaDerivativePacketRawScoreGap_eq_integral (m j : ℕ) (t : ℝ) :
    thetaDerivativePacketRawScoreGap m t j =
      2 * ∫ x : ℝ in Ioi 0, x ^ (2 * j) *
        thetaScoreFloorOperator (thetaDerivativePacket m t) x := by
  rw [← even_integral_eq_twice_Ioi (score_monomial_even m j t)
    (score_monomial_integrable m j t), score_monomial_expansion]
  have hsub :
      (∫ x : ℝ, x ^ (2 * j) * thetaDerivativePacket m t x -
        303 * (x ^ (2 * j + 2) * thetaDerivativePacket m t x) -
        16 * (x ^ (2 * j + 1) * deriv (thetaDerivativePacket m t) x)) =
      (∫ x : ℝ, x ^ (2 * j) * thetaDerivativePacket m t x -
        303 * (x ^ (2 * j + 2) * thetaDerivativePacket m t x)) -
      ∫ x : ℝ, 16 * (x ^ (2 * j + 1) * deriv (thetaDerivativePacket m t) x) :=
    integral_sub
      ((integrable_pow_mul_thetaDerivativePacket m (2 * j) t).sub
        ((integrable_pow_mul_thetaDerivativePacket m (2 * j + 2) t).const_mul 303))
      ((packet_pow_deriv_integrable m (2 * j + 1) t).const_mul 16)
  rw [hsub, integral_sub (integrable_pow_mul_thetaDerivativePacket m (2 * j) t)
      ((integrable_pow_mul_thetaDerivativePacket m (2 * j + 2) t).const_mul 303),
    integral_const_mul, integral_const_mul, packet_pow_deriv_integral m (2 * j) t]
  unfold thetaDerivativePacketRawScoreGap
  rw [thetaDerivativePacketRawEvenMoment_eq_integral, thetaDerivativePacketRawEvenMoment_eq_integral]
  rw [show 2 * (j + 1) = 2 * j + 2 by omega]
  push_cast
  ring

private def coefficientObservable {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ i, a i * x ^ (2 * (i : ℕ))

private theorem square_expansion {N : ℕ} (a : Fin N → ℝ) (g : ℝ → ℝ) :
    (fun x => coefficientObservable a x ^ 2 * g x) =
      fun x => ∑ i, ∑ j, (a i * a j) * (x ^ (2 * ((i : ℕ) + (j : ℕ))) * g x) := by
  funext x
  simp only [coefficientObservable, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.mul_add, pow_add]
  ring

/-- Every finite signed coefficient polynomial square times the packet score is integrable. -/
theorem integrableOn_finiteSquare_mul_thetaDerivativePacket_score
    {N : ℕ} (m : ℕ) (t : ℝ) (a : Fin N → ℝ) :
    IntegrableOn (fun x : ℝ => (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 *
      thetaScoreFloorOperator (thetaDerivativePacket m t) x) (Ioi 0) := by
  change IntegrableOn (fun x : ℝ => coefficientObservable a x ^ 2 *
    thetaScoreFloorOperator (thetaDerivativePacket m t) x) (Ioi 0)
  rw [square_expansion]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrableOn_pow_mul_thetaDerivativePacket_score m ((i : ℕ) + (j : ℕ)) t).const_mul (a i * a j)

/-- The complete signed finite quadratic form equals its polynomial-square score integral. -/
theorem thetaDerivativePacketFiniteScoreGap_eq_integral
    {N : ℕ} (m : ℕ) (t : ℝ) (a : Fin N → ℝ) :
    thetaDerivativePacketFiniteScoreGap m t a =
      2 * ∫ x : ℝ in Ioi 0, (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 *
        thetaScoreFloorOperator (thetaDerivativePacket m t) x := by
  change thetaDerivativePacketFiniteScoreGap m t a =
    2 * ∫ x : ℝ in Ioi 0, coefficientObservable a x ^ 2 *
      thetaScoreFloorOperator (thetaDerivativePacket m t) x
  rw [square_expansion, integral_finsetSum _ (fun (i : Fin N) _ =>
    integrable_finsetSum _ fun (j : Fin N) _ =>
      (integrableOn_pow_mul_thetaDerivativePacket_score m ((i : ℕ) + (j : ℕ)) t).const_mul (a i * a j)),
    Finset.mul_sum]
  unfold thetaDerivativePacketFiniteScoreGap
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun (j : Fin N) _ =>
    (integrableOn_pow_mul_thetaDerivativePacket_score m ((i : ℕ) + (j : ℕ)) t).const_mul (a i * a j)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, thetaDerivativePacketRawScoreGap_eq_integral]
  ring

private theorem polynomial_coefficientObservable (P : ℝ[X]) (x : ℝ) :
    coefficientObservable (fun i : Fin (P.natDegree + 1) => P.coeff i) x =
      P.eval (x ^ 2) := by
  rw [Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simp only [coefficientObservable, pow_mul]

/-- Every polynomial square times the packet score is integrable on the half-line. -/
theorem integrableOn_polynomialSquare_mul_thetaDerivativePacket_score
    (m : ℕ) (t : ℝ) (P : ℝ[X]) :
    IntegrableOn (fun x : ℝ => P.eval (x ^ 2) ^ 2 *
      thetaScoreFloorOperator (thetaDerivativePacket m t) x) (Ioi 0) := by
  have h := integrableOn_finiteSquare_mul_thetaDerivativePacket_score m t
    (fun i : Fin (P.natDegree + 1) => P.coeff i)
  change IntegrableOn (fun x : ℝ => coefficientObservable
    (fun i : Fin (P.natDegree + 1) => P.coeff i) x ^ 2 *
    thetaScoreFloorOperator (thetaDerivativePacket m t) x) (Ioi 0) at h
  simp_rw [polynomial_coefficientObservable] at h
  exact h

/-- Exact polynomial score identity; no coefficient signs are assumed. -/
theorem thetaDerivativePacketPolynomialScoreGap_eq_integral
    (m : ℕ) (t : ℝ) (P : ℝ[X]) :
    thetaDerivativePacketPolynomialScoreGap m t P =
      2 * ∫ x : ℝ in Ioi 0, P.eval (x ^ 2) ^ 2 *
        thetaScoreFloorOperator (thetaDerivativePacket m t) x := by
  have h := thetaDerivativePacketFiniteScoreGap_eq_integral m t
    (fun i : Fin (P.natDegree + 1) => P.coeff i)
  change thetaDerivativePacketPolynomialScoreGap m t P =
    2 * ∫ x : ℝ in Ioi 0, coefficientObservable
      (fun i : Fin (P.natDegree + 1) => P.coeff i) x ^ 2 *
      thetaScoreFloorOperator (thetaDerivativePacket m t) x at h
  simp_rw [polynomial_coefficientObservable] at h
  exact h

end
end RHTower
