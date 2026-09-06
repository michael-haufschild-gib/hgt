import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspQuotient

/-!
# Exact algebraic loss admits uniform polynomial recovery

An explicit sequence inside the cusp algebra recovers the missing middle gap
on every physical probe with uniform error at most 2/(n+2). Hence there is no
positive uniform separation from that algebra, despite the already proved
failure of exact polynomial membership. The algebraic normalization quotient
must therefore be distinguished from a quotient completed in the uniform norm.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial

def cubicRecoveryValue : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n+1, t => cubicRecoveryValue n t+(t^2-(cubicRecoveryValue n t)^2)/2

theorem cubicRecoveryValue_bounds (n : ℕ) :
    ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ cubicRecoveryValue n t ∧ cubicRecoveryValue n t ≤ t := by
  intro t ht
  induction n with
  | zero => simpa [cubicRecoveryValue] using ht.1
  | succ n ih =>
    rw [cubicRecoveryValue]
    constructor
    · nlinarith [sq_nonneg (t-cubicRecoveryValue n t)]
    · have hp := mul_nonneg (sub_nonneg.mpr ih.2)
        (show 0 ≤ 2-(t+cubicRecoveryValue n t) by linarith [ht.2])
      nlinarith

theorem cubicRecoveryValue_error (n : ℕ) :
    ∀ t ∈ Icc (0:ℝ) 1, t-cubicRecoveryValue n t ≤ 2/((n:ℝ)+2) := by
  intro t ht
  induction n with
  | zero => simpa [cubicRecoveryValue] using ht.2
  | succ n ih =>
    have hb := cubicRecoveryValue_bounds n t ht
    have hN : 0 < (n:ℝ)+2 := by positivity
    have ha : 2/((n:ℝ)+2) ≤ 1 := (div_le_one hN).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have he0 : 0 ≤ t-cubicRecoveryValue n t := sub_nonneg.mpr hb.2
    have he1 : t-cubicRecoveryValue n t ≤ 1 := by linarith [ht.2]
    have hstep : t-cubicRecoveryValue (n+1) t ≤
        (t-cubicRecoveryValue n t)-(t-cubicRecoveryValue n t)^2/2 := by
      rw [cubicRecoveryValue]
      nlinarith [mul_nonneg hb.1 he0]
    have hmono : (t-cubicRecoveryValue n t)-(t-cubicRecoveryValue n t)^2/2 ≤
        2/((n:ℝ)+2)-(2/((n:ℝ)+2))^2/2 := by
      have hm := mul_nonneg (sub_nonneg.mpr ih)
        (show 0 ≤ 2-(2/((n:ℝ)+2)+(t-cubicRecoveryValue n t)) by linarith)
      nlinarith
    have hdiff : 2/((n:ℝ)+3)-(2/((n:ℝ)+2)-(2/((n:ℝ)+2))^2/2)=
        2/(((n:ℝ)+2)^2*((n:ℝ)+3)) := by
      field_simp
      ring
    have hrat : 2/((n:ℝ)+2)-(2/((n:ℝ)+2))^2/2 ≤ 2/((n:ℝ)+3) := by
      have hpos : 0 ≤ 2/(((n:ℝ)+2)^2*((n:ℝ)+3)) := by positivity
      linarith
    have h := hstep.trans (hmono.trans hrat)
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+2=3 by ring] using h

def cubicRecoveryPolynomial : ℕ → Polynomial (Polynomial ℝ)
  | 0 => 0
  | n+1 => cubicRecoveryPolynomial n+Polynomial.C (Polynomial.C (1/2))*
      (Polynomial.X^2-(cubicRecoveryPolynomial n)^2)

theorem cubicRecoveryPolynomial_mem (n : ℕ) : cubicRecoveryPolynomial n ∈ cubicCuspAlgebra := by
  induction n with
  | zero => exact cubicCuspAlgebra.zero_mem
  | succ n ih =>
    exact cubicCuspAlgebra.add_mem ih
      (cubicCuspAlgebra.mul_mem (cubicCuspAlgebra_constant _)
        (cubicCuspAlgebra.sub_mem cubicCuspAlgebra_square (cubicCuspAlgebra.pow_mem ih 2)))

theorem cubicRecoveryPolynomial_observation (n : ℕ) (g : cubicProbeSection) :
    cubicPolynomialObservation (cubicRecoveryPolynomial n) g=cubicRecoveryValue n (g.val 2) := by
  induction n with
  | zero => simp [cubicRecoveryPolynomial,cubicRecoveryValue]
  | succ n ih =>
    simp only [cubicRecoveryPolynomial,map_add,map_mul,map_sub,map_pow,
      Pi.add_apply,Pi.mul_apply,Pi.sub_apply,Pi.pow_apply,ih,cubicRecoveryValue]
    have hX : cubicPolynomialObservation Polynomial.X g=g.val 2 := by
      change Polynomial.eval₂ _ _ Polynomial.X=_
      simp
    have hC : cubicPolynomialObservation (Polynomial.C (Polynomial.C (1/2))) g=(1/2:ℝ) := by
      change Polynomial.eval₂ (Polynomial.evalRingHom _) _ _=_
      simp
    rw [hX,hC]
    ring

theorem cubicRecoveryPolynomial_uniformError (n : ℕ) (g : cubicProbeSection) :
    |cubicPolynomialObservation (cubicRecoveryPolynomial n) g-g.val 2| ≤ 2/((n:ℝ)+2) := by
  have ht : g.val 2 ∈ Icc (0:ℝ) 1 := by
    refine ⟨g.property.1 2,?_⟩
    have hs := g.property.2.1
    linarith [g.property.1 0,g.property.1 1,g.property.1 3,g.property.1 4]
  rw [cubicRecoveryPolynomial_observation,abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr (cubicRecoveryValue_bounds n (g.val 2) ht).2)]
  exact cubicRecoveryValue_error n (g.val 2) ht


theorem cubicCuspAlgebra_approximatesMiddle :
    ∀ ε : Ioi (0:ℝ), ∃ P ∈ cubicCuspAlgebra,
      ∀ g : cubicProbeSection, |cubicPolynomialObservation P g-g.val 2| < ε.val := by
  intro ε
  obtain ⟨n,hn⟩ := exists_nat_gt (2/ε.val)
  refine ⟨cubicRecoveryPolynomial n,cubicRecoveryPolynomial_mem n,?_⟩
  intro g
  apply (cubicRecoveryPolynomial_uniformError n g).trans_lt
  apply (div_lt_iff₀ (by positivity : 0 < (n:ℝ)+2)).mpr
  have h := (div_lt_iff₀ ε.property).mp hn
  nlinarith [ε.property]

theorem cubicCuspAlgebra_noPositiveMiddleGap :
    ¬ ∃ δ : Ioi (0:ℝ), ∀ P ∈ cubicCuspAlgebra,
      ∃ g : cubicProbeSection, δ.val ≤ |cubicPolynomialObservation P g-g.val 2| := by
  rintro ⟨δ,hδ⟩
  obtain ⟨P,hP,hclose⟩ := cubicCuspAlgebra_approximatesMiddle δ
  obtain ⟨g,hg⟩ := hδ P hP
  exact (not_lt_of_ge hg) (hclose g)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
