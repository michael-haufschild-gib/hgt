import GaloisForLFunctions.HTGeometry.DifferentialPolynomial
import Mathlib.Tactic

/-!
# The Schwarzian bridge from a projective stable core

This file formalizes the source-pure algebraic step in the rational coarse-graining theorem.  A
differential endomorphism which acts projectively on a surviving hypertranscendental coordinate
fixes its Schwarzian, and that Schwarzian cannot be a base constant.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The Schwarzian differential invariant. -/
def schwarzian {K : Type*} [Field K] [Differential K] (x : K) : K :=
  x′′′ / x′ - (3 / 2 : K) * (x′′ / x′) ^ 2

/-- The Schwarzian is unchanged by a differential-constant affine transformation. -/
theorem schwarzian_affine
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x a b : K) (ha : a′ = 0) (hb : b′ = 0) (hax : a ≠ 0) (hx : x′ ≠ 0) :
    schwarzian (a * x + b) = schwarzian x := by
  have h1 : (a * x + b)′ = a * x′ := by
    simp only [map_add, Derivation.leibniz, ha, hb, smul_eq_mul, mul_zero, add_zero]
  have h2 : (a * x + b)′′ = a * x′′ := by
    rw [h1]
    simp only [Derivation.leibniz, ha, smul_eq_mul, mul_zero, add_zero]
  have h3 : (a * x + b)′′′ = a * x′′′ := by
    rw [h2]
    simp only [Derivation.leibniz, ha, smul_eq_mul, mul_zero, add_zero]
  rw [schwarzian, h3, h2, h1, schwarzian]
  field_simp

/-- The Schwarzian is unchanged by inversion away from its genuine denominators. -/
theorem schwarzian_inv
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x : K) (hx : x ≠ 0) (hdx : x′ ≠ 0) :
    schwarzian x⁻¹ = schwarzian x := by
  have h1 : (x⁻¹)′ = -x⁻¹ ^ 2 * x′ := by
    simpa [smul_eq_mul] using Differential.deriv.leibniz_inv x
  have h2 : (x⁻¹)′′ = 2 * x⁻¹ ^ 3 * x′ ^ 2 - x⁻¹ ^ 2 * x′′ := by
    rw [h1]
    simp only [map_neg, Derivation.leibniz,
      Derivation.leibniz_pow, Derivation.leibniz_inv, smul_eq_mul]
    ring
  have h3 : (x⁻¹)′′′ =
      -6 * x⁻¹ ^ 4 * x′ ^ 3 + 6 * x⁻¹ ^ 3 * x′ * x′′ - x⁻¹ ^ 2 * x′′′ := by
    have htwo : (2 : K)′ = 0 := by
      have h := (Differential.deriv : Derivation ℤ K K).map_intCast (2 : ℤ)
      norm_num at h
      exact h
    rw [h2]
    simp only [map_sub, Derivation.leibniz,
      Derivation.leibniz_pow, Derivation.leibniz_inv, htwo, smul_eq_mul]
    ring
  rw [schwarzian, h3, h2, h1, schwarzian]
  field_simp
  ring

private theorem deriv_div_eq_zero
    {K : Type*} [Field K] [Differential K]
    (a b : K) (ha : a′ = 0) (hb : b′ = 0) : (a / b)′ = 0 := by
  rw [(Differential.deriv : Derivation ℤ K K).leibniz_div]
  simp [ha, hb]

/-- The Schwarzian is invariant under every nondegenerate differential-constant Möbius map. -/
theorem schwarzian_mobius
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x a b c d : K)
    (ha : a′ = 0) (hb : b′ = 0) (hcder : c′ = 0) (hdder : d′ = 0)
    (hdet : a * d - b * c ≠ 0)
    (hden : c * x + d ≠ 0) (hdx : x′ ≠ 0) :
    schwarzian ((a * x + b) / (c * x + d)) = schwarzian x := by
  by_cases hc : c = 0
  · have had : a * d ≠ 0 := by simpa [hc] using hdet
    have ha0 : a ≠ 0 := left_ne_zero_of_mul had
    have hd0 : d ≠ 0 := right_ne_zero_of_mul had
    have hform : (a * x + b) / (c * x + d) = (a / d) * x + b / d := by
      rw [hc]
      field_simp [hd0]
      ring
    rw [hform]
    apply schwarzian_affine x (a / d) (b / d)
    · exact deriv_div_eq_zero a d ha hdder
    · exact deriv_div_eq_zero b d hb hdder
    · exact div_ne_zero ha0 hd0
    · exact hdx
  · let w : K := c * x + d
    let A : K := a / c
    let B : K := (b * c - a * d) / c
    have hw0 : w ≠ 0 := by simpa [w] using hden
    have hwder : w′ = c * x′ := by
      simp only [w, map_add, Derivation.leibniz, hcder, hdder, smul_eq_mul,
        mul_zero, add_zero]
    have hwder0 : w′ ≠ 0 := by
      rw [hwder]
      exact mul_ne_zero hc hdx
    have hAder : A′ = 0 := deriv_div_eq_zero a c ha hcder
    have hnumder : (b * c - a * d)′ = 0 := by
      simp only [map_sub, Derivation.leibniz, ha, hb, hcder, hdder,
        smul_eq_mul, mul_zero, add_zero, sub_self]
    have hBder : B′ = 0 :=
      deriv_div_eq_zero (b * c - a * d) c hnumder hcder
    have hB0 : B ≠ 0 := by
      apply div_ne_zero
      · intro hzero
        apply hdet
        linear_combination -hzero
      · exact hc
    have hwinvder0 : (w⁻¹)′ ≠ 0 := by
      rw [(Differential.deriv : Derivation ℤ K K).leibniz_inv]
      simp only [smul_eq_mul]
      exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (inv_ne_zero hw0))) hwder0
    have hform : (a * x + b) / (c * x + d) = A + B * w⁻¹ := by
      have hden' : x * c + d ≠ 0 := by simpa [mul_comm] using hden
      dsimp [A, B, w]
      field_simp [hc, hden']
      ring
    rw [hform, add_comm A]
    calc
      schwarzian (B * w⁻¹ + A) = schwarzian w⁻¹ :=
        schwarzian_affine w⁻¹ B A hBder hAder hB0 hwinvder0
      _ = schwarzian w := schwarzian_inv w hw0 hwder0
      _ = schwarzian x := schwarzian_affine x c d hcder hdder hc hdx

/-- A differential algebra homomorphism commutes with the Schwarzian. -/
theorem algHom_schwarzian
    {C K : Type*} [Field C] [Field K] [CharZero K] [Algebra C K] [Differential K]
    (phi : K →ₐ[C] K) (hphi : ∀ z : K, phi z′ = (phi z)′) (x : K) :
    phi (schwarzian x) = schwarzian (phi x) := by
  have h1 : phi x′ = (phi x)′ := hphi x
  have h2 : phi x′′ = (phi x)′′ := by
    rw [hphi x′, h1]
  have h3 : phi x′′′ = (phi x)′′′ := by
    rw [hphi x′′, h2]
  simp only [schwarzian, map_sub, map_div₀, map_mul, map_pow, map_ofNat]
  rw [h1, h2, h3]

/-- A projective semiconjugate of a differential endomorphism yields a fixed Schwarzian
observable. -/
theorem schwarzian_fixed_of_projective_semiconjugacy
    {C K : Type*} [Field C] [Field K] [CharZero K] [Algebra C K] [Differential K]
    (phi : K →ₐ[C] K) (hphi : ∀ z : K, phi z′ = (phi z)′)
    (u a b c d : K)
    (ha : a′ = 0) (hb : b′ = 0) (hcder : c′ = 0) (hdder : d′ = 0)
    (hdet : a * d - b * c ≠ 0) (hden : c * u + d ≠ 0) (hdu : u′ ≠ 0)
    (hsemi : phi u = (a * u + b) / (c * u + d)) :
    phi (schwarzian u) = schwarzian u := by
  rw [algHom_schwarzian phi hphi u, hsemi]
  exact schwarzian_mobius u a b c d ha hb hcder hdder hdet hden hdu

/-- The cleared differential polynomial for the equation `schwarzian x = c`. -/
def schwarzianRelation {C : Type*} [Field C] (c : C) :
    DifferentialPolynomial Unit C :=
  2 * MvPolynomial.X ((), 1) * MvPolynomial.X ((), 3) -
    3 * MvPolynomial.X ((), 2) ^ 2 -
    2 * MvPolynomial.C c * MvPolynomial.X ((), 1) ^ 2

theorem schwarzianRelation_ne_zero
    {C : Type*} [Field C] [CharZero C] (c : C) :
    schwarzianRelation c ≠ 0 := by
  classical
  intro hzero
  let f : Unit × ℕ → C := fun p =>
    if p.2 = 1 then 1 else if p.2 = 3 then c + 1 else 0
  have heval := congrArg (MvPolynomial.eval f) hzero
  simp [schwarzianRelation, f] at heval
  have htwo : (2 : C) = 0 := by linear_combination heval
  exact two_ne_zero htwo

@[simp]
theorem differentialPolynomialEval_schwarzianRelation
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (x : K) (c : C) :
    differentialPolynomialEval (C := C) (fun _ : Unit => x) (schwarzianRelation c) =
      2 * x′ * x′′′ - 3 * x′′ ^ 2 - 2 * algebraMap C K c * x′ ^ 2 := by
  simp [schwarzianRelation, differentialJet_succ, map_ofNat]

/-- The Schwarzian of a hypertranscendental scalar cannot collapse to a base constant. -/
theorem schwarzian_ne_constant_of_hypertranscendentalOver
    {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K]
    [Algebra C K] [Differential K]
    {x : K} (hx : HypertranscendentalOver C x) (c : C) :
    schwarzian x ≠ algebraMap C K c := by
  intro hconst
  have hind : DifferentialIndependent C (fun _ : Unit => x) :=
    (hypertranscendentalOver_iff_differentialIndependent_singleton C x).mp hx
  have hj : AlgebraicIndependent C
      (fun p : Unit × ℕ => differentialJet p.2 x) := hind
  have hdx : x′ ≠ 0 := by
    intro hzero
    have htr := hj.transcendental ((), 1)
    apply htr
    simpa [differentialJet_succ, hzero] using
      (isAlgebraic_zero : IsAlgebraic C (0 : K))
  have hcross :
      2 * x′ * x′′′ - 3 * x′′ ^ 2 - 2 * algebraMap C K c * x′ ^ 2 = 0 := by
    unfold schwarzian at hconst
    field_simp [hdx] at hconst
    linear_combination hconst
  have hrel : schwarzianRelation c ∈
      differentialRelationIdeal (C := C) (fun _ : Unit => x) := by
    rw [mem_differentialRelationIdeal_iff,
      differentialPolynomialEval_schwarzianRelation]
    exact hcross
  have hbot : differentialRelationIdeal (C := C) (fun _ : Unit => x) = ⊥ :=
    (differentialIndependent_iff_relationIdeal_eq_bot _).mp hind
  rw [hbot, Ideal.mem_bot] at hrel
  exact schwarzianRelation_ne_zero c hrel

end


end GaloisForLFunctions
