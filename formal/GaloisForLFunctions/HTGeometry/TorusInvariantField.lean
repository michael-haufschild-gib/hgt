import GaloisForLFunctions.HTGeometry.TorusVelocityField

/-!
# Scaling-invariant elements of a torus torsor

A freely generating palette is algebraically independent over the differential field of its
logarithmic derivatives, and the constant torus acts on the ambient field by rescaling the palette
while fixing that velocity field pointwise.  This file computes the invariants of a set of
rescalings.

The mechanism is a minimal-denominator argument.  An invariant element is a quotient of two
polynomials in the palette over the base; among all such presentations choose one whose denominator
has the fewest monomials.  Subtracting from the rescaled denominator the multiple of the original
denominator that matches its coefficient at one fixed exponent gives another denominator with fewer
monomials, hence zero, so the denominator is an eigenvector of every rescaling and every exponent
occurring in it has the same character as the fixed one.  The numerator inherits the same
eigenvalue.  If the acting set separates characters of exponent vectors, both are monomials with the
same exponent and the quotient lies in the base.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

section Poly

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Rescaling the variables of a multivariate polynomial by a family of scalars. -/
def scaleMvPolynomial (a : Fin r → R) (Q : MvPolynomial (Fin r) R) : MvPolynomial (Fin r) R :=
  ∑ e ∈ Q.support, MvPolynomial.monomial e ((∏ i, a i ^ e i) * MvPolynomial.coeff e Q)

/-- Rescaling multiplies the coefficient of an exponent vector by the corresponding monomial in the
scalars. -/
theorem coeff_scaleMvPolynomial (a : Fin r → R) (Q : MvPolynomial (Fin r) R) (e : Fin r →₀ ℕ) :
    MvPolynomial.coeff e (scaleMvPolynomial a Q)
      = (∏ i, a i ^ e i) * MvPolynomial.coeff e Q := by
  classical
  rw [scaleMvPolynomial, MvPolynomial.coeff_sum]
  by_cases he : e ∈ Q.support
  · rw [Finset.sum_eq_single e]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro f _ hfe
      rw [MvPolynomial.coeff_monomial, if_neg hfe]
    · intro h
      exact absurd he h
  · rw [MvPolynomial.notMem_support_iff.mp he, mul_zero]
    refine Finset.sum_eq_zero fun f hf ↦ ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    rintro rfl
    exact he hf

/-- Evaluating a rescaled polynomial is evaluating the original at the rescaled points. -/
theorem aeval_scaleMvPolynomial {A : Type*} [CommRing A] [Algebra R A] (a : Fin r → R)
    (f : Fin r → A) (Q : MvPolynomial (Fin r) R) :
    MvPolynomial.aeval f (scaleMvPolynomial a Q)
      = MvPolynomial.aeval (fun i ↦ algebraMap R A (a i) * f i) Q := by
  classical
  rw [scaleMvPolynomial, map_sum, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  have hsub : (∏ i, a i ^ e i) = ∏ i ∈ e.support, a i ^ e i :=
    (Finset.prod_subset (Finset.subset_univ e.support) fun i _ hi ↦ by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero]).symm
  rw [MvPolynomial.aeval_monomial, Finsupp.prod, hsub, map_mul, map_prod]
  simp only [map_pow, mul_pow, Finset.prod_mul_distrib]
  ring

end Poly

section Base

variable {C E : Type u} [Field C] [Field E] [Algebra C E] {r : ℕ}

/-- A scaling constant, viewed in an intermediate field. -/
def scaleBase (K : IntermediateField C E) (u : Fin r → Cˣ) (i : Fin r) : ↥K :=
  ⟨algebraMap C E ((u i : C)), K.algebraMap_mem _⟩

/-- The character of an exponent vector at a scaling vector, viewed in an intermediate field. -/
def scaleChar (K : IntermediateField C E) (u : Fin r → Cˣ) (e : Fin r →₀ ℕ) : ↥K :=
  ∏ i, scaleBase K u i ^ e i

theorem algebraMap_scaleBase (K : IntermediateField C E) (u : Fin r → Cˣ) (i : Fin r) :
    algebraMap (↥K) E (scaleBase K u i) = algebraMap C E ((u i : C)) := rfl

theorem algebraMap_scaleChar (K : IntermediateField C E) (u : Fin r → Cˣ) (e : Fin r →₀ ℕ) :
    algebraMap (↥K) E (scaleChar K u e) = algebraMap C E (∏ i, ((u i : C)) ^ e i) := by
  rw [scaleChar, map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [map_pow, map_pow, algebraMap_scaleBase]

/-- Two exponent vectors have the same character at a scaling vector exactly when the corresponding
monomials in the scaling constants agree. -/
theorem scaleChar_eq_iff (K : IntermediateField C E) (u : Fin r → Cˣ) (e d : Fin r →₀ ℕ) :
    scaleChar K u e = scaleChar K u d ↔
      (∏ i, ((u i : C)) ^ e i) = ∏ i, ((u i : C)) ^ d i := by
  constructor
  · intro h
    have := congrArg (algebraMap (↥K) E) h
    rw [algebraMap_scaleChar, algebraMap_scaleChar] at this
    exact (algebraMap C E).injective this
  · intro h
    apply (algebraMap (↥K) E).injective
    rw [algebraMap_scaleChar, algebraMap_scaleChar, h]

end Base

section Invariance

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E]

variable {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

section

variable (K : IntermediateField C E) {S : Set (Fin r → Cˣ)}

include hx hgen in
/-- Rescaling the palette rescales the variables of a polynomial with coefficients in a fixed
intermediate field. -/
theorem torusScaleEquiv_aeval (hKfix : ∀ u ∈ S, ∀ z ∈ K, torusScaleEquiv hx hgen u z = z)
    {u : Fin r → Cˣ} (hu : u ∈ S) (Q : MvPolynomial (Fin r) ↥K) :
    torusScaleEquiv hx hgen u (MvPolynomial.aeval x Q)
      = MvPolynomial.aeval x (scaleMvPolynomial (scaleBase K u) Q) := by
  classical
  rw [aeval_scaleMvPolynomial]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, map_sum, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [map_mul, map_prod]
  have hc : torusScaleEquiv hx hgen u (algebraMap (↥K) E (MvPolynomial.coeff e Q))
      = algebraMap (↥K) E (MvPolynomial.coeff e Q) :=
    hKfix u hu _ (MvPolynomial.coeff e Q).2
  rw [hc]
  refine congrArg _ (Finset.prod_congr rfl fun i _ ↦ ?_)
  rw [map_pow, torusScaleEquiv_apply, algebraMap_scaleBase]

end

include hx hgen in
/-- **Scaling invariants of a torus torsor.**  Let a set `S` of constant rescalings fix an
intermediate field `K` pointwise, let the palette be algebraically independent over `K`, and let `S`
separate the characters of exponent vectors.  Then every element of `K(x)` fixed by every rescaling
in `S` already lies in `K`. -/
theorem mem_of_torusScale_invariant (K : IntermediateField C E) {S : Set (Fin r → Cˣ)}
    (halg : AlgebraicIndependent (↥K) x)
    (hKfix : ∀ u ∈ S, ∀ z ∈ K, torusScaleEquiv hx hgen u z = z)
    (hsep : ∀ e d : Fin r →₀ ℕ,
      (∀ u ∈ S, (∏ i, ((u i : C)) ^ e i) = ∏ i, ((u i : C)) ^ d i) → e = d)
    {z : E} (hz : z ∈ IntermediateField.adjoin (↥K) (Set.range x))
    (hfix : ∀ u ∈ S, torusScaleEquiv hx hgen u z = z) :
    z ∈ K := by
  classical
  have hx0 : ∀ i, x i ≠ 0 := torus_palette_ne_zero hx
  have haeval0 : ∀ W : MvPolynomial (Fin r) ↥K, MvPolynomial.aeval x W = 0 → W = 0 :=
    algebraicIndependent_iff.mp halg
  by_cases hz0 : z = 0
  · rw [hz0]
    exact K.zero_mem
  obtain ⟨P₀, Q₀, hPQ⟩ := (IntermediateField.mem_adjoin_range_iff (↥K) x z).mp hz
  have hQ₀ : MvPolynomial.aeval x Q₀ ≠ 0 := by
    intro h
    rw [h, div_zero] at hPQ
    exact hz0 hPQ
  have hexists : ∃ n, ∃ P Q : MvPolynomial (Fin r) ↥K,
      Q ≠ 0 ∧ Q.support.card = n ∧ z * MvPolynomial.aeval x Q = MvPolynomial.aeval x P := by
    refine ⟨Q₀.support.card, P₀, Q₀, ?_, rfl, ?_⟩
    · intro h
      rw [h, map_zero] at hQ₀
      exact hQ₀ rfl
    · rw [hPQ, div_mul_cancel₀ _ hQ₀]
  obtain ⟨P, Q, hQne, hQcard, hPQeq⟩ := Nat.find_spec hexists
  have hmin : ∀ m, m < Nat.find hexists → ¬ ∃ P' Q' : MvPolynomial (Fin r) ↥K,
      Q' ≠ 0 ∧ Q'.support.card = m ∧ z * MvPolynomial.aeval x Q' = MvPolynomial.aeval x P' :=
    fun m hm ↦ Nat.find_min hexists hm
  -- a fixed exponent occurring in the minimal denominator
  have hQsupp : Q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hQne (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨d, hd⟩ := hQsupp
  -- the twisted difference of a polynomial against the fixed exponent
  set twist : (Fin r → Cˣ) → MvPolynomial (Fin r) ↥K → MvPolynomial (Fin r) ↥K :=
    fun u W ↦ scaleMvPolynomial (scaleBase K u) W - MvPolynomial.C (scaleChar K u d) * W with htwist
  have hcoeff_twist : ∀ (u : Fin r → Cˣ) (W : MvPolynomial (Fin r) ↥K) (e : Fin r →₀ ℕ),
      MvPolynomial.coeff e (twist u W)
        = (scaleChar K u e - scaleChar K u d) * MvPolynomial.coeff e W := by
    intro u W e
    rw [htwist]
    simp only [MvPolynomial.coeff_sub, coeff_scaleMvPolynomial, MvPolynomial.coeff_C_mul]
    rw [show (∏ i, scaleBase K u i ^ e i) = scaleChar K u e from rfl]
    ring
  have haeval_twist : ∀ (u : Fin r → Cˣ), u ∈ S → ∀ W : MvPolynomial (Fin r) ↥K,
      MvPolynomial.aeval x (twist u W)
        = torusScaleEquiv hx hgen u (MvPolynomial.aeval x W)
          - algebraMap (↥K) E (scaleChar K u d) * MvPolynomial.aeval x W := by
    intro u hu W
    rw [htwist, map_sub, map_mul, MvPolynomial.aeval_C,
      torusScaleEquiv_aeval hx hgen K hKfix hu W]
  -- the twisted denominator is again a denominator
  have hden : ∀ (u : Fin r → Cˣ), u ∈ S →
      z * MvPolynomial.aeval x (twist u Q) = MvPolynomial.aeval x (twist u P) := by
    intro u hu
    rw [haeval_twist u hu Q, haeval_twist u hu P, mul_sub]
    have h1 : z * torusScaleEquiv hx hgen u (MvPolynomial.aeval x Q)
        = torusScaleEquiv hx hgen u (MvPolynomial.aeval x P) := by
      rw [← hfix u hu, ← map_mul, hPQeq]
    have h2 : z * (algebraMap (↥K) E (scaleChar K u d) * MvPolynomial.aeval x Q)
        = algebraMap (↥K) E (scaleChar K u d) * MvPolynomial.aeval x P := by
      linear_combination (algebraMap (↥K) E (scaleChar K u d)) * hPQeq
    rw [h1, h2]
  -- the twisted denominator has strictly fewer monomials, hence vanishes
  have htwistQ : ∀ (u : Fin r → Cˣ), u ∈ S → twist u Q = 0 := by
    intro u hu
    by_contra hne
    have hsub : (twist u Q).support ⊆ Q.support.erase d := by
      intro e he
      rw [MvPolynomial.mem_support_iff, hcoeff_twist] at he
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · rintro rfl
        exact he (by rw [sub_self, zero_mul])
      · exact MvPolynomial.mem_support_iff.mpr fun h ↦ he (by rw [h, mul_zero])
    have hcard : (twist u Q).support.card < Nat.find hexists := by
      calc (twist u Q).support.card ≤ (Q.support.erase d).card := Finset.card_le_card hsub
        _ < Q.support.card := Finset.card_erase_lt_of_mem hd
        _ = Nat.find hexists := hQcard
    exact hmin _ hcard ⟨twist u P, twist u Q, hne, rfl, hden u hu⟩
  have htwistP : ∀ (u : Fin r → Cˣ), u ∈ S → twist u P = 0 := by
    intro u hu
    apply haeval0
    rw [← hden u hu, htwistQ u hu, map_zero, mul_zero]
  -- every exponent occurring in numerator or denominator equals the fixed one
  have hsingle : ∀ W : MvPolynomial (Fin r) ↥K, (∀ u ∈ S, twist u W = 0) →
      ∀ e ∈ W.support, e = d := by
    intro W hW e he
    refine hsep e d fun u hu ↦ ?_
    have hc := congrArg (MvPolynomial.coeff e) (hW u hu)
    rw [hcoeff_twist, MvPolynomial.coeff_zero] at hc
    rcases mul_eq_zero.mp hc with h | h
    · exact (scaleChar_eq_iff K u e d).mp (sub_eq_zero.mp h)
    · exact absurd h (MvPolynomial.mem_support_iff.mp he)
  have hQmono : Q = MvPolynomial.monomial d (MvPolynomial.coeff d Q) := by
    refine MvPolynomial.ext _ _ fun m ↦ ?_
    rw [MvPolynomial.coeff_monomial]
    by_cases hm : m = d
    · rw [if_pos hm.symm, hm]
    · rw [if_neg (fun h ↦ hm h.symm)]
      by_contra hc
      exact hm (hsingle Q htwistQ m (MvPolynomial.mem_support_iff.mpr hc))
  have hPmono : P = MvPolynomial.monomial d (MvPolynomial.coeff d P) := by
    refine MvPolynomial.ext _ _ fun m ↦ ?_
    rw [MvPolynomial.coeff_monomial]
    by_cases hm : m = d
    · rw [if_pos hm.symm, hm]
    · rw [if_neg (fun h ↦ hm h.symm)]
      by_contra hc
      exact hm (hsingle P htwistP m (MvPolynomial.mem_support_iff.mpr hc))
  -- read off the quotient
  set mon : E := ∏ i ∈ d.support, x i ^ d i with hmon
  have hmon0 : mon ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hx0 i)
  have hQval : MvPolynomial.aeval x Q = algebraMap (↥K) E (MvPolynomial.coeff d Q) * mon := by
    rw [hQmono, MvPolynomial.aeval_monomial, Finsupp.prod, ← hmon]
  have hPval : MvPolynomial.aeval x P = algebraMap (↥K) E (MvPolynomial.coeff d P) * mon := by
    rw [hPmono, MvPolynomial.aeval_monomial, Finsupp.prod, ← hmon]
  have hcQ : MvPolynomial.coeff d Q ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hcQ0 : algebraMap (↥K) E (MvPolynomial.coeff d Q) ≠ 0 := by
    simpa using hcQ
  rw [hQval, hPval] at hPQeq
  have hzeq : z = algebraMap (↥K) E (MvPolynomial.coeff d P / MvPolynomial.coeff d Q) := by
    rw [map_div₀]
    field_simp at hPQeq ⊢
    linear_combination hPQeq
  rw [hzeq]
  exact (MvPolynomial.coeff d P / MvPolynomial.coeff d Q).2

end Invariance

end

end GaloisForLFunctions.HTGeometry
