import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Nullstellensatz

/-!
# Finite multivariate Hermite interpolation by Chinese remainders

The maximal ideals of two distinct points of affine space over a field are distinct and hence
coprime.  Their arbitrary powers remain coprime, so the polynomial Chinese remainder theorem
simultaneously realizes arbitrary residue classes modulo arbitrary finite point-ideal powers.

This is the algebraic interpolation layer required by affine finite-jet packet arguments.  It is
genuinely multivariate: the local residue class modulo the `m`-th power of a point ideal records
the full Taylor packet of total order strictly below `m`.
-/

open Set Function

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Distinct affine points have distinct vanishing ideals. -/
theorem vanishingIdeal_singleton_ne_of_ne
    {K σ : Type*} [Field K] {x y : σ → K} (hxy : x ≠ y) :
    MvPolynomial.vanishingIdeal K {x} ≠
      MvPolynomial.vanishingIdeal K {y} := by
  intro hideal
  apply hxy
  funext i
  have hmem : MvPolynomial.X i - MvPolynomial.C (x i) ∈
      MvPolynomial.vanishingIdeal K {x} := by
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  rw [hideal, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hmem
  have hmem' : y i - x i = 0 := by
    simpa using hmem
  exact (sub_eq_zero.mp hmem').symm

/-- Arbitrary powers of the maximal ideals of two distinct affine points are coprime. -/
theorem isCoprime_pow_vanishingIdeal_singleton
    {K σ : Type*} [Field K] {x y : σ → K} (hxy : x ≠ y) (m n : ℕ) :
    IsCoprime
      (MvPolynomial.vanishingIdeal K {x} ^ m)
      (MvPolynomial.vanishingIdeal K {y} ^ n) := by
  exact (Ideal.isCoprime_of_isMaximal
    (vanishingIdeal_singleton_ne_of_ne hxy)).pow

/-- **Finite multivariate Hermite CRT.**  At finitely many pairwise distinct affine points, one
multivariable polynomial realizes every prescribed local polynomial class modulo an arbitrary
power of the corresponding point ideal. -/
theorem exists_mvPolynomial_sub_mem_pow_vanishingIdeal_singleton
    {K σ ι : Type*} [Field K] [Finite ι]
    (w : ι → σ → K) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → MvPolynomial σ K) :
    ∃ P : MvPolynomial σ K, ∀ i,
      P - target i ∈ MvPolynomial.vanishingIdeal K {w i} ^ m i := by
  let I : ι → Ideal (MvPolynomial σ K) := fun i =>
    MvPolynomial.vanishingIdeal K {w i} ^ m i
  have hI : Pairwise (IsCoprime on I) := by
    intro i j hij
    exact isCoprime_pow_vanishingIdeal_singleton (hw.ne hij) (m i) (m j)
  simpa only [I] using Ideal.exists_forall_sub_mem_ideal hI target

/-- The origin point ideal is exactly the ideal spanned by all variables. -/
theorem mem_idealOfVars_iff_eval_zero_eq_zero
    {K σ : Type*} [Field K] (P : MvPolynomial σ K) :
    P ∈ MvPolynomial.idealOfVars σ K ↔
      MvPolynomial.eval (fun _ => 0) P = 0 := by
  rw [show MvPolynomial.idealOfVars σ K =
      MvPolynomial.idealOfVars σ K ^ 1 by simp,
    MvPolynomial.mem_pow_idealOfVars_iff']
  rw [MvPolynomial.eval_zero']
  change (∀ x, Finsupp.degree x < 1 → P.coeff x = 0) ↔ P.coeff 0 = 0
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h x hx
    have hx0 : x = 0 := by
      rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hx
      exact hx
    simpa [hx0] using h

theorem idealOfVars_eq_vanishingIdeal_zero
    {K σ : Type*} [Field K] :
    MvPolynomial.idealOfVars σ K =
      MvPolynomial.vanishingIdeal K {(fun _ : σ => (0 : K))} := by
  ext P
  rw [mem_idealOfVars_iff_eval_zero_eq_zero,
    MvPolynomial.mem_vanishingIdeal_singleton_iff]
  simp only [MvPolynomial.aeval_eq_eval]

/-- Translation by a point carries its maximal ideal to the origin ideal. -/
theorem map_vanishingIdeal_singleton_mvPolynomialBaseTranslation
    {K σ : Type*} [Field K] (x : σ → K) :
    Ideal.map (mvPolynomialBaseTranslation x).toRingHom
        (MvPolynomial.vanishingIdeal K {x}) =
      MvPolynomial.idealOfVars σ K := by
  symm
  apply Ideal.IsMaximal.eq_of_le
    (show (MvPolynomial.idealOfVars σ K).IsMaximal by
      rw [idealOfVars_eq_vanishingIdeal_zero]
      infer_instance)
  · have hmax : (Ideal.map (mvPolynomialBaseTranslation x).toRingHom
        (MvPolynomial.vanishingIdeal K {x})).IsMaximal :=
      (Ideal.isMaximal_map_iff_of_bijective
        (mvPolynomialBaseTranslation x).toRingHom
        (mvPolynomialBaseTranslation x).bijective).2 inferInstance
    exact hmax.ne_top
  · rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : MvPolynomial.X i - MvPolynomial.C (x i) ∈
        MvPolynomial.vanishingIdeal K {x} := by
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    have himage := Ideal.mem_map_of_mem
      (mvPolynomialBaseTranslation x).toRingHom hmem
    simpa [mvPolynomialBaseTranslation] using himage

/-- Membership in a point-ideal power becomes membership in the total-degree origin filtration
after centering the variables at that point. -/
theorem mvPolynomialBaseTranslation_mem_idealOfVars_pow_of_mem_pointIdeal_pow
    {K σ : Type*} [Field K] (x : σ → K) {m : ℕ}
    {P : MvPolynomial σ K}
    (hP : P ∈ MvPolynomial.vanishingIdeal K {x} ^ m) :
    mvPolynomialBaseTranslation x P ∈ MvPolynomial.idealOfVars σ K ^ m := by
  have himage := Ideal.mem_map_of_mem
    (mvPolynomialBaseTranslation x).toRingHom hP
  rw [Ideal.map_pow,
    map_vanishingIdeal_singleton_mvPolynomialBaseTranslation] at himage
  exact himage

/-- Congruence modulo the `m`-th point-ideal power is equality of every centered coefficient of
total degree below `m`. -/
theorem coeff_mvPolynomialBaseTranslation_eq_of_sub_mem_pointIdeal_pow
    {K σ : Type*} [Field K] (x : σ → K) {m : ℕ}
    {P T : MvPolynomial σ K}
    (hPT : P - T ∈ MvPolynomial.vanishingIdeal K {x} ^ m)
    {a : σ →₀ ℕ} (ha : Finsupp.degree a < m) :
    (mvPolynomialBaseTranslation x P).coeff a =
      (mvPolynomialBaseTranslation x T).coeff a := by
  have htrans :=
    mvPolynomialBaseTranslation_mem_idealOfVars_pow_of_mem_pointIdeal_pow x hPT
  have hcoeff := (MvPolynomial.mem_pow_idealOfVars_iff' m _).mp htrans a ha
  rw [map_sub, MvPolynomial.coeff_sub] at hcoeff
  exact sub_eq_zero.mp hcoeff

/-- **Simultaneous finite multivariate Taylor interpolation.**  One polynomial matches every
centered Taylor coefficient, through the independently prescribed total order, at every point of
a finite injective packet. -/
theorem exists_mvPolynomial_centered_coeff_eq
    {K σ ι : Type*} [Field K] [Finite ι]
    (w : ι → σ → K) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → MvPolynomial σ K) :
    ∃ P : MvPolynomial σ K, ∀ i a, Finsupp.degree a < m i →
      (mvPolynomialBaseTranslation (w i) P).coeff a =
        (mvPolynomialBaseTranslation (w i) (target i)).coeff a := by
  obtain ⟨P, hP⟩ :=
    exists_mvPolynomial_sub_mem_pow_vanishingIdeal_singleton w hw m target
  exact ⟨P, fun i a ha =>
    coeff_mvPolynomialBaseTranslation_eq_of_sub_mem_pointIdeal_pow
      (w i) (hP i) ha⟩

/-- The polynomial with an arbitrarily specified finite total-degree coefficient packet. -/
def mvPolynomialOfFiniteJet
    {K σ : Type*} [CommSemiring K] [Finite σ]
    (m : ℕ) (jet : (σ →₀ ℕ) → K) : MvPolynomial σ K :=
  ∑ a ∈ (Finsupp.finite_of_degree_lt m).toFinset,
    MvPolynomial.monomial a (jet a)

theorem coeff_mvPolynomialOfFiniteJet
    {K σ : Type*} [CommSemiring K] [Finite σ]
    (m : ℕ) (jet : (σ →₀ ℕ) → K) {a : σ →₀ ℕ}
    (ha : Finsupp.degree a < m) :
    (mvPolynomialOfFiniteJet m jet).coeff a = jet a := by
  classical
  simp [mvPolynomialOfFiniteJet, MvPolynomial.coeff_sum, ha]

/-- **Arbitrary finite multivariate Hermite interpolation.**  At a finite injective packet of
points, every independently prescribed finite centered Taylor packet is realized by one
multivariable polynomial. -/
theorem exists_mvPolynomial_centered_coeff_eq_arbitrary
    {K σ ι : Type*} [Field K] [Finite σ] [Finite ι]
    (w : ι → σ → K) (hw : Function.Injective w)
    (m : ι → ℕ) (jet : ι → (σ →₀ ℕ) → K) :
    ∃ P : MvPolynomial σ K, ∀ i a, Finsupp.degree a < m i →
      (mvPolynomialBaseTranslation (w i) P).coeff a = jet i a := by
  let target : ι → MvPolynomial σ K := fun i =>
    (mvPolynomialBaseTranslation (w i)).symm
      (mvPolynomialOfFiniteJet (m i) (jet i))
  obtain ⟨P, hP⟩ := exists_mvPolynomial_centered_coeff_eq w hw m target
  refine ⟨P, fun i a ha => ?_⟩
  rw [hP i a ha]
  simp only [target, AlgEquiv.apply_symm_apply]
  exact coeff_mvPolynomialOfFiniteJet (m i) (jet i) ha

end

end GaloisForLFunctions.HTGeometry
