import GaloisForLFunctions.RHTower.DeningerRationalWittAICDomainComparison
import GaloisForLFunctions.RHTower.DeningerDynSysOmegaRing
import GaloisForLFunctions.RHTower.DeningerDynSysWittHomCharacters
import GaloisForLFunctions.RHTower.DeningerRationalWittNilpotentKernel

/-!
# `ω : ℤ̲A ≅ W_rat (A)` for an integrally closed domain with algebraically closed fraction field

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.1(b).

Over an integrally closed domain `A` whose fraction field is algebraically closed, the comparison
`ℤ[A ∖ 0] → W_rat (A)` sending the generator `(a)` to the Teichmüller element `[a]` is bijective:
a polynomial with constant term `1` has monic reverse, whose roots are integral over `A` and hence
lie in `A`, so the polynomial is a product `∏ (1 - α t)`.  As over a field, the comparison is
multiplicative because both sides are biadditive and `(a) · (b) = (a b)` matches `[a] ⊙ [b] = [a b]`.

Consequently the ring homomorphisms out of `W_rat (A)` are exactly the pointed multiplicative maps
`A → R`, which is the description of the `𝒪`-valued points used in §§3 and 13.
-/

namespace RHTower

noncomputable section

open scoped nonZeroDivisors

/-- Ring homomorphisms of a monoid algebra over `ℤ` are the monoid homomorphisms of the monoid. -/
def deningerIntMonoidAlgebraHomEquiv (M : Type*) [CommMonoid M] (R : Type*) [CommRing R] :
    (MonoidAlgebra ℤ M →+* R) ≃ (M →* R) where
  toFun φ := φ.toMonoidHom.comp (MonoidAlgebra.of ℤ M)
  invFun f := (MonoidAlgebra.lift ℤ R M f : MonoidAlgebra ℤ M →ₐ[ℤ] R).toRingHom
  left_inv φ := by
    refine MonoidAlgebra.ringHom_ext ?_ ?_
    · intro b
      have h1 : (MonoidAlgebra.single (1 : M) b : MonoidAlgebra ℤ M)
          = b • (1 : MonoidAlgebra ℤ M) := by
        rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [h1, map_zsmul, map_zsmul, map_one, map_one]
    · intro a
      show (MonoidAlgebra.lift ℤ R M (φ.toMonoidHom.comp (MonoidAlgebra.of ℤ M)))
        (MonoidAlgebra.single a (1 : ℤ)) = φ (MonoidAlgebra.single a (1 : ℤ))
      simp
  right_inv f := by
    refine MonoidHom.ext fun a => ?_
    show (MonoidAlgebra.lift ℤ R M f) (MonoidAlgebra.single a (1 : ℤ)) = f a
    simp

@[simp] theorem deningerIntMonoidAlgebraHomEquiv_apply (M : Type*) [CommMonoid M]
    (R : Type*) [CommRing R] (φ : MonoidAlgebra ℤ M →+* R) (a : M) :
    deningerIntMonoidAlgebraHomEquiv M R φ a = φ (MonoidAlgebra.single a (1 : ℤ)) := rfl

variable (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [IsAlgClosed (FractionRing A)]

/-- The additive comparison `ℤ[A ∖ 0] → W_rat (A)` landing in the canonical rational Witt ring. -/
def deningerOmegaDomainAddHom :
    MonoidAlgebra ℤ A⁰ →+ DeningerCanonicalRationalWittRing A where
  toFun x := ⟨deningerAICRationalWittComparison A x⟩
  map_zero' := by
    apply DeningerCanonicalRationalWittRing.ext
    show deningerAICRationalWittComparison A 0
      = (0 : DeningerCanonicalRationalWittRing A).additiveVal
    rw [map_zero]
    exact ((deningerCanonicalRationalWittValAddHom A).map_zero).symm
  map_add' x y := by
    apply DeningerCanonicalRationalWittRing.ext
    show deningerAICRationalWittComparison A (x + y)
      = (⟨deningerAICRationalWittComparison A x⟩
          + ⟨deningerAICRationalWittComparison A y⟩ :
            DeningerCanonicalRationalWittRing A).additiveVal
    rw [deningerCanonicalRationalWittRing_additiveVal_add]
    exact map_add (deningerAICRationalWittComparison A) x y

variable {A}

omit [IsIntegrallyClosed A] [IsAlgClosed (FractionRing A)] in
@[simp] theorem deningerOmegaDomainAddHom_apply (x : MonoidAlgebra ℤ A⁰) :
    (deningerOmegaDomainAddHom A x).additiveVal = deningerAICRationalWittComparison A x := rfl

omit [IsIntegrallyClosed A] [IsAlgClosed (FractionRing A)] in
@[simp] theorem deningerOmegaDomainAddHom_single (a : A⁰) (n : ℤ) :
    deningerOmegaDomainAddHom A (MonoidAlgebra.single a n)
      = n • deningerCanonicalRationalWittTeichmuller (a : A) := by
  apply DeningerCanonicalRationalWittRing.ext
  rw [deningerOmegaDomainAddHom_apply, deningerAICRationalWittComparison_single,
    deningerCanonicalRationalWittRing_additiveVal_zsmul]
  rfl

omit [IsIntegrallyClosed A] [IsAlgClosed (FractionRing A)] in
theorem deningerOmegaDomainAddHom_mul (x y : MonoidAlgebra ℤ A⁰) :
    deningerOmegaDomainAddHom A (x * y)
      = deningerOmegaDomainAddHom A x * deningerOmegaDomainAddHom A y := by
  classical
  have key : ∀ (b : A⁰) (n : ℤ) (z : MonoidAlgebra ℤ A⁰),
      deningerOmegaDomainAddHom A (z * MonoidAlgebra.single b n)
        = deningerOmegaDomainAddHom A z
          * deningerOmegaDomainAddHom A (MonoidAlgebra.single b n) := by
    intro b n
    have h1 : ((deningerOmegaDomainAddHom A).comp
          (AddMonoidHom.mulRight (MonoidAlgebra.single b n)))
        = (AddMonoidHom.mulRight (deningerOmegaDomainAddHom A (MonoidAlgebra.single b n))).comp
          (deningerOmegaDomainAddHom A) := by
      refine MonoidAlgebra.addMonoidHom_ext ?_
      intro a m
      show deningerOmegaDomainAddHom A (MonoidAlgebra.single a m * MonoidAlgebra.single b n)
        = deningerOmegaDomainAddHom A (MonoidAlgebra.single a m) *
          deningerOmegaDomainAddHom A (MonoidAlgebra.single b n)
      rw [MonoidAlgebra.single_mul_single, deningerOmegaDomainAddHom_single,
        deningerOmegaDomainAddHom_single, deningerOmegaDomainAddHom_single, smul_mul_smul_comm,
        deningerCanonicalRationalWittTeichmuller_mul, Submonoid.coe_mul]
    intro z
    exact congrArg
      (fun F : MonoidAlgebra ℤ A⁰ →+ DeningerCanonicalRationalWittRing A => F z) h1
  have h2 : ((deningerOmegaDomainAddHom A).comp (AddMonoidHom.mulLeft x))
      = (AddMonoidHom.mulLeft (deningerOmegaDomainAddHom A x)).comp
        (deningerOmegaDomainAddHom A) := by
    refine MonoidAlgebra.addMonoidHom_ext ?_
    intro b n
    exact key b n x
  exact congrArg (fun F : MonoidAlgebra ℤ A⁰ →+ DeningerCanonicalRationalWittRing A => F y) h2

variable (A)

/-- **Deninger, Proposition 1.1(b).**  Over an integrally closed domain with algebraically closed
fraction field the comparison `ω : ℤ̲A → W_rat (A)` is a ring isomorphism. -/
def deningerOmegaDomainRingEquiv :
    MonoidAlgebra ℤ A⁰ ≃+* DeningerCanonicalRationalWittRing A where
  toFun := deningerOmegaDomainAddHom A
  invFun w := (deningerAICRationalWittComparisonEquiv A).symm w.additiveVal
  left_inv x := (deningerAICRationalWittComparisonEquiv A).symm_apply_apply x
  right_inv w := by
    apply DeningerCanonicalRationalWittRing.ext
    exact (deningerAICRationalWittComparisonEquiv A).apply_symm_apply w.additiveVal
  map_add' := map_add (deningerOmegaDomainAddHom A)
  map_mul' := deningerOmegaDomainAddHom_mul

variable {A}

@[simp] theorem deningerOmegaDomainRingEquiv_single (a : A⁰) (n : ℤ) :
    deningerOmegaDomainRingEquiv A (MonoidAlgebra.single a n)
      = n • deningerCanonicalRationalWittTeichmuller (a : A) :=
  deningerOmegaDomainAddHom_single a n

/-! ### Homomorphisms out of `W_rat (A)` -/

open Classical in
/-- For a domain, monoid homomorphisms of the nonzero elements are the pointed multiplicative maps
of the whole ring. -/
def deningerNonZeroHomEquivPointed (R : Type*) [CommRing R] :
    (A⁰ →* R) ≃ (A →*₀ R) where
  toFun f :=
    { toFun := fun a => if h : a = 0 then 0 else f ⟨a, mem_nonZeroDivisors_of_ne_zero h⟩
      map_zero' := dif_pos rfl
      map_one' := by
        rw [dif_neg (one_ne_zero (α := A))]
        have : (⟨(1 : A), mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩ : A⁰) = 1 := rfl
        rw [this, map_one]
      map_mul' := by
        intro a b
        by_cases ha : a = 0
        · subst ha; simp
        by_cases hb : b = 0
        · subst hb; simp
        rw [dif_neg ha, dif_neg hb, dif_neg (mul_ne_zero ha hb)]
        have : (⟨a * b, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero ha hb)⟩ : A⁰)
            = ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ * ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ :=
          rfl
        rw [this, map_mul] }
  invFun P :=
    { toFun := fun a => P (a : A)
      map_one' := by
        show P ((1 : A⁰) : A) = 1
        rw [show ((1 : A⁰) : A) = 1 from rfl, map_one]
      map_mul' := by
        intro a b
        show P ((a * b : A⁰) : A) = P (a : A) * P (b : A)
        rw [Submonoid.coe_mul, map_mul] }
  left_inv f := by
    refine MonoidHom.ext fun a => ?_
    have ha : (a : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 a.2
    show (if h : (a : A) = 0 then 0 else f ⟨(a : A), mem_nonZeroDivisors_of_ne_zero h⟩) = f a
    rw [dif_neg ha]
  right_inv P := by
    refine MonoidWithZeroHom.ext fun a => ?_
    by_cases ha : a = 0
    · subst ha
      show (if h : (0 : A) = 0 then 0 else _) = P 0
      rw [dif_pos rfl, map_zero]
    · show (if h : a = 0 then 0 else P ((⟨a, mem_nonZeroDivisors_of_ne_zero h⟩ : A⁰) : A)) = P a
      rw [dif_neg ha]

omit [IsIntegrallyClosed A] [IsAlgClosed (FractionRing A)] in
@[simp] theorem deningerNonZeroHomEquivPointed_apply_of_ne {R : Type*} [CommRing R]
    (f : A⁰ →* R) {a : A} (ha : a ≠ 0) :
    deningerNonZeroHomEquivPointed R f a = f ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ := by
  classical
  exact dif_neg ha

variable (A)

/-- **Deninger, Proposition 1.1(b), the form used for the valued points.**  Over an integrally
closed domain with algebraically closed fraction field the ring homomorphisms out of `W_rat (A)`
are exactly the pointed multiplicative maps of `A`. -/
def deningerWittRingHomEquivPointed (R : Type*) [CommRing R] :
    (DeningerCanonicalRationalWittRing A →+* R) ≃ (A →*₀ R) :=
  ((deningerPrecompRingHomEquiv (deningerOmegaDomainRingEquiv A) R).trans
    (deningerIntMonoidAlgebraHomEquiv A⁰ R)).trans (deningerNonZeroHomEquivPointed R)

variable {A}

omit [IsDomain A] [IsIntegrallyClosed A] [IsAlgClosed (FractionRing A)] in
theorem deningerCanonicalRationalWittTeichmuller_zero :
    deningerCanonicalRationalWittTeichmuller (0 : A)
      = (0 : DeningerCanonicalRationalWittRing A) := by
  apply DeningerCanonicalRationalWittRing.ext
  show Additive.ofMul (deningerRationalWittTeichmuller (0 : A))
    = (0 : DeningerCanonicalRationalWittRing A).additiveVal
  rw [deningerRationalWittTeichmuller_zero]
  exact ((deningerCanonicalRationalWittValAddHom A).map_zero).symm

@[simp] theorem deningerWittRingHomEquivPointed_apply (R : Type*) [CommRing R]
    (φ : DeningerCanonicalRationalWittRing A →+* R) (a : A) :
    deningerWittRingHomEquivPointed A R φ a
      = φ (deningerCanonicalRationalWittTeichmuller a) := by
  classical
  have hdef : deningerWittRingHomEquivPointed A R φ
      = deningerNonZeroHomEquivPointed R
        (deningerIntMonoidAlgebraHomEquiv A⁰ R
          (φ.comp (deningerOmegaDomainRingEquiv A).toRingHom)) := rfl
  rw [hdef]
  by_cases ha : a = 0
  · subst ha
    rw [map_zero, deningerCanonicalRationalWittTeichmuller_zero, map_zero]
  · rw [deningerNonZeroHomEquivPointed_apply_of_ne _ ha,
      deningerIntMonoidAlgebraHomEquiv_apply]
    show φ (deningerOmegaDomainRingEquiv A
      (MonoidAlgebra.single (⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ : A⁰) (1 : ℤ))) = _
    rw [deningerOmegaDomainRingEquiv_single, one_smul]

end

end RHTower
