import GaloisForLFunctions.HTGeometry.PolynomialTwistedCech

/-! Polynomial localization embeds in the Laurent ring over any commutative base ring. -/

noncomputable section

open HTGeometry MvPolynomial AddMonoidAlgebra GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.SchemeCohomology.RingPolynomialCech

universe u

variable {K : Type u} [CommRing K] {ι ν : Type}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable (K ι ν) in
/-- The grading of `T` by the degree in the projective coordinates. -/
abbrev projGrading : ℕ → Submodule K (MvPolynomial (ι ⊕ ν) K) :=
  weightedHomogeneousSubmodule K (projWeight ι ν)

variable (K ι ν) in
/-- The projective coordinates. -/
noncomputable def projCoord : ι → MvPolynomial (ι ⊕ ν) K := fun i => X (Sum.inl i)

theorem projCoord_mem (i : ι) : projCoord K ι ν i ∈ projGrading K ι ν 1 :=
  isWeightedHomogeneous_X K (projWeight ι ν) (Sum.inl i)

variable (K ι ν) in
/-- Laurent polynomials with arbitrary commutative coefficients. -/
abbrev LaurentRing := AddMonoidAlgebra K (LaurentExp ι ν)

variable (K ι ν) in
/-- **The embedding of polynomials into Laurent polynomials.** -/
noncomputable def laurentEmb : MvPolynomial (ι ⊕ ν) K →+* LaurentRing K ι ν :=
  AddMonoidAlgebra.mapDomainRingHom K (castExp ι ν)

theorem laurentEmb_injective : Function.Injective (laurentEmb K ι ν) := by
  intro x y h
  apply AddMonoidAlgebra.ext
  have h' := congrArg AddMonoidAlgebra.coeff h
  simp only [laurentEmb, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain] at h'
  exact Finsupp.mapDomain_injective castExp_injective h'

theorem support_laurentEmb [DecidableEq ι] [DecidableEq ν] (x : MvPolynomial (ι ⊕ ν) K) :
    (laurentEmb K ι ν x).coeff.support = x.support.image (castExp ι ν) := by
  classical
  simp only [laurentEmb, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_support_of_injective castExp_injective _

theorem laurentEmb_monomial (b : ι ⊕ ν →₀ ℕ) (c : K) :
    laurentEmb K ι ν (monomial b c) = AddMonoidAlgebra.single (castExp ι ν b) c := by
  simp only [laurentEmb, AddMonoidAlgebra.mapDomainRingHom_apply, MvPolynomial.monomial,
    AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.mapDomain_single]

theorem laurentEmb_wProd [DecidableEq ι] (s : Finset ι) :
    laurentEmb K ι ν (wProd (projCoord K ι ν) s) = AddMonoidAlgebra.single (sExp s) 1 := by
  induction s using Finset.induction_on with
  | empty =>
    rw [wProd, Finset.prod_empty, map_one, sExp, Finset.sum_empty, AddMonoidAlgebra.one_def]
  | insert a s ha ih =>
    rw [wProd, Finset.prod_insert ha, map_mul, ← wProd, ih,
      show sExp (ν := ν) (insert a s) = Finsupp.single (Sum.inl a) 1 + sExp s by
        rw [sExp, Finset.sum_insert ha, ← sExp],
      projCoord, MvPolynomial.X, laurentEmb_monomial, castExp_single,
      AddMonoidAlgebra.single_mul_single, one_mul]
    rfl

theorem single_mul_single_neg (a : LaurentExp ι ν) :
    AddMonoidAlgebra.single a (1 : K) * AddMonoidAlgebra.single (-a) 1 = 1 := by
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul, AddMonoidAlgebra.one_def]

theorem isUnit_laurentEmb_wProd [DecidableEq ι] (s : Finset ι) :
    IsUnit (laurentEmb K ι ν (wProd (projCoord K ι ν) s)) := by
  rw [laurentEmb_wProd]
  exact ⟨⟨_, _, single_mul_single_neg _, by rw [mul_comm]; exact single_mul_single_neg _⟩, rfl⟩

/-! ## Embedding the localizations -/

section Loc

variable [DecidableEq ι]

variable (K ι ν) in
/-- **The embedding of `T[w_s⁻¹]` into the Laurent ring.** -/
noncomputable def laurentLoc (s : Finset ι) : LocAt (projCoord K ι ν) s →+* LaurentRing K ι ν :=
  IsLocalization.Away.lift (wProd (projCoord K ι ν) s) (isUnit_laurentEmb_wProd s)

theorem laurentLoc_algebraMap (s : Finset ι) (x : MvPolynomial (ι ⊕ ν) K) :
    laurentLoc K ι ν s (algebraMap _ (LocAt (projCoord K ι ν) s) x) = laurentEmb K ι ν x :=
  IsLocalization.lift_eq _ x

theorem laurentLoc_resLoc {s t : Finset ι} (h : s ⊆ t) (y : LocAt (projCoord K ι ν) s) :
    laurentLoc K ι ν t (resLoc (projCoord K ι ν) h y) = laurentLoc K ι ν s y := by
  have : (laurentLoc K ι ν t).comp (resLoc (projCoord K ι ν) h) = laurentLoc K ι ν s :=
    IsLocalization.ringHom_ext (Submonoid.powers (wProd (projCoord K ι ν) s)) (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, resLoc_algebraMap, laurentLoc_algebraMap])
  exact DFunLike.congr_fun this y

/-- **The Laurent expansion of a fraction.** -/
theorem laurentLoc_frac (s : Finset ι) (m : ℕ) (x : MvPolynomial (ι ⊕ ν) K) :
    laurentLoc K ι ν s (frac (projCoord K ι ν) s m x)
      = laurentEmb K ι ν x * AddMonoidAlgebra.single (-(m • sExp s)) 1 := by
  rw [frac, Localization.mk_eq_mk']
  simp only [laurentLoc, IsLocalization.Away.lift]
  rw [IsLocalization.lift_mk'_spec]
  change laurentEmb K ι ν x = laurentEmb K ι ν (wProd (projCoord K ι ν) s ^ m)
    * (laurentEmb K ι ν x * AddMonoidAlgebra.single (-(m • sExp s)) 1)
  rw [map_pow, laurentEmb_wProd, AddMonoidAlgebra.single_pow, one_pow, mul_left_comm,
    single_mul_single_neg, mul_one]

/-- **The embedding of the localization is injective.** -/
theorem laurentLoc_injective (s : Finset ι) : Function.Injective (laurentLoc K ι ν s) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨⟨x, ⟨_, m, rfl⟩⟩, hxy⟩ :=
    IsLocalization.surj (Submonoid.powers (wProd (projCoord K ι ν) s)) y
  simp only at hxy
  have hx : laurentEmb K ι ν x = 0 := by
    rw [← laurentLoc_algebraMap s x, ← hxy, map_mul, hy, zero_mul]
  have hx0 : x = 0 := (map_eq_zero_iff _ laurentEmb_injective).mp hx
  rw [hx0, map_zero] at hxy
  have hu : IsUnit (algebraMap _ (LocAt (projCoord K ι ν) s) (wProd (projCoord K ι ν) s ^ m)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow m
  exact (hu.mul_left_eq_zero).mp hxy

end Loc

end GlobalTheory.SchemeCohomology.RingPolynomialCech
