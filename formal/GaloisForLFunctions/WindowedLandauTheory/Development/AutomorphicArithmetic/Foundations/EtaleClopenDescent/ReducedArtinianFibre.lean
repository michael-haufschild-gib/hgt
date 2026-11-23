import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineRationalPoints
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsFinite
import GaloisForLFunctions.HTGeometry.PointsSeparate
import Mathlib.RingTheory.Artinian.Ring

/-! A finite fibre over an algebraically closed field is reduced when its
defining functions generate the cotangent space at each of its points. -/

open AlgebraicGeometry CategoryTheory GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

/-- The zero fibre of a finite algebra over a polynomial ring is finite
over the coefficient field. -/
theorem finite_quotient_of_polynomial_coordinates {K B σ : Type*} [Field K] [CommRing B]
    [Algebra K B] (φ : MvPolynomial σ K →ₐ[K] B) (hφ : φ.Finite) :
    Module.Finite K (B ⧸ Ideal.span (Set.range fun i => φ (MvPolynomial.X i))) := by
  let I := Ideal.span (Set.range fun i => φ (MvPolynomial.X i))
  let q := Ideal.Quotient.mkₐ K I
  let c := Algebra.ofId K (B ⧸ I)
  let ev : MvPolynomial σ K →ₐ[K] K := MvPolynomial.aeval (fun _ => 0)
  have hq : q.Finite := AlgHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have h : q.comp φ = c.comp ev := by
    apply MvPolynomial.algHom_ext
    intro i
    have hzero : q (φ (MvPolynomial.X i)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
    change q (φ (MvPolynomial.X i)) = c (ev (MvPolynomial.X i))
    rw [hzero, show ev (MvPolynomial.X i) = 0 by simp [ev], map_zero]
  have hfin : c.Finite := AlgHom.Finite.of_comp_finite (h ▸ hq.comp hφ)
  exact (RingHom.finite_algebraMap).mp hfin

private theorem quotient_maximal_le_sq {A : Type*} [CommRing A] (I : Ideal A)
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2)
    (M : Ideal (A ⧸ I)) (hM : M.IsMaximal) : M ≤ M ^ 2 := by
  let f := Ideal.Quotient.mk I
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  let m := M.comap f
  letI := hM
  have hm : m.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have hIm : I ≤ m := fun x hx => by
    change f x ∈ M
    rw [show f x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact M.zero_mem
  have e := Ideal.map_mono (f := f) (h m hm hIm)
  change m.map (Ideal.Quotient.mk I) ≤ (I ⊔ m ^ 2).map (Ideal.Quotient.mk I) at e
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_quotient_self, bot_sup_eq,
    show m.map f = M from Ideal.map_comap_of_surjective f hsurj _] at e
  exact e

private theorem pow_eq_self_of_le_sq {R : Type*} [CommRing R] (M : Ideal R) (h : M ≤ M ^ 2)
    (k : ℕ) : M ^ (k + 1) = M := by
  have e : M * M = M := by
    rw [← sq]
    exact le_antisymm (Ideal.pow_le_self two_ne_zero) h
  induction k with
  | zero => exact pow_one M
  | succ k ih => rw [pow_succ, ih, e]

/-- A quotient of finite length with zero cotangent space at each maximal
ideal is reduced. -/
theorem isReduced_of_artinian_quotient {A : Type*} [CommRing A] (I : Ideal A)
    [IsArtinianRing (A ⧸ I)]
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) : IsReduced (A ⧸ I) := by
  let R := A ⧸ I
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
  have he : nilradical R ^ (k + 1) = nilradical R := by
    rw [IsArtinianRing.nilradical_pow_eq_iInf, IsArtinianRing.nilradical_eq_iInf]
    exact congrArg iInf (funext fun M : MaximalSpectrum R =>
      pow_eq_self_of_le_sq _ (quotient_maximal_le_sq I h _ M.isMaximal) k)
  have hz : nilradical R ^ (k + 1) = ⊥ := by
    rw [pow_succ, hk, zero_mul]
    rfl
  have hbot := he.symm.trans hz
  refine ⟨fun x hx => ?_⟩
  have hx' : x ∈ nilradical R := mem_nilradical.mpr hx
  rwa [hbot, Ideal.mem_bot] at hx'

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
  {s : X ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType s] {U : X.Opens}

/-- On an affine chart over an algebraically closed field, each maximal
ideal cuts out a rational point. -/
theorem exists_affinePoint_ker (hU : IsAffineOpen U) (m : Ideal (SectionRing s U)) [m.IsMaximal] :
    ∃ y : {y : X.BaseFieldPointOver K s // y.hom default ∈ U},
      RingHom.ker (affinePointEval y.1 y.2).toRingHom = m := by
  letI := sectionRing_finiteType s hU
  obtain ⟨e, he⟩ := exists_algHom_ker_eq_of_isMaximal (C := K) m
  obtain ⟨y, hy⟩ := (affinePointEquiv hU).surjective e
  refine ⟨y, ?_⟩
  have hy' : affinePointEval y.1 y.2 = e := hy
  rw [hy']
  exact SetLike.ext fun x => RingHom.mem_ker.trans (he x)

end GlobalTheory.SchemeCohomology
