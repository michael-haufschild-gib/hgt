import GaloisForLFunctions.HTGeometry.AffineDomainRationalPointCut
import GaloisForLFunctions.HTGeometry.IntegralExtensionKrullDim
import GaloisForLFunctions.HTGeometry.PointsSeparate
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial

/-! Dimension on nonempty smooth affine opens over an algebraically closed
field, and dominance of finite morphisms to affine space of equal dimension. -/

noncomputable section

open AlgebraicGeometry CategoryTheory GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

private theorem krullDim_etale_polynomial (K B : Type) [Field K] [IsAlgClosed K] [CommRing B]
    [Nontrivial B] (d : ℕ) [Algebra (MvPolynomial (Fin d) K) B]
    [Algebra.Etale (MvPolynomial (Fin d) K) B] : ringKrullDim B = d := by
  let A := MvPolynomial (Fin d) K
  have hA : ringKrullDim A = d := by
    simp [A, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  apply le_antisymm
  · rw [← hA]
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) fun p q hpq => ?_
    refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) fun h => hpq.ne ?_
    exact PrimeSpectrum.ext
      (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) _ _ hpq.le (congrArg PrimeSpectrum.asIdeal h))
  · letI : Algebra K B := ((algebraMap A B).comp (algebraMap K A)).toAlgebra
    letI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.FiniteType K B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
    letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
    obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    letI := hm
    let p := m.under A
    obtain ⟨χ, hχ⟩ := exists_algHom_ker_eq_of_isMaximal (C := K) m
    let ψ : A →ₐ[K] K := χ.comp (IsScalarTower.toAlgHom K A B)
    let a (j : Fin d) := ψ (MvPolynomial.X j)
    have he : MvPolynomial.aeval a = ψ := MvPolynomial.algHom_ext fun j =>
      MvPolynomial.aeval_X a j
    have hp : (partialEvalSeries a).last.asIdeal = p := by
      rw [partialEvalSeries_last, he]
      exact SetLike.ext fun x => RingHom.mem_ker.trans (hχ (algebraMap A B x))
    have hbase : (d : ℕ∞) ≤ p.height := by
      rw [← hp, PrimeSpectrum.height_eq_orderHeight]
      exact Order.length_le_height_last (p := partialEvalSeries a)
    have hle : p.height ≤ m.height := by
      rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p m]
      exact le_self_add
    exact (WithBot.coe_le_coe.mpr (hbase.trans hle)).trans Ideal.height_le_ringKrullDim_of_isPrime

private theorem krullDim_standardSmooth {K B : Type} [Field K] [IsAlgClosed K] [CommRing B]
    [Nontrivial B] {d : ℕ} {f : K →+* B} (hf : f.IsStandardSmoothOfRelativeDimension d) :
    ringKrullDim B = d := by
  obtain ⟨g, -, hg⟩ := hf.exists_etale_mvPolynomial
  algebraize [g]
  exact krullDim_etale_polynomial K B d

private theorem krullDim_of_basicOpen_cover {A : Type} [CommRing A] [Nontrivial A]
    (S : Set A) (hS : Ideal.span S = ⊤) (d : WithBot ℕ∞)
    (h : ∀ x ∈ S, Nontrivial (Localization.Away x) → ringKrullDim (Localization.Away x) = d) :
    ringKrullDim A = d := by
  have hk (p : Ideal A) (hp : p.IsPrime) : ∃ x : A, Disjoint (Submonoid.powers x : Set A) p ∧
      ringKrullDim (Localization.Away x) = d := by
    obtain ⟨x, hx, hx'⟩ : ∃ x ∈ S, x ∉ p := by
      by_contra! hle
      exact hp.ne_top (top_le_iff.mp (hS ▸ Ideal.span_le.mpr hle))
    have hd : Disjoint (Submonoid.powers x : Set A) (p : Set A) :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hx'
    have hq := IsLocalization.isPrime_of_isPrime_disjoint (.powers x) (Localization.Away x) _ hp hd
    refine ⟨x, hd, h x hx ?_⟩
    by_contra hzero
    rw [not_nontrivial_iff_subsingleton] at hzero
    exact hq.ne_top (Subsingleton.elim _ _)
  apply le_antisymm
  · apply (ringKrullDim_le_iff_height_le d).mpr
    intro p hp
    obtain ⟨x, hd, hx⟩ := hk p hp
    have hq := IsLocalization.isPrime_of_isPrime_disjoint (.powers x) (Localization.Away x) _ hp hd
    rw [← IsLocalization.height_map_of_disjoint (S := Localization.Away x) _ p hd, ← hx]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  · obtain ⟨p, hp⟩ := Ideal.exists_maximal A
    obtain ⟨x, -, hx⟩ := hk p hp.isPrime
    rw [← hx]
    apply (ringKrullDim_le_iff_height_le _).mpr
    intro q hq
    rw [← IsLocalization.height_under (R := A) (.powers x) q]
    exact Ideal.height_le_ringKrullDim_of_isPrime

/-- A nonempty affine open in a smooth scheme of relative dimension d has
Krull dimension d. -/
theorem ringKrullDim_smooth_affineOpen {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (s : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d s]
    {U : X.Opens} (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) : ringKrullDim Γ(X, U) = d := by
  letI : Nonempty U := hne.to_subtype
  obtain ⟨S, hS, hstd⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension d) s inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  refine krullDim_of_basicOpen_cover S hS d fun x hx hnon => ?_
  letI := hnon
  exact krullDim_standardSmooth
    (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _ e (hstd x hx))

/-- A finite map from a polynomial ring in d variables to a ring of
dimension d is injective. -/
theorem finite_polynomial_injective_of_krullDim {K B σ : Type} [Field K] [CommRing B] [Fintype σ]
    (φ : MvPolynomial σ K →+* B) (hφ : φ.Finite) (hB : ringKrullDim B = Fintype.card σ) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  let A := MvPolynomial σ K
  let ψ := RingHom.kerLift φ
  letI : Algebra (A ⧸ RingHom.ker φ) B := ψ.toAlgebra
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (show (ψ.comp (Ideal.Quotient.mk _)).Finite from hφ)
  letI : Algebra.IsIntegral (A ⧸ RingHom.ker φ) B := ⟨hψ.to_isIntegral⟩
  have hD : ringKrullDim (A ⧸ RingHom.ker φ) = ringKrullDim B :=
    ringKrullDim_eq_of_isIntegral _ _ ((RingHom.injective_iff_ker_eq_bot ψ).mp (RingHom.kerLift_injective φ))
  have hm : Ideal.span {x} ≤ RingHom.ker φ := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hq : ringKrullDim (A ⧸ RingHom.ker φ) ≤ ringKrullDim (A ⧸ Ideal.span {x}) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hm)
  have hc := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  rw [hD, hB] at hq
  have h := (add_le_add hq (le_rfl : (1 : WithBot ℕ∞) ≤ 1)).trans hc
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
  simp only [Nat.card_eq_fintype_card, zero_add] at h
  norm_cast at h
  omega

end GlobalTheory.SchemeCohomology
