import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginFibreSpecialization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalKaehlerBasis
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ChartLocalAlgebra
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.LocalRing

/-! At a point of the reduced origin fibre, the normalized chart is
étale over its polynomial chart. The coordinate differentials thus
give a basis over the point-local ring. -/

noncomputable section

open KaehlerDifferential GaloisForLFunctions.HTGeometry
open GlobalTheory.WH

namespace GlobalTheory.PD

private theorem isUnramifiedAt_of_reduced_finite_fibre {k A B : Type} [Field k] [CharZero k]
    [CommRing A] [CommRing B] [Algebra A B] [Algebra k A] [Module.Finite A B]
    (p : Ideal A) [p.IsMaximal] [IsReduced (B ⧸ p.map (algebraMap A B))]
    (q : Ideal B) [q.IsPrime] [q.LiesOver p] : Algebra.IsUnramifiedAt A q := by
  let J := p.map (algebraMap A B)
  have hJ : J.IsRadical := (Ideal.isRadical_iff_quotient_reduced J).mpr inferInstance
  letI := Localization.AtPrime.algebraOfLiesOver p q
  letI : CharZero p.ResidueField := charZero_of_injective_algebraMap (algebraMap k p.ResidueField).injective
  rw [Algebra.isUnramifiedAt_iff_map_eq A p q]
  refine ⟨inferInstance, ?_⟩
  have hle : J ≤ q := Ideal.map_le_iff_le_comap.mpr (q.over_def p).le
  have hmin : q ∈ J.minimalPrimes := by
    refine ⟨⟨inferInstance, hle⟩, fun q' hq' hq'q => ?_⟩
    letI : q'.IsPrime := hq'.1
    have hpq : p ≤ q'.comap (algebraMap A B) := Ideal.map_le_iff_le_comap.mp hq'.2
    have hsame := (inferInstance : p.IsMaximal).eq_of_le (Ideal.comap_ne_top _ hq'.1.ne_top) hpq
    have hm := Ideal.IsIntegral.isMaximal_of_isMaximal_comap q'
      (hsame ▸ (inferInstance : p.IsMaximal))
    exact (hm.eq_of_le (inferInstance : q.IsPrime).ne_top hq'q).ge
  have he := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes q J hmin
    (A := Localization.AtPrime q)
  rw [← IsLocalization.map_radical q.primeCompl (Localization.AtPrime q), hJ.radical] at he
  rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime q), ← Ideal.map_map]
  exact he.trans (IsLocalization.AtPrime.map_eq_maximalIdeal q _)

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

local notation "A" => rA k x {0}
local notation "B" => rB k E x {0}

/-- The polynomial chart is formally étale into the normalized chart
localized at any rational point of its reduced origin fibre. -/
theorem IsFinCover.isEtaleAt_originFibre (h : IsFinCover k E x)
    [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)] (e : OriginFibrePoint k E x) :
    letI : Algebra A B := (integralClosure A E).algebra
    letI : (RingHom.ker e.1.toRingHom).IsPrime := (algebraPointKernel_isMaximal e.1).isPrime
    Algebra.IsEtaleAt A (RingHom.ker e.1.toRingHom) := by
  letI : Algebra A B := (integralClosure A E).algebra
  let p : Ideal A := RingHom.ker (originEval h.pd).toRingHom
  let q : Ideal B := RingHom.ker e.1.toRingHom
  letI : p.IsMaximal := algebraPointKernel_isMaximal (originEval h.pd)
  letI : q.IsMaximal := algebraPointKernel_isMaximal e.1
  letI : Module.Finite A B := (h.finiteProjective_chart 0).1
  letI : Module.Projective A B := (h.finiteProjective_chart 0).2
  letI : IsNoetherianRing A := isNoetherianRing_of_ringEquiv _ (h.pd.chartPolynomialEquiv 0).toRingEquiv
  letI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : q.LiesOver p := ⟨by
    apply Ideal.ext
    intro a
    change originEval h.pd a = 0 ↔ e.1 (algebraMap A B a) = 0
    have he : e.1 (algebraMap A B a) = originEval h.pd a :=
      AlgHom.congr_fun (originEval_comp_chart h.pd e) a
    rw [he]⟩
  have hJ : p.map (algebraMap A B) = originIdeal k E x := by
    rw [show p = RingHom.ker (originEval h.pd).toRingHom from rfl,
      ker_originEval, Ideal.map_span, ← Set.range_comp]
    unfold originIdeal
    apply congrArg Ideal.span
    exact congrArg Set.range (funext fun j => (Subtype.ext rfl : _ = _))
  letI : IsReduced (B ⧸ p.map (algebraMap A B)) :=
    hJ.symm ▸ (inferInstance : IsReduced (B ⧸ originIdeal k E x))
  letI : Algebra.IsUnramifiedAt A q := isUnramifiedAt_of_reduced_finite_fibre (k := k) p q
  change Algebra.IsEtaleAt A q
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q

/-- The differentials of the affine coordinate ratios form a basis at
each point of the reduced origin fibre. -/
theorem IsFinCover.exists_originCoordinateBasis (h : IsFinCover k E x)
    [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)] (e : OriginFibrePoint k E x) :
    letI : (RingHom.ker e.1.toRingHom).IsPrime := (algebraPointKernel_isMaximal e.1).isPrime
    let C := Localization.AtPrime (RingHom.ker e.1.toRingHom)
    ∃ b : Module.Basis (Fin d) C Ω[C⁄k], ∀ j,
      b j = D k C (algebraMap (rB k E x {0}) C ⟨_, tco_mem k E x j⟩) := by
  let ab : Algebra A B := (integralClosure A E).algebra
  letI : Algebra A B := ab
  letI : SMul A B := ab.toSMul
  let q : Ideal B := RingHom.ker e.1.toRingHom
  letI : q.IsPrime := (algebraPointKernel_isMaximal e.1).isPrime
  let C := Localization.AtPrime q
  letI : IsScalarTower k A B := .of_algebraMap_eq fun c =>
    Subtype.ext (IsScalarTower.algebraMap_apply k F E c)
  letI : IsScalarTower k A C := IsScalarTower.to₁₂₄ k A B C
  letI : Algebra.FormallyEtale A C := h.isEtaleAt_originFibre e
  obtain ⟨b, hb⟩ := exists_kaehler_basis_of_polynomial_chart (C := C) (h.pd.chartPolynomialEquiv 0)
  have ht (j : Fin d) :
      algebraMap A B (h.pd.chartPolynomialEquiv 0 (MvPolynomial.X j)) =
        ⟨_, tco_mem k E x j⟩ := by
    apply Subtype.ext
    change algebraMap F E (h.pd.chartPolynomialEquiv 0 (MvPolynomial.X j) : F) = _
    rw [h.pd.chartPolynomialEquiv_X]
    simp [chartCoordinates]
  change ∃ b : Module.Basis (Fin d) C Ω[C⁄k], ∀ j,
    b j = D k C (algebraMap B C ⟨_, tco_mem k E x j⟩)
  refine ⟨b, fun j => (hb j).trans ?_⟩
  rw [IsScalarTower.algebraMap_apply A B C, ht j]

end GlobalTheory.PD
