import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothRegularRings
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineSmoothDimension

/-! The local dimension at a rational point of a smooth affine scheme
equals the relative dimension. -/

noncomputable section

open AlgebraicGeometry CategoryTheory GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

/-- Standard smooth coordinates lift a polynomial prime chain through the
given rational point. The relative dimension bounds its length from above. -/
theorem regular_local_dimension_of_rational_point {K B : Type} [Field K] [IsAlgClosed K]
    [CommRing B] [Algebra K B] (d : ℕ)
    [SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap K B)))]
    (ε : B →ₐ[K] K) [hε : (RingHom.ker ε.toRingHom).IsPrime] :
    IsRegularLocalRing (Localization.AtPrime (RingHom.ker ε.toRingHom)) ∧
      ringKrullDim (Localization.AtPrime (RingHom.ker ε.toRingHom)) = d := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K B))
  letI : Smooth f := SmoothOfRelativeDimension.smooth d f
  letI : Algebra.Smooth K B := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap K B))).mp (inferInstance : Smooth f))
  letI : IsRegularRing B := isRegularRing_of_smooth K B
  let p := RingHom.ker ε.toRingHom
  letI : p.IsPrime := hε
  refine ⟨inferInstance, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
  apply le_antisymm
  · have hU : ((⊤ : (Spec (.of B)).Opens) : Set (Spec (.of B))).Nonempty :=
      ⟨(⟨p, inferInstance⟩ : PrimeSpectrum B), trivial⟩
    have h := ringKrullDim_smooth_affineOpen f d (isAffineOpen_top _) hU
    rw [ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv] at h
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans_eq h
  · obtain ⟨S, hS, hstd⟩ := (HasRingHomProperty.Spec_iff
      (P := @SmoothOfRelativeDimension d)).mp (inferInstance : SmoothOfRelativeDimension d f)
    obtain ⟨r, hr, hr'⟩ : ∃ r ∈ S, ε r ≠ 0 := by
      by_contra! h
      exact (RingHom.ker_ne_top ε.toRingHom)
        (top_le_iff.mp (hS ▸ Ideal.span_le.mpr h))
    let T := Localization.Away r
    let χ : T →+* K := IsLocalization.Away.lift r (Ne.isUnit hr')
    let m := RingHom.ker χ
    letI : m.IsPrime := RingHom.ker_isPrime χ
    have hc (x : B) : χ (algebraMap B T x) = ε x :=
      IsLocalization.Away.lift_eq r (Ne.isUnit hr') x
    have hm : m.under B = p := Ideal.ext fun x => by
      change χ (algebraMap B T x) = 0 ↔ ε x = 0
      rw [hc]
    obtain ⟨g, hgc, hg⟩ := (hstd r hr).exists_etale_mvPolynomial
    let D := MvPolynomial (Fin d) K
    letI : Algebra D T := g.toAlgebra
    letI : Algebra.Etale D T := hg
    let P := m.under D
    letI : P.IsPrime := Ideal.comap_isPrime (algebraMap D T) m
    let ψ : D →ₐ[K] K := ⟨χ.comp g, fun x => by
      have e : g (MvPolynomial.C x) = algebraMap K T x :=
        congrArg (fun u : K →+* T => u x) hgc
      change χ (g (MvPolynomial.C x)) = x
      rw [e]
      exact (hc (algebraMap K B x)).trans (ε.commutes x)⟩
    let a (j : Fin d) := ψ (MvPolynomial.X j)
    have hψ : MvPolynomial.aeval a = ψ :=
      MvPolynomial.algHom_ext fun j => MvPolynomial.aeval_X a j
    have hP : (partialEvalSeries a).last.asIdeal = P := by
      rw [partialEvalSeries_last, hψ]
      rfl
    have hp : (d : ℕ∞) ≤ P.height := by
      rw [← hP, PrimeSpectrum.height_eq_orderHeight]
      exact Order.length_le_height_last (p := partialEvalSeries a)
    have hPm : P.height ≤ m.height := by
      rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P m]
      exact le_self_add
    rw [← hm, IsLocalization.height_under (.powers r) m]
    exact WithBot.coe_le_coe.mpr (hp.trans hPm)

end GlobalTheory.SchemeCohomology
