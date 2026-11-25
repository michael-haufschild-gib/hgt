import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AffineSmoothTranscendenceDegree
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PolynomialTwistGeneration

/-! The global sections of positive powers of a very ample bundle grow with the relative dimension. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.ProjectiveSections

/-- On a smooth integral projective scheme, a nonempty coordinate chart identifies the
large-twist section space with the bounded-degree part of its coordinate ring. -/
theorem finrank_twistSections_growth {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d f]
    {H : LB X} (hH : H.IsLB) {m : ℕ} (s : Fin m → H.Sec)
    (hcov : ⊤ ≤ ⨆ i, nonzeroLocus (s i))
    (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin m → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hπ : ∀ i, letI := sectionAlgebra f (nonzeroLocus (s i))
      Function.Surjective (MvPolynomial.aeval (R := K) (r i))) :
    ∃ b c C : ℕ, 1 ≤ c ∧ ∀ n : ℕ, b ≤ n → 1 ≤ n →
      n ^ d ≤ c * Module.finrank K (TwistSections f (LB.trivial X) H ⊤ n) ∧
      Module.finrank K (TwistSections f (LB.trivial X) H ⊤ n) ≤ C * n ^ d := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨i, hx⟩ := Opens.mem_iSup.mp (hcov (Set.mem_univ x))
  let V := nonzeroLocus (s i)
  have hV : (V : Set X).Nonempty := ⟨x, hx⟩
  letI : Nonempty V := hV.to_subtype
  letI := sectionAlgebra f V
  have hd : Algebra.trdeg K Γ(X, V) = d := trdeg_sectionRing_of_smooth f d (ha i) hV
  obtain ⟨c, C, hc, hGrowth⟩ := finrank_totalDegree_image_growth K Γ(X, V) m d (r i) (hπ i) hd
  obtain ⟨b, hb⟩ := range_twistRestrictionRatio_eq f hH s hcov r hr hπ
  refine ⟨b, c, C, hc, fun n hn hn' => ?_⟩
  let e := LinearEquiv.ofInjective (twistRestrictionRatio f hH s i n)
    (twistRestrictionRatio_injective f hH s i n hV)
  have he := LinearEquiv.finrank_eq e
  rw [hb n hn i] at he
  rw [he]
  exact hGrowth n hn'

end GlobalTheory.ProjectiveSections
