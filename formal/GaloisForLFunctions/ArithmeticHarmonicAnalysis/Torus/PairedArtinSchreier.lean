import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.LaurentArtinSchreier
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralIdempotents

/-!
# Artin–Schreier solution descent through paired neutral substitution

For every neutral ideal over the binary field, substitution `hᵢ ↦ zᵢwᵢ`
induces a bijection on the solution fibres of every neutral Artin–Schreier
equation. Oriented Laurent charts force all nonzero relative weights of a
solution to vanish. Its zero-weight coefficient is the unique neutral
solution that maps to it. Nonlinear, nonradical, and unit ideals are included.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
open scoped PairedNeutral
variable {ι : Type*} [Fintype ι]

/-- Each oriented chart sends neutral quotient elements to Laurent constants. -/
theorem pairedQuotientChartMap_algebraMap (K : Type*) [Field K]
    (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) (a : MvPolynomial ι K ⧸ J) :
    pairedQuotientChartMap K J ε (algebraMap (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) a) =
        AddMonoidAlgebra.single 0 a := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  change pairedChartMap K J ε (invariantSubstitution K f) = _
  exact pairedChartMap_invariant K J ε f

/-- An Artin–Schreier solution with neutral constant has no nonzero relative weight. -/
theorem pairedNeutral_binaryArtinSchreier_nonzero_weight
    (J : Ideal (MvPolynomial ι (ZMod 2)))
    (x : MvPolynomial (ι ⊕ ι) (ZMod 2) ⧸ J.map (invariantSubstitution (ZMod 2)))
    (a : MvPolynomial ι (ZMod 2) ⧸ J)
    (hx : binaryArtinSchreier _ x = algebraMap (MvPolynomial ι (ZMod 2) ⧸ J) _ a)
    (q : ι → ℤ) (hq : q ≠ 0) :
    pairedNeutralQuotientEquiv (ZMod 2) J x q = 0 := by
  let F := pairedQuotientChartMap (ZMod 2) J (weightOrientation q)
  have hf : binaryArtinSchreier _ (F x) = AddMonoidAlgebra.single 0 a := by
    calc
      binaryArtinSchreier _ (F x) = F (binaryArtinSchreier _ x) := by
        simp only [binaryArtinSchreier_apply, map_add, map_pow]
      _ = F (algebraMap (MvPolynomial ι (ZMod 2) ⧸ J) _ a) := congrArg F hx
      _ = AddMonoidAlgebra.single 0 a :=
        pairedQuotientChartMap_algebraMap (ZMod 2) J (weightOrientation q) a
  have he := congrArg (fun f : NeutralLaurent (ZMod 2) J => f.coeff q)
    (laurent_binaryArtinSchreier_eq_constantCoeff (F x) a hf)
  change (pairedQuotientChartMap (ZMod 2) J (weightOrientation q) x).coeff q = _ at he
  rw [pairedQuotientChartMap_recovers] at he
  simpa [AddMonoidAlgebra.coeff_single, hq, Ne.symm hq] using he

/-- Every solution of a neutral binary Artin–Schreier equation descends to its
zero-weight coefficient, with no radicality assumption on the neutral ideal. -/
theorem pairedNeutral_binaryArtinSchreier_eq_algebraMap
    (J : Ideal (MvPolynomial ι (ZMod 2)))
    (x : MvPolynomial (ι ⊕ ι) (ZMod 2) ⧸ J.map (invariantSubstitution (ZMod 2)))
    (a : MvPolynomial ι (ZMod 2) ⧸ J)
    (hx : binaryArtinSchreier _ x = algebraMap (MvPolynomial ι (ZMod 2) ⧸ J) _ a) :
    x = algebraMap (MvPolynomial ι (ZMod 2) ⧸ J)
      (MvPolynomial (ι ⊕ ι) (ZMod 2) ⧸ J.map (invariantSubstitution (ZMod 2)))
        (pairedNeutralQuotientEquiv (ZMod 2) J x 0) := by
  apply (pairedNeutralQuotientEquiv (ZMod 2) J).injective
  ext q
  rw [pairedNeutralQuotientEquiv_algebraMap]
  by_cases hq : q = 0
  · simp [hq]
  · rw [if_neg hq]
    exact pairedNeutral_binaryArtinSchreier_nonzero_weight J x a hx q hq

/-- Paired substitution neither loses nor creates binary Artin–Schreier solutions. -/
theorem pairedNeutral_binaryArtinSchreier_solvable_iff
    (J : Ideal (MvPolynomial ι (ZMod 2))) (a : MvPolynomial ι (ZMod 2) ⧸ J) :
    (∃ x : MvPolynomial (ι ⊕ ι) (ZMod 2) ⧸ J.map (invariantSubstitution (ZMod 2)),
      binaryArtinSchreier _ x = algebraMap (MvPolynomial ι (ZMod 2) ⧸ J) _ a) ↔
      ∃ b : MvPolynomial ι (ZMod 2) ⧸ J, binaryArtinSchreier _ b = a := by
  let F := algebraMap (MvPolynomial ι (ZMod 2) ⧸ J)
    (MvPolynomial (ι ⊕ ι) (ZMod 2) ⧸ J.map (invariantSubstitution (ZMod 2)))
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨pairedNeutralQuotientEquiv (ZMod 2) J x 0, ?_⟩
    apply pairedNeutralQuotient_algebraMap_injective (ZMod 2) J
    rw [binaryArtinSchreier_map F,
      ← pairedNeutral_binaryArtinSchreier_eq_algebraMap J x a hx]
    exact hx
  · rintro ⟨b, hb⟩
    refine ⟨F b, ?_⟩
    rw [← binaryArtinSchreier_map F, hb]

/-- The coefficient embedding is a canonical bijection on complete solution fibres. -/
def pairedNeutralBinaryArtinSchreierFibreEquiv
    (J : Ideal (MvPolynomial ι (ZMod 2))) (a : MvPolynomial ι (ZMod 2) ⧸ J) :
    {b : MvPolynomial ι (ZMod 2) ⧸ J // binaryArtinSchreier _ b = a} ≃
      {x : MvPolynomial (ι ⊕ ι) (ZMod 2) ⧸ J.map (invariantSubstitution (ZMod 2)) //
        binaryArtinSchreier _ x = algebraMap (MvPolynomial ι (ZMod 2) ⧸ J) _ a} := by
  let F := algebraMap (MvPolynomial ι (ZMod 2) ⧸ J)
    (MvPolynomial (ι ⊕ ι) (ZMod 2) ⧸ J.map (invariantSubstitution (ZMod 2)))
  refine Equiv.ofBijective (fun b => ⟨F b.1, ?_⟩) ⟨?_, ?_⟩
  · rw [← binaryArtinSchreier_map F, b.2]
  · intro b c h
    exact Subtype.ext (pairedNeutralQuotient_algebraMap_injective (ZMod 2) J
      (congrArg Subtype.val h))
  · intro x
    let b := pairedNeutralQuotientEquiv (ZMod 2) J x.1 0
    have he : F b = x.1 :=
      (pairedNeutral_binaryArtinSchreier_eq_algebraMap J x.1 a x.2).symm
    have hb : binaryArtinSchreier _ b = a := by
      apply pairedNeutralQuotient_algebraMap_injective (ZMod 2) J
      rw [binaryArtinSchreier_map F, he]
      exact x.2
    exact ⟨⟨b, hb⟩, Subtype.ext he⟩

#print axioms pairedQuotientChartMap_algebraMap
#print axioms pairedNeutral_binaryArtinSchreier_eq_algebraMap
#print axioms pairedNeutral_binaryArtinSchreier_solvable_iff
#print axioms pairedNeutralBinaryArtinSchreierFibreEquiv
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
