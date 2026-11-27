import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedCechHomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedComplexEquivalence
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedKunneth
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MixedCechTensorDifferential

/-! For mixed intersections with tensor coefficients, the joined Čech
cohomology dimensions are the convolution of the two factor dimensions. -/

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.WH GlobalTheory.CechDR
open Finset.HasAntidiagonal

namespace HTGeometry.FinsetCechDatum

variable {K ι κ : Type} [Field K] [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]
  (A : FinsetCechDatum.{0} ι) (B : FinsetCechDatum.{0} κ)
  (D : FinsetCechDatum.{0} (ι ⊕ₗ κ))
  [∀ s, Module K (A.obj s)] [∀ t, Module K (B.obj t)] [∀ u, Module K (D.obj u)]
  (hA : ∀ {s t} (h : s ⊆ t) (r : K) (x : A.obj s), A.res h (r • x) = r • A.res h x)
  (hB : ∀ {s t} (h : s ⊆ t) (r : K) (x : B.obj s), B.res h (r • x) = r • B.res h x)
  (hD : ∀ {s t} (h : s ⊆ t) (r : K) (x : D.obj s), D.res h (r • x) = r • D.res h x)

/-- Two nonempty intersections contribute total cardinality two higher than
the cohomological degree in the tensor complex. -/
theorem finrank_mixed_cech
    (hzero : ∀ s t, ¬ (s.Nonempty ∧ t.Nonempty) → Subsingleton (D.obj (uni s t)))
    (e : ∀ (s : Finset ι) (t : Finset κ), s.Nonempty → t.Nonempty →
      (A.obj s ⊗[K] B.obj t ≃ₗ[K] D.obj (uni s t)))
    (hnat : ∀ {s s' t t'} (hs : s ⊆ s') (ht : t ⊆ t')
      (hs₀ : s.Nonempty) (ht₀ : t.Nonempty) (a : A.obj s) (b : B.obj t),
      D.res (uni_mono hs ht) (e s t hs₀ ht₀ (a ⊗ₜ b)) =
        e s' t' (hs₀.mono hs) (ht₀.mono ht) (A.res hs a ⊗ₜ B.res ht b))
    (hfinA : ∀ p, Module.Finite K ((A.linearComplex hA).homology p))
    (hfinB : ∀ q, Module.Finite K ((B.linearComplex hB).homology q)) (n : ℕ) :
    Module.Finite K ((D.linearComplex hD).homology (n + 1)) ∧
      Module.finrank K ((D.linearComplex hD).homology (n + 1)) =
        ∑ x ∈ antidiagonal n, Module.finrank K ((A.linearComplex hA).homology x.1) *
          Module.finrank K ((B.linearComplex hB).homology x.2) := by
  have hA₀ (p : ℕ) : Module.Finite K ((A.graded hA).degreeShort p).homology := by
    letI := hfinA p
    exact Module.Finite.equiv (A.nonempty_gradedHomology_equiv hA p).some.symm
  have hB₀ (q : ℕ) : Module.Finite K ((B.graded hB).degreeShort q).homology := by
    letI := hfinB q
    exact Module.Finite.equiv (B.nonempty_gradedHomology_equiv hB q).some.symm
  obtain ⟨hF, hN⟩ := (A.graded hA).finrank_homology_tensor (B.graded hB) hA₀ hB₀ n
  letI := hF
  let G := (A.graded hA).tensorComplex (B.graded hB)
  let H := D.graded hD
  obtain ⟨E₁⟩ := FiniteGradedComplex.nonempty_homology_equiv_of_graded
    (G := G) (H := H)
    (mixedTensorEquiv A B D hzero e)
    (fun j x => mixedTensorEquiv_π A B D hA hB hD hzero e j x)
    (fun x => mixedTensorEquiv_d A B D hA hB hD hzero e hnat x) (n + 1)
  obtain ⟨E₂⟩ := D.nonempty_gradedHomology_equiv hD (n + 1)
  let E := E₁.trans E₂
  refine ⟨Module.Finite.equiv E, ?_⟩
  rw [← E.finrank_eq, hN]
  exact Finset.sum_congr rfl fun x _ => congrArg₂ (· * ·)
    (A.nonempty_gradedHomology_equiv hA x.1).some.finrank_eq
    (B.nonempty_gradedHomology_equiv hB x.2).some.finrank_eq

end HTGeometry.FinsetCechDatum
