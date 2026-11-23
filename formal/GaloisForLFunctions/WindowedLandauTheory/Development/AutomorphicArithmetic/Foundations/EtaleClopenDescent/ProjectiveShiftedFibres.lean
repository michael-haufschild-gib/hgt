import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineSmoothDimension
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectivePointRatios
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveRatioTransitions
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedArtinianFibre
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RegularAffineFibres
import Mathlib.Algebra.MvPolynomial.Funext

/-! Shifting homogeneous numerators by a multiple of the denominator
makes their affine common zero scheme formally étale. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open UpperTheory.Cb GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of K)} {N m : ℕ}

private abbrev Grade := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

/-- On the denominator chart, subtracting a multiple of the denominator
subtracts the corresponding scalar from the ratio. -/
theorem projectiveRatio_sub_smul (i : X ⟶ PSpace K N) (hi : i ≫ PSpace.str K N = s)
    (hm : 0 < m) (h g : Grade (K := K) (N := N) m) (c : K) :
    let V := i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) h.1
    let r : SectionRing s V := projectiveRatio i h.2 g.2
    let r' : SectionRing s V := projectiveRatio i h.2 (g - c • h).2
    r' = r - algebraMap K (SectionRing s V) c := by
  intro V r r'
  let R := projectiveRatioLinear i hi h.2 hm
  change R (g - c • h) = R g - algebraMap K (SectionRing s V) c
  have hh : R h = 1 := projectiveRatio_self i h.2
  rw [map_sub, map_smul, hh, Algebra.smul_def, mul_one]

variable [IsIntegral X] [IsAlgClosed K] [CharZero K]

/-- A common shift makes the zero fibre of the ratios on a nonempty chart
formally étale and keeps each numerator nonzero at the generic point. -/
theorem exists_shift_formallyEtale_projective_fibre (i : X ⟶ PSpace K N) [IsClosedImmersion i]
    (hi : i ≫ PSpace.str K N = s) (d : ℕ) [SmoothOfRelativeDimension d s] (hm : 0 < m)
    (h : Grade (K := K) (N := N) m)
    (hh : genericPoint X ∈ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) h.1)
    (g : Fin d → Grade (K := K) (N := N) m) :
    ∃ c : Fin d → K,
      (∀ j, genericPoint X ∈ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) (g j - c j • h).1) ∧
      let V := i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) h.1
      let A := SectionRing s V
      let r (j : Fin d) : A := projectiveRatio i h.2 (g j - c j • h).2
      Algebra.FormallyEtale K (A ⧸ Ideal.span (Set.range r)) := by
  classical
  let V := i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) h.1
  let A := SectionRing s V
  letI : Nonempty V := ⟨⟨genericPoint X, hh⟩⟩
  letI : IsDomain A := IsIntegral.component_integral V
  letI : Smooth s := SmoothOfRelativeDimension.smooth d s
  have hV : IsAffineOpen V := (Proj.isAffineOpen_basicOpen (Grade (K := K) (N := N)) _ h.2 hm).preimage i
  letI : Algebra.FiniteType K A := sectionRing_finiteType s hV
  have hd : ringKrullDim A = (d : ℕ∞) := ringKrullDim_smooth_affineOpen s d hV ⟨_, hh⟩
  let r (j : Fin d) : A := projectiveRatio i h.2 (g j).2
  let φ : MvPolynomial (Fin d) K →ₐ[K] A := MvPolynomial.aeval r
  obtain ⟨a, ha, hav⟩ := exists_polynomial_formallyEtale_fibres hd φ
  obtain ⟨p, hp⟩ := Ideal.exists_maximal A
  letI : p.IsMaximal := hp
  obtain ⟨y, _⟩ := exists_affinePoint_ker hV p
  let ε : A →ₐ[K] K := affinePointEval y.1 y.2
  let z (j : Fin d) := ε (r j)
  let b : Fin d → MvPolynomial (Fin d) K := fun j => MvPolynomial.X j - MvPolynomial.C (z j)
  have hb (j : Fin d) : b j ≠ 0 := by
    intro he
    have hf := congrArg (MvPolynomial.eval (fun _ => z j + 1)) he
    simp [b] at hf
  let p' := a * ∏ j, b j
  have hp' : p' ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr (fun j _ => hb j))
  obtain ⟨c, hc⟩ : ∃ c : Fin d → K, MvPolynomial.eval c p' ≠ 0 := by
    by_contra! H
    exact hp' (MvPolynomial.funext fun c => (H c).trans (map_zero _).symm)
  have hca : MvPolynomial.eval c a ≠ 0 := by
    intro hzero
    apply hc
    rw [map_mul, hzero, zero_mul]
  have hcb (j : Fin d) : c j ≠ z j := by
    intro he
    apply hc
    have hbj : MvPolynomial.eval c (b j) = 0 := by simp [b, he]
    rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ j) hbj, mul_zero]
  have hr (j : Fin d) : (projectiveRatio i h.2 (g j - c j • h).2 : A) =
      φ (MvPolynomial.X j) - algebraMap K A (c j) := by
    exact (projectiveRatio_sub_smul i hi hm h (g j) (c j)).trans
      (congrArg (fun w : A => w - algebraMap K A (c j)) (MvPolynomial.aeval_X r j).symm)
  refine ⟨c, ?_, ?_⟩
  · intro j
    let w := projectiveRatio i h.2 (g j - c j • h).2
    have hne : ε w ≠ 0 := by
      change ε (projectiveRatio i h.2 (g j - c j • h).2) ≠ 0
      rw [hr j, map_sub, ε.commutes, MvPolynomial.aeval_X, sub_ne_zero]
      exact (hcb j).symm
    have hyw := (pointEval_ne_zero_iff y.1.hom V y.2 w).mp hne
    have hyy := (genericPoint_specializes (y.1.hom default)).mem_open (X.basicOpen w).isOpen hyw
    exact ((basicOpen_projectiveRatio i h.2 (g j - c j • h).2).le hyy).2
  · let w (j : Fin d) : A := projectiveRatio i h.2 (g j - c j • h).2
    change Algebra.FormallyEtale K (A ⧸ Ideal.span (Set.range w))
    have hw : w = fun j => φ (MvPolynomial.X j) - algebraMap K A (c j) := funext hr
    exact hw.symm ▸ hav c hca

end GlobalTheory.SchemeCohomology
