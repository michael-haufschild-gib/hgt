import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62ReflectedContour

/-!
# Chen--Gupta--Li Lemma 6.2: reflected Dirichlet-series split

On CGL's reflected right line the inverse-character `L`-function is an
absolutely convergent Dirichlet series.  This module makes the source's
finite-polynomial plus complementary-tail decomposition exact, before the
two pieces receive their separate contour displacements and estimates.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation

namespace RHTower

noncomputable section

/-- The reflected CGL right point, packaged with its closed absolute-
convergence certificate. -/
def cglLemma62RightPointAC (t v : ℝ) : CGLAbsoluteConvergencePoint :=
  ⟨cglLemma62RightPoint t v, by
    unfold cglLemma62RightPoint
    norm_num⟩

/-- The `0≤m≤M` L-series prefix; its zero-th term is definitionally zero, so
this is CGL's literal `1≤m≤M` finite Dirichlet polynomial. -/
def cglLemma62DirichletHead (χ : DirichletCharacter ℂ q) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (M + 1), LSeries.term (↗χ) s n

/-- The absolutely convergent complement of the finite CGL Dirichlet prefix. -/
def cglLemma62DirichletTail (χ : DirichletCharacter ℂ q) (M : ℕ)
    (s : CGLAbsoluteConvergencePoint) : ℂ :=
  ∑' n : {n : ℕ // n ∉ Finset.range (M + 1)}, LSeries.term (↗χ) s.1 n

/-- Any Dirichlet character L-series in CGL's certified convergence half-plane
is exactly its finite prefix plus complementary tail. -/
theorem cglLemma62_lseries_eq_head_add_tail (χ : DirichletCharacter ℂ q) (M : ℕ)
    (s : CGLAbsoluteConvergencePoint) :
    L ↗χ s.1 = cglLemma62DirichletHead χ M s.1 + cglLemma62DirichletTail χ M s := by
  have hsum : LSeriesSummable (↗χ) s.1 :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ s.2
  simpa [LSeries, cglLemma62DirichletHead, cglLemma62DirichletTail] using
    (hsum.sum_add_tsum_subtype_compl (Finset.range (M + 1))).symm

/-- On the reflected right line, the ambient inverse-character `L`-function
is CGL's finite Dirichlet polynomial plus its exact tail. -/
theorem cglLemma62_right_lfunction_eq_head_add_tail
    (B : CGLLemma62InducedCharacter) (t v : ℝ) (M : ℕ) :
    DirichletCharacter.LFunction B.character⁻¹ (cglLemma62RightPoint t v) =
      cglLemma62DirichletHead B.character⁻¹ M (cglLemma62RightPoint t v) +
        cglLemma62DirichletTail B.character⁻¹ M (cglLemma62RightPointAC t v) := by
  rw [DirichletCharacter.LFunction_eq_LSeries]
  · exact cglLemma62_lseries_eq_head_add_tail B.character⁻¹ M
      (cglLemma62RightPointAC t v)
  · unfold cglLemma62RightPoint
    norm_num

/-- The reflected CGL integrand with the `L`-function replaced by its finite
Dirichlet polynomial. -/
def cglLemma62ReflectedFiniteIntegrand (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) (v : ℝ) : ℂ :=
  cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
    (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
      cglLemma62PrimitiveFunctionalFactor B.primitive (cglLemma62LeftPoint t v) *
        cglLemma62EulerCorrection B t v *
          cglLemma62DirichletHead B.character⁻¹ M (cglLemma62RightPoint t v)

/-- The reflected CGL integrand with the complementary Dirichlet tail. -/
def cglLemma62ReflectedTailIntegrand (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) (v : ℝ) : ℂ :=
  cglLemma62MellinTransform w ((-1 : ℂ) + (v : ℂ) * I) *
    (N.value : ℂ) ^ ((-1 : ℂ) + (v : ℂ) * I) *
      cglLemma62PrimitiveFunctionalFactor B.primitive (cglLemma62LeftPoint t v) *
        cglLemma62EulerCorrection B t v *
          cglLemma62DirichletTail B.character⁻¹ M (cglLemma62RightPointAC t v)

/-- **CGL (6.4), algebraic split.** The reflected integrand equals the sum of
its finite Dirichlet-polynomial and complementary-tail integrands. -/
theorem cglLemma62_reflected_eq_finite_add_tail
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) (v : ℝ) :
    cglLemma62ReflectedLineIntegrand w N B t v =
      cglLemma62ReflectedFiniteIntegrand w N B t M v +
        cglLemma62ReflectedTailIntegrand w N B t M v := by
  unfold cglLemma62ReflectedLineIntegrand cglLemma62ReflectedFiniteIntegrand
    cglLemma62ReflectedTailIntegrand
  rw [cglLemma62_right_lfunction_eq_head_add_tail]
  ring

end

end RHTower
