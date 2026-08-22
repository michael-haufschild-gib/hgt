import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FunctionalAnalytic

/-!
# Chen--Gupta--Li Lemma 6.2: finite reflected contour

The finite dual Dirichlet polynomial in CGL's reflected integrand is extended
off the initial `Re(s)=-1` line here.  It is holomorphic throughout the
source's displacement strip, so its contour movement has no singular residue.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- CGL's reflected finite Dirichlet-polynomial integrand, extended from its
initial `Re(s)=-1` line to the full finite-part contour strip. -/
def cglLemma62FiniteContourIntegrand (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) (s : ℂ) : ℂ :=
  cglLemma62MellinTransform w s * (N.value : ℂ) ^ s *
    cglLemma62PrimitiveFunctionalFactor B.primitive (s - (t : ℂ) * I) *
      cglLemma62EulerCorrectionAt B (s - (t : ℂ) * I) *
        cglLemma62DirichletHead B.character⁻¹ M (1 - s + (t : ℂ) * I)

/-- The off-line finite integrand restricts exactly to CGL's finite reflected
integrand on the source's initial left line. -/
theorem cglLemma62_finiteContourIntegrand_eq_line (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (B : CGLLemma62InducedCharacter) (t v : ℝ) (M : ℕ) :
    cglLemma62FiniteContourIntegrand w N B t M ((-1 : ℂ) + (v : ℂ) * I) =
      cglLemma62ReflectedFiniteIntegrand w N B t M v := by
  have hleft : ((-1 : ℂ) + (v : ℂ) * I) - (t : ℂ) * I =
      cglLemma62LeftPoint t v := by
    unfold cglLemma62LeftPoint
    push_cast
    ring
  have hright : 1 - ((-1 : ℂ) + (v : ℂ) * I) + (t : ℂ) * I =
      cglLemma62RightPoint t v := by
    unfold cglLemma62RightPoint
    push_cast
    ring
  unfold cglLemma62FiniteContourIntegrand cglLemma62ReflectedFiniteIntegrand
  rw [hleft, hright, cglLemma62EulerCorrectionAt_eq_line]

private theorem cglLemma62_dirichletTerm_differentiable
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    Differentiable ℂ (fun s : ℂ => LSeries.term (↗χ) s n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa only [LSeries.term_zero] using (differentiable_const (c := (0 : ℂ)))
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hfun : (fun s : ℂ => LSeries.term (↗χ) s n) =
        fun s : ℂ => (↗χ) n * (n : ℂ) ^ (-s) := by
      funext s
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg]
    rw [hfun]
    intro s
    exact (differentiableAt_const _).mul
      (DifferentiableAt.cpow (differentiableAt_const _) differentiableAt_id.neg
        (Complex.ofReal_mem_slitPlane.mpr hnpos))

/-- CGL's literal finite Dirichlet prefix is entire.  The `n=0` convention
for L-series terms is discharged internally. -/
theorem cglLemma62DirichletHead_differentiable (χ : DirichletCharacter ℂ q) (M : ℕ) :
    Differentiable ℂ (fun s : ℂ => cglLemma62DirichletHead χ M s) := by
  intro s
  unfold cglLemma62DirichletHead
  have hsum : DifferentiableAt ℂ
      (∑ n ∈ Finset.range (M + 1), fun s : ℂ => LSeries.term (↗χ) s n) s := by
    apply DifferentiableAt.sum
    intro n hn
    exact cglLemma62_dirichletTerm_differentiable χ n s
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards with z
  simp only [Finset.sum_apply]

private theorem cglLemma62FiniteContour_shift_mapsTo (t : ℝ) :
    Set.MapsTo (fun z : ℂ => z - (t : ℂ) * I)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2))
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) := by
  intro z hz
  change (-1 : ℝ) ≤ (z - (t : ℂ) * I).re ∧
    (z - (t : ℂ) * I).re ≤ (1 / 2 : ℝ)
  simpa [GaloisForLFunctions.HTGeometry.verticalStrip] using hz

/-- CGL's finite reflected integrand is holomorphic on the whole source
strip from `Re(s)=-1` to `Re(s)=1/2`. -/
theorem cglLemma62FiniteContourIntegrand_differentiableOn (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (B : CGLLemma62InducedCharacter) (t : ℝ) (M : ℕ) :
    DifferentiableOn ℂ (cglLemma62FiniteContourIntegrand w N B t M)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) := by
  intro s hs
  have hshift := cglLemma62FiniteContour_shift_mapsTo t
  have hdshift : DifferentiableWithinAt ℂ (fun z : ℂ => z - (t : ℂ) * I)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) s :=
    (differentiableAt_id.sub (differentiableAt_const _)).differentiableWithinAt
  have hH : DifferentiableWithinAt ℂ (cglLemma62MellinTransform w)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) s :=
    (cglLemma62_mellinTransform_analyticOnNhd w s (mem_univ s)).differentiableAt.differentiableWithinAt
  have hNne : (N.value : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.positive)
  have hN : DifferentiableWithinAt ℂ (fun z : ℂ => (N.value : ℂ) ^ z)
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) s :=
    (differentiableAt_id.const_cpow (Or.inl hNne)).differentiableWithinAt
  have hP : DifferentiableWithinAt ℂ
      (fun z : ℂ => cglLemma62PrimitiveFunctionalFactor B.primitive (z - (t : ℂ) * I))
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) s := by
    simpa only [Function.comp_def] using
      ((cglLemma62PrimitiveFunctionalFactor_differentiableOn B.primitive
        (s - (t : ℂ) * I) (hshift hs)).comp s hdshift hshift)
  have hE : DifferentiableWithinAt ℂ
      (fun z : ℂ => cglLemma62EulerCorrectionAt B (z - (t : ℂ) * I))
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) s := by
    simpa only [Function.comp_def] using
      ((cglLemma62EulerCorrectionAt_differentiableOn B
        (s - (t : ℂ) * I) (hshift hs)).comp s hdshift hshift)
  have hinner : DifferentiableAt ℂ (fun z : ℂ => 1 - z + (t : ℂ) * I) s :=
    ((differentiableAt_const _).sub differentiableAt_id).add (differentiableAt_const _)
  have hD : DifferentiableWithinAt ℂ
      (fun z : ℂ => cglLemma62DirichletHead B.character⁻¹ M (1 - z + (t : ℂ) * I))
      (GaloisForLFunctions.HTGeometry.verticalStrip (-1) (1 / 2)) s := by
    simpa only [Function.comp_def] using
      ((cglLemma62DirichletHead_differentiable B.character⁻¹ M
        (1 - s + (t : ℂ) * I)).comp s hinner).differentiableWithinAt
  unfold cglLemma62FiniteContourIntegrand
  exact (((hH.mul hN).mul hP).mul hE).mul hD

end

end RHTower
