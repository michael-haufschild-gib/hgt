import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.ContinuousMap.Polynomial

/-!
# The continuous functional calculus acts on an eigenvector by the scalar value

If `R v = x v` then every polynomial in `R` scales `v` by the same polynomial evaluated at `x`.
Because the functional calculus is continuous in the function and the polynomial functions are
dense in the continuous functions on the compact spectrum, the same holds for every continuous
function: `cfc f R v = f x • v`.

The proof needs no subalgebra construction.  The set of test functions satisfying the identity is
the zero set of a continuous map, hence closed, and it contains the polynomial functions; taking
closures and using Stone–Weierstrass gives every continuous function.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Polynomial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Powers act on an eigenvector by powers of the eigenvalue. -/
theorem pow_apply_of_eigenvector' {R : H →L[ℂ] H} {x : ℝ} {v : H}
    (hv : R v = ((x : ℝ) : ℂ) • v) (n : ℕ) : (R ^ n) v = (((x ^ n : ℝ)) : ℂ) • v := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hstep : (R ^ (k + 1)) v = (R ^ k) (R v) := by
        rw [pow_succ]
        rfl
      have hsc : ((x : ℝ) : ℂ) * (((x ^ k : ℝ)) : ℂ) = (((x ^ (k + 1) : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hstep, hv, ContinuousLinearMap.map_smul, ih, smul_smul, hsc]

omit [CompleteSpace H] in
/-- Real scalars act on a complex space through the coercion. -/
theorem real_smul_complex_smul' (c : ℝ) (z : ℂ) (w : H) :
    c • (z • w) = ((c : ℂ) * z) • w := by
  have h : ((c : ℂ)) • (z • w) = c • (z • w) := by simp
  rw [← h, smul_smul]

omit [CompleteSpace H] in
/-- **A real polynomial in an operator acts on an eigenvector by its value at the eigenvalue.** -/
theorem aeval_apply_of_eigenvector' {q : ℝ[X]} {R : H →L[ℂ] H} {x : ℝ} {v : H}
    (hv : R v = ((x : ℝ) : ℂ) • v) :
    (Polynomial.aeval R q) v = ((q.eval x : ℝ) : ℂ) • v := by
  classical
  have hsum : Polynomial.aeval R q
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • R ^ i :=
    Polynomial.aeval_eq_sum_range R
  have hev : q.eval x = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * x ^ i :=
    Polynomial.eval_eq_sum_range x
  have hstep : ∀ i : ℕ, (q.coeff i • R ^ i : H →L[ℂ] H) v
      = (((q.coeff i * x ^ i : ℝ)) : ℂ) • v := by
    intro i
    have hpow : (R ^ i) v = (((x ^ i : ℝ)) : ℂ) • v := pow_apply_of_eigenvector' hv i
    have h1 : (q.coeff i • R ^ i : H →L[ℂ] H) v = q.coeff i • ((R ^ i) v) := rfl
    have hsc : ((q.coeff i : ℝ) : ℂ) * (((x ^ i : ℝ)) : ℂ)
        = (((q.coeff i * x ^ i : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h1, hpow, real_smul_complex_smul', hsc]
  have hsumapp : (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • R ^ i : H →L[ℂ] H) v
      = ∑ i ∈ Finset.range (q.natDegree + 1), (q.coeff i • R ^ i : H →L[ℂ] H) v := by
    simp
  rw [hsum, hsumapp, hev, Complex.ofReal_sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => hstep i

/-! ## From polynomials to all continuous functions -/

/-- The functional calculus applied to a polynomial function is the polynomial in the operator.
Both sides are `ℝ`-algebra homomorphisms out of `ℝ[X]` sending `X` to the operator. -/
theorem cfcHom_toContinuousMapOnAlgHom {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) (q : ℝ[X]) :
    cfcHom hR ((Polynomial.toContinuousMapOnAlgHom (spectrum ℝ R)) q)
      = Polynomial.aeval R q := by
  have hcomp : ((cfcHom hR : C(spectrum ℝ R, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H)).toAlgHom).comp
      (Polynomial.toContinuousMapOnAlgHom (spectrum ℝ R)) = Polynomial.aeval R := by
    refine Polynomial.algHom_ext ?_
    have hX : (Polynomial.toContinuousMapOnAlgHom (spectrum ℝ R)) (Polynomial.X : ℝ[X])
        = ContinuousMap.restrict (spectrum ℝ R) (ContinuousMap.id ℝ) := by
      ext y
      simp
    show cfcHom hR ((Polynomial.toContinuousMapOnAlgHom (spectrum ℝ R)) (Polynomial.X : ℝ[X]))
        = Polynomial.aeval R (Polynomial.X : ℝ[X])
    rw [hX, cfcHom_id hR, Polynomial.aeval_X]
  exact DFunLike.congr_fun hcomp q

/-- **The continuous functional calculus acts on an eigenvector by the value at the eigenvalue.**

If `R v = x • v` for a self-adjoint operator `R` and `x` lies in its spectrum, then
`cfc f R v = f x • v` for every function continuous on the spectrum.

The set of test functions satisfying the identity is closed, because `g ↦ cfcHom hR g v` and
`g ↦ g x • v` are both continuous, and it contains the polynomial functions by the eigenvector law
for polynomials.  Stone–Weierstrass makes the polynomial functions dense in `C(spectrum ℝ R, ℝ)`,
so the identity holds for every continuous function. -/
theorem cfc_apply_eigenvector {R : H →L[ℂ] H} (hR : IsSelfAdjoint R) {x : ℝ} {v : H}
    (hv : R v = ((x : ℝ) : ℂ) • v) (hx : x ∈ spectrum ℝ R) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ R)) :
    (cfc f R) v = ((f x : ℝ) : ℂ) • v := by
  haveI hcs : CompactSpace (spectrum ℝ R) :=
    isCompact_iff_compactSpace.mp (spectrum.isCompact R)
  -- the set of test functions obeying the eigenvector law
  have hSclosed : IsClosed {g : C(spectrum ℝ R, ℝ) |
      cfcHom hR g v = ((g ⟨x, hx⟩ : ℝ) : ℂ) • v} := by
    have hcont1 : Continuous (fun g : C(spectrum ℝ R, ℝ) => cfcHom hR g v) :=
      (ContinuousLinearMap.apply ℂ H v).continuous.comp (cfcHom_continuous hR)
    have heval : Continuous (fun g : C(spectrum ℝ R, ℝ) => g ⟨x, hx⟩) :=
      continuous_eval_const _
    have hcont2 : Continuous (fun g : C(spectrum ℝ R, ℝ) => ((g ⟨x, hx⟩ : ℝ) : ℂ) • v) :=
      (Complex.continuous_ofReal.comp heval).smul continuous_const
    exact isClosed_eq hcont1 hcont2
  -- polynomial functions obey it
  have hpoly : (↑(polynomialFunctions (spectrum ℝ R)) : Set C(spectrum ℝ R, ℝ))
      ⊆ {g : C(spectrum ℝ R, ℝ) | cfcHom hR g v = ((g ⟨x, hx⟩ : ℝ) : ℂ) • v} := by
    rintro g hg
    obtain ⟨q, -, rfl⟩ := hg
    show cfcHom hR ((Polynomial.toContinuousMapOnAlgHom (spectrum ℝ R)) q) v
        = ((((Polynomial.toContinuousMapOnAlgHom (spectrum ℝ R)) q) ⟨x, hx⟩ : ℝ) : ℂ) • v
    rw [cfcHom_toContinuousMapOnAlgHom hR q]
    have hval : (((Polynomial.toContinuousMapOnAlgHom (spectrum ℝ R)) q) ⟨x, hx⟩ : ℝ)
        = q.eval x := by
      simp
    rw [hval]
    exact aeval_apply_of_eigenvector' hv
  -- density
  have hdense : ∀ g : C(spectrum ℝ R, ℝ),
      cfcHom hR g v = ((g ⟨x, hx⟩ : ℝ) : ℂ) • v := by
    intro g
    have htop : (polynomialFunctions (spectrum ℝ R)).topologicalClosure = ⊤ :=
      ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
        (polynomialFunctions_separatesPoints (spectrum ℝ R))
    have hsub := closure_minimal hpoly hSclosed
    have hmem : g ∈ closure (↑(polynomialFunctions (spectrum ℝ R)) : Set C(spectrum ℝ R, ℝ)) := by
      rw [← Subalgebra.topologicalClosure_coe, htop]
      trivial
    exact hsub hmem
  rw [cfc_apply f R hR hf]
  exact hdense ⟨(spectrum ℝ R).restrict f, hf.restrict⟩

end GaloisForLFunctions.HTGeometry
