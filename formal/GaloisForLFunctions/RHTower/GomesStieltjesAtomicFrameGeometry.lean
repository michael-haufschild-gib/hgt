import GaloisForLFunctions.HTGeometry.GomesCanonicalMomentGeometry
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryPadeContactParity
import GaloisForLFunctions.HTGeometry.StieltjesSemidefiniteExistence

/-!
Concrete corpus applications of the internal-frame and tensor-observation viewpoint in
Gomes, arXiv:2404.10461 and arXiv:2509.25276v7. Source equality is proved before
transferring the geometry. These are applications, not numbered paper transcriptions.
-/
open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.RHTower
open _root_.HTGeometry
open GaloisForLFunctions.HTGeometry

open _root_.RHTower Polynomial
open scoped BigOperators

/-- Finite atomic moments with arbitrary real amplitudes and nonnegative squared weights. -/
def gomesAtomicMoment (S : Finset ℝ) (w : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ S, (w x)^(2 : ℕ)*x^n

/-- The exact source quadratic form is the sum of its squared weighted observations. -/
theorem gomesAtomicMoment_inner (S : Finset ℝ) (w : ℝ → ℝ) (p : Polynomial ℝ) :
    momentInner (gomesAtomicMoment S w) p p = ∑ x ∈ S, (w x*p.eval x)^(2 : ℕ) := by
  rw [momentInner_def]
  change momentFunctional (fun n => ∑ x ∈ S, (w x)^(2 : ℕ)*x^n) (p*p) = _
  rw [momentFunctional_finiteAtomicMoment]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Polynomial.eval_mul]
  ring

/-- Finite atomic sources are always semidefinite. -/
theorem gomesAtomicMoment_nonnegative (S : Finset ℝ) (w : ℝ → ℝ) (p : Polynomial ℝ) :
    0 ≤ momentInner (gomesAtomicMoment S w) p p := by
  rw [gomesAtomicMoment_inner]
  exact Finset.sum_nonneg (fun x hx => sq_nonneg _)

/-- The atomic kernel consists exactly of polynomials invisible at every weighted observation. -/
theorem gomesAtomicMoment_kernel (S : Finset ℝ) (w : ℝ → ℝ) (p : Polynomial ℝ) :
    momentInner (gomesAtomicMoment S w) p p = 0 ↔ ∀ x ∈ S, w x*p.eval x = 0 := by
  rw [gomesAtomicMoment_inner]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x hx => sq_nonneg (w x*p.eval x))]
  simp only [sq_eq_zero_iff]

/-- Finite observations cannot be strictly positive on the entire polynomial space. -/
theorem gomesAtomicMoment_not_positive (S : Finset ℝ) (w : ℝ → ℝ) :
    ¬ PositiveMomentForm (gomesAtomicMoment S w) := by
  classical
  intro h
  let p : Polynomial ℝ := ∏ x ∈ S, (X-C x)
  have hp : p ≠ 0 := by
    exact (Polynomial.monic_prod_of_monic S _ (fun x hx => Polynomial.monic_X_sub_C x)).ne_zero
  have hz : momentInner (gomesAtomicMoment S w) p p = 0 := by
    apply (gomesAtomicMoment_kernel S w p).mpr
    intro x hx
    have he : p.eval x = 0 := by
      simp only [p,Polynomial.eval_prod]
      apply Finset.prod_eq_zero hx
      simp
    rw [he,mul_zero]
  have hpos := h.pos_of_ne_zero p hp
  rw [hz] at hpos
  exact (lt_irrefl 0) hpos

/-- Every positive uniform-tail regularization restores full polynomial positivity. -/
theorem gomesAtomicStieltjes_positive (S : Finset ℝ) (w : ℝ → ℝ) (j : ℕ) :
    PositiveMomentForm (stieltjesPerturbedSequence (gomesAtomicMoment S w) j) :=
  stieltjesPerturbedSequence_positiveMomentForm (gomesAtomicMoment_nonnegative S w) j


/-- The canonical frame model of this concrete corpus source. -/
def gomesAtomicStieltjesModel (S : Finset ℝ) (w : ℝ → ℝ) (j : ℕ) : GomesMomentModel := gomesCanonicalMomentModel (stieltjesPerturbedSequence (gomesAtomicMoment S w) j)

/-- Exact source identification, retaining its original mass. -/
theorem gomesAtomicStieltjesModel_moments (S : Finset ℝ) (w : ℝ → ℝ) (j : ℕ) :
    (gomesAtomicStieltjesModel S w j).moments = (stieltjesPerturbedSequence (gomesAtomicMoment S w) j) := by
  apply (gomesCanonicalMomentModel_moments_iff _).mpr
  exact gomesAtomicStieltjes_positive S w j

/-- The actual source polynomials strictly increase distance from the real axis at every higher quotient. -/
theorem gomesAtomicStieltjes_quotient_height (S : Finset ℝ) (w : ℝ → ℝ) (j : ℕ) (n : ℕ) (z : ℂ) :
    |z.im| < |(monicOrthoC (stieltjesPerturbedSequence (gomesAtomicMoment S w) j) ((n+1)+1) z /
      monicOrthoC (stieltjesPerturbedSequence (gomesAtomicMoment S w) j) (n+1) z).im| ↔ z.im ≠ 0 := by
  simpa only [gomesMomentQuotient,gomesAtomicStieltjesModel_moments] using
    gomesMomentQuotient_succ_abs_im_gt_iff (gomesAtomicStieltjesModel S w j) n z

/-- The normalized flux detects the upper half-plane and the exact observation-depth threshold. -/
theorem gomesAtomicStieltjes_flux_signature (S : Finset ℝ) (w : ℝ → ℝ) (j : ℕ) (n : ℕ) (z : ℂ) :
    (gomesMomentNormalizedFlux (gomesAtomicStieltjesModel S w j) n z).PosDef ↔ 0 < z.im ∧ n ≠ 0 :=
  gomesMomentNormalizedFlux_posDef_iff (gomesAtomicStieltjesModel S w j) n z

/-- A single fixed tensor entry measures the reciprocal mass of the original source. -/
theorem gomesAtomicStieltjes_mass_probe (S : Finset ℝ) (w : ℝ → ℝ) (j : ℕ) :
    gomesMomentNormalizedFlux (gomesAtomicStieltjesModel S w j) 0 Complex.I 0 0 = ((2/(stieltjesPerturbedSequence (gomesAtomicMoment S w) j) 0 : ℝ) : ℂ) := by
  rw [gomesMomentNormalizedFlux_mass_probe,gomesAtomicStieltjesModel_moments]

end GaloisForLFunctions.RHTower
