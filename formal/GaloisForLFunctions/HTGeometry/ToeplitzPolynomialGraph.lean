import GaloisForLFunctions.HTGeometry.GraphSaturationCore
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The analytic-polynomial graph on a circle measure

This module instantiates the abstract graph-saturation core for the polynomial synthesis map
from finitely supported coefficient sequences to `L²` of a finite circle measure.  It proves that
the joint annihilator may be tested on monomials alone.  The remaining singular-measure input is
the one-sided Fourier rigidity theorem; it is deliberately not encoded as an assumption about
the graph closure.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

noncomputable instance : MeasurableSpace Circle := borel Circle
instance : BorelSpace Circle := ⟨rfl⟩
instance : OpensMeasurableSpace Circle := ⟨le_rfl⟩

/-- The coefficient Hilbert space `ℓ²(ℕ)`. -/
abbrev CoefficientL2 := lp (fun _ : ℕ => ℂ) 2

/-- The canonical inclusion of finitely supported coefficient sequences into `ℓ²(ℕ)`. -/
noncomputable def finsuppCoefficientL2 : (ℕ →₀ ℂ) →ₗ[ℂ] CoefficientL2 :=
  Finsupp.lsum ℂ (fun n => lp.lsingle (E := fun _ : ℕ => ℂ) 2 n)

@[simp]
theorem finsuppCoefficientL2_single (n : ℕ) (c : ℂ) :
    finsuppCoefficientL2 (Finsupp.single n c) = lp.single 2 n c := by
  simp [finsuppCoefficientL2]

/-- Analytic monomials belong to `L²` of every finite circle measure. -/
theorem circleMonomial_memLp (mu : Measure Circle) [IsFiniteMeasure mu] (n : ℕ) :
    MemLp (fun z : Circle => (z : ℂ) ^ n) 2 mu :=
  MemLp.of_bound
      ((by fun_prop : Continuous (fun z : Circle => (z : ℂ) ^ n)).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun z => by simp [norm_pow])

/-- The `n`th analytic monomial as an element of `L²(μ)`. -/
noncomputable def circleMonomialLp (mu : Measure Circle) [IsFiniteMeasure mu] (n : ℕ) :
    Lp ℂ 2 mu :=
  MemLp.toLp (fun z : Circle => (z : ℂ) ^ n) (circleMonomial_memLp mu n)

theorem circleMonomialLp_coeFn_ae (mu : Measure Circle) [IsFiniteMeasure mu] (n : ℕ) :
    ⇑(circleMonomialLp mu n) =ᵐ[mu] fun z : Circle => (z : ℂ) ^ n :=
  (circleMonomial_memLp mu n).coeFn_toLp

/-- The monomial `L²` inner product is its corresponding weighted Fourier integral. -/
theorem circleMonomialLp_inner (mu : Measure Circle) [IsFiniteMeasure mu]
    (n : ℕ) (y : Lp ℂ 2 mu) :
    inner ℂ (circleMonomialLp mu n) y =
      ∫ z : Circle, ⇑y z * (starRingEnd ℂ) ((z : ℂ) ^ n) ∂mu := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleMonomialLp_coeFn_ae mu n] with z hz
  rw [hz, RCLike.inner_apply]

/-- Analytic-polynomial synthesis in `L²(μ)`. -/
noncomputable def polynomialSynthesisL2 (mu : Measure Circle) [IsFiniteMeasure mu] :
    (ℕ →₀ ℂ) →ₗ[ℂ] Lp ℂ 2 mu :=
  Finsupp.lsum ℂ (fun n => LinearMap.toSpanSingleton ℂ _ (circleMonomialLp mu n))

@[simp]
theorem polynomialSynthesisL2_single (mu : Measure Circle) [IsFiniteMeasure mu]
    (n : ℕ) (c : ℂ) :
    polynomialSynthesisL2 mu (Finsupp.single n c) = c • circleMonomialLp mu n := by
  simp [polynomialSynthesisL2]

/-- Testing the joint annihilator on the monomial basis is equivalent to testing it on every
finitely supported polynomial. -/
theorem polynomial_annihilator_of_monomial_annihilator
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (x : CoefficientL2) (y : Lp ℂ 2 mu)
    (hmono : ∀ n : ℕ,
      inner ℂ (lp.single 2 n 1) x + inner ℂ (circleMonomialLp mu n) y = 0) :
    ∀ d : ℕ →₀ ℂ,
      inner ℂ (finsuppCoefficientL2 d) x + inner ℂ (polynomialSynthesisL2 mu d) y = 0 := by
  intro d
  induction d using Finsupp.induction with
  | zero => simp
  | single_add n c d hn hc ih =>
      have hsingle :
          (lp.single (E := fun _ : ℕ => ℂ) 2 n c : CoefficientL2) =
            c • lp.single 2 n 1 := by
        apply lp.ext
        funext j
        simp [lp.single_apply, Pi.single_apply]
      simp only [map_add, finsuppCoefficientL2_single, polynomialSynthesisL2_single,
        inner_add_left, inner_smul_left]
      rw [hsingle]
      simp only [inner_smul_left]
      calc
        (starRingEnd ℂ) c * inner ℂ (lp.single 2 n 1) x +
              inner ℂ (finsuppCoefficientL2 d) x +
            ((starRingEnd ℂ) c * inner ℂ (circleMonomialLp mu n) y +
              inner ℂ (polynomialSynthesisL2 mu d) y) =
            (starRingEnd ℂ) c *
                (inner ℂ (lp.single 2 n 1) x + inner ℂ (circleMonomialLp mu n) y) +
              (inner ℂ (finsuppCoefficientL2 d) x +
                inner ℂ (polynomialSynthesisL2 mu d) y) := by ring
        _ = 0 := by rw [hmono n, ih]; ring

/-- **Polynomial graph-saturation reduction.** It suffices to prove that the monomial joint
annihilator is trivial.  This is the exact interface at which one-sided Fourier rigidity enters. -/
theorem polynomialGraph_closure_eq_top_of_monomial_annihilator
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (hann : ∀ x : CoefficientL2, ∀ y : Lp ℂ 2 mu,
      (∀ n : ℕ,
        inner ℂ (lp.single 2 n 1) x + inner ℂ (circleMonomialLp mu n) y = 0) →
      x = 0 ∧ y = 0) :
    (linearGraphSubmodule finsuppCoefficientL2 (polynomialSynthesisL2 mu)).topologicalClosure =
      ⊤ := by
  apply linearGraphSubmodule_closure_eq_top_of_annihilator
  intro x y hall
  apply hann x y
  intro n
  simpa using hall (Finsupp.single n 1)

/-- Full-product closure of the analytic-polynomial graph is exactly monomial-annihilator
rigidity.  This gives a bidirectional formal boundary for the missing Fourier theorem. -/
theorem polynomialGraph_closure_eq_top_iff_monomial_annihilator
    (mu : Measure Circle) [IsFiniteMeasure mu] :
    (linearGraphSubmodule finsuppCoefficientL2 (polynomialSynthesisL2 mu)).topologicalClosure =
        ⊤ ↔
      ∀ x : CoefficientL2, ∀ y : Lp ℂ 2 mu,
        (∀ n : ℕ,
          inner ℂ (lp.single 2 n 1) x + inner ℂ (circleMonomialLp mu n) y = 0) →
        x = 0 ∧ y = 0 := by
  constructor
  · intro hclosure x y hmono
    have hall := polynomial_annihilator_of_monomial_annihilator mu x y hmono
    exact (linearGraphSubmodule_closure_eq_top_iff_annihilator
      finsuppCoefficientL2 (polynomialSynthesisL2 mu)).mp hclosure x y hall
  · exact polynomialGraph_closure_eq_top_of_monomial_annihilator mu

/-- The exact one-sided Riesz-brothers rigidity property needed by graph saturation: an `L²(μ)`
function whose analytic monomial coefficients form an `ℓ²` sequence must vanish. -/
def IsOneSidedFourierRigid (mu : Measure Circle) [IsFiniteMeasure mu] : Prop :=
  ∀ y : Lp ℂ 2 mu, Memℓp (fun n : ℕ => inner ℂ (circleMonomialLp mu n) y) 2 → y = 0

/-- The algebraic span of analytic monomials in `L²(μ)`. -/
def analyticMonomialSpan (mu : Measure Circle) [IsFiniteMeasure mu] :
    Submodule ℂ (Lp ℂ 2 mu) :=
  Submodule.span ℂ (Set.range (circleMonomialLp mu))

/-- One-sided Fourier rigidity forces analytic polynomials to be dense in `L²(μ)`.  This is
the exact completeness input behind surjectivity of the coherently repaired orthonormal-polynomial
map. -/
theorem analyticMonomialSpan_closure_eq_top_of_oneSidedFourierRigid
    (mu : Measure Circle) [IsFiniteMeasure mu] (hrigid : IsOneSidedFourierRigid mu) :
    (analyticMonomialSpan mu).topologicalClosure = ⊤ := by
  have horth : (analyticMonomialSpan mu)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    apply hrigid y
    have hzero : (fun n : ℕ => inner ℂ (circleMonomialLp mu n) y) = 0 := by
      funext n
      exact hy (circleMonomialLp mu n)
        (Submodule.subset_span (Set.mem_range_self n))
    rw [hzero]
    exact zero_memℓp
  calc
    (analyticMonomialSpan mu).topologicalClosure = (analyticMonomialSpan mu)ᗮᗮ :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = (⊥ : Submodule ℂ (Lp ℂ 2 mu))ᗮ := by rw [horth]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- One-sided Fourier rigidity kills the polynomial graph's joint annihilator. -/
theorem monomial_annihilator_trivial_of_oneSidedFourierRigid
    (mu : Measure Circle) [IsFiniteMeasure mu] (hrigid : IsOneSidedFourierRigid mu)
    (x : CoefficientL2) (y : Lp ℂ 2 mu)
    (hmono : ∀ n : ℕ,
      inner ℂ (lp.single 2 n 1) x + inner ℂ (circleMonomialLp mu n) y = 0) :
    x = 0 ∧ y = 0 := by
  have hcoeff : (fun n : ℕ => inner ℂ (circleMonomialLp mu n) y) = -(⇑x) := by
    funext n
    have hn := hmono n
    rw [lp.inner_single_left] at hn
    simp only [RCLike.inner_apply, map_one, mul_one] at hn
    exact eq_neg_of_add_eq_zero_right hn
  have hy : y = 0 := hrigid y (hcoeff ▸ (lp.memℓp x).neg)
  subst y
  constructor
  · apply lp.ext
    funext n
    have hn := hmono n
    rw [lp.inner_single_left] at hn
    simpa [RCLike.inner_apply] using hn
  · rfl

/-- The analytic-polynomial graph saturates whenever the exact one-sided Fourier rigidity input
holds.  Proving this rigidity from pure singularity is the remaining F. and M. Riesz obligation. -/
theorem polynomialGraph_closure_eq_top_of_oneSidedFourierRigid
    (mu : Measure Circle) [IsFiniteMeasure mu] (hrigid : IsOneSidedFourierRigid mu) :
    (linearGraphSubmodule finsuppCoefficientL2 (polynomialSynthesisL2 mu)).topologicalClosure =
      ⊤ :=
  polynomialGraph_closure_eq_top_of_monomial_annihilator mu
    (monomial_annihilator_trivial_of_oneSidedFourierRigid mu hrigid)

end

end GaloisForLFunctions.HTGeometry
