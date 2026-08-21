import Mathlib

/-!
# The orbit form is the energy of the periodization

§VII (11) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `∫ |∑_{q ∈ O_S^*} f(qx)|² |x| d^*x = ∑_{O_S^*} ⟨f, U(q) f⟩_A`.

The algebraic heart of that identity is pointwise and needs no measure theory at all: expanding
the square of an absolutely convergent orbit sum and reindexing the second factor by
`r = q p` turns it into the double orbit sum whose `q`-slice is the ambient correlation
`⟨f, U(q) f⟩`.  Integrating over a fundamental domain and unfolding — mathlib's
`MeasureTheory.IsFundamentalDomain.integral_eq_tsum` — is then exactly (11).  This file supplies
the pointwise identity, which is what makes the orbit form of `ConnesOrbitFormFourier` the inner
product of the quotient space.
-/

open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {G X : Type*} [Group G] [MulAction G X]

/-- Conjugate-square of a complex number as a real square. -/
theorem connes_conj_mul_self (z : ℂ) :
    (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq z

/-- The reindexing `(q, p) ↦ (p, q p)` of the double orbit. -/
def connesOrbitReindex : G × G ≃ G × G where
  toFun z := (z.2, z.1 * z.2)
  invFun z := (z.2 * z.1⁻¹, z.1)
  left_inv z := by
    ext
    · exact mul_inv_cancel_right z.1 z.2
    · rfl
  right_inv z := by
    ext
    · rfl
    · exact inv_mul_cancel_right z.2 z.1

/-- **§VII (11), pointwise core.**  The squared modulus of the periodization at a point is the
double orbit sum of the correlation. -/
theorem connes_periodization_normSq_eq_orbitSum (f : X → ℂ) (x : X)
    (hs : Summable fun p : G => ‖f (p • x)‖) :
    ((‖∑' p : G, f (p • x)‖ ^ 2 : ℝ) : ℂ)
      = ∑' z : G × G, (starRingEnd ℂ) (f (z.2 • x)) * f ((z.1 * z.2) • x) := by
  have hsc : Summable fun p : G => f (p • x) := hs.of_norm
  have hconjnorm : Summable fun p : G => ‖(starRingEnd ℂ) (f (p • x))‖ := by
    simpa using hs
  have hprod := tsum_mul_tsum_of_summable_norm (f := fun p : G => (starRingEnd ℂ) (f (p • x)))
    (g := fun r : G => f (r • x)) hconjnorm hs
  have hconjsum : (∑' p : G, (starRingEnd ℂ) (f (p • x)))
      = (starRingEnd ℂ) (∑' p : G, f (p • x)) := by
    exact (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap.map_tsum hsc).symm
  rw [← connes_conj_mul_self, ← hconjsum, hprod]
  exact ((connesOrbitReindex (G := G)).tsum_eq
    (fun z : G × G => (starRingEnd ℂ) (f (z.1 • x)) * f (z.2 • x))).symm

/-- **§VII (11).**  The orbit form of the ambient correlation is the energy of the periodization
over a fundamental domain.  This is what identifies the orbit form of `ConnesOrbitFormFourier`
with the inner product of the quotient Hilbert space. -/
theorem connes_orbitForm_eq_fundamentalDomain_energy
    [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasurableSpace G] [MeasurableSMul G X] [MeasureTheory.SMulInvariantMeasure G X μ]
    [Countable G] {F : Set X} (hF : MeasureTheory.IsFundamentalDomain G F μ) (f : X → ℂ)
    (hq : ∀ q : G, MeasureTheory.Integrable
      (fun x => (starRingEnd ℂ) (f x) * f (q • x)) μ)
    (hint : ∀ z : G × G, MeasureTheory.IntegrableOn
      (fun x => (starRingEnd ℂ) (f (z.2 • x)) * f ((z.1 * z.2) • x)) F μ)
    (hsum : Summable fun z : G × G =>
      ∫ x in F, ‖(starRingEnd ℂ) (f (z.2 • x)) * f ((z.1 * z.2) • x)‖ ∂μ)
    (hpt : ∀ x : X, Summable fun p : G => ‖f (p • x)‖) :
    (∑' q : G, ∫ x, (starRingEnd ℂ) (f x) * f (q • x) ∂μ)
      = ∫ x in F, ((‖∑' p : G, f (p • x)‖ ^ 2 : ℝ) : ℂ) ∂μ := by
  have hstep1 : ∀ q : G, (∫ x, (starRingEnd ℂ) (f x) * f (q • x) ∂μ)
      = ∑' p : G, ∫ x in F, (starRingEnd ℂ) (f (p • x)) * f ((q * p) • x) ∂μ := by
    intro q
    rw [hF.integral_eq_tsum' _ (hq q)]
    have hre := (Equiv.inv G).tsum_eq
      (fun p : G => ∫ x in F, (starRingEnd ℂ) (f (p • x)) * f ((q * p) • x) ∂μ)
    rw [← hre]
    refine tsum_congr fun g => ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (starRingEnd ℂ) (f (g⁻¹ • x)) * f (q • g⁻¹ • x)
      = (starRingEnd ℂ) (f (g⁻¹ • x)) * f ((q * g⁻¹) • x)
    rw [mul_smul]
  have hprodsummable : Summable fun z : G × G =>
      ∫ x in F, (starRingEnd ℂ) (f (z.2 • x)) * f ((z.1 * z.2) • x) ∂μ := by
    refine Summable.of_norm ?_
    refine hsum.of_nonneg_of_le (fun z => norm_nonneg _) (fun z => ?_)
    exact MeasureTheory.norm_integral_le_integral_norm _
  calc (∑' q : G, ∫ x, (starRingEnd ℂ) (f x) * f (q • x) ∂μ)
      = ∑' q : G, ∑' p : G,
          ∫ x in F, (starRingEnd ℂ) (f (p • x)) * f ((q * p) • x) ∂μ :=
        tsum_congr hstep1
    _ = ∑' z : G × G,
          ∫ x in F, (starRingEnd ℂ) (f (z.2 • x)) * f ((z.1 * z.2) • x) ∂μ :=
        (hprodsummable.tsum_prod).symm
    _ = ∫ x in F, ∑' z : G × G,
          (starRingEnd ℂ) (f (z.2 • x)) * f ((z.1 * z.2) • x) ∂μ :=
        MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum
    _ = ∫ x in F, ((‖∑' p : G, f (p • x)‖ ^ 2 : ℝ) : ℂ) ∂μ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact (connes_periodization_normSq_eq_orbitSum f x (hpt x)).symm

end

end GaloisForLFunctions.RHTower
