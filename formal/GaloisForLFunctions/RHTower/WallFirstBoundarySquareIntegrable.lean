import GaloisForLFunctions.RHTower.WallFirstBoundaryLaplace

/-!
# The first boundary term is square integrable

The first boundary term does not decay in the frequency, so its square integrability cannot come from
a power bound.  It comes instead from the Laplace representation: each semigroup slice acts on the
angular transform of the weighted block profile, whose frequency energy is `2π e^{-2sm}` times the
physical block energy, while the semigroup contributes `e^{-2(μ₀−m)s}` from the numerical floor
available above the threshold.  The two rates **add** to `μ₀`, and Minkowski's integral inequality in
the Laplace variable turns that into the factor `μ₀^{-1}`:

`‖first boundary‖_{L²(ray)} ≤ μ₀^{-1}·√(2π ∫‖g‖²)`.

The constant does not see the block, which is the whole point of the frequency threshold.

Minkowski needs genuine joint measurability of `(x,s) ↦ ‖e^{-sB(x)}Ψ(x,s)‖ₑ`.  The semigroup half is
jointly continuous, because the generator depends continuously on the frequency and the exponential
is continuous on the operator algebra; the slice half is a parametrised Bochner integral of a jointly
strongly measurable integrand, hence strongly measurable in the pair.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {T : X →L[ℂ] X}

omit [CompleteSpace X] in
theorem continuous_wallGenerator (T : X →L[ℂ] X) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (wallGenerator T σ) := by
  have hscal : Continuous (wallGeneratorScalar σ) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_wallGeneratorScalar hσ0 hσ1 x).continuousAt
  have h : Continuous fun x : ℝ =>
      wallGeneratorScalar σ x • (ContinuousLinearMap.id ℂ X) - (1 / 2 : ℂ) • T :=
    (hscal.smul continuous_const).sub continuous_const
  exact h

theorem continuous_semigroup_pair (T : X →L[ℂ] X) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous fun p : ℝ × ℝ => accretiveSemigroup (wallGenerator T σ p.1) p.2 := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  have hgen : Continuous fun p : ℝ × ℝ => (-p.2) • wallGenerator T σ p.1 :=
    (continuous_snd.neg).smul ((continuous_wallGenerator T hσ0 hσ1).comp continuous_fst)
  exact NormedSpace.exp_continuous.comp hgen

/-- The block slice cut to the terminal ray. -/
def cutSlice (g : ℝ → X) (A : Set ℝ) (x s : ℝ) : X :=
  A.indicator (fun y => blockSlice g s y) x

omit [CompleteSpace X] in
theorem stronglyMeasurable_blockSlice_pair {g : ℝ → X} (hg : StronglyMeasurable g) :
    StronglyMeasurable fun p : ℝ × ℝ => blockSlice g p.2 p.1 := by
  have hF : StronglyMeasurable fun q : (ℝ × ℝ) × ℝ =>
      Complex.exp (-(Complex.I) * (q.1.1 : ℂ) * (q.2 : ℂ))
        • (Real.exp (-(q.2 * q.1.2)) • g q.2) := by
    have h1 : Continuous fun q : (ℝ × ℝ) × ℝ =>
        Complex.exp (-(Complex.I) * (q.1.1 : ℂ) * (q.2 : ℂ)) := by fun_prop
    have h2 : Continuous fun q : (ℝ × ℝ) × ℝ => Real.exp (-(q.2 * q.1.2)) := by fun_prop
    have h3 : StronglyMeasurable fun q : (ℝ × ℝ) × ℝ => g q.2 :=
      hg.comp_measurable measurable_snd
    exact h1.stronglyMeasurable.smul (h2.stronglyMeasurable.smul h3)
  have hint := hF.integral_prod_right' (ν := (volume : Measure ℝ))
  have heq : (fun p : ℝ × ℝ => blockSlice g p.2 p.1)
      = fun p : ℝ × ℝ => ∫ L : ℝ, Complex.exp (-(Complex.I) * (p.1 : ℂ) * (L : ℂ))
          • (Real.exp (-(L * p.2)) • g L) := rfl
  rw [heq]
  exact hint

omit [CompleteSpace X] in
theorem stronglyMeasurable_cutSlice_pair {g : ℝ → X} (hg : StronglyMeasurable g)
    {A : Set ℝ} (hA : MeasurableSet A) :
    StronglyMeasurable fun p : ℝ × ℝ => cutSlice g A p.1 p.2 := by
  have hbase := stronglyMeasurable_blockSlice_pair hg
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 ∈ A} :=
    hA.preimage measurable_fst
  have heq : (fun p : ℝ × ℝ => cutSlice g A p.1 p.2)
      = fun p : ℝ × ℝ =>
        Set.indicator {q : ℝ × ℝ | q.1 ∈ A} (fun q : ℝ × ℝ => blockSlice g q.2 q.1) p := by
    funext p
    rw [cutSlice]
    by_cases hp : p.1 ∈ A
    · rw [Set.indicator_of_mem hp,
        Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | q.1 ∈ A} from hp)]
    · rw [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem (show p ∉ {q : ℝ × ℝ | q.1 ∈ A} from hp)]
  rw [heq]
  exact hbase.indicator hset

theorem measurable_semigroup_cutSlice {g : ℝ → X} (hg : StronglyMeasurable g)
    {A : Set ℝ} (hA : MeasurableSet A)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Measurable (Function.uncurry fun x s : ℝ =>
      ‖accretiveSemigroup (wallGenerator T σ x) s (cutSlice g A x s)‖ₑ) := by
  have hsem : StronglyMeasurable fun p : ℝ × ℝ => accretiveSemigroup (wallGenerator T σ p.1) p.2 :=
    (continuous_semigroup_pair T hσ0 hσ1).stronglyMeasurable
  have hcut := stronglyMeasurable_cutSlice_pair hg hA
  have hev : StronglyMeasurable fun p : ℝ × ℝ =>
      accretiveSemigroup (wallGenerator T σ p.1) p.2 (cutSlice g A p.1 p.2) := by
    have hcont : Continuous fun q : (X →L[ℂ] X) × X => q.1 q.2 :=
      isBoundedBilinearMap_apply.continuous
    exact hcont.comp_stronglyMeasurable (hsem.prodMk hcut)
  exact hev.enorm

/-! ## The square-integrability of the first boundary term -/

omit [InnerProductSpace ℂ X] [CompleteSpace X] in
theorem lintegral_enorm_sq_eq_ofReal_integral {f : ℝ → X}
    (hf : Integrable (fun x : ℝ => ‖f x‖ ^ 2) (volume : Measure ℝ)) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) = ENNReal.ofReal (∫ x : ℝ, ‖f x‖ ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- **`(20)`: the first boundary term is square integrable on the terminal ray**, with the
block-independent constant.  It does not decay, so the estimate comes entirely from the Laplace
representation: each semigroup slice carries the frequency energy `2π e^{-2sm}` of the weighted block
profile and the operator decay `e^{-2(μ₀−m)s}`, the two rates add to `μ₀`, and Minkowski in the
Laplace variable turns that into the factor `μ₀^{-1}`. -/
theorem lintegral_sq_firstBoundary_le {σ m μ₀ : ℝ} {A : Set ℝ} {g : ℝ → X}
    (hA : MeasurableSet A) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgm : StronglyMeasurable g)
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hfloor : ∀ x ∈ A, μ₀ - m ≤ wallFloor T σ x) :
    (∫⁻ x : ℝ, ‖(A).indicator (firstBoundary T g σ) x‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.sqrt ((2 * Real.pi) * ∫ L : ℝ, ‖g L‖ ^ 2) / μ₀) := by
  set K : ℝ := Real.sqrt ((2 * Real.pi) * ∫ L : ℝ, ‖g L‖ ^ 2) with hKdef
  have hEnn : (0 : ℝ) ≤ (2 * Real.pi) * ∫ L : ℝ, ‖g L‖ ^ 2 := by
    have : (0 : ℝ) ≤ ∫ L : ℝ, ‖g L‖ ^ 2 := integral_nonneg fun L => by positivity
    positivity
  have hKnn : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K ^ 2 = (2 * Real.pi) * ∫ L : ℝ, ‖g L‖ ^ 2 := Real.sq_sqrt hEnn
  have hgap : 0 < (μ₀ - m) + m := by linarith
  have hB : ∀ x ∈ A, ∀ u : X,
      (μ₀ - m) * ‖u‖ ^ 2 ≤ (inner ℂ (wallGenerator T σ x u) u).re := by
    intro x hx u
    have hbase := re_inner_wallGenerator_ge (T := T) hσ0 hσ1 x u
    have hfl := hfloor x hx
    nlinarith [sq_nonneg ‖u‖, hbase, hfl]
  have hcutsupp : ∀ s : ℝ, ∀ x, x ∉ A → cutSlice g A x s = 0 := by
    intro s x hx
    rw [cutSlice, Set.indicator_of_notMem hx]
  have hΦ : ∀ x : ℝ, ‖(A).indicator (firstBoundary T g σ) x‖ₑ
      ≤ ∫⁻ s in Ioi (0 : ℝ),
          ‖accretiveSemigroup (wallGenerator T σ x) s (cutSlice g A x s)‖ₑ := by
    intro x
    by_cases hx : x ∈ A
    · have hfl : μ₀ ≤ wallFloor T σ x + m := by
        have := hfloor x hx
        linarith
      rw [Set.indicator_of_mem hx, firstBoundary_eq_laplace hσ0 hσ1 hμ hg2 hsupp hfl]
      refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
      refine lintegral_congr fun s => ?_
      rw [cutSlice, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      simp
  have hslice : ∀ s : ℝ, 0 < s →
      (∫⁻ x : ℝ, ‖cutSlice g A x s‖ₑ ^ 2)
        ≤ ENNReal.ofReal (Real.exp (-(2 * s * m))) * ENNReal.ofReal (K ^ 2) := by
    intro s hs
    have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
    have hw1 : Integrable (blockWeighted g s) := integrable_blockWeighted hs.le hg1 hsupp
    have hw2 : MemLp (blockWeighted g s) 2 (volume : Measure ℝ) :=
      memLp_blockWeighted hs.le hg2 hsupp
    have hsqint : Integrable (fun x : ℝ => ‖blockSlice g s x‖ ^ 2) (volume : Measure ℝ) :=
      integrable_norm_sq_vectorAngularTransform hw1 hw2
    have hmono : (∫⁻ x : ℝ, ‖cutSlice g A x s‖ₑ ^ 2)
        ≤ ∫⁻ x : ℝ, ‖blockSlice g s x‖ₑ ^ 2 := by
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ A
      · rw [cutSlice, Set.indicator_of_mem hx]
      · rw [cutSlice, Set.indicator_of_notMem hx]
        simp
    refine hmono.trans ?_
    rw [lintegral_enorm_sq_eq_ofReal_integral hsqint, hKsq,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (integral_norm_sq_blockSlice_le hs.le hg2 hsupp)
  have hfin := lintegral_sq_blockLaplace_le hB hgap hKnn hcutsupp
    (measurable_semigroup_cutSlice hgm hA hσ0 hσ1) hΦ hslice
  have hsum : μ₀ - m + m = μ₀ := by ring
  rwa [hsum] at hfin

end GaloisForLFunctions.RHTower
