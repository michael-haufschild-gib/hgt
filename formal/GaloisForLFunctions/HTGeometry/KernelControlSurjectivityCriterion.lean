import GaloisForLFunctions.HTGeometry.WeightedJetControlSurjective

/-!
# A surjectivity criterion for kernel control maps

Surjectivity of a bounded-density control map splits into two parts.  One is measure-theoretic and
generic: annihilation of the range by a coefficient packet, tested on indicators, forces all set
integrals of the paired kernel to vanish, hence the pairing vanishes almost everywhere.  The other
is rigidity of the particular kernel: that an almost-everywhere vanishing pairing forces the
coefficients to vanish.

Only the second depends on the kernel.  The first is isolated here over an arbitrary measure space,
so that a new control map needs only its own rigidity lemma.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The indicator of a measurable set as a bounded density, over any measure space.  At exponent
`∞` boundedness is the only condition, so no finiteness of the set is required. -/
def indicatorLpTopGen (μ : Measure α) {S : Set α} (hS : MeasurableSet S) : Lp ℝ ⊤ μ :=
  (memLp_top_of_bound (f := S.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hS).aestronglyMeasurable 1
    (by
      filter_upwards with t
      by_cases h : t ∈ S
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h])).toLp _

theorem indicatorLpTopGen_coeFn (μ : Measure α) {S : Set α} (hS : MeasurableSet S) :
    indicatorLpTopGen μ hS =ᵐ[μ] S.indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _

/-- **Surjectivity from kernel rigidity.**  A control map represented on indicators by set integrals
of a family of integrable kernels is surjective as soon as no nonzero coefficient packet makes the
paired kernel have vanishing real part almost everywhere.

The measure-theoretic half is carried out here; the rigidity hypothesis is the only kernel-specific
input. -/
theorem surjective_of_kernel_ae_re_rigidity {σ : Type*} [Fintype σ]
    (μ : Measure α) (L : Lp ℝ ⊤ μ →ₗ[ℝ] (σ → ℂ))
    (Kern : α → σ → ℂ)
    (hKint : ∀ s : σ, Integrable (fun t => Kern t s) μ)
    (hrep : ∀ (S : Set α) (hS : MeasurableSet S) (s : σ),
      L (indicatorLpTopGen μ hS) s = ∫ t in S, Kern t s ∂μ)
    (hrig : ∀ c : σ → ℂ,
      (∀ᵐ t ∂μ, (∑ s : σ, c s * Kern t s).re = 0) → ∀ s, c s = 0) :
    Function.Surjective L := by
  classical
  apply surjective_of_forall_coefficients_eq_zero L
  intro c hc
  have hQint : Integrable (fun t => ∑ s : σ, c s * Kern t s) μ := by
    apply integrable_finsetSum
    intro s _
    exact (hKint s).const_mul (c s)
  -- Testing the annihilation on indicators makes every set integral vanish.
  have hset : ∀ S : Set α, MeasurableSet S → μ S < ⊤ →
      ∫ t in S, (∑ s : σ, c s * Kern t s).re ∂μ = 0 := by
    intro S hS _
    have hind := hc (indicatorLpTopGen μ hS)
    simp only [hrep S hS] at hind
    have hexch : ∑ s : σ, c s * ∫ t in S, Kern t s ∂μ =
        ∫ t in S, ∑ s : σ, c s * Kern t s ∂μ := by
      have hstep1 : ∑ s : σ, c s * ∫ t in S, Kern t s ∂μ =
          ∑ s : σ, ∫ t in S, c s * Kern t s ∂μ :=
        Finset.sum_congr rfl fun s _ => (integral_const_mul _ _).symm
      rw [hstep1, ← integral_finsetSum]
      intro s _
      exact ((hKint s).restrict).const_mul (c s)
    have hcomm : ∫ t in S, (∑ s : σ, c s * Kern t s).re ∂μ =
        (∫ t in S, ∑ s : σ, c s * Kern t s ∂μ).re :=
      Complex.reCLM.integral_comp_comm hQint.restrict
    rw [hcomm, ← hexch]
    exact hind
  have hae := Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero hQint.re hset
  exact hrig c (by filter_upwards [hae] with t ht using ht)

end

end GaloisForLFunctions.HTGeometry
