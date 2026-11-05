import GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry.TheWindowEdgeCarriesTheNewestPrime
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomIsExactlyLogarithmic
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms

/-!
# The window energy has no trace

The archimedean part of Weil's form is the logarithmic jump energy
`𝒥(f) = ∫_0^∞ ω(x) ∫ (f(u) − f(u + x))² du dx`, `ω(x) ~ 1/(2x)`. This module is the trace theory of
review §2.7 Q5: what a window certificate can read at the boundary of `[a, b]`.

* **Regional–edge decomposition** (`levyEnergy_eq_regional_add_edge`). For `f` vanishing off
  `[a, b]`, `𝒥(f) = 𝒥_reg(f) + 𝒦(f)`: the regional energy of the jumps with both ends in `[a, b]`,
  and the **edge killing energy** `𝒦(f) = ∫_0^∞ ω(x)(m_a(x) + m_b(x)) dx`, where `m_a(x)`, `m_b(x)`
  are the masses of `f²` within distance `x` of the two edges. The boundary enters `𝒥` only through
  `𝒦`, a logarithmically weighted edge mass (`∫ f²(Ω(u − a) + Ω(b − u))` by Fubini,
  `Ω(δ) = ∫_δ^∞ ω ~ ½log(1/δ)`); `𝒦 ≤ 𝒥` is the edge Hardy inequality, and every prime reflection,
  which lives on an edge sliver, is an edge datum (`levyTail_mul_leftEdgeMass_le_edgeKilling`).
* **The plateau is pure edge** (`levyEnergy_indicator`, `edgeKilling_indicator`). The indicator of
  `[a, b]` has `∫(1(u) − 1(u + x))² du = 2min(x, b − a)`, so its energy is finite and equals its
  edge killing energy `∫_0^∞ ω(x)·2min(x, b − a) dx`: a window test may jump at the edge.
* **No point traces** (`exists_spike`). For every point `x₀` and `ε > 0` there is a `C²` spike with
  `g(x₀) = 1`, support in `[x₀ − ε, x₀ + ε]`, and `‖g‖₂², ‖g‖₁, 𝒥(g) ≤ ε`: point evaluation is
  unbounded in the energy norm, at the edge as anywhere else. A certificate continuous in the energy
  norm sees no boundary values; its edge data are edge masses weighted by `Ω`.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower

/-! ### Three-term integrals -/

theorem integral_add_three {A B C : ℝ → ℝ} {μ : Measure ℝ} (hA : Integrable A μ)
    (hB : Integrable B μ) (hC : Integrable C μ) :
    ∫ x, A x + B x + C x ∂μ = (∫ x, A x ∂μ) + (∫ x, B x ∂μ) + ∫ x, C x ∂μ := by
  rw [integral_add (f := fun x => A x + B x) (hA.add hB) hC, integral_add hA hB]

theorem integral_sub_add_three {A B C : ℝ → ℝ} {μ : Measure ℝ} (hA : Integrable A μ)
    (hB : Integrable B μ) (hC : Integrable C μ) :
    ∫ x, A x - B x + C x ∂μ = (∫ x, A x ∂μ) - (∫ x, B x ∂μ) + ∫ x, C x ∂μ := by
  rw [integral_add (f := fun x => A x - B x) (hA.sub hB) hC, integral_sub hA hB]

theorem integral_add_sub_three {A B C : ℝ → ℝ} {μ : Measure ℝ} (hA : Integrable A μ)
    (hB : Integrable B μ) (hC : Integrable C μ) :
    ∫ x, A x + B x - C x ∂μ = (∫ x, A x ∂μ) + (∫ x, B x ∂μ) - ∫ x, C x ∂μ := by
  rw [integral_sub (f := fun x => A x + B x) (hA.add hB) hC, integral_add hA hB]

/-! ### Edge masses and the regional jump -/

/-- Mass of `f²` within distance `x` of the right edge `b`. -/
def rightEdgeMass (f : ℝ → ℝ) (b x : ℝ) : ℝ := ∫ u in Ioi (b - x), f u ^ 2

/-- Mass of `f²` within distance `x` of the left edge `a`. -/
def leftEdgeMass (f : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ u in Iio (a + x), f u ^ 2

/-- The regional jump of length `x`: jumps `u ↦ u + x` with both ends in `[a, b]`. -/
def regionalJump (f : ℝ → ℝ) (a b x : ℝ) : ℝ := ∫ u in Icc a (b - x), (f u - f (u + x)) ^ 2

/-- The regional energy of `f` on `[a, b]`. -/
def regionalEnergy (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), archLevyDensity x * regionalJump f a b x

/-- The edge killing energy of `f` on `[a, b]`. -/
def edgeKilling (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), archLevyDensity x * (leftEdgeMass f a x + rightEdgeMass f b x)

variable {f : ℝ → ℝ} {a b : ℝ}

/-- Pointwise split of a jump of length `x > 0` for `f` vanishing off `[a, b]`: regional, leaving
through `b`, or entering through `a`. -/
theorem sub_shift_sq_eq_split (hf : ∀ u, u ∉ Icc a b → f u = 0) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    (f u - f (u + x)) ^ 2 =
      (Icc a (b - x)).indicator (fun u => (f u - f (u + x)) ^ 2) u +
        (Ioi (b - x)).indicator (fun u => f u ^ 2) u +
        (Iio a).indicator (fun u => f (u + x) ^ 2) u := by
  simp only [Set.indicator_apply, mem_Icc, mem_Ioi, mem_Iio]
  by_cases h1 : b - x < u
  · have hR : ¬ (a ≤ u ∧ u ≤ b - x) := fun h => absurd h.2 (not_le.mpr h1)
    have hux : f (u + x) = 0 := hf _ fun h => by linarith [h.2]
    rw [if_neg hR, if_pos h1, hux]
    by_cases h2 : u < a
    · rw [if_pos h2, hf u fun h => by linarith [h.1]]
      ring
    · rw [if_neg h2]
      ring
  · have h1' : u ≤ b - x := not_lt.mp h1
    rw [if_neg h1]
    by_cases h2 : u < a
    · rw [if_neg (fun h : a ≤ u ∧ u ≤ b - x => absurd h.1 (not_le.mpr h2)), if_pos h2,
        hf u fun h => by linarith [h.1]]
      ring
    · rw [if_pos ⟨not_lt.mp h2, h1'⟩, if_neg h2]
      ring

theorem integrable_sq_of_cont (hfc : Continuous f) (hfs : HasCompactSupport f) :
    Integrable fun u => f u ^ 2 :=
  SpacingScaleHarmonicAnalysis.integrable_sq_of_continuous hfc hfs

/-- Entering through `a` is the left edge mass. -/
theorem integral_Iio_shift_eq_leftEdgeMass (x : ℝ) :
    ∫ u, (Iio a).indicator (fun u => f (u + x) ^ 2) u = leftEdgeMass f a x := by
  have h : (fun u => (Iio a).indicator (fun u => f (u + x) ^ 2) u) =
      fun u => (Iio (a + x)).indicator (fun v => f v ^ 2) (u + x) := by
    funext u
    by_cases hu : u < a
    · rw [indicator_of_mem (show u ∈ Iio a from hu),
        indicator_of_mem (show u + x ∈ Iio (a + x) by simp [hu])]
    · rw [indicator_of_notMem (show u ∉ Iio a from hu),
        indicator_of_notMem (show u + x ∉ Iio (a + x) by simpa using hu)]
  rw [h, integral_add_right_eq_self (μ := volume)
    (fun v => (Iio (a + x)).indicator (fun v => f v ^ 2) v) x,
    integral_indicator measurableSet_Iio]
  rfl

/-- **The jump integrand splits**: `∫(f(u) − f(u + x))² = regional + m_b(x) + m_a(x)`. -/
theorem integral_sub_shift_sq_eq (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hf : ∀ u, u ∉ Icc a b → f u = 0) {x : ℝ} (hx : 0 < x) :
    ∫ u, (f u - f (u + x)) ^ 2 =
      regionalJump f a b x + rightEdgeMass f b x + leftEdgeMass f a x := by
  have hsq := integrable_sq_of_cont hfc hfs
  have hsh : Integrable fun u => f (u + x) ^ 2 := hsq.comp_add_right x
  have hJ : Integrable fun u => (f u - f (u + x)) ^ 2 :=
    (SpacingScaleHarmonicAnalysis.integrable_sub_shift_mul hfc hfs hfc x).congr
      (Eventually.of_forall fun u => (sq _).symm)
  have i1 : Integrable ((Icc a (b - x)).indicator fun u => (f u - f (u + x)) ^ 2) :=
    hJ.indicator measurableSet_Icc
  have i2 : Integrable ((Ioi (b - x)).indicator fun u => f u ^ 2) := hsq.indicator measurableSet_Ioi
  have i3 : Integrable ((Iio a).indicator fun u => f (u + x) ^ 2) := hsh.indicator measurableSet_Iio
  rw [integral_congr_ae (Eventually.of_forall (sub_shift_sq_eq_split hf hx)),
    integral_add_three i1 i2 i3, integral_indicator measurableSet_Icc,
    integral_indicator measurableSet_Ioi, integral_Iio_shift_eq_leftEdgeMass]
  rfl

theorem rightEdgeMass_nonneg (f : ℝ → ℝ) (b x : ℝ) : 0 ≤ rightEdgeMass f b x :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _

theorem leftEdgeMass_nonneg (f : ℝ → ℝ) (a x : ℝ) : 0 ≤ leftEdgeMass f a x :=
  setIntegral_nonneg measurableSet_Iio fun _ _ => sq_nonneg _

theorem regionalJump_nonneg (f : ℝ → ℝ) (a b x : ℝ) : 0 ≤ regionalJump f a b x :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _

theorem monotone_rightEdgeMass (hfc : Continuous f) (hfs : HasCompactSupport f) (b : ℝ) :
    Monotone (rightEdgeMass f b) := fun x y hxy =>
  setIntegral_mono_set (integrable_sq_of_cont hfc hfs).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun u (hu : u ∈ Ioi (b - x)) => (show b - y < u by
      have : b - x < u := hu
      linarith))

theorem monotone_leftEdgeMass (hfc : Continuous f) (hfs : HasCompactSupport f) (a : ℝ) :
    Monotone (leftEdgeMass f a) := fun x y hxy =>
  setIntegral_mono_set (integrable_sq_of_cont hfc hfs).integrableOn
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun u (hu : u ∈ Iio (a + x)) => (show u < a + y by
      have : u < a + x := hu
      linarith))

theorem measurable_archLevyDensity : Measurable archLevyDensity := by
  unfold archLevyDensity
  fun_prop

/-- A nonnegative monotone mass dominated by the Lévy integrand is Lévy-integrable. -/
theorem integrableOn_mul_of_monotone_le (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    {m : ℝ → ℝ} (hm : Monotone m) (h0 : ∀ x, 0 ≤ m x)
    (hle : ∀ x, 0 < x → m x ≤ ∫ u, (f u - f (u + x)) ^ 2) :
    IntegrableOn (fun x => archLevyDensity x * m x) (Ioi 0) := by
  refine (integrableOn_levyIntegrand hf hfs).mono'
    ((measurable_archLevyDensity.mul hm.measurable).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  have hω := (archLevyDensity_pos (show (0 : ℝ) < x from hx)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hω (h0 x))]
  exact mul_le_mul_of_nonneg_left (hle x hx) hω

theorem integrableOn_rightEdge (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc a b → f u = 0) :
    IntegrableOn (fun x => archLevyDensity x * rightEdgeMass f b x) (Ioi 0) :=
  integrableOn_mul_of_monotone_le hf hfs (monotone_rightEdgeMass hf.continuous hfs b)
    (rightEdgeMass_nonneg f b) fun x hx => by
      rw [integral_sub_shift_sq_eq hf.continuous hfs hab hx]
      linarith [regionalJump_nonneg f a b x, leftEdgeMass_nonneg f a x]

theorem integrableOn_leftEdge (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc a b → f u = 0) :
    IntegrableOn (fun x => archLevyDensity x * leftEdgeMass f a x) (Ioi 0) :=
  integrableOn_mul_of_monotone_le hf hfs (monotone_leftEdgeMass hf.continuous hfs a)
    (leftEdgeMass_nonneg f a) fun x hx => by
      rw [integral_sub_shift_sq_eq hf.continuous hfs hab hx]
      linarith [regionalJump_nonneg f a b x, rightEdgeMass_nonneg f b x]

/-- The right-edge part of the killing energy is at most the edge killing energy. -/
theorem rightEdgeKilling_le_edgeKilling (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc a b → f u = 0) :
    ∫ x in Ioi (0 : ℝ), archLevyDensity x * rightEdgeMass f b x ≤ edgeKilling f a b := by
  unfold edgeKilling
  refine setIntegral_mono_on (integrableOn_rightEdge hf hfs hab)
    ((integrableOn_leftEdge hf hfs hab).add (integrableOn_rightEdge hf hfs hab) |>.congr_fun
      (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi) measurableSet_Ioi fun x hx => ?_
  have hω := (archLevyDensity_pos (show (0 : ℝ) < x from hx)).le
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (leftEdgeMass_nonneg f a x)) hω

/-- **Regional–edge decomposition of the window energy.** For a `C²` test vanishing off `[a, b]`,
`𝒥(f) = 𝒥_reg(f) + 𝒦(f)`. -/
theorem levyEnergy_eq_regional_add_edge (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc a b → f u = 0) :
    levyEnergy f = regionalEnergy f a b + edgeKilling f a b := by
  have hfc := hf.continuous
  have hsplit : ∀ x, 0 < x → ∫ u, (f u - f (u + x)) ^ 2 =
      regionalJump f a b x + rightEdgeMass f b x + leftEdgeMass f a x :=
    fun x hx => integral_sub_shift_sq_eq hfc hfs hab hx
  have hR := integrableOn_mul_of_monotone_le hf hfs (monotone_rightEdgeMass hfc hfs b)
    (rightEdgeMass_nonneg f b) fun x hx => by
      rw [hsplit x hx]
      linarith [regionalJump_nonneg f a b x, leftEdgeMass_nonneg f a x]
  have hL := integrableOn_mul_of_monotone_le hf hfs (monotone_leftEdgeMass hfc hfs a)
    (leftEdgeMass_nonneg f a) fun x hx => by
      rw [hsplit x hx]
      linarith [regionalJump_nonneg f a b x, rightEdgeMass_nonneg f b x]
  have hT := integrableOn_levyIntegrand hf hfs
  have hreg : IntegrableOn (fun x => archLevyDensity x * regionalJump f a b x) (Ioi 0) := by
    refine ((hT.sub hR).sub hL).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [hsplit x hx]
    ring
  have hpt : EqOn (fun x => archLevyDensity x * ∫ u, (f u - f (u + x)) ^ 2)
      (fun x => archLevyDensity x * regionalJump f a b x +
        archLevyDensity x * (leftEdgeMass f a x + rightEdgeMass f b x)) (Ioi 0) := by
    intro x hx
    try simp only
    rw [hsplit x hx]
    ring
  unfold levyEnergy regionalEnergy edgeKilling
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hreg]
  exact (hL.add hR).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi

theorem regionalEnergy_nonneg (f : ℝ → ℝ) (a b : ℝ) : 0 ≤ regionalEnergy f a b :=
  setIntegral_nonneg measurableSet_Ioi fun x hx =>
    mul_nonneg (archLevyDensity_pos hx).le (regionalJump_nonneg f a b x)

theorem edgeKilling_nonneg (f : ℝ → ℝ) (a b : ℝ) : 0 ≤ edgeKilling f a b :=
  setIntegral_nonneg measurableSet_Ioi fun x hx =>
    mul_nonneg (archLevyDensity_pos hx).le
      (add_nonneg (leftEdgeMass_nonneg f a x) (rightEdgeMass_nonneg f b x))

/-- **Edge Hardy inequality**: the edge killing energy is at most the window energy. -/
theorem edgeKilling_le_levyEnergy (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc a b → f u = 0) : edgeKilling f a b ≤ levyEnergy f := by
  rw [levyEnergy_eq_regional_add_edge hf hfs hab]
  linarith [regionalEnergy_nonneg f a b]

/-- The edge killing energy dominates `Ω(δ)` times the mass within `δ` of the left edge: prime
reflections, which live on edge slivers, are edge data. -/
theorem levyTail_mul_leftEdgeMass_le_edgeKilling (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc a b → f u = 0) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in Ioi δ, archLevyDensity x) * leftEdgeMass f a δ ≤ edgeKilling f a b := by
  have hfc := hf.continuous
  have hsplit : ∀ x, 0 < x → ∫ u, (f u - f (u + x)) ^ 2 =
      regionalJump f a b x + rightEdgeMass f b x + leftEdgeMass f a x :=
    fun x hx => integral_sub_shift_sq_eq hfc hfs hab hx
  have hL := integrableOn_mul_of_monotone_le hf hfs (monotone_leftEdgeMass hfc hfs a)
    (leftEdgeMass_nonneg f a) fun x hx => by
      rw [hsplit x hx]
      linarith [regionalJump_nonneg f a b x, rightEdgeMass_nonneg f b x]
  have hR := integrableOn_mul_of_monotone_le hf hfs (monotone_rightEdgeMass hfc hfs b)
    (rightEdgeMass_nonneg f b) fun x hx => by
      rw [hsplit x hx]
      linarith [regionalJump_nonneg f a b x, leftEdgeMass_nonneg f a x]
  have hsub : (fun x => (Ioi δ).indicator archLevyDensity x * leftEdgeMass f a δ) ≤ᵐ[volume.restrict (Ioi 0)]
      fun x => archLevyDensity x * (leftEdgeMass f a x + rightEdgeMass f b x) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    have hω := (archLevyDensity_pos (show (0 : ℝ) < x from hx)).le
    beta_reduce
    by_cases hxδ : x ∈ Ioi δ
    · rw [indicator_of_mem hxδ]
      exact mul_le_mul_of_nonneg_left
        (le_add_of_le_of_nonneg (monotone_leftEdgeMass hfc hfs a (le_of_lt hxδ))
          (rightEdgeMass_nonneg f b x)) hω
    · rw [indicator_of_notMem hxδ, zero_mul]
      exact mul_nonneg hω (add_nonneg (leftEdgeMass_nonneg f a x) (rightEdgeMass_nonneg f b x))
  have hint : IntegrableOn (fun x => (Ioi δ).indicator archLevyDensity x * leftEdgeMass f a δ)
      (Ioi 0) := by
    refine Integrable.mul_const ?_ _
    refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi hδ.le)]
    exact WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hδ
  have h := integral_mono_ae hint (hL.add hR |>.congr_fun (fun x _ => by simp only [Pi.add_apply]; ring)
    measurableSet_Ioi) hsub
  unfold edgeKilling
  refine le_trans (le_of_eq ?_) h
  rw [integral_mul_const, setIntegral_indicator measurableSet_Ioi,
    inter_eq_self_of_subset_right (Ioi_subset_Ioi hδ.le)]

/-! ### The plateau is pure edge -/

/-- The jump integrand of the indicator of `[a, b]`: `|[a, b] Δ ([a, b] − x)| = 2min(x, b − a)`. -/
theorem integral_indicator_sub_shift_sq (hab : a ≤ b) {x : ℝ} (hx : 0 ≤ x) :
    ∫ u, ((Icc a b).indicator (fun _ => (1 : ℝ)) u -
      (Icc a b).indicator (fun _ => (1 : ℝ)) (u + x)) ^ 2 = 2 * min x (b - a) := by
  have hpt : ∀ u, ((Icc a b).indicator (fun _ => (1 : ℝ)) u -
      (Icc a b).indicator (fun _ => (1 : ℝ)) (u + x)) ^ 2 =
      (Icc a b).indicator (fun _ => (1 : ℝ)) u + (Icc (a - x) (b - x)).indicator (fun _ => (1 : ℝ)) u -
        2 * (Icc a (b - x)).indicator (fun _ => (1 : ℝ)) u := by
    intro u
    have hs : (Icc a b).indicator (fun _ => (1 : ℝ)) (u + x) =
        (Icc (a - x) (b - x)).indicator (fun _ => (1 : ℝ)) u := by
      by_cases hu : u + x ∈ Icc a b
      · rw [indicator_of_mem hu, indicator_of_mem (show u ∈ Icc (a - x) (b - x) from
          ⟨by linarith [hu.1], by linarith [hu.2]⟩)]
      · rw [indicator_of_notMem hu, indicator_of_notMem fun h : u ∈ Icc (a - x) (b - x) =>
          hu ⟨by linarith [h.1], by linarith [h.2]⟩]
    rw [hs]
    by_cases h1 : u ∈ Icc a b <;> by_cases h2 : u ∈ Icc (a - x) (b - x)
    · rw [indicator_of_mem h1, indicator_of_mem h2,
        indicator_of_mem (show u ∈ Icc a (b - x) from ⟨h1.1, h2.2⟩)]
      norm_num
    · rw [indicator_of_mem h1, indicator_of_notMem h2,
        indicator_of_notMem (show u ∉ Icc a (b - x) from fun h => h2 ⟨by linarith [h.1], h.2⟩)]
      norm_num
    · rw [indicator_of_notMem h1, indicator_of_mem h2,
        indicator_of_notMem (show u ∉ Icc a (b - x) from fun h => h1 ⟨h.1, by linarith [h.2]⟩)]
      norm_num
    · rw [indicator_of_notMem h1, indicator_of_notMem h2,
        indicator_of_notMem (show u ∉ Icc a (b - x) from fun h => h1 ⟨h.1, by linarith [h.2]⟩)]
      norm_num
  have i1 : Integrable ((Icc a b).indicator fun _ => (1 : ℝ)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have i2 : Integrable ((Icc (a - x) (b - x)).indicator fun _ => (1 : ℝ)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have i3 : Integrable ((Icc a (b - x)).indicator fun _ => (1 : ℝ)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add_sub_three i1 i2 (i3.const_mul 2),
    integral_const_mul, integral_indicator_const _ measurableSet_Icc,
    integral_indicator_const _ measurableSet_Icc, integral_indicator_const _ measurableSet_Icc]
  simp only [Measure.real, Real.volume_Icc, smul_eq_mul, mul_one]
  rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  rcases le_total x (b - a) with h | h
  · rw [ENNReal.toReal_ofReal (by linarith), min_eq_left h]
    ring
  · rw [ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero, min_eq_right h]
    ring

/-- **The energy of the window plateau is finite**: `𝒥(1_{[a,b]}) = ∫_0^∞ ω(x)·2min(x, b − a)`, and
the integrand is integrable. -/
theorem levyEnergy_indicator (hab : a ≤ b) :
    levyEnergy ((Icc a b).indicator fun _ => (1 : ℝ)) =
      ∫ x in Ioi (0 : ℝ), archLevyDensity x * (2 * min x (b - a)) := by
  unfold levyEnergy
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by
    try simp only
    rw [integral_indicator_sub_shift_sq hab (le_of_lt hx)]

theorem integrableOn_archLevyDensity_mul_min (L : ℝ) (hL : 0 ≤ L) :
    IntegrableOn (fun x => archLevyDensity x * (2 * min x L)) (Ioi 0) := by
  have h1 : IntegrableOn (fun x : ℝ => x * Real.exp (-(1 / 2) * x)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2) * x)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num)
  have hdom : IntegrableOn (fun x => 2 * ((x + 1 / 2) * Real.exp (-x / 2))) (Ioi 0) := by
    refine IntegrableOn.congr_fun ((h1.add (h2.const_mul (1 / 2))).const_mul 2)
      (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]
    rw [show -x / 2 = -(1 / 2) * x by ring]
    ring
  refine hdom.mono' ((measurable_archLevyDensity.mul (measurable_const.mul
    (measurable_id.min measurable_const))).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hω := (archLevyDensity_pos hx0).le
  have hmin : 0 ≤ min x L := le_min hx0.le hL
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hω (by positivity))]
  have h1 : archLevyDensity x * min x L ≤ archLevyDensity x * x :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) hω
  have h2 := CHMDDoobGraph.archLevy_firstMoment_le hx0
  nlinarith

/-- `volume(Icc a b ∩ Ioi (b − x)) = min x (b − a)`. -/
theorem volume_Icc_inter_Ioi (hab : a ≤ b) {x : ℝ} (hx : 0 ≤ x) :
    (volume (Icc a b ∩ Ioi (b - x))).toReal = min x (b - a) := by
  rcases lt_or_ge (b - x) a with h | h
  · have hset : Icc a b ∩ Ioi (b - x) = Icc a b := inter_eq_left.mpr fun u hu => by
      simp only [mem_Ioi]; linarith [hu.1]
    rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), min_eq_right (by linarith)]
  · have hset : Icc a b ∩ Ioi (b - x) = Ioc (b - x) b := by
      ext u; simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨by linarith, h2⟩, h3⟩
    rw [hset, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), min_eq_left (by linarith)]
    ring

/-- `volume(Icc a b ∩ Iio (a + x)) = min x (b − a)`. -/
theorem volume_Icc_inter_Iio (hab : a ≤ b) {x : ℝ} (hx : 0 ≤ x) :
    (volume (Icc a b ∩ Iio (a + x))).toReal = min x (b - a) := by
  rcases lt_or_ge b (a + x) with h | h
  · have hset : Icc a b ∩ Iio (a + x) = Icc a b := inter_eq_left.mpr fun u hu => by
      simp only [mem_Iio]; linarith [hu.2]
    rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), min_eq_right (by linarith)]
  · have hset : Icc a b ∩ Iio (a + x) = Ico a (a + x) := by
      ext u; simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [hset, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith), min_eq_left (by linarith)]
    ring

theorem sq_indicator_one (s : Set ℝ) (u : ℝ) :
    (s.indicator (fun _ => (1 : ℝ)) u) ^ 2 = s.indicator (fun _ => (1 : ℝ)) u := by
  by_cases hu : u ∈ s
  · rw [indicator_of_mem hu]; norm_num
  · rw [indicator_of_notMem hu]; norm_num

theorem rightEdgeMass_indicator (hab : a ≤ b) {x : ℝ} (hx : 0 ≤ x) :
    rightEdgeMass ((Icc a b).indicator fun _ => (1 : ℝ)) b x = min x (b - a) := by
  unfold rightEdgeMass
  simp_rw [sq_indicator_one]
  rw [integral_indicator_const _ measurableSet_Icc]
  simp only [Measure.real, Measure.restrict_apply measurableSet_Icc, smul_eq_mul, mul_one]
  exact volume_Icc_inter_Ioi hab hx

theorem leftEdgeMass_indicator (hab : a ≤ b) {x : ℝ} (hx : 0 ≤ x) :
    leftEdgeMass ((Icc a b).indicator fun _ => (1 : ℝ)) a x = min x (b - a) := by
  unfold leftEdgeMass
  simp_rw [sq_indicator_one]
  rw [integral_indicator_const _ measurableSet_Icc]
  simp only [Measure.real, Measure.restrict_apply measurableSet_Icc, smul_eq_mul, mul_one]
  exact volume_Icc_inter_Iio hab hx

/-- **The plateau is pure edge**: the energy of `1_{[a,b]}` equals its edge killing energy. -/
theorem edgeKilling_indicator (hab : a ≤ b) :
    edgeKilling ((Icc a b).indicator fun _ => (1 : ℝ)) a b =
      levyEnergy ((Icc a b).indicator fun _ => (1 : ℝ)) := by
  rw [levyEnergy_indicator hab]
  unfold edgeKilling
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  try simp only
  rw [leftEdgeMass_indicator hab (le_of_lt hx), rightEdgeMass_indicator hab (le_of_lt hx)]
  ring

/-! ### No point traces -/

/-- The fixed profile: a `C^∞` bump on `(0, 1)` equal to `1` near `1/2`. -/
def spikeProfile : ContDiffBump ((1 / 2 : ℝ)) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem spikeProfile_eq_zero {v : ℝ} (hv : v ∉ Icc (0 : ℝ) 1) : spikeProfile v = 0 := by
  refine spikeProfile.zero_of_le_dist ?_
  simp only [mem_Icc, not_and_or, not_le] at hv
  show (1 / 2 : ℝ) ≤ dist v (1 / 2)
  rw [Real.dist_eq]
  rcases hv with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The dilated spike `g_w(u) = φ(u/w)`, supported in `[0, w]`, with `g_w(w/2) = 1`. -/
def dilatedSpike (w : ℝ) (u : ℝ) : ℝ := spikeProfile (u / w)

theorem dilatedSpike_half {w : ℝ} (hw : 0 < w) : dilatedSpike w (w / 2) = 1 := by
  unfold dilatedSpike
  rw [show w / 2 / w = 1 / 2 by field_simp]
  exact spikeProfile.one_of_mem_closedBall (Metric.mem_closedBall_self spikeProfile.rIn_pos.le)

theorem dilatedSpike_eq_zero {w : ℝ} (hw : 0 < w) {u : ℝ} (hu : u ∉ Icc 0 w) :
    dilatedSpike w u = 0 := by
  refine spikeProfile_eq_zero fun h => hu ⟨?_, ?_⟩
  · have := h.1
    rwa [le_div_iff₀ hw, zero_mul] at this
  · have := h.2
    rwa [div_le_iff₀ hw, one_mul] at this

theorem contDiff_dilatedSpike (w : ℝ) : ContDiff ℝ 2 (dilatedSpike w) :=
  (spikeProfile.contDiff (n := 2)).comp (contDiff_id.div_const w)

theorem hasCompactSupport_dilatedSpike {w : ℝ} (hw : 0 < w) :
    HasCompactSupport (dilatedSpike w) :=
  HasCompactSupport.intro (isCompact_Icc (a := 0) (b := w)) fun u hu => dilatedSpike_eq_zero hw hu

theorem dilatedSpike_nonneg (w u : ℝ) : 0 ≤ dilatedSpike w u := spikeProfile.nonneg

theorem dilatedSpike_le_one (w u : ℝ) : dilatedSpike w u ≤ 1 := spikeProfile.le_one

theorem dilatedSpike_le_indicator {w : ℝ} (hw : 0 < w) (u : ℝ) :
    dilatedSpike w u ≤ (Icc 0 w).indicator (fun _ => (1 : ℝ)) u := by
  by_cases hu : u ∈ Icc 0 w
  · rw [indicator_of_mem hu]; exact dilatedSpike_le_one w u
  · rw [indicator_of_notMem hu, dilatedSpike_eq_zero hw hu]

theorem integral_dilatedSpike_le {w : ℝ} (hw : 0 < w) : ∫ u, dilatedSpike w u ≤ w := by
  have hi : Integrable ((Icc 0 w).indicator fun _ => (1 : ℝ)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  calc ∫ u, dilatedSpike w u ≤ ∫ u, (Icc 0 w).indicator (fun _ => (1 : ℝ)) u :=
        integral_mono ((contDiff_dilatedSpike w).continuous.integrable_of_hasCompactSupport
          (hasCompactSupport_dilatedSpike hw)) hi (dilatedSpike_le_indicator hw)
    _ = w := by
        rw [integral_indicator_const _ measurableSet_Icc]
        simp [Measure.real, Real.volume_Icc, hw.le]

theorem integral_dilatedSpike_sq_le {w : ℝ} (hw : 0 < w) : ∫ u, dilatedSpike w u ^ 2 ≤ w := by
  refine le_trans (integral_mono (integrable_sq_of_cont (contDiff_dilatedSpike w).continuous
    (hasCompactSupport_dilatedSpike hw)) ((contDiff_dilatedSpike w).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_dilatedSpike hw)) fun u => ?_) (integral_dilatedSpike_le hw)
  have h0 := dilatedSpike_nonneg w u
  have h1 := dilatedSpike_le_one w u
  nlinarith

/-- `log y ≤ 2√y` for `y > 0`. -/
theorem log_le_two_mul_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have h := Real.log_le_sub_one_of_pos hs
  have e : Real.log y = 2 * Real.log (Real.sqrt y) := by
    rw [← Real.log_rpow hs, show (Real.sqrt y) ^ (2 : ℝ) = y by
      rw [Real.rpow_two, Real.sq_sqrt hy.le]]
  linarith

/-- **The energy of a unit spike vanishes with its width**: `𝒥(g_w) ≤ 2√w + w(C₀ + e^{1/2}K)`. -/
theorem levyEnergy_dilatedSpike_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℝ, 0 < w → w ≤ 1 →
      levyEnergy (dilatedSpike w) ≤
        2 * Real.sqrt w + w * (SpacingScaleHarmonicAnalysis.selfEnergyConstant + Real.exp (1 / 2) * K) := by
  obtain ⟨C, hC⟩ := (spikeProfile.contDiff (n := 1)).lipschitzWith_of_hasCompactSupport
    spikeProfile.hasCompactSupport (by norm_num)
  refine ⟨C, C.2, fun w hw0 hw1 => ?_⟩
  have hlip : ∀ u v, |dilatedSpike w u - dilatedSpike w v| ≤ (C / w) * |u - v| := by
    intro u v
    have h := hC.dist_le_mul (u / w) (v / w)
    rw [Real.dist_eq, Real.dist_eq] at h
    unfold dilatedSpike
    calc |spikeProfile (u / w) - spikeProfile (v / w)| ≤ C * |u / w - v / w| := h
      _ = (C / w) * |u - v| := by
          rw [show u / w - v / w = (u - v) / w by ring, abs_div, abs_of_pos hw0]
          ring
  have hK0 : 0 ≤ (C : ℝ) / w := div_nonneg C.2 hw0.le
  have h := SpacingScaleHarmonicAnalysis.levyEnergy_atom_le (contDiff_dilatedSpike w)
    (hasCompactSupport_dilatedSpike hw0) (fun u hu => dilatedSpike_eq_zero hw0 hu) hw0 hw1 hK0 hlip
  have hC0 : 0 ≤ SpacingScaleHarmonicAnalysis.selfEnergyConstant := by
    unfold SpacingScaleHarmonicAnalysis.selfEnergyConstant
    have : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have : 0 < 1 - Real.exp (-2) := by linarith
    positivity
  have hlog0 : 0 ≤ Real.log (1 / w) := Real.log_nonneg (by rw [le_div_iff₀ hw0]; linarith)
  have hsq := integral_dilatedSpike_sq_le hw0
  have habs : ∫ u, |dilatedSpike w u| ≤ w := by
    simp_rw [abs_of_nonneg (dilatedSpike_nonneg w _)]
    exact integral_dilatedSpike_le hw0
  have hsq0 : 0 ≤ ∫ u, dilatedSpike w u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hlogw : w * Real.log (1 / w) ≤ 2 * Real.sqrt w := by
    have h1 := log_le_two_mul_sqrt (show 0 < 1 / w by positivity)
    have h2 : Real.sqrt (1 / w) = 1 / Real.sqrt w := by
      rw [Real.sqrt_div' 1 hw0.le, Real.sqrt_one]
    rw [h2] at h1
    have hs : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw0
    calc w * Real.log (1 / w) ≤ w * (2 * (1 / Real.sqrt w)) := mul_le_mul_of_nonneg_left h1 hw0.le
      _ = 2 * (w / Real.sqrt w) := by ring
      _ = 2 * Real.sqrt w := by rw [Real.div_sqrt]
  have e1 : (Real.log (1 / w) + SpacingScaleHarmonicAnalysis.selfEnergyConstant) *
      (∫ u, dilatedSpike w u ^ 2) ≤
      (Real.log (1 / w) + SpacingScaleHarmonicAnalysis.selfEnergyConstant) * w :=
    mul_le_mul_of_nonneg_left hsq (by linarith)
  have e2 : Real.exp (1 / 2) * (C / w) * w * (∫ u, |dilatedSpike w u|) ≤
      Real.exp (1 / 2) * C * w := by
    have : Real.exp (1 / 2) * (C / w) * w = Real.exp (1 / 2) * C := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left habs (by positivity)
  nlinarith

/-- **No point traces.** At every point `x₀`, for every `ε > 0`, a `C²` spike `g` with `g(x₀) = 1`
supported in `[x₀ − ε, x₀ + ε]` has `‖g‖₂² ≤ ε`, `‖g‖₁ ≤ ε` and `𝒥(g) ≤ ε`. -/
theorem exists_spike (x₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ g x₀ = 1 ∧
      (∀ u, ε < |u - x₀| → g u = 0) ∧ (∫ u, g u ^ 2) ≤ ε ∧ (∫ u, |g u|) ≤ ε ∧
        levyEnergy g ≤ ε := by
  obtain ⟨K, hK0, hK⟩ := levyEnergy_dilatedSpike_le
  set A := SpacingScaleHarmonicAnalysis.selfEnergyConstant + Real.exp (1 / 2) * K
  have hA : 0 ≤ A := by
    have : 0 ≤ SpacingScaleHarmonicAnalysis.selfEnergyConstant := by
      unfold SpacingScaleHarmonicAnalysis.selfEnergyConstant
      have : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      have : 0 < 1 - Real.exp (-2) := by linarith
      positivity
    positivity
  set w := min (min 1 ε) (min ((ε / 4) ^ 2) (ε / (2 * (A + 1)))) with hw
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hwε : w ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
  have hw4 : w ≤ (ε / 4) ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hwA : w ≤ ε / (2 * (A + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨fun u => dilatedSpike w (u - x₀ + w / 2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contDiff_dilatedSpike w).comp ((contDiff_id.sub contDiff_const).add contDiff_const)
  · exact HasCompactSupport.intro (isCompact_Icc (a := x₀ - w / 2) (b := x₀ + w / 2)) fun u hu =>
      dilatedSpike_eq_zero hw0 fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
  · simp only [sub_self, zero_add]
    exact dilatedSpike_half hw0
  · intro u hu
    refine dilatedSpike_eq_zero hw0 fun h => ?_
    have h1 := h.1
    have h2 := h.2
    have : |u - x₀| ≤ w / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · have e : (∫ u, dilatedSpike w (u - x₀ + w / 2) ^ 2) = ∫ u, dilatedSpike w u ^ 2 := by
      have := integral_add_right_eq_self (μ := volume) (fun u => dilatedSpike w u ^ 2) (-x₀ + w / 2)
      simpa [sub_eq_add_neg, add_assoc] using this
    rw [e]
    exact (integral_dilatedSpike_sq_le hw0).trans hwε
  · have e : (∫ u, |dilatedSpike w (u - x₀ + w / 2)|) = ∫ u, |dilatedSpike w u| := by
      have := integral_add_right_eq_self (μ := volume) (fun u => |dilatedSpike w u|) (-x₀ + w / 2)
      simpa [sub_eq_add_neg, add_assoc] using this
    rw [e]
    simp_rw [abs_of_nonneg (dilatedSpike_nonneg w _)]
    exact (integral_dilatedSpike_le hw0).trans hwε
  · have e : levyEnergy (fun u => dilatedSpike w (u - x₀ + w / 2)) = levyEnergy (dilatedSpike w) := by
      have := SpacingScaleHarmonicAnalysis.levyEnergy_translate (g := dilatedSpike w) (x₀ - w / 2)
      simpa [sub_sub_eq_add_sub, sub_add_eq_add_sub] using this
    rw [e]
    have hb := hK w hw0 hw1
    have hs : Real.sqrt w ≤ ε / 4 := by
      calc Real.sqrt w ≤ Real.sqrt ((ε / 4) ^ 2) := Real.sqrt_le_sqrt hw4
        _ = ε / 4 := Real.sqrt_sq (by positivity)
    have hwA' : w * A ≤ ε / 2 := by
      have h1 : w * (2 * (A + 1)) ≤ ε := by
        rw [le_div_iff₀ (by positivity)] at hwA
        linarith
      nlinarith
    linarith

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
