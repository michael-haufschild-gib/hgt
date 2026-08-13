import Mathlib
import GaloisForLFunctions.RHTower.SuzukiFiniteApertureHermiteBiehler
import GaloisForLFunctions.HTGeometry.CompactMomentDeterminacy

/-!
# Inverse-moment holography of the Donoghue transform, and the free-boundary tangent

For a finite measure `ν` on `ℝ` whose mass sits at distance at least `δ > 0` from the origin, the
Cauchy transform `R ν z = ∫ (t - z)⁻¹ dν` is differentiable to every order on the disc of radius
`δ/2`, with `j`-th derivative `j! ∫ (t - z)^{-(j+1)} dν`.  The Donoghue transform
`m ν z = z + (z² + 1) R ν z` therefore has explicit odd central jets: for a probability measure,

`m^{(2n+1)}(0) / (2n+1)! = q n + q (n+1)`,   `q n = ∫ t^{-2n} dν`,

so the complete odd jet reconstructs every inverse even moment by the two-term recursion.  The
inverse moments are the moments of the pushforward of `ν` under `t ↦ (t²)⁻¹`, which is carried by
the compact interval `[0, δ⁻²]`; compact moment determinacy identifies that pushforward, and an
even measure is recovered from it because the preimage of a set under `t ↦ |t|` splits into two
reflected copies of equal mass.  Hence an even measure with a spectral gap is determined by its
inverse even moments.  The scale-free shape `q n / (q 1)ⁿ` is invariant under every dilation of
the measure.

The last section carries the free-boundary tangent: the Livšic quotient built from a Fourier
family, its parameter derivative (the anti-reflected logarithmic derivative), and the transported
derivative of the normalized Herglotz presentation through the Cayley inverse.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Filter Metric Topology

/-! ## The Cauchy kernel powers and their derivatives -/

/-- The `j`-th Cauchy kernel power transform: `∫ (t - z)^{-(j+1)} dν`. -/
def suzukiCauchyPow (nu : Measure ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  ∫ t, (((t : ℂ) - z)⁻¹) ^ (j + 1) ∂nu

/-- The Donoghue transform `m ν z = z + (z² + 1) ∫ (t - z)⁻¹ dν`. -/
def suzukiDonoghueTransform (nu : Measure ℝ) (z : ℂ) : ℂ :=
  z + (z ^ 2 + 1) * suzukiCauchyPow nu 0 z

/-- The inverse even moments `q n = ∫ t^{-2n} dν`. -/
def suzukiInverseEvenMoment (nu : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ t, (t ^ (2 * n))⁻¹ ∂nu

/-- The scale-free projective moment shape `κ n = q n / (q 1)ⁿ`. -/
def suzukiProjectiveMomentShape (nu : Measure ℝ) (n : ℕ) : ℝ :=
  suzukiInverseEvenMoment nu n / (suzukiInverseEvenMoment nu 1) ^ n

theorem measurable_suzukiCauchyKernel (x : ℂ) (k : ℕ) :
    Measurable fun t : ℝ => (((t : ℂ) - x)⁻¹) ^ k :=
  ((Complex.measurable_ofReal.sub measurable_const).inv).pow_const k

/-- On the spectral gap, the Cauchy kernel powers are uniformly bounded on the half-gap disc. -/
theorem norm_suzukiCauchyKernel_le {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : δ ≤ |t|)
    {x : ℂ} (hx : ‖x‖ < δ / 2) (k : ℕ) :
    ‖(((t : ℂ) - x)⁻¹) ^ k‖ ≤ (2 / δ) ^ k := by
  rw [norm_pow, norm_inv]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  have hnt : ‖((t : ℝ) : ℂ)‖ = |t| := Complex.norm_real t
  have hlow : δ / 2 ≤ ‖(t : ℂ) - x‖ := by
    have h1 := norm_sub_norm_le ((t : ℝ) : ℂ) x
    rw [hnt] at h1
    linarith
  have h2 : ‖(t : ℂ) - x‖⁻¹ ≤ (δ / 2)⁻¹ := by
    gcongr
    linarith
  calc ‖(t : ℂ) - x‖⁻¹ ≤ (δ / 2)⁻¹ := h2
    _ = 2 / δ := by field_simp

theorem suzukiCauchyKernel_ne_zero {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : δ ≤ |t|)
    {x : ℂ} (hx : ‖x‖ < δ / 2) : (t : ℂ) - x ≠ 0 := by
  intro h
  have hnt : ‖((t : ℝ) : ℂ)‖ = |t| := Complex.norm_real t
  have h1 := norm_sub_norm_le ((t : ℝ) : ℂ) x
  rw [h, norm_zero, hnt] at h1
  linarith

theorem integrable_suzukiCauchyKernel {nu : Measure ℝ} [IsFiniteMeasure nu] {δ : ℝ}
    (hδ : 0 < δ) (hgap : ∀ᵐ t ∂nu, δ ≤ |t|) {x : ℂ} (hx : ‖x‖ < δ / 2) (k : ℕ) :
    Integrable (fun t : ℝ => (((t : ℂ) - x)⁻¹) ^ k) nu := by
  refine Integrable.mono' (integrable_const ((2 / δ) ^ k))
    ((measurable_suzukiCauchyKernel x k).aestronglyMeasurable) ?_
  filter_upwards [hgap] with t ht
  exact norm_suzukiCauchyKernel_le hδ ht hx k

/-- Pointwise derivative of the Cauchy kernel power in the spectral parameter. -/
theorem hasDerivAt_suzukiCauchyKernel {t : ℝ} {x : ℂ} (hx : (t : ℂ) - x ≠ 0) (j : ℕ) :
    HasDerivAt (fun y : ℂ => (((t : ℂ) - y)⁻¹) ^ (j + 1))
      (((j : ℂ) + 1) * (((t : ℂ) - x)⁻¹) ^ (j + 2)) x := by
  have h1 : HasDerivAt (fun y : ℂ => (t : ℂ) - y) (-1) x :=
    (hasDerivAt_id x).const_sub ((t : ℝ) : ℂ)
  have h2 : HasDerivAt (fun y : ℂ => ((t : ℂ) - y) ^ (j + 1))
      (((j + 1 : ℕ) : ℂ) * ((t : ℂ) - x) ^ (j + 1 - 1) * (-1)) x := h1.pow (j + 1)
  have h3 : HasDerivAt (fun y : ℂ => (((t : ℂ) - y) ^ (j + 1))⁻¹)
      (-(((j + 1 : ℕ) : ℂ) * ((t : ℂ) - x) ^ (j + 1 - 1) * (-1))
        / (((t : ℂ) - x) ^ (j + 1)) ^ 2) x := h2.inv (pow_ne_zero _ hx)
  have h4 : HasDerivAt (fun y : ℂ => (((t : ℂ) - y)⁻¹) ^ (j + 1))
      (-(((j + 1 : ℕ) : ℂ) * ((t : ℂ) - x) ^ (j + 1 - 1) * (-1))
        / (((t : ℂ) - x) ^ (j + 1)) ^ 2) x := by
    have hfun : (fun y : ℂ => (((t : ℂ) - y)⁻¹) ^ (j + 1))
        = fun y : ℂ => (((t : ℂ) - y) ^ (j + 1))⁻¹ := by
      funext y
      rw [inv_pow]
    rw [hfun]
    exact h3
  convert h4 using 1
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- **Differentiation under the Cauchy transform.**  On the half-gap disc, the `j`-th kernel power
transform differentiates to `(j+1)` times the next one. -/
theorem hasDerivAt_suzukiCauchyPow {nu : Measure ℝ} [IsFiniteMeasure nu] {δ : ℝ}
    (hδ : 0 < δ) (hgap : ∀ᵐ t ∂nu, δ ≤ |t|) (j : ℕ) {z : ℂ} (hz : ‖z‖ < δ / 2) :
    HasDerivAt (suzukiCauchyPow nu j) (((j : ℂ) + 1) * suzukiCauchyPow nu (j + 1) z) z := by
  have hε : (0 : ℝ) < δ / 2 - ‖z‖ := by linarith
  have hmem : ∀ x ∈ Metric.ball z (δ / 2 - ‖z‖), ‖x‖ < δ / 2 := by
    intro x hx
    have h1 : ‖x - z‖ < δ / 2 - ‖z‖ := mem_ball_iff_norm.mp hx
    calc ‖x‖ = ‖x - z + z‖ := by ring_nf
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ < δ / 2 := by linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (x : ℂ) (t : ℝ) => (((t : ℂ) - x)⁻¹) ^ (j + 1))
    (F' := fun (x : ℂ) (t : ℝ) => ((j : ℂ) + 1) * (((t : ℂ) - x)⁻¹) ^ (j + 2))
    (bound := fun _ : ℝ => ((j : ℝ) + 1) * (2 / δ) ^ (j + 2))
    (Metric.ball_mem_nhds z hε)
    (Eventually.of_forall fun x =>
      (measurable_suzukiCauchyKernel x (j + 1)).aestronglyMeasurable)
    (integrable_suzukiCauchyKernel hδ hgap hz (j + 1))
    (((measurable_suzukiCauchyKernel z (j + 2)).const_mul _).aestronglyMeasurable)
    ?_ (integrable_const _) ?_
  · have h1 := key.2
    rw [integral_const_mul] at h1
    exact h1
  · filter_upwards [hgap] with t ht
    intro x hx
    rw [norm_mul]
    have hn1 : ‖(j : ℂ) + 1‖ = (j : ℝ) + 1 := by
      have hc : ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_natCast]
      push_cast
      ring
    rw [hn1]
    exact mul_le_mul_of_nonneg_left
      (norm_suzukiCauchyKernel_le hδ ht (hmem x hx) (j + 2)) (by positivity)
  · filter_upwards [hgap] with t ht
    intro x hx
    exact hasDerivAt_suzukiCauchyKernel (suzukiCauchyKernel_ne_zero hδ ht (hmem x hx)) j

/-- **Iterated derivatives of the Cauchy transform** on the half-gap disc:
`R^{(j)}(z) = j! ∫ (t - z)^{-(j+1)} dν`. -/
theorem iteratedDeriv_suzukiCauchyPow {nu : Measure ℝ} [IsFiniteMeasure nu] {δ : ℝ}
    (hδ : 0 < δ) (hgap : ∀ᵐ t ∂nu, δ ≤ |t|) :
    ∀ (j : ℕ) {z : ℂ}, ‖z‖ < δ / 2 →
      iteratedDeriv j (suzukiCauchyPow nu 0) z = (j.factorial : ℂ) * suzukiCauchyPow nu j z := by
  intro j
  induction j with
  | zero =>
    intro z hz
    simp [iteratedDeriv_zero]
  | succ j ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (suzukiCauchyPow nu 0)
        =ᶠ[𝓝 z] fun w => (j.factorial : ℂ) * suzukiCauchyPow nu j w :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz))
        fun w hw => ih (mem_ball_zero_iff.mp hw)
    rw [hev.deriv_eq]
    have h : HasDerivAt (fun w : ℂ => (j.factorial : ℂ) * suzukiCauchyPow nu j w)
        ((j.factorial : ℂ) * (((j : ℂ) + 1) * suzukiCauchyPow nu (j + 1) z)) z :=
      (hasDerivAt_suzukiCauchyPow hδ hgap j hz).const_mul (j.factorial : ℂ)
    rw [h.deriv]
    push_cast [Nat.factorial_succ]
    ring

/-! ## Odd central jets of the Donoghue transform -/

/-- First derivative of the Donoghue transform on the half-gap disc. -/
theorem iteratedDeriv_one_suzukiDonoghueTransform {nu : Measure ℝ} [IsFiniteMeasure nu] {δ : ℝ}
    (hδ : 0 < δ) (hgap : ∀ᵐ t ∂nu, δ ≤ |t|) {z : ℂ} (hz : ‖z‖ < δ / 2) :
    iteratedDeriv 1 (suzukiDonoghueTransform nu) z
      = 1 + (2 * z * suzukiCauchyPow nu 0 z + (z ^ 2 + 1) * suzukiCauchyPow nu 1 z) := by
  have h0 := hasDerivAt_suzukiCauchyPow hδ hgap 0 hz
  have h : HasDerivAt (fun y : ℂ => y + (y ^ 2 + 1) * suzukiCauchyPow nu 0 y)
      (1 + (((2 : ℕ) : ℂ) * z ^ (2 - 1) * suzukiCauchyPow nu 0 z
        + (z ^ 2 + 1) * ((((0 : ℕ) : ℂ) + 1) * suzukiCauchyPow nu (0 + 1) z))) z :=
    (hasDerivAt_id z).add (((hasDerivAt_pow 2 z).add_const 1).mul h0)
  have hfun : suzukiDonoghueTransform nu
      = fun y : ℂ => y + (y ^ 2 + 1) * suzukiCauchyPow nu 0 y := rfl
  rw [iteratedDeriv_one, hfun, h.deriv]
  norm_num

/-- Higher derivatives of the Donoghue transform on the half-gap disc:
`m^{(r+2)}(z) = (r+2)! ((z²+1) P_{r+2} + 2z P_{r+1} + P_r)`. -/
theorem iteratedDeriv_succ_succ_suzukiDonoghueTransform {nu : Measure ℝ} [IsFiniteMeasure nu]
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ᵐ t ∂nu, δ ≤ |t|) :
    ∀ (r : ℕ) {z : ℂ}, ‖z‖ < δ / 2 →
      iteratedDeriv (r + 2) (suzukiDonoghueTransform nu) z
        = ((r + 2).factorial : ℂ) * ((z ^ 2 + 1) * suzukiCauchyPow nu (r + 2) z
            + 2 * z * suzukiCauchyPow nu (r + 1) z + suzukiCauchyPow nu r z) := by
  intro r
  induction r with
  | zero =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv 1 (suzukiDonoghueTransform nu)
        =ᶠ[𝓝 z] fun w => 1 + (2 * w * suzukiCauchyPow nu 0 w
          + (w ^ 2 + 1) * suzukiCauchyPow nu 1 w) :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz))
        fun w hw => iteratedDeriv_one_suzukiDonoghueTransform hδ hgap (mem_ball_zero_iff.mp hw)
    rw [hev.deriv_eq]
    have hP0 := hasDerivAt_suzukiCauchyPow hδ hgap 0 hz
    have hP1 := hasDerivAt_suzukiCauchyPow hδ hgap 1 hz
    have h : HasDerivAt (fun w : ℂ => 1 + (2 * w * suzukiCauchyPow nu 0 w
        + (w ^ 2 + 1) * suzukiCauchyPow nu 1 w))
        ((2 * 1 * suzukiCauchyPow nu 0 z
            + 2 * z * (((0 : ℂ) + 1) * suzukiCauchyPow nu (0 + 1) z))
          + (((2 : ℕ) : ℂ) * z ^ (2 - 1) * suzukiCauchyPow nu 1 z
            + (z ^ 2 + 1) * (((1 : ℂ) + 1) * suzukiCauchyPow nu (1 + 1) z))) z :=
      ((((hasDerivAt_id z).const_mul 2).mul hP0).add
        (((hasDerivAt_pow 2 z).add_const 1).mul hP1)).const_add 1
    rw [h.deriv]
    push_cast [Nat.factorial]
    norm_num
    ring
  | succ r ih =>
    intro z hz
    have hidx : r + 1 + 2 = r + 2 + 1 := rfl
    rw [hidx, iteratedDeriv_succ]
    have hev : iteratedDeriv (r + 2) (suzukiDonoghueTransform nu)
        =ᶠ[𝓝 z] fun w => ((r + 2).factorial : ℂ)
          * ((w ^ 2 + 1) * suzukiCauchyPow nu (r + 2) w
            + 2 * w * suzukiCauchyPow nu (r + 1) w + suzukiCauchyPow nu r w) :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz))
        fun w hw => ih (mem_ball_zero_iff.mp hw)
    rw [hev.deriv_eq]
    have hPr := hasDerivAt_suzukiCauchyPow hδ hgap r hz
    have hPr1 := hasDerivAt_suzukiCauchyPow hδ hgap (r + 1) hz
    have hPr2 := hasDerivAt_suzukiCauchyPow hδ hgap (r + 2) hz
    have h : HasDerivAt (fun w : ℂ => ((r + 2).factorial : ℂ)
        * ((w ^ 2 + 1) * suzukiCauchyPow nu (r + 2) w
          + 2 * w * suzukiCauchyPow nu (r + 1) w + suzukiCauchyPow nu r w))
        (((r + 2).factorial : ℂ)
          * (((((2 : ℕ) : ℂ) * z ^ (2 - 1) * suzukiCauchyPow nu (r + 2) z
              + (z ^ 2 + 1) * (((r : ℂ) + 2 + 1) * suzukiCauchyPow nu (r + 2 + 1) z))
            + (2 * 1 * suzukiCauchyPow nu (r + 1) z
              + 2 * z * (((r : ℂ) + 1 + 1) * suzukiCauchyPow nu (r + 1 + 1) z)))
            + ((r : ℂ) + 1) * suzukiCauchyPow nu (r + 1) z)) z := by
      have hPr1' : HasDerivAt (suzukiCauchyPow nu (r + 1))
          (((r : ℂ) + 1 + 1) * suzukiCauchyPow nu (r + 1 + 1) z) z := by
        convert hPr1 using 2
        push_cast
        ring
      have hPr2' : HasDerivAt (suzukiCauchyPow nu (r + 2))
          (((r : ℂ) + 2 + 1) * suzukiCauchyPow nu (r + 2 + 1) z) z := by
        convert hPr2 using 2
        push_cast
        ring
      exact (((((hasDerivAt_pow 2 z).add_const 1).mul hPr2').add
        (((hasDerivAt_id z).const_mul 2).mul hPr1')).add hPr).const_mul _
    rw [h.deriv]
    push_cast [Nat.factorial_succ]
    norm_num
    ring

/-- The Cauchy kernel powers at the origin are the real inverse-power integrals. -/
theorem suzukiCauchyPow_zero_eq (nu : Measure ℝ) (j : ℕ) :
    suzukiCauchyPow nu j 0 = ((∫ t, (t ^ (j + 1))⁻¹ ∂nu : ℝ) : ℂ) := by
  rw [suzukiCauchyPow]
  have hker : ∀ t : ℝ, ((((t : ℝ) : ℂ) - 0)⁻¹) ^ (j + 1)
      = (((t ^ (j + 1))⁻¹ : ℝ) : ℂ) := by
    intro t
    rw [sub_zero, ← inv_pow]
    push_cast
    ring
  simp_rw [hker]
  exact integral_complex_ofReal

/-- For a probability measure, the zeroth inverse even moment is one. -/
theorem suzukiInverseEvenMoment_zero (nu : Measure ℝ) [IsProbabilityMeasure nu] :
    suzukiInverseEvenMoment nu 0 = 1 := by
  have h : suzukiInverseEvenMoment nu 0 = ∫ _t, (1 : ℝ) ∂nu := by
    unfold suzukiInverseEvenMoment
    norm_num
  rw [h, integral_const]
  simp [measureReal_def]

/-- **Complete inverse-moment holography** — the card's `(5)`:
`m^{(2n+1)}(0) / (2n+1)! = q n + q (n+1)` for the Donoghue transform of a spectral probability
with a gap about the origin. -/
theorem iteratedDeriv_suzukiDonoghueTransform_odd_zero {nu : Measure ℝ}
    [IsProbabilityMeasure nu] {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ᵐ t ∂nu, δ ≤ |t|) (n : ℕ) :
    iteratedDeriv (2 * n + 1) (suzukiDonoghueTransform nu) 0
      = (((2 * n + 1).factorial : ℕ) : ℂ)
        * (((suzukiInverseEvenMoment nu n : ℝ) : ℂ)
          + ((suzukiInverseEvenMoment nu (n + 1) : ℝ) : ℂ)) := by
  have h0 : ‖(0 : ℂ)‖ < δ / 2 := by
    rw [norm_zero]
    linarith
  cases n with
  | zero =>
    have hidx : 2 * 0 + 1 = 1 := by norm_num
    rw [hidx, iteratedDeriv_one_suzukiDonoghueTransform hδ hgap h0]
    have hbq : suzukiCauchyPow nu 1 0 = ((suzukiInverseEvenMoment nu 1 : ℝ) : ℂ) := by
      rw [suzukiCauchyPow_zero_eq]
      norm_num [suzukiInverseEvenMoment]
    rw [hbq, suzukiInverseEvenMoment_zero]
    push_cast [Nat.factorial]
    ring
  | succ m =>
    have hidx : 2 * (m + 1) + 1 = 2 * m + 1 + 2 := by ring
    rw [hidx, iteratedDeriv_succ_succ_suzukiDonoghueTransform hδ hgap (2 * m + 1) h0]
    have hb1 : suzukiCauchyPow nu (2 * m + 1 + 2) 0
        = ((suzukiInverseEvenMoment nu (m + 1 + 1) : ℝ) : ℂ) := by
      rw [suzukiCauchyPow_zero_eq]
      have he : 2 * m + 1 + 2 + 1 = 2 * (m + 1 + 1) := by ring
      rw [he]
      rfl
    have hb2 : suzukiCauchyPow nu (2 * m + 1) 0
        = ((suzukiInverseEvenMoment nu (m + 1) : ℝ) : ℂ) := by
      rw [suzukiCauchyPow_zero_eq]
      have he : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
      rw [he]
      rfl
    rw [hb1, hb2]
    push_cast
    ring

/-- **The inverse-moment reconstruction** — the card's `(6)`:
`q (n+1) = m^{(2n+1)}(0) / (2n+1)! - q n`. -/
theorem suzukiInverseMomentReconstruction_eq {nu : Measure ℝ}
    [IsProbabilityMeasure nu] {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ᵐ t ∂nu, δ ≤ |t|) (n : ℕ) :
    ((suzukiInverseEvenMoment nu (n + 1) : ℝ) : ℂ)
      = iteratedDeriv (2 * n + 1) (suzukiDonoghueTransform nu) 0
          / (((2 * n + 1).factorial : ℕ) : ℂ)
        - ((suzukiInverseEvenMoment nu n : ℝ) : ℂ) := by
  have h := iteratedDeriv_suzukiDonoghueTransform_odd_zero hδ hgap n
  have hfac : ((((2 * n + 1).factorial : ℕ)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (2 * n + 1).factorial_ne_zero
  rw [h]
  field_simp

/-! ## Pushforward moments and dilation invariance -/

/-- **The pushforward moment identity** — the card's `(7)`: the `n`-th moment of the pushforward
of `ν` under `t ↦ (t²)⁻¹` is the `n`-th inverse even moment. -/
theorem suzukiInverseMoment_pushforward (nu : Measure ℝ) (n : ℕ) :
    ∫ y, y ^ n ∂(nu.map fun t => (t ^ 2)⁻¹) = suzukiInverseEvenMoment nu n := by
  rw [integral_map ((measurable_id.pow_const 2).inv).aemeasurable
    (measurable_id.pow_const n).aestronglyMeasurable]
  simp only [suzukiInverseEvenMoment]
  congr 1
  funext t
  rw [← inv_pow, ← pow_mul, mul_comm n 2]

/-- Inverse even moments scale geometrically under dilation: `q n ↦ c^{-2n} q n`. -/
theorem suzukiInverseEvenMoment_dilation (nu : Measure ℝ) (c : ℝ) (n : ℕ) :
    suzukiInverseEvenMoment (nu.map fun t => c * t) n
      = (c ^ (2 * n))⁻¹ * suzukiInverseEvenMoment nu n := by
  rw [suzukiInverseEvenMoment,
    integral_map (measurable_const_mul c).aemeasurable
      ((measurable_id.pow_const (2 * n)).inv).aestronglyMeasurable]
  have hker : ∀ t : ℝ, ((c * t) ^ (2 * n))⁻¹ = (c ^ (2 * n))⁻¹ * (t ^ (2 * n))⁻¹ := by
    intro t
    rw [mul_pow, mul_inv]
  simp_rw [hker]
  rw [integral_const_mul]
  rfl

/-- **Dilation invariance of the projective moment shape** — the card's `(8)`:
`κ n` is unchanged by every spectral dilation `t ↦ c t`, `c ≠ 0`. -/
theorem suzukiProjectiveMomentShape_geometricScale (nu : Measure ℝ) {c : ℝ} (hc : c ≠ 0)
    (h1 : suzukiInverseEvenMoment nu 1 ≠ 0) (n : ℕ) :
    suzukiProjectiveMomentShape (nu.map fun t => c * t) n
      = suzukiProjectiveMomentShape nu n := by
  rw [suzukiProjectiveMomentShape, suzukiProjectiveMomentShape,
    suzukiInverseEvenMoment_dilation, suzukiInverseEvenMoment_dilation]
  have hc2 : c ^ (2 * n) ≠ 0 := pow_ne_zero _ hc
  have hcn : (c ^ (2 * 1))⁻¹ ^ n = (c ^ (2 * n))⁻¹ := by
    rw [← inv_pow, ← pow_mul]
    congr 1
    ring
  rw [mul_pow, hcn]
  field_simp

/-! ## Determinacy: an even gapped measure is its inverse moments -/

/-- Pushing an even measure forward by the absolute value doubles the mass of a positive set:
the preimage of `A ⊆ (0, ∞)` under `|·|` is the disjoint union of `A` and its reflection. -/
theorem measure_abs_preimage_of_even {nu : Measure ℝ}
    (he : nu.map (fun t => -t) = nu) {A : Set ℝ} (hA : MeasurableSet A)
    (hpos : A ⊆ Set.Ioi (0 : ℝ)) :
    nu (abs ⁻¹' A) = 2 * nu A := by
  have habs : abs ⁻¹' A = A ∪ (fun t : ℝ => -t) ⁻¹' A := by
    ext t
    simp only [Set.mem_preimage, Set.mem_union]
    constructor
    · intro h
      rcases le_or_lt 0 t with hto | hto
      · left
        rwa [abs_of_nonneg hto] at h
      · right
        rwa [abs_of_neg hto] at h
    · intro h
      rcases h with h | h
      · have hp := hpos h
        rw [Set.mem_Ioi] at hp
        rwa [abs_of_pos hp]
      · have hp := hpos h
        rw [Set.mem_Ioi] at hp
        have ht : t < 0 := by linarith
        rwa [abs_of_neg ht]
  have hdisj : Disjoint A ((fun t : ℝ => -t) ⁻¹' A) := by
    rw [Set.disjoint_iff]
    rintro t ⟨h1, h2⟩
    have hp1 := hpos h1
    have hp2 := hpos h2
    rw [Set.mem_Ioi] at hp1 hp2
    exact absurd hp2 (by simp only [Set.mem_preimage] at hp2 ⊢; linarith)
  have hmeasneg : MeasurableSet ((fun t : ℝ => -t) ⁻¹' A) := measurable_neg hA
  have hrefl : nu ((fun t : ℝ => -t) ⁻¹' A) = nu A := by
    conv_rhs => rw [← he]
    rw [Measure.map_apply measurable_neg hA]
  rw [habs, measure_union hdisj hmeasneg, hrefl, two_mul]

/-- **Even recovery.**  Two even measures vanishing at the origin and with the same pushforward
under `t ↦ (t²)⁻¹` are equal: the pushforward sees `|t|`, and evenness splits each absolute value
into two reflected copies of equal mass. -/
theorem ext_of_even_of_map_invSq_eq {nu₁ nu₂ : Measure ℝ}
    (he₁ : nu₁.map (fun t => -t) = nu₁) (he₂ : nu₂.map (fun t => -t) = nu₂)
    (h0₁ : nu₁ {0} = 0) (h0₂ : nu₂ {0} = 0)
    (hmap : nu₁.map (fun t => (t ^ 2)⁻¹) = nu₂.map (fun t => (t ^ 2)⁻¹)) :
    nu₁ = nu₂ := by
  have hs : Measurable fun t : ℝ => (t ^ 2)⁻¹ := (measurable_id.pow_const 2).inv
  have hr : Measurable fun u : ℝ => (Real.sqrt u)⁻¹ :=
    Real.continuous_sqrt.measurable.inv
  have hcomp : ∀ t : ℝ, (Real.sqrt ((t ^ 2)⁻¹))⁻¹ = |t| := by
    intro t
    rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs, inv_inv]
  have hpos_agree : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Ioi (0 : ℝ) →
      nu₁ A = nu₂ A := by
    intro A hA hApos
    have hCmeas : MeasurableSet ((fun u : ℝ => (Real.sqrt u)⁻¹) ⁻¹' A) := hr hA
    have hpre : (fun t : ℝ => (t ^ 2)⁻¹) ⁻¹' ((fun u : ℝ => (Real.sqrt u)⁻¹) ⁻¹' A)
        = abs ⁻¹' A := by
      ext t
      simp only [Set.mem_preimage]
      rw [hcomp t]
      rfl
    have hkey : ∀ nu : Measure ℝ,
        (nu.map fun t : ℝ => (t ^ 2)⁻¹) ((fun u : ℝ => (Real.sqrt u)⁻¹) ⁻¹' A)
          = nu (abs ⁻¹' A) := by
      intro nu
      rw [Measure.map_apply hs hCmeas, hpre]
    have h1 := hkey nu₁
    have h2 := hkey nu₂
    rw [hmap] at h1
    have habs : nu₁ (abs ⁻¹' A) = nu₂ (abs ⁻¹' A) := by
      rw [← h1, h2]
    rw [measure_abs_preimage_of_even he₁ hA hApos,
      measure_abs_preimage_of_even he₂ hA hApos] at habs
    exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp habs
  have hneg_agree : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Iio (0 : ℝ) →
      nu₁ A = nu₂ A := by
    intro A hA hAneg
    have hAeq : A = (fun t : ℝ => -t) ⁻¹' ((fun t : ℝ => -t) ⁻¹' A) := by
      ext t
      simp
    have hBmeas : MeasurableSet ((fun t : ℝ => -t) ⁻¹' A) := measurable_neg hA
    have hBpos : ((fun t : ℝ => -t) ⁻¹' A) ⊆ Set.Ioi (0 : ℝ) := by
      intro t ht
      rw [Set.mem_preimage] at ht
      have hin := hAneg ht
      rw [Set.mem_Iio] at hin
      rw [Set.mem_Ioi]
      linarith
    have h1 : nu₁ A = nu₁ ((fun t : ℝ => -t) ⁻¹' A) := by
      conv_lhs => rw [hAeq]
      conv_rhs => rw [← he₁]
      rw [Measure.map_apply measurable_neg hBmeas]
    have h2 : nu₂ A = nu₂ ((fun t : ℝ => -t) ⁻¹' A) := by
      conv_lhs => rw [hAeq]
      conv_rhs => rw [← he₂]
      rw [Measure.map_apply measurable_neg hBmeas]
    rw [h1, h2]
    exact hpos_agree _ hBmeas hBpos
  refine Measure.ext fun A hA => ?_
  have hm1 : MeasurableSet (A ∩ Set.Iio (0 : ℝ)) := hA.inter measurableSet_Iio
  have hm2 : MeasurableSet (A ∩ ({0} : Set ℝ)) := hA.inter (measurableSet_singleton 0)
  have hm3 : MeasurableSet (A ∩ Set.Ioi (0 : ℝ)) := hA.inter measurableSet_Ioi
  have hsplit : A = A ∩ Set.Iio 0 ∪ (A ∩ {0} ∪ A ∩ Set.Ioi 0) := by
    ext t
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi,
      Set.mem_singleton_iff]
    constructor
    · intro ht
      rcases lt_trichotomy t 0 with h | h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (Or.inl ⟨ht, h⟩)
      · exact Or.inr (Or.inr ⟨ht, h⟩)
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
  have hcount : ∀ nu : Measure ℝ, nu {0} = 0 →
      nu (A ∩ Set.Iio 0 ∪ (A ∩ {0} ∪ A ∩ Set.Ioi 0))
        = nu (A ∩ Set.Iio 0) + nu (A ∩ Set.Ioi 0) := by
    intro nu h0
    have hz : nu (A ∩ {0}) = 0 := measure_mono_null Set.inter_subset_right h0
    have hd23 : Disjoint (A ∩ ({0} : Set ℝ)) (A ∩ Set.Ioi 0) := by
      rw [Set.disjoint_iff]
      rintro t ⟨⟨_, ht0⟩, ⟨_, htpos⟩⟩
      rw [Set.mem_singleton_iff] at ht0
      rw [Set.mem_Ioi] at htpos
      subst ht0
      exact absurd htpos (lt_irrefl 0)
    have hd123 : Disjoint (A ∩ Set.Iio (0 : ℝ)) (A ∩ {0} ∪ A ∩ Set.Ioi 0) := by
      rw [Set.disjoint_iff]
      rintro t ⟨⟨_, htneg⟩, ht⟩
      rw [Set.mem_Iio] at htneg
      rcases ht with ⟨_, ht0⟩ | ⟨_, htpos⟩
      · rw [Set.mem_singleton_iff] at ht0
        subst ht0
        exact absurd htneg (lt_irrefl 0)
      · rw [Set.mem_Ioi] at htpos
        exact absurd htpos (by linarith)
    rw [measure_union hd123 (hm2.union hm3), measure_union hd23 hm3, hz, zero_add]
  rw [hsplit, hcount nu₁ h0₁, hcount nu₂ h0₂,
    hneg_agree _ hm1 Set.inter_subset_right,
    hpos_agree _ hm3 Set.inter_subset_right]

/-- On the spectral gap, the origin is null. -/
theorem measure_singleton_zero_of_gap {nu : Measure ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ t ∂nu, δ ≤ |t|) : nu {0} = 0 := by
  have hsub : ({0} : Set ℝ) ⊆ {t : ℝ | ¬ δ ≤ |t|} := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    simp only [Set.mem_setOf_eq, abs_zero, not_le]
    exact hδ
  exact measure_mono_null hsub (ae_iff.mp hgap)

/-- The pushforward under `t ↦ (t²)⁻¹` of a gapped measure is carried by `[0, δ⁻²]`. -/
theorem map_invSq_ae_mem_Icc {nu : Measure ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ t ∂nu, δ ≤ |t|) :
    ∀ᵐ y ∂(nu.map fun t => (t ^ 2)⁻¹), y ∈ Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹) := by
  rw [ae_map_iff ((measurable_id.pow_const 2).inv).aemeasurable measurableSet_Icc]
  filter_upwards [hgap] with t ht
  constructor
  · positivity
  · have h1 : δ ^ 2 ≤ t ^ 2 := by
      have h2 := sq_abs t
      nlinarith [abs_nonneg t]
    gcongr
    · positivity

/-- **Equal inverse moments identify the compact pushforward.**  Two gapped finite measures with
the same inverse even moments have the same pushforward under `t ↦ (t²)⁻¹`, by compact moment
determinacy on `[0, δ⁻²]`. -/
theorem map_invSq_eq_of_suzukiInverseMoments {nu₁ nu₂ : Measure ℝ}
    [IsFiniteMeasure nu₁] [IsFiniteMeasure nu₂] {δ : ℝ} (hδ : 0 < δ)
    (h₁ : ∀ᵐ t ∂nu₁, δ ≤ |t|) (h₂ : ∀ᵐ t ∂nu₂, δ ≤ |t|)
    (hq : ∀ n, suzukiInverseEvenMoment nu₁ n = suzukiInverseEvenMoment nu₂ n) :
    nu₁.map (fun t => (t ^ 2)⁻¹) = nu₂.map (fun t => (t ^ 2)⁻¹) := by
  have hIcc : MeasurableSet (Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹)) := measurableSet_Icc
  have hemb : MeasurableEmbedding ((↑) : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹) → ℝ) :=
    MeasurableEmbedding.subtype_coe hIcc
  have hres₁ : (nu₁.map fun t => (t ^ 2)⁻¹).restrict (Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹))
      = nu₁.map fun t => (t ^ 2)⁻¹ :=
    Measure.restrict_eq_self_of_ae_mem (map_invSq_ae_mem_Icc hδ h₁)
  have hres₂ : (nu₂.map fun t => (t ^ 2)⁻¹).restrict (Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹))
      = nu₂.map fun t => (t ^ 2)⁻¹ :=
    Measure.restrict_eq_self_of_ae_mem (map_invSq_ae_mem_Icc hδ h₂)
  haveI hf₁ : IsFiniteMeasure ((nu₁.map fun t => (t ^ 2)⁻¹).comap
      ((↑) : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹) → ℝ)) := by
    constructor
    rw [hemb.comap_apply]
    exact measure_lt_top _ _
  haveI hf₂ : IsFiniteMeasure ((nu₂.map fun t => (t ^ 2)⁻¹).comap
      ((↑) : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹) → ℝ)) := by
    constructor
    rw [hemb.comap_apply]
    exact measure_lt_top _ _
  have hmom : ∀ n : ℕ,
      (∫ x : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹), ((x : ℝ)) ^ n
          ∂((nu₁.map fun t => (t ^ 2)⁻¹).comap ((↑) : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹) → ℝ)))
        = ∫ x : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹), ((x : ℝ)) ^ n
          ∂((nu₂.map fun t => (t ^ 2)⁻¹).comap ((↑) : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹) → ℝ)) := by
    intro n
    rw [MeasureTheory.integral_subtype_comap hIcc (fun y => y ^ n),
      MeasureTheory.integral_subtype_comap hIcc (fun y => y ^ n)]
    have e₁ : ∫ y in Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹), y ^ n ∂(nu₁.map fun t => (t ^ 2)⁻¹)
        = ∫ y, y ^ n ∂(nu₁.map fun t => (t ^ 2)⁻¹) := by
      conv_rhs => rw [← hres₁]
    have e₂ : ∫ y in Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹), y ^ n ∂(nu₂.map fun t => (t ^ 2)⁻¹)
        = ∫ y, y ^ n ∂(nu₂.map fun t => (t ^ 2)⁻¹) := by
      conv_rhs => rw [← hres₂]
    rw [e₁, e₂, suzukiInverseMoment_pushforward, suzukiInverseMoment_pushforward]
    exact hq n
  have hsub := GaloisForLFunctions.HTGeometry.ext_of_forall_integral_pow_eq hmom
  calc nu₁.map (fun t => (t ^ 2)⁻¹)
      = ((nu₁.map fun t => (t ^ 2)⁻¹).comap
          ((↑) : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹) → ℝ)).map
            ((↑) : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹) → ℝ) := by
        rw [hemb.map_comap, Subtype.range_coe, hres₁]
    _ = ((nu₂.map fun t => (t ^ 2)⁻¹).comap
          ((↑) : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹) → ℝ)).map
            ((↑) : Set.Icc (0 : ℝ) ((δ ^ 2)⁻¹) → ℝ) := by rw [hsub]
    _ = nu₂.map (fun t => (t ^ 2)⁻¹) := by
        rw [hemb.map_comap, Subtype.range_coe, hres₂]

/-- **Complete determinacy** — the card's Theorem A determinacy claim: an even finite measure
with a spectral gap about the origin is determined by its inverse even moments. -/
theorem suzukiInverseMoment_determinacy {nu₁ nu₂ : Measure ℝ}
    [IsFiniteMeasure nu₁] [IsFiniteMeasure nu₂]
    (he₁ : nu₁.map (fun t => -t) = nu₁) (he₂ : nu₂.map (fun t => -t) = nu₂)
    {δ : ℝ} (hδ : 0 < δ) (h₁ : ∀ᵐ t ∂nu₁, δ ≤ |t|) (h₂ : ∀ᵐ t ∂nu₂, δ ≤ |t|)
    (hq : ∀ n, suzukiInverseEvenMoment nu₁ n = suzukiInverseEvenMoment nu₂ n) :
    nu₁ = nu₂ :=
  ext_of_even_of_map_invSq_eq he₁ he₂
    (measure_singleton_zero_of_gap hδ h₁) (measure_singleton_zero_of_gap hδ h₂)
    (map_invSq_eq_of_suzukiInverseMoments hδ h₁ h₂ hq)

/-! ## The free-boundary tangent -/

/-- The Fourier–Livšic quotient of a characteristic profile: `(z - i) F(z) / ((z + i) F(-z))`. -/
def suzukiFourierLivsic (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - Complex.I) * F z / ((z + Complex.I) * F (-z))

/-- **The free-boundary tangent of the Livšic quotient** — the card's `(17)`/`(25)`:
for a parameter family with first variation `-H` at the free boundary, the quotient's derivative
is the quotient itself times the anti-reflected logarithmic derivative
`Δ(z) = H(-z)/F(-z) - H(z)/F(z)`. -/
theorem hasDerivAt_suzukiFourierLivsic_freeBoundary
    {F : ℝ → ℂ → ℂ} {H : ℂ → ℂ} {z : ℂ}
    (hz : HasDerivAt (fun eps => F eps z) (-(H z)) 0)
    (hzneg : HasDerivAt (fun eps => F eps (-z)) (-(H (-z))) 0)
    (hF0 : F 0 z ≠ 0) (hF0neg : F 0 (-z) ≠ 0) (hzi : z + Complex.I ≠ 0) :
    HasDerivAt (fun eps => suzukiFourierLivsic (F eps) z)
      (suzukiFourierLivsic (F 0) z * (H (-z) / F 0 (-z) - H z / F 0 z)) 0 := by
  have hnum : HasDerivAt (fun eps => (z - Complex.I) * F eps z)
      ((z - Complex.I) * -(H z)) 0 := hz.const_mul _
  have hden : HasDerivAt (fun eps => (z + Complex.I) * F eps (-z))
      ((z + Complex.I) * -(H (-z))) 0 := hzneg.const_mul _
  have hden0 : (z + Complex.I) * F 0 (-z) ≠ 0 := mul_ne_zero hzi hF0neg
  have h : HasDerivAt (fun eps => (z - Complex.I) * F eps z / ((z + Complex.I) * F eps (-z)))
      (((z - Complex.I) * -(H z) * ((z + Complex.I) * F 0 (-z))
          - (z - Complex.I) * F 0 z * ((z + Complex.I) * -(H (-z))))
        / ((z + Complex.I) * F 0 (-z)) ^ 2) 0 := hnum.div hden hden0
  have hfun : (fun eps => suzukiFourierLivsic (F eps) z)
      = fun eps => (z - Complex.I) * F eps z / ((z + Complex.I) * F eps (-z)) := rfl
  rw [hfun]
  convert h using 1
  rw [suzukiFourierLivsic]
  field_simp
  ring

/-- **The parameter derivative of the Cayley inverse** — the transport factor of the card's
`(18)`: along any parameter path `w`, `d/dε [i (1 + w)/(1 - w)] = 2i/(1 - w)² · w'`. -/
theorem hasDerivAt_suzukiUpperCayleyInv_parameter {w : ℝ → ℂ} {w' : ℂ} {x : ℝ}
    (hw : HasDerivAt w w' x) (h1 : w x ≠ 1) :
    HasDerivAt (fun eps => suzukiUpperCayleyInv (w eps))
      (2 * Complex.I / (1 - w x) ^ 2 * w') x := by
  have hsub : (1 : ℂ) - w x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hnum : HasDerivAt (fun eps => 1 + w eps) w' x := hw.const_add 1
  have hden : HasDerivAt (fun eps => 1 - w eps) (-w') x := hw.const_sub 1
  have h : HasDerivAt (fun eps => Complex.I * ((1 + w eps) / (1 - w eps)))
      (Complex.I * ((w' * (1 - w x) - (1 + w x) * -w') / (1 - w x) ^ 2)) x :=
    (hnum.div hden hsub).const_mul Complex.I
  have hfun : (fun eps => suzukiUpperCayleyInv (w eps))
      = fun eps => Complex.I * ((1 + w eps) / (1 - w eps)) := rfl
  rw [hfun]
  convert h using 1
  field_simp
  ring

/-- **The free-boundary tangent of the Herglotz presentation** — the card's `(18)`:
if the characteristic's variation at the free boundary is `Θfree · Δ`, the Herglotz function moves
by `2i Θfree Δ / (1 - Θfree)²`. -/
theorem hasDerivAt_suzukiHerglotz_freeBoundary
    {Θ : ℝ → ℂ} {Θfree Δ : ℂ} {x : ℝ}
    (hΘ : HasDerivAt Θ (Θfree * Δ) x) (hΘx : Θ x = Θfree) (h1 : Θfree ≠ 1) :
    HasDerivAt (fun eps => suzukiUpperCayleyInv (Θ eps))
      (2 * Complex.I * Θfree * Δ / (1 - Θfree) ^ 2) x := by
  have h1' : Θ x ≠ 1 := by
    rw [hΘx]
    exact h1
  have h := hasDerivAt_suzukiUpperCayleyInv_parameter hΘ h1'
  rw [hΘx] at h
  convert h using 1
  have hsub : (1 : ℂ) - Θfree ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

end GaloisForLFunctions.RHTower
