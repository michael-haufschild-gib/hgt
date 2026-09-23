import GaloisForLFunctions.HTGeometry.KleinGordonEnergyConservation
import GaloisForLFunctions.HTGeometry.VolterraStrongKernel

/-!
# The Cauchy problem for a bounded potential: existence in the energy space

The energy estimate controls a solution by its data; it does not produce one. This file produces one.

In the energy variables `w = (⟨D⟩u, ∂ₜu)` the equation `∂ₜ²u = -⟨D⟩²u + Vu` is the first-order system
`∂ₜw = Jw + Nw` with `J` the generator of the rotation by `t⟨ξ⟩` and

`N (w₁, w₂) = (0, V ⟨D⟩⁻¹ w₁)`.

Since `‖⟨D⟩⁻¹‖ ≤ 1`, the perturbation `N` is a *bounded* operator on `L² × L²` of norm at most the
supremum of the potential — this is the whole point of the energy variables, and it is what makes the
problem a linear Volterra equation with a bounded kernel rather than a problem about unbounded
operators. Duhamel's formula

`w(t) = U(t)w₀ + ∫₀ᵗ U(t-s) N w(s) ds`

then has a unique continuous solution for every datum, by the perturbation series, with no smallness
hypothesis on the potential and no restriction on the time.

The potential is only asked to be measurable and bounded: no continuity, no decay, no smoothness.
That is far below the `C^{2d+5}` that the Fourier synthesis of clock probes needs.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The perturbation -/

section Potential

variable {V : E → ℂ} {b : ℝ}

/-- **The perturbation of the free evolution by a bounded potential**, in energy coordinates:
`(w₁, w₂) ↦ (0, V ⟨D⟩⁻¹ w₁)`. -/
def kgPotentialOp (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b) :
    KGEnergy E →L[ℂ] KGEnergy E :=
  (kgPair E).comp
    ((0 : KGEnergy E →L[ℂ] Lp (α := E) ℂ 2).prod
      (((lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb).comp
        kgFreqInvOp).comp (kgFst E)))

theorem kgPotentialOp_apply (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b)
    (v : KGEnergy E) :
    kgPotentialOp hV hb0 hb v
      = kgPair E (0, lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb
          (kgFreqInvOp v.fst)) := rfl

/-- **The perturbation is bounded by the supremum of the potential.** The factor `⟨D⟩⁻¹` is a
contraction, so no derivative is lost. -/
theorem norm_kgPotentialOp_le (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b) :
    ‖kgPotentialOp hV hb0 hb‖ ≤ b := by
  refine ContinuousLinearMap.opNorm_le_bound _ hb0 fun v => ?_
  rw [kgPotentialOp_apply, kgPair_apply, WithLp.norm_toLp_snd]
  have hv1 : ‖v.fst‖ ≤ ‖v‖ := WithLp.norm_fst_le _ v
  have hmul := (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb).le_of_opNorm_le
    (norm_lpBoundedMulCLM_le (p := 2) (μ := (volume : Measure E)) hV hb0 hb) (kgFreqInvOp v.fst)
  have hinv : ‖kgFreqInvOp (E := E) v.fst‖ ≤ ‖v.fst‖ := by
    have h := (kgFreqInvOp (E := E)).le_of_opNorm_le norm_kgFreqInvOp_le v.fst
    rwa [one_mul] at h
  calc ‖lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb (kgFreqInvOp v.fst)‖
      ≤ b * ‖kgFreqInvOp (E := E) v.fst‖ := hmul
    _ ≤ b * ‖v.fst‖ := mul_le_mul_of_nonneg_left hinv hb0
    _ ≤ b * ‖v‖ := mul_le_mul_of_nonneg_left hv1 hb0

/-! ## The Duhamel data -/

/-- The free evolution of the Cauchy datum: the inhomogeneous term of the Duhamel equation. -/
def kgFreeCurve (w₀ : KGEnergy E) (t : ℝ) : KGEnergy E := kgPropagator t w₀

/-- The Duhamel kernel: the perturbation, propagated from the source time to the observation
time. -/
def kgMildDuhamelKernel (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b) (t s : ℝ) :
    KGEnergy E →L[ℝ] KGEnergy E :=
  (((kgPropagator (t - s)).comp (kgPotentialOp hV hb0 hb)) :
    KGEnergy E →L[ℂ] KGEnergy E).restrictScalars ℝ

theorem kgMildDuhamelKernel_apply (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b)
    (t s : ℝ) (v : KGEnergy E) :
    kgMildDuhamelKernel hV hb0 hb t s v = kgPropagator (t - s) (kgPotentialOp hV hb0 hb v) := rfl

theorem continuous_kgFreeCurve (w₀ : KGEnergy E) : Continuous (kgFreeCurve w₀) :=
  continuous_kgPropagator_apply w₀

theorem norm_kgFreeCurve_le (w₀ : KGEnergy E) (t : ℝ) : ‖kgFreeCurve w₀ t‖ ≤ ‖w₀‖ :=
  le_of_eq (norm_kgPropagator_apply t w₀)

theorem norm_kgMildDuhamelKernel_le (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b)
    (t s : ℝ) : ‖kgMildDuhamelKernel hV hb0 hb t s‖ ≤ b := by
  rw [kgMildDuhamelKernel, ContinuousLinearMap.norm_restrictScalars]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  have h := mul_le_mul (norm_kgPropagator_le_one (E := E) (t - s))
    (norm_kgPotentialOp_le hV hb0 hb) (norm_nonneg _) zero_le_one
  rwa [one_mul] at h

/-- **The Duhamel kernel is strongly continuous.** The propagator is not norm continuous, so this is
the form the perturbation series has to consume. -/
theorem strongKernel_kgMildDuhamelKernel (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b) :
    StrongKernel (kgMildDuhamelKernel (E := E) hV hb0 hb) := by
  intro u hu
  have hcomp : Continuous fun p : ℝ × ℝ =>
      kgPropagator (p.1 - p.2) (kgPotentialOp hV hb0 hb (u p.2)) :=
    continuous_kgPropagator_comp (continuous_fst.sub continuous_snd)
      ((kgPotentialOp hV hb0 hb).continuous.comp (hu.comp continuous_snd))
  exact hcomp.congr fun p => (kgMildDuhamelKernel_apply hV hb0 hb p.1 p.2 (u p.2)).symm

end Potential

/-! ## The mild solution -/

section Solution

variable {V : E → ℂ} {b : ℝ}

/-- **The mild solution of the Klein–Gordon equation with a bounded potential**, in the energy
space. -/
def kgMildSolution (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b) (w₀ : KGEnergy E)
    (t : ℝ) : KGEnergy E :=
  volterraSolution (kgFreeCurve w₀) (kgMildDuhamelKernel hV hb0 hb) t

variable (hV : Measurable V) (hb0 : 0 ≤ b) (hb : ∀ ξ, ‖V ξ‖ ≤ b) (w₀ : KGEnergy E)

/-- **The mild solution is continuous in time.** -/
theorem continuous_kgMildSolution : Continuous (kgMildSolution hV hb0 hb w₀) :=
  continuous_volterraSolution_of_strong (continuous_kgFreeCurve w₀)
    (strongKernel_kgMildDuhamelKernel hV hb0 hb) hb0 (norm_nonneg w₀)
    (norm_kgMildDuhamelKernel_le hV hb0 hb) (norm_kgFreeCurve_le w₀)

/-- **The mild solution satisfies Duhamel's formula.** -/
theorem kgMildSolution_eq (t : ℝ) :
    kgMildSolution hV hb0 hb w₀ t
      = kgPropagator t w₀
        + ∫ s in (0 : ℝ)..t, kgMildDuhamelKernel hV hb0 hb t s (kgMildSolution hV hb0 hb w₀ s) :=
  volterraSolution_eq_of_strong (continuous_kgFreeCurve w₀)
    (strongKernel_kgMildDuhamelKernel hV hb0 hb) hb0 (norm_nonneg w₀)
    (norm_kgMildDuhamelKernel_le hV hb0 hb) (norm_kgFreeCurve_le w₀) t

/-- **The mild solution starts at the datum.** -/
theorem kgMildSolution_zero : kgMildSolution hV hb0 hb w₀ 0 = w₀ := by
  rw [kgMildSolution_eq hV hb0 hb w₀ 0, intervalIntegral.integral_same, add_zero,
    kgPropagator_zero_apply]

/-- **The energy of the mild solution grows at most exponentially**, at a rate set by the supremum
of the potential alone. -/
theorem norm_kgMildSolution_le (t : ℝ) :
    ‖kgMildSolution hV hb0 hb w₀ t‖ ≤ ‖w₀‖ * Real.exp (b * |t|) :=
  norm_volterraSolution_le_of_strong (continuous_kgFreeCurve w₀)
    (strongKernel_kgMildDuhamelKernel hV hb0 hb) hb0 (norm_nonneg w₀)
    (norm_kgMildDuhamelKernel_le hV hb0 hb) (norm_kgFreeCurve_le w₀) t

/-- **Uniqueness: Duhamel's formula has at most one continuous solution.** -/
theorem eq_kgMildSolution_of_duhamel {w : ℝ → KGEnergy E} (hw : Continuous w)
    (hduh : ∀ t : ℝ, w t = kgPropagator t w₀
      + ∫ s in (0 : ℝ)..t, kgMildDuhamelKernel hV hb0 hb t s (w s)) :
    w = kgMildSolution hV hb0 hb w₀ :=
  volterra_eq_of_eq_of_eq_of_strong (strongKernel_kgMildDuhamelKernel hV hb0 hb) hb0
    (norm_kgMildDuhamelKernel_le hV hb0 hb) hw (continuous_kgMildSolution hV hb0 hb w₀) hduh
    (kgMildSolution_eq hV hb0 hb w₀)

/-- **The energy estimate for the constructed solution.** The energy at time `t` is controlled by
the energy of the datum with an exponential rate set by the supremum of the potential alone — the
same shape as the estimate proved for classical solutions, now for the solution that exists. -/
theorem kgEnergy_kgMildSolution_le (t : ℝ) :
    kgEnergy (kgMildSolution hV hb0 hb w₀ t) ≤ kgEnergy w₀ * Real.exp (2 * b * |t|) := by
  have h := norm_kgMildSolution_le hV hb0 hb w₀ t
  have hpos : (0 : ℝ) ≤ ‖w₀‖ * Real.exp (b * |t|) := by positivity
  have hsq : ‖kgMildSolution hV hb0 hb w₀ t‖ ^ (2 : ℕ) ≤ (‖w₀‖ * Real.exp (b * |t|)) ^ (2 : ℕ) := by
    nlinarith [norm_nonneg (kgMildSolution hV hb0 hb w₀ t)]
  have hexp : (Real.exp (b * |t|)) ^ (2 : ℕ) = Real.exp (2 * b * |t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [kgEnergy_eq_norm_sq, kgEnergy_eq_norm_sq]
  refine hsq.trans (le_of_eq ?_)
  rw [mul_pow, hexp]

/-- **The Cauchy problem for a bounded measurable potential is globally well posed in the energy
space.** For every datum there is exactly one continuous curve satisfying Duhamel's formula, it
starts at the datum, and its energy is controlled by the datum with an exponential rate depending
only on the supremum of the potential. -/
theorem exists_unique_kgMildSolution :
    ∃! w : ℝ → KGEnergy E, Continuous w ∧
      ∀ t : ℝ, w t = kgPropagator t w₀
        + ∫ s in (0 : ℝ)..t, kgMildDuhamelKernel hV hb0 hb t s (w s) := by
  refine ⟨kgMildSolution hV hb0 hb w₀, ⟨continuous_kgMildSolution hV hb0 hb w₀,
    kgMildSolution_eq hV hb0 hb w₀⟩, ?_⟩
  rintro w ⟨hwc, hwd⟩
  exact eq_kgMildSolution_of_duhamel hV hb0 hb w₀ hwc hwd

end Solution

end GaloisForLFunctions.HTGeometry
