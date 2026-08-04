import GaloisForLFunctions.HTGeometry.KleinGordonStrongStability

/-!
# The field-level mild solution, for arbitrary `L²` data

The mild theory built so far lives in the energy space, on pairs `(⟨D⟩u, ∂ₜu)`. The classical theory
writes the Duhamel formula one level down, for the field itself:

`u(t) = cos(t⟨D⟩)f + (sin(t⟨D⟩)/⟨D⟩)h + ∫₀ᵗ (sin((t-s)⟨D⟩)/⟨D⟩) W u(s) ds`.

Every operator appearing here is a Fourier multiplier with symbol bounded by **one**, uniformly in
time — `|sin(r⟨ξ⟩)/⟨ξ⟩| ≤ ⟨ξ⟩⁻¹ ≤ 1`, the very cancellation that made the propagator differentiable
on regular data. So the Volterra layer applies with no regularity hypothesis on the data at all:
`f` and `h` are arbitrary elements of `L²`, and the solution exists, is unique among continuous
curves, and obeys `‖u(t)‖ ≤ (‖f‖+‖h‖)e^{‖W‖|t|}`.

The last statement identifies this construction with the strong solution: the strong field of
statement 68 is the field-level mild solution of its own Cauchy data, with `W = 0`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The half-order propagator `sin(t⟨D⟩)/⟨D⟩` -/

/-- The sine propagator of the field variables, `sin(t⟨D⟩)/⟨D⟩`. Unlike the energy-coordinate sine
it is bounded by one uniformly in time. -/
def kgSinFreqOp (t : ℝ) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMulCLM (measurable_kgSinOverFreq (E := E) t) zero_le_one (norm_kgSinOverFreq_le t)

theorem kgSinFreqOp_eq (t : ℝ) : kgSinFreqOp (E := E) t
    = fourierMulCLM (measurable_kgSinOverFreq (E := E) t) zero_le_one
      (norm_kgSinOverFreq_le t) := rfl

theorem norm_kgSinFreqOp_le (t : ℝ) : ‖kgSinFreqOp (E := E) t‖ ≤ 1 :=
  norm_fourierMulCLM_le _ _ _

theorem norm_kgSinFreqOp_apply_le (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgSinFreqOp t x‖ ≤ ‖x‖ := by
  have h := (kgSinFreqOp (E := E) t).le_of_opNorm_le (norm_kgSinFreqOp_le t) x
  rwa [one_mul] at h

theorem kgSinFreqOp_zero : kgSinFreqOp (E := E) 0 = 0 := by
  refine fourierMulCLM_eq_zero _ _ _ (Filter.Eventually.of_forall fun ξ => ?_)
  show ((Real.sin (0 * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ) = 0
  rw [zero_mul, Real.sin_zero, zero_div]
  norm_num

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem continuous_kgSinOverFreq_time (ξ : E) :
    Continuous fun t : ℝ => kgSinOverFreq t ξ := by
  show Continuous fun t : ℝ => ((Real.sin (t * kgFreq ξ) / kgFreq ξ : ℝ) : ℂ)
  refine Complex.continuous_ofReal.comp ?_
  exact (Real.continuous_sin.comp (continuous_id.mul continuous_const)).div_const _

/-- **The half-order propagator is strongly continuous.** -/
theorem continuous_kgSinFreqOp_apply (x : Lp ℂ 2 (volume : Measure E)) :
    Continuous fun t : ℝ => kgSinFreqOp t x := by
  rw [continuous_iff_continuousAt]
  intro t₀
  exact tendsto_fourierMulCLM_apply (l := nhds t₀)
    (fun t => measurable_kgSinOverFreq (E := E) t) (measurable_kgSinOverFreq (E := E) t₀)
    zero_le_one (fun t => norm_kgSinOverFreq_le t) (norm_kgSinOverFreq_le t₀)
    (fun ξ => (continuous_kgSinOverFreq_time ξ).continuousAt) x

theorem continuous_kgSinFreqOp_comp {ι : Type*} [TopologicalSpace ι] {r : ι → ℝ}
    {x : ι → Lp ℂ 2 (volume : Measure E)} (hr : Continuous r) (hx : Continuous x) :
    Continuous fun i => kgSinFreqOp (r i) (x i) :=
  continuous_of_strong_comp norm_kgSinFreqOp_le continuous_kgSinFreqOp_apply hr hx

/-! ## The Duhamel data at the level of the field -/

/-- The free field with arbitrary `L²` Cauchy data `(f, h)`. -/
def kgFieldFree (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  kgCosOp t f + kgSinFreqOp t h

theorem kgFieldFree_zero (f h : Lp ℂ 2 (volume : Measure E)) : kgFieldFree f h 0 = f := by
  rw [kgFieldFree, kgCosOp_zero, kgSinFreqOp_zero]
  simp

theorem continuous_kgFieldFree (f h : Lp ℂ 2 (volume : Measure E)) :
    Continuous (kgFieldFree f h) :=
  (continuous_kgCosOp_apply f).add (continuous_kgSinFreqOp_apply h)

theorem norm_kgFieldFree_le (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldFree f h t‖ ≤ ‖f‖ + ‖h‖ := by
  refine le_trans (norm_add_le _ _) ?_
  have h1 := norm_kgCosOp_apply_le t f
  have h2 := norm_kgSinFreqOp_apply_le t h
  linarith

/-- The Duhamel kernel of the field equation: the perturbation, propagated by the half-order
propagator. -/
def kgFieldKernel (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) (t s : ℝ) :
    Lp ℂ 2 (volume : Measure E) →L[ℝ] Lp ℂ 2 (volume : Measure E) :=
  (((kgSinFreqOp (t - s)).comp W :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)).restrictScalars ℝ)

theorem kgFieldKernel_apply (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (t s : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    kgFieldKernel W t s x = kgSinFreqOp (t - s) (W x) := rfl

theorem norm_kgFieldKernel_le {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {b : ℝ} (hW : ‖W‖ ≤ b) (t s : ℝ) : ‖kgFieldKernel W t s‖ ≤ b := by
  rw [kgFieldKernel, ContinuousLinearMap.norm_restrictScalars]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  have h := mul_le_mul (norm_kgSinFreqOp_le (E := E) (t - s)) hW (norm_nonneg _) zero_le_one
  rwa [one_mul] at h

/-- **The field Duhamel kernel is strongly continuous.** -/
theorem strongKernel_kgFieldKernel
    (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :
    StrongKernel (kgFieldKernel W) := by
  intro x hx
  have hcomp : Continuous fun p : ℝ × ℝ => kgSinFreqOp (p.1 - p.2) (W (x p.2)) :=
    continuous_kgSinFreqOp_comp (continuous_fst.sub continuous_snd)
      (W.continuous.comp (hx.comp continuous_snd))
  exact hcomp.congr fun p => (kgFieldKernel_apply W p.1 p.2 (x p.2)).symm

/-! ## The field-level mild solution -/

/-- **The mild solution of the field equation** `∂ₜ²u = -⟨D⟩²u + Wu` with Cauchy data `(f, h)`, for
arbitrary `f, h ∈ L²`. -/
def kgFieldMild (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  volterraSolution (kgFieldFree f h) (kgFieldKernel W) t

section Solution

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

theorem continuous_kgFieldMild (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (f h : Lp ℂ 2 (volume : Measure E)) : Continuous (kgFieldMild W f h) :=
  continuous_volterraSolution_of_strong (continuous_kgFieldFree f h)
    (strongKernel_kgFieldKernel W) hb0 (by positivity)
    (fun t s => norm_kgFieldKernel_le hW t s) (norm_kgFieldFree_le f h)

/-- **The field-level Duhamel formula.** -/
theorem kgFieldMild_eq (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMild W f h t
      = kgFieldFree f h t
        + ∫ s in (0 : ℝ)..t, kgFieldKernel W t s (kgFieldMild W f h s) :=
  volterraSolution_eq_of_strong (continuous_kgFieldFree f h) (strongKernel_kgFieldKernel W)
    hb0 (by positivity) (fun t s => norm_kgFieldKernel_le hW t s) (norm_kgFieldFree_le f h) t

theorem kgFieldMild_zero (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (f h : Lp ℂ 2 (volume : Measure E)) :
    kgFieldMild W f h 0 = f := by
  rw [kgFieldMild_eq hb0 hW f h 0, intervalIntegral.integral_same, add_zero, kgFieldFree_zero]

/-- **The field grows at most exponentially**, at a rate set by the norm of the perturbation. -/
theorem norm_kgFieldMild_le (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (f h : Lp ℂ 2 (volume : Measure E))
    (t : ℝ) : ‖kgFieldMild W f h t‖ ≤ (‖f‖ + ‖h‖) * Real.exp (b * |t|) :=
  norm_volterraSolution_le_of_strong (continuous_kgFieldFree f h) (strongKernel_kgFieldKernel W)
    hb0 (by positivity) (fun t s => norm_kgFieldKernel_le hW t s) (norm_kgFieldFree_le f h) t

/-- **Uniqueness of the field-level mild solution.** -/
theorem eq_kgFieldMild_of_duhamel (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (f h : Lp ℂ 2 (volume : Measure E)) {u : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hu : Continuous u)
    (hduh : ∀ t : ℝ, u t = kgFieldFree f h t
      + ∫ s in (0 : ℝ)..t, kgFieldKernel W t s (u s)) :
    u = kgFieldMild W f h :=
  volterra_eq_of_eq_of_eq_of_strong (strongKernel_kgFieldKernel W) hb0
    (fun t s => norm_kgFieldKernel_le hW t s) hu (continuous_kgFieldMild hb0 hW f h) hduh
    (kgFieldMild_eq hb0 hW f h)

/-- **Well-posedness of the field equation for arbitrary `L²` data.** -/
theorem exists_unique_kgFieldMild (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (f h : Lp ℂ 2 (volume : Measure E)) :
    ∃! u : ℝ → Lp ℂ 2 (volume : Measure E), Continuous u ∧
      ∀ t : ℝ, u t = kgFieldFree f h t
        + ∫ s in (0 : ℝ)..t, kgFieldKernel W t s (u s) := by
  refine ⟨kgFieldMild W f h, ⟨continuous_kgFieldMild hb0 hW f h, kgFieldMild_eq hb0 hW f h⟩, ?_⟩
  rintro u ⟨huc, hud⟩
  exact eq_kgFieldMild_of_duhamel hb0 hW f h huc hud

end Solution

/-! ## The free case, and the strong solution -/

theorem kgFieldMild_zero_op (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMild 0 f h t = kgFieldFree f h t := by
  have hker : kgFieldKernel (0 : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
      = fun _ _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E) →L[ℝ] Lp ℂ 2 (volume : Measure E)) := by
    funext r s
    rw [kgFieldKernel]
    simp
  rw [kgFieldMild, hker, volterraSolution_zero_kernel]

/-- `sin(t⟨D⟩)/⟨D⟩` is the energy-coordinate sine composed with `⟨D⟩⁻¹`. -/
theorem kgSinFreqOp_eq_comp (t : ℝ) :
    kgSinFreqOp (E := E) t = (kgSinOp t).comp kgFreqInvOp :=
  (kgSinOp_comp_kgFreqInvOp t).symm

/-- **The strong field is the field-level free solution of its own Cauchy data.** So the strong
solution of statement 68 and the mild solution of this file are the same object where both are
defined. -/
theorem kgFreeField_eq_kgFieldFree (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFreeField f h t = kgFieldFree (kgFreqInvOp (kgFreqInvOp f)) (kgFreqInvOp h) t := by
  rw [kgFieldFree, kgFreeField, kgSinFreqOp_eq_comp]
  rfl

/-- **The strong field is the mild solution of the free field equation.** -/
theorem kgFreeField_eq_kgFieldMild (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFreeField f h t
      = kgFieldMild 0 (kgFreqInvOp (kgFreqInvOp f)) (kgFreqInvOp h) t := by
  rw [kgFieldMild_zero_op, kgFreeField_eq_kgFieldFree]

end GaloisForLFunctions.HTGeometry
