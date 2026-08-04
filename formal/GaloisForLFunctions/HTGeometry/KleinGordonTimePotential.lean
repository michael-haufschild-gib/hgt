import GaloisForLFunctions.HTGeometry.KleinGordonPotentialUniqueness

/-!
# The field equation with a time-dependent perturbation

A clock reads a field that is not static. The whole mild theory built so far fixes one bounded
operator `W`; this file replaces it by a curve of them,

`∂ₜ²u = -⟨D⟩²u + W(t)u`,

which is the equation an observer in a time-varying background actually solves.

Nothing in the Volterra layer used the autonomy of the kernel — it takes an arbitrary strongly
continuous, uniformly bounded family `K(t,s)` — so the existence, uniqueness and exponential bound
transfer verbatim once the new kernel `sin((t-s)⟨D⟩)/⟨D⟩ ∘ W(s)` is shown to be strongly continuous.
That is where the hypotheses on `W` enter, and they are the weakest ones the corpus's own idiom
supports: a uniform norm bound and strong continuity, exactly the pair that makes a propagator family
composable with continuous curves.

The autonomous theory is the constant case, definitionally.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The time-dependent Duhamel kernel -/

/-- The Duhamel kernel of the field equation with a time-dependent perturbation: the perturbation at
the source time, propagated by the half-order propagator over the elapsed time. -/
def kgFieldKernelT
    (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))) (t s : ℝ) :
    Lp ℂ 2 (volume : Measure E) →L[ℝ] Lp ℂ 2 (volume : Measure E) :=
  (((kgSinFreqOp (t - s)).comp (W s) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)).restrictScalars ℝ)

theorem kgFieldKernelT_apply
    (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))) (t s : ℝ)
    (x : Lp ℂ 2 (volume : Measure E)) :
    kgFieldKernelT W t s x = kgSinFreqOp (t - s) (W s x) := rfl

/-- The autonomous kernel is the constant case. -/
theorem kgFieldKernelT_const
    (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)) :
    kgFieldKernelT (fun _ : ℝ => W) = kgFieldKernel W := rfl

section Kernel

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

theorem norm_kgFieldKernelT_le (hW : ∀ r : ℝ, ‖W r‖ ≤ b) (t s : ℝ) :
    ‖kgFieldKernelT W t s‖ ≤ b := by
  rw [kgFieldKernelT, ContinuousLinearMap.norm_restrictScalars]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  have h := mul_le_mul (norm_kgSinFreqOp_le (E := E) (t - s)) (hW s) (norm_nonneg _) zero_le_one
  rwa [one_mul] at h

/-- **The time-dependent Duhamel kernel is strongly continuous.** -/
theorem strongKernel_kgFieldKernelT (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) :
    StrongKernel (kgFieldKernelT W) := by
  intro x hx
  have hWx : Continuous fun s : ℝ => W s (x s) :=
    continuous_of_strong_comp hWb hWs continuous_id hx
  have hcomp : Continuous fun p : ℝ × ℝ => kgSinFreqOp (p.1 - p.2) (W p.2 (x p.2)) :=
    continuous_kgSinFreqOp_comp (continuous_fst.sub continuous_snd) (hWx.comp continuous_snd)
  exact hcomp.congr fun p => (kgFieldKernelT_apply W p.1 p.2 (x p.2)).symm

end Kernel

/-! ## The mild solution -/

/-- **The mild solution of the field equation with a time-dependent perturbation.** -/
def kgFieldMildT (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  volterraSolution (kgFieldFree f h) (kgFieldKernelT W) t

/-- **The autonomous theory is the constant case.** -/
theorem kgFieldMildT_const (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (f h : Lp ℂ 2 (volume : Measure E)) : kgFieldMildT (fun _ : ℝ => W) f h = kgFieldMild W f h :=
  rfl

section Solution

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

theorem continuous_kgFieldMildT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f h : Lp ℂ 2 (volume : Measure E)) : Continuous (kgFieldMildT W f h) :=
  continuous_volterraSolution_of_strong (continuous_kgFieldFree f h)
    (strongKernel_kgFieldKernelT hWb hWs) hb0 (by positivity)
    (fun t s => norm_kgFieldKernelT_le hWb t s) (norm_kgFieldFree_le f h)

/-- **The Duhamel formula for a time-dependent perturbation.** -/
theorem kgFieldMildT_eq (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMildT W f h t
      = kgFieldFree f h t
        + ∫ s in (0 : ℝ)..t, kgFieldKernelT W t s (kgFieldMildT W f h s) :=
  volterraSolution_eq_of_strong (continuous_kgFieldFree f h)
    (strongKernel_kgFieldKernelT hWb hWs) hb0 (by positivity)
    (fun t s => norm_kgFieldKernelT_le hWb t s) (norm_kgFieldFree_le f h) t

theorem kgFieldMildT_zero (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f h : Lp ℂ 2 (volume : Measure E)) : kgFieldMildT W f h 0 = f := by
  rw [kgFieldMildT_eq hb0 hWb hWs f h 0, intervalIntegral.integral_same, add_zero,
    kgFieldFree_zero]

/-- **The field grows at most exponentially**, at a rate set by the uniform bound. -/
theorem norm_kgFieldMildT_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMildT W f h t‖ ≤ (‖f‖ + ‖h‖) * Real.exp (b * |t|) :=
  norm_volterraSolution_le_of_strong (continuous_kgFieldFree f h)
    (strongKernel_kgFieldKernelT hWb hWs) hb0 (by positivity)
    (fun t s => norm_kgFieldKernelT_le hWb t s) (norm_kgFieldFree_le f h) t

/-- **Uniqueness of the mild solution.** -/
theorem eq_kgFieldMildT_of_duhamel (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f h : Lp ℂ 2 (volume : Measure E)) {u : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hu : Continuous u)
    (hduh : ∀ t : ℝ, u t = kgFieldFree f h t
      + ∫ s in (0 : ℝ)..t, kgFieldKernelT W t s (u s)) :
    u = kgFieldMildT W f h :=
  volterra_eq_of_eq_of_eq_of_strong (strongKernel_kgFieldKernelT hWb hWs) hb0
    (fun t s => norm_kgFieldKernelT_le hWb t s) hu
    (continuous_kgFieldMildT hb0 hWb hWs f h) hduh (kgFieldMildT_eq hb0 hWb hWs f h)

/-- **Well-posedness of the field equation with a time-dependent perturbation.** -/
theorem exists_unique_kgFieldMildT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f h : Lp ℂ 2 (volume : Measure E)) :
    ∃! u : ℝ → Lp ℂ 2 (volume : Measure E), Continuous u ∧
      ∀ t : ℝ, u t = kgFieldFree f h t
        + ∫ s in (0 : ℝ)..t, kgFieldKernelT W t s (u s) := by
  refine ⟨kgFieldMildT W f h,
    ⟨continuous_kgFieldMildT hb0 hWb hWs f h, kgFieldMildT_eq hb0 hWb hWs f h⟩, ?_⟩
  rintro u ⟨huc, hud⟩
  exact eq_kgFieldMildT_of_duhamel hb0 hWb hWs f h huc hud

theorem intervalIntegrable_kgFieldKernelT (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    {u : ℝ → Lp ℂ 2 (volume : Measure E)} (hu : Continuous u) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => kgFieldKernelT W t s (u s)) volume 0 t :=
  (((strongKernel_kgFieldKernelT hWb hWs) u hu).comp
    (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t

end Solution

/-! ## Linearity in the Cauchy data -/

section Linear

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

theorem kgFieldFree_linear (a c : ℂ) (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldFree (a • f₁ + c • f₂) (a • h₁ + c • h₂) t
      = a • kgFieldFree f₁ h₁ t + c • kgFieldFree f₂ h₂ t := by
  rw [kgFieldFree, kgFieldFree, kgFieldFree, map_add, map_add, map_smul, map_smul, map_smul,
    map_smul, smul_add, smul_add]
  abel

/-- **The solution is linear in the Cauchy data.** -/
theorem kgFieldMildT_linear (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (a c : ℂ) (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMildT W (a • f₁ + c • f₂) (a • h₁ + c • h₂) t
      = a • kgFieldMildT W f₁ h₁ t + c • kgFieldMildT W f₂ h₂ t := by
  have hc1 := continuous_kgFieldMildT hb0 hWb hWs f₁ h₁
  have hc2 := continuous_kgFieldMildT hb0 hWb hWs f₂ h₂
  have hcand : Continuous fun τ : ℝ =>
      a • kgFieldMildT W f₁ h₁ τ + c • kgFieldMildT W f₂ h₂ τ :=
    (continuous_const_smul a |>.comp hc1).add (continuous_const_smul c |>.comp hc2)
  have hduh : ∀ τ : ℝ, a • kgFieldMildT W f₁ h₁ τ + c • kgFieldMildT W f₂ h₂ τ
      = kgFieldFree (a • f₁ + c • f₂) (a • h₁ + c • h₂) τ
        + ∫ s in (0 : ℝ)..τ, kgFieldKernelT W τ s
            (a • kgFieldMildT W f₁ h₁ s + c • kgFieldMildT W f₂ h₂ s) := by
    intro τ
    have hI1 := intervalIntegrable_kgFieldKernelT hWb hWs hc1 τ
    have hI2 := intervalIntegrable_kgFieldKernelT hWb hWs hc2 τ
    have hIa : IntervalIntegrable
        (fun s : ℝ => a • kgFieldKernelT W τ s (kgFieldMildT W f₁ h₁ s)) volume 0 τ := hI1.smul a
    have hIc : IntervalIntegrable
        (fun s : ℝ => c • kgFieldKernelT W τ s (kgFieldMildT W f₂ h₂ s)) volume 0 τ := hI2.smul c
    have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) τ, kgFieldKernelT W τ s
        (a • kgFieldMildT W f₁ h₁ s + c • kgFieldMildT W f₂ h₂ s)
        = a • kgFieldKernelT W τ s (kgFieldMildT W f₁ h₁ s)
          + c • kgFieldKernelT W τ s (kgFieldMildT W f₂ h₂ s) := by
      intro s _
      rw [kgFieldKernelT_apply, kgFieldKernelT_apply, kgFieldKernelT_apply, map_add, map_smul,
        map_smul, map_add, map_smul, map_smul]
    have hint : (∫ s in (0 : ℝ)..τ, kgFieldKernelT W τ s
          (a • kgFieldMildT W f₁ h₁ s + c • kgFieldMildT W f₂ h₂ s))
        = a • (∫ s in (0 : ℝ)..τ, kgFieldKernelT W τ s (kgFieldMildT W f₁ h₁ s))
          + c • ∫ s in (0 : ℝ)..τ, kgFieldKernelT W τ s (kgFieldMildT W f₂ h₂ s) := by
      rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hIa hIc,
        intervalIntegral.integral_smul, intervalIntegral.integral_smul]
    rw [hint, kgFieldFree_linear, kgFieldMildT_eq hb0 hWb hWs f₁ h₁ τ,
      kgFieldMildT_eq hb0 hWb hWs f₂ h₂ τ, smul_add, smul_add]
    abel
  have hfin := eq_kgFieldMildT_of_duhamel hb0 hWb hWs (a • f₁ + c • f₂) (a • h₁ + c • h₂)
    hcand hduh
  exact (congrFun hfin t).symm

theorem kgFieldMildT_add (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMildT W (f₁ + f₂) (h₁ + h₂) t
      = kgFieldMildT W f₁ h₁ t + kgFieldMildT W f₂ h₂ t := by
  have h := kgFieldMildT_linear hb0 hWb hWs 1 1 f₁ h₁ f₂ h₂ t
  simpa using h

theorem kgFieldMildT_smul (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (a : ℂ) (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMildT W (a • f) (a • h) t = a • kgFieldMildT W f h t := by
  have h0 := kgFieldMildT_linear hb0 hWb hWs a 0 f h f h t
  simpa using h0

theorem kgFieldMildT_sub (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMildT W (f₁ - f₂) (h₁ - h₂) t
      = kgFieldMildT W f₁ h₁ t - kgFieldMildT W f₂ h₂ t := by
  have h := kgFieldMildT_linear hb0 hWb hWs 1 (-1) f₁ h₁ f₂ h₂ t
  simpa [sub_eq_add_neg] using h

/-- **Continuous dependence on the Cauchy data.** -/
theorem norm_kgFieldMildT_sub_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMildT W f₁ h₁ t - kgFieldMildT W f₂ h₂ t‖
      ≤ (‖f₁ - f₂‖ + ‖h₁ - h₂‖) * Real.exp (b * |t|) := by
  rw [← kgFieldMildT_sub hb0 hWb hWs]
  exact norm_kgFieldMildT_le hb0 hWb hWs (f₁ - f₂) (h₁ - h₂) t

/-! ## The solution operator -/

variable (W b)

/-- The solution operator of the time-dependent equation, as a linear map. -/
def kgSolutionTLM (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (t : ℝ) :
    (Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E)) →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure E) where
  toFun w := kgFieldMildT W w.1 w.2 t
  map_add' w₁ w₂ := kgFieldMildT_add hb0 hWb hWs w₁.1 w₁.2 w₂.1 w₂.2 t
  map_smul' a w := kgFieldMildT_smul hb0 hWb hWs a w.1 w.2 t

/-- **The solution operator of the time-dependent equation**, with an explicit bound. -/
def kgSolutionTCLM (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (t : ℝ) :
    (Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E)) →L[ℂ]
      Lp ℂ 2 (volume : Measure E) :=
  LinearMap.mkContinuous (kgSolutionTLM W b hb0 hWb hWs t) (2 * Real.exp (b * |t|)) (by
    intro w
    have hle := norm_kgFieldMildT_le hb0 hWb hWs w.1 w.2 t
    have h1 : ‖w.1‖ ≤ ‖w‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have h2 : ‖w.2‖ ≤ ‖w‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hexp : (0 : ℝ) < Real.exp (b * |t|) := Real.exp_pos _
    calc ‖kgFieldMildT W w.1 w.2 t‖ ≤ (‖w.1‖ + ‖w.2‖) * Real.exp (b * |t|) := hle
      _ ≤ (2 * ‖w‖) * Real.exp (b * |t|) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hexp)
      _ = 2 * Real.exp (b * |t|) * ‖w‖ := by ring)

theorem kgSolutionTCLM_apply (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (t : ℝ)
    (w : Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E)) :
    kgSolutionTCLM W b hb0 hWb hWs t w = kgFieldMildT W w.1 w.2 t := rfl

theorem norm_kgSolutionTCLM_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (t : ℝ) :
    ‖kgSolutionTCLM W b hb0 hWb hWs t‖ ≤ 2 * Real.exp (b * |t|) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end Linear

end GaloisForLFunctions.HTGeometry
