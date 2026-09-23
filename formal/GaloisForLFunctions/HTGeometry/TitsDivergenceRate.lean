import GaloisForLFunctions.HTGeometry.ObserverHomothety
import GaloisForLFunctions.HTGeometry.ObserverBoundaryAtInfinity

/-!
# The divergence rate of two rays, and the Tits metric

The distance between two exponential rays grows at most linearly and its ratio to the time is
nondecreasing, so the rate

```text
lim_{t → ∞} d (exp (t T), exp (t S)) / t
```

exists.  This is the Tits distance between the two boundary points: it is defined for arbitrary
directions, so between boundary points of *different* apartments, and inside an apartment it is
the chordal distance of the unit directions already computed.

Monotonicity is the homothety contraction, and the linear bound is the triangle inequality
through the reference metric.  A monotone bounded quantity converges, which is the whole of the
argument.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Filter Topology

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## The distance between two rays -/

/-- The distance between two exponential rays at time `t`. -/
noncomputable def rayDist {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) (t : ℝ) : ℝ :=
  observerDist (isSymmetric_metricRay hT hn t) hn (isSymmetric_metricRay hS hn t)

/-! ## Reparametrising a ray -/

omit [FiniteDimensional ℂ E] in
theorem coe_smul_op (r : ℝ) (X : E →L[ℂ] E) : ((r : ℂ)) • X = r • X :=
  Complex.coe_smul r X

theorem metricRay_smul_left (T : E →ₗ[ℂ] E) (r t : ℝ) :
    (metricRay ((r : ℝ) • T) t : E →L[ℂ] E) = metricRay T (t * r) := by
  have h : LinearMap.toContinuousLinearMap ((r : ℝ) • T)
      = r • LinearMap.toContinuousLinearMap T := by
    ext x
    simp
  rw [metricRay, metricRay, h, ← coe_smul_op, smul_smul, ← Complex.ofReal_mul]

theorem metricRay_smul_left_coe (T : E →ₗ[ℂ] E) (r t : ℝ) :
    ((metricRay ((r : ℝ) • T) t : E →ₗ[ℂ] E)) = ((metricRay T (t * r) : E →ₗ[ℂ] E)) :=
  congrArg (fun X : E →L[ℂ] E => (X : E →ₗ[ℂ] E)) (metricRay_smul_left T r t)

theorem metricRay_zero (T : E →ₗ[ℂ] E) : (metricRay T 0 : E →L[ℂ] E) = 1 := by
  rw [metricRay]
  simp

/-! ## The ratio is nondecreasing -/

/-- **The ratio of the distance to the time is nondecreasing.**  This is the homothety
contraction, reparametrised. -/
theorem rayDist_div_mono {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    rayDist hT hS hn s / s ≤ rayDist hT hS hn t / t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hlam0 : 0 ≤ s / t := div_nonneg (le_of_lt hs) (le_of_lt ht)
  have hlam1 : s / t ≤ 1 := div_le_one_of_le₀ hst (le_of_lt ht)
  have hkey := observerDist_metricRay_smul_le (isSymmetric_smul_real hT t)
    (isSymmetric_smul_real hS t) hn hlam0 hlam1
  have hTs : ((metricRay ((t : ℝ) • T) (s / t) : E →ₗ[ℂ] E))
      = ((metricRay T s : E →ₗ[ℂ] E)) := by
    rw [metricRay_smul_left_coe, div_mul_cancel₀ _ (ne_of_gt ht)]
  have hSs : ((metricRay ((t : ℝ) • S) (s / t) : E →ₗ[ℂ] E))
      = ((metricRay S s : E →ₗ[ℂ] E)) := by
    rw [metricRay_smul_left_coe, div_mul_cancel₀ _ (ne_of_gt ht)]
  have hTt : ((metricRay ((t : ℝ) • T) 1 : E →ₗ[ℂ] E)) = ((metricRay T t : E →ₗ[ℂ] E)) := by
    rw [metricRay_smul_left_coe, one_mul]
  have hSt : ((metricRay ((t : ℝ) • S) 1 : E →ₗ[ℂ] E)) = ((metricRay S t : E →ₗ[ℂ] E)) := by
    rw [metricRay_smul_left_coe, one_mul]
  rw [observerDist_congr _ (isSymmetric_metricRay hT hn s) _
      (isSymmetric_metricRay hS hn s) hn hTs hSs,
    observerDist_congr _ (isSymmetric_metricRay hT hn t) _
      (isSymmetric_metricRay hS hn t) hn hTt hSt] at hkey
  rw [div_le_div_iff₀ hs ht]
  calc rayDist hT hS hn s * t ≤ (s / t * rayDist hT hS hn t) * t := by
        exact mul_le_mul_of_nonneg_right hkey (le_of_lt ht)
    _ = rayDist hT hS hn t * s := by
        field_simp

/-! ## The linear bound -/

/-- **The distance between two rays grows at most linearly.** -/
theorem rayDist_le {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) {t : ℝ} (ht : 0 ≤ t) :
    rayDist hT hS hn t
      ≤ t * (ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T)
        + ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap S)) := by
  have hzero : ((metricRay T 0 : E →ₗ[ℂ] E)) = ((metricRay S 0 : E →ₗ[ℂ] E)) := by
    have h1 := metricRay_zero (E := E) T
    have h2 := metricRay_zero (E := E) S
    rw [show ((metricRay T 0 : E →ₗ[ℂ] E))
        = ((metricRay T 0 : E →L[ℂ] E) : E →ₗ[ℂ] E) from rfl, h1,
      show ((metricRay S 0 : E →ₗ[ℂ] E))
        = ((metricRay S 0 : E →L[ℂ] E) : E →ₗ[ℂ] E) from rfl, h2]
  have htri := observerDist_triangle (isSymmetric_metricRay hT hn t)
    (isSymmetric_metricRay hT hn 0) (isSymmetric_metricRay hS hn t) hn
    (fun x hx => inner_metricRay_pos hT hn hx t)
    (fun x hx => inner_metricRay_pos hT hn hx 0)
    (fun x hx => inner_metricRay_pos hS hn hx t)
  have hfirst : observerDist (isSymmetric_metricRay hT hn t) hn
      (isSymmetric_metricRay hT hn 0)
      = t * ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T) := by
    rw [observerDist_metricRay hT hn t 0, zero_sub, abs_neg, abs_of_nonneg ht]
  have hsecond : observerDist (isSymmetric_metricRay hT hn 0) hn
      (isSymmetric_metricRay hS hn t)
      = t * ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap S) := by
    rw [observerDist_congr _ (isSymmetric_metricRay hS hn 0) _
        (isSymmetric_metricRay hS hn t) hn hzero rfl,
      observerDist_metricRay hS hn 0 t, sub_zero, abs_of_nonneg ht]
  rw [rayDist]
  calc observerDist (isSymmetric_metricRay hT hn t) hn (isSymmetric_metricRay hS hn t)
      ≤ observerDist (isSymmetric_metricRay hT hn t) hn (isSymmetric_metricRay hT hn 0)
        + observerDist (isSymmetric_metricRay hT hn 0) hn
          (isSymmetric_metricRay hS hn t) := htri
    _ = t * (ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T)
        + ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap S)) := by
        rw [hfirst, hsecond, mul_add]


/-! ## The divergence rate -/

/-- The ratio of distance to time, frozen below time one so that it is monotone on the line. -/
noncomputable def rayRate {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) (t : ℝ) : ℝ :=
  rayDist hT hS hn (max t 1) / max t 1

theorem monotone_rayRate {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) : Monotone (rayRate hT hS hn) := by
  intro a c hac
  exact rayDist_div_mono hT hS hn (lt_of_lt_of_le zero_lt_one (le_max_right a 1))
    (max_le_max hac le_rfl)

theorem rayRate_le {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) (t : ℝ) :
    rayRate hT hS hn t ≤ ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T)
      + ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap S) := by
  have hm : (0 : ℝ) < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right t 1)
  have h := rayDist_le hT hS hn (le_of_lt hm)
  rw [rayRate, div_le_iff₀ hm]
  linarith

theorem bddAbove_range_rayRate {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) : BddAbove (Set.range (rayRate hT hS hn)) := by
  refine ⟨ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap T)
    + ContinuousLinearMap.hsNorm (LinearMap.toContinuousLinearMap S), ?_⟩
  rintro _ ⟨t, rfl⟩
  exact rayRate_le hT hS hn t

/-- **The Tits distance between the boundary points of two rays**: the rate at which the two rays
diverge.  It is defined for arbitrary directions, so between boundary points of different
apartments. -/
noncomputable def titsRate {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) : ℝ :=
  ⨆ t : ℝ, rayRate hT hS hn t

/-- **The divergence rate exists.**  A monotone bounded quantity converges. -/
theorem tendsto_rayDist_div {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank ℂ E = n) :
    Tendsto (fun t => rayDist hT hS hn t / t) atTop (𝓝 (titsRate hT hS hn)) := by
  have hmain : Tendsto (rayRate hT hS hn) atTop (𝓝 (titsRate hT hS hn)) :=
    tendsto_atTop_ciSup (monotone_rayRate hT hS hn) (bddAbove_range_rayRate hT hS hn)
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [rayRate, max_eq_left ht]

/-! ## Inside an apartment -/

/-- **Inside an apartment the Tits distance is the chordal distance of the unit directions.**  So
the rate defined for arbitrary directions extends the metric already computed on a flat. -/
theorem titsRate_diagOp (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    (w w' : Fin n → ℝ) (hw : ∑ i, w i ^ (2 : ℕ) = 1) (hw' : ∑ i, w' i ^ (2 : ℕ) = 1) :
    titsRate (isSymmetric_diagOp b w) (isSymmetric_diagOp b w') hn
      = Real.sqrt (2 - 2 * ∑ i, w i * w' i) := by
  have hconst : Tendsto (fun t => rayDist (isSymmetric_diagOp b w) (isSymmetric_diagOp b w') hn t
      / t) atTop (𝓝 (Real.sqrt (2 - 2 * ∑ i, w i * w' i))) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [rayDist, observerDist_metricRay_diagOp_unit b hn w w' hw hw' t, abs_of_pos ht,
      mul_div_cancel_left₀ _ (ne_of_gt ht)]
  exact tendsto_nhds_unique (tendsto_rayDist_div _ _ hn) hconst

end GaloisForLFunctions.HTGeometry
