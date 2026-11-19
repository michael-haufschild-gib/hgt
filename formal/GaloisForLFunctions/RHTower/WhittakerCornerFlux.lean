import GaloisForLFunctions.RHTower.WhittakerStreamCorner
import GaloisForLFunctions.RHTower.ModularArcGrowingModePositivity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Boundary jets and nonvanishing Whittaker corner flux

The actual decaying cosine modes are bounded smooth periodic solutions of
the axisymmetric equation above the modular arc. Their radial flux extends
to the corner and equals minus three halves of the trace derivative there.
In particular smooth boundary data need not have vanishing corner flux.
-/

noncomputable section
open Set Filter Topology
open scoped ContDiff BigOperators
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero
namespace RHTower.ModularCorner
set_option autoImplicit false

/-- Every Bessel moment is smooth on its actual positive parameter domain. -/
theorem contDiffOn_kMoment (j : ℕ) : ContDiffOn ℝ ∞ (kMoment j) (Ioi 0) := by
  apply contDiffOn_infty.mpr
  intro n
  induction n generalizing j with
  | zero => exact contDiffOn_zero.mpr (continuousOn_kMoment j)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun r hr => (differentiableAt_kMoment j hr).differentiableWithinAt, ?_, ?_⟩
    · intro hn
      simp at hn
    · exact (ih (j + 1)).neg.congr (fun r hr => deriv_kMoment j hr)

/-- A single actual summand of the finite Whittaker potential. -/
def cosineMode (k u y : ℝ) : ℝ := kMoment 0 (k * y) * Real.cos (k * u)

/-- Radial derivative along the ray through the physical point `(u,y)`. -/
def cosineRadialFlux (k u y : ℝ) : ℝ :=
  -(k * u * kMoment 0 (k * y) * Real.sin (k * u)) -
    k * y * kMoment 1 (k * y) * Real.cos (k * u)

/-- The radial derivative restricted to the actual modular arc. -/
def cosineArcFlux (k u : ℝ) : ℝ := cosineRadialFlux k u (modularArcHeight u)

/-- Euclidean distance along the arc to the upper-right modular corner. -/
def arcCornerDistance (u : ℝ) : ℝ :=
  Real.sqrt ((u - 1 / 2) ^ 2 + (modularArcHeight u - modularArcHeight (1 / 2)) ^ 2)

theorem continuous_arcCornerDistance : Continuous arcCornerDistance := by
  unfold arcCornerDistance modularArcHeight
  fun_prop

theorem arcCornerDistance_corner : arcCornerDistance (1 / 2) = 0 := by
  simp only [arcCornerDistance, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_add, Real.sqrt_zero]

private theorem linear_apply_pair (L : (ℝ × ℝ) →L[ℝ] ℝ) (a b : ℝ) :
    L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have he : (a, b) = a • ((1 : ℝ), 0) + b • ((0 : ℝ), 1) := by
    ext <;> simp
  rw [he, map_add, map_smul, map_smul]
  rfl

private theorem derivative_zero_of_even {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (he : ∀ t, f (-t) = f t) : d = 0 := by
  have hf0 : HasDerivAt f d (-(0 : ℝ)) := by simpa only [neg_zero] using hf
  have hneg : HasDerivAt (fun t => f (-t)) (-d) 0 := by
    convert! hf0.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id (0 : ℝ)).neg using 1
    simp [smul_eq_mul]
  rw [show (fun t => f (-t)) = f from funext he] at hneg
  have hh := hf.unique hneg
  linarith only [hh]

/-- For every differentiable even periodic potential, the corner normal jet is fixed by its trace. -/
theorem corner_radial_deriv_eq_trace_deriv {W : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ}
    (hW : HasFDerivAt W L ((1 / 2 : ℝ), modularArcHeight (1 / 2)))
    (heven : ∀ u y, W (-u, y) = W (u, y))
    (hperiod : ∀ u y, W (u + 1, y) = W (u, y)) :
    deriv (fun t : ℝ => W ((1 + t) * (1 / 2), (1 + t) * modularArcHeight (1 / 2))) 0 =
      -(3 / 2 : ℝ) * deriv (fun u => W (u, modularArcHeight u)) (1 / 2) := by
  have haxis : HasDerivAt (fun t : ℝ => W (1 / 2 + t, modularArcHeight (1 / 2)))
      (L (1, 0)) 0 := by
    have hc : HasDerivAt (fun t : ℝ => (1 / 2 + t, modularArcHeight (1 / 2))) (1, 0) 0 := by
      convert! ((hasDerivAt_id (0 : ℝ)).const_add (1 / 2 : ℝ)).prodMk
        (hasDerivAt_const (0 : ℝ) (modularArcHeight (1 / 2))) using 1
    have hw : HasFDerivAt W L ((1 / 2 : ℝ) + 0, modularArcHeight (1 / 2)) := by
      simpa only [add_zero] using hW
    exact hw.comp_hasDerivAt 0 hc
  have hx : L (1, 0) = 0 := by
    apply derivative_zero_of_even haxis
    intro t
    calc
      W (1 / 2 + -t, modularArcHeight (1 / 2)) =
          W (-(1 / 2 + t) + 1, modularArcHeight (1 / 2)) :=
        congrArg W (Prod.ext (by ring) rfl)
      _ = W (-(1 / 2 + t), modularArcHeight (1 / 2)) := hperiod _ _
      _ = W (1 / 2 + t, modularArcHeight (1 / 2)) := heven _ _
  have ht : HasDerivAt (fun u => W (u, modularArcHeight u))
      (L (1, -(2 * (1 / 2)) / (2 * modularArcHeight (1 / 2)))) (1 / 2) :=
    hW.comp_hasDerivAt (1 / 2)
      ((hasDerivAt_id (1 / 2 : ℝ)).prodMk (hasDerivAt_modularArcHeight (by norm_num)))
  have hr : HasDerivAt (fun t : ℝ =>
      W ((1 + t) * (1 / 2), (1 + t) * modularArcHeight (1 / 2)))
      (L (1 / 2, modularArcHeight (1 / 2))) 0 := by
    have hc : HasDerivAt (fun t : ℝ =>
        ((1 + t) * (1 / 2), (1 + t) * modularArcHeight (1 / 2)))
        (1 / 2, modularArcHeight (1 / 2)) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const (1 / 2)).prodMk
        (((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const (modularArcHeight (1 / 2)))
    have hw : HasFDerivAt W L
        ((1 + (0 : ℝ)) * (1 / 2), (1 + 0) * modularArcHeight (1 / 2)) := by
      simpa only [add_zero, one_mul] using hW
    exact hw.comp_hasDerivAt 0 hc
  rw [hr.deriv, ht.deriv,
    linear_apply_pair L (1 / 2) (modularArcHeight (1 / 2)),
    linear_apply_pair L 1 (-(2 * (1 / 2)) / (2 * modularArcHeight (1 / 2))), hx]
  have hy := modularArcHeight_half_pos.ne'
  have hs := modularArcHeight_half_sq
  field_simp
  ring_nf
  rw [hs]
  ring

theorem cosineMode_even (k u y : ℝ) : cosineMode k (-u) y = cosineMode k u y := by
  simp only [cosineMode, mul_neg, Real.cos_neg]

theorem cosineMode_periodic (n : ℕ) (u y : ℝ) :
    cosineMode (arcFreq n) (u + 1) y = cosineMode (arcFreq n) u y := by
  have he : arcFreq n * (u + 1) = arcFreq n * u + ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
    unfold arcFreq
    push_cast
    ring
  rw [cosineMode, cosineMode, he, Real.cos_add_nat_mul_two_pi]

/-- Smoothness is proved from the Bessel integral derivatives, without a regularity premise. -/
theorem contDiffOn_cosineMode {k : ℝ} (hk : 0 < k) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => cosineMode k p.1 p.2) {p | 0 < p.2} := by
  unfold cosineMode
  apply ContDiffOn.mul
  · exact (contDiffOn_kMoment 0).comp (by fun_prop)
      (fun p hp => mul_pos hk hp)
  · fun_prop

theorem hasDerivAt_cosineMode_x (k u y : ℝ) :
    HasDerivAt (fun v => cosineMode k v y)
      (-(k * kMoment 0 (k * y) * Real.sin (k * u))) u := by
  have h := (((hasDerivAt_id u).const_mul k).cos).const_mul (kMoment 0 (k * y))
  exact h.congr_deriv (by simp only [id]; ring)

theorem hasDerivAt_cosineMode_y {k y : ℝ} (hk : 0 < k) (hy : 0 < y) (u : ℝ) :
    HasDerivAt (fun v => cosineMode k u v)
      (-(k * kMoment 1 (k * y) * Real.cos (k * u))) y := by
  exact ((hasDerivAt_kMoment_comp_mul 0 hk hy).mul_const _).congr_deriv
    (by simp only [zero_add]; ring)

/-- The existing Whittaker slope is the derivative of the actual smooth boundary trace. -/
theorem hasDerivAt_cosineArcTrace {k u : ℝ} (hk : 0 < k) (hu : |u| < 1) :
    HasDerivAt (fun v => cosineMode k v (modularArcHeight v)) (arcWhittakerSlope k u) u := by
  have hy := modularArcHeight_pos_of_abs_lt hu
  have hK := (hasDerivAt_kMoment_comp_mul 0 hk hy).comp u (hasDerivAt_modularArcHeight hu)
  have hc := ((hasDerivAt_id u).const_mul k).cos
  exact (hK.mul hc).congr_deriv (by
    simp only [arcWhittakerSlope, Function.comp_apply, zero_add, id]
    field_simp
    ring)

/-- The arc trace is smooth on an open interval containing both corner endpoints. -/
theorem contDiffOn_cosineArcTrace {k : ℝ} (hk : 0 < k) :
    ContDiffOn ℝ ∞ (fun u => cosineMode k u (modularArcHeight u)) (Ioo (-1) 1) := by
  have hY : ContDiffOn ℝ ∞ modularArcHeight (Ioo (-1) 1) := by
    intro u hu
    have hp : 0 < 1 - u ^ 2 := by nlinarith only [hu.1, hu.2]
    unfold modularArcHeight
    exact (contDiffWithinAt_const.sub (contDiffWithinAt_id.pow 2)).sqrt hp.ne'
  exact (contDiffOn_cosineMode hk).comp (contDiffOn_id.prodMk hY)
    (fun u hu => modularArcHeight_pos_of_abs_lt (abs_lt.mpr hu))

/-- The derivative is taken on the actual ray, rather than a formal flux symbol. -/
theorem hasDerivAt_cosineMode_ray {k y : ℝ} (hk : 0 < k) (hy : 0 < y) (u : ℝ) :
    HasDerivAt (fun t => cosineMode k ((1 + t) * u) ((1 + t) * y))
      (cosineRadialFlux k u y) 0 := by
  have hr : HasDerivAt (fun t : ℝ => k * ((1 + t) * y)) (k * y) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const y).const_mul k
  have hK := (hasDerivAt_kMoment 0
    (show 0 < k * ((1 + 0) * y) by simpa using mul_pos hk hy)).comp 0
    (show HasDerivAt (fun t : ℝ => k * ((1 + t) * y)) (k * y) 0 from hr)
  have hc : HasDerivAt (fun t : ℝ => Real.cos (k * ((1 + t) * u)))
      (-Real.sin (k * u) * (k * u)) 0 := by
    simpa using ((((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const u).const_mul k).cos
  exact (hK.mul hc).congr_deriv (by
    simp only [cosineRadialFlux, Function.comp_apply, add_zero, one_mul, zero_add]
    ring)

/-- The Bessel differential equation gives the actual second-derivative equation. -/
theorem cosineMode_axisymmetric_equation {k y : ℝ} (hk : 0 < k) (hy : 0 < y) (u : ℝ) :
    y * (deriv (fun v => deriv (fun w => cosineMode k w y) v) u +
      deriv (fun v => deriv (fun w => cosineMode k u w) v) y) +
        deriv (fun v => cosineMode k u v) y = 0 := by
  have hx : (fun v => deriv (fun w => cosineMode k w y) v) =
      fun v => -(k * kMoment 0 (k * y) * Real.sin (k * v)) :=
    funext (fun v => (hasDerivAt_cosineMode_x k v y).deriv)
  have hxx : HasDerivAt (fun v => -(k * kMoment 0 (k * y) * Real.sin (k * v)))
      (-(k ^ 2 * kMoment 0 (k * y) * Real.cos (k * u))) u := by
    exact ((((hasDerivAt_id u).const_mul k).sin).const_mul _).neg.congr_deriv
      (by simp only [id]; ring)
  have hye : (fun v => deriv (fun w => cosineMode k u w) v) =ᶠ[𝓝 y]
      (fun v => -(k * kMoment 1 (k * v) * Real.cos (k * u))) := by
    filter_upwards [Ioi_mem_nhds hy] with v hv
    exact (hasDerivAt_cosineMode_y hk hv u).deriv
  have hyy : HasDerivAt (fun v => deriv (fun w => cosineMode k u w) v)
      (k ^ 2 * kMoment 2 (k * y) * Real.cos (k * u)) y := by
    apply HasDerivAt.congr_of_eventuallyEq _ hye
    exact (((hasDerivAt_kMoment_comp_mul 1 hk hy).const_mul k).mul_const _).neg.congr_deriv
      (by norm_num only [Nat.reduceAdd]; ring)
  rw [hx, hxx.deriv, hyy.deriv, (hasDerivAt_cosineMode_y hk hy u).deriv]
  linear_combination (k * Real.cos (k * u)) * kMoment_ode (mul_pos hk hy)

/-- A positive lower height gives an explicit bound throughout the unbounded strip. -/
theorem abs_cosineMode_le {k y y₀ : ℝ} (hk : 0 < k) (hy₀ : 0 < y₀)
    (hy : y₀ ≤ y) (u : ℝ) : |cosineMode k u y| ≤ kMoment 0 (k * y₀) := by
  have hky : k * y₀ ≤ k * y := mul_le_mul_of_nonneg_left hy hk.le
  have hK := kMoment_le_exp_mul 0 (mul_pos hk hy₀) hky
  have he : Real.exp (-(k * y - k * y₀)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith only [hky])
  calc
    |cosineMode k u y| ≤ kMoment 0 (k * y) := by
      rw [cosineMode, abs_mul, abs_of_nonneg (kMoment_nonneg 0 _)]
      exact mul_le_of_le_one_right (kMoment_nonneg 0 _) (Real.abs_cos_le_one _)
    _ ≤ Real.exp (-(k * y - k * y₀)) * kMoment 0 (k * y₀) := hK
    _ ≤ kMoment 0 (k * y₀) := mul_le_of_le_one_left (kMoment_nonneg 0 _) he

/-- Every point of the closed modular strip stays above its corner height. -/
theorem modularCornerHeight_le {u y : ℝ} (hu : |u| ≤ 1 / 2) (hy : 0 ≤ y)
    (hr : 1 ≤ u ^ 2 + y ^ 2) : modularArcHeight (1 / 2) ≤ y := by
  have hu' := abs_le.mp hu
  have hsq := modularArcHeight_half_sq
  have hpos := modularArcHeight_half_pos
  nlinarith only [hu'.1, hu'.2, hy, hr, hsq, hpos]

/-- Each actual integral-frequency mode is bounded on the entire closed modular strip. -/
theorem cosineMode_modular_strip_bound (n : ℕ) {u y : ℝ} (hu : |u| ≤ 1 / 2)
    (hy : 0 ≤ y) (hr : 1 ≤ u ^ 2 + y ^ 2) :
    |cosineMode (arcFreq n) u y| ≤ kMoment 0 (arcFreq n * modularArcHeight (1 / 2)) :=
  abs_cosineMode_le (arcFreq_pos n) modularArcHeight_half_pos
    (modularCornerHeight_le hu hy hr) u

/-- The actual modular corner value of every integral-frequency cosine flux. -/
theorem cosineArcFlux_corner (n : ℕ) :
    cosineArcFlux (arcFreq n) (1 / 2) =
      -(arcFreq n * modularArcHeight (1 / 2) *
        kMoment 1 (arcFreq n * modularArcHeight (1 / 2)) * (-1 : ℝ) ^ (n + 1)) := by
  have he : arcFreq n * (1 / 2) = ((n + 1 : ℕ) : ℝ) * Real.pi := by
    unfold arcFreq
    push_cast
    ring
  simp only [cosineArcFlux, cosineRadialFlux, he, Real.sin_nat_mul_pi,
    Real.cos_nat_mul_pi, mul_zero, neg_zero, zero_sub]

/-- At the corner the radial flux is exactly minus three halves of the trace slope. -/
theorem cosineArcFlux_corner_eq_slope (n : ℕ) :
    cosineArcFlux (arcFreq n) (1 / 2) = -(3 / 2 : ℝ) * arcWhittakerSlope (arcFreq n) (1 / 2) := by
  have he : Real.sin (arcFreq n * (1 / 2)) = 0 := by
    have hh : arcFreq n * (1 / 2) = ((n + 1 : ℕ) : ℝ) * Real.pi := by
      unfold arcFreq
      push_cast
      ring
    rw [hh, Real.sin_nat_mul_pi]
  have hy := modularArcHeight_half_pos.ne'
  have hs := modularArcHeight_half_sq
  unfold cosineArcFlux cosineRadialFlux arcWhittakerSlope
  rw [he]
  field_simp
  ring_nf
  rw [hs]
  ring

/-- Finite mode sums retain the exact endpoint boundary-jet law. -/
theorem sum_cosineArcFlux_corner_eq_slope (N : ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, a n * cosineArcFlux (arcFreq n) (1 / 2)) =
      -(3 / 2 : ℝ) * ∑ n ∈ Finset.range N, a n * arcWhittakerSlope (arcFreq n) (1 / 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [cosineArcFlux_corner_eq_slope]
  ring

/-- The finite-sum boundary jet is the literal derivative, with no smoothness assumption. -/
theorem hasDerivAt_cosineArcSum_corner (N : ℕ) (a : ℕ → ℝ) :
    HasDerivAt (fun u => ∑ n ∈ Finset.range N, a n * cosineMode (arcFreq n) u (modularArcHeight u))
      (∑ n ∈ Finset.range N, a n * arcWhittakerSlope (arcFreq n) (1 / 2)) (1 / 2) := by
  apply HasDerivAt.fun_sum
  intro n _
  exact (hasDerivAt_cosineArcTrace (arcFreq_pos n) (by norm_num)).const_mul (a n)

/-- Corner flux vanishes precisely when the trace has zero endpoint derivative. -/
theorem sum_cosineArcFlux_corner_eq_zero_iff (N : ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ Finset.range N, a n * cosineArcFlux (arcFreq n) (1 / 2)) = 0 ↔
      (∑ n ∈ Finset.range N, a n * arcWhittakerSlope (arcFreq n) (1 / 2)) = 0 := by
  rw [sum_cosineArcFlux_corner_eq_slope, mul_eq_zero]
  norm_num

/-- The smooth mode of frequency four pi has strictly negative corner radial flux. -/
theorem cosineArcFlux_second_corner_neg : cosineArcFlux (arcFreq 1) (1 / 2) < 0 := by
  have he : cosineArcFlux (arcFreq 1) (1 / 2) =
      -(arcFreq 1 * modularArcHeight (1 / 2) *
        kMoment 1 (arcFreq 1 * modularArcHeight (1 / 2))) := by
    rw [cosineArcFlux_corner]
    norm_num
  rw [he]
  exact neg_lt_zero.mpr (mul_pos (mul_pos (arcFreq_pos 1) modularArcHeight_half_pos)
    (kMoment_pos_of_pos 1 (mul_pos (arcFreq_pos 1) modularArcHeight_half_pos)))

/-- The nonzero endpoint value is the limit of the actual open-arc flux. -/
theorem continuousAt_cosineArcFlux_corner {k : ℝ} (hk : 0 < k) :
    ContinuousAt (cosineArcFlux k) (1 / 2) := by
  have hy : ContinuousAt modularArcHeight (1 / 2) := by
    unfold modularArcHeight
    fun_prop
  have hK (j : ℕ) : ContinuousAt (fun u => kMoment j (k * modularArcHeight u)) (1 / 2) :=
    ContinuousAt.comp (g := kMoment j) (f := fun u => k * modularArcHeight u)
      (differentiableAt_kMoment j (mul_pos hk modularArcHeight_half_pos)).continuousAt
      (hy.const_mul k)
  unfold cosineArcFlux cosineRadialFlux
  fun_prop

/-- The decaying smooth mode's corner flux is not bounded by the square root of corner distance. -/
theorem not_isBigO_cosineArcFlux_corner_sqrt_distance :
    ¬ Asymptotics.IsBigO (𝓝[<] (1 / 2 : ℝ)) (cosineArcFlux (arcFreq 1))
      (fun u : ℝ => Real.sqrt (arcCornerDistance u)) := by
  intro h
  have hr : Tendsto (fun u : ℝ => Real.sqrt (arcCornerDistance u))
      (𝓝[<] (1 / 2 : ℝ)) (𝓝 0) := by
    have hc := continuous_arcCornerDistance.sqrt
    simpa only [arcCornerDistance_corner, Real.sqrt_zero] using
      (hc.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hf := (continuousAt_cosineArcFlux_corner (arcFreq_pos 1)).tendsto.mono_left
    (show 𝓝[<] (1 / 2 : ℝ) ≤ 𝓝 (1 / 2 : ℝ) from nhdsWithin_le_nhds)
  have hz : cosineArcFlux (arcFreq 1) (1 / 2) = 0 := tendsto_nhds_unique hf (h.trans_tendsto hr)
  exact cosineArcFlux_second_corner_neg.ne hz

/-- The obstruction concerns the literal normal derivative of the smooth bounded solution. -/
theorem not_isBigO_cosineMode_corner_radial_deriv :
    ¬ Asymptotics.IsBigO (𝓝[<] (1 / 2 : ℝ))
      (fun u => deriv (fun t => cosineMode (arcFreq 1)
        ((1 + t) * u) ((1 + t) * modularArcHeight u)) 0)
      (fun u : ℝ => Real.sqrt (arcCornerDistance u)) := by
  intro h
  have he : (fun u => deriv (fun t => cosineMode (arcFreq 1)
      ((1 + t) * u) ((1 + t) * modularArcHeight u)) 0) =ᶠ[𝓝[<] (1 / 2 : ℝ)]
        cosineArcFlux (arcFreq 1) := by
    have hu : ∀ᶠ u in 𝓝 (1 / 2 : ℝ), |u| < 1 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
    filter_upwards [hu.filter_mono nhdsWithin_le_nhds] with u hu
    exact (hasDerivAt_cosineMode_ray (arcFreq_pos 1) (modularArcHeight_pos_of_abs_lt hu) u).deriv
  exact not_isBigO_cosineArcFlux_corner_sqrt_distance
    (h.congr' he (Filter.Eventually.of_forall (fun _ => rfl)))

end RHTower.ModularCorner
