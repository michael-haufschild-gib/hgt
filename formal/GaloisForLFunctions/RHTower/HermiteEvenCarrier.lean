import GaloisForLFunctions.RHTower.GaussianEvenCarrier
import GaloisForLFunctions.HTGeometry.HermiteOrthogonality
import GaloisForLFunctions.HTGeometry.TrialSpanConcentration
import GaloisForLFunctions.HTGeometry.PositiveFormTrialSpan
import GaloisForLFunctions.HTGeometry.ExpSquareRayTail

/-!
# The Hermite family inside the even prolate carrier

The one-dimensional Gaussian trial space caps only the ground leakage.  To cap the `n`-th one a
trial space of dimension `n + 1` is needed, and the Hermite functions supply it: they are an
orthonormal family, and every fourth one is fixed by the Fourier transform, since its eigenvalue
is `(−i)^{4j} = 1`.  Fixed vectors are what the truncation estimate consumes, so the admissible
subfamily is exactly the step-four one — the same step-four ladder the constrained transfer runs
on.

Three ingredients combine:

* the `L²` classes of the Hermite functions of even index lie in the even carrier, because those
  functions are even;
* the step-four subfamily is fixed by the even Fourier transform;
* each member is moved by the compressed block `Tₐ = Pₐ F Pₐ` by at most twice its aperture
  truncation error, and that error vanishes as the aperture grows, because an `L²` function has
  vanishing mass outside a large interval.

Aggregating over `n + 1` members costs a factor `√(n+1)`, which is harmless for a fixed index.
The conclusion is that **every** fixed leakage of the true compressed Fourier block tends to zero
as the aperture grows — not only the ground one.
-/

open MeasureTheory Filter
open scoped Real

noncomputable section

namespace RHTower

/-! ## The Hermite classes in the even carrier -/

/-- The `L²` class of the `n`-th Hermite function. -/
def hermiteL2 (n : ℕ) : SoninL2 := (GaloisForLFunctions.hermiteSchwartz n).toLp 2

theorem hermiteL2_coeFn (n : ℕ) :
    (hermiteL2 n : ℝ → ℂ) =ᵐ[volume] fun x => GaloisForLFunctions.hermiteSchwartz n x :=
  SchwartzMap.coeFn_toLp (GaloisForLFunctions.hermiteSchwartz n) 2 (μ := volume)

/-- **Hermite functions of even index lie in the even carrier.** -/
theorem hermiteL2_mem_evenSubspace (k : ℕ) : hermiteL2 (2 * k) ∈ evenSubspace := by
  rw [mem_evenSubspace_iff]
  apply Lp.ext
  have hneg := (hermiteL2_coeFn (2 * k)).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (hermiteL2 (2 * k)), hneg, hermiteL2_coeFn (2 * k)] with
    x href hleft hright
  have hleft' : (hermiteL2 (2 * k) : ℝ → ℂ) (-x)
      = GaloisForLFunctions.hermiteSchwartz (2 * k) (-x) := by
    simpa [Function.comp_apply] using hleft
  rw [href, hleft', hright, GaloisForLFunctions.hermiteSchwartz_even]

/-- The `j`-th member of the step-four Hermite subfamily, as an element of the even carrier. -/
def hermiteEven (j : ℕ) : evenSubspace :=
  ⟨hermiteL2 (4 * j), by
    have h : 4 * j = 2 * (2 * j) := by ring
    rw [h]
    exact hermiteL2_mem_evenSubspace (2 * j)⟩

@[simp] theorem coe_hermiteEven (j : ℕ) : (hermiteEven j : SoninL2) = hermiteL2 (4 * j) := rfl

/-- **The even Fourier transform fixes the step-four Hermite functions**, their eigenvalue being
`(−i)^{4j} = 1`. -/
theorem evenFourierTransform_hermiteEven (j : ℕ) :
    evenFourierTransform (hermiteEven j) = hermiteEven j := by
  apply Subtype.ext
  rw [coe_evenFourierTransform_apply, coe_hermiteEven]
  have h := GaloisForLFunctions.fourier_hermiteSchwartz_toLp (4 * j)
  have hpow : ((-Complex.I) ^ (4 * j) : ℂ) = 1 := by
    rw [pow_mul]
    have h4 : ((-Complex.I) ^ 4 : ℂ) = 1 := by
      have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc ((-Complex.I) ^ 4 : ℂ) = (Complex.I * Complex.I) * (Complex.I * Complex.I) := by ring
        _ = 1 := by rw [hII]; ring
    rw [h4, one_pow]
  rw [hpow, one_smul] at h
  exact h

theorem hermiteEven_ne_zero (j : ℕ) : hermiteEven j ≠ 0 := by
  intro hzero
  have hcoe : hermiteL2 (4 * j) = 0 := congrArg Subtype.val hzero
  exact GaloisForLFunctions.hermiteSchwartz_toLp_ne_zero (4 * j) hcoe

/-! ## The orthonormal step-four family -/

/-- The normalized step-four Hermite family. -/
def hermiteEvenUnit (j : ℕ) : evenSubspace := ((‖hermiteEven j‖ : ℂ))⁻¹ • hermiteEven j

theorem norm_hermiteEvenUnit (j : ℕ) : ‖hermiteEvenUnit j‖ = 1 :=
  norm_smul_inv_norm (hermiteEven_ne_zero j)

/-- The normalized step-four Hermite vectors are still Fourier-fixed. -/
theorem evenFourierTransform_hermiteEvenUnit (j : ℕ) :
    evenFourierTransform (hermiteEvenUnit j) = hermiteEvenUnit j := by
  rw [hermiteEvenUnit, map_smul, evenFourierTransform_hermiteEven]

theorem inner_hermiteEven_eq_zero {i j : ℕ} (hij : i ≠ j) :
    inner ℂ (hermiteEven i) (hermiteEven j) = 0 := by
  have hne : 4 * i ≠ 4 * j := by omega
  have h := GaloisForLFunctions.inner_hermiteSchwartz_toLp_eq_zero hne
  exact h

/-- **The normalized step-four Hermite family is orthonormal in the even carrier.** -/
theorem orthonormal_hermiteEvenUnit (m : ℕ) :
    Orthonormal ℂ (fun j : Fin m => hermiteEvenUnit (j : ℕ)) := by
  constructor
  · intro j
    exact norm_hermiteEvenUnit _
  · intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have hcoe : ∀ k : ℕ, ((hermiteEvenUnit k : evenSubspace) : SoninL2)
        = ((‖hermiteEven k‖ : ℂ))⁻¹ • ((hermiteEven k : evenSubspace) : SoninL2) :=
      fun _ => rfl
    have hinner : inner ℂ (hermiteEvenUnit (i : ℕ)) (hermiteEvenUnit (j : ℕ))
        = inner ℂ ((hermiteEvenUnit (i : ℕ) : evenSubspace) : SoninL2)
            ((hermiteEvenUnit (j : ℕ) : evenSubspace) : SoninL2) := rfl
    have hzero : inner ℂ ((hermiteEven (i : ℕ) : evenSubspace) : SoninL2)
        ((hermiteEven (j : ℕ) : evenSubspace) : SoninL2) = 0 :=
      inner_hermiteEven_eq_zero hne
    rw [hinner, hcoe, hcoe, inner_smul_left, inner_smul_right, hzero, mul_zero, mul_zero]

/-! ## The aperture truncation error -/

/-- The truncation error of any even carrier vector is its `L²` mass outside the aperture. -/
theorem norm_sq_sub_cut_eq (a : ℝ) (f : evenSubspace) :
    ‖f - evenIndicatorCutoff a f‖ ^ 2
      = ∫ x in (centralInterval a)ᶜ, ‖((f : SoninL2) : ℝ → ℂ) x‖ ^ 2 := by
  have hnorm : ‖f - evenIndicatorCutoff a f‖
      = ‖(f : SoninL2) - indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) (f : SoninL2)‖ := rfl
  rw [hnorm, norm_sq_eq_integral]
  have hae : (((f : SoninL2) - indicatorCutoff (centralInterval a)
      (measurableSet_centralInterval a) (f : SoninL2) : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] fun x => (centralInterval a)ᶜ.indicator ((f : SoninL2) : ℝ → ℂ) x := by
    filter_upwards [Lp.coeFn_sub (f : SoninL2) (indicatorCutoff (centralInterval a)
        (measurableSet_centralInterval a) (f : SoninL2)),
      indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) (f : SoninL2)]
      with x hsub hcut
    rw [hsub, Pi.sub_apply, hcut]
    by_cases hx : x ∈ centralInterval a
    · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx), sub_self]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx), sub_zero]
  rw [integral_congr_ae (hae.mono fun x hx => by rw [hx])]
  rw [← integral_indicator (measurableSet_centralInterval a).compl]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ (centralInterval a)ᶜ
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- The squared pointwise norm of an `L²` class is integrable. -/
theorem integrable_norm_sq (f : SoninL2) : Integrable (fun x : ℝ => ‖(f : ℝ → ℂ) x‖ ^ 2) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f
  have hre := h.re
  refine hre.congr ?_
  filter_upwards with x
  exact inner_self_eq_norm_sq _

/-- **The truncation error of any even carrier vector vanishes as the aperture grows.**  This is
the statement that an `L²` function has vanishing mass outside a large interval. -/
theorem tendsto_norm_sq_sub_cut (f : evenSubspace) :
    Tendsto (fun a : ℝ => ‖f - evenIndicatorCutoff a f‖ ^ 2) atTop (nhds 0) := by
  set g : ℝ → ℝ := fun x => ‖((f : SoninL2) : ℝ → ℂ) x‖ ^ 2 with hg
  have hgint : Integrable g volume := integrable_norm_sq (f : SoninL2)
  have hgnn : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
  have hlim : Tendsto (fun a : ℝ => ∫ x, (centralInterval a)ᶜ.indicator g x) atTop
      (nhds (∫ _x : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hgint ?_
    · filter_upwards with a
      exact (hgint.aestronglyMeasurable).indicator (measurableSet_centralInterval a).compl
    · filter_upwards with a
      filter_upwards with x
      rcases Classical.em (x ∈ (centralInterval a)ᶜ) with hx | hx
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (hgnn x)]
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact hgnn x
    · filter_upwards with x
      have hev : (fun a : ℝ => (centralInterval a)ᶜ.indicator g x)
          =ᶠ[atTop] fun _ : ℝ => (0 : ℝ) := by
        filter_upwards [eventually_ge_atTop |x|] with a ha
        have hmem : x ∈ centralInterval a := by
          rw [centralInterval, Set.mem_Icc]
          constructor
          · linarith [neg_abs_le x]
          · linarith [le_abs_self x]
        exact Set.indicator_of_notMem (by simpa using hmem) _
      exact Tendsto.congr' hev.symm tendsto_const_nhds
  rw [integral_zero] at hlim
  refine Tendsto.congr ?_ hlim
  intro a
  rw [norm_sq_sub_cut_eq a f, integral_indicator (measurableSet_centralInterval a).compl]

theorem tendsto_norm_sub_cut (f : evenSubspace) :
    Tendsto (fun a : ℝ => ‖f - evenIndicatorCutoff a f‖) atTop (nhds 0) := by
  have hsq := tendsto_norm_sq_sub_cut f
  have hcont : Tendsto (fun t : ℝ => Real.sqrt t) (nhds 0) (nhds 0) := by
    have h := (Real.continuous_sqrt).continuousAt (x := (0 : ℝ))
    rw [ContinuousAt, Real.sqrt_zero] at h
    exact h
  have h := hcont.comp hsq
  refine Tendsto.congr ?_ h
  intro a
  rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]

/-! ## The trial-space bound for every fixed index -/

/-- The compressed block is the aperture cut composed with the transform and the cut again. -/
theorem evenTimeBandFourier_apply_eq (a : ℝ) (f : evenSubspace) :
    evenTimeBandFourier a f
      = evenIndicatorCutoff a (evenFourierTransform (evenIndicatorCutoff a f)) := by
  rw [evenTimeBandFourier_eq_mul]
  rfl

/-- Each step-four Hermite vector is moved by the compressed block by at most twice its
truncation error. -/
theorem norm_hermiteEvenUnit_sub_timeBand_le (a : ℝ) (j : ℕ) :
    ‖hermiteEvenUnit j - evenTimeBandFourier a (hermiteEvenUnit j)‖
      ≤ 2 * ‖hermiteEvenUnit j - evenIndicatorCutoff a (hermiteEvenUnit j)‖ := by
  have hfix : evenFourierTransform (hermiteEvenUnit j) = hermiteEvenUnit j :=
    evenFourierTransform_hermiteEvenUnit j
  rw [evenTimeBandFourier_apply_eq]
  exact ContinuousLinearMap.norm_sub_proj_unitary_proj_le
    (fun x => evenFourierTransform_isometry x)
    (ContinuousLinearMap.norm_sq_eq_of_isIdempotent_symmetric
      (evenIndicatorCutoff_apply_apply a) (evenIndicatorCutoff_symmetric a))
    hfix

/-- **The leakage bound from the step-four Hermite trial space.**  An `(n+1)`-member family with
truncation error at most `η` caps the `n`-th leakage of the true compressed Fourier block. -/
theorem evenProlateLeakageValue_le_of_hermite_trial (a : ℝ) (n : ℕ) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ j : Fin (n + 1),
      ‖hermiteEvenUnit (j : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (j : ℕ))‖ ≤ η)
    (hsm : Real.sqrt (n + 1) * (2 * η) ≤ 1) :
    evenProlateLeakageValue a n ≤ 1 - (1 - Real.sqrt (n + 1) * (2 * η)) ^ 2 := by
  set g : Fin (n + 1) → evenSubspace := fun j => hermiteEvenUnit (j : ℕ) with hgdef
  have hg : Orthonormal ℂ g := orthonormal_hermiteEvenUnit (n + 1)
  have hdim : n < Module.finrank ℂ (Submodule.span ℂ (Set.range g)) := by
    rw [ContinuousLinearMap.finrank_span_orthonormal hg]
    omega
  refine evenProlateLeakageValue_le_of_form_trial a n (Submodule.span ℂ (Set.range g)) hdim ?_
  intro f hf
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  have hstep : ∀ k : Fin (n + 1), ‖g k - evenTimeBandFourier a (g k)‖ ≤ 2 * η := by
    intro k
    exact le_trans (norm_hermiteEvenUnit_sub_timeBand_le a (k : ℕ))
      (by linarith [hη k])
  have hmain := ContinuousLinearMap.norm_sq_apply_ge_of_orthonormal_span hg
    (evenTimeBandFourier a) (by linarith : (0 : ℝ) ≤ 2 * η) hstep
    (by rw [← hcast]; exact hsm) hf
  have hrw : Real.sqrt ((n + 1 : ℕ) : ℝ) = Real.sqrt ((n : ℝ) + 1) := by rw [hcast]
  rw [hrw] at hmain
  have hfinal : (1 : ℝ) - (1 - (1 - Real.sqrt ((n : ℝ) + 1) * (2 * η)) ^ 2)
      = (1 - Real.sqrt ((n : ℝ) + 1) * (2 * η)) ^ 2 := by ring
  rw [hfinal]
  exact hmain

/-! ## The sharp quadratic trial-space bound -/

theorem evenProlateLeakage_symmetric (a : ℝ) (x y : evenSubspace) :
    inner ℂ (evenProlateLeakage a x) y = inner ℂ x (evenProlateLeakage a y) :=
  (evenProlateLeakage_isPositive a).isSymmetric x y

theorem re_inner_evenProlateLeakage (a : ℝ) (f : evenSubspace) :
    RCLike.re (inner ℂ (evenProlateLeakage a f) f)
      = ‖f‖ ^ 2 - ‖evenTimeBandFourier a f‖ ^ 2 := by
  rw [evenProlateLeakage_inner_eq, RCLike.re_to_complex, Complex.ofReal_re]

theorem re_inner_evenProlateLeakage_nonneg (a : ℝ) (f : evenSubspace) :
    0 ≤ RCLike.re (inner ℂ (evenProlateLeakage a f) f) := by
  have h := (evenProlateLeakage_isPositive a).2 f
  rwa [ContinuousLinearMap.reApplyInnerSelf_apply] at h

/-- **The quadratic per-vector leakage bound.**  A Fourier-fixed vector loses at most five times
the SQUARE of its truncation error under the compressed block.  Unlike the norm form, this bound
survives aggregation to a span without degrading to a linear one. -/
theorem re_inner_evenProlateLeakage_le (a : ℝ) {g : evenSubspace}
    (hfix : evenFourierTransform g = g) :
    RCLike.re (inner ℂ (evenProlateLeakage a g) g)
      ≤ 5 * ‖g - evenIndicatorCutoff a g‖ ^ 2 := by
  have hpyth := ContinuousLinearMap.norm_sq_eq_of_isIdempotent_symmetric
    (evenIndicatorCutoff_apply_apply a) (evenIndicatorCutoff_symmetric a)
  have hpy := hpyth g
  have hmain := ContinuousLinearMap.norm_sq_proj_unitary_proj_ge
    (fun x => evenFourierTransform_isometry x) hpyth hfix
  rw [re_inner_evenProlateLeakage, evenTimeBandFourier_apply_eq]
  linarith

/-- The step-four Hermite trial space of dimension `n + 1`. -/
def hermiteTrialSpace (n : ℕ) : Submodule ℂ evenSubspace :=
  Submodule.span ℂ (Set.range (fun j : Fin (n + 1) => hermiteEvenUnit (j : ℕ)))

/-- The aggregate squared truncation error of the trial family. -/
noncomputable def hermiteTrialDefect (a : ℝ) (n : ℕ) : ℝ :=
  ∑ k : Fin (n + 1),
    5 * ‖hermiteEvenUnit (k : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))‖ ^ 2

theorem hermiteTrialDefect_nonneg (a : ℝ) (n : ℕ) : 0 ≤ hermiteTrialDefect a n :=
  Finset.sum_nonneg fun k _ => by positivity

theorem finrank_hermiteTrialSpace (n : ℕ) :
    Module.finrank ℂ (hermiteTrialSpace n) = n + 1 :=
  ContinuousLinearMap.finrank_span_orthonormal (orthonormal_hermiteEvenUnit (n + 1))

/-- **The trial space concentrates.**  On the span of the step-four Hermite family the compressed
block retains all but the aggregate squared truncation error. -/
theorem hermiteTrialSpace_concentration (a : ℝ) (n : ℕ) {f : evenSubspace}
    (hf : f ∈ hermiteTrialSpace n) :
    (1 - hermiteTrialDefect a n) * ‖f‖ ^ 2 ≤ ‖evenTimeBandFourier a f‖ ^ 2 := by
  set g : Fin (n + 1) → evenSubspace := fun j => hermiteEvenUnit (j : ℕ) with hgdef
  have hg : Orthonormal ℂ g := orthonormal_hermiteEvenUnit (n + 1)
  have htrace := ContinuousLinearMap.re_inner_apply_self_le_of_orthonormal_span hg
    (evenProlateLeakage a) (evenProlateLeakage_symmetric a)
    (re_inner_evenProlateLeakage_nonneg a) hf
  have hdiag : ∀ k : Fin (n + 1),
      RCLike.re (inner ℂ (evenProlateLeakage a (g k)) (g k))
        ≤ 5 * ‖g k - evenIndicatorCutoff a (g k)‖ ^ 2 := fun k =>
    re_inner_evenProlateLeakage_le a (evenFourierTransform_hermiteEvenUnit (k : ℕ))
  have hsum : ∑ k : Fin (n + 1), RCLike.re (inner ℂ (evenProlateLeakage a (g k)) (g k))
      ≤ hermiteTrialDefect a n :=
    Finset.sum_le_sum fun k _ => hdiag k
  have hform : RCLike.re (inner ℂ (evenProlateLeakage a f) f)
      = ‖f‖ ^ 2 - ‖evenTimeBandFourier a f‖ ^ 2 := re_inner_evenProlateLeakage a f
  rw [hform] at htrace
  nlinarith [htrace, hsum, sq_nonneg ‖f‖, norm_nonneg f]

/-- **The leakage of the true compressed Fourier block is bounded by the squared Hermite tails.**
For each fixed index this is the sharp shape: quadratic in the truncation error, with only a
linear-in-index number of terms. -/
theorem evenProlateLeakageValue_le_hermite_tail_sq (a : ℝ) (n : ℕ) :
    evenProlateLeakageValue a n ≤ hermiteTrialDefect a n := by
  refine evenProlateLeakageValue_le_of_form_trial a n (hermiteTrialSpace n) ?_ ?_
  · rw [finrank_hermiteTrialSpace]
    omega
  · exact fun f hf => hermiteTrialSpace_concentration a n hf

/-! ## Every fixed leakage vanishes -/

/-- **Every fixed leakage of the true compressed Fourier block vanishes as the aperture grows.**
For `n = 0` this recovers the Gaussian statement; for general `n` the step-four Hermite family
supplies the `(n+1)`-dimensional trial space. -/
theorem evenProlateLeakageValue_tendsto_zero (n : ℕ) :
    Tendsto (fun a : ℝ => evenProlateLeakageValue a n) atTop (nhds 0) := by
  set η : ℝ → ℝ := fun a => ∑ j : Fin (n + 1),
    ‖hermiteEvenUnit (j : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (j : ℕ))‖ with hηdef
  have hη0 : ∀ a, 0 ≤ η a := fun a =>
    Finset.sum_nonneg fun j _ => norm_nonneg _
  have hηle : ∀ a (j : Fin (n + 1)),
      ‖hermiteEvenUnit (j : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (j : ℕ))‖ ≤ η a := by
    intro a j
    exact Finset.single_le_sum (f := fun k : Fin (n + 1) =>
      ‖hermiteEvenUnit (k : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))‖)
      (fun k _ => norm_nonneg _) (Finset.mem_univ j)
  have hηlim : Tendsto η atTop (nhds 0) := by
    have h : Tendsto (fun a : ℝ => ∑ j : Fin (n + 1),
        ‖hermiteEvenUnit (j : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (j : ℕ))‖) atTop
        (nhds (∑ _j : Fin (n + 1), (0 : ℝ))) :=
      tendsto_finsetSum _ fun j _ => tendsto_norm_sub_cut (hermiteEvenUnit (j : ℕ))
    simpa using h
  have hbound : Tendsto (fun a : ℝ => 1 - (1 - Real.sqrt ((n : ℝ) + 1) * (2 * η a)) ^ 2) atTop
      (nhds 0) := by
    have h1 : Tendsto (fun a : ℝ => 1 - Real.sqrt ((n : ℝ) + 1) * (2 * η a)) atTop (nhds 1) := by
      have := (hηlim.const_mul (2 : ℝ)).const_mul (Real.sqrt ((n : ℝ) + 1))
      simpa using tendsto_const_nhds.sub this
    have h2 : Tendsto (fun a : ℝ => (1 - Real.sqrt ((n : ℝ) + 1) * (2 * η a)) ^ 2) atTop
        (nhds 1) := by simpa using h1.pow 2
    have h3 : Tendsto (fun a : ℝ => 1 - (1 - Real.sqrt ((n : ℝ) + 1) * (2 * η a)) ^ 2) atTop
        (nhds ((1 : ℝ) - 1)) := tendsto_const_nhds.sub h2
    simpa using h3
  have hsmall : ∀ᶠ a : ℝ in atTop, Real.sqrt ((n : ℝ) + 1) * (2 * η a) ≤ 1 := by
    have h1 : Tendsto (fun a : ℝ => Real.sqrt ((n : ℝ) + 1) * (2 * η a)) atTop (nhds 0) := by
      have := (hηlim.const_mul (2 : ℝ)).const_mul (Real.sqrt ((n : ℝ) + 1))
      simpa using this
    exact h1.eventually_le_const (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ ?_
  · filter_upwards with a
    exact evenProlateLeakageValue_nonneg a n
  · filter_upwards [hsmall] with a ha
    exact evenProlateLeakageValue_le_of_hermite_trial a n (hη0 a) (hηle a) ha

/-- **The concentration values of the true compressed Fourier block converge to one at every
fixed index.**  The dual form of the leakage statement: for each fixed mode the compressed block
becomes asymptotically norm-preserving as the aperture grows. -/
theorem evenProlateConcentrationValue_tendsto_one (n : ℕ) :
    Tendsto (fun a : ℝ => evenProlateConcentrationValue a n) atTop (nhds 1) := by
  have h := evenProlateLeakageValue_tendsto_zero n
  have hrw : ∀ a : ℝ, evenProlateConcentrationValue a n
      = 1 - evenProlateLeakageValue a n := by
    intro a
    rw [evenProlateLeakageValue]
    ring
  have hsub : Tendsto (fun a : ℝ => (1 : ℝ) - evenProlateLeakageValue a n) atTop
      (nhds ((1 : ℝ) - 0)) := tendsto_const_nhds.sub h
  rw [sub_zero] at hsub
  exact Tendsto.congr (fun a => (hrw a).symm) hsub

/-! ## The explicit exponential rate -/

/-- **A Hermite function's squared modulus is dominated by a multiple of `e^{−πx²}`.**  One of
its two Gaussian factors absorbs the polynomial; the other survives. -/
theorem exists_bound_norm_sq_hermiteSchwartz (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖GaloisForLFunctions.hermiteSchwartz n x‖ ^ 2 ≤ C * Real.exp (-(π * x ^ 2)) := by
  obtain ⟨C, hC⟩ := GaloisForLFunctions.exists_bound_poly_mul_gaussReal
    (GaloisForLFunctions.hermitePoly n * GaloisForLFunctions.hermitePoly n) 0
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hval : ‖GaloisForLFunctions.hermiteSchwartz n x‖ ^ 2
      = (GaloisForLFunctions.hermitePoly n).eval x ^ 2
        * GaloisForLFunctions.gaussReal x ^ 2 := by
    rw [GaloisForLFunctions.hermiteSchwartz_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hgnn : 0 ≤ GaloisForLFunctions.gaussReal x := (GaloisForLFunctions.gaussReal_pos x).le
  have hdiag : (GaloisForLFunctions.hermitePoly n).eval x ^ 2
      * GaloisForLFunctions.gaussReal x ≤ max C 0 := by
    have h := hC x
    simp only [pow_zero, one_mul, Polynomial.eval_mul] at h
    rw [abs_of_nonneg (mul_self_nonneg _)] at h
    have hsq : (GaloisForLFunctions.hermitePoly n).eval x ^ 2
        = (GaloisForLFunctions.hermitePoly n).eval x
          * (GaloisForLFunctions.hermitePoly n).eval x := sq _
    rw [hsq]
    exact le_trans h (le_max_left _ _)
  rw [hval]
  have hstep := mul_le_mul_of_nonneg_right hdiag hgnn
  calc (GaloisForLFunctions.hermitePoly n).eval x ^ 2 * GaloisForLFunctions.gaussReal x ^ 2
      = (GaloisForLFunctions.hermitePoly n).eval x ^ 2 * GaloisForLFunctions.gaussReal x
          * GaloisForLFunctions.gaussReal x := by ring
    _ ≤ max C 0 * GaloisForLFunctions.gaussReal x := hstep

/-- **The aperture tail of a step-four Hermite vector is explicitly exponentially small.** -/
theorem exists_norm_sq_hermiteEven_sub_cut_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a →
      ‖hermiteEven j - evenIndicatorCutoff a (hermiteEven j)‖ ^ 2
        ≤ C * (Real.exp (-(π * a ^ 2)) / (π * a)) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_sq_hermiteSchwartz (4 * j)
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hint : Integrable
      (fun x : ℝ => ‖GaloisForLFunctions.hermiteSchwartz (4 * j) x‖ ^ 2) volume := by
    refine Integrable.mono' ((GaloisForLFunctions.integrable_expNegSq hpi).const_mul C) ?_ ?_
    · exact ((GaloisForLFunctions.hermiteSchwartz (4 * j)).continuous.norm.pow 2).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hC x
  refine ⟨C, hC0, fun a ha => ?_⟩
  rw [norm_sq_sub_cut_eq a (hermiteEven j)]
  have hae : ∫ x in (centralInterval a)ᶜ, ‖((hermiteEven j : SoninL2) : ℝ → ℂ) x‖ ^ 2
      = ∫ x in (centralInterval a)ᶜ,
          ‖GaloisForLFunctions.hermiteSchwartz (4 * j) x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hermiteL2_coeFn (4 * j))] with x hx
    rw [coe_hermiteEven, hx]
  rw [hae]
  exact GaloisForLFunctions.setIntegral_compl_Icc_le_of_le_expNegSq hpi ha hC0
    hint.integrableOn hC

/-- The normalized truncation error is the unnormalized one divided by the squared norm. -/
theorem norm_sq_hermiteEvenUnit_sub_cut (j : ℕ) (a : ℝ) :
    ‖hermiteEvenUnit j - evenIndicatorCutoff a (hermiteEvenUnit j)‖ ^ 2
      = ‖hermiteEven j - evenIndicatorCutoff a (hermiteEven j)‖ ^ 2 / ‖hermiteEven j‖ ^ 2 := by
  have hne : ‖hermiteEven j‖ ≠ 0 := norm_ne_zero_iff.mpr (hermiteEven_ne_zero j)
  have hsplit : hermiteEvenUnit j - evenIndicatorCutoff a (hermiteEvenUnit j)
      = ((‖hermiteEven j‖ : ℂ))⁻¹ • (hermiteEven j - evenIndicatorCutoff a (hermiteEven j)) := by
    rw [hermiteEvenUnit, map_smul, smul_sub]
  rw [hsplit, norm_smul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  field_simp

/-- **Every fixed leakage of the true compressed Fourier block decays exponentially in the
squared aperture.**  This is the quantitative form of the vanishing statement: the variational
route through the step-four Hermite trial space yields the rate `e^{−πa²}/a` at every index. -/
theorem exists_hermiteTrialDefect_le_exp (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a →
      hermiteTrialDefect a n ≤ C * (Real.exp (-(π * a ^ 2)) / a) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  choose C hC0 hCle using fun k : Fin (n + 1) => exists_norm_sq_hermiteEven_sub_cut_le (k : ℕ)
  have hnormpos : ∀ k : Fin (n + 1), (0 : ℝ) < ‖hermiteEven (k : ℕ)‖ ^ 2 := by
    intro k
    have := norm_ne_zero_iff.mpr (hermiteEven_ne_zero (k : ℕ))
    positivity
  refine ⟨∑ k : Fin (n + 1), 5 * C k / (π * ‖hermiteEven (k : ℕ)‖ ^ 2), ?_, fun a ha => ?_⟩
  · refine Finset.sum_nonneg fun k _ => ?_
    have := hC0 k
    have := hnormpos k
    positivity
  · rw [hermiteTrialDefect]
    have hterm : ∀ k : Fin (n + 1),
        5 * ‖hermiteEvenUnit (k : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))‖ ^ 2
          ≤ (5 * C k / (π * ‖hermiteEven (k : ℕ)‖ ^ 2)) * (Real.exp (-(π * a ^ 2)) / a) := by
      intro k
      rw [norm_sq_hermiteEvenUnit_sub_cut]
      have hnk := hnormpos k
      have hbase := hCle k a ha
      have hpine : (π : ℝ) ≠ 0 := ne_of_gt hpi
      have hane : a ≠ 0 := ne_of_gt ha
      have hnne : ‖hermiteEven (k : ℕ)‖ ^ 2 ≠ 0 := ne_of_gt hnk
      have hrw : (5 * C k / (π * ‖hermiteEven (k : ℕ)‖ ^ 2)) * (Real.exp (-(π * a ^ 2)) / a)
          = 5 * ((C k * (Real.exp (-(π * a ^ 2)) / (π * a))) / ‖hermiteEven (k : ℕ)‖ ^ 2) := by
        field_simp
      rw [hrw]
      gcongr
    calc ∑ k : Fin (n + 1),
          5 * ‖hermiteEvenUnit (k : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))‖ ^ 2
        ≤ ∑ k : Fin (n + 1),
            (5 * C k / (π * ‖hermiteEven (k : ℕ)‖ ^ 2)) * (Real.exp (-(π * a ^ 2)) / a) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = (∑ k : Fin (n + 1), 5 * C k / (π * ‖hermiteEven (k : ℕ)‖ ^ 2))
            * (Real.exp (-(π * a ^ 2)) / a) := by rw [Finset.sum_mul]

/-- **Every fixed leakage of the true compressed Fourier block decays exponentially in the
squared aperture.** -/
theorem exists_evenProlateLeakageValue_le_exp (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a →
      evenProlateLeakageValue a n ≤ C * (Real.exp (-(π * a ^ 2)) / a) := by
  obtain ⟨C, hC0, hC⟩ := exists_hermiteTrialDefect_le_exp n
  exact ⟨C, hC0, fun a ha =>
    le_trans (evenProlateLeakageValue_le_hermite_tail_sq a n) (hC a ha)⟩

/-- The aggregate trial defect vanishes as the aperture grows. -/
theorem tendsto_hermiteTrialDefect (n : ℕ) :
    Tendsto (fun a : ℝ => hermiteTrialDefect a n) atTop (nhds 0) := by
  have h : Tendsto (fun a : ℝ => ∑ k : Fin (n + 1),
      5 * ‖hermiteEvenUnit (k : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))‖ ^ 2)
      atTop (nhds (∑ _k : Fin (n + 1), (0 : ℝ))) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    have hk := tendsto_norm_sub_cut (hermiteEvenUnit (k : ℕ))
    have := ((hk.pow 2).const_mul (5 : ℝ))
    simpa using this
  simpa [hermiteTrialDefect] using h

end RHTower

end
