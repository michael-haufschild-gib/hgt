import GaloisForLFunctions.RHTower.GaussianEvenCarrier
import GaloisForLFunctions.HTGeometry.HermiteOrthogonality
import GaloisForLFunctions.HTGeometry.TrialSpanConcentration

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
  have hfix : evenFourierTransform (hermiteEvenUnit j) = hermiteEvenUnit j := by
    rw [hermiteEvenUnit, map_smul, evenFourierTransform_hermiteEven]
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

end RHTower

end
