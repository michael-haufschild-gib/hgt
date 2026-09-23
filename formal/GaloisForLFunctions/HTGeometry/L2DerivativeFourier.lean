import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Fourier multiplier of the derivative on `L²(ℝ)`

Mathlib carries the Fourier transform on `L²` as a linear isometry equivalence and the
derivative/multiplier exchange on tempered distributions.  This file glues the two: for a
differentiable `f : ℝ → ℂ` whose value and derivative both lie in `L²`, the `L²`-Fourier transform
of the derivative is `2πiξ` times the `L²`-Fourier transform of `f`, almost everywhere.

Iterating along a chain `f 0, f 1, …` of successive derivatives gives the `m`-th order statement,
and Plancherel then converts an `L²` bound on the `m`-th derivative into a decay bound for the
Fourier transform of `f 0` on a frequency half-line — the analytic engine of a Paley–Wiener
support argument.
-/

open MeasureTheory SchwartzMap TemperedDistribution FourierTransform

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The `L²` norm as an integral -/

theorem norm_lpTwo_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℂ 2 μ) :
    ‖u‖ ^ (2 : ℕ) = ∫ x, ‖u x‖ ^ (2 : ℕ) ∂μ := by
  have h : (inner ℂ u u : ℂ) = ∫ a, (inner ℂ (u a) (u a) : ℂ) ∂μ := L2.inner_def u u
  have h3 : ∀ a : α, (inner ℂ (u a) (u a) : ℂ) = ((‖u a‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro a
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [h3] at h
  rw [integral_complex_ofReal] at h
  have h2 : ‖u‖ ^ (2 : ℕ) = (RCLike.re (inner ℂ u u : ℂ)) := (inner_self_eq_norm_sq _).symm
  rw [h2, h]
  simp


/-! ## Restriction of an `L²` class to a measurable set -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The restriction of an `L²` class to a subset, as an element of `L²` for the restricted
measure. -/
def restrictLp (S : Set α) (u : Lp ℂ 2 μ) : Lp ℂ 2 (μ.restrict S) :=
  ((Lp.memLp u).restrict S).toLp (u : α → ℂ)

theorem coeFn_restrictLp (S : Set α) (u : Lp ℂ 2 μ) :
    (restrictLp S u : α → ℂ) =ᵐ[μ.restrict S] (u : α → ℂ) :=
  MemLp.coeFn_toLp _

theorem norm_restrictLp_sq (S : Set α) (u : Lp ℂ 2 μ) :
    ‖restrictLp S u‖ ^ (2 : ℕ) = ∫ x in S, ‖u x‖ ^ (2 : ℕ) ∂μ := by
  rw [norm_lpTwo_sq]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_restrictLp S u] with x hx
  rw [hx]

theorem restrictLp_add (S : Set α) (u v : Lp ℂ 2 μ) :
    restrictLp S (u + v) = restrictLp S u + restrictLp S v := by
  rw [restrictLp, restrictLp, restrictLp, ← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ ?_
  exact (Lp.coeFn_add u v).filter_mono (Measure.restrict_le_self.absolutelyContinuous.ae_le)

theorem norm_restrictLp_le (S : Set α) (u : Lp ℂ 2 μ) : ‖restrictLp S u‖ ≤ ‖u‖ := by
  have hint : Integrable (fun x => ‖u x‖ ^ (2 : ℕ)) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have hle : ‖restrictLp S u‖ ^ (2 : ℕ) ≤ ‖u‖ ^ (2 : ℕ) := by
    rw [norm_restrictLp_sq, norm_lpTwo_sq]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle

/-! ## The distributional derivative of an `L²` function -/

theorem schwartz_lineDerivOp_one (u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (LineDeriv.lineDerivOp (1 : ℝ) u) x = deriv u x :=
  Complex.ext rfl rfl

/-- If `f` is differentiable with `f` and `f'` both in `L²`, then the tempered-distribution
derivative of `f` is the class of `f'`. -/
theorem lineDerivOp_toTemperedDistribution_eq {f f' : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hf' : MemLp f' 2 (volume : Measure ℝ))
    (hd : ∀ x : ℝ, HasDerivAt f (f' x) x) :
    LineDeriv.lineDerivOp (1 : ℝ) (Lp.toTemperedDistribution (hf.toLp f) : 𝓢'(ℝ, ℂ))
      = Lp.toTemperedDistribution (hf'.toLp f') := by
  ext u
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hu2 : MemLp (⇑u) 2 (volume : Measure ℝ) := u.memLp 2 volume
  have hdu : MemLp (fun x : ℝ => deriv u x) 2 (volume : Measure ℝ) := by
    have h := (SchwartzMap.derivCLM ℝ ℂ u).memLp 2 (volume : Measure ℝ)
    have he : ⇑(SchwartzMap.derivCLM ℝ ℂ u) = fun x : ℝ => deriv (⇑u) x := by
      funext x
      exact SchwartzMap.derivCLM_apply ℝ u x
    rwa [he] at h
  have hint1 : Integrable (⇑u * f') (volume : Measure ℝ) := hu2.integrable_mul hf'
  have hint2 : Integrable ((fun x : ℝ => deriv u x) * f) (volume : Measure ℝ) :=
    hdu.integrable_mul hf
  have hint3 : Integrable (⇑u * f) (volume : Measure ℝ) := hu2.integrable_mul hf
  have hparts : (∫ x : ℝ, u x * f' x) = -∫ x : ℝ, deriv u x * f x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := ⇑u) (v := f) (u' := fun x : ℝ => deriv u x) (v' := f')
      (fun x _ => (u.differentiable.differentiableAt).hasDerivAt)
      (fun x _ => hd x) hint1 hint2 hint3
  have hlhs : (∫ x : ℝ, (-(LineDeriv.lineDerivOp (1 : ℝ) u)) x • (hf.toLp f) x)
      = ∫ x : ℝ, (-(deriv u x)) * f x := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul]
    simp [schwartz_lineDerivOp_one]
  have hrhs : (∫ x : ℝ, u x • (hf'.toLp f') x) = ∫ x : ℝ, u x * f' x := by
    refine integral_congr_ae ?_
    filter_upwards [hf'.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul]
  rw [hlhs, hrhs, hparts]
  simp [integral_neg]


/-! ## The Fourier multiplier -/

/-- **The Fourier transform of a derivative.**  For a differentiable `f` with `f` and `f'` in `L²`,
the `L²`-Fourier transform of `f'` is `2πiξ` times that of `f`. -/
theorem coeFn_fourier_deriv_ae {f f' : ℝ → ℂ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hf' : MemLp f' 2 (volume : Measure ℝ))
    (hd : ∀ x : ℝ, HasDerivAt f (f' x) x) :
    ∀ᵐ ξ : ℝ, ((𝓕 (hf'.toLp f') : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ
      = (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))
        * ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ := by
  obtain ⟨w, hw⟩ : ∃ w : Lp ℂ 2 (volume : Measure ℝ), w = 𝓕 (hf.toLp f) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Lp ℂ 2 (volume : Measure ℝ), v = 𝓕 (hf'.toLp f') := ⟨_, rfl⟩
  have hmul : Function.HasTemperateGrowth (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ)) := by
    fun_prop
  have hkey : (Lp.toTemperedDistribution v : 𝓢'(ℝ, ℂ))
      = (2 * (Real.pi : ℂ) * Complex.I) •
        (TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => ((inner ℝ x (1 : ℝ) : ℝ) : ℂ))
          (Lp.toTemperedDistribution w)) := by
    rw [hv, hw, ← Lp.fourier_toTemperedDistribution_eq, ← Lp.fourier_toTemperedDistribution_eq,
      ← lineDerivOp_toTemperedDistribution_eq hf hf' hd]
    exact TemperedDistribution.fourier_lineDerivOp_eq _ 1
  have hv1 : LocallyIntegrable (fun ξ : ℝ => (v : ℝ → ℂ) ξ) volume :=
    (Lp.memLp v).locallyIntegrable one_le_two
  have hw1 : LocallyIntegrable (fun ξ : ℝ => (w : ℝ → ℂ) ξ) volume :=
    (Lp.memLp w).locallyIntegrable one_le_two
  have hw2 : LocallyIntegrable
      (fun ξ : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) * (w : ℝ → ℂ) ξ) volume := by
    rw [← locallyIntegrableOn_univ] at hw1 ⊢
    exact hw1.continuousOn_mul (by fun_prop) isClosed_univ.isLocallyClosed
  have hloc : LocallyIntegrable
      (fun ξ : ℝ => (v : ℝ → ℂ) ξ - (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) * (w : ℝ → ℂ) ξ)
      volume := hv1.sub hw2
  have hzero : ∀ᵐ ξ : ℝ,
      ((v : ℝ → ℂ) ξ - (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) * (w : ℝ → ℂ) ξ) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
    intro g hg hgc
    have hgc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
    obtain ⟨u, hu⟩ : ∃ u : 𝓢(ℝ, ℂ), u = hgc'.toSchwartzMap (by fun_prop) := ⟨_, rfl⟩
    have hufun : ∀ x : ℝ, u x = ((g x : ℝ) : ℂ) := by
      intro x
      rw [hu]
      rfl
    have happ := congrArg (fun T : 𝓢'(ℝ, ℂ) => T u) hkey
    simp only [IsSMulApply.smul_apply, Lp.toTemperedDistribution_apply,
      TemperedDistribution.smulLeftCLM_apply_apply, SchwartzMap.smulLeftCLM_apply hmul] at happ
    have hint1 : Integrable (fun x : ℝ => g x • (v : ℝ → ℂ) x) volume :=
      hv1.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
    have hint2 : Integrable
        (fun x : ℝ => g x • ((2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * (w : ℝ → ℂ) x)) volume :=
      hw2.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
    simp only [smul_sub]
    rw [integral_sub hint1 hint2]
    have hlhs : (∫ x : ℝ, g x • (v : ℝ → ℂ) x) = ∫ x : ℝ, u x • (v : ℝ → ℂ) x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hufun, smul_eq_mul, Complex.real_smul]
    have hrhs : (∫ x : ℝ, g x • ((2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) * (w : ℝ → ℂ) x))
        = (2 * (Real.pi : ℂ) * Complex.I) •
          ∫ x : ℝ, (((inner ℝ x (1 : ℝ) : ℝ) : ℂ) • u x) • (w : ℝ → ℂ) x := by
      rw [← integral_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have hinner : ∀ a : ℝ, (inner ℝ a (1 : ℝ) : ℝ) = a := fun a => by simp
      simp only [hufun, hinner, smul_eq_mul, Complex.real_smul]
      ring
    rw [hlhs, hrhs, ← happ]
    simp
  filter_upwards [hzero] with ξ hξ
  rw [hv, hw] at hξ
  exact sub_eq_zero.mp hξ


/-! ## Iterated derivatives -/

/-- The `L²`-Fourier transform of the `m`-th member of a derivative chain is `(2πiξ)^m` times the
transform of the first. -/
theorem coeFn_fourier_iter_ae {f : ℕ → ℝ → ℂ}
    (hmem : ∀ j : ℕ, MemLp (f j) 2 (volume : Measure ℝ))
    (hd : ∀ (j : ℕ) (x : ℝ), HasDerivAt (f j) (f (j + 1) x) x) (m : ℕ) :
    ∀ᵐ ξ : ℝ, ((𝓕 ((hmem m).toLp (f m)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ
      = (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) ^ m
        * ((𝓕 ((hmem 0).toLp (f 0)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ := by
  induction m with
  | zero =>
    filter_upwards with ξ
    simp
  | succ m ih =>
    have hstep := coeFn_fourier_deriv_ae (hmem m) (hmem (m + 1)) (hd m)
    filter_upwards [hstep, ih] with ξ h1 h2
    rw [h1, h2, pow_succ]
    ring

/-! ## The frequency tail bound -/

/-- The set of frequencies at which `2π|ξ|` is at least `r`. -/
def highFrequencySet (r : ℝ) : Set ℝ := {ξ : ℝ | r ≤ 2 * Real.pi * |ξ|}

theorem measurableSet_highFrequencySet (r : ℝ) : MeasurableSet (highFrequencySet r) := by
  have : Continuous fun ξ : ℝ => 2 * Real.pi * |ξ| := by fun_prop
  exact measurableSet_le measurable_const this.measurable

theorem integrable_normSq_lpTwo (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (fun x : ℝ => ‖u x‖ ^ (2 : ℕ)) volume :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)

/-- **The Paley–Wiener tail estimate.**  If the `m`-th derivative of `f 0` has small `L²` norm,
then the Fourier transform of `f 0` carries little mass above frequency `r`. -/
theorem highFrequency_integral_le {f : ℕ → ℝ → ℂ}
    (hmem : ∀ j : ℕ, MemLp (f j) 2 (volume : Measure ℝ))
    (hd : ∀ (j : ℕ) (x : ℝ), HasDerivAt (f j) (f (j + 1) x) x) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    r ^ (2 * m) * (∫ ξ in highFrequencySet r,
        ‖((𝓕 ((hmem 0).toLp (f 0)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ (2 : ℕ))
      ≤ ‖(hmem m).toLp (f m)‖ ^ (2 : ℕ) := by
  obtain ⟨w, hw⟩ : ∃ w : Lp ℂ 2 (volume : Measure ℝ), w = 𝓕 ((hmem 0).toLp (f 0)) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Lp ℂ 2 (volume : Measure ℝ), v = 𝓕 ((hmem m).toLp (f m)) := ⟨_, rfl⟩
  have hiter := coeFn_fourier_iter_ae hmem hd m
  rw [← hw, ← hv] at hiter
  rw [← hw]
  have hwint : Integrable (fun x : ℝ => ‖(w : ℝ → ℂ) x‖ ^ (2 : ℕ)) volume := integrable_normSq_lpTwo w
  have hvint : Integrable (fun x : ℝ => ‖(v : ℝ → ℂ) x‖ ^ (2 : ℕ)) volume := integrable_normSq_lpTwo v
  have hmeas : MeasurableSet (highFrequencySet r) := measurableSet_highFrequencySet r
  have hstep : ∀ᵐ ξ : ℝ ∂(volume.restrict (highFrequencySet r)),
      r ^ (2 * m) * ‖(w : ℝ → ℂ) ξ‖ ^ (2 : ℕ) ≤ ‖(v : ℝ → ℂ) ξ‖ ^ (2 : ℕ) := by
    rw [ae_restrict_iff' hmeas]
    filter_upwards [hiter] with ξ hξ hmem'
    have hge : r ≤ 2 * Real.pi * |ξ| := hmem'
    have hnorm : ‖(v : ℝ → ℂ) ξ‖ = (2 * Real.pi * |ξ|) ^ m * ‖(w : ℝ → ℂ) ξ‖ := by
      rw [hξ, norm_mul, norm_pow]
      congr 2
      rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)
          = ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I by push_cast; ring, norm_mul, Complex.norm_I,
        Complex.norm_real, mul_one]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    rw [hnorm, mul_pow, ← pow_mul]
    have hbase : r ^ (2 * m) ≤ (2 * Real.pi * |ξ|) ^ (m * 2) := by
      rw [mul_comm m 2]
      exact pow_le_pow_left₀ hr.le hge (2 * m)
    have hnn : (0 : ℝ) ≤ ‖(w : ℝ → ℂ) ξ‖ ^ (2 : ℕ) := by positivity
    exact mul_le_mul_of_nonneg_right hbase hnn
  have hle : (∫ ξ in highFrequencySet r, r ^ (2 * m) * ‖(w : ℝ → ℂ) ξ‖ ^ (2 : ℕ))
      ≤ ∫ ξ in highFrequencySet r, ‖(v : ℝ → ℂ) ξ‖ ^ (2 : ℕ) :=
    integral_mono_ae ((hwint.const_mul _).restrict) hvint.restrict hstep
  have hfull : (∫ ξ in highFrequencySet r, ‖(v : ℝ → ℂ) ξ‖ ^ (2 : ℕ))
      ≤ ∫ ξ : ℝ, ‖(v : ℝ → ℂ) ξ‖ ^ (2 : ℕ) :=
    setIntegral_le_integral hvint (Filter.Eventually.of_forall fun x => by positivity)
  have hnormv : (∫ ξ : ℝ, ‖(v : ℝ → ℂ) ξ‖ ^ (2 : ℕ)) = ‖(hmem m).toLp (f m)‖ ^ (2 : ℕ) := by
    rw [← norm_lpTwo_sq v, hv, Lp.norm_fourier_eq]
  rw [integral_const_mul] at hle
  rw [← hnormv]
  exact le_trans hle hfull


/-- **The Paley--Wiener tail estimate in norm form.** -/
theorem norm_restrictLp_fourier_le {f : ℕ → ℝ → ℂ}
    (hmem : ∀ j : ℕ, MemLp (f j) 2 (volume : Measure ℝ))
    (hd : ∀ (j : ℕ) (x : ℝ), HasDerivAt (f j) (f (j + 1) x) x) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    r ^ m * ‖restrictLp (highFrequencySet r) (𝓕 ((hmem 0).toLp (f 0)))‖
      ≤ ‖(hmem m).toLp (f m)‖ := by
  have h := highFrequency_integral_le hmem hd hr m
  rw [← norm_restrictLp_sq] at h
  have h2 : (r ^ m * ‖restrictLp (highFrequencySet r) (𝓕 ((hmem 0).toLp (f 0)))‖) ^ (2 : ℕ)
      ≤ ‖(hmem m).toLp (f m)‖ ^ (2 : ℕ) := by
    rw [mul_pow, ← pow_mul, mul_comm m 2]
    exact h
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h2


/-! ## The real-to-complex embedding of `L²` -/

theorem norm_lpTwo_real_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℝ 2 μ) :
    ‖u‖ ^ (2 : ℕ) = ∫ x, u x ^ (2 : ℕ) ∂μ := by
  have h := @real_inner_self_eq_norm_sq (Lp ℝ 2 μ) _ _ u
  rw [← h, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

/-- The complexification of a real `L²` class. -/
def ofRealLp {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℝ 2 μ) : Lp ℂ 2 μ :=
  Complex.ofRealCLM.compLpL 2 μ u

theorem coeFn_ofRealLp {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℝ 2 μ) :
    (ofRealLp u : α → ℂ) =ᵐ[μ] fun x => ((u x : ℝ) : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL u

theorem norm_ofRealLp {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℝ 2 μ) :
    ‖ofRealLp u‖ = ‖u‖ := by
  have hsq : ‖ofRealLp u‖ ^ (2 : ℕ) = ‖u‖ ^ (2 : ℕ) := by
    rw [norm_lpTwo_sq, norm_lpTwo_real_sq]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_ofRealLp u] with x hx
    rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h1 := (pow_le_pow_iff_left₀ (norm_nonneg (ofRealLp u)) (norm_nonneg u) two_ne_zero).1 hsq.le
  have h2 := (pow_le_pow_iff_left₀ (norm_nonneg u) (norm_nonneg (ofRealLp u)) two_ne_zero).1 hsq.ge
  exact le_antisymm h1 h2

theorem ofRealLp_sub {α : Type*} [MeasurableSpace α] {μ : Measure α} (u v : Lp ℝ 2 μ) :
    ofRealLp (u - v) = ofRealLp u - ofRealLp v :=
  map_sub (Complex.ofRealCLM.compLpL 2 μ) u v

theorem memLp_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {h : α → ℝ}
    (hh : MemLp h 2 μ) : MemLp (fun x => ((h x : ℝ) : ℂ)) 2 μ := hh.ofReal

theorem ofRealLp_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {h : α → ℝ}
    (hh : MemLp h 2 μ) :
    ofRealLp (hh.toLp h) = (memLp_ofReal hh).toLp fun x => ((h x : ℝ) : ℂ) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ofRealLp (hh.toLp h), hh.coeFn_toLp,
    (memLp_ofReal hh).coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, h3]


/-! ## Passing the tail bound to a strong limit -/

theorem fourier_lp_sub (u v : Lp ℂ 2 (volume : Measure ℝ)) :
    (𝓕 (u - v) : Lp ℂ 2 (volume : Measure ℝ)) = 𝓕 u - 𝓕 v :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).map_sub u v

/-- A uniform frequency-tail bound along a strongly convergent sequence passes to the limit. -/
theorem norm_restrictLp_fourier_limit_le {u : ℕ → Lp ℂ 2 (volume : Measure ℝ)}
    {U : Lp ℂ 2 (volume : Measure ℝ)}
    (hu : Filter.Tendsto u Filter.atTop (nhds U)) (S : Set ℝ) {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : ∀ k : ℕ, ‖restrictLp S (𝓕 (u k))‖ ≤ c k)
    (hcL : Filter.Tendsto c Filter.atTop (nhds c₀)) :
    ‖restrictLp S (𝓕 U)‖ ≤ c₀ := by
  have hdiff : Filter.Tendsto (fun k : ℕ => ‖U - u k‖) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun k : ℕ => U - u k) Filter.atTop (nhds (U - U)) :=
      tendsto_const_nhds.sub hu
    rw [sub_self] at h
    simpa using h.norm
  have hstep : ∀ k : ℕ, ‖restrictLp S (𝓕 U)‖ ≤ ‖U - u k‖ + c k := by
    intro k
    have hsum : (𝓕 (U - u k) : Lp ℂ 2 (volume : Measure ℝ)) + 𝓕 (u k) = 𝓕 U := by
      rw [fourier_lp_sub]
      abel
    calc ‖restrictLp S (𝓕 U)‖
        = ‖restrictLp S (𝓕 (U - u k)) + restrictLp S (𝓕 (u k))‖ := by
          rw [← restrictLp_add, hsum]
      _ ≤ ‖restrictLp S (𝓕 (U - u k))‖ + ‖restrictLp S (𝓕 (u k))‖ := norm_add_le _ _
      _ ≤ ‖U - u k‖ + c k := by
          refine add_le_add ?_ (hc k)
          refine le_trans (norm_restrictLp_le _ _) ?_
          rw [Lp.norm_fourier_eq]
  have hlim : Filter.Tendsto (fun k : ℕ => ‖U - u k‖ + c k) Filter.atTop (nhds (0 + c₀)) :=
    hdiff.add hcL
  rw [zero_add] at hlim
  exact ge_of_tendsto' hlim hstep


theorem ae_eq_zero_of_restrictLp_eq_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S : Set α} (hS : MeasurableSet S) {u : Lp ℂ 2 μ} (h : restrictLp S u = 0) :
    ∀ᵐ x ∂μ, x ∈ S → (u : α → ℂ) x = 0 := by
  have h0 : (restrictLp S u : α → ℂ) =ᵐ[μ.restrict S] 0 := by
    rw [h]
    exact Lp.coeFn_zero ℂ 2 (μ.restrict S)
  have h1 : ∀ᵐ x ∂μ.restrict S, (u : α → ℂ) x = 0 := by
    filter_upwards [(coeFn_restrictLp S u).symm, h0] with x hx hx0
    rw [hx, hx0]
    rfl
  rwa [← ae_restrict_iff' hS]

end GaloisForLFunctions.HTGeometry

end
