import GaloisForLFunctions.PNTPlus.MediumPNT
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Mertens' theorem with the Euler constant for the von Mangoldt function

`Σ_{n ≤ x} Λ(n)/n = log x − γ + o(1)`.

The proof is the classical Abelian argument.  The Laurent expansion of the logarithmic derivative,
`−ζ'(s)/ζ(s) = 1/(s−1) − γ + o(1)` at `s → 1`, follows from Mathlib's limit `ζ(s) − 1/(s−1) → γ`
and the removable singularity of that regular part.  Abel summation writes
`Σ Λ(n)n^{−s} = s∫_1^∞ ψ(t)t^{−s−1}dt` for real `s > 1`, so with `E(t) = ψ(t) − t`
`s∫_1^∞ E(t)t^{−s−1}dt = −ζ'/ζ(s) − s/(s−1) → −γ − 1`.  The prime number theorem with error term
makes `E(t)/t²` integrable on `(1,∞)`, and dominated convergence identifies
`∫_1^∞ E(t)t^{−2}dt = −γ − 1`.  A second Abel summation gives
`Σ_{n≤x}Λ(n)/n = 1 + E(x)/x + log x + ∫_1^x E(t)t^{−2}dt`, whence the theorem.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-! ## The Laurent constant of the logarithmic derivative -/

/-- The regular part `ζ(s) − 1/(s−1)`, extended by `γ` at `s = 1`. -/
def zetaRegularPart : ℂ → ℂ :=
  Function.update (fun s : ℂ => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)

theorem zetaRegularPart_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaRegularPart s = riemannZeta s - 1 / (s - 1) := by
  unfold zetaRegularPart
  rw [Function.update_of_ne hs]

theorem zetaRegularPart_one : zetaRegularPart 1 = (Real.eulerMascheroniConstant : ℂ) := by
  unfold zetaRegularPart
  rw [Function.update_self]

theorem continuousAt_zetaRegularPart_one : ContinuousAt zetaRegularPart 1 := by
  unfold zetaRegularPart
  rw [continuousAt_update_same]
  exact tendsto_riemannZeta_sub_one_div

theorem differentiableAt_zetaRegularPart_of_ne {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ zetaRegularPart s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => riemannZeta s - 1 / (s - 1)) s := by
    apply (differentiableAt_riemannZeta hs).sub
    exact (differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs)
  apply h1.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hs] with z hz
  exact zetaRegularPart_of_ne hz

theorem analyticAt_zetaRegularPart_one : AnalyticAt ℂ zetaRegularPart 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _
    continuousAt_zetaRegularPart_one
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact differentiableAt_zetaRegularPart_of_ne hz

theorem tendsto_deriv_zetaRegularPart_one :
    Tendsto (deriv zetaRegularPart) (𝓝 1) (𝓝 (deriv zetaRegularPart 1)) :=
  analyticAt_zetaRegularPart_one.deriv.continuousAt

theorem deriv_riemannZeta_eq_of_ne {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta s = -(1 / (s - 1) ^ 2) + deriv zetaRegularPart s := by
  have hR : HasDerivAt zetaRegularPart (deriv zetaRegularPart s) s :=
    (differentiableAt_zetaRegularPart_of_ne hs).hasDerivAt
  have hinv : HasDerivAt (fun s : ℂ => (s - 1)⁻¹) (-(1 / (s - 1) ^ 2)) s := by
    have h := ((hasDerivAt_id s).sub_const 1).inv (sub_ne_zero.mpr hs)
    exact h.congr_deriv (by simp [neg_div])
  have hsum := hR.add hinv
  have heq : riemannZeta =ᶠ[𝓝 s] (fun s : ℂ => zetaRegularPart s + (s - 1)⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    rw [zetaRegularPart_of_ne hz]
    ring
  rw [(hsum.congr_of_eventuallyEq heq).deriv]
  ring

/-- **Laurent constant of `−ζ'/ζ` at `1`:** `−ζ'(s)/ζ(s) − 1/(s−1) → −γ`. -/
theorem tendsto_neg_logDeriv_riemannZeta_sub_one_div :
    Tendsto (fun s : ℂ => -deriv riemannZeta s / riemannZeta s - 1 / (s - 1)) (𝓝[≠] 1)
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
  have hR : Tendsto zetaRegularPart (𝓝[≠] 1) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
    have := continuousAt_zetaRegularPart_one.tendsto
    rw [zetaRegularPart_one] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hR' : Tendsto (deriv zetaRegularPart) (𝓝[≠] 1) (𝓝 (deriv zetaRegularPart 1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_deriv_zetaRegularPart_one
  have hs1 : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - 1) (𝓝 1) (𝓝 ((1 : ℂ) - 1)) :=
      (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hnum : Tendsto (fun s : ℂ => -((s - 1) * deriv zetaRegularPart s) - zetaRegularPart s)
      (𝓝[≠] 1) (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    have := ((hs1.mul hR').neg).sub hR
    simpa using this
  have hden : Tendsto (fun s : ℂ => 1 + (s - 1) * zetaRegularPart s) (𝓝[≠] 1) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ))).add (hs1.mul hR)
    simpa using this
  have hlim := hnum.div hden one_ne_zero
  simp only [div_one] at hlim
  refine hlim.congr' ?_
  have hne : ∀ᶠ s in 𝓝[≠] 1, 1 + (s - 1) * zetaRegularPart s ≠ 0 := hden.eventually_ne one_ne_zero
  filter_upwards [hne, self_mem_nhdsWithin] with s hs hs1'
  have hs1'' : s ≠ 1 := hs1'
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1''
  rw [deriv_riemannZeta_eq_of_ne hs1'']
  have hz : riemannZeta s = (1 + (s - 1) * zetaRegularPart s) / (s - 1) := by
    rw [zetaRegularPart_of_ne hs1'']
    field_simp
    ring
  simp only [Pi.div_apply]
  rw [hz]
  field_simp
  ring

/-- The same limit along real `s → 1⁺`. -/
theorem tendsto_neg_logDeriv_riemannZeta_sub_one_div_real :
    Tendsto (fun s : ℝ => -deriv riemannZeta s / riemannZeta s - 1 / ((s : ℂ) - 1)) (𝓝[>] 1)
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
  have hmap : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := Complex.continuous_ofReal.tendsto 1
      simp only [Complex.ofReal_one] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have : s = 1 := by exact_mod_cast h
      exact absurd this (ne_of_gt hs)
  exact tendsto_neg_logDeriv_riemannZeta_sub_one_div.comp hmap

/-! ## The prime error and its integrability -/

open MeasureTheory Set
open scoped Chebyshev
open ArithmeticFunction (vonMangoldt)

/-- The Chebyshev error `E(t) = ψ(t) − t`. -/
def chebyshevError (t : ℝ) : ℝ := ψ t - t

theorem measurable_psi : Measurable ψ := by
  have : ψ = fun t : ℝ => (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, vonMangoldt k) ⌊t⌋₊ := by
    funext t
    exact Chebyshev.psi_eq_sum_Icc t
  rw [this]
  exact (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, vonMangoldt k)).comp
    (Nat.measurable_floor (R := ℝ))

theorem measurable_chebyshevError : Measurable chebyshevError :=
  measurable_psi.sub measurable_id

/-- The prime number theorem with error term, in the form used below. -/
theorem chebyshevError_bound : ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in atTop,
    |chebyshevError t| ≤ C * (t * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C, hC⟩ := hO.bound
  refine ⟨c, hc, |C|, abs_nonneg _, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with t ht ht1
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at ht
  simp only [Pi.sub_apply, id_eq] at ht
  unfold chebyshevError
  have hpos : 0 ≤ t * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10)) := by positivity
  rw [abs_of_nonneg hpos] at ht
  calc |ψ t - t| ≤ C * (t * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))) := ht
    _ ≤ |C| * (t * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hpos

/-- `e^{−c u^{1/10}} ≤ 20!/(c^{20} u²)` for `c, u > 0`. -/
theorem exp_neg_rpow_tenth_le {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    Real.exp (-c * u ^ ((1 : ℝ) / 10)) ≤ (Nat.factorial 20 : ℝ) / (c ^ 20 * u ^ 2) := by
  have hx : 0 ≤ c * u ^ ((1 : ℝ) / 10) := by positivity
  have h := Real.sum_le_exp_of_nonneg hx 21
  have hterm : (c * u ^ ((1 : ℝ) / 10)) ^ 20 / (Nat.factorial 20 : ℝ) ≤
      ∑ i ∈ Finset.range 21, (c * u ^ ((1 : ℝ) / 10)) ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (f := fun i => (c * u ^ ((1 : ℝ) / 10)) ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (by norm_num : 20 < 21))
  have hpow : (u ^ ((1 : ℝ) / 10)) ^ 20 = u ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    norm_num
  have hkey : c ^ 20 * u ^ 2 / (Nat.factorial 20 : ℝ) ≤ Real.exp (c * u ^ ((1 : ℝ) / 10)) := by
    calc c ^ 20 * u ^ 2 / (Nat.factorial 20 : ℝ)
        = (c * u ^ ((1 : ℝ) / 10)) ^ 20 / (Nat.factorial 20 : ℝ) := by rw [mul_pow, hpow]
      _ ≤ _ := hterm
      _ ≤ _ := h
  rw [neg_mul, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  all_goals exact hkey

/-- `1/(t (log t)²)` is integrable on `(e, ∞)`. -/
theorem integrableOn_inv_mul_log_sq :
    IntegrableOn (fun t : ℝ => 1 / (t * Real.log t ^ 2)) (Ioi (Real.exp 1)) := by
  have hg : ∀ x ∈ Ioi (Real.exp 1),
      HasDerivAt (fun t : ℝ => -(Real.log t)⁻¹) (1 / (x * Real.log x ^ 2)) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
    have hlog : 0 < Real.log x := by
      have := Real.log_lt_log (Real.exp_pos 1) hx
      rw [Real.log_exp] at this
      linarith
    have h := ((Real.hasDerivAt_log hx0.ne').inv hlog.ne').neg
    refine h.congr_deriv ?_
    field_simp
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun t => -(Real.log t)⁻¹) (l := 0) ?_ hg ?_ ?_
  · apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.neg
    apply ContinuousAt.inv₀ (Real.continuousAt_log (Real.exp_pos 1).ne')
    rw [Real.log_exp]
    norm_num
  · intro x hx
    have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
    positivity
  · have : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
      Real.tendsto_log_atTop.inv_tendsto_atTop
    simpa using this.neg

theorem integrableOn_chebyshevError_div_sq :
    IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi 1) := by
  obtain ⟨c, hc, C, hC0, hC⟩ := chebyshevError_bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hC
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = max T₀ (Real.exp 1) := ⟨_, rfl⟩
  have hTe : Real.exp 1 ≤ T := hT ▸ le_max_right _ _
  have hT0 : T₀ ≤ T := hT ▸ le_max_left _ _
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hT1 : 1 < T := lt_of_lt_of_le he1 hTe
  have hmeas : Measurable (fun t : ℝ => chebyshevError t / t ^ 2) :=
    measurable_chebyshevError.div (measurable_id.pow_const 2)
  have htail : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi T) := by
    have hK : IntegrableOn (fun t : ℝ =>
        (C * (Nat.factorial 20 : ℝ) / c ^ 20) * (1 / (t * Real.log t ^ 2))) (Ioi T) :=
      (integrableOn_inv_mul_log_sq.mono_set (Ioi_subset_Ioi hTe)).const_mul _
    refine hK.mono' hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht1 : 1 < t := lt_trans hT1 ht
    have hbound := hT₀ t (le_trans hT0 ht.le)
    have hlog1 : 1 ≤ Real.log t := by
      have := Real.log_le_log (Real.exp_pos 1) (le_trans hTe ht.le)
      rwa [Real.log_exp] at this
    have hexp := exp_neg_rpow_tenth_le hc (show 0 < Real.log t by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2),
      div_le_iff₀ (by positivity)]
    have ht0 : 0 < t := by linarith
    calc |chebyshevError t| ≤ C * (t * Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10))) := hbound
      _ ≤ C * (t * ((Nat.factorial 20 : ℝ) / (c ^ 20 * Real.log t ^ 2))) := by gcongr
      _ = (C * (Nat.factorial 20 : ℝ) / c ^ 20) * (1 / (t * Real.log t ^ 2)) * t ^ 2 := by
          field_simp
  have hhead : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioc 1 T) := by
    apply Measure.integrableOn_of_bounded (M := ψ T + T) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht1 : 1 < t := ht.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    have hψ : ψ t ≤ ψ T := Chebyshev.psi_mono ht.2
    have hψ0 := Chebyshev.psi_nonneg t
    have hψT := Chebyshev.psi_nonneg T
    have hE : |chebyshevError t| ≤ ψ T + T := by
      unfold chebyshevError
      rw [abs_le]
      constructor <;> linarith [ht.2]
    have ht2 : 1 ≤ t ^ 2 := by nlinarith
    calc |chebyshevError t| / t ^ 2 ≤ |chebyshevError t| / 1 :=
          div_le_div_of_nonneg_left (abs_nonneg _) one_pos ht2
      _ = |chebyshevError t| := div_one _
      _ ≤ ψ T + T := hE
  have := hhead.union htail
  rwa [Ioc_union_Ioi_eq_Ioi hT1.le] at this

/-! ## Abel summation and the Mellin identity -/

/-- Real summability of `Λ(n) n^{−s}` for `s > 1`. -/
theorem summable_vonMangoldt_div_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => vonMangoldt n / (n : ℝ) ^ s) := by
  have hε : 0 < (s - 1) / 2 := by linarith
  have hsum : Summable (fun n : ℕ => 2 / (s - 1) * ((n : ℝ) ^ ((s + 1) / 2))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (show 1 < (s + 1) / 2 by linarith)).mul_left _
  have hs1 : 0 < s - 1 := by linarith
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [ArithmeticFunction.map_zero, Nat.cast_zero, zero_div]
    positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have h2 : Real.log n ≤ (n : ℝ) ^ ((s - 1) / 2) / ((s - 1) / 2) :=
      Real.log_le_rpow_div hn'.le hε
    have hsplit : (n : ℝ) ^ ((s - 1) / 2) = ((n : ℝ) ^ ((s + 1) / 2))⁻¹ * (n : ℝ) ^ s := by
      rw [← Real.rpow_neg hn'.le, ← Real.rpow_add hn']
      congr 1
      ring
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hn' s)]
    calc vonMangoldt n ≤ (n : ℝ) ^ ((s - 1) / 2) / ((s - 1) / 2) := h1.trans h2
      _ = 2 / (s - 1) * (n : ℝ) ^ ((s - 1) / 2) := by
          field_simp
      _ = 2 / (s - 1) * ((n : ℝ) ^ ((s + 1) / 2))⁻¹ * (n : ℝ) ^ s := by
          rw [hsplit]
          ring

theorem finset_Icc_zero_eq_range (n : ℕ) : Finset.Icc 0 n = Finset.range (n + 1) := by
  ext k
  simp

/-- Abel summation: `Σ_n Λ(n) n^{−s} = s ∫_1^∞ ψ(t) t^{−s−1} dt` for real `s > 1`. -/
theorem tsum_vonMangoldt_div_rpow_eq {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s) = s * ∫ t in Ioi 1, ψ t * t ^ (-s - 1) := by
  obtain ⟨c, hc, C, hC0, hC⟩ := chebyshevError_bound
  have hψ : ∀ᶠ t : ℝ in atTop, |ψ t| ≤ (C + 1) * t := by
    filter_upwards [hC, eventually_ge_atTop 1] with t ht ht1
    have hexp1 : Real.exp (-c * Real.log t ^ ((1 : ℝ) / 10)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ Real.log t ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (Real.log_nonneg ht1) _
      nlinarith
    have hE : |chebyshevError t| ≤ C * t := by
      refine ht.trans ?_
      have ht0 : 0 ≤ t := by linarith
      nlinarith [mul_nonneg hC0 ht0]
    unfold chebyshevError at hE
    rw [abs_of_nonneg (Chebyshev.psi_nonneg t)]
    rw [abs_le] at hE
    linarith [hE.2]
  have hψn : ∀ᶠ n : ℕ in atTop, |ψ n| ≤ (C + 1) * n := tendsto_natCast_atTop_atTop.eventually hψ
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun t => t ^ (-s) := ⟨_, rfl⟩
  have hf_diff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ f t := fun t ht => by
    rw [hf]
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (show 0 < t by linarith [mem_Ici.mp ht])))).differentiableAt
  have hderiv : ∀ t ∈ Ici (1 : ℝ), deriv f t = -s * t ^ (-s - 1) := fun t ht => by
    rw [hf, (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (show 0 < t by linarith [mem_Ici.mp ht])))).deriv]
  have hf_int : LocallyIntegrableOn (deriv f) (Ici 1) := by
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ici
    refine ContinuousOn.congr ?_ (fun t ht => (hderiv t ht))
    exact continuousOn_const.mul
      (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (show 0 < t by
        linarith [mem_Ici.mp ht]))))
  have hpsi_n : ∀ n : ℕ, ∑ k ∈ Finset.Icc 0 n, vonMangoldt k = ψ n := fun n => by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp
  have h_lim : Tendsto (fun n : ℕ => f n * ∑ k ∈ Finset.Icc 0 n, vonMangoldt k) atTop (𝓝 0) := by
    simp_rw [hpsi_n]
    apply squeeze_zero_norm' (a := fun n : ℕ => (C + 1) * (n : ℝ) ^ (-(s - 1)))
    · filter_upwards [hψn, eventually_ge_atTop 1] with n hn hn1
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      rw [hf, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
      calc (n : ℝ) ^ (-s) * |ψ n| ≤ (n : ℝ) ^ (-s) * ((C + 1) * n) := by gcongr
        _ = (C + 1) * (n : ℝ) ^ (-(s - 1)) := by
            rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add (by linarith), Real.rpow_one]
            ring
    · have := (tendsto_rpow_neg_atTop (show 0 < s - 1 by linarith)).comp tendsto_natCast_atTop_atTop
      simpa using this.const_mul (C + 1)
  have hg_dom : (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k) =O[atTop]
      (fun t : ℝ => t ^ (-s)) := by
    apply Asymptotics.IsBigO.of_bound (s * (C + 1))
    filter_upwards [hψ, eventually_ge_atTop 1] with t ht ht1
    rw [← Chebyshev.psi_eq_sum_Icc, hderiv t (mem_Ici.mpr ht1)]
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
      abs_of_pos (by linarith : (0 : ℝ) < s), abs_of_pos (Real.rpow_pos_of_pos ht0 _),
      abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    have hpow : t ^ (-s - 1) * t = t ^ (-s) := by
      rw [show -s - 1 = -s + (-1) by ring, Real.rpow_add ht0, Real.rpow_neg_one]
      field_simp
    calc s * t ^ (-s - 1) * |ψ t| ≤ s * t ^ (-s - 1) * ((C + 1) * t) := by gcongr
      _ = s * (C + 1) * t ^ (-s) := by rw [← hpow]; ring
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-s)) atTop :=
    ⟨Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) one_pos⟩
  have h := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := fun n => vonMangoldt n) (f := f)
    (by simp) hf_diff hf_int h_lim hg_dom hg_int
  have hsum : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, f k * vonMangoldt k) atTop
      (𝓝 (∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s)) := by
    have hS := (summable_vonMangoldt_div_rpow hs).hasSum.tendsto_sum_nat
    have hS' := (Filter.tendsto_add_atTop_iff_nat 1).mpr hS
    refine hS'.congr ?_
    intro n
    rw [← finset_Icc_zero_eq_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf, Real.rpow_neg (Nat.cast_nonneg k)]
    ring
  have hlimeq := tendsto_nhds_unique hsum h
  rw [hlimeq, zero_sub, ← integral_neg, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only
  rw [← Chebyshev.psi_eq_sum_Icc, hderiv t (mem_Ici.mpr (le_of_lt ht))]
  ring

theorem mul_rpow_neg_sub_one {t : ℝ} (ht : 0 < t) (s : ℝ) : t * t ^ (-s - 1) = t ^ (-s) := by
  have : t ^ (-s) = t ^ (1 + (-s - 1)) := by
    congr 1
    ring
  rw [this, Real.rpow_add ht, Real.rpow_one]

/-- Splitting `ψ = t + E`: `∫_1^∞ ψ t^{−s−1} = 1/(s−1) + ∫_1^∞ E t^{−s−1}`. -/
theorem integral_psi_rpow_split {s : ℝ} (hs : 1 < s) :
    (∫ t in Ioi 1, ψ t * t ^ (-s - 1)) =
      1 / (s - 1) + ∫ t in Ioi 1, chebyshevError t * t ^ (-s - 1) := by
  have h1 : IntegrableOn (fun t : ℝ => t * t ^ (-s - 1)) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (show -s < -1 by linarith) one_pos).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    simp only
    rw [mul_rpow_neg_sub_one (lt_trans one_pos ht)]
  have h2 : IntegrableOn (fun t : ℝ => chebyshevError t * t ^ (-s - 1)) (Ioi 1) := by
    refine integrableOn_chebyshevError_div_sq.abs.mono'
      (measurable_chebyshevError.mul (measurable_id.pow_const _)).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    have hle : t ^ (-s - 1) ≤ t ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt ht) (by linarith)
    rw [Real.rpow_neg ht0.le, Real.rpow_two] at hle
    calc |chebyshevError t| * t ^ (-s - 1) ≤ |chebyshevError t| * (t ^ 2)⁻¹ := by gcongr
      _ = |chebyshevError t| / t ^ 2 := by rw [div_eq_mul_inv]
  have hsplit : (fun t : ℝ => ψ t * t ^ (-s - 1)) =
      fun t => t * t ^ (-s - 1) + chebyshevError t * t ^ (-s - 1) := by
    funext t
    unfold chebyshevError
    ring
  rw [hsplit, integral_add h1 h2]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => t ^ (-s)) (fun t ht => by
      simp only
      rw [mul_rpow_neg_sub_one (lt_trans one_pos ht)]),
    integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs)
  have h2' : -s + 1 ≠ 0 := by
    rw [show -s + 1 = -(s - 1) by ring]
    exact neg_ne_zero.mpr h1'
  rw [div_eq_div_iff h2' h1']
  ring

/-! ## The constant `−γ − 1` -/

theorem integral_chebyshevError_div_sq :
    (∫ t in Ioi 1, chebyshevError t / t ^ 2) = -Real.eulerMascheroniConstant - 1 := by
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun t : ℝ => chebyshevError t * t ^ (-s - 1))
      (volume.restrict (Ioi 1)) := fun s =>
    (measurable_chebyshevError.mul (measurable_id.pow_const _)).aestronglyMeasurable
  have hbound_int : Integrable (fun t : ℝ => |chebyshevError t| / t ^ 2) (volume.restrict (Ioi 1)) := by
    refine integrableOn_chebyshevError_div_sq.abs.congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
  -- dominated convergence as `s → 1⁺`
  have hway2 : Tendsto (fun s : ℝ => s * ∫ t in Ioi 1, chebyshevError t * t ^ (-s - 1)) (𝓝[>] 1)
      (𝓝 (1 * ∫ t in Ioi 1, chebyshevError t * t ^ (-(1 : ℝ) - 1))) := by
    apply Tendsto.mul (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
    apply tendsto_integral_filter_of_dominated_convergence (fun t => |chebyshevError t| / t ^ 2)
    · exact Filter.Eventually.of_forall hmeas
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht0 : 0 < t := lt_trans one_pos ht
      have hs1 : (1 : ℝ) < s := hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
      have hle : t ^ (-s - 1) ≤ t ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt ht) (by linarith)
      rw [Real.rpow_neg ht0.le, Real.rpow_two] at hle
      calc |chebyshevError t| * t ^ (-s - 1) ≤ |chebyshevError t| * (t ^ 2)⁻¹ := by gcongr
        _ = |chebyshevError t| / t ^ 2 := by rw [div_eq_mul_inv]
    · exact hbound_int
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht0 : 0 < t := lt_trans one_pos ht
      apply Tendsto.const_mul
      have hcont := (Real.continuousAt_const_rpow (a := t) (b := -(1 : ℝ) - 1) ht0.ne').tendsto
      have hexp : Tendsto (fun s : ℝ => -s - 1) (𝓝 1) (𝓝 (-(1 : ℝ) - 1)) :=
        (continuous_neg.sub continuous_const).tendsto 1
      exact tendsto_nhdsWithin_of_tendsto_nhds (hcont.comp hexp)
  -- the zeta side as `s → 1⁺`
  have hway1 : Tendsto (fun s : ℝ => s * ∫ t in Ioi 1, chebyshevError t * t ^ (-s - 1)) (𝓝[>] 1)
      (𝓝 (-Real.eulerMascheroniConstant - 1)) := by
    have hre : Tendsto (fun s : ℝ =>
        (-deriv riemannZeta s / riemannZeta s - 1 / ((s : ℂ) - 1)).re) (𝓝[>] 1)
        (𝓝 (-Real.eulerMascheroniConstant)) := by
      have h := (Complex.continuous_re.tendsto _).comp
        tendsto_neg_logDeriv_riemannZeta_sub_one_div_real
      simp only [Function.comp_def, Complex.neg_re, Complex.ofReal_re] at h
      exact h
    refine (hre.sub_const 1).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (1 : ℝ) < s := hs
    have hL : LSeries (fun n => (vonMangoldt n : ℂ)) (s : ℂ) =
        ((∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      unfold LSeries
      congr 1
      funext n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [LSeries.term_zero]
      · rw [LSeries.term_of_ne_zero hn.ne', Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n)]
        push_cast
        rfl
    have hzeta := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s := (s : ℂ)) (by simpa using hs1)
    rw [← hzeta, hL]
    have hcast : ((∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s : ℝ) : ℂ) - 1 / ((s : ℂ) - 1) =
        (((∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s) - 1 / (s - 1) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.ofReal_re, tsum_vonMangoldt_div_rpow_eq hs1, integral_psi_rpow_split hs1]
    have : s - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hlim := tendsto_nhds_unique hway2 hway1
  rw [one_mul] at hlim
  rw [← hlim]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [show -(1 : ℝ) - 1 = -(2 : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_two, div_eq_mul_inv]

/-! ## Mertens' theorem with the Euler constant -/

/-- Abel summation for the reciprocal sum: `Σ_{k ≤ x} Λ(k)/k = ψ(x)/x + ∫_1^x ψ(t)/t² dt`. -/
theorem sum_vonMangoldt_div_eq {x : ℝ} (hx : 1 ≤ x) :
    (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / k) = ψ x / x + ∫ t in (1 : ℝ)..x, ψ t / t ^ 2 := by
  have h := sum_mul_eq_sub_integral_mul₀ (c := fun k => vonMangoldt k) (f := fun t : ℝ => t⁻¹)
    (by simp) x (fun t ht => differentiableAt_inv (by linarith [ht.1] : t ≠ 0)) ?_
  · simp_rw [← Chebyshev.psi_eq_sum_Icc] at h
    have hder : ∀ t : ℝ, deriv (fun t : ℝ => t⁻¹) t = -(t ^ 2)⁻¹ := fun t => deriv_inv
    simp_rw [hder] at h
    rw [intervalIntegral.integral_of_le hx]
    have hsum : ∀ k : ℕ, (k : ℝ)⁻¹ * vonMangoldt k = vonMangoldt k / k := fun k => by
      rw [div_eq_inv_mul]
    simp_rw [hsum] at h
    rw [h, sub_eq_add_neg, ← integral_neg, div_eq_inv_mul]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    simp only
    rw [div_eq_mul_inv]
    ring
  · apply ContinuousOn.integrableOn_Icc
    refine ContinuousOn.congr ?_ (fun t _ => deriv_inv)
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
    intro t ht
    have : (0 : ℝ) < t := by linarith [ht.1]
    exact pow_ne_zero 2 (ne_of_gt this)

/-- The relative prime error tends to zero: `(ψ(x) − x)/x → 0`. -/
theorem tendsto_chebyshevError_div :
    Tendsto (fun x : ℝ => chebyshevError x / x) atTop (𝓝 0) := by
  obtain ⟨c, hc, C, hC0, hC⟩ := chebyshevError_bound
  apply squeeze_zero_norm' (a := fun x : ℝ => C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))
  · filter_upwards [hC, eventually_ge_atTop 1] with x hx hx1
    have hx0 : 0 < x := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    calc |chebyshevError x| ≤ C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := hx
      _ = C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) * x := by ring
  · have h1 : Tendsto (fun x : ℝ => c * Real.log x ^ ((1 : ℝ) / 10)) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        Real.tendsto_log_atTop).const_mul_atTop hc
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := h2.const_mul C
    simp only [mul_zero] at h3
    refine h3.congr fun x => ?_
    simp only [Function.comp, neg_mul]

/-- **Mertens' theorem with the Euler constant**: `Σ_{n ≤ x} Λ(n)/n − log x → −γ`. -/
theorem tendsto_real_sum_vonMangoldt_div_sub_log :
    Tendsto (fun x : ℝ => (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / k) - Real.log x) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have key : ∀ x : ℝ, 1 ≤ x →
      (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt k / k) - Real.log x =
        1 + chebyshevError x / x + ∫ t in (1 : ℝ)..x, chebyshevError t / t ^ 2 := by
    intro x hx
    rw [sum_vonMangoldt_div_eq hx]
    have hx0 : 0 < x := by linarith
    have hint : IntervalIntegrable (fun t : ℝ => chebyshevError t / t ^ 2) volume 1 x := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
      exact integrableOn_chebyshevError_div_sq.mono_set Ioc_subset_Ioi_self
    have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 x := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_inv₀.mono
      intro t ht
      rw [uIcc_of_le hx] at ht
      exact Set.mem_compl_singleton_iff.mpr (ne_of_gt (by linarith [ht.1]))
    have hpsi : (fun t : ℝ => ψ t / t ^ 2) = fun t => t⁻¹ + chebyshevError t / t ^ 2 := by
      funext t
      unfold chebyshevError
      rcases eq_or_ne t 0 with rfl | ht
      · simp
      · field_simp
        ring
    rw [hpsi, intervalIntegral.integral_add hinv hint, integral_inv_of_pos one_pos hx0, div_one]
    unfold chebyshevError
    field_simp
    ring
  have hE := tendsto_chebyshevError_div
  have hI : Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, chebyshevError t / t ^ 2) atTop
      (𝓝 (∫ t in Ioi 1, chebyshevError t / t ^ 2)) :=
    intervalIntegral_tendsto_integral_Ioi 1 integrableOn_chebyshevError_div_sq tendsto_id
  rw [integral_chebyshevError_div_sq] at hI
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).add hE).add hI
  have : (1 : ℝ) + 0 + (-Real.eulerMascheroniConstant - 1) = -Real.eulerMascheroniConstant := by ring
  rw [this] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  exact (key x hx).symm

end

end RHTower
