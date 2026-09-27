import GaloisForLFunctions.RHTower.ThetaRenewalIncrement
import GaloisForLFunctions.HTGeometry.VolterraConvolutionAlgebra

/-!
# The logarithmic renewal kernel of the theta profile and its universal reflection

With the oriented Volterra convolution `(f ⋆ g)(t) = ∫₀^t f(t - s) g(s) ds`, the convolution powers
`ν^{⋆m}` of the renewal increment are defined on the whole real line, and
`Q(t) = Σ_{m≥1} ν^{⋆m}(t)/(m c^m)` converges locally uniformly (`|ν^{⋆m}(t)| ≤ C^m |t|^{m-1}/(m-1)!`).
It is positive for `t > 0` and, through the weighted powers `v^{⋆m} = e^{at} ν^{⋆m}/c^m ≤
a^m e^{-βt} t^{m-1}/(m-1)!` (`a = 1/4`, `β = π - 3/2`), satisfies
`0 < Q(t) ≤ e^{-βt}(1 - e^{-at})/t ≤ a e^{-βt}`, `∫₀^∞ e^{at} Q = Σ q^m/m = -log(1 - q) < 1/5`, and
`∫₀^∞ e^{-st} Q(t) dt = -log(1 - N(s)/c)`, i.e. `D(s) = c e^{-Q̂(s)}` on `Re s ≥ -a`.

Multiplication by `t` is a derivation of `⋆`, so `t ν^{⋆(m+1)} = (m+1)(τν) ⋆ ν^{⋆m}` and the
positive Volterra law `c t Q(t) = t ν(t) + (ν ⋆ τQ)(t)` holds.  Convolving it with `e^{a·}`, and
using `e^{a·} ⋆ ν = c e^{a·} - P` and `e^{a·} ⋆ τν = -τP + e^{a·} ⋆ P`, gives
`P ⋆ (τQ) = -τP + e^{a·} ⋆ P`; hence `y(t) = e^{-at} + t Q(t)` satisfies
`P ⋆ y = P ⋆ (2 cosh(a·)) - τP`, an equation invariant under `t ↦ -t` because `P` is even.  Since
`P = c e^{a·} - e^{a·} ⋆ ν`, uniqueness for the exponential kernel and for homogeneous Volterra
equations of the second kind forces `y` to be even.  This is the universal reflection
`Q(-t) + Q(t) = 2 sinh(at)/t`; consequently `Q(0) = a`, `W(t) = e^{-at}/t + Q(t)` is odd, the
negative branch `Q(-t)` is positive and `Q(-t) ~ e^{at}/t`.
-/
open Complex Filter Topology Set MeasureTheory HurwitzZeta
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## Convolution powers of the increment -/

/-- The convolution powers `ν^{⋆(m+1)}` of the renewal increment. -/
def thetaRenewalPower : ℕ → ℝ → ℝ
  | 0 => thetaRenewalIncrement
  | m + 1 => volterraConv thetaRenewalIncrement (thetaRenewalPower m)

theorem continuous_thetaRenewalPower (m : ℕ) : Continuous (thetaRenewalPower m) := by
  induction m with
  | zero => exact continuous_thetaRenewalIncrement
  | succ m ih => exact continuous_volterraConv continuous_thetaRenewalIncrement ih

theorem exists_bound_thetaRenewalIncrement (T : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s, |s| ≤ T → |thetaRenewalIncrement s| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_thetaRenewalIncrement.continuousOn (s := Icc (-T) T))
  refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
  have := hC s ⟨(abs_le.mp hs).1, (abs_le.mp hs).2⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- `|ν^{⋆(m+1)}(t)| ≤ C^{m+1} |t|^m / m!` whenever `|ν| ≤ C` on `[-T, T]` and `|t| ≤ T`. -/
theorem abs_thetaRenewalPower_le {T C : ℝ}
    (hC : ∀ s, |s| ≤ T → |thetaRenewalIncrement s| ≤ C) (m : ℕ) {t : ℝ} (ht : |t| ≤ T) :
    |thetaRenewalPower m t| ≤ C ^ (m + 1) * |t| ^ m / m.factorial := by
  induction m generalizing t with
  | zero => simpa [thetaRenewalPower] using hC t ht
  | succ m ih =>
    have h := abs_volterraConv_le (f := thetaRenewalIncrement) (g := thetaRenewalPower m)
      (A := C) (B := C ^ (m + 1)) (n := m) (fun s hs => hC s (hs.trans ht))
      (fun s hs => ih (hs.trans ht))
    simp only [thetaRenewalPower]
    exact h.trans (le_of_eq (by ring))

theorem thetaRenewalPower_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < thetaRenewalPower m t := by
  induction m generalizing t with
  | zero => exact thetaRenewalIncrement_pos t
  | succ m ih =>
    simp only [thetaRenewalPower, volterraConv]
    refine intervalIntegral.integral_pos ht ((by
      have := continuous_thetaRenewalPower m
      have := continuous_thetaRenewalIncrement
      fun_prop : Continuous fun s => thetaRenewalIncrement (t - s) * thetaRenewalPower m s)
        |>.continuousOn) (fun s hs => (mul_pos (thetaRenewalIncrement_pos _) (ih hs.1)).le)
      ⟨t, ⟨ht.le, le_rfl⟩, mul_pos (thetaRenewalIncrement_pos _) (ih ht)⟩

/-! ## The logarithmic renewal kernel -/

/-- The logarithmic renewal kernel `Q(t) = Σ_{m≥1} ν^{⋆m}(t)/(m c^m)`, defined on the whole real
line through oriented convolutions. -/
def thetaRenewalLogKernel (t : ℝ) : ℝ :=
  ∑' m : ℕ, thetaRenewalPower m t / ((m + 1) * Θ 1 ^ (m + 1))

theorem abs_thetaRenewalLogKernel_term_le {T C : ℝ}
    (hC : ∀ s, |s| ≤ T → |thetaRenewalIncrement s| ≤ C) (m : ℕ) {t : ℝ} (ht : |t| ≤ T) :
    |thetaRenewalPower m t / ((m + 1) * Θ 1 ^ (m + 1))| ≤
      C / Θ 1 * ((C / Θ 1 * T) ^ m / m.factorial) := by
  have hc := thetaSeam_pos
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 (by simpa using (abs_nonneg t).trans ht))
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) + 1) * Θ 1 ^ (m + 1))]
  have h1 := abs_thetaRenewalPower_le hC m ht
  have h2 : |t| ^ m ≤ T ^ m := pow_le_pow_left₀ (abs_nonneg t) ht m
  rw [div_le_iff₀ (by positivity)]
  calc |thetaRenewalPower m t| ≤ C ^ (m + 1) * |t| ^ m / m.factorial := h1
    _ ≤ C ^ (m + 1) * T ^ m / m.factorial := by gcongr
    _ ≤ C / Θ 1 * ((C / Θ 1 * T) ^ m / m.factorial) * (((m : ℝ) + 1) * Θ 1 ^ (m + 1)) := by
        rw [mul_pow, div_pow]
        have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
        have e : C / Θ 1 * (C ^ m / Θ 1 ^ m * T ^ m / m.factorial) * (((m : ℝ) + 1) * Θ 1 ^ (m + 1)) =
            ((m : ℝ) + 1) * (C ^ (m + 1) * T ^ m / m.factorial) := by
          field_simp; ring
        rw [e]
        have : 0 ≤ C ^ (m + 1) * T ^ m / m.factorial := by positivity
        nlinarith

theorem summable_thetaRenewalLogKernel_bound (C T : ℝ) :
    Summable fun m : ℕ => C / Θ 1 * ((C / Θ 1 * T) ^ m / m.factorial) :=
  (Real.summable_pow_div_factorial _).mul_left _

theorem summable_thetaRenewalLogKernel_terms (t : ℝ) :
    Summable fun m : ℕ => thetaRenewalPower m t / ((m + 1) * Θ 1 ^ (m + 1)) := by
  obtain ⟨C, _, hC⟩ := exists_bound_thetaRenewalIncrement |t|
  exact Summable.of_norm_bounded (summable_thetaRenewalLogKernel_bound C |t|) fun m => by
    rw [Real.norm_eq_abs]; exact abs_thetaRenewalLogKernel_term_le hC m le_rfl

theorem continuous_thetaRenewalLogKernel : Continuous thetaRenewalLogKernel := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  set T := |t| + 1
  obtain ⟨C, _, hC⟩ := exists_bound_thetaRenewalIncrement T
  have hon : ContinuousOn thetaRenewalLogKernel (Icc (-T) T) :=
    continuousOn_tsum (fun m => ((continuous_thetaRenewalPower m).div_const _).continuousOn)
      (summable_thetaRenewalLogKernel_bound C T) fun m s hs => by
        rw [Real.norm_eq_abs]
        exact abs_thetaRenewalLogKernel_term_le hC m (abs_le.mpr ⟨hs.1, hs.2⟩)
  refine hon.continuousAt (Icc_mem_nhds ?_ ?_)
  · linarith [neg_abs_le t]
  · linarith [le_abs_self t]

theorem thetaRenewalLogKernel_pos {t : ℝ} (ht : 0 < t) : 0 < thetaRenewalLogKernel t := by
  have hc := thetaSeam_pos
  exact (summable_thetaRenewalLogKernel_terms t).tsum_pos
    (fun m => div_nonneg (thetaRenewalPower_pos m ht).le (by positivity)) 0
    (div_pos (thetaRenewalPower_pos 0 ht) (by positivity))

/-! ## The weighted powers and the kernel bound -/

/-- The weighted powers `v^{⋆(m+1)} = e^{at} ν^{⋆(m+1)}/c^{m+1}`. -/
def thetaRenewalDensityPower (m : ℕ) (t : ℝ) : ℝ :=
  Real.exp (t / 4) * thetaRenewalPower m t / Θ 1 ^ (m + 1)

theorem thetaRenewalDensityPower_zero (t : ℝ) :
    thetaRenewalDensityPower 0 t = thetaRenewalDensity t := by
  simp [thetaRenewalDensityPower, thetaRenewalDensity, thetaRenewalPower]

theorem thetaRenewalDensityPower_succ (m : ℕ) (t : ℝ) :
    thetaRenewalDensityPower (m + 1) t =
      volterraConv thetaRenewalDensity (thetaRenewalDensityPower m) t := by
  have hc := thetaSeam_pos
  simp only [thetaRenewalDensityPower, thetaRenewalPower, volterraConv, thetaRenewalDensity]
  rw [mul_div_assoc, ← intervalIntegral.integral_div, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have e : Real.exp (t / 4) = Real.exp ((t - s) / 4) * Real.exp (s / 4) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  field_simp
  ring

theorem continuous_thetaRenewalDensityPower (m : ℕ) : Continuous (thetaRenewalDensityPower m) := by
  have := continuous_thetaRenewalPower m
  unfold thetaRenewalDensityPower
  fun_prop

/-- `0 ≤ v^{⋆(m+1)}(t) ≤ a^{m+1} e^{-βt} t^m/m!` for `t ≥ 0` (`a = 1/4`, `β = π - 3/2`). -/
theorem thetaRenewalDensityPower_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ thetaRenewalDensityPower m t ∧ thetaRenewalDensityPower m t ≤
      (1 / 4) ^ (m + 1) * Real.exp (-((Real.pi - 3 / 2) * t)) * t ^ m / m.factorial := by
  have hc := thetaSeam_pos
  induction m generalizing t with
  | zero =>
    rw [thetaRenewalDensityPower_zero]
    refine ⟨(thetaRenewalDensity_pos t).le, ?_⟩
    simpa using thetaRenewalDensity_le ht
  | succ m ih =>
    rw [thetaRenewalDensityPower_succ, volterraConv]
    constructor
    · refine intervalIntegral.integral_nonneg ht fun s hs => ?_
      exact mul_nonneg (thetaRenewalDensity_pos _).le (ih hs.1).1
    · have hmono := intervalIntegral.integral_mono_on (μ := volume) ht
        (((continuous_thetaRenewalDensity.comp (continuous_const.sub continuous_id)).mul
          (continuous_thetaRenewalDensityPower m)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun s : ℝ => (1 / 4 : ℝ) ^ (m + 2) *
          Real.exp (-((Real.pi - 3 / 2) * t)) * s ^ m / m.factorial).intervalIntegrable 0 t)
        (fun s hs => by
          have h1 := thetaRenewalDensity_le (show 0 ≤ t - s by linarith [hs.2])
          have h2 := (ih hs.1).2
          have h3 := (ih hs.1).1
          calc thetaRenewalDensity (t - s) * thetaRenewalDensityPower m s
              ≤ (1 / 4 * Real.exp (-((Real.pi - 3 / 2) * (t - s)))) *
                ((1 / 4) ^ (m + 1) * Real.exp (-((Real.pi - 3 / 2) * s)) * s ^ m / m.factorial) :=
                mul_le_mul h1 h2 h3 (by positivity)
            _ = (1 / 4 : ℝ) ^ (m + 2) * Real.exp (-((Real.pi - 3 / 2) * t)) * s ^ m /
                m.factorial := by
                rw [show -((Real.pi - 3 / 2) * t) = -((Real.pi - 3 / 2) * (t - s)) +
                  -((Real.pi - 3 / 2) * s) by ring, Real.exp_add]
                ring)
      refine hmono.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow,
        Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-- `Q(t) = e^{-t/4} Σ_{m≥0} v^{⋆(m+1)}(t)/(m+1)`. -/
theorem thetaRenewalLogKernel_eq_density (t : ℝ) :
    thetaRenewalLogKernel t =
      Real.exp (-(t / 4)) * ∑' m : ℕ, thetaRenewalDensityPower m t / (m + 1) := by
  rw [thetaRenewalLogKernel, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hc := thetaSeam_pos
  rw [thetaRenewalDensityPower, Real.exp_neg]
  field_simp

/-- **The kernel bound (2).** `0 < Q(t) ≤ e^{-βt}(1 - e^{-at})/t ≤ a e^{-βt}` for `t > 0`. -/
theorem thetaRenewalLogKernel_le {t : ℝ} (ht : 0 < t) :
    thetaRenewalLogKernel t ≤
      Real.exp (-((Real.pi - 3 / 2) * t)) * (1 - Real.exp (-(t / 4))) / t := by
  have hsum : HasSum (fun m : ℕ => (1 / 4) ^ (m + 1) * Real.exp (-((Real.pi - 3 / 2) * t)) *
      t ^ m / m.factorial / (m + 1))
      (Real.exp (-((Real.pi - 3 / 2) * t)) * (Real.exp (t / 4) - 1) / t) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (t / 4)
    rw [← Real.exp_eq_exp_ℝ] at h
    have h2 := (hasSum_nat_add_iff' 1).mpr h
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, Finset.range_one,
      Finset.sum_singleton] at h2
    have h3 := (h2.mul_left (Real.exp (-((Real.pi - 3 / 2) * t)) / t))
    rw [show Real.exp (-((Real.pi - 3 / 2) * t)) * (Real.exp (t / 4) - 1) / t =
      Real.exp (-((Real.pi - 3 / 2) * t)) / t * (Real.exp (t / 4) - 1) by ring]
    refine h3.congr_fun fun m => ?_
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have hle : ∀ m : ℕ, thetaRenewalDensityPower m t / (m + 1) ≤
      (1 / 4) ^ (m + 1) * Real.exp (-((Real.pi - 3 / 2) * t)) * t ^ m / m.factorial / (m + 1) :=
    fun m => div_le_div_of_nonneg_right (thetaRenewalDensityPower_le m ht.le).2 (by positivity)
  have hsd : Summable fun m : ℕ => thetaRenewalDensityPower m t / (m + 1) :=
    Summable.of_nonneg_of_le (fun m => div_nonneg (thetaRenewalDensityPower_le m ht.le).1
      (by positivity)) hle hsum.summable
  rw [thetaRenewalLogKernel_eq_density]
  calc Real.exp (-(t / 4)) * ∑' m : ℕ, thetaRenewalDensityPower m t / (m + 1)
      ≤ Real.exp (-(t / 4)) *
        (Real.exp (-((Real.pi - 3 / 2) * t)) * (Real.exp (t / 4) - 1) / t) :=
        mul_le_mul_of_nonneg_left (hsd.tsum_le_tsum hle hsum.summable |>.trans
          (le_of_eq hsum.tsum_eq)) (Real.exp_pos _).le
    _ = _ := by
        have e1 : Real.exp (-(t / 4)) * Real.exp (t / 4) = 1 := by rw [← Real.exp_add]; simp
        calc Real.exp (-(t / 4)) * (Real.exp (-((Real.pi - 3 / 2) * t)) * (Real.exp (t / 4) - 1) / t)
            = Real.exp (-((Real.pi - 3 / 2) * t)) / t *
              (Real.exp (-(t / 4)) * Real.exp (t / 4) - Real.exp (-(t / 4))) := by ring
          _ = _ := by rw [e1]; ring

theorem thetaRenewalLogKernel_le_quarter {t : ℝ} (ht : 0 < t) :
    thetaRenewalLogKernel t ≤ 1 / 4 * Real.exp (-((Real.pi - 3 / 2) * t)) := by
  refine (thetaRenewalLogKernel_le ht).trans ?_
  have h1 : 1 - Real.exp (-(t / 4)) ≤ t / 4 := by
    have := Real.add_one_le_exp (-(t / 4)); linarith
  rw [div_le_iff₀ ht]
  have := Real.exp_pos (-((Real.pi - 3 / 2) * t))
  nlinarith

/-! ## Masses and the Laplace transform of the kernel -/

theorem pow_div_factorial_mul_exp_neg_le {β : ℝ} (hβ : 0 < β) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(β * t)) * t ^ m / m.factorial ≤ (2 / β) ^ m * Real.exp (-(β / 2 * t)) := by
  have h := Real.pow_div_factorial_le_exp (β / 2 * t) (by positivity) m
  have e : Real.exp (-(β / 2 * t)) = Real.exp (β / 2 * t) * Real.exp (-(β * t)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hpos := Real.exp_pos (-(β * t))
  have key : t ^ m / m.factorial ≤ (2 / β) ^ m * Real.exp (β / 2 * t) := by
    rw [mul_pow, div_pow] at h
    calc t ^ m / m.factorial = (2 / β) ^ m * ((β / 2) ^ m * t ^ m / m.factorial) := by
          rw [div_pow, div_pow]; field_simp
      _ ≤ (2 / β) ^ m * Real.exp (β / 2 * t) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_pow]; exact h
  calc Real.exp (-(β * t)) * t ^ m / m.factorial = Real.exp (-(β * t)) * (t ^ m / m.factorial) := by
        ring
    _ ≤ Real.exp (-(β * t)) * ((2 / β) ^ m * Real.exp (β / 2 * t)) :=
        mul_le_mul_of_nonneg_left key hpos.le
    _ = _ := by ring

theorem integrableOn_thetaRenewalDensityPower (m : ℕ) :
    IntegrableOn (thetaRenewalDensityPower m) (Ioi 0) := by
  have hβ : 0 < Real.pi - 3 / 2 := by linarith [Real.pi_gt_three]
  have hdom : IntegrableOn (fun t : ℝ => (1 / 4) ^ (m + 1) * ((2 / (Real.pi - 3 / 2)) ^ m *
      Real.exp ((-((Real.pi - 3 / 2) / 2)) * t))) (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _).const_mul _
  refine hdom.mono' (continuous_thetaRenewalDensityPower m).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  obtain ⟨h0, h1⟩ := thetaRenewalDensityPower_le m ht0
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  refine h1.trans ?_
  have := pow_div_factorial_mul_exp_neg_le hβ m ht0
  rw [mul_assoc, mul_div_assoc, neg_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact this

/-- Real Laplace product at `s = 0`: `∫₀^∞ (f ⋆ g) = (∫₀^∞ f)(∫₀^∞ g)`. -/
theorem integral_Ioi_volterraConv {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfi : IntegrableOn (fun t => |f t|) (Ioi 0)) (hgi : IntegrableOn (fun t => |g t|) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), volterraConv f g t) = (∫ t in Ioi (0 : ℝ), f t) * ∫ t in Ioi (0 : ℝ), g t := by
  have h := integral_Ioi_cexp_mul_volterraConv hf hg (s := 0)
    (by simpa using hfi) (by simpa using hgi)
  simp only [zero_mul, neg_zero, Complex.exp_zero, one_mul, integral_complex_ofReal] at h
  exact_mod_cast h

/-- `∫₀^∞ v^{⋆(m+1)} = q^{m+1}`. -/
theorem integral_thetaRenewalDensityPower (m : ℕ) :
    (∫ t in Ioi (0 : ℝ), thetaRenewalDensityPower m t) = thetaRenewalMass ^ (m + 1) := by
  induction m with
  | zero =>
    simp only [thetaRenewalDensityPower_zero, zero_add, pow_one, thetaRenewalMass]
  | succ m ih =>
    simp only [thetaRenewalDensityPower_succ]
    rw [integral_Ioi_volterraConv continuous_thetaRenewalDensity
      (continuous_thetaRenewalDensityPower m)
      (integrableOn_thetaRenewalDensity.abs) (integrableOn_thetaRenewalDensityPower m).abs,
      ih, ← thetaRenewalMass, pow_succ]
    ring

/-- `∫₀^∞ e^{at} Q(t) dt = Σ q^m/m = -log(1 - q)`. -/
theorem integral_exp_mul_thetaRenewalLogKernel :
    (∫ t in Ioi (0 : ℝ), Real.exp (t / 4) * thetaRenewalLogKernel t) =
      -Real.log (1 - thetaRenewalMass) := by
  have hq0 := thetaRenewalMass_pos
  have hq1 := thetaRenewalMass_lt
  have hfun : ∀ t, Real.exp (t / 4) * thetaRenewalLogKernel t =
      ∑' m : ℕ, thetaRenewalDensityPower m t / (m + 1) := by
    intro t
    rw [thetaRenewalLogKernel_eq_density, ← mul_assoc, ← Real.exp_add]; simp
  simp_rw [hfun]
  have hint : ∀ m : ℕ, Integrable (fun t => thetaRenewalDensityPower m t / (m + 1))
      (volume.restrict (Ioi 0)) := fun m =>
    (integrableOn_thetaRenewalDensityPower m).div_const _
  have hnorm : ∀ m : ℕ, (∫ t in Ioi (0 : ℝ), ‖thetaRenewalDensityPower m t / (m + 1)‖) =
      thetaRenewalMass ^ (m + 1) / (m + 1) := by
    intro m
    rw [← integral_thetaRenewalDensityPower, ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (thetaRenewalDensityPower_le m
      (le_of_lt ht)).1 (by positivity))]
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (x := thetaRenewalMass)
    (by rw [abs_of_pos hq0]; linarith)
  rw [← integral_tsum_of_summable_integral_norm hint (by simp_rw [hnorm]; exact hlog.summable)]
  rw [← hlog.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [integral_div, integral_thetaRenewalDensityPower]

theorem neg_log_one_sub_thetaRenewalMass_lt : -Real.log (1 - thetaRenewalMass) < 1 / 5 := by
  have hq0 := thetaRenewalMass_pos
  have hq1 := thetaRenewalMass_lt
  have h1 : 0 < 1 - thetaRenewalMass := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos h1
  have hinv : (1 - thetaRenewalMass)⁻¹ < 6 / 5 := by
    rw [inv_lt_comm₀ h1 (by norm_num)]; norm_num; linarith
  linarith

theorem thetaRenewalPower_eq_density (m : ℕ) (t : ℝ) :
    thetaRenewalPower m t = Θ 1 ^ (m + 1) * Real.exp (-(t / 4)) * thetaRenewalDensityPower m t := by
  have hc := thetaSeam_pos
  rw [thetaRenewalDensityPower, Real.exp_neg]
  field_simp

theorem integrableOn_exp_mul_abs_thetaRenewalPower {σ : ℝ} (hσ : σ ≤ 1 / 4) (m : ℕ) :
    IntegrableOn (fun t => Real.exp (σ * t) * |thetaRenewalPower m t|) (Ioi 0) := by
  have hc := thetaSeam_pos
  refine ((integrableOn_thetaRenewalDensityPower m).const_mul (Θ 1 ^ (m + 1))).mono'
    ((by have := continuous_thetaRenewalPower m; fun_prop : Continuous fun t =>
      Real.exp (σ * t) * |thetaRenewalPower m t|).aestronglyMeasurable.restrict) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos (thetaRenewalPower_pos m ht0),
    thetaRenewalPower_eq_density]
  have h1 : Real.exp (σ * t) * Real.exp (-(t / 4)) ≤ 1 := by
    rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by nlinarith)
  have h2 := (thetaRenewalDensityPower_le m ht0.le).1
  calc Real.exp (σ * t) * (Θ 1 ^ (m + 1) * Real.exp (-(t / 4)) * thetaRenewalDensityPower m t)
      = Θ 1 ^ (m + 1) * thetaRenewalDensityPower m t * (Real.exp (σ * t) * Real.exp (-(t / 4))) := by
        ring
    _ ≤ Θ 1 ^ (m + 1) * thetaRenewalDensityPower m t * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- `∫₀^∞ e^{-st} ν^{⋆(m+1)}(t) dt = N(s)^{m+1}` on `Re s ≥ -1/4`. -/
theorem integral_cexp_mul_thetaRenewalPower {s : ℂ} (hs : -(1 / 4) ≤ s.re) (m : ℕ) :
    (∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (thetaRenewalPower m t : ℂ)) =
      thetaRenewalLaplace s ^ (m + 1) := by
  induction m with
  | zero => simp [thetaRenewalPower, thetaRenewalLaplace]
  | succ m ih =>
    have hνi : IntegrableOn (fun t => Real.exp (-(s.re * t)) * |thetaRenewalIncrement t|) (Ioi 0) := by
      obtain ⟨C, _, hC⟩ := thetaRenewalIncrement_superexp (-s.re)
      refine ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul C).mono'
        ((by have := continuous_thetaRenewalIncrement; fun_prop : Continuous fun t =>
          Real.exp (-(s.re * t)) * |thetaRenewalIncrement t|).aestronglyMeasurable.restrict) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_one_mul]
      have := hC t (le_of_lt ht)
      rwa [neg_mul] at this
    have hAi : IntegrableOn (fun t => Real.exp (-(s.re * t)) * |thetaRenewalPower m t|) (Ioi 0) := by
      have := integrableOn_exp_mul_abs_thetaRenewalPower (σ := -s.re) (by linarith) m
      simpa [neg_mul] using this
    simp only [thetaRenewalPower]
    rw [integral_Ioi_cexp_mul_volterraConv continuous_thetaRenewalIncrement
      (continuous_thetaRenewalPower m) hνi hAi, ih, ← thetaRenewalLaplace, pow_succ]
    ring

/-- The Laplace transform `Q̂(s) = ∫₀^∞ e^{-st} Q(t) dt`. -/
def thetaRenewalLogKernelLaplace (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (thetaRenewalLogKernel t : ℂ)

theorem norm_thetaRenewalLaplace_div_lt {s : ℂ} (hs : -(1 / 4) ≤ s.re) :
    ‖thetaRenewalLaplace s / (Θ 1 : ℂ)‖ < 1 := by
  have hc := thetaSeam_pos
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, div_lt_one hc]
  have := norm_thetaRenewalLaplace_le hs
  have hq := thetaRenewalMass_lt
  nlinarith

/-- **The logarithmic renewal identity (7).** On `Re s ≥ -1/4`,
`Q̂(s) = Σ_{m≥1} (N(s)/c)^m/m = -log(1 - N(s)/c)`. -/
theorem thetaRenewalLogKernelLaplace_eq {s : ℂ} (hs : -(1 / 4) ≤ s.re) :
    thetaRenewalLogKernelLaplace s = -Complex.log (1 - thetaRenewalLaplace s / (Θ 1 : ℂ)) := by
  have hc := thetaSeam_pos
  have hcC : ((Θ 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hq0 := thetaRenewalMass_pos
  have hq1 := thetaRenewalMass_lt
  set F : ℕ → ℝ → ℂ := fun m t =>
    cexp (-(s * t)) * ((thetaRenewalPower m t / ((m + 1) * Θ 1 ^ (m + 1)) : ℝ) : ℂ)
  have hnormF : ∀ m t, ‖F m t‖ = Real.exp (-(s.re * t)) * |thetaRenewalPower m t| /
      ((m + 1) * Θ 1 ^ (m + 1)) := by
    intro m t
    simp only [F]
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) + 1) * Θ 1 ^ (m + 1))]
    have hre : (-(s * (t : ℂ))).re = -(s.re * t) := by simp
    rw [hre]; ring
  have hFi : ∀ m, Integrable (F m) (volume.restrict (Ioi 0)) := by
    intro m
    have h := (integrableOn_exp_mul_abs_thetaRenewalPower (σ := -s.re) (by linarith) m).div_const
      (((m : ℝ) + 1) * Θ 1 ^ (m + 1))
    refine h.mono' ((by have := continuous_thetaRenewalPower m; fun_prop : Continuous (F m))
      |>.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [hnormF, neg_mul]
  have hFle : ∀ m, (∫ t in Ioi (0 : ℝ), ‖F m t‖) ≤ thetaRenewalMass ^ (m + 1) / (m + 1) := by
    intro m
    rw [← integral_thetaRenewalDensityPower, ← integral_div]
    refine setIntegral_mono_on (hFi m).norm ((integrableOn_thetaRenewalDensityPower m).div_const _)
      measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    rw [hnormF, abs_of_pos (thetaRenewalPower_pos m ht0), thetaRenewalPower_eq_density]
    have h1 : Real.exp (-(s.re * t)) * Real.exp (-(t / 4)) ≤ 1 := by
      rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 := (thetaRenewalDensityPower_le m ht0.le).1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc Real.exp (-(s.re * t)) * (Θ 1 ^ (m + 1) * Real.exp (-(t / 4)) *
          thetaRenewalDensityPower m t) * ((m : ℝ) + 1)
        = (Real.exp (-(s.re * t)) * Real.exp (-(t / 4))) *
          (thetaRenewalDensityPower m t * ((m + 1) * Θ 1 ^ (m + 1))) := by ring
      _ ≤ 1 * (thetaRenewalDensityPower m t * ((m + 1) * Θ 1 ^ (m + 1))) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (x := thetaRenewalMass)
    (by rw [abs_of_pos hq0]; linarith)
  have hsumm : Summable fun m => ∫ t in Ioi (0 : ℝ), ‖F m t‖ :=
    Summable.of_nonneg_of_le (fun m => integral_nonneg fun t => norm_nonneg _) hFle hlog.summable
  have hpt : ∀ t : ℝ, cexp (-(s * t)) * (thetaRenewalLogKernel t : ℂ) = ∑' m, F m t := by
    intro t
    rw [thetaRenewalLogKernel, Complex.ofReal_tsum, ← tsum_mul_left]
  have hFint : ∀ m, (∫ t in Ioi (0 : ℝ), F m t) =
      thetaRenewalLaplace s ^ (m + 1) / (((m : ℂ) + 1) * (Θ 1 : ℂ) ^ (m + 1)) := by
    intro m
    rw [← integral_cexp_mul_thetaRenewalPower hs m, div_eq_mul_inv, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show F m t = cexp (-(s * t)) *
      ((thetaRenewalPower m t / ((m + 1) * Θ 1 ^ (m + 1)) : ℝ) : ℂ) from rfl]
    push_cast
    field_simp
  rw [thetaRenewalLogKernelLaplace]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hFi hsumm]
  simp_rw [hFint]
  -- the logarithmic series
  have hz := norm_thetaRenewalLaplace_div_lt hs
  have hser := Complex.hasSum_taylorSeries_neg_log hz
  have hser1 := (hasSum_nat_add_iff' 1).mpr hser
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
    sub_zero] at hser1
  rw [← hser1.tsum_eq]
  refine tsum_congr fun m => ?_
  push_cast
  rw [div_pow]
  field_simp

/-- `D(s) = c exp(-Q̂(s))` on `Re s ≥ -1/4`. -/
theorem thetaRenewalDenominator_eq_exp {s : ℂ} (hs : -(1 / 4) ≤ s.re) :
    thetaRenewalDenominator s = (Θ 1 : ℂ) * cexp (-thetaRenewalLogKernelLaplace s) := by
  have hc := thetaSeam_pos
  have hcC : ((Θ 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hz := norm_thetaRenewalLaplace_div_lt hs
  have hne : 1 - thetaRenewalLaplace s / (Θ 1 : ℂ) ≠ 0 := by
    intro h
    have : thetaRenewalLaplace s / (Θ 1 : ℂ) = 1 := by linear_combination -h
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  rw [thetaRenewalLogKernelLaplace_eq hs, neg_neg, Complex.exp_log hne, thetaRenewalDenominator]
  field_simp

/-! ## The positive Volterra law -/

/-- The moment-weighted increment `(τν)(s) = s ν(s)`. -/
def thetaRenewalMomentIncrement (s : ℝ) : ℝ := s * thetaRenewalIncrement s

theorem continuous_thetaRenewalMomentIncrement : Continuous thetaRenewalMomentIncrement := by
  have := continuous_thetaRenewalIncrement
  unfold thetaRenewalMomentIncrement; fun_prop

/-- `t ν^{⋆(m+2)}(t) = (m+2) ((τν) ⋆ ν^{⋆(m+1)})(t)`. -/
theorem mul_thetaRenewalPower_succ (m : ℕ) (t : ℝ) :
    t * thetaRenewalPower (m + 1) t =
      (m + 2) * volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m) t := by
  have hν := continuous_thetaRenewalIncrement
  have hτ := continuous_thetaRenewalMomentIncrement
  induction m generalizing t with
  | zero =>
    have hτdef : (fun s => s * thetaRenewalIncrement s) = thetaRenewalMomentIncrement := rfl
    simp only [thetaRenewalPower]
    rw [mul_volterraConv hν hν, hτdef, volterraConv_comm thetaRenewalIncrement
      thetaRenewalMomentIncrement]
    push_cast; ring
  | succ m ih =>
    have hA := continuous_thetaRenewalPower m
    have hA1 := continuous_thetaRenewalPower (m + 1)
    have hfun : (fun s => s * thetaRenewalPower (m + 1) s) =
        fun s => ((m : ℝ) + 2) * volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m) s :=
      funext ih
    have hassoc : volterraConv thetaRenewalIncrement
        (volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m)) t =
        volterraConv thetaRenewalMomentIncrement (thetaRenewalPower (m + 1)) t := by
      rw [← volterraConv_assoc hν hτ hA, volterraConv_comm' thetaRenewalIncrement
        thetaRenewalMomentIncrement, volterraConv_assoc hτ hν hA]
      rfl
    conv_lhs => rw [show thetaRenewalPower (m + 1 + 1) = volterraConv thetaRenewalIncrement
      (thetaRenewalPower (m + 1)) from rfl]
    have hτdef : (fun s => s * thetaRenewalIncrement s) = thetaRenewalMomentIncrement := rfl
    rw [mul_volterraConv hν hA1, hfun, hτdef, volterraConv_smul_right, hassoc]
    push_cast; ring

/-- The series `S(t) = Σ_{m≥0} ((τν) ⋆ ν^{⋆(m+1)})(t)/c^{m+2}`. -/
def thetaRenewalMomentSeries (t : ℝ) : ℝ :=
  ∑' m : ℕ, volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m) t / Θ 1 ^ (m + 2)

theorem thetaRenewalMomentSeries_term_eq (m : ℕ) (t : ℝ) :
    volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m) t / Θ 1 ^ (m + 2) =
      t * (thetaRenewalPower (m + 1) t / ((((m + 1 : ℕ) : ℝ) + 1) * Θ 1 ^ (m + 1 + 1))) := by
  have hc := thetaSeam_pos
  have h := mul_thetaRenewalPower_succ m t
  have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
  rw [mul_div_assoc', h]
  push_cast
  rw [show (m : ℝ) + 1 + 1 = m + 2 by ring, show m + 1 + 1 = m + 2 by ring]
  field_simp

theorem mul_thetaRenewalLogKernel_eq (t : ℝ) :
    t * thetaRenewalLogKernel t = t * thetaRenewalIncrement t / Θ 1 + thetaRenewalMomentSeries t := by
  have hsum := (summable_thetaRenewalLogKernel_terms t).mul_left t
  rw [thetaRenewalLogKernel, ← tsum_mul_left, hsum.tsum_eq_zero_add, thetaRenewalMomentSeries]
  congr 1
  · simp [thetaRenewalPower]; ring
  · refine tsum_congr fun m => ?_
    rw [thetaRenewalMomentSeries_term_eq]

theorem abs_thetaRenewalMomentSeries_term_le {T C : ℝ}
    (hC : ∀ s, |s| ≤ T → |thetaRenewalIncrement s| ≤ C) (m : ℕ) {s : ℝ} (hs : |s| ≤ T) :
    |volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m) s / Θ 1 ^ (m + 2)| ≤
      T * (C / Θ 1 * ((C / Θ 1 * T) ^ (m + 1) / (m + 1).factorial)) := by
  rw [thetaRenewalMomentSeries_term_eq, abs_mul]
  exact mul_le_mul hs (abs_thetaRenewalLogKernel_term_le hC (m + 1) hs) (abs_nonneg _)
    ((abs_nonneg _).trans hs)

theorem continuous_thetaRenewalMomentSeries : Continuous thetaRenewalMomentSeries := by
  have h : thetaRenewalMomentSeries = fun t =>
      t * thetaRenewalLogKernel t - t * thetaRenewalIncrement t / Θ 1 := by
    funext t; rw [mul_thetaRenewalLogKernel_eq]; ring
  rw [h]
  have := continuous_thetaRenewalLogKernel
  have := continuous_thetaRenewalIncrement
  fun_prop

/-- **The positive Volterra law (3a).** `c t Q(t) = t ν(t) + ∫₀^t ν(s)(t - s) Q(t - s) ds`. -/
theorem thetaRenewal_volterra_law (t : ℝ) :
    Θ 1 * (t * thetaRenewalLogKernel t) = t * thetaRenewalIncrement t +
      volterraConv thetaRenewalIncrement (fun s => s * thetaRenewalLogKernel s) t := by
  have hc := thetaSeam_pos
  have hν := continuous_thetaRenewalIncrement
  have hτ := continuous_thetaRenewalMomentIncrement
  have hS := continuous_thetaRenewalMomentSeries
  have hfun : (fun s => s * thetaRenewalLogKernel s) =
      (fun s => (1 / Θ 1) * thetaRenewalMomentIncrement s) + thetaRenewalMomentSeries := by
    funext s; simp only [Pi.add_apply, thetaRenewalMomentIncrement]
    rw [mul_thetaRenewalLogKernel_eq]; ring
  obtain ⟨C, _, hC⟩ := exists_bound_thetaRenewalIncrement |t|
  have hconvS : volterraConv thetaRenewalIncrement thetaRenewalMomentSeries t =
      ∑' m : ℕ, volterraConv thetaRenewalMomentIncrement (thetaRenewalPower (m + 1)) t /
        Θ 1 ^ (m + 2) := by
    rw [show thetaRenewalMomentSeries = fun s => ∑' m : ℕ,
      volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m) s / Θ 1 ^ (m + 2) from rfl,
      volterraConv_tsum hν (fun m => (continuous_volterraConv hτ
        (continuous_thetaRenewalPower m)).div_const _)
        (summable_thetaRenewalLogKernel_bound C |t| |>.comp_injective (add_left_injective 1)
          |>.mul_left |t|)
        (fun m s hs => abs_thetaRenewalMomentSeries_term_le hC m hs)]
    refine tsum_congr fun m => ?_
    have := volterraConv_smul_right (1 / Θ 1 ^ (m + 2)) thetaRenewalIncrement
      (volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m)) t
    simp only [one_div_mul_eq_div] at this
    rw [show (fun s => volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m) s /
      Θ 1 ^ (m + 2)) = fun s => 1 / Θ 1 ^ (m + 2) *
        volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m) s by funext s; ring,
      volterraConv_smul_right, ← volterraConv_assoc hν hτ (continuous_thetaRenewalPower m),
      volterraConv_comm' thetaRenewalIncrement thetaRenewalMomentIncrement,
      volterraConv_assoc hτ hν (continuous_thetaRenewalPower m)]
    simp only [thetaRenewalPower]
    ring
  have hcS : Θ 1 * thetaRenewalMomentSeries t =
      volterraConv thetaRenewalMomentIncrement thetaRenewalIncrement t / Θ 1 +
        ∑' m : ℕ, volterraConv thetaRenewalMomentIncrement (thetaRenewalPower (m + 1)) t /
          Θ 1 ^ (m + 2) := by
    have hsumm : Summable fun m : ℕ =>
        volterraConv thetaRenewalMomentIncrement (thetaRenewalPower m) t / Θ 1 ^ (m + 2) := by
      refine Summable.of_norm_bounded ((summable_thetaRenewalLogKernel_bound C |t|
        |>.comp_injective (add_left_injective 1)).mul_left |t|) fun m => ?_
      rw [Real.norm_eq_abs]
      exact abs_thetaRenewalMomentSeries_term_le hC m le_rfl
    rw [thetaRenewalMomentSeries, ← tsum_mul_left, (hsumm.mul_left _).tsum_eq_zero_add]
    congr 1
    · simp only [thetaRenewalPower]; field_simp; ring
    · refine tsum_congr fun m => ?_
      field_simp; ring
  rw [hfun, volterraConv_add_right (g := fun s => 1 / Θ 1 * thetaRenewalMomentIncrement s)
    (h := thetaRenewalMomentSeries) hν (by fun_prop) hS, volterraConv_smul_right, hconvS,
    volterraConv_comm thetaRenewalIncrement thetaRenewalMomentIncrement, mul_thetaRenewalLogKernel_eq,
    mul_add, hcS]
  field_simp

/-! ## The universal reflection -/

theorem thetaLogProfile_zero : thetaLogProfile 0 = Θ 1 := by simp [thetaLogProfile]

theorem continuous_exp_quarter : Continuous fun s : ℝ => Real.exp (s / 4) := by fun_prop

/-- `(e^{a·} ⋆ ν)(t) = c e^{at} - P(t)`. -/
theorem volterraConv_exp_thetaRenewalIncrement (t : ℝ) :
    volterraConv (fun s => Real.exp (s / 4)) thetaRenewalIncrement t =
      Θ 1 * Real.exp (t / 4) - thetaLogProfile t := by
  rw [volterraConv]
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt (fun s => -(Real.exp ((t - s) / 4) *
      thetaLogProfile s)) (Real.exp ((t - s) / 4) * thetaRenewalIncrement s) s := by
    intro s _
    have h1 : HasDerivAt (fun s => Real.exp ((t - s) / 4)) (Real.exp ((t - s) / 4) * (-1 / 4)) s :=
      (((hasDerivAt_id s).const_sub t).div_const 4).exp.congr_deriv (by simp)
    refine (h1.mul (hasDerivAt_thetaLogProfile s)).neg.congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by have := continuous_thetaRenewalIncrement; fun_prop : Continuous fun s =>
      Real.exp ((t - s) / 4) * thetaRenewalIncrement s).intervalIntegrable _ _),
    thetaLogProfile_zero]
  simp only [sub_self, zero_div, Real.exp_zero, sub_zero, one_mul]
  ring

/-- `(e^{a·} ⋆ τν)(t) = -t P(t) + (e^{a·} ⋆ P)(t)`. -/
theorem volterraConv_exp_thetaRenewalMomentIncrement (t : ℝ) :
    volterraConv (fun s => Real.exp (s / 4)) thetaRenewalMomentIncrement t =
      -(t * thetaLogProfile t) + volterraConv (fun s => Real.exp (s / 4)) thetaLogProfile t := by
  rw [volterraConv, volterraConv]
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt (fun s => -(s * Real.exp ((t - s) / 4) *
      thetaLogProfile s)) (s * Real.exp ((t - s) / 4) * thetaRenewalIncrement s -
        Real.exp ((t - s) / 4) * thetaLogProfile s) s := by
    intro s _
    have h1 : HasDerivAt (fun s => Real.exp ((t - s) / 4)) (Real.exp ((t - s) / 4) * (-1 / 4)) s :=
      (((hasDerivAt_id s).const_sub t).div_const 4).exp.congr_deriv (by simp)
    refine (((hasDerivAt_id' s).mul h1).mul (hasDerivAt_thetaLogProfile s)).neg.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hP := continuous_thetaLogProfile
  have hν := continuous_thetaRenewalIncrement
  have hsplit : (∫ s in (0 : ℝ)..t, Real.exp ((t - s) / 4) * thetaRenewalMomentIncrement s) =
      (∫ s in (0 : ℝ)..t, (s * Real.exp ((t - s) / 4) * thetaRenewalIncrement s -
        Real.exp ((t - s) / 4) * thetaLogProfile s)) +
      ∫ s in (0 : ℝ)..t, Real.exp ((t - s) / 4) * thetaLogProfile s := by
    rw [← intervalIntegral.integral_add
      ((by fun_prop : Continuous fun s => s * Real.exp ((t - s) / 4) * thetaRenewalIncrement s -
        Real.exp ((t - s) / 4) * thetaLogProfile s).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s => Real.exp ((t - s) / 4) * thetaLogProfile s).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [thetaRenewalMomentIncrement]; ring
  rw [hsplit, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun s => s * Real.exp ((t - s) / 4) * thetaRenewalIncrement s -
      Real.exp ((t - s) / 4) * thetaLogProfile s).intervalIntegrable _ _)]
  simp

/-- The moment kernel `w(t) = t Q(t)`. -/
def thetaRenewalMomentKernel (t : ℝ) : ℝ := t * thetaRenewalLogKernel t

theorem continuous_thetaRenewalMomentKernel : Continuous thetaRenewalMomentKernel := by
  have := continuous_thetaRenewalLogKernel
  unfold thetaRenewalMomentKernel; fun_prop

/-- `P ⋆ (τQ) = -τP + e^{a·} ⋆ P`. -/
theorem volterraConv_thetaLogProfile_momentKernel (t : ℝ) :
    volterraConv thetaLogProfile thetaRenewalMomentKernel t =
      -(t * thetaLogProfile t) + volterraConv (fun s => Real.exp (s / 4)) thetaLogProfile t := by
  have hc := thetaSeam_pos
  have he := continuous_exp_quarter
  have hν := continuous_thetaRenewalIncrement
  have hτ := continuous_thetaRenewalMomentIncrement
  have hw := continuous_thetaRenewalMomentKernel
  have hP := continuous_thetaLogProfile
  have hνw := continuous_volterraConv hν hw
  -- the Volterra law as an identity of functions
  have hlaw : (fun s => Θ 1 * thetaRenewalMomentKernel s) =
      thetaRenewalMomentIncrement + volterraConv thetaRenewalIncrement thetaRenewalMomentKernel := by
    funext s
    simp only [Pi.add_apply, thetaRenewalMomentKernel, thetaRenewalMomentIncrement]
    exact thetaRenewal_volterra_law s
  have h1 : volterraConv (fun s => Real.exp (s / 4)) (fun s => Θ 1 * thetaRenewalMomentKernel s) t =
      Θ 1 * volterraConv (fun s => Real.exp (s / 4)) thetaRenewalMomentKernel t :=
    volterraConv_smul_right _ _ _ _
  rw [hlaw, volterraConv_add_right he hτ hνw, volterraConv_exp_thetaRenewalMomentIncrement,
    ← volterraConv_assoc he hν hw] at h1
  have hE1 : volterraConv (fun s => Real.exp (s / 4)) thetaRenewalIncrement =
      fun s => Θ 1 * Real.exp (s / 4) - thetaLogProfile s :=
    funext volterraConv_exp_thetaRenewalIncrement
  rw [hE1, volterraConv_comm (fun s => Θ 1 * Real.exp (s / 4) - thetaLogProfile s),
    volterraConv_sub_right (g := fun s => Θ 1 * Real.exp (s / 4)) (h := thetaLogProfile) hw
      (continuous_const.mul he) hP, volterraConv_smul_right,
    volterraConv_comm thetaRenewalMomentKernel, volterraConv_comm thetaRenewalMomentKernel] at h1
  linarith

/-- The even-ness candidate `y(t) = e^{-at} + t Q(t)`. -/
def thetaRenewalReflectionProfile (t : ℝ) : ℝ := Real.exp (-(t / 4)) + thetaRenewalMomentKernel t

theorem continuous_thetaRenewalReflectionProfile : Continuous thetaRenewalReflectionProfile := by
  have := continuous_thetaRenewalMomentKernel
  unfold thetaRenewalReflectionProfile; fun_prop

/-- `P ⋆ y = P ⋆ (e^{-a·} + e^{a·}) - τP`. -/
theorem volterraConv_thetaLogProfile_reflectionProfile (t : ℝ) :
    volterraConv thetaLogProfile thetaRenewalReflectionProfile t =
      volterraConv thetaLogProfile (fun s => Real.exp (-(s / 4)) + Real.exp (s / 4)) t -
        t * thetaLogProfile t := by
  have hP := continuous_thetaLogProfile
  have he := continuous_exp_quarter
  have he' : Continuous fun s : ℝ => Real.exp (-(s / 4)) := by fun_prop
  have hw := continuous_thetaRenewalMomentKernel
  rw [show thetaRenewalReflectionProfile = (fun s => Real.exp (-(s / 4))) + thetaRenewalMomentKernel
    from rfl, volterraConv_add_right hP he' hw, volterraConv_thetaLogProfile_momentKernel,
    show (fun s : ℝ => Real.exp (-(s / 4)) + Real.exp (s / 4)) =
      (fun s => Real.exp (-(s / 4))) + fun s => Real.exp (s / 4) from rfl,
    volterraConv_add_right hP he' he, volterraConv_comm (fun s => Real.exp (s / 4))]
  ring

/-- The profile `y(t) = e^{-at} + t Q(t)` is even. -/
theorem thetaRenewalReflectionProfile_neg (t : ℝ) :
    thetaRenewalReflectionProfile (-t) = thetaRenewalReflectionProfile t := by
  have hc := thetaSeam_pos
  have hP := continuous_thetaLogProfile
  have hy := continuous_thetaRenewalReflectionProfile
  have hν := continuous_thetaRenewalIncrement
  have he := continuous_exp_quarter
  set y := thetaRenewalReflectionProfile
  set yr : ℝ → ℝ := fun s => y (-s)
  have hyr : Continuous yr := hy.comp continuous_neg
  have hPe : (fun s => thetaLogProfile (-s)) = thetaLogProfile := funext thetaLogProfile_neg
  set h2 : ℝ → ℝ := fun s => Real.exp (-(s / 4)) + Real.exp (s / 4)
  have hh2 : (fun s => h2 (-s)) = h2 := by funext s; simp only [h2]; ring_nf
  have hPh : ∀ u, volterraConv thetaLogProfile h2 (-u) = -volterraConv thetaLogProfile h2 u := by
    intro u; rw [volterraConv_neg, hPe, hh2]
  have heq : ∀ u, volterraConv thetaLogProfile yr u = volterraConv thetaLogProfile y u := by
    intro u
    have h := volterraConv_neg thetaLogProfile yr (-u)
    rw [neg_neg, hPe] at h
    have hyy : (fun s => yr (-s)) = y := by funext s; simp [yr]
    rw [hyy] at h
    rw [h, volterraConv_thetaLogProfile_reflectionProfile, volterraConv_thetaLogProfile_reflectionProfile,
      hPh, thetaLogProfile_neg]
    ring
  -- `P ⋆ (yr - y) = 0`, and `P = c e^{a·} - e^{a·} ⋆ ν`
  set f : ℝ → ℝ := fun s => yr s - y s
  have hf : Continuous f := hyr.sub hy
  have hPf : ∀ u, volterraConv thetaLogProfile f u = 0 := by
    intro u
    rw [show f = fun s => yr s - y s from rfl, volterraConv_sub_right hP hyr hy, heq, sub_self]
  have hPdecomp : thetaLogProfile = fun s => Θ 1 * Real.exp (s / 4) -
      volterraConv (fun s => Real.exp (s / 4)) thetaRenewalIncrement s := by
    funext s; rw [volterraConv_exp_thetaRenewalIncrement]; ring
  have hEc := continuous_volterraConv he hν
  have hkey : ∀ u, volterraConv (fun s => Real.exp (1 / 4 * s))
      (fun s => Θ 1 * f s - volterraConv thetaRenewalIncrement f s) u = 0 := by
    intro u
    have h := hPf u
    rw [hPdecomp, volterraConv_comm, volterraConv_sub_right (g := fun s => Θ 1 * Real.exp (s / 4))
      (h := volterraConv (fun s => Real.exp (s / 4)) thetaRenewalIncrement) hf
      (continuous_const.mul he) hEc,
      volterraConv_smul_right, volterraConv_comm f, volterraConv_comm f,
      volterraConv_assoc he hν hf] at h
    rw [show (fun s : ℝ => Real.exp (1 / 4 * s)) = fun s => Real.exp (s / 4) by
      funext s; ring_nf, volterraConv_sub_right (g := fun s => Θ 1 * f s)
      (h := volterraConv thetaRenewalIncrement f) he (continuous_const.mul hf)
      (continuous_volterraConv hν hf), volterraConv_smul_right]
    linarith
  have h0 := eq_zero_of_volterraConv_exp_eq_zero ((continuous_const.mul hf).sub
    (continuous_volterraConv hν hf)) hkey
  have hf0 := eq_zero_of_mul_eq_volterraConv hc.ne' hν hf fun u => by
    have := congrFun h0 u
    simp only [Pi.zero_apply, Pi.sub_apply, Pi.mul_apply] at this
    linarith
  have := congrFun hf0 t
  simp only [f, yr, Pi.zero_apply] at this
  linarith

/-- **The universal reflection (3).** `Q(-t) + Q(t) = 2 sinh(at)/t` for `t ≠ 0`, where `Q` on the
negative axis is the continuation by oriented convolutions. -/
theorem thetaRenewalLogKernel_neg_add {t : ℝ} (ht : t ≠ 0) :
    thetaRenewalLogKernel (-t) + thetaRenewalLogKernel t = 2 * Real.sinh (t / 4) / t := by
  have h := thetaRenewalReflectionProfile_neg t
  simp only [thetaRenewalReflectionProfile, thetaRenewalMomentKernel] at h
  rw [Real.sinh_eq, eq_div_iff ht]
  rw [show -(-t / 4) = t / 4 by ring] at h
  linear_combination (-1 : ℝ) * h

/-- `Q(0) = a`, the value of `2 sinh(at)/t` at zero halved. -/
theorem thetaRenewalLogKernel_zero : thetaRenewalLogKernel 0 = 1 / 4 := by
  have hc := thetaSeam_pos
  rw [thetaRenewalLogKernel, tsum_eq_single 0 fun m hm => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simp [thetaRenewalPower, volterraConv]]
  simp only [thetaRenewalPower, thetaRenewalIncrement_zero, Nat.cast_zero, zero_add, pow_one,
    one_mul]
  field_simp

/-- The odd boundary kernel `W(t) = e^{-at}/t + Q(t)`. -/
def thetaRenewalOddKernel (t : ℝ) : ℝ := Real.exp (-(t / 4)) / t + thetaRenewalLogKernel t

/-- `W(-t) = -W(t)`: the continuation through the simple pole at zero is odd. -/
theorem thetaRenewalOddKernel_neg {t : ℝ} (ht : t ≠ 0) :
    thetaRenewalOddKernel (-t) = -thetaRenewalOddKernel t := by
  have h := thetaRenewalLogKernel_neg_add ht
  rw [Real.sinh_eq] at h
  simp only [thetaRenewalOddKernel]
  rw [show -(-t / 4) = t / 4 by ring]
  field_simp
  field_simp at h
  linarith

/-- The negative branch is positive: `Q(-t) > 0` for `t > 0`. -/
theorem thetaRenewalLogKernel_neg_pos {t : ℝ} (ht : 0 < t) : 0 < thetaRenewalLogKernel (-t) := by
  have h := thetaRenewalLogKernel_neg_add ht.ne'
  have hs : t / 4 ≤ Real.sinh (t / 4) := Real.self_le_sinh_iff.mpr (by positivity)
  have hQ := thetaRenewalLogKernel_le_quarter ht
  have hexp : Real.exp (-((Real.pi - 3 / 2) * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_gt_three])
  have h2 : 1 / 2 ≤ 2 * Real.sinh (t / 4) / t := by
    rw [le_div_iff₀ ht]; linarith
  linarith

/-- **Negative-end asymptotic.** `Q(-t) ~ e^{at}/t` as `t → ∞`. -/
theorem tendsto_thetaRenewalLogKernel_neg :
    Tendsto (fun t => thetaRenewalLogKernel (-t) / (Real.exp (t / 4) / t)) atTop (𝓝 1) := by
  set κ := Real.pi - 3 / 2 + 1 / 4 with hκ
  have hκ0 : 0 < κ := by linarith [Real.pi_gt_three]
  have hdecay : Tendsto (fun t : ℝ => t * Real.exp (-(κ * t))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hκ0)).div_const κ
    rw [zero_div] at h
    refine h.congr fun t => ?_
    simp only [Function.comp, pow_one, id]
    field_simp
  have hsmall : Tendsto (fun t : ℝ => t * thetaRenewalLogKernel t * Real.exp (-(t / 4))) atTop
      (𝓝 0) := by
    have hdom := hdecay.const_mul (1 / 4)
    rw [mul_zero] at hdom
    refine squeeze_zero' ?_ ?_ hdom
    · filter_upwards [eventually_gt_atTop 0] with t ht
      exact mul_nonneg (mul_nonneg ht.le (thetaRenewalLogKernel_pos ht).le) (Real.exp_pos _).le
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have hQ := thetaRenewalLogKernel_le_quarter ht
      calc t * thetaRenewalLogKernel t * Real.exp (-(t / 4))
          ≤ t * (1 / 4 * Real.exp (-((Real.pi - 3 / 2) * t))) * Real.exp (-(t / 4)) := by gcongr
        _ = 1 / 4 * (t * Real.exp (-(κ * t))) := by
            rw [hκ, show -((Real.pi - 3 / 2 + 1 / 4) * t) = -((Real.pi - 3 / 2) * t) + -(t / 4) by
              ring, Real.exp_add]; ring
  have hmain := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const two_pos)).add hsmall)
  simp only [add_zero, sub_zero, Function.comp_apply, id] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have h := thetaRenewalLogKernel_neg_add ht.ne'
  have e1 : Real.exp (t / 4) * Real.exp (-(t / 4)) = 1 := by rw [← Real.exp_add]; simp
  have e2 : Real.exp (-(t / 4)) * Real.exp (-(t / 4)) = Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hEinv : (Real.exp (t / 4))⁻¹ = Real.exp (-(t / 4)) := by rw [← Real.exp_neg]
  rw [Real.sinh_eq] at h
  have hQ : thetaRenewalLogKernel (-t) * t =
      Real.exp (t / 4) - Real.exp (-(t / 4)) - t * thetaRenewalLogKernel t := by
    have h' : thetaRenewalLogKernel (-t) = (Real.exp (t / 4) - Real.exp (-(t / 4))) / t -
        thetaRenewalLogKernel t := by
      rw [eq_sub_iff_add_eq, h]; ring
    rw [h']; field_simp
  have hE := Real.exp_pos (t / 4)
  symm
  calc thetaRenewalLogKernel (-t) / (Real.exp (t / 4) / t)
      = thetaRenewalLogKernel (-t) * t * (Real.exp (t / 4))⁻¹ := by field_simp
    _ = (Real.exp (t / 4) - Real.exp (-(t / 4)) - t * thetaRenewalLogKernel t) *
          Real.exp (-(t / 4)) := by rw [hQ, hEinv]
    _ = 1 - (Real.exp (-(t / 2)) + t * thetaRenewalLogKernel t * Real.exp (-(t / 4))) := by
        linear_combination e1 - e2

end RHTower
