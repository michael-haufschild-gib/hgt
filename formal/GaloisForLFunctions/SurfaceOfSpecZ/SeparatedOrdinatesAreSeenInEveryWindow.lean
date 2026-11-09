import GaloisForLFunctions.SurfaceOfSpecZ.BohrDenseSetsSampleEveryAttainedTop
import GaloisForLFunctions.SquareRootThreshold.InghamInequalityForSeparatedSpectra
import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyDeterminesTheConfiguration

/-!
# Separated ordinates are seen in every window

Let a tempered configuration without real zeros have *separated ordinates*: two exponents
`z = ρ − ½` (zeros and their conjugates) that are neither equal nor reflections `z' = −z̄` have
ordinates at least `δ` apart (`SeparatedOrdinates`). If some zero is off the line, then for every
`K` and every `ℓ ≥ 40/δ` the trace falls below `−K` in every window `[u₀ − ℓ, u₀ + ℓ]` far enough
out (`exists_lt_in_window_of_separatedOrdinates`). No attainment of the maximal real part is
assumed, and the window length depends on `δ` only.

* **Triangle average** (`triAvg`, `triAvg_expSum`). The mean `A_ℓ f = ℓ⁻² ∫∫ f(s + t)` over
  `s, t ∈ [−ℓ/2, ℓ/2]` takes `e^{wv}` to `σ_ℓ(w)²`, `σ_ℓ(w) = ℓ⁻¹ ∫ e^{ws} ds`, and
  `|σ_ℓ(w)| ≤ 2 e^{|Re w| ℓ/2}/(|w| ℓ)` (`norm_boxAvg_le_div`).
* **Landau on a window** (`norm_le_of_window_lower`). Testing `F + K ≥ 0` against
  `e^{−x₀v}(1 + Re(ω e^{iγ₀v}))` isolates the weight `|D_{z₀}| e^{x₀u₀}` of one exponent, up to the
  leakage of every other exponent through `σ_ℓ`.
* **Dominance** (`exists_dominant`, `le_re_of_dominant`, `weight_drift_le`). Take `z₀` of maximal
  weight `|D_z| e^{Re z · u₀}`. The depth of the dominant exponent tends to the supremum `b` of
  the depths, so on `[u₀ − ℓ, u₀ + ℓ]` no weight exceeds that of `z₀` by more than `e^{ηℓ}`: deeper
  exponents are controlled at `u₀ + ℓ`, shallower ones at `u₀ − ℓ`.
* **Counting** (`sum_inv_sq_im_le`). Separation bounds `Σ (Im z − t)⁻²` by `8/g²`, so the
  leakage is `O(1/(δℓ)²)` of the dominant weight; the reflection `−z̄₀` of the dominant exponent
  is damped by `e^{−2x₀(u₀ − ℓ)}`. The dominant weight is then `O(K e^{ℓ/2})`, against its growth.

Consequences: an impure configuration bounded below on windows of length `80/δ` beyond every
bound is not `δ`-separated (`onLine_of_bddBelow_windows_of_separatedOrdinates`); on the integers,
windows `[x, e^{80/δ} x]` suffice (`onLine_of_bddBelow_integer_windows_of_separatedOrdinates`).
On windows of unbounded length an impure configuration bounded below has no positive
separation (`not_separatedOrdinates_of_bddBelow_long_intervals`): a configuration that defeats
growing windows must carry near-coincident ordinates.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-! ### The triangle average -/

/-- The box average `σ_ℓ(w) = ℓ⁻¹ ∫_{−ℓ/2}^{ℓ/2} e^{ws} ds`. -/
def boxAvg (ℓ : ℝ) (w : ℂ) : ℂ := (ℓ : ℂ)⁻¹ * ∫ s in -(ℓ / 2)..ℓ / 2, cexp (w * s)

/-- The triangle average `A_ℓ f = ℓ⁻² ∫∫_{[−ℓ/2, ℓ/2]²} f(s + t)`: the mean of `f` against the
Fejér triangle on `[−ℓ, ℓ]`. -/
def triAvg (ℓ : ℝ) (f : ℝ → ℂ) : ℂ :=
  ((ℓ : ℂ)⁻¹) ^ 2 * ∫ s in -(ℓ / 2)..ℓ / 2, ∫ t in -(ℓ / 2)..ℓ / 2, f (s + t)

/-- **The triangle average of an exponential sum** is `Σ c_i σ_ℓ(w_i)²`. -/
theorem triAvg_expSum {ι : Type*} (S : Finset ι) (c w : ι → ℂ) (ℓ : ℝ) :
    triAvg ℓ (fun v => ∑ i ∈ S, c i * cexp (w i * v)) = ∑ i ∈ S, c i * boxAvg ℓ (w i) ^ 2 := by
  set J : ι → ℂ := fun i => ∫ t in -(ℓ / 2)..ℓ / 2, cexp (w i * t) with hJ
  have hinner : ∀ s : ℝ, (∫ t in -(ℓ / 2)..ℓ / 2, ∑ i ∈ S, c i * cexp (w i * ((s + t : ℝ) : ℂ))) =
      ∑ i ∈ S, (c i * J i) * cexp (w i * s) := by
    intro s
    rw [intervalIntegral.integral_finsetSum fun i _ => (by fun_prop : Continuous fun t : ℝ =>
      c i * cexp (w i * ((s + t : ℝ) : ℂ))).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : (fun t : ℝ => c i * cexp (w i * ((s + t : ℝ) : ℂ))) =
        fun t : ℝ => (c i * cexp (w i * s)) * cexp (w i * t) := by
      funext t; push_cast; rw [mul_add, Complex.exp_add]; ring
    rw [h, intervalIntegral.integral_const_mul]; ring
  unfold triAvg
  simp only []
  simp_rw [hinner]
  rw [intervalIntegral.integral_finsetSum fun i _ => (by fun_prop : Continuous fun s : ℝ =>
    (c i * J i) * cexp (w i * s)).intervalIntegrable _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, boxAvg]
  ring

/-- An interval integral of a function with nonnegative real part has nonnegative real part. -/
theorem re_intervalIntegral_nonneg {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, 0 ≤ (g x).re) : 0 ≤ (∫ x in a..b, g x).re := by
  by_cases hg : IntervalIntegrable g MeasureTheory.volume a b
  · have e := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hg
    simp only [Complex.reCLM_apply] at e
    rw [← e]
    exact intervalIntegral.integral_nonneg hab h
  · rw [intervalIntegral.integral_undef hg, Complex.zero_re]

/-- **Positivity of the triangle average.** -/
theorem re_triAvg_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) {f : ℝ → ℂ}
    (hf : ∀ v ∈ Icc (-ℓ) ℓ, 0 ≤ (f v).re) : 0 ≤ (triAvg ℓ f).re := by
  have hab : -(ℓ / 2) ≤ ℓ / 2 := by linarith
  have h2 : 0 ≤ (∫ s in -(ℓ / 2)..ℓ / 2, ∫ t in -(ℓ / 2)..ℓ / 2, f (s + t)).re :=
    re_intervalIntegral_nonneg hab fun s hs => re_intervalIntegral_nonneg hab fun t ht =>
      hf _ ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
  have hc : ((ℓ : ℂ)⁻¹) ^ 2 = ((ℓ⁻¹ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  unfold triAvg
  rw [hc, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) h2

theorem boxAvg_zero {ℓ : ℝ} (hℓ : 0 < ℓ) : boxAvg ℓ 0 = 1 := by
  unfold boxAvg
  simp only [zero_mul, Complex.exp_zero, intervalIntegral.integral_const]
  have : ((ℓ / 2 - -(ℓ / 2) : ℝ) : ℂ) = (ℓ : ℂ) := by push_cast; ring
  rw [Complex.real_smul, mul_one, this, inv_mul_cancel₀ (by exact_mod_cast hℓ.ne')]

theorem norm_cexp_mul_ofReal (w : ℂ) (s : ℝ) : ‖cexp (w * s)‖ = Real.exp (w.re * s) := by
  rw [Complex.norm_exp]; congr 1; simp

theorem re_mul_le_abs {x s ℓ : ℝ} (hs : |s| ≤ ℓ / 2) : x * s ≤ |x| * ℓ / 2 :=
  calc x * s ≤ |x * s| := le_abs_self _
    _ = |x| * |s| := abs_mul _ _
    _ ≤ |x| * (ℓ / 2) := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = |x| * ℓ / 2 := by ring

/-- `|σ_ℓ(w)| ≤ e^{|Re w| ℓ/2}`. -/
theorem norm_boxAvg_le {ℓ : ℝ} (hℓ : 0 < ℓ) (w : ℂ) :
    ‖boxAvg ℓ w‖ ≤ Real.exp (|w.re| * ℓ / 2) := by
  have hb : ‖∫ s in -(ℓ / 2)..ℓ / 2, cexp (w * s)‖ ≤
      Real.exp (|w.re| * ℓ / 2) * |ℓ / 2 - -(ℓ / 2)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [Set.uIoc_of_le (by linarith)] at hs
    rw [norm_cexp_mul_ofReal]
    exact Real.exp_le_exp.mpr (re_mul_le_abs (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩))
  have hl : |ℓ / 2 - -(ℓ / 2)| = ℓ := by rw [abs_of_pos (by linarith)]; ring
  rw [hl] at hb
  unfold boxAvg
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hℓ.le]
  calc ℓ⁻¹ * ‖∫ s in -(ℓ / 2)..ℓ / 2, cexp (w * s)‖ ≤ ℓ⁻¹ * (Real.exp (|w.re| * ℓ / 2) * ℓ) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = Real.exp (|w.re| * ℓ / 2) := by field_simp

/-- `|σ_ℓ(w)| ≤ 2 e^{|Re w| ℓ/2}/(|w| ℓ)` for `w ≠ 0`. -/
theorem norm_boxAvg_le_div {ℓ : ℝ} (hℓ : 0 < ℓ) {w : ℂ} (hw : w ≠ 0) :
    ‖boxAvg ℓ w‖ ≤ 2 * Real.exp (|w.re| * ℓ / 2) / (‖w‖ * ℓ) := by
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h1 : ‖cexp (w * ((ℓ / 2 : ℝ) : ℂ))‖ ≤ Real.exp (|w.re| * ℓ / 2) := by
    rw [norm_cexp_mul_ofReal]
    exact Real.exp_le_exp.mpr (re_mul_le_abs (by rw [abs_of_pos (by linarith)]))
  have h2 : ‖cexp (w * ((-(ℓ / 2) : ℝ) : ℂ))‖ ≤ Real.exp (|w.re| * ℓ / 2) := by
    rw [norm_cexp_mul_ofReal]
    exact Real.exp_le_exp.mpr (re_mul_le_abs (by rw [abs_neg, abs_of_pos (by linarith)]))
  have hn := (norm_sub_le (cexp (w * ((ℓ / 2 : ℝ) : ℂ))) (cexp (w * ((-(ℓ / 2) : ℝ) : ℂ)))).trans
    (add_le_add h1 h2)
  unfold boxAvg
  rw [integral_exp_mul_complex hw, norm_mul, norm_div, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hℓ.le]
  calc ℓ⁻¹ * (‖cexp (w * ((ℓ / 2 : ℝ) : ℂ)) - cexp (w * ((-(ℓ / 2) : ℝ) : ℂ))‖ / ‖w‖)
      ≤ ℓ⁻¹ * ((Real.exp (|w.re| * ℓ / 2) + Real.exp (|w.re| * ℓ / 2)) / ‖w‖) := by gcongr
    _ = 2 * Real.exp (|w.re| * ℓ / 2) / (‖w‖ * ℓ) := by field_simp; ring

/-- `|σ_ℓ(w)|² ≤ e^{|Re w| ℓ} · 4/(|w| ℓ)²` for `w ≠ 0`. -/
theorem norm_boxAvg_sq_le {ℓ : ℝ} (hℓ : 0 < ℓ) {w : ℂ} (hw : w ≠ 0) :
    ‖boxAvg ℓ w‖ ^ 2 ≤ Real.exp (|w.re| * ℓ) * (4 / (‖w‖ * ℓ) ^ 2) := by
  have h := norm_boxAvg_le_div hℓ hw
  have hwp : 0 < ‖w‖ * ℓ := mul_pos (norm_pos_iff.mpr hw) hℓ
  have he : Real.exp (|w.re| * ℓ) = Real.exp (|w.re| * ℓ / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc ‖boxAvg ℓ w‖ ^ 2 ≤ (2 * Real.exp (|w.re| * ℓ / 2) / (‖w‖ * ℓ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = Real.exp (|w.re| * ℓ) * (4 / (‖w‖ * ℓ) ^ 2) := by rw [he]; field_simp; ring

/-- `|σ_ℓ(w)|² ≤ e^{|Re w| ℓ}`. -/
theorem norm_boxAvg_sq_le_exp {ℓ : ℝ} (hℓ : 0 < ℓ) (w : ℂ) :
    ‖boxAvg ℓ w‖ ^ 2 ≤ Real.exp (|w.re| * ℓ) := by
  have he : Real.exp (|w.re| * ℓ) = Real.exp (|w.re| * ℓ / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [he]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_boxAvg_le hℓ w) 2

/-! ### Landau's inequality on a window -/

/-- The Landau multiplier `e^{−x₀v}(1 + Re(ω e^{iγ₀v}))` as a sum of three exponentials. -/
theorem landau_multiplier (z₀ ω : ℂ) (v : ℝ) :
    cexp (-(z₀.re : ℂ) * v) + ω / 2 * cexp (-(conj z₀) * v) + conj ω / 2 * cexp (-z₀ * v) =
      ((Real.exp (-z₀.re * v) * (1 + (ω * cexp (I * z₀.im * v)).re) : ℝ) : ℂ) := by
  have hc : -(conj z₀) * (v : ℂ) = -(z₀.re : ℂ) * v + I * z₀.im * v := by
    apply Complex.ext <;> simp
  have hz : -z₀ * (v : ℂ) = -(z₀.re : ℂ) * v + conj (I * z₀.im * v) := by
    apply Complex.ext <;> simp
  have hr : cexp (-(z₀.re : ℂ) * v) = ((Real.exp (-z₀.re * v) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [hc, hz, Complex.exp_add, Complex.exp_add, Complex.exp_conj, hr]
  set E := cexp (I * z₀.im * v)
  have hadd : ω * E + conj (ω * E) = (((ω * E).re * 2 : ℝ) : ℂ) := by
    rw [Complex.add_conj]; push_cast; ring
  have : ω / 2 * (((Real.exp (-z₀.re * v) : ℝ) : ℂ) * E) +
      conj ω / 2 * (((Real.exp (-z₀.re * v) : ℝ) : ℂ) * conj E) =
      ((Real.exp (-z₀.re * v) : ℝ) : ℂ) * ((ω * E + conj (ω * E)) / 2) := by
    rw [map_mul]; ring
  rw [add_assoc, this, hadd]
  push_cast; ring

/-- **Landau's inequality on a window.** If `Re Σ_{z∈S} D_z e^{z(u₀+v)} ≥ −K` for `|v| ≤ ℓ`, the
weight `|D_{z₀} e^{z₀u₀}|` of an exponent `z₀` with `z̄₀ ∈ S` and `D_{z̄₀} = \bar D_{z₀}` is at most
the leakage of the other exponents through `σ_ℓ` plus `2K e^{|Re z₀| ℓ}`. The test is the triangle
average of `(F + K) e^{−x₀v}(1 + Re(ω e^{iγ₀v}))`, `ω` opposite to the phase of `D_{z₀} e^{z₀u₀}`. -/
theorem norm_le_of_window_lower {S : Finset ℂ} {D : ℂ → ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ S)
    (hz₀' : conj z₀ ∈ S) (hD : D (conj z₀) = conj (D z₀)) {u₀ ℓ K : ℝ} (hℓ : 0 < ℓ)
    (hK : 0 ≤ K)
    (hlow : ∀ v ∈ Icc (-ℓ) ℓ, -K ≤ (∑ z ∈ S, D z * cexp (z * ((u₀ + v : ℝ) : ℂ))).re) :
    ‖D z₀ * cexp (z₀ * u₀)‖ ≤
      ∑ z ∈ S, ‖D z * cexp (z * u₀) * boxAvg ℓ (z - z₀.re) ^ 2‖ +
      (∑ z ∈ S.erase (conj z₀), ‖D z * cexp (z * u₀) * boxAvg ℓ (z - conj z₀) ^ 2‖ +
        ∑ z ∈ S.erase z₀, ‖D z * cexp (z * u₀) * boxAvg ℓ (z - z₀) ^ 2‖) / 2 +
      2 * K * Real.exp (|z₀.re| * ℓ) := by
  classical
  set P : ℂ := D z₀ * cexp (z₀ * u₀) with hPdef
  set R₀ := ∑ z ∈ S, ‖D z * cexp (z * u₀) * boxAvg ℓ (z - z₀.re) ^ 2‖
  set Rp := ∑ z ∈ S.erase (conj z₀), ‖D z * cexp (z * u₀) * boxAvg ℓ (z - conj z₀) ^ 2‖
  set Rm := ∑ z ∈ S.erase z₀, ‖D z * cexp (z * u₀) * boxAvg ℓ (z - z₀) ^ 2‖
  have hR₀ : 0 ≤ R₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hRp : 0 ≤ Rp := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hRm : 0 ≤ Rm := Finset.sum_nonneg fun _ _ => norm_nonneg _
  by_cases hP : P = 0
  · rw [hP, norm_zero]; positivity
  have hPn : 0 < ‖P‖ := norm_pos_iff.mpr hP
  set ω : ℂ := -(P / (‖P‖ : ℂ)) with hω
  have hωn : ‖ω‖ = 1 := by
    rw [hω, norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg hPn.le, div_self hPn.ne']
  -- the test function as an exponential sum
  let a : Option ℂ → ℂ := fun o => o.elim (K : ℂ) fun z => D z * cexp (z * u₀)
  let β : Option ℂ → ℂ := fun o => o.elim 0 id
  let κ : Fin 3 → ℂ := ![1, ω / 2, conj ω / 2]
  let θ : Fin 3 → ℂ := ![(z₀.re : ℂ), conj z₀, z₀]
  let c : Option ℂ × Fin 3 → ℂ := fun p => a p.1 * κ p.2
  let w : Option ℂ × Fin 3 → ℂ := fun p => β p.1 - θ p.2
  set T := Finset.insertNone S ×ˢ (Finset.univ : Finset (Fin 3)) with hT
  have hG : ∀ v : ℝ, ∑ p ∈ T, c p * cexp (w p * v) =
      (((K : ℂ) + ∑ z ∈ S, D z * cexp (z * ((u₀ + v : ℝ) : ℂ)))) *
        ((Real.exp (-z₀.re * v) * (1 + (ω * cexp (I * z₀.im * v)).re) : ℝ) : ℂ) := by
    intro v
    rw [← landau_multiplier, hT, Finset.sum_product]
    have hf : (K : ℂ) + ∑ z ∈ S, D z * cexp (z * ((u₀ + v : ℝ) : ℂ)) =
        ∑ o ∈ Finset.insertNone S, a o * cexp (β o * v) := by
      rw [Finset.sum_insertNone]
      simp only [a, β, Option.elim, zero_mul, Complex.exp_zero, mul_one, id]
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      push_cast; rw [mul_add, Complex.exp_add]; ring
    rw [hf, Finset.sum_mul]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Fin.sum_univ_three]
    simp only [c, w, κ, θ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have e : ∀ q : ℂ, cexp ((β o - q) * v) = cexp (β o * v) * cexp (-q * v) := fun q => by
      rw [← Complex.exp_add]; ring_nf
    rw [e, e, e]; ring
  -- positivity of the test
  have hpos : 0 ≤ (triAvg ℓ fun v => ∑ p ∈ T, c p * cexp (w p * v)).re := by
    refine re_triAvg_nonneg hℓ fun v hv => ?_
    rw [hG v, Complex.re_mul_ofReal, Complex.add_re, Complex.ofReal_re]
    have hm : 0 ≤ Real.exp (-z₀.re * v) * (1 + (ω * cexp (I * z₀.im * v)).re) := by
      refine mul_nonneg (Real.exp_pos _).le ?_
      have h1 : |(ω * cexp (I * z₀.im * v)).re| ≤ 1 := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, hωn, one_mul, show I * (z₀.im : ℂ) * (v : ℂ) = ((z₀.im * v : ℝ) : ℂ) * I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I]
      linarith [(abs_le.mp h1).1]
    exact mul_nonneg (by linarith [hlow v hv]) hm
  -- its value
  have hval : (triAvg ℓ fun v => ∑ p ∈ T, c p * cexp (w p * v)) =
      (K : ℂ) * (boxAvg ℓ (-(z₀.re : ℂ)) ^ 2 + ω / 2 * boxAvg ℓ (-(conj z₀)) ^ 2 +
        conj ω / 2 * boxAvg ℓ (-z₀) ^ 2) +
      (∑ z ∈ S, D z * cexp (z * u₀) * boxAvg ℓ (z - z₀.re) ^ 2 +
        ω / 2 * ∑ z ∈ S, D z * cexp (z * u₀) * boxAvg ℓ (z - conj z₀) ^ 2 +
        conj ω / 2 * ∑ z ∈ S, D z * cexp (z * u₀) * boxAvg ℓ (z - z₀) ^ 2) := by
    rw [triAvg_expSum, hT, Finset.sum_product, Finset.sum_insertNone, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    · rw [Fin.sum_univ_three]
      simp only [c, w, a, β, κ, θ, Option.elim, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_sub]
      ring
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [Fin.sum_univ_three]
      simp only [c, w, a, β, κ, θ, Option.elim, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, id]
      ring
  -- the two main terms
  have hσ0 : boxAvg ℓ 0 = 1 := boxAvg_zero hℓ
  have hAm : ∑ z ∈ S, D z * cexp (z * u₀) * boxAvg ℓ (z - z₀) ^ 2 =
      P + ∑ z ∈ S.erase z₀, D z * cexp (z * u₀) * boxAvg ℓ (z - z₀) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ hz₀, sub_self, hσ0, one_pow, mul_one]
  have hAp : ∑ z ∈ S, D z * cexp (z * u₀) * boxAvg ℓ (z - conj z₀) ^ 2 =
      conj P + ∑ z ∈ S.erase (conj z₀), D z * cexp (z * u₀) * boxAvg ℓ (z - conj z₀) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ hz₀', sub_self, hσ0, one_pow, mul_one, hD, hPdef, map_mul,
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  have hmain : ω / 2 * conj P + conj ω / 2 * P = -(‖P‖ : ℂ) := by
    have hPP : P * conj P = ((‖P‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hPc : (‖P‖ : ℂ) ≠ 0 := by exact_mod_cast hPn.ne'
    rw [hω, map_neg, map_div₀, Complex.conj_ofReal]
    field_simp
    rw [hPP]; push_cast; ring
  -- the constant term
  have hKc : ‖(K : ℂ) * (boxAvg ℓ (-(z₀.re : ℂ)) ^ 2 + ω / 2 * boxAvg ℓ (-(conj z₀)) ^ 2 +
      conj ω / 2 * boxAvg ℓ (-z₀) ^ 2)‖ ≤ 2 * K * Real.exp (|z₀.re| * ℓ) := by
    have hb : ∀ q : ℂ, q.re = -z₀.re → ‖boxAvg ℓ q‖ ^ 2 ≤ Real.exp (|z₀.re| * ℓ) := fun q hq => by
      have := norm_boxAvg_sq_le_exp hℓ q; rwa [hq, abs_neg] at this
    have h1 := hb (-(z₀.re : ℂ)) (by simp)
    have h2 := hb (-(conj z₀)) (by simp)
    have h3 := hb (-z₀) (by simp)
    have hωc : ‖conj ω‖ = 1 := by rw [Complex.norm_conj, hωn]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hK]
    have hin : ‖boxAvg ℓ (-(z₀.re : ℂ)) ^ 2 + ω / 2 * boxAvg ℓ (-(conj z₀)) ^ 2 +
        conj ω / 2 * boxAvg ℓ (-z₀) ^ 2‖ ≤ 2 * Real.exp (|z₀.re| * ℓ) := by
      refine norm_add₃_le.trans ?_
      rw [norm_mul, norm_mul, norm_div, norm_div, hωn, hωc, norm_pow, norm_pow, norm_pow,
        Complex.norm_ofNat]
      linarith
    calc K * ‖_‖ ≤ K * (2 * Real.exp (|z₀.re| * ℓ)) := mul_le_mul_of_nonneg_left hin hK
      _ = 2 * K * Real.exp (|z₀.re| * ℓ) := by ring
  -- assemble
  rw [hval, hAm, hAp] at hpos
  have hsplit : ω / 2 * (conj P + ∑ z ∈ S.erase (conj z₀),
        D z * cexp (z * u₀) * boxAvg ℓ (z - conj z₀) ^ 2) +
      conj ω / 2 * (P + ∑ z ∈ S.erase z₀, D z * cexp (z * u₀) * boxAvg ℓ (z - z₀) ^ 2) =
      -(‖P‖ : ℂ) + (ω / 2 * ∑ z ∈ S.erase (conj z₀),
        D z * cexp (z * u₀) * boxAvg ℓ (z - conj z₀) ^ 2 +
        conj ω / 2 * ∑ z ∈ S.erase z₀, D z * cexp (z * u₀) * boxAvg ℓ (z - z₀) ^ 2) := by
    rw [← hmain]; ring
  have hhalf : ‖ω / 2‖ = 1 / 2 := by rw [norm_div, hωn, Complex.norm_ofNat]
  have hhalf' : ‖conj ω / 2‖ = 1 / 2 := by
    rw [norm_div, Complex.norm_conj, hωn, Complex.norm_ofNat]
  have n₀ := norm_sum_le S fun z => D z * cexp (z * u₀) * boxAvg ℓ (z - z₀.re) ^ 2
  have np := norm_sum_le (S.erase (conj z₀)) fun z => D z * cexp (z * u₀) *
    boxAvg ℓ (z - conj z₀) ^ 2
  have nm := norm_sum_le (S.erase z₀) fun z => D z * cexp (z * u₀) * boxAvg ℓ (z - z₀) ^ 2
  set X₀ := ∑ z ∈ S, D z * cexp (z * u₀) * boxAvg ℓ (z - z₀.re) ^ 2
  set Xp := ∑ z ∈ S.erase (conj z₀), D z * cexp (z * u₀) * boxAvg ℓ (z - conj z₀) ^ 2
  set Xm := ∑ z ∈ S.erase z₀, D z * cexp (z * u₀) * boxAvg ℓ (z - z₀) ^ 2
  set Kc := (K : ℂ) * (boxAvg ℓ (-(z₀.re : ℂ)) ^ 2 + ω / 2 * boxAvg ℓ (-(conj z₀)) ^ 2 +
      conj ω / 2 * boxAvg ℓ (-z₀) ^ 2)
  have hre : (Kc + (X₀ + ω / 2 * (conj P + Xp) + conj ω / 2 * (P + Xm))).re =
      Kc.re + X₀.re - ‖P‖ + (ω / 2 * Xp).re + (conj ω / 2 * Xm).re := by
    have e : Kc + (X₀ + ω / 2 * (conj P + Xp) + conj ω / 2 * (P + Xm)) =
        Kc + X₀ + (ω / 2 * (conj P + Xp) + conj ω / 2 * (P + Xm)) := by ring
    rw [e, hsplit]
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    ring
  rw [hre] at hpos
  have b1 := Complex.re_le_norm Kc
  have b2 := Complex.re_le_norm X₀
  have b3 : (ω / 2 * Xp).re ≤ Rp / 2 := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, hhalf]; linarith
  have b4 : (conj ω / 2 * Xm).re ≤ Rm / 2 := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, hhalf']; linarith
  linarith

/-! ### Separated reals -/

/-- **Separated reals.** If `A ∪ {t}` is `g`-separated, then `Σ_{a ∈ A} (a − t)⁻² ≤ 4/g²`: the
`n`-th point on each side of `t` lies at distance at least `ng`, and `Σ 1/n² = π²/6 < 2`. -/
theorem sum_inv_sq_le_of_separated {A : Finset ℝ} {t g : ℝ} (hg : 0 < g) (htA : t ∉ A)
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → g ≤ |a - a'|) (ht : ∀ a ∈ A, g ≤ |a - t|) :
    ∑ a ∈ A, 1 / (a - t) ^ 2 ≤ 4 / g ^ 2 := by
  classical
  set B : Finset ℝ := insert t A with hB
  let γ : B → ℝ := fun x => x.1
  have hsep : ∀ j l : B, j ≠ l → g ≤ |γ j - γ l| := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hne : x ≠ y := fun h => hxy (Subtype.ext h)
    simp only [γ]
    rcases Finset.mem_insert.mp hx with rfl | hx' <;> rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact absurd rfl hne
    · rw [abs_sub_comm]; exact ht y hy'
    · exact ht x hx'
    · exact hA x hx' y hy' hne
  have hψ0 : ∀ x, g ≤ x → 0 ≤ 1 / x ^ 2 := fun x _ => by positivity
  have hψmono : ∀ x y, g ≤ x → x ≤ y → 1 / y ^ 2 ≤ 1 / x ^ 2 := fun x y hx hxy =>
    one_div_le_one_div_of_le (by have : 0 < x := by linarith
                                 positivity) (pow_le_pow_left₀ (by linarith) hxy 2)
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using h
  have hψs : HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * g) ^ 2) (Real.pi ^ 2 / 6 / g ^ 2) := by
    have hfun : (fun n : ℕ => 1 / (((n : ℝ) + 1) * g) ^ 2) =
        fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 / g ^ 2 := by
      funext n; rw [mul_pow, div_div]
    rw [hfun]; exact hz.div_const _
  have key := sum_offDiag_le_two_tsum γ hg hsep hψ0 hψmono hψs.summable
    ⟨t, Finset.mem_insert_self t A⟩
  rw [hψs.tsum_eq] at key
  have hL : ∑ l ∈ Finset.univ.filter (· ≠ (⟨t, Finset.mem_insert_self t A⟩ : B)),
      1 / |γ ⟨t, Finset.mem_insert_self t A⟩ - γ l| ^ 2 = ∑ a ∈ A, 1 / (a - t) ^ 2 := by
    rw [Finset.sum_filter]
    have e : ∀ l : B, (if l ≠ (⟨t, Finset.mem_insert_self t A⟩ : B) then
        1 / |γ ⟨t, Finset.mem_insert_self t A⟩ - γ l| ^ 2 else 0) =
        (fun x : ℝ => if x ≠ t then 1 / (x - t) ^ 2 else 0) l.1 := fun l => by
      simp only [γ, ne_eq, Subtype.ext_iff, sq_abs]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_coe_sort B
      (fun x : ℝ => if x ≠ t then 1 / (x - t) ^ 2 else 0), ← Finset.sum_filter, hB,
      Finset.filter_insert, if_neg (by simp)]
    exact Finset.sum_congr (Finset.filter_true_of_mem fun a ha (h : a = t) => htA (h ▸ ha))
      fun _ _ => rfl
  rw [hL] at key
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  calc ∑ a ∈ A, 1 / (a - t) ^ 2 ≤ 2 * (Real.pi ^ 2 / 6 / g ^ 2) := key
    _ ≤ 2 * (2 / g ^ 2) := by gcongr
    _ = 4 / g ^ 2 := by ring

/-- **Separated ordinates up to reflection.** If distinct points of `S` that are not reflections
`z' = −z̄` of each other have ordinates `g` apart, and ordinates different from `t` are `g` apart
from `t`, then `Σ_{Im z ≠ t} (Im z − t)⁻² ≤ 8/g²`: on each half `Re z ≥ 0`, `Re z < 0` the ordinate
is injective. -/
theorem sum_inv_sq_im_le {S : Finset ℂ} {t g : ℝ} (hg : 0 < g)
    (hS : ∀ z ∈ S, ∀ z' ∈ S, z' ≠ z → z' ≠ -conj z → g ≤ |z.im - z'.im|)
    (ht : ∀ z ∈ S, z.im ≠ t → g ≤ |z.im - t|) :
    ∑ z ∈ S.filter (fun z => z.im ≠ t), 1 / (z.im - t) ^ 2 ≤ 8 / g ^ 2 := by
  classical
  have half : ∀ (p : ℂ → Prop) [DecidablePred p],
      (∀ z z', p z → p z' → z' = -conj z → z' = z) →
      ∑ z ∈ (S.filter (fun z => z.im ≠ t)).filter p, 1 / (z.im - t) ^ 2 ≤ 4 / g ^ 2 := by
    intro p _ hp
    set Q := (S.filter (fun z => z.im ≠ t)).filter p with hQ
    have memQ : ∀ z ∈ Q, z ∈ S ∧ z.im ≠ t ∧ p z := fun z hz => by
      rw [hQ, Finset.mem_filter, Finset.mem_filter] at hz; exact ⟨hz.1.1, hz.1.2, hz.2⟩
    have hinj : Set.InjOn Complex.im Q := by
      intro z hz z' hz' h
      by_contra hne
      have h1 := memQ z hz
      have h2 := memQ z' hz'
      by_cases hr : z' = -conj z
      · exact hne (hp z z' h1.2.2 h2.2.2 hr).symm
      · have := hS z h1.1 z' h2.1 (Ne.symm hne) hr
        rw [show z.im - z'.im = 0 by rw [h]; ring, abs_zero] at this
        linarith
    rw [← Finset.sum_image (f := fun a : ℝ => 1 / (a - t) ^ 2) hinj]
    refine sum_inv_sq_le_of_separated hg ?_ ?_ ?_
    · intro hm
      obtain ⟨z, hz, hzt⟩ := Finset.mem_image.mp hm
      exact (memQ z hz).2.1 hzt
    · intro a ha a' ha' hne
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp ha'
      have hzz : z' ≠ z := fun h => hne (by rw [h])
      by_cases hr : z' = -conj z
      · exact absurd (hp z z' (memQ z hz).2.2 (memQ z' hz').2.2 hr) hzz
      · exact hS z (memQ z hz).1 z' (memQ z' hz').1 hzz hr
    · intro a ha
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
      exact ht z (memQ z hz).1 (memQ z hz).2.1
  have h1 := half (fun z => 0 ≤ z.re) fun z z' hz hz' hr => by
    have hre : z'.re = -z.re := by rw [hr]; simp
    have h0 : z.re = 0 := by linarith
    rw [hr]; apply Complex.ext <;> simp [h0]
  have h2 := half (fun z => ¬ 0 ≤ z.re) fun z z' hz hz' hr => by
    have hre : z'.re = -z.re := by rw [hr]; simp
    exact absurd (by linarith [not_le.mp hz, not_le.mp hz'] : False) id
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun z => 0 ≤ z.re)]
  calc _ ≤ 4 / g ^ 2 + 4 / g ^ 2 := add_le_add h1 h2
    _ = 8 / g ^ 2 := by ring

/-! ### Separated ordinates -/

/-- The exponents `z = ρ − ½` of the zeros and of their conjugates. -/
def zeroExps (Z : ZeroConfig) : Set ℂ :=
  {z | 1 / 2 + z ∈ Z.carrier ∨ 1 / 2 + conj z ∈ Z.carrier}

/-- **Separated ordinates.** Two exponents that are neither equal nor reflections `z' = −z̄` of each
other have ordinates at least `δ` apart: each ordinate carries one zero up to reflection, and the
distinct ordinates, taken with both signs, are `δ`-separated. -/
def SeparatedOrdinates (Z : ZeroConfig) (δ : ℝ) : Prop :=
  ∀ z ∈ zeroExps Z, ∀ z' ∈ zeroExps Z, z' ≠ z → z' ≠ -conj z → δ ≤ |z.im - z'.im|

/-- The weight `|D_z| e^{Re z · u}` of the exponent `z` in the cubic spline trace at log-scale `u`. -/
def expWeight (Z : ZeroConfig) (u : ℝ) (z : ℂ) : ℝ :=
  ‖evenCoeff Z (boxSpline 1 3) z‖ * Real.exp (z.re * u)

section Config

variable {Z : ZeroConfig}

theorem conj_mem_zeroExps {z : ℂ} (hz : z ∈ zeroExps Z) : conj z ∈ zeroExps Z := by
  rcases hz with h | h
  · exact Or.inr (by rwa [Complex.conj_conj])
  · exact Or.inl h

theorem abs_re_le_of_mem_zeroExps {z : ℂ} (hz : z ∈ zeroExps Z) : |z.re| ≤ 1 / 2 := by
  rcases hz with h | h
  · have h2 := Z.strip _ h
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    rw [e] at h2
    exact abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · have h2 := Z.strip _ h
    have e : (1 / 2 + conj z).re = 1 / 2 + z.re := by simp
    rw [e] at h2
    exact abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩

theorem im_ne_zero_of_mem_zeroExps (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {z : ℂ}
    (hz : z ∈ zeroExps Z) : z.im ≠ 0 := by
  rcases hz with h | h
  · have := hnoreal _ h; simpa using this
  · have := hnoreal _ h; simpa using this

/-- Conjugate exponents are separated too: `|Im z| ≥ δ/2`. -/
theorem half_le_abs_im (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {δ : ℝ}
    (hsep : SeparatedOrdinates Z δ) {z : ℂ} (hz : z ∈ zeroExps Z) : δ / 2 ≤ |z.im| := by
  have him := im_ne_zero_of_mem_zeroExps hnoreal hz
  have h1 : conj z ≠ z := fun h => him (by have := congrArg Complex.im h; simp at this; linarith)
  have h2 : conj z ≠ -conj z := fun h => him (by
    have := congrArg Complex.im h; simp at this; linarith)
  have h := hsep z hz (conj z) (conj_mem_zeroExps hz) h1 h2
  rw [Complex.conj_im, sub_neg_eq_add, ← two_mul, abs_mul, abs_two] at h
  linarith

theorem expWeight_add (u s : ℝ) (z : ℂ) :
    expWeight Z (u + s) z = expWeight Z u z * Real.exp (z.re * s) := by
  unfold expWeight; rw [mul_add, Real.exp_add]; ring

theorem expWeight_nonneg (u : ℝ) (z : ℂ) : 0 ≤ expWeight Z u z := by
  unfold expWeight; positivity

theorem expWeight_le (u : ℝ) (z : ℂ) :
    expWeight Z u z ≤ ‖evenCoeff Z (boxSpline 1 3) z‖ * Real.exp (|u| / 2) := by
  unfold expWeight
  by_cases h : evenCoeff Z (boxSpline 1 3) z = 0
  · simp [h]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hr := abs_re_le_of_mem_zeroExps (mem_of_evenCoeff_ne_zero h)
  calc z.re * u ≤ |z.re * u| := le_abs_self _
    _ = |z.re| * |u| := abs_mul _ _
    _ ≤ 1 / 2 * |u| := mul_le_mul_of_nonneg_right hr (abs_nonneg _)
    _ = |u| / 2 := by ring

theorem summable_expWeight (hZ : TemperedConfig Z) (u : ℝ) : Summable (expWeight Z u) :=
  Summable.of_nonneg_of_le (expWeight_nonneg u) (expWeight_le u)
    ((summable_norm_evenCoeff_spline hZ).mul_right _)

theorem norm_term_eq (z : ℂ) (u : ℝ) (q : ℂ) :
    ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u) * q‖ = expWeight Z u z * ‖q‖ := by
  rw [norm_mul, norm_mul, norm_cexp_mul_ofReal]; rfl

/-- **A dominant exponent.** At every scale some exponent has maximal weight. -/
theorem exists_dominant (hZ : TemperedConfig Z) (u : ℝ) {z₁ : ℂ}
    (hz₁ : evenCoeff Z (boxSpline 1 3) z₁ ≠ 0) :
    ∃ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 ∧ ∀ z', expWeight Z u z' ≤ expWeight Z u z := by
  have hpos : 0 < expWeight Z u z₁ := mul_pos (norm_pos_iff.mpr hz₁) (Real.exp_pos _)
  have hfin : {z | expWeight Z u z₁ ≤ expWeight Z u z}.Finite := by
    have h := (summable_expWeight hZ u).tendsto_cofinite_zero.eventually (gt_mem_nhds hpos)
    rw [Filter.eventually_cofinite] at h
    simpa [not_lt] using h
  obtain ⟨z, hz, hmax⟩ := Set.exists_max_image _ (expWeight Z u) hfin
    ⟨z₁, show expWeight Z u z₁ ≤ expWeight Z u z₁ from le_refl _⟩
  refine ⟨z, fun h0 => ?_, fun z' => ?_⟩
  · have h0' : expWeight Z u z = 0 := by simp [expWeight, h0]
    have : expWeight Z u z₁ ≤ expWeight Z u z := hz
    linarith
  · by_cases h : expWeight Z u z₁ ≤ expWeight Z u z'
    · exact hmax z' h
    · exact (not_le.mp h).le.trans hz

/-- The supremum `b` of the depths `Re z` of the exponents. -/
theorem exists_depth_sup {z₁ : ℂ} (hz₁ : evenCoeff Z (boxSpline 1 3) z₁ ≠ 0) :
    ∃ b : ℝ, (∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re ≤ b) ∧
      ∀ η > 0, ∃ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 ∧ b - η < z.re := by
  set s : Set ℝ := {x | ∃ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 ∧ z.re = x}
  have hne : s.Nonempty := ⟨z₁.re, z₁, hz₁, rfl⟩
  have hbdd : BddAbove s := ⟨1 / 2, by rintro _ ⟨z, hz, rfl⟩; exact re_le_of_evenCoeff_ne_zero hz⟩
  refine ⟨sSup s, fun z hz => le_csSup hbdd ⟨z, hz, rfl⟩, fun η hη => ?_⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne (by linarith : sSup s - η < sSup s)
  exact ⟨z, hz, hlt⟩

/-- **The dominant depth tends to the supremum.** Far out, every exponent of maximal weight has
depth at least `b − η`: an exponent of depth `> b − η/2` outweighs every shallower one by
`e^{(η/2)u}`. -/
theorem le_re_of_dominant (hZ : TemperedConfig Z) {b η : ℝ} (hη : 0 < η)
    {z₁ : ℂ} (hz₁ : evenCoeff Z (boxSpline 1 3) z₁ ≠ 0) (hz₁b : b - η / 2 < z₁.re) :
    ∃ U : ℝ, ∀ u, U ≤ u → ∀ z, (∀ z', expWeight Z u z' ≤ expWeight Z u z) → b - η ≤ z.re := by
  set A := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖
  have hs := summable_norm_evenCoeff_spline hZ
  have hle : ∀ z, ‖evenCoeff Z (boxSpline 1 3) z‖ ≤ A := fun z =>
    hs.le_tsum z fun _ _ => norm_nonneg _
  have hc : 0 < ‖evenCoeff Z (boxSpline 1 3) z₁‖ := norm_pos_iff.mpr hz₁
  have hA : 0 < A := lt_of_lt_of_le hc (hle z₁)
  set L := Real.log (A / ‖evenCoeff Z (boxSpline 1 3) z₁‖)
  refine ⟨max 1 (2 * L / η), fun u hu z hz => ?_⟩
  by_contra hlt
  push Not at hlt
  have hu0 : 0 < u := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hu)
  have hLu : L ≤ η / 2 * u := by
    have h := (le_max_right _ _).trans hu
    rw [div_le_iff₀ hη] at h; linarith
  have h1 : L < (z₁.re - z.re) * u := by nlinarith
  have h2 : A / ‖evenCoeff Z (boxSpline 1 3) z₁‖ < Real.exp ((z₁.re - z.re) * u) := by
    rw [← Real.exp_log (div_pos hA hc)]; exact Real.exp_lt_exp.mpr h1
  have h4 : Real.exp ((z₁.re - z.re) * u) ≤ A / ‖evenCoeff Z (boxSpline 1 3) z₁‖ := by
    rw [le_div_iff₀ hc, sub_mul, Real.exp_sub, div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos _)]
    calc Real.exp (z₁.re * u) * ‖evenCoeff Z (boxSpline 1 3) z₁‖ = expWeight Z u z₁ := by
          unfold expWeight; ring
      _ ≤ expWeight Z u z := hz z₁
      _ ≤ A * Real.exp (z.re * u) := mul_le_mul_of_nonneg_right (hle z) (Real.exp_pos _).le
  linarith

/-- **Drift on a window.** If `z₀` has maximal weight at `u₀` and depth `≥ b − η`, the maximal
exponent at `u₀ − ℓ` has depth `≥ b − η`, and all depths are `≤ b`, then on `[u₀ − ℓ, u₀ + ℓ]` no
weight exceeds that of `z₀` by more than `e^{ηℓ}`: `|D_z| e^{Re z · u₀} e^{|Re z − Re z₀| ℓ} ≤
e^{ηℓ} |D_{z₀}| e^{Re z₀ · u₀}`. Deeper exponents are compared at `u₀ + ℓ`, shallower at `u₀ − ℓ`. -/
theorem expWeight_drift_le {b η ℓ u₀ : ℝ} (hℓ : 0 ≤ ℓ)
    (hb : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re ≤ b) {z₀ z₁ z₂ : ℂ}
    (h₀ : ∀ z', expWeight Z u₀ z' ≤ expWeight Z u₀ z₀) (hz₀ : evenCoeff Z (boxSpline 1 3) z₀ ≠ 0)
    (hz₀b : b - η ≤ z₀.re)
    (h₁ : ∀ z', expWeight Z (u₀ + ℓ) z' ≤ expWeight Z (u₀ + ℓ) z₁)
    (hz₁ : evenCoeff Z (boxSpline 1 3) z₁ ≠ 0)
    (h₂ : ∀ z', expWeight Z (u₀ + -ℓ) z' ≤ expWeight Z (u₀ + -ℓ) z₂) (hz₂b : b - η ≤ z₂.re)
    (z : ℂ) :
    expWeight Z u₀ z * Real.exp (|z.re - z₀.re| * ℓ) ≤ Real.exp (η * ℓ) * expWeight Z u₀ z₀ := by
  have hw0 := expWeight_nonneg (Z := Z) u₀ z₀
  rcases le_or_gt z₀.re z.re with h | h
  · rw [abs_of_nonneg (by linarith)]
    have e : expWeight Z u₀ z * Real.exp ((z.re - z₀.re) * ℓ) =
        expWeight Z (u₀ + ℓ) z * Real.exp (-z₀.re * ℓ) := by
      rw [expWeight_add, mul_assoc, ← Real.exp_add]; ring_nf
    have e1 : expWeight Z (u₀ + ℓ) z₁ * Real.exp (-z₀.re * ℓ) =
        expWeight Z u₀ z₁ * Real.exp ((z₁.re - z₀.re) * ℓ) := by
      rw [expWeight_add, mul_assoc, ← Real.exp_add]; ring_nf
    have hx : (z₁.re - z₀.re) * ℓ ≤ η * ℓ :=
      mul_le_mul_of_nonneg_right (by linarith [hb z₁ hz₁]) hℓ
    calc expWeight Z u₀ z * Real.exp ((z.re - z₀.re) * ℓ)
        = expWeight Z (u₀ + ℓ) z * Real.exp (-z₀.re * ℓ) := e
      _ ≤ expWeight Z (u₀ + ℓ) z₁ * Real.exp (-z₀.re * ℓ) :=
          mul_le_mul_of_nonneg_right (h₁ z) (Real.exp_pos _).le
      _ = expWeight Z u₀ z₁ * Real.exp ((z₁.re - z₀.re) * ℓ) := e1
      _ ≤ expWeight Z u₀ z₀ * Real.exp (η * ℓ) :=
          mul_le_mul (h₀ z₁) (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le hw0
      _ = Real.exp (η * ℓ) * expWeight Z u₀ z₀ := by ring
  · rw [abs_of_neg (by linarith)]
    have e : expWeight Z u₀ z * Real.exp (-(z.re - z₀.re) * ℓ) =
        expWeight Z (u₀ + -ℓ) z * Real.exp (z₀.re * ℓ) := by
      rw [expWeight_add, mul_assoc, ← Real.exp_add]; ring_nf
    have e2 : expWeight Z (u₀ + -ℓ) z₂ * Real.exp (z₀.re * ℓ) =
        expWeight Z u₀ z₂ * Real.exp ((z₀.re - z₂.re) * ℓ) := by
      rw [expWeight_add, mul_assoc, ← Real.exp_add]; ring_nf
    have hx : (z₀.re - z₂.re) * ℓ ≤ η * ℓ :=
      mul_le_mul_of_nonneg_right (by linarith [hb z₀ hz₀]) hℓ
    calc expWeight Z u₀ z * Real.exp (-(z.re - z₀.re) * ℓ)
        = expWeight Z (u₀ + -ℓ) z * Real.exp (z₀.re * ℓ) := e
      _ ≤ expWeight Z (u₀ + -ℓ) z₂ * Real.exp (z₀.re * ℓ) :=
          mul_le_mul_of_nonneg_right (h₂ z) (Real.exp_pos _).le
      _ = expWeight Z u₀ z₂ * Real.exp ((z₀.re - z₂.re) * ℓ) := e2
      _ ≤ expWeight Z u₀ z₀ * Real.exp (η * ℓ) :=
          mul_le_mul (h₀ z₂) (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le hw0
      _ = Real.exp (η * ℓ) * expWeight Z u₀ z₀ := by ring

/-- **Leakage of one exponent.** Under the drift bound `B`, the term of `z` in the test at
`w` (`Re w = Re z − x₀`, `Im w ≠ 0`) is at most `B · 4/ℓ² · (Im w)⁻²`. -/
theorem norm_term_le {z w : ℂ} {u₀ ℓ x₀ B : ℝ} (hℓ : 0 < ℓ) (hw : w.im ≠ 0)
    (hwre : w.re = z.re - x₀) (hdrift : expWeight Z u₀ z * Real.exp (|z.re - x₀| * ℓ) ≤ B) :
    ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ w ^ 2‖ ≤
      B * (4 / ℓ ^ 2) * (1 / w.im ^ 2) := by
  have hw0 : w ≠ 0 := fun h => hw (by rw [h, Complex.zero_im])
  rw [norm_term_eq, norm_pow]
  have hσ := norm_boxAvg_sq_le hℓ hw0
  rw [hwre] at hσ
  have him : w.im ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm w) 2
  have hq : 4 / (‖w‖ * ℓ) ^ 2 ≤ 4 / ℓ ^ 2 * (1 / w.im ^ 2) := by
    rw [mul_pow, div_mul_div_comm, mul_one, mul_comm (ℓ ^ 2)]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right him (by positivity))
  calc expWeight Z u₀ z * ‖boxAvg ℓ w‖ ^ 2
      ≤ expWeight Z u₀ z * (Real.exp (|z.re - x₀| * ℓ) * (4 / ℓ ^ 2 * (1 / w.im ^ 2))) :=
        mul_le_mul_of_nonneg_left (hσ.trans (mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le))
          (expWeight_nonneg _ _)
    _ = expWeight Z u₀ z * Real.exp (|z.re - x₀| * ℓ) * (4 / ℓ ^ 2 * (1 / w.im ^ 2)) := by ring
    _ ≤ B * (4 / ℓ ^ 2 * (1 / w.im ^ 2)) :=
        mul_le_mul_of_nonneg_right hdrift (by positivity)
    _ = B * (4 / ℓ ^ 2) * (1 / w.im ^ 2) := by ring

/-- **The zero-frequency leakage.** -/
theorem sum_term_zero_le (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : SeparatedOrdinates Z δ) {S : Finset ℂ} (hS : ∀ z ∈ S, z ∈ zeroExps Z)
    {u₀ ℓ x₀ B : ℝ} (hℓ : 0 < ℓ)
    (hdrift : ∀ z, expWeight Z u₀ z * Real.exp (|z.re - x₀| * ℓ) ≤ B) :
    ∑ z ∈ S, ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - x₀) ^ 2‖ ≤
      B * (4 / ℓ ^ 2) * (32 / δ ^ 2) := by
  have hB : 0 ≤ B :=
    le_trans (mul_nonneg (expWeight_nonneg _ _) (Real.exp_pos _).le) (hdrift 0)
  have hterm : ∀ z ∈ S, ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - x₀) ^ 2‖ ≤
      B * (4 / ℓ ^ 2) * (1 / (z.im - 0) ^ 2) := fun z hz => by
    have hi : (z - (x₀ : ℂ)).im = z.im - 0 := by rw [Complex.sub_im, Complex.ofReal_im]
    have hw : (z - (x₀ : ℂ)).im ≠ 0 := by
      rw [hi, sub_zero]; exact im_ne_zero_of_mem_zeroExps hnoreal (hS z hz)
    have h := norm_term_le (Z := Z) (w := z - x₀) hℓ hw (by simp) (hdrift z)
    rwa [hi] at h
  have hcount := sum_inv_sq_im_le (S := S) (t := 0) (half_pos hδ)
    (fun z hz z' hz' h1 h2 => le_trans (by linarith) (hsep z (hS z hz) z' (hS z' hz') h1 h2))
    (fun z hz _ => by rw [sub_zero]; exact half_le_abs_im hnoreal hsep (hS z hz))
  rw [Finset.filter_true_of_mem fun z hz => im_ne_zero_of_mem_zeroExps hnoreal (hS z hz)]
    at hcount
  calc _ ≤ ∑ z ∈ S, B * (4 / ℓ ^ 2) * (1 / (z.im - 0) ^ 2) := Finset.sum_le_sum hterm
    _ = B * (4 / ℓ ^ 2) * ∑ z ∈ S, 1 / (z.im - 0) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ B * (4 / ℓ ^ 2) * (8 / (δ / 2) ^ 2) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = B * (4 / ℓ ^ 2) * (32 / δ ^ 2) := by ring

/-- **The leakage at a dominant ordinate.** The exponents of other ordinates leak
`O(B/(δℓ)²)`; the only exponent of the same ordinate is the reflection `−z̄_m`, damped by
`e^{−2 Re z_m (u₀ − ℓ)}`. -/
theorem sum_term_erase_le {δ : ℝ} (hδ : 0 < δ) (hsep : SeparatedOrdinates Z δ) {S : Finset ℂ}
    (hS : ∀ z ∈ S, z ∈ zeroExps Z) {zm : ℂ} (hzm : zm ∈ zeroExps Z) (hxm : 0 ≤ zm.re)
    {u₀ ℓ B : ℝ} (hℓ : 0 < ℓ)
    (hdrift : ∀ z, expWeight Z u₀ z * Real.exp (|z.re - zm.re| * ℓ) ≤ B) :
    ∑ z ∈ S.erase zm, ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - zm) ^ 2‖ ≤
      B * (4 / ℓ ^ 2) * (8 / δ ^ 2) + expWeight Z u₀ zm * Real.exp (-(2 * zm.re) * (u₀ - ℓ)) := by
  classical
  have hB : 0 ≤ B :=
    le_trans (mul_nonneg (expWeight_nonneg _ _) (Real.exp_pos _).le) (hdrift 0)
  set f : ℂ → ℝ := fun z =>
    ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u₀) * boxAvg ℓ (z - zm) ^ 2‖
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun z => z.im ≠ zm.im)]
  have hS' : ∀ z ∈ S.erase zm, z ∈ zeroExps Z := fun z hz => hS z (Finset.mem_of_mem_erase hz)
  -- other ordinates
  have h1 : ∑ z ∈ (S.erase zm).filter (fun z => z.im ≠ zm.im), f z ≤
      B * (4 / ℓ ^ 2) * (8 / δ ^ 2) := by
    have hterm : ∀ z ∈ (S.erase zm).filter (fun z => z.im ≠ zm.im),
        f z ≤ B * (4 / ℓ ^ 2) * (1 / (z.im - zm.im) ^ 2) := fun z hz => by
      have hne := (Finset.mem_filter.mp hz).2
      have hw : (z - zm).im ≠ 0 := by rw [Complex.sub_im]; exact sub_ne_zero.mpr hne
      have h := norm_term_le (Z := Z) (w := z - zm) (x₀ := zm.re) hℓ hw (by simp) (hdrift z)
      rw [Complex.sub_im] at h
      exact h
    have hcount := sum_inv_sq_im_le (S := S.erase zm) (t := zm.im) hδ
      (fun z hz z' hz' h1 h2 => hsep z (hS' z hz) z' (hS' z' hz') h1 h2)
      (fun z hz hne => by
        have h := hsep zm hzm z (hS' z hz)
          (fun h => hne (by rw [h])) (fun h => hne (by rw [h]; simp))
        rwa [abs_sub_comm] at h)
    calc _ ≤ ∑ z ∈ (S.erase zm).filter (fun z => z.im ≠ zm.im),
          B * (4 / ℓ ^ 2) * (1 / (z.im - zm.im) ^ 2) := Finset.sum_le_sum hterm
      _ = B * (4 / ℓ ^ 2) * ∑ z ∈ (S.erase zm).filter (fun z => z.im ≠ zm.im),
          1 / (z.im - zm.im) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ B * (4 / ℓ ^ 2) * (8 / δ ^ 2) := mul_le_mul_of_nonneg_left hcount (by positivity)
  -- the same ordinate: only the reflection
  have h2 : ∑ z ∈ (S.erase zm).filter (fun z => ¬ z.im ≠ zm.im), f z ≤
      expWeight Z u₀ zm * Real.exp (-(2 * zm.re) * (u₀ - ℓ)) := by
    have hsub : (S.erase zm).filter (fun z => ¬ z.im ≠ zm.im) ⊆ {-conj zm} := by
      intro z hz
      obtain ⟨hzS, hzi⟩ := Finset.mem_filter.mp hz
      push Not at hzi
      rw [Finset.mem_singleton]
      by_contra hr
      have h := hsep zm hzm z (hS' z hzS) (Finset.ne_of_mem_erase hzS) hr
      rw [hzi, sub_self, abs_zero] at h
      linarith
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _).trans ?_
    rw [Finset.sum_singleton, norm_term_eq, norm_pow]
    have hσ := norm_boxAvg_sq_le_exp hℓ (-conj zm - zm)
    have hre : |(-conj zm - zm).re| = 2 * zm.re := by
      rw [show (-conj zm - zm).re = -(2 * zm.re) by
        rw [Complex.sub_re, Complex.neg_re, Complex.conj_re]; ring, abs_neg,
        abs_of_nonneg (by linarith)]
    rw [hre] at hσ
    have hw : expWeight Z u₀ (-conj zm) = expWeight Z u₀ zm * Real.exp (-(2 * zm.re) * u₀) := by
      unfold expWeight
      rw [evenCoeff_neg_conj Z (contDiff_boxSpline (r := 1) one_pos 2).continuous
        (hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)),
        Complex.norm_conj, mul_assoc, ← Real.exp_add]
      congr 2; simp; ring
    rw [hw]
    calc expWeight Z u₀ zm * Real.exp (-(2 * zm.re) * u₀) * ‖boxAvg ℓ (-conj zm - zm)‖ ^ 2
        ≤ expWeight Z u₀ zm * Real.exp (-(2 * zm.re) * u₀) * Real.exp (2 * zm.re * ℓ) :=
          mul_le_mul_of_nonneg_left hσ (mul_nonneg (expWeight_nonneg _ _) (Real.exp_pos _).le)
      _ = expWeight Z u₀ zm * Real.exp (-(2 * zm.re) * (u₀ - ℓ)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  linarith

/-- Every zero off the line gives an exponent of positive depth with nonzero coefficient. -/
theorem exists_pos_re_evenCoeff_ne_zero {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ Z.carrier) (hre : ρ₁.re ≠ 1 / 2) :
    ∃ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 ∧ 0 < z.re := by
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  have key : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re →
      ∃ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 ∧ 0 < z.re := fun ρ hρ h =>
    ⟨ρ - 1 / 2, evenCoeff_sub_half_ne_zero_of_conj_symm Z hb3.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero h.ne')), by simp; linarith⟩
  rcases lt_or_gt_of_ne hre with h | h
  · refine key _ (Z.reflect_mem ρ₁ hρ₁) ?_
    have : (Zeta23.reflect ρ₁).re = 1 - ρ₁.re := by simp [Zeta23.reflect]
    linarith
  · exact key ρ₁ hρ₁ h

/-- **Finite truncation.** On scales `|u| ≤ R`, finitely many exponents carry the trace up to `ε`,
uniformly. -/
theorem exists_finset_trace_approx (hZ : TemperedConfig Z) {ε : ℝ} (R : ℝ) (hε : 0 < ε) :
    ∃ S₀ : Finset ℂ, ∀ S : Finset ℂ, S₀ ⊆ S → ∀ u : ℝ, |u| ≤ R →
      ‖((2 * (lagStructure Z (boxSpline 1 3) u).re : ℝ) : ℂ) -
        ∑ z ∈ S, evenCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ ≤ ε := by
  have hs := summable_norm_evenCoeff_spline hZ
  have hev := (tendsto_tsum_compl_atTop_zero fun z => ‖evenCoeff Z (boxSpline 1 3) z‖).eventually
    (gt_mem_nhds (div_pos hε (Real.exp_pos (R / 2))))
  obtain ⟨S₀, hS₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨S₀, fun S hS u hu => ?_⟩
  obtain ⟨hsum, heq⟩ := two_re_lagStructure_eq Z hZ (contDiff_boxSpline (r := 1) one_pos 2)
    (boxSpline_support (r := 1) one_pos 3) u
  rw [heq, ← hsum.sum_add_tsum_subtype_compl S, add_sub_cancel_left]
  have hnorm : ∀ z : ℂ, ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ = expWeight Z u z :=
    fun z => by rw [norm_mul, norm_cexp_mul_ofReal]; rfl
  have hsn : Summable fun z : {x // x ∉ S} =>
      ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ := by
    simp_rw [hnorm]; exact (summable_expWeight hZ u).subtype _
  have hle : ∀ z : {x // x ∉ S}, ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ ≤
      ‖evenCoeff Z (boxSpline 1 3) z‖ * Real.exp (R / 2) := fun z => by
    rw [hnorm]
    exact (expWeight_le u z).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _))
  calc ‖∑' z : {x // x ∉ S}, evenCoeff Z (boxSpline 1 3) z * cexp (z * u)‖
      ≤ ∑' z : {x // x ∉ S}, ‖evenCoeff Z (boxSpline 1 3) z * cexp (z * u)‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' z : {x // x ∉ S}, ‖evenCoeff Z (boxSpline 1 3) z‖ * Real.exp (R / 2) :=
        Summable.tsum_le_tsum hle hsn ((hs.subtype _).mul_right _)
    _ = (∑' z : {x // x ∉ S}, ‖evenCoeff Z (boxSpline 1 3) z‖) * Real.exp (R / 2) :=
        tsum_mul_right
    _ ≤ ε / Real.exp (R / 2) * Real.exp (R / 2) :=
        mul_le_mul_of_nonneg_right (hS₀ S hS).le (Real.exp_pos _).le
    _ = ε := by field_simp

/-- **The windowed width law for separated ordinates.** Let `Z` be tempered, without real zeros,
with `δ`-separated ordinates, and with a zero `ρ₁` of real part `> ½ + s`, `s ≥ 0`. For every `K` and
every `ℓ ≥ 40/δ`, far enough out every window `[u₀ − ℓ, u₀ + ℓ]` contains a scale with
`2 Re S(u) < −K e^{su}`.

The exponent `z₀` of maximal weight at `u₀` is tested by Landau's inequality on the window
(`norm_le_of_window_lower`) with `K' = (|K| + 1) e^{s(u₀ + ℓ)}`. Its weight `M₀` is at most
`(2/25 + 1/50) e^{ηℓ} M₀` of leakage from other ordinates, `M₀/4` from its reflection, and
`2K' e^{ℓ/2}`; with `ηℓ ≤ 1` this bounds `M₀`, while `M₀ e^{−su₀} ≥ |D_z| e^{(Re z − s)u₀} → ∞` for
`z = ρ₁ − ½`. -/
theorem exists_lt_exp_in_window_of_separatedOrdinates (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hsep : SeparatedOrdinates Z δ)
    {s : ℝ} (hs : 0 ≤ s) {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ Z.carrier) (hρ₁re : 1 / 2 + s < ρ₁.re) {ℓ : ℝ}
    (hℓ : 40 / δ ≤ ℓ) (K : ℝ) :
    ∃ U : ℝ, ∀ u₀, U ≤ u₀ → ∃ u ∈ Icc (u₀ - ℓ) (u₀ + ℓ),
      2 * (lagStructure Z (boxSpline 1 3) u).re < -(K * Real.exp (s * u)) := by
  set zp : ℂ := ρ₁ - 1 / 2 with hzpdef
  have hzp : evenCoeff Z (boxSpline 1 3) zp ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z (contDiff_boxSpline (r := 1) one_pos 2).continuous
      (hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3))
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₁
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  have hzpre : s < zp.re := by simp [zp]; linarith
  obtain ⟨b, hb, hbsup⟩ := exists_depth_sup hzp
  have hb0 : 0 < b := lt_of_le_of_lt hs (lt_of_lt_of_le hzpre (hb zp hzp))
  have hδℓ : 40 ≤ δ * ℓ := by rw [div_le_iff₀ hδ] at hℓ; linarith
  have hℓ0 : 0 < ℓ := by
    by_contra h; push Not at h; nlinarith
  set η := min (b / 2) (1 / ℓ) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  have hηb : η ≤ b / 2 := min_le_left _ _
  have hηℓ : η * ℓ ≤ 1 :=
    calc η * ℓ ≤ 1 / ℓ * ℓ := mul_le_mul_of_nonneg_right (min_le_right _ _) hℓ0.le
      _ = 1 := by field_simp
  obtain ⟨z₁, hz₁, hz₁b⟩ := hbsup (η / 2) (half_pos hη)
  obtain ⟨U₁, hdom⟩ := le_re_of_dominant hZ hη hz₁ hz₁b
  set C : ℝ := 5 * (|K| + 1) * Real.exp (s * ℓ) * Real.exp (ℓ / 2) with hCdef
  have hgrow : Tendsto (fun u => expWeight Z u zp * Real.exp (-(s * u))) atTop atTop := by
    have e : (fun u => expWeight Z u zp * Real.exp (-(s * u))) =
        fun u => ‖evenCoeff Z (boxSpline 1 3) zp‖ * Real.exp ((zp.re - s) * u) := by
      funext u; unfold expWeight; rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [e]
    exact Tendsto.const_mul_atTop (norm_pos_iff.mpr hzp)
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith)))
  obtain ⟨U₃, hU₃⟩ := Filter.eventually_atTop.mp (hgrow.eventually_gt_atTop C)
  refine ⟨max (U₁ + ℓ) (max U₃ (ℓ + Real.log 4 / b)), fun u₀ hu₀ => ?_⟩
  have hu₁ : U₁ + ℓ ≤ u₀ := (le_max_left _ _).trans hu₀
  have hu₃ : U₃ ≤ u₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hu₀
  have hu₄ : ℓ + Real.log 4 / b ≤ u₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans hu₀
  have hlog4 : 0 ≤ Real.log 4 / b := div_nonneg (Real.log_nonneg (by norm_num)) hb0.le
  have hu0ℓ : 0 ≤ u₀ - ℓ := by linarith
  by_contra hall
  push Not at hall
  set K' : ℝ := (|K| + 1) * Real.exp (s * (u₀ + ℓ)) with hK'
  have hE1 : 1 ≤ Real.exp (s * (u₀ + ℓ)) := Real.one_le_exp (mul_nonneg hs (by linarith))
  have hK'0 : 0 ≤ K' := by positivity
  -- dominant exponents at `u₀`, `u₀ + ℓ`, `u₀ − ℓ`
  obtain ⟨z₀, hz₀, h₀⟩ := exists_dominant hZ u₀ hzp
  obtain ⟨zA, hzA, hA⟩ := exists_dominant hZ (u₀ + ℓ) hzp
  obtain ⟨zB, -, hB⟩ := exists_dominant hZ (u₀ + -ℓ) hzp
  have hz₀b : b - η ≤ z₀.re := hdom u₀ (by linarith) z₀ h₀
  have hzBb : b - η ≤ zB.re := hdom (u₀ + -ℓ) (by linarith) zB hB
  set M₀ := expWeight Z u₀ z₀ with hM₀
  set B := Real.exp (η * ℓ) * M₀ with hBdef
  have hdrift : ∀ z, expWeight Z u₀ z * Real.exp (|z.re - z₀.re| * ℓ) ≤ B :=
    expWeight_drift_le hℓ0.le hb h₀ hz₀ hz₀b hA hzA hB hzBb
  have hx₀ : b / 2 ≤ z₀.re := by linarith
  have hz₀E : z₀ ∈ zeroExps Z := mem_of_evenCoeff_ne_zero hz₀
  have hz₀'E : conj z₀ ∈ zeroExps Z := conj_mem_zeroExps hz₀E
  have hconj0 : evenCoeff Z (boxSpline 1 3) (conj z₀) ≠ 0 := by
    rw [evenCoeff_conj]; exact (map_ne_zero _).mpr hz₀
  -- truncation to finitely many exponents
  obtain ⟨S₀, hS₀⟩ := exists_finset_trace_approx hZ (|u₀| + ℓ) one_pos
  classical
  set S := (S₀ ∪ {z₀, conj z₀}).filter (fun z => evenCoeff Z (boxSpline 1 3) z ≠ 0) with hS
  have hSE : ∀ z ∈ S, z ∈ zeroExps Z := fun z hz =>
    mem_of_evenCoeff_ne_zero (Finset.mem_filter.mp hz).2
  have hz₀S : z₀ ∈ S := Finset.mem_filter.mpr ⟨by simp, hz₀⟩
  have hz₀'S : conj z₀ ∈ S := Finset.mem_filter.mpr ⟨by simp, hconj0⟩
  have hlow : ∀ v ∈ Icc (-ℓ) ℓ, -K' ≤
      (∑ z ∈ S, evenCoeff Z (boxSpline 1 3) z * cexp (z * ((u₀ + v : ℝ) : ℂ))).re := by
    intro v hv
    have hsumS : ∑ z ∈ S, evenCoeff Z (boxSpline 1 3) z * cexp (z * ((u₀ + v : ℝ) : ℂ)) =
        ∑ z ∈ S₀ ∪ {z₀, conj z₀}, evenCoeff Z (boxSpline 1 3) z * cexp (z * ((u₀ + v : ℝ) : ℂ)) :=
      Finset.sum_filter_of_ne fun z _ h => left_ne_zero_of_mul h
    have hR : |u₀ + v| ≤ |u₀| + ℓ :=
      (abs_add_le _ _).trans (by linarith [abs_le.mpr ⟨hv.1, hv.2⟩])
    have happ := hS₀ (S₀ ∪ {z₀, conj z₀}) Finset.subset_union_left (u₀ + v) hR
    have hK1 := hall (u₀ + v) ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hKe : K * Real.exp (s * (u₀ + v)) ≤ |K| * Real.exp (s * (u₀ + ℓ)) :=
      mul_le_mul (le_abs_self K) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by linarith [hv.2]) hs)) (Real.exp_pos _).le (abs_nonneg K)
    rw [hsumS]
    have hd := Complex.re_le_norm (((2 * (lagStructure Z (boxSpline 1 3) (u₀ + v)).re : ℝ) : ℂ) -
      ∑ z ∈ S₀ ∪ {z₀, conj z₀}, evenCoeff Z (boxSpline 1 3) z * cexp (z * ((u₀ + v : ℝ) : ℂ)))
    rw [Complex.sub_re, Complex.ofReal_re] at hd
    have hK'e : K' = |K| * Real.exp (s * (u₀ + ℓ)) + Real.exp (s * (u₀ + ℓ)) := by
      rw [hK']; ring
    linarith
  -- Landau's inequality and the leakage bounds
  have hL := norm_le_of_window_lower (D := evenCoeff Z (boxSpline 1 3)) hz₀S hz₀'S
    (evenCoeff_conj Z z₀) hℓ0 hK'0 hlow
  have hM : ‖evenCoeff Z (boxSpline 1 3) z₀ * cexp (z₀ * u₀)‖ = M₀ := by
    rw [norm_mul, norm_cexp_mul_ofReal]; rfl
  rw [hM] at hL
  have h0 := sum_term_zero_le hnoreal hδ hsep hSE hℓ0 hdrift
  have hm := sum_term_erase_le hδ hsep hSE hz₀E (by linarith) hℓ0 hdrift
  have hdrift' : ∀ z, expWeight Z u₀ z * Real.exp (|z.re - (conj z₀).re| * ℓ) ≤ B := by
    simpa only [Complex.conj_re] using hdrift
  have hp := sum_term_erase_le hδ hsep hSE hz₀'E (by rw [Complex.conj_re]; linarith) hℓ0 hdrift'
  have hwc : expWeight Z u₀ (conj z₀) = M₀ := by
    rw [hM₀]; unfold expWeight; rw [evenCoeff_conj, Complex.norm_conj, Complex.conj_re]
  rw [hwc, Complex.conj_re] at hp
  -- numerics
  have hM0 : 0 ≤ M₀ := expWeight_nonneg _ _
  have hB0 : 0 ≤ B := mul_nonneg (Real.exp_pos _).le hM0
  have h1600 : (1600 : ℝ) ≤ (δ * ℓ) ^ 2 := by nlinarith
  have hq0 : 4 / ℓ ^ 2 * (32 / δ ^ 2) ≤ 2 / 25 := by
    rw [show 4 / ℓ ^ 2 * (32 / δ ^ 2) = 128 / (δ * ℓ) ^ 2 by field_simp; ring]
    calc 128 / (δ * ℓ) ^ 2 ≤ 128 / 1600 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1600
      _ = 2 / 25 := by norm_num
  have hq1 : 4 / ℓ ^ 2 * (8 / δ ^ 2) ≤ 1 / 50 := by
    rw [show 4 / ℓ ^ 2 * (8 / δ ^ 2) = 32 / (δ * ℓ) ^ 2 by field_simp; ring]
    calc 32 / (δ * ℓ) ^ 2 ≤ 32 / 1600 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1600
      _ = 1 / 50 := by norm_num
  have t0 : B * (4 / ℓ ^ 2) * (32 / δ ^ 2) ≤ B * (2 / 25) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq0 hB0
  have t1 : B * (4 / ℓ ^ 2) * (8 / δ ^ 2) ≤ B * (1 / 50) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq1 hB0
  have hdec : Real.exp (-(2 * z₀.re) * (u₀ - ℓ)) ≤ 1 / 4 := by
    have hlog : Real.log 4 ≤ b * (u₀ - ℓ) := by
      have : Real.log 4 / b ≤ u₀ - ℓ := by linarith
      rwa [div_le_iff₀ hb0, mul_comm] at this
    have hle : -(2 * z₀.re) * (u₀ - ℓ) ≤ -Real.log 4 := by nlinarith
    calc Real.exp (-(2 * z₀.re) * (u₀ - ℓ)) ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr hle
      _ = 1 / 4 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have t2 : M₀ * Real.exp (-(2 * z₀.re) * (u₀ - ℓ)) ≤ M₀ * (1 / 4) :=
    mul_le_mul_of_nonneg_left hdec hM0
  have hBle : B ≤ 3 * M₀ := by
    have : Real.exp (η * ℓ) ≤ 3 :=
      (Real.exp_le_exp.mpr hηℓ).trans (by linarith [Real.exp_one_lt_d9])
    rw [hBdef]; exact mul_le_mul_of_nonneg_right this hM0
  have hKexp : 2 * K' * Real.exp (|z₀.re| * ℓ) ≤ 2 * K' * Real.exp (ℓ / 2) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have := abs_re_le_of_mem_zeroExps hz₀E
    nlinarith
  -- growth: `5 K' e^{ℓ/2} < M₀`
  have hgr : 5 * K' * Real.exp (ℓ / 2) < M₀ := by
    have h1 := hU₃ u₀ hu₃
    have h2 : expWeight Z u₀ zp * Real.exp (-(s * u₀)) * Real.exp (s * u₀) =
        expWeight Z u₀ zp := by rw [mul_assoc, ← Real.exp_add]; simp
    have h3 : 5 * K' * Real.exp (ℓ / 2) = C * Real.exp (s * u₀) := by
      rw [hK', hCdef, mul_add, Real.exp_add]; ring
    rw [h3]
    calc C * Real.exp (s * u₀) < expWeight Z u₀ zp * Real.exp (-(s * u₀)) * Real.exp (s * u₀) :=
          mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
      _ = expWeight Z u₀ zp := h2
      _ ≤ M₀ := h₀ zp
  have hKE : 0 ≤ K' * Real.exp (ℓ / 2) := by positivity
  linarith

/-- **Separated ordinates are seen in every window.** Let `Z` be tempered, without real zeros,
with `δ`-separated ordinates, and with a zero off the line. For every `K` and every `ℓ ≥ 40/δ`,
far enough out every window `[u₀ − ℓ, u₀ + ℓ]` contains a scale with `2 Re S(u) < −K`: the case
`s = 0` of `exists_lt_exp_in_window_of_separatedOrdinates`, after reflecting the zero to the right
of the line. -/
theorem exists_lt_in_window_of_separatedOrdinates (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hsep : SeparatedOrdinates Z δ)
    {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ Z.carrier) (hρ₁re : ρ₁.re ≠ 1 / 2) {ℓ : ℝ} (hℓ : 40 / δ ≤ ℓ) (K : ℝ) :
    ∃ U : ℝ, ∀ u₀, U ≤ u₀ → ∃ u ∈ Icc (u₀ - ℓ) (u₀ + ℓ),
      2 * (lagStructure Z (boxSpline 1 3) u).re < -K := by
  obtain ⟨ρ, hρ, hre⟩ : ∃ ρ ∈ Z.carrier, 1 / 2 + 0 < ρ.re := by
    rcases lt_or_gt_of_ne hρ₁re with h | h
    · refine ⟨_, Z.reflect_mem ρ₁ hρ₁, ?_⟩
      have : (Zeta23.reflect ρ₁).re = 1 - ρ₁.re := by simp [Zeta23.reflect]
      linarith
    · exact ⟨ρ₁, hρ₁, by linarith⟩
  obtain ⟨U, hU⟩ := exists_lt_exp_in_window_of_separatedOrdinates hZ hnoreal hδ hsep le_rfl hρ hre
    hℓ K
  refine ⟨U, fun u₀ hu₀ => ?_⟩
  obtain ⟨u, hu, hlt⟩ := hU u₀ hu₀
  exact ⟨u, hu, by simpa using hlt⟩

/-- **The width law on windows.** If `2 Re S ≥ −K e^{su}`, `s ≥ 0`, on a set containing a window of
length `80/δ` beyond every bound, every zero of a tempered configuration without real zeros and with
`δ`-separated ordinates has real part `≤ ½ + s`. -/
theorem re_le_of_bddBelow_exp_windows_of_separatedOrdinates (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hsep : SeparatedOrdinates Z δ)
    {s : ℝ} (hs : 0 ≤ s) {T : Set ℝ} (hT : ∀ U : ℝ, ∃ a, U ≤ a ∧ Icc a (a + 80 / δ) ⊆ T) {K : ℝ}
    (hK : ∀ u ∈ T, -(K * Real.exp (s * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + s := by
  intro ρ₁ hρ₁
  by_contra h
  push Not at h
  obtain ⟨U, hU⟩ := exists_lt_exp_in_window_of_separatedOrdinates hZ hnoreal hδ hsep hs hρ₁ h
    (le_refl (40 / δ)) K
  obtain ⟨a, ha, hsub⟩ := hT U
  have h40 : 0 < 40 / δ := by positivity
  have h80 : 80 / δ = 40 / δ + 40 / δ := by ring
  obtain ⟨u, hu, hlt⟩ := hU (a + 40 / δ) (by linarith)
  have hmem : u ∈ T := hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩
  linarith [hK u hmem]

/-- **Windows of length `80/δ` decide separated configurations.** If `T` contains a window of
length `80/δ` beyond every bound and `2 Re S ≥ −K` on `T`, every zero of a tempered configuration
without real zeros and with `δ`-separated ordinates lies on the line. -/
theorem onLine_of_bddBelow_windows_of_separatedOrdinates (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hsep : SeparatedOrdinates Z δ)
    {T : Set ℝ} (hT : ∀ U : ℝ, ∃ a, U ≤ a ∧ Icc a (a + 80 / δ) ⊆ T) {K : ℝ}
    (hK : ∀ u ∈ T, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  by_contra h
  push Not at h
  obtain ⟨ρ₁, hρ₁, hre⟩ := h
  obtain ⟨U, hU⟩ := exists_lt_in_window_of_separatedOrdinates hZ hnoreal hδ hsep hρ₁ hre
    (le_refl (40 / δ)) K
  obtain ⟨a, ha, hsub⟩ := hT U
  have h40 : 0 < 40 / δ := by positivity
  have h80 : 80 / δ = 40 / δ + 40 / δ := by ring
  obtain ⟨u, hu, hlt⟩ := hU (a + 40 / δ) (by linarith)
  have hmem : u ∈ T := hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩
  linarith [hK u hmem]

/-- From the integers to the reals: a lower bound at `log n`, `n ∈ D`, gives one at every `u ≥ 1`
with `⌊eᵘ⌋ ∈ D`, losing `4 Σ |c_z| |z|` (`norm_lagStructure_sub_le`). -/
theorem neg_le_of_floor_exp_mem (hZ : TemperedConfig Z) {D : Set ℕ} {K : ℝ}
    (hK : ∀ n ∈ D, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re) {u : ℝ}
    (hu1 : 1 ≤ u) (hn : ⌊Real.exp u⌋₊ ∈ D) :
    -(K + 4 * ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖) ≤
      2 * (lagStructure Z (boxSpline 1 3) u).re := by
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  set C := ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖ with hCdef
  have hC0 : 0 ≤ C := tsum_nonneg fun _ => by positivity
  set n := ⌊Real.exp u⌋₊ with hndef
  have hK1 := hK n hn
  have he : (2 : ℝ) ≤ Real.exp u := by have := Real.add_one_le_exp u; linarith
  have hn1 : Real.exp u < n + 1 := Nat.lt_floor_add_one _
  have hnle : (n : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos _).le
  have hnpos : (1 : ℝ) ≤ n := by linarith
  have hlogn : Real.log n ≤ u := by
    rw [← Real.log_exp u]; exact Real.log_le_log (by linarith) hnle
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnpos
  have hgap : u - Real.log n ≤ 1 / n := by
    have h1 : u ≤ Real.log (n + 1) := by
      rw [← Real.log_exp u]; exact Real.log_le_log (Real.exp_pos _) hn1.le
    have h2 : Real.log (n + 1) - Real.log n ≤ 1 / n := by
      have hn0 : (n : ℝ) ≠ 0 := (show (0 : ℝ) < n by linarith).ne'
      rw [← Real.log_div (show (0 : ℝ) < n + 1 by linarith).ne' hn0]
      have := Real.log_le_sub_one_of_pos
        (show 0 < ((n : ℝ) + 1) / n from div_pos (by linarith) (by linarith))
      have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by rw [div_sub_one hn0]; congr 1; ring
      linarith
    linarith
  have hL := norm_lagStructure_sub_le hZ hb3 (by positivity) hbs hlog0 hlogn
  have hfac : (u - Real.log n) * Real.exp (u / 2) ≤ 2 := by
    have hpos : 0 < Real.exp (u / 2) := Real.exp_pos _
    have hsq : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
      rw [← Real.exp_add]; ring_nf
    have h1 : 1 ≤ Real.exp (u / 2) := Real.one_le_exp (by linarith)
    have hn2 : Real.exp u ≤ 2 * n := by linarith
    calc (u - Real.log n) * Real.exp (u / 2) ≤ (1 / n) * Real.exp (u / 2) :=
          mul_le_mul_of_nonneg_right hgap hpos.le
      _ ≤ 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
          nlinarith
  have hdiff : |2 * (lagStructure Z (boxSpline 1 3) u).re -
      2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re| ≤ 4 * C := by
    rw [← mul_sub, abs_mul, abs_two, ← Complex.sub_re]
    have h1 := (Complex.abs_re_le_norm _).trans hL
    have h2 : C * (u - Real.log n) * Real.exp (u / 2) ≤ C * 2 := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hfac hC0
    linarith
  linarith [(abs_le.mp hdiff).1]

/-- **Integer windows of ratio `e^{80/δ}` decide separated configurations.** If `D ⊂ ℕ` contains
every integer of `[x, e^{80/δ} x]` for arbitrarily large `x`, a lower bound on the spline traces at
the degrees of `D` puts every zero of a tempered, real-zero-free configuration with `δ`-separated
ordinates on the line. -/
theorem onLine_of_bddBelow_integer_windows_of_separatedOrdinates (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hsep : SeparatedOrdinates Z δ)
    (D : Set ℕ)
    (hD : ∀ U : ℝ, ∃ x : ℕ, U ≤ x ∧ ∀ n : ℕ, x ≤ n → (n : ℝ) ≤ Real.exp (80 / δ) * x → n ∈ D)
    {K : ℝ} (hK : ∀ n ∈ D, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  refine onLine_of_bddBelow_windows_of_separatedOrdinates hZ hnoreal hδ hsep
    (T := {u | 1 ≤ u ∧ ⌊Real.exp u⌋₊ ∈ D}) ?_ (fun u hu => neg_le_of_floor_exp_mem hZ hK hu.1 hu.2)
  intro U
  obtain ⟨x, hx, hxD⟩ := hD (Real.exp (max U 1))
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlx : max U 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx; rwa [Real.log_exp] at this
  refine ⟨Real.log x, le_trans (le_max_left U 1) hlx, fun u hu => ⟨?_, ?_⟩⟩
  · linarith [hu.1, le_max_right U 1]
  · apply hxD
    · apply Nat.le_floor
      calc ((x : ℕ) : ℝ) = Real.exp (Real.log x) := (Real.exp_log hx0).symm
        _ ≤ Real.exp u := Real.exp_le_exp.mpr hu.1
    · calc (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos _).le
        _ ≤ Real.exp (Real.log x + 80 / δ) := Real.exp_le_exp.mpr hu.2
        _ = Real.exp (80 / δ) * x := by rw [Real.exp_add, Real.exp_log hx0]; ring

/-- **Growing windows force near-coincident ordinates.** An impure tempered configuration without
real zeros that is bounded below on a set containing arbitrarily long intervals arbitrarily far
out has no positive separation of ordinates. -/
theorem not_separatedOrdinates_of_bddBelow_long_intervals (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ Z.carrier) (hre : ρ₁.re ≠ 1 / 2)
    {T : Set ℝ} (hT : ∀ L U : ℝ, ∃ a, U ≤ a ∧ Icc a (a + L) ⊆ T) {K : ℝ}
    (hK : ∀ u ∈ T, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) {δ : ℝ} (hδ : 0 < δ) :
    ¬ SeparatedOrdinates Z δ := fun hsep =>
  hre (onLine_of_bddBelow_windows_of_separatedOrdinates hZ hnoreal hδ hsep
    (fun U => hT (80 / δ) U) hK ρ₁ hρ₁)

/-- **Runs of integers force near-coincident ordinates.** The same on the integers: if `D`
contains every integer of `[x, e^L x]` for arbitrarily large `x` and `L` and the traces are bounded
below at the degrees of `D`, an impure configuration has no positive separation of ordinates. -/
theorem not_separatedOrdinates_of_bddBelow_integer_runs (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ Z.carrier) (hre : ρ₁.re ≠ 1 / 2)
    (D : Set ℕ)
    (hD : ∀ L U : ℝ, ∃ x : ℕ, U ≤ x ∧ ∀ n : ℕ, x ≤ n → (n : ℝ) ≤ Real.exp L * x → n ∈ D)
    {K : ℝ} (hK : ∀ n ∈ D, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re) {δ : ℝ}
    (hδ : 0 < δ) : ¬ SeparatedOrdinates Z δ := fun hsep =>
  hre (onLine_of_bddBelow_integer_windows_of_separatedOrdinates hZ hnoreal hδ hsep D
    (fun U => hD (80 / δ) U) hK ρ₁ hρ₁)

end Config

end GaloisForLFunctions.SurfaceOfSpecZ
