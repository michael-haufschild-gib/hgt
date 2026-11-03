import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateHorizonAtTheFirstPrime

/-!
# The second stage is a weighted path

On a window of the second stage, `log 3 < A < log 4`, the folds by `ℓ₂ = log 2` and `ℓ₃ = log 3` link the
points of the window into finite orbit graphs. Ordering the window as
`−A < −ℓ₃ < −ℓ₂ < ℓ₂ − A < ℓ₃ − A < 0`, a point `x ∈ [−A, −ℓ₃]` is linked to `x + ℓ₂` (fold `2`) and to
`x + ℓ₃` (fold `3`), and `x + ℓ₃` to `x + ℓ₃ − ℓ₂` (fold `2`): the largest orbit graph is the path
`x + ℓ₂ —2— x —3— x + ℓ₃ —2— x + ℓ₃ − ℓ₂`. A path with edge weights `α, β, α` has spectral radius
`≤ 1` iff `α² + β ≤ 1`.

* **Path Picone inequality** (`two_abs_autocorr_le`): for any positive weight `h`, a fold correlation is
  bounded by the `h`-ratios of the window points it links (AM–GM with a ground state).
* **Second-stage bound** (`two_mul_abs_autocorr_add_le`): with the Perron weights of the path
  (`h = 1/α` on the two inner regions `[−A, −ℓ₃]`, `[ℓ₃ − A, 0]`, `1` elsewhere), for `α, β ≥ 0` with
  `α² + β ≤ 1`, `2α|c₂(H)| + 2β|c₃(H)| ≤ ‖H‖²`, `c_n(H) = ∫H(u)H(u + log n)`.
* **The Tate operators of the second stage** (`tateFunction_nonneg_secondStage`): `ρ_A(J_k) ≥ 0` as soon
  as `(2^k − 1)²/8 + (3^k − 1)/(2√3) ≤ 1`, i.e. for `k ≤ 1.19966…` (numerically this is the exact horizon:
  the alternating Perron vector of the path is extremal).
* **The arithmetic term of the second stage** (`abs_arith_secondStage_le`): `|w₂c₂ + w₃c₃| ≤ r‖H‖²` for
  every `r > 0` with `w₂² + 2rw₃ ≤ 4r²`, `w_n = Λ(n)/√n`; the least such `r` is
  `(w₃ + √(w₃² + 4w₂²))/4 ≈ 0.4505`, against `w₂ + w₃ ≈ 1.124` for the pointwise canonical density.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory MeasureTheory Set

variable {A : ℝ} {H : ℝ → ℝ}

/-! ### Picone inequality for one fold -/

/-- AM–GM with a ground state: `2|xy| ≤ (q/p)x² + (p/q)y²` for `p, q > 0`. -/
theorem two_abs_mul_le_ratio {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (x y : ℝ) :
    2 * |x * y| ≤ q / p * x ^ 2 + p / q * y ^ 2 := by
  rw [abs_mul, ← sq_abs x, ← sq_abs y]
  have h : q / p * |x| ^ 2 + p / q * |y| ^ 2 - 2 * (|x| * |y|) = (q * |x| - p * |y|) ^ 2 / (p * q) := by
    field_simp; ring
  have : 0 ≤ (q * |x| - p * |y|) ^ 2 / (p * q) := div_nonneg (sq_nonneg _) (mul_pos hp hq).le
  linarith

/-- The window gate `G(v) = h(v)` on the window, `0` off it. -/
def windowGate (A : ℝ) (h : ℝ → ℝ) (v : ℝ) : ℝ := (Icc (-A) 0).indicator h v

/-- **Path Picone inequality**: for a weight `1 ≤ h ≤ C`,
`2|∫H(u)H(u + ℓ)| ≤ ∫ (G(u + ℓ) + G(u − ℓ))/h(u) · H(u)²`. -/
theorem two_abs_autocorr_le (hH : IsWindowTest A H) {h : ℝ → ℝ} (hm : Measurable h) {C : ℝ}
    (h1 : ∀ u, 1 ≤ h u) (hC : ∀ u, h u ≤ C) (ℓ : ℝ) :
    2 * |∫ u, H u * H (u + ℓ)| ≤
      ∫ u, (windowGate A h (u + ℓ) + windowGate A h (u - ℓ)) / h u * H u ^ 2 := by
  have hc := hH.continuous
  have hpos : ∀ u, 0 < h u := fun u => lt_of_lt_of_le one_pos (h1 u)
  have iH : Integrable fun u => H u ^ 2 := _root_.RHTower.WeilMarkovPole.integrable_sq hc
    hH.hasCompactSupport
  have iH' : Integrable fun u => H (u + ℓ) ^ 2 := iH.comp_add_right ℓ
  have hGm : Measurable (windowGate A h) := hm.indicator measurableSet_Icc
  have hG0 : ∀ v, 0 ≤ windowGate A h v := fun v =>
    indicator_nonneg (fun u _ => (hpos u).le) v
  have hGC : ∀ v, windowGate A h v ≤ C := fun v => by
    unfold windowGate
    by_cases hv : v ∈ Icc (-A) 0
    · rw [indicator_of_mem hv]; exact hC v
    · rw [indicator_of_notMem hv]; exact le_trans (by norm_num) ((h1 v).trans (hC v))
  -- bounded measurable multipliers
  have hbdd : ∀ s : ℝ, Integrable fun u => windowGate A h (u + s) / h u * H u ^ 2 := fun s =>
    iH.bdd_mul (c := C) ((hGm.comp (measurable_add_const s)).div hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        show ‖windowGate A h (u + s) / h u‖ ≤ C
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hG0 _) (hpos u).le)]
        exact (div_le_self (hG0 _) (h1 u)).trans (hGC _))
  have iB : Integrable fun u => windowGate A h u / h (u + ℓ) * H (u + ℓ) ^ 2 := by
    have := (hbdd (-ℓ)).comp_add_right ℓ
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [add_neg_cancel_right]
  have iP : Integrable fun u => H u * H (u + ℓ) :=
    (hc.mul (hc.comp (continuous_add_const ℓ))).integrable_of_hasCompactSupport
      hH.hasCompactSupport.mul_right
  -- pointwise: a product vanishes unless both points lie in the window
  have hpt : ∀ u, 2 * |H u * H (u + ℓ)| ≤
      windowGate A h (u + ℓ) / h u * H u ^ 2 + windowGate A h u / h (u + ℓ) * H (u + ℓ) ^ 2 :=
    fun u => by
      have hR : 0 ≤ windowGate A h (u + ℓ) / h u * H u ^ 2 +
          windowGate A h u / h (u + ℓ) * H (u + ℓ) ^ 2 :=
        add_nonneg (mul_nonneg (div_nonneg (hG0 _) (hpos u).le) (sq_nonneg _))
          (mul_nonneg (div_nonneg (hG0 _) (hpos _).le) (sq_nonneg _))
      by_cases ha : H u = 0
      · have h0 : H u * H (u + ℓ) = 0 := by rw [ha, zero_mul]
        rw [h0, abs_zero, mul_zero]; exact hR
      by_cases hb : H (u + ℓ) = 0
      · have h0 : H u * H (u + ℓ) = 0 := by rw [hb, mul_zero]
        rw [h0, abs_zero, mul_zero]; exact hR
      have hu : u ∈ Icc (-A) 0 := by by_contra hh; exact ha (hH.vanish u hh)
      have hu' : u + ℓ ∈ Icc (-A) 0 := by by_contra hh; exact hb (hH.vanish _ hh)
      rw [windowGate, windowGate, indicator_of_mem hu, indicator_of_mem hu']
      exact two_abs_mul_le_ratio (hpos u) (hpos _) _ _
  have hstep := abs_integral_le_integral_abs (μ := volume) (f := fun u => H u * H (u + ℓ))
  have hmono := integral_mono (f := fun u => 2 * |H u * H (u + ℓ)|)
    (g := fun u => windowGate A h (u + ℓ) / h u * H u ^ 2 +
      windowGate A h u / h (u + ℓ) * H (u + ℓ) ^ 2) (iP.abs.const_mul 2) ((hbdd ℓ).add iB) hpt
  rw [integral_const_mul, integral_add (hbdd ℓ) iB] at hmono
  -- shift the second half back by `ℓ`
  have hshift : ∫ u, windowGate A h u / h (u + ℓ) * H (u + ℓ) ^ 2 =
      ∫ u, windowGate A h (u - ℓ) / h u * H u ^ 2 := by
    have := integral_add_right_eq_self (μ := volume)
      (fun v => windowGate A h (v - ℓ) / h v * H v ^ 2) ℓ
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only [add_sub_cancel_right])
  have hsplit : ∫ u, (windowGate A h (u + ℓ) + windowGate A h (u - ℓ)) / h u * H u ^ 2 =
      (∫ u, windowGate A h (u + ℓ) / h u * H u ^ 2) + ∫ u, windowGate A h (u - ℓ) / h u * H u ^ 2 := by
    rw [← integral_add (hbdd ℓ) (by simpa only [sub_eq_add_neg] using hbdd (-ℓ))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  rw [hsplit, ← hshift]
  linarith

/-! ### The Perron weight of the second stage -/

/-- The inner regions `[−A, −ℓ₃] ∪ [ℓ₃ − A, 0]` of a second-stage window. -/
def innerRegions (A : ℝ) : Set ℝ := Icc (-A) (-Real.log 3) ∪ Icc (Real.log 3 - A) 0

open Classical in
/-- The Perron weight of the path: `t` on the inner regions, `1` elsewhere. -/
def pathWeight (A t : ℝ) : ℝ → ℝ := (innerRegions A).piecewise (fun _ => t) (fun _ => 1)

theorem measurable_pathWeight (A t : ℝ) : Measurable (pathWeight A t) := by
  classical
  exact Measurable.piecewise (measurableSet_Icc.union measurableSet_Icc) measurable_const
    measurable_const

theorem pathWeight_of_mem {A t v : ℝ} (hv : v ∈ innerRegions A) : pathWeight A t v = t := by
  classical
  simp [pathWeight, Set.piecewise, hv]

theorem pathWeight_of_not_mem {A t v : ℝ} (hv : v ∉ innerRegions A) : pathWeight A t v = 1 := by
  classical
  simp [pathWeight, Set.piecewise, hv]

theorem gate_of_not_window {A t v : ℝ} (hv : v ∉ Icc (-A) 0) : windowGate A (pathWeight A t) v = 0 :=
  indicator_of_notMem hv _

theorem gate_inner {A t v : ℝ} (hw : v ∈ Icc (-A) 0) (hv : v ∈ innerRegions A) :
    windowGate A (pathWeight A t) v = t := by
  rw [windowGate, indicator_of_mem hw, pathWeight_of_mem hv]

theorem gate_outer {A t v : ℝ} (hw : v ∈ Icc (-A) 0) (hv : v ∉ innerRegions A) :
    windowGate A (pathWeight A t) v = 1 := by
  rw [windowGate, indicator_of_mem hw, pathWeight_of_not_mem hv]

theorem gate_le {A t v : ℝ} (ht : 1 ≤ t) : windowGate A (pathWeight A t) v ≤ t := by
  by_cases hw : v ∈ Icc (-A) 0
  · by_cases hv : v ∈ innerRegions A
    · rw [gate_inner hw hv]
    · rw [gate_outer hw hv]; exact ht
  · rw [gate_of_not_window hw]; linarith

/-- The logarithmic facts of the second stage. -/
theorem log_facts : 0 < Real.log 2 ∧ Real.log 2 < Real.log 3 ∧ 3 * Real.log 2 < 2 * Real.log 3 ∧
    Real.log 4 = 2 * Real.log 2 := by
  refine ⟨Real.log_pos (by norm_num), Real.log_lt_log (by norm_num) (by norm_num), ?_, ?_⟩
  · rw [← Real.log_rpow (by norm_num), ← Real.log_rpow (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  · rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

/-- **The Perron weight balances every point of a second-stage window**:
`α(G(u ± ℓ₂)) + β(G(u ± ℓ₃)) ≤ h(u)` for `t = 1/α`, `α² + β ≤ 1`. -/
theorem path_balance (hA3 : Real.log 3 < A) (hA4 : A < Real.log 4) {α β : ℝ} (hα : 0 < α)
    (hβ : 0 ≤ β) (hc : α ^ 2 + β ≤ 1) {u : ℝ} (hu : u ∈ Icc (-A) 0) :
    α * (windowGate A (pathWeight A α⁻¹) (u + Real.log 2) +
        windowGate A (pathWeight A α⁻¹) (u - Real.log 2)) +
      β * (windowGate A (pathWeight A α⁻¹) (u + Real.log 3) +
        windowGate A (pathWeight A α⁻¹) (u - Real.log 3)) ≤ pathWeight A α⁻¹ u := by
  obtain ⟨h2, h23, h89, h4⟩ := log_facts
  rw [h4] at hA4
  set t := α⁻¹ with ht
  have hαt : α * t = 1 := mul_inv_cancel₀ hα.ne'
  have hα1 : α ≤ 1 := by nlinarith
  have ht1 : 1 ≤ t := by rw [ht]; exact one_le_inv₀ hα |>.mpr hα1
  have hkey : α + β * t ≤ t := by nlinarith
  set ℓ₂ := Real.log 2
  set ℓ₃ := Real.log 3
  obtain ⟨hu1, hu2⟩ := hu
  have hW : ∀ v, -A ≤ v → v ≤ 0 → v ∈ Icc (-A) 0 := fun v a b => ⟨a, b⟩
  have hnW : ∀ v, (v < -A ∨ 0 < v) → v ∉ Icc (-A) 0 := fun v h hv => by
    rcases h with h | h <;> linarith [hv.1, hv.2]
  have hin1 : ∀ v, -A ≤ v → v ≤ -ℓ₃ → v ∈ innerRegions A := fun v a b => Or.inl ⟨a, b⟩
  have hin5 : ∀ v, ℓ₃ - A ≤ v → v ≤ 0 → v ∈ innerRegions A := fun v a b => Or.inr ⟨a, b⟩
  have hout : ∀ v, -ℓ₃ < v → v < ℓ₃ - A → v ∉ innerRegions A := fun v a b hv => by
    rcases hv with hv | hv <;> linarith [hv.1, hv.2]
  -- the five regions
  rcases le_or_gt u (-ℓ₃) with hr1 | hr1
  · -- `[−A, −ℓ₃]`: links to `u + ℓ₂` (outer) and `u + ℓ₃` (inner)
    rw [pathWeight_of_mem (hin1 u hu1 hr1),
      gate_outer (hW (u + ℓ₂) (by linarith) (by linarith)) (hout (u + ℓ₂) (by linarith) (by linarith)),
      gate_of_not_window (hnW (u - ℓ₂) (Or.inl (by linarith))),
      gate_inner (hW (u + ℓ₃) (by linarith) (by linarith)) (hin5 (u + ℓ₃) (by linarith) (by linarith)),
      gate_of_not_window (hnW (u - ℓ₃) (Or.inl (by linarith)))]
    linarith
  rcases le_or_gt u (-ℓ₂) with hr2 | hr2
  · -- `(−ℓ₃, −ℓ₂]`: links only to `u + ℓ₂`
    rw [pathWeight_of_not_mem (hout u hr1 (by linarith)),
      gate_of_not_window (hnW (u - ℓ₂) (Or.inl (by linarith))),
      gate_of_not_window (hnW (u + ℓ₃) (Or.inr (by linarith))),
      gate_of_not_window (hnW (u - ℓ₃) (Or.inl (by linarith)))]
    have := gate_le (A := A) (v := u + ℓ₂) ht1
    nlinarith
  rcases lt_or_ge u (ℓ₂ - A) with hr3 | hr3
  · -- `(−ℓ₂, ℓ₂ − A)`: no links
    rw [pathWeight_of_not_mem (hout u hr1 (by linarith)),
      gate_of_not_window (hnW (u + ℓ₂) (Or.inr (by linarith))),
      gate_of_not_window (hnW (u - ℓ₂) (Or.inl (by linarith))),
      gate_of_not_window (hnW (u + ℓ₃) (Or.inr (by linarith))),
      gate_of_not_window (hnW (u - ℓ₃) (Or.inl (by linarith)))]
    simp
  rcases lt_or_ge u (ℓ₃ - A) with hr4 | hr4
  · -- `[ℓ₂ − A, ℓ₃ − A)`: links only to `u − ℓ₂`
    rw [pathWeight_of_not_mem (hout u hr1 hr4),
      gate_of_not_window (hnW (u + ℓ₂) (Or.inr (by linarith))),
      gate_of_not_window (hnW (u + ℓ₃) (Or.inr (by linarith))),
      gate_of_not_window (hnW (u - ℓ₃) (Or.inl (by linarith)))]
    have := gate_le (A := A) (v := u - ℓ₂) ht1
    nlinarith
  · -- `[ℓ₃ − A, 0]`: links to `u − ℓ₂` (outer) and `u − ℓ₃` (inner)
    rw [pathWeight_of_mem (hin5 u hr4 hu2),
      gate_of_not_window (hnW (u + ℓ₂) (Or.inr (by linarith))),
      gate_outer (hW (u - ℓ₂) (by linarith) (by linarith)) (hout (u - ℓ₂) (by linarith) (by linarith)),
      gate_of_not_window (hnW (u + ℓ₃) (Or.inr (by linarith))),
      gate_inner (hW (u - ℓ₃) (by linarith) (by linarith)) (hin1 (u - ℓ₃) (by linarith) (by linarith))]
    linarith

/-- **The second-stage bound**: for `α, β ≥ 0` with `α² + β ≤ 1`,
`2α|c₂(H)| + 2β|c₃(H)| ≤ ‖H‖²` on every window of length `log 3 < A < log 4`. -/
theorem two_mul_abs_autocorr_add_le (hA3 : Real.log 3 < A) (hA4 : A < Real.log 4)
    (hH : IsWindowTest A H) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : α ^ 2 + β ≤ 1) :
    2 * α * |∫ u, H u * H (u + Real.log 2)| + 2 * β * |∫ u, H u * H (u + Real.log 3)| ≤
      ∫ u, H u ^ 2 := by
  obtain ⟨h2, h23, h89, h4⟩ := log_facts
  have hnorm : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun u => sq_nonneg _
  rcases hα.lt_or_eq with hα0 | hα0
  swap
  · -- `α = 0`: one fold, longer than half the window
    subst hα0
    have h3 := abs_autocorr_le_half hH (ℓ := Real.log 3) (by rw [h4] at hA4; linarith)
    have hβ1 : β ≤ 1 := by nlinarith
    have : 2 * β * |∫ u, H u * H (u + Real.log 3)| ≤ ∫ u, H u ^ 2 := by
      have := mul_le_mul_of_nonneg_left h3 (by linarith : 0 ≤ 2 * β)
      nlinarith
    linarith [this]
  set t := α⁻¹
  have hα1 : α ≤ 1 := by nlinarith
  have ht1 : 1 ≤ t := one_le_inv₀ hα0 |>.mpr hα1
  set h := pathWeight A t
  have hm : Measurable h := measurable_pathWeight A t
  have h1 : ∀ u, 1 ≤ h u := fun u => by
    show 1 ≤ pathWeight A t u
    by_cases hv : u ∈ innerRegions A
    · rw [pathWeight_of_mem hv]; exact ht1
    · rw [pathWeight_of_not_mem hv]
  have hC : ∀ u, h u ≤ t := fun u => by
    show pathWeight A t u ≤ t
    by_cases hv : u ∈ innerRegions A
    · rw [pathWeight_of_mem hv]
    · rw [pathWeight_of_not_mem hv]; exact ht1
  have hpos : ∀ u, 0 < h u := fun u => lt_of_lt_of_le one_pos (h1 u)
  have e2 := two_abs_autocorr_le hH hm h1 hC (Real.log 2)
  have e3 := two_abs_autocorr_le hH hm h1 hC (Real.log 3)
  have iH : Integrable fun u => H u ^ 2 := _root_.RHTower.WeilMarkovPole.integrable_sq
    hH.continuous hH.hasCompactSupport
  have hGm : Measurable (windowGate A h) := hm.indicator measurableSet_Icc
  have hG0 : ∀ v, 0 ≤ windowGate A h v := fun v =>
    indicator_nonneg (fun u _ => (hpos u).le) v
  have hint : ∀ s : ℝ, Integrable fun u =>
      (windowGate A h (u + s) + windowGate A h (u - s)) / h u * H u ^ 2 := fun s =>
    iH.bdd_mul (c := 2 * t)
      ((((hGm.comp (measurable_add_const s)).add (hGm.comp (measurable_sub_const s))).div
        hm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun u => by
        show ‖(windowGate A h (u + s) + windowGate A h (u - s)) / h u‖ ≤ 2 * t
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (add_nonneg (hG0 _) (hG0 _)) (hpos u).le)]
        refine (div_le_self (add_nonneg (hG0 _) (hG0 _)) (h1 u)).trans ?_
        linarith [gate_le (A := A) (v := u + s) ht1, gate_le (A := A) (v := u - s) ht1])
  -- combine with the balance of the Perron weight
  have hbal : ∫ u, (α * ((windowGate A h (u + Real.log 2) + windowGate A h (u - Real.log 2)) /
      h u * H u ^ 2) + β * ((windowGate A h (u + Real.log 3) + windowGate A h (u - Real.log 3)) /
      h u * H u ^ 2)) ≤ ∫ u, H u ^ 2 := by
    refine integral_mono (((hint _).const_mul α).add ((hint _).const_mul β)) iH fun u => ?_
    by_cases hu : u ∈ Icc (-A) 0
    · have hb := path_balance hA3 hA4 hα0 hβ hc hu
      have hsq : 0 ≤ H u ^ 2 := sq_nonneg _
      have hhu := hpos u
      have : α * ((windowGate A h (u + Real.log 2) + windowGate A h (u - Real.log 2)) / h u *
          H u ^ 2) + β * ((windowGate A h (u + Real.log 3) + windowGate A h (u - Real.log 3)) /
          h u * H u ^ 2) = (α * (windowGate A h (u + Real.log 2) + windowGate A h (u - Real.log 2)) +
          β * (windowGate A h (u + Real.log 3) + windowGate A h (u - Real.log 3))) / h u *
          H u ^ 2 := by ring
      rw [this]
      calc _ ≤ h u / h u * H u ^ 2 :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hhu.le) hsq
        _ = H u ^ 2 := by rw [div_self hhu.ne', one_mul]
    · rw [hH.vanish u hu]; simp
  rw [integral_add ((hint _).const_mul α) ((hint _).const_mul β), integral_const_mul,
    integral_const_mul] at hbal
  nlinarith [mul_le_mul_of_nonneg_left e2 hα, mul_le_mul_of_nonneg_left e3 hβ]

/-! ### Tate operators and the arithmetic term of the second stage -/

theorem windowLevel_eq_three (h1 : Real.log 3 ≤ A) (h2 : A < Real.log 4) : windowLevel A = 3 := by
  rw [windowLevel, Nat.floor_eq_iff (Real.exp_pos A).le]
  constructor
  · have := Real.exp_le_exp.mpr h1
    rw [Real.exp_log (by norm_num)] at this
    norm_num; exact this
  · have := Real.exp_lt_exp.mpr h2
    rw [Real.exp_log (by norm_num)] at this
    norm_num; exact this

/-- **The Tate operators of the second stage are positive below the path threshold**:
`ρ_A(J_k) ≥ 0` if `k ≥ 0` and `((2^k − 1)/(2√2))² + (3^k − 1)/(2√3) ≤ 1`. -/
theorem tateFunction_nonneg_secondStage (hA3 : Real.log 3 < A) (hA4 : A < Real.log 4)
    (hH : IsWindowTest A H) {k : ℝ} (hk : 0 ≤ k)
    (hpath : (((2 : ℝ) ^ k - 1) / (2 * Real.sqrt 2)) ^ 2 + ((3 : ℝ) ^ k - 1) / (2 * Real.sqrt 3) ≤ 1) :
    0 ≤ tateFunction A H k := by
  have hlev := windowLevel_eq_three hA3.le hA4
  rw [tateFunction_eq hH, hlev, show Finset.Icc 1 3 = {1, 2, 3} by decide,
    Finset.sum_insert (by decide), Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3), jordanTotient_one]
  have h2 : jordanTotient k 2 = (2 : ℝ) ^ k - 1 := by
    simpa using jordanTotient_prime_pow Nat.prime_two k (a := 1) le_rfl
  have h3 : jordanTotient k 3 = (3 : ℝ) ^ k - 1 := by
    simpa using jordanTotient_prime_pow Nat.prime_three k (a := 1) le_rfl
  rw [h2, h3]
  simp only [Nat.cast_one, Real.sqrt_one, div_one, one_mul, Real.log_one, add_zero, Nat.cast_ofNat]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have ha : 0 ≤ ((2 : ℝ) ^ k - 1) / (2 * Real.sqrt 2) :=
    div_nonneg (sub_nonneg.mpr (Real.one_le_rpow (by norm_num) hk)) (by positivity)
  have hb : 0 ≤ ((3 : ℝ) ^ k - 1) / (2 * Real.sqrt 3) :=
    div_nonneg (sub_nonneg.mpr (Real.one_le_rpow (by norm_num) hk)) (by positivity)
  have key := two_mul_abs_autocorr_add_le hA3 hA4 hH ha hb hpath
  have e1 : ∫ u, H u * H u = ∫ u, H u ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => by simp [sq])
  rw [e1]
  have c2 := neg_abs_le (∫ u, H u * H (u + Real.log 2))
  have c3 := neg_abs_le (∫ u, H u * H (u + Real.log 3))
  have f2 : ((2 : ℝ) ^ k - 1) / Real.sqrt 2 = 2 * (((2 : ℝ) ^ k - 1) / (2 * Real.sqrt 2)) := by
    field_simp
  have f3 : ((3 : ℝ) ^ k - 1) / Real.sqrt 3 = 2 * (((3 : ℝ) ^ k - 1) / (2 * Real.sqrt 3)) := by
    field_simp
  rw [f2, f3]
  nlinarith [mul_le_mul_of_nonneg_left c2 (by linarith : 0 ≤ 2 * (((2 : ℝ) ^ k - 1) / (2 * Real.sqrt 2))),
    mul_le_mul_of_nonneg_left c3 (by linarith : 0 ≤ 2 * (((3 : ℝ) ^ k - 1) / (2 * Real.sqrt 3)))]

/-- **The arithmetic term of the second stage**: `|w₂c₂ + w₃c₃| ≤ r‖H‖²` for every `r > 0` with
`w₂² + 2rw₃ ≤ 4r²`, `w_n = Λ(n)/√n`. -/
theorem abs_arith_secondStage_le (hA3 : Real.log 3 < A) (hA4 : A < Real.log 4)
    (hH : IsWindowTest A H) {r : ℝ} (hr : 0 < r)
    (hrw : (Real.log 2 / Real.sqrt 2) ^ 2 + 2 * r * (Real.log 3 / Real.sqrt 3) ≤ 4 * r ^ 2) :
    |Real.log 2 / Real.sqrt 2 * (∫ u, H u * H (u + Real.log 2)) +
        Real.log 3 / Real.sqrt 3 * ∫ u, H u * H (u + Real.log 3)| ≤ r * ∫ u, H u ^ 2 := by
  set w₂ := Real.log 2 / Real.sqrt 2
  set w₃ := Real.log 3 / Real.sqrt 3
  have hw₂ : 0 ≤ w₂ := div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
  have hw₃ : 0 ≤ w₃ := div_nonneg (Real.log_nonneg (by norm_num)) (Real.sqrt_nonneg _)
  have hr0 : r ≠ 0 := hr.ne'
  have hc : (w₂ / (2 * r)) ^ 2 + w₃ / (2 * r) ≤ 1 := by
    rw [div_pow, div_add_div _ _ (by positivity) (by positivity), div_le_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hrw (by positivity : (0 : ℝ) ≤ 2 * r)]
  have key := two_mul_abs_autocorr_add_le hA3 hA4 hH (div_nonneg hw₂ (by positivity))
    (div_nonneg hw₃ (by positivity)) hc
  have hrw' : 2 * (w₂ / (2 * r)) = w₂ / r := by field_simp
  have hrw'' : 2 * (w₃ / (2 * r)) = w₃ / r := by field_simp
  rw [hrw', hrw''] at key
  have hle : |w₂ * (∫ u, H u * H (u + Real.log 2)) + w₃ * ∫ u, H u * H (u + Real.log 3)| ≤
      w₂ * |∫ u, H u * H (u + Real.log 2)| + w₃ * |∫ u, H u * H (u + Real.log 3)| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hw₂, abs_of_nonneg hw₃]
  have : w₂ * |∫ u, H u * H (u + Real.log 2)| + w₃ * |∫ u, H u * H (u + Real.log 3)| =
      r * (w₂ / r * |∫ u, H u * H (u + Real.log 2)| + w₃ / r * |∫ u, H u * H (u + Real.log 3)|) := by
    field_simp
  rw [this] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left key hr.le)

end GaloisForLFunctions.WindowTowerOfSpecZ
