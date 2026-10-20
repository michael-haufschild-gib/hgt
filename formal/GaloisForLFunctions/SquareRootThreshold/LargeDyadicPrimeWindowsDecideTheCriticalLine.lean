import GaloisForLFunctions.SquareRootThreshold.NegativityRateEqualsMaximalDepth

/-!
# Large dyadic prime windows decide the critical line

Let `b` be supported in `[−w, w]`. The kernel `k = f ⋆ f̃` of the two-bump test
`f = b(t + v/2) + τ b(t − v/2)` vanishes off `[−2w, 2w] ∪ ±[v − 2w, v + 2w]`
(`weilTest_twoBump_eq_zero`). For `2w < log 2` the prime side of the explicit formula therefore
reads `Λ(n)` only on the window `|log n − v| ≤ 2w`, which lies in `(X/2, 2X)` for `X = e^v`
(`tsum_vonMangoldt_twoBump_eq_window`).

The Laplace argument needs only a tail of lags. On `[0, V]` the minor deficit is bounded a priori
by the upper rate with `D = ½`. So the unbounded excess forced by an off-line zero of depth
`> σ ≥ 0` occurs beyond `V`: the deficit is `< −K e^{σv}` at some lag `v ≥ V`, for every `K`
and `V` (`exists_minorDeficit_lt_of_ge`).

Hence, for every `X₀ = e^V`, RH holds iff the window functional

`P_v(k) = h_k(i/2) + h_k(−i/2) − Σ_{|log n − v| ≤ 2w} Λ(n)/√n (k(log n) + k(−log n))
  + (1/2π) ∫ h_k Γ`

is nonnegative on the unimodular two-bump tests at every lag `v ≥ V` and height `γ`
(`onLine_iff_primeWindow_nonneg`). Each test reads the primes of a single dyadic window, and no
prime below `X₀/2` enters. An off-line zero of depth `> σ` drives `P_v` below `−K e^{σv}` in windows
beyond every `X₀` (`zeta_exists_primeWindow_lt`). The same holds for primitive Dirichlet
`L`-functions with `χ(n)Λ(n)` (`grh_iff_primeWindow_nonneg`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Tail visibility -/

/-- **Tail visibility.** Under the hypotheses of `exists_minor_gt_of_top`, the minor inequality
fails by more than `K e^{σv}` at some lag `v ≥ V`, for every `V`. -/
theorem exists_minor_gt_of_top_of_ge (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {t₀ : ℂ}
    (ht₀ : t₀ ∈ rightZeros Z) (hq₀ : offLineWeight b (Z.mult t₀) t₀ ≠ 0)
    (htop : ∀ t ∈ rightZeros Z, t.im = t₀.im → offLineWeight b (Z.mult t) t ≠ 0 → t.re ≤ t₀.re)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < t₀.re - 1 / 2) (K V : ℝ) :
    ∃ v : ℝ, 0 ≤ v ∧ V ≤ v ∧ 2 * (lagStructure Z b 0).re + K * Real.exp (σ * v) <
      ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  -- a priori the excess is at most `C e^{v/2}`, since every depth is below `½`
  obtain ⟨C, hC⟩ := minorDeficit_ge Z hZ hb hbs (D := 1 / 2) (by norm_num)
    fun ρ hρ => by linarith [(Z.strip ρ hρ).2]
  set K' := |K| + |C| * Real.exp (V / 2) with hK'
  have hCV : 0 ≤ |C| * Real.exp (V / 2) := by positivity
  obtain ⟨v, hv, hgt⟩ := exists_minor_gt_of_top Z hZ hb hbs ht₀ hq₀ htop hσ0 hσ K'
  have he : 1 ≤ Real.exp (σ * v) := Real.one_le_exp (mul_nonneg hσ0 hv)
  have hK : K * Real.exp (σ * v) ≤ K' * Real.exp (σ * v) :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (Real.exp_pos _).le
  refine ⟨v, hv, ?_, by linarith⟩
  by_contra hlt
  push Not at hlt
  have h1 := hC v hv
  rw [minorDeficit] at h1
  have h2 : C * Real.exp (1 / 2 * v) ≤ |C| * Real.exp (V / 2) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (abs_nonneg C))
  have h3 : |C| * Real.exp (V / 2) ≤ K' * Real.exp (σ * v) := by
    rw [hK']
    nlinarith [abs_nonneg K]
  linarith

/-- **Negativity beyond every lag.** If some zero has depth `|Re ρ − ½| > σ ≥ 0`, then for every
`K` and `V` there are a height `γ` and a lag `v ≥ V` with `μ(v) < −K e^{σv}` for the bump `κ_w`
modulated to `γ`. -/
theorem exists_minorDeficit_lt_of_ge (Z : ZeroConfig) (hZ : TemperedConfig Z) {w : ℝ}
    (hw : 0 < w) {ρ : ℂ} (hρ : ρ ∈ Z.carrier) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < |ρ.re - 1 / 2|)
    (K V : ℝ) :
    ∃ γ v : ℝ, 0 ≤ v ∧ V ≤ v ∧
      minorDeficit Z (modScaledBump w γ) v < -(K * Real.exp (σ * v)) := by
  -- a zero right of the line of the same depth
  obtain ⟨t, ht, htd⟩ : ∃ t ∈ rightZeros Z, t.re - 1 / 2 = |ρ.re - 1 / 2| := by
    rcases le_or_gt ρ.re (1 / 2) with h | h
    · refine ⟨reflect ρ, ⟨Z.reflect_mem ρ hρ, ?_⟩, ?_⟩
      · have : ρ.re ≠ 1 / 2 := fun he => by rw [he, sub_self, abs_zero] at hσ; linarith
        simp [reflect]
        linarith [lt_of_le_of_ne h this]
      · rw [abs_of_nonpos (by linarith)]
        simp [reflect]
        ring
    · exact ⟨ρ, ⟨hρ, h⟩, by rw [abs_of_pos (by linarith)]⟩
  have hqne : ∀ t' ∈ rightZeros Z, t'.im = t.im →
      offLineWeight (modScaledBump w t.im) (Z.mult t') t' ≠ 0 := fun t' ht' him => by
    have hm := Z.one_le_mult t' ht'.1
    rw [offLineWeight, him]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (pairWeight_modScaledBump_ne_zero hw _ _)
  obtain ⟨t₀, ht₀, him₀, -, htop⟩ := exists_top_at_height Z ht (fun _ => True) trivial
  have hdeep : σ < t₀.re - 1 / 2 := by
    have := htop t ht rfl trivial
    linarith
  obtain ⟨v, hv, hV, h⟩ := exists_minor_gt_of_top_of_ge Z hZ (contDiff_modScaledBump_two w t.im)
    (modScaledBump_support hw t.im) ht₀ (hqne t₀ ht₀ him₀)
    (fun t' ht' him' _ => htop t' ht' (him'.trans him₀) trivial) hσ0 hdeep K V
  exact ⟨t.im, v, hv, hV, by rw [minorDeficit]; linarith⟩

/-- **Large lags decide the line.** For every `V`, a tempered configuration is Weil nonnegative on
the unimodular two-bump tests `κ_{w,γ}(t + v/2) + τ κ_{w,γ}(t − v/2)` with `v ≥ V` iff all its
zeros lie on the critical line. -/
theorem onLine_iff_twoBump_nonneg_of_ge (Z : ZeroConfig) (hZ : TemperedConfig Z) {w : ℝ}
    (hw : 0 < w) (V : ℝ) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔ ∀ (γ v : ℝ) (τ : ℂ), V ≤ v → ‖τ‖ = 1 →
      0 ≤ (Z.W (twoBump (modScaledBump w γ) v τ) (twoBump (modScaledBump w γ) v τ)).re := by
  refine ⟨fun hon _ _ _ _ _ => weil_nonneg_of_onLine Z hon _, fun h ρ hρ => ?_⟩
  by_contra hre
  obtain ⟨γ, v, -, hV, hlt⟩ := exists_minorDeficit_lt_of_ge Z hZ hw hρ le_rfl
    (abs_pos.mpr (sub_ne_zero.mpr hre)) 0 V
  obtain ⟨τ, hτ, heq⟩ := exists_unit_re_W_eq_minorDeficit Z hZ (contDiff_modScaledBump_two w γ)
    (modScaledBump_support hw γ) v
  have := h γ v τ hV hτ
  rw [heq] at this
  simp only [zero_mul, neg_zero] at hlt
  linarith

/-! ### The window read by a two-bump test -/

/-- **Support of the two-bump Weil kernel.** For `b` supported in `[−w, w]`, the kernel of
`b(t + v/2) + τ b(t − v/2)` vanishes off `[−2w, 2w] ∪ ±[v − 2w, v + 2w]`. -/
theorem weilTest_twoBump_eq_zero {b : ℝ → ℂ} {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ)
    (τ : ℂ) {x : ℝ} (h0 : 2 * w < |x|) (h1 : 2 * w < |x - v|) (h2 : 2 * w < |x + v|) :
    EF.weilTest (twoBump b v τ) (twoBump b v τ) x = 0 := by
  have hf : ∀ t, twoBump b v τ t ≠ 0 → |t + v / 2| ≤ w ∨ |t - v / 2| ≤ w := fun t ht => by
    by_contra hcon
    push Not at hcon
    have e1 : b (t + v / 2) = 0 := by_contra fun hb => absurd (hbs _ hb) (not_le.mpr hcon.1)
    have e2 : b (t - v / 2) = 0 := by_contra fun hb => absurd (hbs _ hb) (not_le.mpr hcon.2)
    refine ht ?_
    simp only [twoBump, bumpTest, Fin.sum_univ_two, lagPoint]
    simp only [Fin.isValue, Matrix.cons_val_zero, Fin.val_zero, Nat.cast_zero, Nat.cast_ofNat,
      Matrix.cons_val_one, Fin.val_one, Nat.cast_one]
    rw [show t - (0 - (2 - 1) / 2) * v = t + v / 2 by ring,
      show t - (1 - (2 - 1) / 2) * v = t - v / 2 by ring, e1, e2]
    simp
  rw [EF.weilTest, convolution_def]
  have hz : ∀ t, (ContinuousLinearMap.mul ℝ ℂ) (twoBump b v τ t)
      (EF.tilde (twoBump b v τ) (x - t)) = 0 := fun t => by
    rw [ContinuousLinearMap.mul_apply', EF.tilde]
    by_contra hne
    obtain ⟨ha, hb'⟩ := mul_ne_zero_iff.mp hne
    have hb'' : twoBump b v τ (-(x - t)) ≠ 0 := fun h => hb' (by rw [h, map_zero])
    rcases hf t ha with h | h <;> rcases hf _ hb'' with h' | h' <;>
      obtain ⟨h₁, h₂⟩ := abs_le.mp h <;> obtain ⟨h₃, h₄⟩ := abs_le.mp h' <;>
      first
        | exact absurd (abs_le.mpr ⟨by linarith, by linarith⟩) (not_le.mpr h0)
        | exact absurd (abs_le.mpr ⟨by linarith, by linarith⟩) (not_le.mpr h1)
        | exact absurd (abs_le.mpr ⟨by linarith, by linarith⟩) (not_le.mpr h2)
  simp_rw [hz, integral_zero]

/-- The integers `n ≤ e^{v + 2w}` with `|log n − v| ≤ 2w`. -/
def lagWindow (v w : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.exp (v + 2 * w)⌋₊ + 1)).filter fun n => |Real.log n - v| ≤ 2 * w

/-- Off the window, either `Λ(n) = 0` or the two-bump kernel vanishes at `± log n`. -/
theorem vonMangoldt_eq_zero_or_weilTest_twoBump_eq_zero {b : ℝ → ℂ} {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (hw2 : 2 * w < Real.log 2) {v : ℝ} (hv : 0 ≤ v) (τ : ℂ)
    {n : ℕ} (hn : n ∉ lagWindow v w) :
    ArithmeticFunction.vonMangoldt n = 0 ∨
      (EF.weilTest (twoBump b v τ) (twoBump b v τ) (Real.log n) = 0 ∧
        EF.weilTest (twoBump b v τ) (twoBump b v τ) (-Real.log n) = 0) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · left
    interval_cases n <;> simp
  right
  have hl : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast h)
  have hwin : 2 * w < |Real.log n - v| := by
    by_contra hle
    push Not at hle
    refine hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ?_)),
      hle⟩)
    exact (Real.log_le_iff_le_exp (by positivity)).mp (by linarith [(abs_le.mp hle).2])
  refine ⟨weilTest_twoBump_eq_zero hbs v τ (lt_abs.mpr (Or.inl (by linarith))) hwin
    (lt_abs.mpr (Or.inl (by linarith))), weilTest_twoBump_eq_zero hbs v τ
    (lt_abs.mpr (Or.inr (by linarith))) (lt_abs.mpr (Or.inr (by linarith))) ?_⟩
  rw [show -Real.log n + v = -(Real.log n - v) by ring, abs_neg]
  exact hwin

/-- **The prime sum of a two-bump test is a window sum.** For `2w < log 2` and `v ≥ 0`, the
twisted prime sum of the two-bump kernel runs over the window `|log n − v| ≤ 2w` only. -/
theorem tsum_vonMangoldt_twoBump_eq_window {b : ℝ → ℂ} {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w)
    (hw2 : 2 * w < Real.log 2) {v : ℝ} (hv : 0 ≤ v) (τ : ℂ) (c c' : ℕ → ℂ) :
    ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (c n * EF.weilTest (twoBump b v τ) (twoBump b v τ) (Real.log n) +
          c' n * EF.weilTest (twoBump b v τ) (twoBump b v τ) (-Real.log n)) =
      ∑ n ∈ lagWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (c n * EF.weilTest (twoBump b v τ) (twoBump b v τ) (Real.log n) +
          c' n * EF.weilTest (twoBump b v τ) (twoBump b v τ) (-Real.log n)) :=
  tsum_eq_sum fun n hn => by
    rcases vonMangoldt_eq_zero_or_weilTest_twoBump_eq_zero hbs hw2 hv τ hn with h | ⟨h1, h2⟩
    · simp [h]
    · simp [h1, h2]

/-! ### The window criteria -/

/-- The explicit-formula functional of `ζ` with the prime sum cut to the window
`|log n − v| ≤ 2w`. -/
def lagWindowRHS (v w : ℝ) (k : ℝ → ℂ) : ℂ :=
  paperFT k (I / 2) + paperFT k (-I / 2)
  - ∑ n ∈ lagWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (k (Real.log n) + k (-Real.log n))
  + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)

theorem literatureRHS_twoBump_eq_lagWindowRHS {b : ℝ → ℂ} {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (hw2 : 2 * w < Real.log 2) {v : ℝ} (hv : 0 ≤ v) (τ : ℂ) :
    EF.literatureRHS (EF.weilTest (twoBump b v τ) (twoBump b v τ)) =
      lagWindowRHS v w (EF.weilTest (twoBump b v τ) (twoBump b v τ)) := by
  have h := tsum_vonMangoldt_twoBump_eq_window hbs hw2 hv τ 1 1
  simp only [Pi.one_apply, one_mul] at h
  rw [EF.literatureRHS, lagWindowRHS, h]

/-- **RH is decided by large dyadic prime windows.** Let `0 < w`, `2w < log 2` and `V ≥ 0`. Every
nontrivial zero of `ζ` lies on the critical line iff the window functional `P_v` is nonnegative on
the unimodular two-bump tests `κ_{w,γ}(t + v/2) + τ κ_{w,γ}(t − v/2)` for every height `γ`, every
lag `v ≥ V` and `|τ| = 1`. The test at lag `v` reads `Λ(n)` only for `e^{v−2w} ≤ n ≤ e^{v+2w}`. -/
theorem onLine_iff_primeWindow_nonneg {w : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) {V : ℝ}
    (hV : 0 ≤ V) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔
      ∀ (γ v : ℝ) (τ : ℂ), V ≤ v → ‖τ‖ = 1 →
        0 ≤ (lagWindowRHS v w (EF.weilTest (twoBump (modScaledBump w γ) v τ)
          (twoBump (modScaledBump w γ) v τ))).re := by
  refine (onLine_iff_twoBump_nonneg_of_ge _ temperedConfig_zetaZeroConfig hw V).trans ?_
  refine forall_congr' fun γ => forall_congr' fun v => forall_congr' fun τ =>
    imp_congr_right fun hv => ?_
  rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w γ) v τ)
    (contDiff_bumpTest (contDiff_modScaledBump_two w γ) v ![1, τ])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw γ)) v τ),
    literatureRHS_twoBump_eq_lagWindowRHS (modScaledBump_support hw γ) hw2 (hV.trans hv)]

/-- **Window negativity at the rate of the depth.** If some nontrivial zero of `ζ` has
`|Re ρ − ½| > σ ≥ 0`, then for every `K` and `V ≥ 0` some unimodular two-bump test at a lag
`v ≥ V` has window functional `P_v < −K e^{σv}`. -/
theorem zeta_exists_primeWindow_lt {w : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < |ρ.re - 1 / 2|)
    (K : ℝ) {V : ℝ} (hV : 0 ≤ V) :
    ∃ (γ v : ℝ) (τ : ℂ), V ≤ v ∧ ‖τ‖ = 1 ∧
      (lagWindowRHS v w (EF.weilTest (twoBump (modScaledBump w γ) v τ)
        (twoBump (modScaledBump w γ) v τ))).re < -(K * Real.exp (σ * v)) := by
  obtain ⟨γ, v, hv, hVv, hlt⟩ := exists_minorDeficit_lt_of_ge zetaZeroConfig
    temperedConfig_zetaZeroConfig hw hρ hσ0 hσ K V
  obtain ⟨τ, hτ, heq⟩ := exists_unit_re_W_eq_minorDeficit zetaZeroConfig
    temperedConfig_zetaZeroConfig (contDiff_modScaledBump_two w γ) (modScaledBump_support hw γ) v
  refine ⟨γ, v, τ, hVv, hτ, ?_⟩
  rw [← literatureRHS_twoBump_eq_lagWindowRHS (modScaledBump_support hw γ) hw2 hv,
    ← zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w γ) v τ)
    (contDiff_bumpTest (contDiff_modScaledBump_two w γ) v ![1, τ])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw γ)) v τ), heq]
  exact hlt

/-- The twisted explicit-formula functional of `L(s, χ)` with the prime sum cut to the window
`|log n − v| ≤ 2w`. -/
def lagWindowRHSchi (κ q : ℕ) (c : ℕ → ℂ) (v w : ℝ) (k : ℝ → ℂ) : ℂ :=
  - ∑ n ∈ lagWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (c n * k (Real.log n) + (starRingEnd ℂ) (c n) * k (-Real.log n))
  + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r
      * ((((Complex.digamma (1 / 4 + (κ : ℂ) / 2 + I * r / 2)).re + Real.log (q / π) : ℝ)) : ℂ)

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **GRH for `L(s, χ)` is decided by large dyadic prime windows.** For a primitive `χ` modulo
`q > 1`, `0 < w`, `2w < log 2` and `V ≥ 0`: every nontrivial zero of `L(s, χ)` lies on the critical
line iff the twisted window functional is nonnegative on the unimodular two-bump tests at every
height and every lag `v ≥ V`. -/
theorem grh_iff_primeWindow_nonneg (hq : 1 < q) (hprim : χ.IsPrimitive) {w : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) {V : ℝ} (hV : 0 ≤ V) :
    (∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re = 1 / 2) ↔
      ∀ (γ v : ℝ) (τ : ℂ), V ≤ v → ‖τ‖ = 1 →
        0 ≤ (lagWindowRHSchi (ThmE.parity χ) q (ThmE.coeff χ) v w
          (EF.weilTest (twoBump (modScaledBump w γ) v τ) (twoBump (modScaledBump w γ) v τ))).re := by
  refine (onLine_iff_twoBump_nonneg_of_ge _ (temperedConfig_LZeros hq hprim) hw V).trans ?_
  refine forall_congr' fun γ => forall_congr' fun v => forall_congr' fun τ =>
    imp_congr_right fun hv => ?_
  have h := tsum_vonMangoldt_twoBump_eq_window (modScaledBump_support hw γ) hw2 (hV.trans hv) τ
    (ThmE.coeff χ) fun n => starRingEnd ℂ (ThmE.coeff χ n)
  beta_reduce at h
  rw [LZeros_W_eq_literatureRHSchi hq hprim (f := twoBump (modScaledBump w γ) v τ)
    (contDiff_bumpTest (contDiff_modScaledBump_two w γ) v ![1, τ])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw γ)) v τ), ThmE.literatureRHSchi, lagWindowRHSchi, h]

end GaloisForLFunctions.SquareRootThreshold
