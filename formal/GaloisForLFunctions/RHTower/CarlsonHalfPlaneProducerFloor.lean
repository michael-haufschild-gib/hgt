import Mathlib
import GaloisForLFunctions.RHTower.Sieve.DirichletMeanValueSharp
import GaloisForLFunctions.HTGeometry.ShortBumpMellinSmoothedSums

/-!
# Carlson's floor: no producer on a half-plane beyond the critical line

A Dirichlet series `D(s) = ∑ a(n) n^{−s}` with `‖a(n)‖ ≤ C n^θ` (`θ < 1`) that continues to a
half-strip `σ₁ ≤ Re s ≤ 3`, `Im s ≥ T₀` with logarithmic growth `‖D(s)‖ ≤ K log Im s` has
`∑_{n ≤ N} |a(n)|² n^{−2σ₁} ≪ log² N` (`exists_sum_sq_rpow_le_log_sq`), hence converges absolutely on
`Re s > σ₁ + 1/2` (`LSeriesSummable_of_logGrowth`).  This is Carlson's mean value theorem in the form
needed here.  The proof:

* Cauchy's theorem on `[σ₁, 3] × [T, 2T]` for `D(s) n^{s−σ₁}` recovers `a(n) n^{−σ₁} T` from the
  twisted mean `∫_T^{2T} D(σ₁+iy) n^{iy} dy` up to `O(n⁴ log T)` (`norm_twistedMean_sub_le`);
* the dual of the sharp Montgomery–Vaughan mean value theorem bounds all twisted means jointly by
  `(T + 104N) ∫_T^{2T} |D(σ₁+iy)|² dy` (`sum_normSq_integral_phase_le`);
* `T = T₀ N⁵` and Abel summation against the `log²` partial-sum bound finish the argument.

**Pole series** (`false_of_logGrowth_pole_of_lt_half`).  A Dirichlet series with a simple pole of
residue `1` at `s = 1` cannot continue with logarithmic growth to any strip left of `Re s = 1/2`.

**Application** (`not_isHalfPlaneProducer_of_lt_half`).  Let `Ψ` have logarithmic growth.  A weight
system `lam` whose Dirichlet series has a simple pole of residue `1` at `s = 1` and makes `Ψ − D` a
Carathéodory function (nonnegative real part) on `Re s > σ₀` cannot exist for `0 < σ₀ < 1/2`.
Harnack's inequality gives `‖D‖ ≪ log Im s` on `Re s ≥ σ₁` for `σ₁ ∈ (σ₀, 1/2)`, and Carlson then makes
the series absolutely convergent at `s = 1`, which contradicts the pole.  For `Ψ` the archimedean
log-derivative of `ζ`, the Weil-positive weight systems are the producers on `Re s > 1/2`, so the
critical line is the leftmost half-plane boundary any of them can have.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section
namespace RHTower.CarlsonFloor

/-- `∫_T^{2T} e^{iyx} dy` is bounded by `2/|x|`. -/
theorem norm_integral_phase_le (x T : ℝ) (hx : x ≠ 0) :
    ‖∫ y in T..2 * T, cexp (((y * x : ℝ) : ℂ) * I)‖ ≤ 2 / |x| := by
  have hc : (x : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hx) I_ne_zero
  have hfun : (fun y : ℝ => cexp (((y * x : ℝ) : ℂ) * I)) = fun y : ℝ => cexp (((x : ℂ) * I) * y) := by
    funext y; congr 1; push_cast; ring
  rw [hfun, integral_exp_mul_complex hc, norm_div]
  have h1 : ‖cexp ((x : ℂ) * I * ((2 * T : ℝ) : ℂ)) - cexp ((x : ℂ) * I * (T : ℂ))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have e1 : (x : ℂ) * I * ((2 * T : ℝ) : ℂ) = (((x * (2 * T)) : ℝ) : ℂ) * I := by push_cast; ring
    have e2 : (x : ℂ) * I * (T : ℂ) = (((x * T) : ℝ) : ℂ) * I := by push_cast; ring
    rw [e1, e2, norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]; norm_num
  have h2 : ‖(x : ℂ) * I‖ = |x| := by simp
  rw [h2]
  exact div_le_div_of_nonneg_right h1 (abs_nonneg x)

/-- Separation of logarithms of distinct positive integers: `1/|log n − log m| ≤ max n m`. -/
theorem inv_abs_log_sub_le_max {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : m ≠ n) :
    1 / |Real.log n - Real.log m| ≤ max (n : ℝ) m := by
  have key : ∀ {p q : ℕ}, 1 ≤ p → p < q → 1 / (q : ℝ) ≤ Real.log q - Real.log p := by
    intro p q hp hpq
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hle : ((p : ℝ) + 1) ≤ q := by exact_mod_cast hpq
    have hlog := Real.log_le_sub_one_of_pos (div_pos hp' hq')
    rw [Real.log_div hp'.ne' hq'.ne'] at hlog
    have : 1 / (q : ℝ) ≤ 1 - (p : ℝ) / q := by
      rw [div_le_iff₀ hq', sub_mul, div_mul_cancel₀ _ hq'.ne']; linarith
    linarith
  rcases lt_or_gt_of_ne hnm with h | h
  · have hk := key hm h
    have hpos : 0 < Real.log n - Real.log m := lt_of_lt_of_le (by
      have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      positivity) hk
    rw [abs_of_pos hpos]
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc 1 / (Real.log n - Real.log m) ≤ 1 / (1 / (n : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) hk
      _ = n := by field_simp
      _ ≤ max (n : ℝ) m := le_max_left _ _
  · have hk := key hn h
    have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hpos : 0 < Real.log m - Real.log n := lt_of_lt_of_le (by positivity) hk
    rw [abs_sub_comm, abs_of_pos hpos]
    calc 1 / (Real.log m - Real.log n) ≤ 1 / (1 / (m : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) hk
      _ = m := by field_simp
      _ ≤ max (n : ℝ) m := le_max_right _ _

/-- The `L`-series term at `3 + iy`, as a real amplitude times a phase. -/
theorem term_three_add_mul_I {a : ℕ → ℂ} {m : ℕ} (hm : m ≠ 0) (y : ℝ) :
    LSeries.term a (3 + y * I) m
      = a m * (((m : ℝ) ^ (-3 : ℝ) : ℝ) : ℂ) * cexp (((-(y * Real.log m)) : ℝ) * I) := by
  rw [LSeries.term_of_ne_zero hm]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [cpow_add _ _ hm0]
  have h3 : (m : ℂ) ^ (3 : ℂ) = (((m : ℝ) ^ (3 : ℝ) : ℝ) : ℂ) := by
    rw [ofReal_cpow hmpos.le]; push_cast; rfl
  have hI : (m : ℂ) ^ ((y : ℂ) * I) = cexp ((((y * Real.log m)) : ℝ) * I) := by
    rw [cpow_def_of_ne_zero hm0, ← natCast_log]; congr 1; push_cast; ring
  rw [h3, hI]
  have hneg : cexp (((-(y * Real.log m)) : ℝ) * I) = (cexp ((((y * Real.log m)) : ℝ) * I))⁻¹ := by
    rw [← Complex.exp_neg]; congr 1; push_cast; ring
  rw [hneg, Real.rpow_neg hmpos.le]
  have hne : cexp ((((y * Real.log m)) : ℝ) * I) ≠ 0 := Complex.exp_ne_zero _
  have hr : ((m : ℝ) ^ (3 : ℝ)) ≠ 0 := by positivity
  push_cast
  field_simp


/-- The off-diagonal weight: for `m ≥ 1`, `m ≠ n`, the oscillatory factor costs at most `4 n m^{θ−2}`. -/
theorem offDiag_weight_le {C θ : ℝ} (hC : 0 ≤ C) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : m ≠ n)
    {A : ℝ} (hA : A ≤ C * (m : ℝ) ^ θ) :
    A * (m : ℝ) ^ (-3 : ℝ) * (2 / |Real.log n - Real.log m|) ≤ 4 * C * n * (m : ℝ) ^ (θ - 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsep := inv_abs_log_sub_le_max hn hm hnm
  have h2 : 2 / |Real.log n - Real.log m| ≤ 4 * n * m := by
    have hmax : max (n : ℝ) m ≤ 2 * n * m := by
      rcases le_total (n : ℝ) m with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    calc 2 / |Real.log n - Real.log m| = 2 * (1 / |Real.log n - Real.log m|) := by ring
      _ ≤ 2 * (2 * n * m) := by gcongr; exact hsep.trans hmax
      _ = 4 * n * m := by ring
  have hpow : (m : ℝ) ^ θ * (m : ℝ) ^ (-3 : ℝ) * m = (m : ℝ) ^ (θ - 2) := by
    rw [← Real.rpow_add hm', ← Real.rpow_add_one hm'.ne']; ring_nf
  have hrp : 0 ≤ (m : ℝ) ^ (-3 : ℝ) := by positivity
  calc A * (m : ℝ) ^ (-3 : ℝ) * (2 / |Real.log n - Real.log m|)
      ≤ (C * (m : ℝ) ^ θ) * (m : ℝ) ^ (-3 : ℝ) * (4 * n * m) := by
        gcongr
    _ = 4 * C * n * ((m : ℝ) ^ θ * (m : ℝ) ^ (-3 : ℝ) * m) := by ring
    _ = 4 * C * n * (m : ℝ) ^ (θ - 2) := by rw [hpow]

/-- **Twisted mean of an absolutely convergent `L`-series on the line `σ = 3`.**  If `‖a m‖ ≤ C m^θ`
with `θ < 1`, then `∫_T^{2T} L(a, 3+iy) n^{iy} dy = a(n) n^{−3} T + O(4 C n Σ m^{θ−2})`. -/
theorem norm_integral_LSeries_three_phase_sub_le (a : ℕ → ℂ) {C θ : ℝ} (hC : 0 ≤ C) (hθ : θ < 1)
    (ha : ∀ m, ‖a m‖ ≤ C * (m : ℝ) ^ θ) {n : ℕ} (hn : 1 ≤ n) (T : ℝ) :
    ‖(∫ y in T..2 * T, LSeries a (3 + y * I) * cexp (((y * Real.log n : ℝ) : ℂ) * I))
        - a n * (((n : ℝ) ^ (-3 : ℝ) : ℝ) : ℂ) * T‖
      ≤ 4 * C * n * ∑' m : ℕ, (m : ℝ) ^ (θ - 2) := by
  classical
  set F : ℕ → ℝ → ℂ := fun m y => LSeries.term a (3 + y * I) m * cexp (((y * Real.log n : ℝ) : ℂ) * I)
    with hF
  set bound : ℕ → ℝ → ℝ := fun m _ => C * (m : ℝ) ^ (θ - 3) with hbound
  have hsum3 : Summable (fun m : ℕ => C * (m : ℝ) ^ (θ - 3)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left C
  have hFle : ∀ m y, ‖F m y‖ ≤ C * (m : ℝ) ^ (θ - 3) := by
    intro m y
    rcases eq_or_ne m 0 with rfl | hm
    · simp [hF, LSeries.term_def]; positivity
    · have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      rw [hF]; simp only
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, term_three_add_mul_I hm, norm_mul, norm_mul,
        norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      calc ‖a m‖ * (m : ℝ) ^ (-3 : ℝ) ≤ C * (m : ℝ) ^ θ * (m : ℝ) ^ (-3 : ℝ) := by
            gcongr; exact ha m
        _ = C * (m : ℝ) ^ (θ - 3) := by rw [mul_assoc, ← Real.rpow_add hm']; ring_nf
  -- pointwise `HasSum`
  have hpt : ∀ y : ℝ, HasSum (fun m => F m y)
      (LSeries a (3 + y * I) * cexp (((y * Real.log n : ℝ) : ℂ) * I)) := by
    intro y
    have hs : LSeriesSummable a (3 + y * I) := by
      refine Summable.of_norm_bounded hsum3 (fun m => ?_)
      have := hFle m y
      rw [hF] at this; simp only at this
      rwa [norm_mul, norm_exp_ofReal_mul_I, mul_one] at this
    exact hs.hasSum.mul_right _
  have hHas : HasSum (fun m => ∫ y in T..2 * T, F m y)
      (∫ y in T..2 * T, LSeries a (3 + y * I) * cexp (((y * Real.log n : ℝ) : ℂ) * I)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_ ?_
    · intro m
      rcases eq_or_ne m 0 with rfl | hm
      · simp [hF, LSeries.term_def]; exact aestronglyMeasurable_const
      · have : (fun y => F m y) = fun y : ℝ => a m * (((m : ℝ) ^ (-3 : ℝ) : ℝ) : ℂ)
            * cexp (((-(y * Real.log m)) : ℝ) * I) * cexp (((y * Real.log n : ℝ) : ℂ) * I) := by
          funext y; rw [hF]; simp only; rw [term_three_add_mul_I hm]
        show AEStronglyMeasurable (fun y => F m y) _
        rw [this]
        exact (Continuous.aestronglyMeasurable (by fun_prop))
    · intro m; exact Filter.Eventually.of_forall (fun y _ => hFle m y)
    · exact Filter.Eventually.of_forall (fun y _ => hsum3)
    · show IntervalIntegrable (fun _ : ℝ => ∑' m : ℕ, C * (m : ℝ) ^ (θ - 3)) volume T (2 * T)
      exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun y _ => hpt y)
  -- the integrals of the individual terms
  have hdiag : ∫ y in T..2 * T, F n y = a n * (((n : ℝ) ^ (-3 : ℝ) : ℝ) : ℂ) * T := by
    have hn0 : n ≠ 0 := by omega
    have : (fun y => F n y) = fun _ : ℝ => a n * (((n : ℝ) ^ (-3 : ℝ) : ℝ) : ℂ) := by
      funext y; rw [hF]; simp only; rw [term_three_add_mul_I hn0, mul_assoc, ← Complex.exp_add]
      have : (((-(y * Real.log n)) : ℝ) : ℂ) * I + (((y * Real.log n : ℝ) : ℂ) * I) = 0 := by
        push_cast; ring
      rw [this, Complex.exp_zero, mul_one]
    rw [this, intervalIntegral.integral_const]; simp; ring
  have hoff : ∀ m, m ≠ n → ‖∫ y in T..2 * T, F m y‖ ≤ 4 * C * n * (m : ℝ) ^ (θ - 2) := by
    intro m hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp [hF, LSeries.term_def]; positivity
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have : (fun y => F m y) = fun y : ℝ => (a m * (((m : ℝ) ^ (-3 : ℝ) : ℝ) : ℂ))
          * cexp (((y * (Real.log n - Real.log m) : ℝ) : ℂ) * I) := by
        funext y; rw [hF]; simp only; rw [term_three_add_mul_I hm, mul_assoc, ← Complex.exp_add]
        congr 2; push_cast; ring
      rw [this, intervalIntegral.integral_const_mul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hx : Real.log n - Real.log m ≠ 0 := by
        intro h0
        have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
        have := Real.log_injOn_pos (Set.mem_Ioi.mpr hn') (Set.mem_Ioi.mpr hm') (by linarith)
        exact hmn (by exact_mod_cast this.symm)
      calc ‖a m‖ * (m : ℝ) ^ (-3 : ℝ) * ‖∫ y in T..2 * T, cexp (((y * (Real.log n - Real.log m) : ℝ) : ℂ) * I)‖
          ≤ ‖a m‖ * (m : ℝ) ^ (-3 : ℝ) * (2 / |Real.log n - Real.log m|) := by
            gcongr; exact norm_integral_phase_le _ T hx
        _ ≤ 4 * C * n * (m : ℝ) ^ (θ - 2) :=
            offDiag_weight_le hC hn hm1 hmn (ha m)
  have hsum2 : Summable (fun m : ℕ => 4 * C * n * (m : ℝ) ^ (θ - 2)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  rw [← hHas.tsum_eq, hHas.summable.tsum_eq_add_tsum_ite n, hdiag, add_sub_cancel_left]
  have hnorm : ∀ m, ‖(if m = n then (0 : ℂ) else ∫ y in T..2 * T, F m y)‖
      ≤ 4 * C * n * (m : ℝ) ^ (θ - 2) := by
    intro m; split_ifs with h
    · simp; positivity
    · exact hoff m h
  calc ‖∑' m, (if m = n then (0 : ℂ) else ∫ y in T..2 * T, F m y)‖
      ≤ ∑' m, ‖(if m = n then (0 : ℂ) else ∫ y in T..2 * T, F m y)‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm hsum2)
    _ ≤ ∑' m : ℕ, 4 * C * n * (m : ℝ) ^ (θ - 2) :=
        Summable.tsum_le_tsum hnorm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm hsum2) hsum2
    _ = 4 * C * n * ∑' m : ℕ, (m : ℝ) ^ (θ - 2) := tsum_mul_left


/-- `e^{(x−σ)log n}` is the real power `n^{x−σ}`. -/
theorem cexp_mul_log_eq_rpow {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    cexp (((u * Real.log n : ℝ) : ℂ)) = (((n : ℝ) ^ u : ℝ) : ℂ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.rpow_def_of_pos hn', ← Complex.ofReal_exp]; congr 2; ring

/-- **The twisted mean on a line left of absolute convergence.**  Let `F` be holomorphic on the
half-strip `σ₁ ≤ Re s ≤ 3`, `Im s ≥ T₀`, equal to `L(a, s)` on `Re s = 3`, with `‖F(s)‖ ≤ K log Im s`.
Then `∫_T^{2T} F(σ₁+iy) n^{iy} dy = a(n) n^{−σ₁} T + O(n⁴ (4CS + 6K log 2T))`, by Cauchy's theorem on
the rectangle `[σ₁, 3] × [T, 2T]` applied to `F(s) n^{s−σ₁}`. -/
theorem norm_twistedMean_sub_le (a : ℕ → ℂ) {C θ : ℝ} (hC : 0 ≤ C) (hθ : θ < 1)
    (ha : ∀ m, ‖a m‖ ≤ C * (m : ℝ) ^ θ) (F : ℂ → ℂ) {σ₁ K T₀ : ℝ} (hσ₁ : 0 ≤ σ₁) (hσ₁3 : σ₁ ≤ 3) (hK : 0 ≤ K)
    (hF : DifferentiableOn ℂ F {s | σ₁ ≤ s.re ∧ s.re ≤ 3 ∧ T₀ ≤ s.im})
    (hFeq : ∀ y : ℝ, T₀ ≤ y → F (3 + y * I) = LSeries a (3 + y * I))
    (hFbd : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 3 → T₀ ≤ s.im → ‖F s‖ ≤ K * Real.log s.im)
    {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : T₀ ≤ T) (hT1 : 1 ≤ T) :
    ‖(∫ y in T..2 * T, F (σ₁ + y * I) * cexp (((y * Real.log n : ℝ) : ℂ) * I))
        - a n * (((n : ℝ) ^ (-σ₁) : ℝ) : ℂ) * T‖
      ≤ (n : ℝ) ^ (4 : ℕ) * (4 * C * ∑' m : ℕ, (m : ℝ) ^ (θ - 2) + 6 * K * Real.log (2 * T)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set S : ℝ := ∑' m : ℕ, (m : ℝ) ^ (θ - 2) with hS
  have hS0 : 0 ≤ S := tsum_nonneg (fun m => by positivity)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog2T : Real.log T ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
  set g : ℂ → ℂ := fun s => F s * cexp ((s - σ₁) * (Real.log n : ℂ)) with hg
  have hrect : DifferentiableOn ℂ g (Set.uIcc σ₁ 3 ×ℂ Set.uIcc T (2 * T)) := by
    refine (hF.mono ?_).mul (by fun_prop)
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    simp only [Set.uIcc_of_le hσ₁3, Set.uIcc_of_le (by linarith : T ≤ 2 * T),
      Set.mem_Icc] at hs
    exact ⟨hs.1.1, hs.1.2, le_trans hT hs.2.1⟩
  have hR := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g ⟨σ₁, T⟩ ⟨3, 2 * T⟩ hrect
  dsimp only at hR
  -- edges
  have hleft : (fun y : ℝ => g ((σ₁ : ℂ) + y * I))
      = fun y : ℝ => F (σ₁ + y * I) * cexp (((y * Real.log n : ℝ) : ℂ) * I) := by
    funext y; rw [hg]; simp only; congr 2; push_cast; ring
  have hright : (fun y : ℝ => g ((3 : ℝ) + y * I))
      = fun y : ℝ => (((n : ℝ) ^ (3 - σ₁) : ℝ) : ℂ)
          * (F (3 + y * I) * cexp (((y * Real.log n : ℝ) : ℂ) * I)) := by
    funext y; rw [hg]; simp only
    rw [← cexp_mul_log_eq_rpow hn]
    have : ((((3 : ℝ) : ℂ) + y * I) - σ₁) * (Real.log n : ℂ)
        = (((3 - σ₁) * Real.log n : ℝ) : ℂ) + ((y * Real.log n : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.exp_add]; push_cast; ring
  rw [hleft, hright] at hR
  set L := ∫ y in T..2 * T, F (σ₁ + y * I) * cexp (((y * Real.log n : ℝ) : ℂ) * I) with hL
  set Rt := ∫ y in T..2 * T, F (3 + y * I) * cexp (((y * Real.log n : ℝ) : ℂ) * I) with hRt
  set Bot := ∫ x in σ₁..3, g (x + T * I) with hBot
  set Top := ∫ x in σ₁..3, g (x + (2 * T : ℝ) * I) with hTop
  rw [intervalIntegral.integral_const_mul] at hR
  have hRt' : Rt = ∫ y in T..2 * T, LSeries a (3 + y * I) * cexp (((y * Real.log n : ℝ) : ℂ) * I) := by
    rw [hRt]; refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le (by linarith : T ≤ 2 * T)] at hy
    rw [hFeq y (le_trans hT hy.1)]
  -- edge bounds
  have hedge : ∀ τ : ℝ, T ≤ τ → τ ≤ 2 * T →
      ‖∫ x in σ₁..3, g (x + τ * I)‖ ≤ K * Real.log (2 * T) * (n : ℝ) ^ (3 - σ₁) * 3 := by
    intro τ hτ1 hτ2
    have hb : ∀ x ∈ Set.uIoc σ₁ 3, ‖g (x + τ * I)‖ ≤ K * Real.log (2 * T) * (n : ℝ) ^ (3 - σ₁) := by
      intro x hx
      rw [Set.uIoc_of_le hσ₁3] at hx
      rw [hg]; simp only
      rw [norm_mul]
      have hre : ((x : ℂ) + τ * I).re = x := by simp
      have him : ((x : ℂ) + τ * I).im = τ := by simp
      have hF1 := hFbd ((x : ℂ) + τ * I) (by rw [hre]; exact hx.1.le) (by rw [hre]; exact hx.2)
        (by rw [him]; linarith)
      rw [him] at hF1
      have hexp : ‖cexp (((x : ℂ) + τ * I - σ₁) * (Real.log n : ℂ))‖ = (n : ℝ) ^ (x - σ₁) := by
        rw [Complex.norm_exp]
        have : (((x : ℂ) + τ * I - σ₁) * ((Real.log n : ℝ) : ℂ)).re = (x - σ₁) * Real.log n := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
          ring
        rw [this, Real.rpow_def_of_pos hnpos]; ring_nf
      rw [hexp]
      have h1 : K * Real.log τ ≤ K * Real.log (2 * T) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hτ2) hK
      have h2 : (n : ℝ) ^ (x - σ₁) ≤ (n : ℝ) ^ (3 - σ₁) :=
        Real.rpow_le_rpow_of_exponent_le hn' (by linarith [hx.2])
      have h3 : 0 ≤ K * Real.log (2 * T) := mul_nonneg hK (by linarith)
      exact mul_le_mul (hF1.trans h1) h2 (by positivity) h3
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
    have : |3 - σ₁| ≤ 3 := by rw [abs_of_nonneg (by linarith)]; linarith
    have h0 : 0 ≤ K * Real.log (2 * T) * (n : ℝ) ^ (3 - σ₁) :=
      mul_nonneg (mul_nonneg hK (by linarith)) (by positivity)
    exact mul_le_mul_of_nonneg_left this h0
  have hBotle := hedge T le_rfl (by linarith)
  have hTople := hedge (2 * T) (by linarith) le_rfl
  -- L = n^{3−σ₁} Rt − I (Bot − Top)
  have hLeq : L = (((n : ℝ) ^ (3 - σ₁) : ℝ) : ℂ) * Rt - I * (Bot - Top) := by
    have hR' : Bot - Top + I * ((((n : ℝ) ^ (3 - σ₁) : ℝ) : ℂ) * Rt) - I * L = 0 := hR
    have hI2 : I * I = -1 := I_mul_I
    linear_combination I * hR' + (L - (((n : ℝ) ^ (3 - σ₁) : ℝ) : ℂ) * Rt) * hI2
  have hmain := norm_integral_LSeries_three_phase_sub_le a hC hθ ha hn T
  rw [← hRt'] at hmain
  have hpow : (((n : ℝ) ^ (3 - σ₁) : ℝ) : ℂ) * (a n * (((n : ℝ) ^ (-3 : ℝ) : ℝ) : ℂ) * T)
      = a n * (((n : ℝ) ^ (-σ₁) : ℝ) : ℂ) * T := by
    have : (n : ℝ) ^ (3 - σ₁) * (n : ℝ) ^ (-3 : ℝ) = (n : ℝ) ^ (-σ₁) := by
      rw [← Real.rpow_add hnpos]; ring_nf
    rw [← this]; push_cast; ring
  have hsplit : L - a n * (((n : ℝ) ^ (-σ₁) : ℝ) : ℂ) * T
      = (((n : ℝ) ^ (3 - σ₁) : ℝ) : ℂ) * (Rt - a n * (((n : ℝ) ^ (-3 : ℝ) : ℝ) : ℂ) * T)
        - I * (Bot - Top) := by
    rw [hLeq, ← hpow]; ring
  have hn3 : (n : ℝ) ^ (3 - σ₁) ≤ (n : ℝ) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hn' (by push_cast; linarith)
  have hn34 : (n : ℝ) ^ (3 : ℕ) * n = (n : ℝ) ^ (4 : ℕ) := by ring
  have hn3le4 : (n : ℝ) ^ (3 : ℕ) ≤ (n : ℝ) ^ (4 : ℕ) := by
    rw [← hn34]; nlinarith [pow_pos hnpos 3]
  rw [hsplit]
  calc ‖(((n : ℝ) ^ (3 - σ₁) : ℝ) : ℂ) * (Rt - a n * (((n : ℝ) ^ (-3 : ℝ) : ℝ) : ℂ) * T) - I * (Bot - Top)‖
      ≤ (n : ℝ) ^ (3 - σ₁) * (4 * C * n * S) + (‖Bot‖ + ‖Top‖) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          Complex.norm_I, one_mul]
        gcongr
        exact norm_sub_le _ _
    _ ≤ (n : ℝ) ^ (3 : ℕ) * (4 * C * n * S) + 2 * (K * Real.log (2 * T) * (n : ℝ) ^ (3 : ℕ) * 3) := by
        have hc : 0 ≤ K * Real.log (2 * T) := mul_nonneg hK (by linarith)
        have e1 : K * Real.log (2 * T) * (n : ℝ) ^ (3 - σ₁) * 3 ≤ K * Real.log (2 * T) * (n : ℝ) ^ (3 : ℕ) * 3 := by
          gcongr
        have e2 : (n : ℝ) ^ (3 - σ₁) * (4 * C * n * S) ≤ (n : ℝ) ^ (3 : ℕ) * (4 * C * n * S) := by
          gcongr
        linarith
    _ = (n : ℝ) ^ (4 : ℕ) * (4 * C * S) + (n : ℝ) ^ (3 : ℕ) * (6 * K * Real.log (2 * T)) := by
        rw [← hn34]; ring
    _ ≤ (n : ℝ) ^ (4 : ℕ) * (4 * C * S) + (n : ℝ) ^ (4 : ℕ) * (6 * K * Real.log (2 * T)) := by
        gcongr
        exact mul_nonneg (mul_nonneg (by norm_num) hK) (by linarith)
    _ = (n : ℝ) ^ (4 : ℕ) * (4 * C * S + 6 * K * Real.log (2 * T)) := by ring

open RHTower.Sieve in
/-- **Dual mean value inequality.**  For `f` continuous on `[T, 2T]`,
`∑_{m<N} |∫_T^{2T} f(y) (m+1)^{iy} dy|² ≤ (T + 104N) ∫_T^{2T} |f|²`: the transpose of the sharp
Montgomery–Vaughan mean value theorem, via `Q ≤ ∫|f||P| ≤ (M/2)∫|f|² + (1/2M)∫|P|²`. -/
theorem sum_normSq_integral_phase_le (N : ℕ) {T : ℝ} (hT : 0 < T) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Set.uIcc T (2 * T))) :
    ∑ m : Fin N, ‖∫ y in T..2 * T, f y * cexp (((y * Real.log ((m : ℕ) + 1) : ℝ) : ℂ) * I)‖ ^ 2
      ≤ (T + 104 * N) * ∫ y in T..2 * T, ‖f y‖ ^ 2 := by
  classical
  set e : Fin N → ℝ → ℂ := fun m y => cexp (((y * Real.log ((m : ℕ) + 1) : ℝ) : ℂ) * I) with he
  set b : Fin N → ℂ := fun m => ∫ y in T..2 * T, f y * e m y with hb
  set P : ℝ → ℂ := dirPoly N (fun m => (starRingEnd ℂ) (b m)) with hP
  set Q : ℝ := ∑ m : Fin N, ‖b m‖ ^ 2 with hQ
  set M : ℝ := T + 104 * N with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hT2 : T ≤ 2 * T := by linarith
  have he_cont : ∀ m, Continuous (e m) := fun m => by rw [he]; fun_prop
  have hP_cont : Continuous P := by
    rw [hP]; unfold dirPoly; fun_prop
  have hfe_int : ∀ m, IntervalIntegrable (fun y => f y * e m y) volume T (2 * T) :=
    fun m => (hf.mul (he_cont m).continuousOn).intervalIntegrable
  -- (1) `Q = ∫ f P`
  have h1 : (Q : ℂ) = ∫ y in T..2 * T, f y * P y := by
    have hPy : ∀ y, f y * P y = ∑ m : Fin N, (starRingEnd ℂ) (b m) * (f y * e m y) := by
      intro y; rw [hP]; unfold dirPoly; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_); rw [he]; ring
    simp_rw [hPy]
    rw [intervalIntegral.integral_finsetSum (fun m _ => (hfe_int m).const_mul _)]
    rw [hQ]; push_cast
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [intervalIntegral.integral_const_mul]
    have hbm : (∫ x in T..2 * T, f x * e m x) = b m := rfl
    rw [hbm, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  -- (2) `Q ≤ ∫ ‖f‖ ‖P‖`
  have h2 : Q ≤ ∫ y in T..2 * T, ‖f y‖ * ‖P y‖ := by
    have : Q = ‖((Q : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [this, h1]
    refine (intervalIntegral.norm_integral_le_integral_norm hT2).trans (le_of_eq ?_)
    congr 1; funext y; rw [norm_mul]
  -- (3) AM–GM
  have hfint : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume T (2 * T) :=
    ((continuous_norm.comp_continuousOn hf).pow 2).intervalIntegrable
  have hPint : IntervalIntegrable (fun y => ‖P y‖ ^ 2) volume T (2 * T) :=
    ((continuous_norm.comp hP_cont).pow 2).intervalIntegrable _ _
  have hfPint : IntervalIntegrable (fun y => ‖f y‖ * ‖P y‖) volume T (2 * T) :=
    ((continuous_norm.comp_continuousOn hf).mul (continuous_norm.comp hP_cont).continuousOn).intervalIntegrable
  have h3 : (∫ y in T..2 * T, ‖f y‖ * ‖P y‖)
      ≤ (M / 2) * (∫ y in T..2 * T, ‖f y‖ ^ 2) + (1 / (2 * M)) * ∫ y in T..2 * T, ‖P y‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hfint.const_mul _) (hPint.const_mul _)]
    refine intervalIntegral.integral_mono_on hT2 hfPint ((hfint.const_mul _).add (hPint.const_mul _))
      (fun y _ => ?_)
    have hsq : 0 ≤ (M * ‖f y‖ - ‖P y‖) ^ 2 := sq_nonneg _
    have : ‖f y‖ * ‖P y‖ = (M ^ 2 * ‖f y‖ ^ 2 + ‖P y‖ ^ 2 - (M * ‖f y‖ - ‖P y‖) ^ 2) / (2 * M) := by
      field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [hsq]
  -- (4) `∫_T^{2T} ‖P‖² ≤ M Q`
  have h4 : (∫ y in T..2 * T, ‖P y‖ ^ 2) ≤ M * Q := by
    have hshift : (∫ y in T..2 * T, ‖P y‖ ^ 2) = ∫ y in (0 : ℝ)..T, ‖P (y + T)‖ ^ 2 := by
      rw [intervalIntegral.integral_comp_add_right (fun y => ‖P y‖ ^ 2) T]
      congr 1 <;> ring
    set b'' : Fin N → ℂ := fun m => (starRingEnd ℂ) (b m)
      * cexp (((T * Real.log ((m : ℕ) + 1) : ℝ) : ℂ) * I) with hb''
    have hPT : ∀ y, P (y + T) = dirPoly N b'' y := by
      intro y; rw [hP]; unfold dirPoly
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hb'', mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
    have hnorm : ∀ m, ‖b'' m‖ = ‖b m‖ := by
      intro m; rw [hb'']; simp only; rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_conj]
    have hMV := dirichlet_meanValue_sharp N b'' T
    simp_rw [hPT] at hshift
    rw [hshift]
    have hle := (abs_le.mp hMV).2
    have hsum : ∑ m : Fin N, (((m : ℕ) : ℝ) + 1) * ‖b'' m‖ ^ 2 ≤ N * ∑ m : Fin N, ‖b'' m‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun m _ => ?_)
      have : ((m : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast m.isLt
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hQ'' : ∑ m : Fin N, ‖b'' m‖ ^ 2 = Q := by rw [hQ]; simp_rw [hnorm]
    rw [hQ''] at hsum hle
    rw [hM]; nlinarith
  -- (5) conclude
  have hQle : Q ≤ (M / 2) * (∫ y in T..2 * T, ‖f y‖ ^ 2) + (1 / (2 * M)) * (M * Q) :=
    h2.trans (h3.trans (by gcongr))
  have : (1 / (2 * M)) * (M * Q) = Q / 2 := by field_simp
  rw [this] at hQle
  show Q ≤ M * ∫ y in T..2 * T, ‖f y‖ ^ 2
  linarith


/-- The closing arithmetic of Carlson's partial-sum bound. -/
theorem carlson_final_arith (K C S L₀ x : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hS : 0 ≤ S) (hL : 0 ≤ L₀)
    (hx : 0 ≤ x) :
    210 * (K * (L₀ + 5 * x)) ^ 2 + 2 * (4 * C * S + 6 * K * (L₀ + 5 * x)) ^ 2
      ≤ (210 * K ^ 2 * (L₀ + 5) ^ 2 + 2 * (4 * C * S + 6 * K * L₀ + 30 * K) ^ 2) * (1 + x) ^ 2 := by
  have hA : L₀ + 5 * x ≤ (L₀ + 5) * (1 + x) := by nlinarith [mul_nonneg hL hx]
  have hB : 4 * C * S + 6 * K * (L₀ + 5 * x) ≤ (4 * C * S + 6 * K * L₀ + 30 * K) * (1 + x) := by
    nlinarith [mul_nonneg (mul_nonneg hC hS) hx, mul_nonneg (mul_nonneg hK hL) hx]
  have hA0 : 0 ≤ L₀ + 5 * x := by linarith
  have hB0 : 0 ≤ 4 * C * S + 6 * K * (L₀ + 5 * x) := by positivity
  have hA2 := pow_le_pow_left₀ hA0 hA 2
  have hB2 := pow_le_pow_left₀ hB0 hB 2
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  calc 210 * (K * (L₀ + 5 * x)) ^ 2 + 2 * (4 * C * S + 6 * K * (L₀ + 5 * x)) ^ 2
      = 210 * (K ^ 2 * (L₀ + 5 * x) ^ 2) + 2 * (4 * C * S + 6 * K * (L₀ + 5 * x)) ^ 2 := by ring
    _ ≤ 210 * (K ^ 2 * ((L₀ + 5) * (1 + x)) ^ 2)
        + 2 * ((4 * C * S + 6 * K * L₀ + 30 * K) * (1 + x)) ^ 2 := by gcongr
    _ = (210 * K ^ 2 * (L₀ + 5) ^ 2 + 2 * (4 * C * S + 6 * K * L₀ + 30 * K) ^ 2) * (1 + x) ^ 2 := by
        ring

/-- **Carlson's partial-sum bound.**  Under the hypotheses of `norm_twistedMean_sub_le` (with
`T₀ ≥ 1`), the weighted coefficient energy grows at most like `log² N`:
`∑_{n ≤ N} |a(n)|² n^{−2σ₁} ≤ B (1 + log N)²`.  Choose `T = T₀ N⁵`, recover each `a(n)` from its twisted
mean, and bound the twisted means jointly by the dual mean value inequality. -/
theorem exists_sum_sq_rpow_le_log_sq (a : ℕ → ℂ) {C θ : ℝ} (hC : 0 ≤ C) (hθ : θ < 1)
    (ha : ∀ m, ‖a m‖ ≤ C * (m : ℝ) ^ θ) (F : ℂ → ℂ) {σ₁ K T₀ : ℝ} (hσ₁ : 0 ≤ σ₁) (hσ₁3 : σ₁ ≤ 3)
    (hK : 0 ≤ K) (hT₀ : 1 ≤ T₀)
    (hF : DifferentiableOn ℂ F {s | σ₁ ≤ s.re ∧ s.re ≤ 3 ∧ T₀ ≤ s.im})
    (hFeq : ∀ y : ℝ, T₀ ≤ y → F (3 + y * I) = LSeries a (3 + y * I))
    (hFbd : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 3 → T₀ ≤ s.im → ‖F s‖ ≤ K * Real.log s.im) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ 2 * ((((m : ℕ) + 1 : ℕ) : ℝ) ^ (-σ₁)) ^ 2
        ≤ B * (1 + Real.log N) ^ 2 := by
  set S : ℝ := ∑' m : ℕ, (m : ℝ) ^ (θ - 2) with hS
  have hS0 : 0 ≤ S := tsum_nonneg (fun m => by positivity)
  set L₀ : ℝ := Real.log (2 * T₀) with hL₀
  have hL₀0 : 0 ≤ L₀ := Real.log_nonneg (by linarith)
  refine ⟨210 * K ^ 2 * (L₀ + 5) ^ 2 + 2 * (4 * C * S + 6 * K * L₀ + 30 * K) ^ 2, by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set T : ℝ := T₀ * (N : ℝ) ^ (5 : ℕ) with hTdef
  have hN5 : (1 : ℝ) ≤ (N : ℝ) ^ (5 : ℕ) := one_le_pow₀ hN1
  have hT₀T : T₀ ≤ T := by rw [hTdef]; nlinarith
  have hT1 : 1 ≤ T := le_trans hT₀ hT₀T
  have hTpos : 0 < T := by linarith
  have hNT : (N : ℝ) ≤ T := by
    have : (N : ℝ) ≤ (N : ℝ) ^ (5 : ℕ) := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (N : ℝ) ^ (5 : ℕ) := pow_le_pow_right₀ hN1 (by norm_num)
    rw [hTdef]; nlinarith
  have hN10 : (N : ℝ) ^ (10 : ℕ) ≤ T ^ 2 := by
    rw [hTdef]
    have : (N : ℝ) ^ (10 : ℕ) = ((N : ℝ) ^ (5 : ℕ)) ^ 2 := by ring
    rw [this, mul_pow]
    have h1 : 1 ≤ T₀ ^ 2 := one_le_pow₀ hT₀
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ((N : ℝ) ^ (5 : ℕ)))]
  have hlog2T : Real.log (2 * T) = L₀ + 5 * Real.log N := by
    rw [hTdef, hL₀, show 2 * (T₀ * (N : ℝ) ^ (5 : ℕ)) = (2 * T₀) * (N : ℝ) ^ (5 : ℕ) by ring,
      Real.log_mul (by linarith) (by positivity), Real.log_pow]; push_cast; ring
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  set Bt : ℝ := 4 * C * S + 6 * K * Real.log (2 * T) with hBt
  have hBt0 : 0 ≤ Bt := by
    rw [hBt, hlog2T]; positivity
  -- the function on the left line
  set f : ℝ → ℂ := fun y => F (σ₁ + y * I) with hfdef
  have hfcont : ContinuousOn f (Set.uIcc T (2 * T)) := by
    rw [Set.uIcc_of_le (by linarith)]
    refine hF.continuousOn.comp (by fun_prop) (fun y hy => ?_)
    refine ⟨by simp, by simp; exact hσ₁3, by simp; exact le_trans hT₀T hy.1⟩
  have hfbd : ∀ y ∈ Set.uIcc T (2 * T), ‖f y‖ ≤ K * Real.log (2 * T) := by
    intro y hy
    rw [Set.uIcc_of_le (by linarith)] at hy
    have h := hFbd (σ₁ + y * I) (by simp) (by simp; exact hσ₁3) (by simp; linarith [hy.1])
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [hy.1]) hy.2) hK)
  have hfint : (∫ y in T..2 * T, ‖f y‖ ^ 2) ≤ T * (K * Real.log (2 * T)) ^ 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2 * T)
      (f := fun y => ‖f y‖ ^ 2) (C := (K * Real.log (2 * T)) ^ 2) (fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hy' : y ∈ Set.uIcc T (2 * T) := Set.uIoc_subset_uIcc hy
        exact pow_le_pow_left₀ (norm_nonneg _) (hfbd y hy') 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg (by linarith)
      (fun y _ => by positivity))] at this
    rw [show |2 * T - T| = T by rw [abs_of_nonneg (by linarith)]; ring] at this
    linarith
  have hdual := sum_normSq_integral_phase_le N hTpos f hfcont
  -- each coefficient from its twisted mean
  have hcoef : ∀ m : Fin N,
      T ^ 2 * (‖a ((m : ℕ) + 1)‖ ^ 2 * ((((m : ℕ) + 1 : ℕ) : ℝ) ^ (-σ₁)) ^ 2)
        ≤ 2 * ‖∫ y in T..2 * T, f y * cexp (((y * Real.log ((m : ℕ) + 1) : ℝ) : ℂ) * I)‖ ^ 2
          + 2 * ((N : ℝ) ^ (8 : ℕ) * Bt ^ 2) := by
    intro m
    have hn : 1 ≤ (m : ℕ) + 1 := by omega
    have htw := norm_twistedMean_sub_le a hC hθ ha F hσ₁ hσ₁3 hK hF hFeq hFbd hn hT₀T hT1
    have hcast : Real.log ((((m : ℕ) + 1 : ℕ) : ℝ)) = Real.log ((m : ℕ) + 1) := by push_cast; ring_nf
    rw [hcast] at htw
    set Im := ∫ y in T..2 * T, f y * cexp (((y * Real.log ((m : ℕ) + 1) : ℝ) : ℂ) * I) with hIm
    set c : ℂ := a ((m : ℕ) + 1) * (((((m : ℕ) + 1 : ℕ) : ℝ) ^ (-σ₁) : ℝ) : ℂ) * T with hc
    have hcnorm : ‖c‖ = T * (‖a ((m : ℕ) + 1)‖ * ((((m : ℕ) + 1 : ℕ) : ℝ) ^ (-σ₁))) := by
      rw [hc, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hTpos.le]; ring
    have hn8 : ((((m : ℕ) + 1 : ℕ) : ℝ)) ^ (4 : ℕ) ≤ (N : ℝ) ^ (4 : ℕ) := by
      have : ((((m : ℕ) + 1 : ℕ) : ℝ)) ≤ N := by exact_mod_cast m.isLt
      exact pow_le_pow_left₀ (by positivity) this 4
    have hE : ‖Im - c‖ ≤ (N : ℝ) ^ (4 : ℕ) * Bt := by
      refine htw.trans ?_
      rw [hBt]; exact mul_le_mul_of_nonneg_right hn8 (by rw [hlog2T]; positivity)
    have hcle : ‖c‖ ≤ ‖Im‖ + (N : ℝ) ^ (4 : ℕ) * Bt := by
      have := norm_sub_norm_le c Im
      rw [norm_sub_rev] at this; linarith
    have hsq : ‖c‖ ^ 2 ≤ 2 * ‖Im‖ ^ 2 + 2 * ((N : ℝ) ^ (4 : ℕ) * Bt) ^ 2 := by
      have h0 : 0 ≤ ‖c‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖Im‖ - (N : ℝ) ^ (4 : ℕ) * Bt), norm_nonneg Im]
    rw [hcnorm] at hsq
    have : ((N : ℝ) ^ (4 : ℕ) * Bt) ^ 2 = (N : ℝ) ^ (8 : ℕ) * Bt ^ 2 := by ring
    rw [this] at hsq
    nlinarith [hsq]
  -- sum the coefficient bounds
  have hsumT : T ^ 2 * ∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ 2 * ((((m : ℕ) + 1 : ℕ) : ℝ) ^ (-σ₁)) ^ 2
      ≤ 2 * ((T + 104 * N) * (T * (K * Real.log (2 * T)) ^ 2)) + 2 * ((N : ℝ) ^ (9 : ℕ) * Bt ^ 2) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum (fun m _ => hcoef m)).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have h1 := hdual.trans (mul_le_mul_of_nonneg_left hfint (by positivity))
    have : (N : ℝ) * (2 * ((N : ℝ) ^ (8 : ℕ) * Bt ^ 2)) = 2 * ((N : ℝ) ^ (9 : ℕ) * Bt ^ 2) := by ring
    rw [this]; linarith
  -- divide by `T²`
  set Ssum := ∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ 2 * ((((m : ℕ) + 1 : ℕ) : ℝ) ^ (-σ₁)) ^ 2 with hSsum
  have hT2pos : 0 < T ^ 2 := by positivity
  have hfirst : 2 * ((T + 104 * N) * (T * (K * Real.log (2 * T)) ^ 2)) ≤ T ^ 2 * (210 * (K * Real.log (2 * T)) ^ 2) := by
    have h105 : T + 104 * N ≤ 105 * T := by linarith
    have hk : 0 ≤ T * (K * Real.log (2 * T)) ^ 2 := mul_nonneg hTpos.le (sq_nonneg _)
    calc 2 * ((T + 104 * N) * (T * (K * Real.log (2 * T)) ^ 2))
        ≤ 2 * ((105 * T) * (T * (K * Real.log (2 * T)) ^ 2)) := by gcongr
      _ = T ^ 2 * (210 * (K * Real.log (2 * T)) ^ 2) := by ring
  have hsecond : 2 * ((N : ℝ) ^ (9 : ℕ) * Bt ^ 2) ≤ T ^ 2 * (2 * Bt ^ 2) := by
    have h9 : (N : ℝ) ^ (9 : ℕ) ≤ T ^ 2 :=
      (pow_le_pow_right₀ hN1 (by norm_num : 9 ≤ 10)).trans hN10
    have hb : 0 ≤ Bt ^ 2 := sq_nonneg _
    calc 2 * ((N : ℝ) ^ (9 : ℕ) * Bt ^ 2) ≤ 2 * (T ^ 2 * Bt ^ 2) := by gcongr
      _ = T ^ 2 * (2 * Bt ^ 2) := by ring
  have hSle : Ssum ≤ 210 * (K * Real.log (2 * T)) ^ 2 + 2 * Bt ^ 2 := by
    have : T ^ 2 * Ssum ≤ T ^ 2 * (210 * (K * Real.log (2 * T)) ^ 2 + 2 * Bt ^ 2) := by linarith
    exact le_of_mul_le_mul_left this hT2pos
  refine hSle.trans ?_
  clear hcoef hsumT hdual hfint hfbd hfcont hfirst hsecond
  rw [hBt, hlog2T]
  exact carlson_final_arith K C S L₀ (Real.log N) hK hC hS0 hL₀0 hlogN

/-- `(1 + log x)² ≤ (1 + 1/ε)² x^{2ε}` for `x ≥ 1`. -/
theorem one_add_log_sq_le {ε x : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) :
    (1 + Real.log x) ^ 2 ≤ (1 + 1 / ε) ^ 2 * x ^ (2 * ε) := by
  have hx0 : 0 ≤ x := by linarith
  have hlog : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hx0 hε
  have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : 1 + Real.log x ≤ (1 + 1 / ε) * x ^ ε := by
    have : x ^ ε / ε = (1 / ε) * x ^ ε := by ring
    rw [this] at hlog; nlinarith
  have h2 : (1 + Real.log x) ^ 2 ≤ ((1 + 1 / ε) * x ^ ε) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  calc (1 + Real.log x) ^ 2 ≤ ((1 + 1 / ε) * x ^ ε) ^ 2 := h2
    _ = (1 + 1 / ε) ^ 2 * x ^ (2 * ε) := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ ε) 2, ← Real.rpow_mul hx0]; push_cast; ring_nf

/-- The difference bound `x^{−δ} − (x+1)^{−δ} ≤ δ x^{−δ−1}` for `x > 0`. -/
theorem rpow_neg_sub_rpow_neg_succ_le {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) :
    x ^ (-δ) - (x + 1) ^ (-δ) ≤ δ * x ^ (-δ - 1) := by
  have hx1 : 0 < x + 1 := by linarith
  -- `(x+1)^{−δ} = x^{−δ} e^{−δ log(1+1/x)} ≥ x^{−δ}(1 − δ/x)`
  have hratio : (x + 1) ^ (-δ) = x ^ (-δ) * Real.exp (-δ * Real.log (1 + 1 / x)) := by
    rw [Real.rpow_def_of_pos hx1, Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1
    have : 1 + 1 / x = (x + 1) / x := by field_simp
    rw [this, Real.log_div hx1.ne' hx.ne']; ring
  have hlog : Real.log (1 + 1 / x) ≤ 1 / x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / x by positivity); linarith
  have hexp : 1 - δ / x ≤ Real.exp (-δ * Real.log (1 + 1 / x)) := by
    have h := Real.add_one_le_exp (-δ * Real.log (1 + 1 / x))
    have : -δ * (1 / x) ≤ -δ * Real.log (1 + 1 / x) := by nlinarith
    have e : -δ * (1 / x) = -(δ / x) := by ring
    linarith
  have hxd : 0 < x ^ (-δ) := Real.rpow_pos_of_pos hx _
  have hpow : x ^ (-δ - 1) = x ^ (-δ) / x := by
    rw [Real.rpow_sub_one hx.ne']
  rw [hratio, hpow]
  have : x ^ (-δ) - x ^ (-δ) * Real.exp (-δ * Real.log (1 + 1 / x))
      ≤ x ^ (-δ) - x ^ (-δ) * (1 - δ / x) := by
    have := mul_le_mul_of_nonneg_left hexp hxd.le; linarith
  refine this.trans (le_of_eq ?_)
  field_simp; ring

/-- **Abel summation against a `log²` partial-sum bound.**  If `c ≥ 0` and
`∑_{n<N} c(n) ≤ B (1 + log N)²` for `N ≥ 1`, then `∑ c(n) (n+1)^{−δ}` converges for every `δ > 0`. -/
theorem summable_mul_rpow_neg_of_sum_le {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {B δ : ℝ} (hB : 0 ≤ B)
    (hδ : 0 < δ) (hP : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.range N, c n ≤ B * (1 + Real.log N) ^ 2) :
    Summable (fun n : ℕ => c n * ((n : ℝ) + 1) ^ (-δ)) := by
  classical
  set f : ℕ → ℝ := fun i => ((i : ℝ) + 1) ^ (-δ) with hf
  set Z : ℝ := ∑' i : ℕ, ((i : ℝ) + 1) ^ (-1 - δ / 2) with hZ
  have hZs : Summable (fun i : ℕ => ((i : ℝ) + 1) ^ (-1 - δ / 2)) := by
    have := (Real.summable_nat_rpow.mpr (show -1 - δ / 2 < -1 by linarith))
    have h := (summable_nat_add_iff 1).mpr this
    refine h.congr (fun i => ?_); push_cast; ring_nf
  have hZ0 : 0 ≤ Z := tsum_nonneg (fun i => by positivity)
  set K1 : ℝ := (1 + 1 / (δ / 2)) ^ 2 with hK1
  set K2 : ℝ := (1 + 1 / (δ / 4)) ^ 2 with hK2
  refine summable_of_sum_range_le (fun n => mul_nonneg (hc n) (by positivity))
    (c := B * K1 + B * K2 * δ * Z) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  have hG : ∀ k, 1 ≤ k → ∑ j ∈ Finset.range k, c j ≤ B * (1 + Real.log k) ^ 2 := hP
  have hparts := Finset.sum_range_by_parts f c n
  simp only [smul_eq_mul] at hparts
  have hsum_eq : ∑ i ∈ Finset.range n, c i * ((i : ℝ) + 1) ^ (-δ) = ∑ i ∈ Finset.range n, f i * c i := by
    refine Finset.sum_congr rfl (fun i _ => ?_); rw [hf]; ring
  rw [hsum_eq, hparts]
  -- first term
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT1 : f (n - 1) * ∑ i ∈ Finset.range n, c i ≤ B * K1 := by
    have hfn : f (n - 1) = (n : ℝ) ^ (-δ) := by
      rw [hf]; simp only; congr 1; rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hfn]
    have hlog := one_add_log_sq_le (show 0 < δ / 2 by linarith) hn1
    rw [← hK1, show 2 * (δ / 2) = δ by ring] at hlog
    have hnd : 0 < (n : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by linarith) _
    calc (n : ℝ) ^ (-δ) * ∑ i ∈ Finset.range n, c i ≤ (n : ℝ) ^ (-δ) * (B * (1 + Real.log n) ^ 2) :=
          mul_le_mul_of_nonneg_left (hG n hn) hnd.le
      _ ≤ (n : ℝ) ^ (-δ) * (B * (K1 * (n : ℝ) ^ δ)) := by gcongr
      _ = B * K1 * ((n : ℝ) ^ (-δ) * (n : ℝ) ^ δ) := by ring
      _ = B * K1 := by
          rw [← Real.rpow_add (by linarith), neg_add_cancel, Real.rpow_zero, mul_one]
  -- second term
  have hT2 : -∑ i ∈ Finset.range (n - 1), (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), c j
      ≤ B * K2 * δ * Z := by
    rw [← Finset.sum_neg_distrib]
    have hterm : ∀ i : ℕ, -((f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), c j)
        ≤ B * K2 * δ * ((i : ℝ) + 1) ^ (-1 - δ / 2) := by
      intro i
      have hx : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have hx1 : (1 : ℝ) ≤ (i : ℝ) + 1 := by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
      have hdiff := rpow_neg_sub_rpow_neg_succ_le hδ hx
      have hfi : f i = ((i : ℝ) + 1) ^ (-δ) := rfl
      have hfi1 : f (i + 1) = ((i : ℝ) + 1 + 1) ^ (-δ) := by rw [hf]; simp only; push_cast; ring_nf
      have hdec : 0 ≤ f i - f (i + 1) := by
        rw [hfi, hfi1]
        exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hx (by linarith) (by linarith))
      have hGi := hG (i + 1) (by omega)
      have hlog := one_add_log_sq_le (show 0 < δ / 4 by linarith) hx1
      rw [← hK2, show 2 * (δ / 4) = δ / 2 by ring] at hlog
      have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hGi
      have hGnn : 0 ≤ ∑ j ∈ Finset.range (i + 1), c j := Finset.sum_nonneg (fun j _ => hc j)
      calc -((f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), c j)
          = (f i - f (i + 1)) * ∑ j ∈ Finset.range (i + 1), c j := by ring
        _ ≤ (δ * ((i : ℝ) + 1) ^ (-δ - 1)) * (B * (K2 * ((i : ℝ) + 1) ^ (δ / 2))) := by
            apply mul_le_mul _ _ hGnn (by positivity)
            · rw [hfi, hfi1]; exact hdiff
            · exact hGi.trans (mul_le_mul_of_nonneg_left hlog hB)
        _ = B * K2 * δ * (((i : ℝ) + 1) ^ (-δ - 1) * ((i : ℝ) + 1) ^ (δ / 2)) := by ring
        _ = B * K2 * δ * ((i : ℝ) + 1) ^ (-1 - δ / 2) := by
            rw [← Real.rpow_add hx]; ring_nf
    calc ∑ i ∈ Finset.range (n - 1), -((f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), c j)
        ≤ ∑ i ∈ Finset.range (n - 1), B * K2 * δ * ((i : ℝ) + 1) ^ (-1 - δ / 2) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = B * K2 * δ * ∑ i ∈ Finset.range (n - 1), ((i : ℝ) + 1) ^ (-1 - δ / 2) := by
          rw [Finset.mul_sum]
      _ ≤ B * K2 * δ * Z := by
          gcongr
          exact hZs.sum_le_tsum _ (fun i _ => by positivity)
  linarith [hT1, hT2]

/-- **Carlson's theorem in the form used here.**  Let `‖a m‖ ≤ C m^θ` with `θ < 1`, and let `F` be
holomorphic on the half-strip `σ₁ ≤ Re s ≤ 3`, `Im s ≥ T₀`, equal to `L(a, s)` on `Re s = 3`, with
`‖F(s)‖ ≤ K log Im s`.  Then `L(a, ·)` converges absolutely at every real `y > σ₁ + 1/2`. -/
theorem LSeriesSummable_of_logGrowth (a : ℕ → ℂ) {C θ : ℝ} (hC : 0 ≤ C) (hθ : θ < 1)
    (ha : ∀ m, ‖a m‖ ≤ C * (m : ℝ) ^ θ) (F : ℂ → ℂ) {σ₁ K T₀ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁3 : σ₁ ≤ 3)
    (hK : 0 ≤ K) (hT₀ : 1 ≤ T₀)
    (hF : DifferentiableOn ℂ F {s | σ₁ ≤ s.re ∧ s.re ≤ 3 ∧ T₀ ≤ s.im})
    (hFeq : ∀ y : ℝ, T₀ ≤ y → F (3 + y * I) = LSeries a (3 + y * I))
    (hFbd : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 3 → T₀ ≤ s.im → ‖F s‖ ≤ K * Real.log s.im)
    {y : ℝ} (hy : σ₁ + 1 / 2 < y) : LSeriesSummable a y := by
  obtain ⟨B, hB0, hBN⟩ :=
    exists_sum_sq_rpow_le_log_sq a hC hθ ha F hσ₁.le hσ₁3 hK hT₀ hF hFeq hFbd
  set c : ℕ → ℝ := fun m => ‖a (m + 1)‖ ^ 2 * ((((m + 1 : ℕ) : ℝ)) ^ (-σ₁)) ^ 2 with hc
  have hc0 : ∀ m, 0 ≤ c m := fun m => by positivity
  have hP : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.range N, c n ≤ B * (1 + Real.log N) ^ 2 := by
    intro N hN
    rw [Finset.sum_range]; exact hBN N hN
  set δ : ℝ := y - σ₁ - 1 / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hAbel := summable_mul_rpow_neg_of_sum_le hc0 hB0 hδ0 hP
  have hgeo : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-1 - δ)) := by
    have := (Real.summable_nat_rpow.mpr (show -1 - δ < -1 by linarith))
    refine ((summable_nat_add_iff 1).mpr this).congr (fun m => ?_); push_cast; ring_nf
  have hmaj : Summable (fun m : ℕ => (c m * ((m : ℝ) + 1) ^ (-δ) + ((m : ℝ) + 1) ^ (-1 - δ)) / 2) :=
    (hAbel.add hgeo).div_const 2
  have hshift : Summable (fun m : ℕ => LSeries.term a (y : ℂ) (m + 1)) := by
    refine Summable.of_norm_bounded hmaj (fun m => ?_)
    rw [LSeries.norm_term_eq]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, ofReal_re]
    have hx : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    set x : ℝ := ((m + 1 : ℕ) : ℝ) with hxdef
    set A : ℝ := ‖a (m + 1)‖ * x ^ (-σ₁ - δ / 2) with hA
    set Bq : ℝ := x ^ (σ₁ + δ / 2 - y) with hBq
    have hAB : ‖a (m + 1)‖ / x ^ y = A * Bq := by
      rw [hA, hBq, mul_assoc, ← Real.rpow_add hx, div_eq_mul_inv, ← Real.rpow_neg hx.le]; ring_nf
    have hA2 : A ^ 2 = c m * ((m : ℝ) + 1) ^ (-δ) := by
      rw [hA, hc]; simp only; rw [← hcast, ← hxdef]
      have e1 : (x ^ (-σ₁ - δ / 2)) ^ 2 = x ^ (-2 * σ₁ - δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; push_cast; ring_nf
      have e2 : (x ^ (-σ₁)) ^ 2 * x ^ (-δ) = x ^ (-2 * σ₁ - δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]; push_cast; ring_nf
      rw [mul_pow, e1, mul_assoc, e2]
    have hB2 : Bq ^ 2 = ((m : ℝ) + 1) ^ (-1 - δ) := by
      rw [hBq, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← hcast]
      congr 1; rw [hδ]; push_cast; ring
    rw [hAB, ← hA2, ← hB2]
    nlinarith [sq_nonneg (A - Bq)]
  exact (summable_nat_add_iff 1).mp hshift

/-- `lam` is a **producer on the half-plane `Re s > σ₀`** for the archimedean function `Ψ`: its
Dirichlet series continues holomorphically to `Re s > σ₀` apart from a simple pole of residue `1`
at `s = 1`, and `Ψ − D` has nonnegative real part there (a Carathéodory function). -/
def IsHalfPlaneProducer (Ψ : ℂ → ℂ) (σ₀ : ℝ) (lam : ℕ → ℂ) : Prop :=
  ∃ D : ℂ → ℂ, DifferentiableOn ℂ D ({s | σ₀ < s.re} \ {1}) ∧
    (∀ s : ℂ, 2 < s.re → D s = LSeries lam s) ∧
    Tendsto (fun s => (s - 1) * D s) (𝓝[≠] 1) (𝓝 1) ∧
    ∀ s : ℂ, σ₀ < s.re → s ≠ 1 → 0 ≤ (Ψ s - D s).re

/-- The `L`-series on `Re s = 3` is bounded by `∑ C m^{θ−3}`. -/
theorem norm_LSeries_three_le (a : ℕ → ℂ) {C θ : ℝ} (hθ : θ < 1)
    (ha : ∀ m, ‖a m‖ ≤ C * (m : ℝ) ^ θ) {s : ℂ} (hs : s.re = 3) :
    ‖LSeries a s‖ ≤ ∑' m : ℕ, C * (m : ℝ) ^ (θ - 3) := by
  have hsum : Summable (fun m : ℕ => C * (m : ℝ) ^ (θ - 3)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left C
  have hle : ∀ m, ‖LSeries.term a s m‖ ≤ C * (m : ℝ) ^ (θ - 3) := by
    intro m
    rw [LSeries.norm_term_eq, hs]
    split_ifs with hm
    · subst hm
      have hθ3 : θ - 3 ≠ 0 := by linarith
      simp [Real.zero_rpow hθ3]
    · have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      rw [div_le_iff₀ (by positivity)]
      calc ‖a m‖ ≤ C * (m : ℝ) ^ θ := ha m
        _ = C * (m : ℝ) ^ (θ - 3) * (m : ℝ) ^ (3 : ℝ) := by
            rw [mul_assoc, ← Real.rpow_add hm']; ring_nf
  calc ‖LSeries a s‖ = ‖∑' m, LSeries.term a s m‖ := rfl
    _ ≤ ∑' m, ‖LSeries.term a s m‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum)
    _ ≤ ∑' m : ℕ, C * (m : ℝ) ^ (θ - 3) :=
        Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum) hsum

/-- **No pole series with logarithmic growth left of the critical line.**  Let `‖lam n‖ ≤ C n^θ`
with `θ < 1`, and let `D` be holomorphic on `Re s > σ₀` off `s = 1`, equal to `L(lam, s)` on
`Re s > 2`, with `(s − 1) D(s) → 1` at `s = 1`.  If `‖D(s)‖ ≤ K log Im s` on `σ₁ ≤ Re s ≤ 3`,
`Im s ≥ T₀` for some `σ₁ ∈ (σ₀, 1/2)`, this is impossible: Carlson's theorem makes `L(lam, ·)`
absolutely convergent, hence holomorphic, at `s = 1`. -/
theorem false_of_logGrowth_pole_of_lt_half (lam : ℕ → ℂ) {C θ : ℝ} (hC : 0 ≤ C) (hθ : θ < 1)
    (hlam : ∀ n, ‖lam n‖ ≤ C * (n : ℝ) ^ θ) (D : ℂ → ℂ) {σ₀ σ₁ K T₀ : ℝ}
    (hD : DifferentiableOn ℂ D ({s | σ₀ < s.re} \ {1}))
    (hDeq : ∀ s : ℂ, 2 < s.re → D s = LSeries lam s)
    (hres : Tendsto (fun s => (s - 1) * D s) (𝓝[≠] 1) (𝓝 1))
    (hσ₁pos : 0 < σ₁) (hσ₀₁ : σ₀ < σ₁) (hσ₁h : σ₁ < 1 / 2) (hKpos : 0 ≤ K) (hT₀1 : 1 ≤ T₀)
    (hDbd : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 3 → T₀ ≤ s.im → ‖D s‖ ≤ K * Real.log s.im) : False := by
  have hmem : ∀ w : ℂ, σ₀ < w.re → 0 < w.im → w ∈ ({s : ℂ | σ₀ < s.re} \ {1}) := by
    intro w hw him
    refine ⟨hw, fun h => ?_⟩
    rw [Set.mem_singleton_iff] at h; rw [h] at him; simp at him
  -- Carlson: absolute convergence beyond `σ₁ + 1/2`
  have hstrip : DifferentiableOn ℂ D {s | σ₁ ≤ s.re ∧ s.re ≤ 3 ∧ T₀ ≤ s.im} :=
    hD.mono (fun w hw => hmem w (by linarith [hw.1]) (by linarith [hw.2.2]))
  have hsumm : ∀ y : ℝ, σ₁ + 1 / 2 < y → LSeriesSummable lam y := fun y hy =>
    LSeriesSummable_of_logGrowth lam hC hθ hlam D hσ₁pos (by linarith) hKpos
      hT₀1 hstrip (fun y hy => hDeq _ (by simp; norm_num)) hDbd hy
  have habs : LSeries.abscissaOfAbsConv lam ≤ ((σ₁ + 1 / 2 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable hsumm
  have hLdiff : DifferentiableOn ℂ (LSeries lam) {s : ℂ | σ₁ + 1 / 2 < s.re} :=
    (LSeries_differentiableOn lam).mono (fun s hs => lt_of_le_of_lt habs (by exact_mod_cast hs))
  -- identity theorem on the upper quarter-plane
  set V : Set ℂ := {s : ℂ | σ₁ + 1 / 2 < s.re ∧ 0 < s.im} with hV
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_im)
  have hVconv : Convex ℝ V := by
    refine (convex_halfSpace_re_gt _).inter ?_
    exact convex_halfSpace_im_gt 0
  have hDV : DifferentiableOn ℂ D V :=
    hD.mono (fun w hw => hmem w (by linarith [hw.1]) hw.2)
  have hLV : DifferentiableOn ℂ (LSeries lam) V := hLdiff.mono (fun w hw => hw.1)
  have hz₀ : (3 + I : ℂ) ∈ V := by
    refine ⟨?_, ?_⟩
    · simp; linarith
    · simp
  have hev : D =ᶠ[𝓝 (3 + I)] LSeries lam := by
    have hopen : IsOpen {s : ℂ | 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (by simp; norm_num)) (fun s hs => hDeq s hs)
  have hEq : Set.EqOn D (LSeries lam) V :=
    (hDV.analyticOnNhd hVopen).eqOn_of_preconnected_of_eventuallyEq (hLV.analyticOnNhd hVopen)
      hVconv.isPreconnected hz₀ hev
  -- approach `1` vertically
  set g : ℝ → ℂ := fun ε => 1 + (ε : ℂ) * I with hg
  have hg0 : Tendsto g (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto g (𝓝 0) (𝓝 (g 0)) := (by fun_prop : Continuous g).tendsto 0
    simpa [hg] using this.mono_left nhdsWithin_le_nhds
  have hgne : Tendsto g (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within g hg0 ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    intro h
    have := congrArg Complex.im h
    simp [hg] at this
    exact (ne_of_gt hε) this
  have hlim1 : Tendsto (fun ε => (g ε - 1) * D (g ε)) (𝓝[>] 0) (𝓝 1) := hres.comp hgne
  have hone_mem : (1 : ℂ) ∈ {s : ℂ | σ₁ + 1 / 2 < s.re} := by
    show σ₁ + 1 / 2 < (1 : ℂ).re; simp; linarith
  have hLcont : ContinuousAt (LSeries lam) 1 :=
    (hLdiff.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hone_mem)).continuousAt
  have hlim0 : Tendsto (fun ε => (g ε - 1) * LSeries lam (g ε)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε => g ε - 1) (𝓝[>] 0) (𝓝 0) := by
      simpa using hg0.sub_const 1
    have h2 : Tendsto (fun ε => LSeries lam (g ε)) (𝓝[>] 0) (𝓝 (LSeries lam 1)) :=
      hLcont.tendsto.comp hg0
    simpa using h1.mul h2
  have hlim0' : Tendsto (fun ε => (g ε - 1) * D (g ε)) (𝓝[>] 0) (𝓝 0) := by
    refine hlim0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hgV : g ε ∈ V := by
      refine ⟨?_, ?_⟩ <;> simp [hg]
      · linarith
      · exact hε
    rw [hEq hgV]
  have := tendsto_nhds_unique hlim1 hlim0'
  exact one_ne_zero this


/-- **No producer lives on a half-plane beyond the critical line.**  Let `Ψ` be holomorphic on
`Re s > σ₀` (off `s = 1`) with `‖Ψ(s)‖ ≤ K₀ log Im s` on `σ₀ < Re s ≤ 3`, `Im s ≥ T₁`, and let
`‖lam n‖ ≤ C n^θ` with `θ < 1`.  If `0 < σ₀ < 1/2`, then `lam` is not a producer on `Re s > σ₀`.

Harnack's inequality on discs centred on `Re s = 3` turns the Carathéodory property into
`‖D(s)‖ ≪ log Im s` on `σ₁ ≤ Re s ≤ 3` for any `σ₁ ∈ (σ₀, 1/2)`.  Carlson's theorem then makes the
Dirichlet series absolutely convergent on `Re s > σ₁ + 1/2`, a half-plane containing `s = 1`, so it
cannot carry the pole. -/
theorem not_isHalfPlaneProducer_of_lt_half (Ψ : ℂ → ℂ) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ₀' : σ₀ < 1 / 2)
    (hΨ : DifferentiableOn ℂ Ψ ({s | σ₀ < s.re} \ {1})) {K₀ T₁ : ℝ} (hK₀ : 0 ≤ K₀)
    (hΨbd : ∀ s : ℂ, σ₀ < s.re → s.re ≤ 3 → T₁ ≤ s.im → ‖Ψ s‖ ≤ K₀ * Real.log s.im)
    (lam : ℕ → ℂ) {C θ : ℝ} (hC : 0 ≤ C) (hθ : θ < 1) (hlam : ∀ n, ‖lam n‖ ≤ C * (n : ℝ) ^ θ) :
    ¬ IsHalfPlaneProducer Ψ σ₀ lam := by
  rintro ⟨D, hD, hDeq, hres, hcar⟩
  set σ₁ : ℝ := (σ₀ + 1 / 2) / 2 with hσ₁
  have hσ₀₁ : σ₀ < σ₁ := by rw [hσ₁]; linarith
  have hσ₁h : σ₁ < 1 / 2 := by rw [hσ₁]; linarith
  have hgap : 0 < σ₁ - σ₀ := by linarith
  have h6pos : 0 ≤ 6 / (σ₁ - σ₀) := by positivity
  set T₀ : ℝ := max T₁ 4 with hT₀
  have hT₀4 : 4 ≤ T₀ := le_max_right _ _
  set A₃ : ℝ := ∑' m : ℕ, C * (m : ℝ) ^ (θ - 3) with hA₃
  have hA₃0 : 0 ≤ A₃ := tsum_nonneg (fun m => by positivity)
  set K : ℝ := K₀ + (1 + 6 / (σ₁ - σ₀)) * (K₀ + A₃) with hK
  have hKpos : 0 ≤ K := by positivity
  have hlog1 : ∀ t : ℝ, 4 ≤ t → 1 ≤ Real.log t := by
    intro t ht
    have he : Real.exp 1 ≤ t := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log t := Real.log_le_log (Real.exp_pos 1) he
  -- the region where `D` and `Ψ` are holomorphic
  have hmem : ∀ w : ℂ, σ₀ < w.re → 0 < w.im → w ∈ ({s : ℂ | σ₀ < s.re} \ {1}) := by
    intro w hw him
    refine ⟨hw, fun h => ?_⟩
    rw [Set.mem_singleton_iff] at h; rw [h] at him; simp at him
  -- logarithmic growth of `D` on the strip
  have hDbd : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 3 → T₀ ≤ s.im → ‖D s‖ ≤ K * Real.log s.im := by
    intro s hs1 hs3 hsT
    set t := s.im with ht
    have ht4 : 4 ≤ t := le_trans hT₀4 hsT
    have hlogt : 1 ≤ Real.log t := hlog1 t ht4
    set c : ℂ := (3 : ℂ) + (t : ℂ) * I with hc
    set R : ℝ := 3 - σ₀ with hR
    set H : ℂ → ℂ := fun w => Ψ w - D w with hH
    have hball : ∀ w ∈ Metric.ball c R, w ∈ ({s : ℂ | σ₀ < s.re} \ {1}) := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have hwre : (w - c).re = w.re - 3 := by rw [hc]; simp
      have hwim : (w - c).im = w.im - t := by rw [hc]; simp
      have hre : |w.re - 3| < R := by
        rw [← hwre]; exact lt_of_le_of_lt (Complex.abs_re_le_norm _) hw
      have him : |w.im - t| < R := by
        rw [← hwim]; exact lt_of_le_of_lt (Complex.abs_im_le_norm _) hw
      refine hmem w ?_ ?_
      · have := (abs_lt.mp hre).1; rw [hR] at this; linarith
      · have := (abs_lt.mp him).1; rw [hR] at this; linarith
    have hHd : DifferentiableOn ℂ H (Metric.ball c R) :=
      (hΨ.sub hD).mono (fun w hw => hball w hw)
    have hHre : ∀ w ∈ Metric.ball c R, 0 ≤ (H w).re := by
      intro w hw
      have hw' := hball w hw
      exact hcar w hw'.1 hw'.2
    have hsc : ‖s - c‖ = 3 - s.re := by
      have : s - c = ((s.re - 3 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hc, ht]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
    have hsball : s ∈ Metric.ball c R := by
      rw [Metric.mem_ball, dist_eq_norm, hsc, hR]; linarith
    have hharn := GaloisForLFunctions.HTGeometry.norm_sub_le_of_re_nonneg_on_ball hHd hHre hsball
    have hcre : c.re = 3 := by simp [hc]
    have hcim : c.im = t := by simp [hc]
    have hΨc : ‖Ψ c‖ ≤ K₀ * Real.log t := by
      have := hΨbd c (by rw [hcre]; linarith) (by rw [hcre]) (by rw [hcim]; linarith [le_max_left T₁ 4])
      rwa [hcim] at this
    have hDc : ‖D c‖ ≤ A₃ := by
      rw [hDeq c (by rw [hcre]; norm_num)]
      exact norm_LSeries_three_le lam hθ hlam hcre
    have hHc : ‖H c‖ ≤ K₀ * Real.log t + A₃ := by
      rw [hH]; simp only; exact (norm_sub_le _ _).trans (by linarith)
    have hfac : 2 * ‖s - c‖ / (R - ‖s - c‖) ≤ 6 / (σ₁ - σ₀) := by
      rw [hsc, hR, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hHs : ‖H s‖ ≤ (1 + 6 / (σ₁ - σ₀)) * (K₀ * Real.log t + A₃) := by
      have h1 : ‖H s‖ ≤ ‖H c‖ + 2 * ‖s - c‖ / (R - ‖s - c‖) * (H c).re := by
        have := norm_sub_norm_le (H s) (H c); linarith
      have h2 : (H c).re ≤ ‖H c‖ := Complex.re_le_norm _
      have h3 : 0 ≤ (H c).re := hHre c (Metric.mem_ball_self (by rw [hR]; linarith))
      have h4 : 0 ≤ 2 * ‖s - c‖ / (R - ‖s - c‖) := by
        rw [hsc, hR]; apply div_nonneg <;> linarith
      have h5 : 2 * ‖s - c‖ / (R - ‖s - c‖) * (H c).re ≤ 6 / (σ₁ - σ₀) * ‖H c‖ :=
        mul_le_mul hfac h2 h3 h6pos
      calc ‖H s‖ ≤ ‖H c‖ + 6 / (σ₁ - σ₀) * ‖H c‖ := by linarith
        _ = (1 + 6 / (σ₁ - σ₀)) * ‖H c‖ := by ring
        _ ≤ (1 + 6 / (σ₁ - σ₀)) * (K₀ * Real.log t + A₃) := by gcongr
    have hΨs : ‖Ψ s‖ ≤ K₀ * Real.log t :=
      hΨbd s (by linarith) hs3 (le_trans (le_max_left _ _) hsT)
    have hDs : D s = Ψ s - H s := by rw [hH]; ring
    rw [hDs]
    have hA : A₃ ≤ A₃ * Real.log t := le_mul_of_one_le_right hA₃0 hlogt
    have hF6 : 0 ≤ 1 + 6 / (σ₁ - σ₀) := by linarith
    calc ‖Ψ s - H s‖ ≤ ‖Ψ s‖ + ‖H s‖ := norm_sub_le _ _
      _ ≤ K₀ * Real.log t + (1 + 6 / (σ₁ - σ₀)) * (K₀ * Real.log t + A₃) := by linarith
      _ ≤ K₀ * Real.log t + (1 + 6 / (σ₁ - σ₀)) * (K₀ * Real.log t + A₃ * Real.log t) := by gcongr
      _ = K * Real.log t := by rw [hK]; ring
  exact false_of_logGrowth_pole_of_lt_half lam hC hθ hlam D hD hDeq hres (by linarith)
    hσ₀₁ hσ₁h hKpos (by linarith) hDbd

end RHTower.CarlsonFloor
