import GaloisForLFunctions.BiScaleUncertainty.PrimeTowerDeletionLocalEulerFactor
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# The prime side on long windows is governed by the pole

On tests supported in an interval of length `L` the prime side `Σ_n Λ(n) L_n` of the Weil
functional sees the nodes `log n < L`, with atoms `w_n = Λ(n)/√n`. Its ceiling over nonnegative
combinations is the top of the weighted operator `f ↦ Σ_n w_n (f(· + log n) + f(· − log n))` on the
window. The atoms are, on average, the polar density: `Σ_n w_n δ_{log n} ≈ e^{y/2} dy` is the
prime number theorem, and the kernel `e^{|s−t|/2}` is semi-separable with top eigenfunction
`φ(t) = e^{−t/2} + e^{−(L−t)/2}`, a polar `cosh` centred at the window's midpoint.

**Theorem** (`tendsto_windowCeiling_div_exp`). The window ceiling
`c(L) = sup (A − W)/‖c‖²` over nonnegative combinations of tests supported in intervals of length
`L` satisfies `c(L)/e^{L/2} → 1`: on windows of length `log X` the prime side reaches exactly
`√X (1 + o(1))`, the top of the polar kernel.

* Upper bound (`abs_nodeArchEnergy_sub_weilEnergy_le_polar`): if `ψ(x) ≤ Kx + B` for `x ≥ 0`, then
  `|A − W| ≤ (K e^{L/2} + B + (1 + L)²) ‖c‖²`; Chebyshev gives `K = log 4 + 4`, `B = 0` for all `L`
  (`abs_nodeArchEnergy_sub_weilEnergy_le_chebyshev`), the prime number theorem `K = 1 + ε`.
* Lower bound (`eventually_exists_windowDeviation_ge`): the polar test
  `(e^{−t/2} + e^{−(L−t)/2}) χ(t)` has mass `≤ 2 + 2L e^{−L/2}` and its two ends correlate,
  `k(y) ≥ e^{−(L−y)/2}(L − y − 2δ)`, so its prime side is at least `2e^{−L/2} Σ_{n≤Y} Λ(n) log(Y/n)`,
  `Y = e^{L−2δ}`; the Riesz mean is `≥ (1 − η)Y` by a Riemann sum of the prime number theorem
  (`exists_riesz_ge`).

**Mechanism.** The weighted Schur bound of `PrimeWindowCeilings` with the polar weight `φ`: the
neighbour sum at `t = a + τ` is exactly
`e^{−τ/2} ψ(e^τ) + e^{−(L−τ)/2} ψ(e^{L−τ}) + e^{−(L−τ)/2} Σ_{n<e^τ} Λ(n)/n + e^{−τ/2} Σ_{n<e^{L−τ}} Λ(n)/n`,
and `e^{−τ/2} e^τ = e^{L/2} e^{−(L−τ)/2}` turns the Chebyshev terms into `K e^{L/2} φ(t)`: the
prime mass at distance `log n` pays the polar weight at the far end of the window. The deviation of
`c(L)` from `e^{L/2}` is carried by the Chebyshev error `ψ(x) − x` near `x = e^L`.

An argument in which an archimedean bound pays a uniform prime ceiling must therefore supply a
margin of order `e^{L/2}` on windows of length `L`.
-/

open MeasureTheory Set Complex Finsupp Filter Topology
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. The polar weight of a window -/

/-- The clamp of `t` to `[a, a + L]`. -/
def clampWindow (a L t : ℝ) : ℝ := max a (min t (a + L))

/-- The polar weight `φ(t) = e^{−(t−a)/2} + e^{−(a+L−t)/2}` of the window `[a, a + L]`, frozen
outside it. -/
def polarWeight (a L t : ℝ) : ℝ :=
  Real.exp (-(clampWindow a L t - a) / 2) + Real.exp (-(a + L - clampWindow a L t) / 2)

theorem clampWindow_of_mem {a L t : ℝ} (ht : t ∈ Icc a (a + L)) : clampWindow a L t = t := by
  rw [clampWindow, min_eq_left ht.2, max_eq_right ht.1]

theorem clampWindow_mem {a L : ℝ} (hL : 0 ≤ L) (t : ℝ) : clampWindow a L t ∈ Icc a (a + L) :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem continuous_polarWeight (a L : ℝ) : Continuous (polarWeight a L) := by
  have hc : Continuous (clampWindow a L) :=
    continuous_const.max (continuous_id.min continuous_const)
  exact (Real.continuous_exp.comp ((hc.sub continuous_const).neg.div_const 2)).add
    (Real.continuous_exp.comp ((continuous_const.sub hc).neg.div_const 2))

theorem polarWeight_pos_lower {a L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    Real.exp (-L / 2) ≤ polarWeight a L t := by
  have hm := clampWindow_mem (a := a) hL t
  have h1 : Real.exp (-L / 2) ≤ Real.exp (-(clampWindow a L t - a) / 2) :=
    Real.exp_le_exp.mpr (by linarith [hm.2])
  have h2 := Real.exp_pos (-(a + L - clampWindow a L t) / 2)
  rw [polarWeight]; linarith

theorem polarWeight_le {a L : ℝ} (hL : 0 ≤ L) (t : ℝ) : polarWeight a L t ≤ 2 := by
  have hm := clampWindow_mem (a := a) hL t
  have h1 : Real.exp (-(clampWindow a L t - a) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [hm.1])
  have h2 : Real.exp (-(a + L - clampWindow a L t) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [hm.2])
  rw [polarWeight]; linarith

/-! ### 2. The Schur bound with finitely many visible nodes -/

/-- On a window of length `L ≤ log N` the prime side is the finite sum over `2 ≤ n < N`. -/
theorem primeSide_eq_sum_of_window {f : WeilTestFn} {a L : ℝ}
    (hsupp : ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) {N : ℕ} (hN : L ≤ Real.log N) :
    linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector f) =
      ∑ n ∈ Finset.Ico 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) * logValue f.1 n := by
  classical
  have hsub : (logVector f).support ⊆ (Finset.Ico 2 N).subtype (fun n => 2 ≤ n) := by
    intro j hj
    rw [Finset.mem_subtype, Finset.mem_Ico]
    refine ⟨j.2, ?_⟩
    by_contra hjN
    push Not at hjN
    apply Finsupp.mem_support_iff.mp hj
    rw [logVector_apply]
    have hj1 : (1 : ℝ) ≤ (j : ℕ) := by exact_mod_cast (by have := j.2; omega : 1 ≤ (j : ℕ))
    have hlog : L ≤ Real.log (j : ℕ) := by
      rcases Nat.eq_zero_or_pos N with h | h
      · rw [h, Nat.cast_zero, Real.log_zero] at hN
        exact hN.trans (Real.log_nonneg hj1)
      · exact hN.trans (Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hjN))
    exact logValue_eq_zero_of_window hsupp (by have := j.2; omega) hlog
  rw [linearCombination_apply, Finsupp.sum_of_support_subset _ hsub
    (fun (i : LogIndex) (v : ℝ) => v • (ArithmeticFunction.vonMangoldt (i : ℕ) : ℝ))
    (fun _ _ => zero_smul _ _)]
  simp_rw [logVector_apply, smul_eq_mul]
  rw [Finset.sum_subtype_eq_sum_filter
      (fun n : ℕ => logValue f.1 n * (ArithmeticFunction.vonMangoldt n : ℝ)),
    Finset.filter_true_of_mem fun n hn => (Finset.mem_Ico.mp hn).1]
  exact Finset.sum_congr rfl fun n _ => mul_comm _ _

/-- **The Schur bound on a window.** If the weight `φ` satisfies
`Σ_{2≤n<N} w_n (φ(t − log n) + φ(t + log n)) ≤ C φ(t)` on the window (neighbours outside the
window counted as `0`), then `|Σ_n Λ(n) L_n(f)| ≤ C ‖f‖²`. -/
theorem abs_primeSide_le_of_window_schur {f : WeilTestFn} {a L : ℝ}
    (hsupp : ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) {N : ℕ} (hN : L ≤ Real.log N)
    {φ : ℝ → ℝ} (hφm : Measurable φ) {m M : ℝ} (hm : 0 < m) (hlo : ∀ t, m ≤ φ t)
    (hhi : ∀ t, φ t ≤ M) {C : ℝ}
    (hS : ∀ t ∈ Ioo a (a + L), ∑ n ∈ Finset.Ico 2 N,
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        ((Ioo a (a + L)).indicator φ (t - Real.log n) +
          (Ioo a (a + L)).indicator φ (t + Real.log n)) ≤ C * φ t) :
    |linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector f)| ≤ C * ∫ u, ‖f.1 u‖ ^ 2 := by
  rw [primeSide_eq_sum_of_window hsupp hN]
  have hfc := f.2.1.continuous
  have hfs := f.2.2
  have hφpos : ∀ t, 0 < φ t := fun t => hm.trans_le (hlo t)
  set I := Ioo a (a + L)
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ → ℝ, F = fun s t => ‖f.1 t‖ ^ 2 *
      (I.indicator φ (t - s) / φ t + I.indicator φ (t + s) / φ t) := ⟨_, rfl⟩
  have hSch : ∀ s, 2 * |(EF.weilTest f.1 f.1 s).re| ≤ ∫ t, F s t := fun s => by
    rw [hF]; exact two_mul_abs_re_weilTest_le hfc hfs hsupp hφm hm hlo hhi s
  have hI : ∀ s, Integrable (F s) := fun s => by
    rw [hF]; exact integrable_schurIntegrand hfc hfs measurableSet_Ioo hφm hm hlo hhi s
  have hneg : ∀ s, F (-s) = F s := fun s => by
    rw [hF]; funext t; simp only [sub_neg_eq_add, ← sub_eq_add_neg]; ring
  have hpair : ∀ s, |(EF.weilTest f.1 f.1 s).re| + |(EF.weilTest f.1 f.1 (-s)).re| ≤
      ∫ t, F s t := by
    intro s
    have h1 := hSch s
    have h2 := hSch (-s)
    rw [hneg] at h2
    linarith
  have hw : ∀ n : ℕ, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n := fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hterm : ∀ n ∈ Finset.Ico 2 N,
      |(ArithmeticFunction.vonMangoldt n : ℝ) * logValue f.1 n| ≤
        (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * ∫ t, F (Real.log n) t := by
    intro n hn
    have hn2 := (Finset.mem_Ico.mp hn).1
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
    have e : (ArithmeticFunction.vonMangoldt n : ℝ) * logValue f.1 n =
        (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
          ((EF.weilTest f.1 f.1 (Real.log n)).re + (EF.weilTest f.1 f.1 (-Real.log n)).re) := by
      rw [logValue, Complex.add_re]; ring
    rw [e, abs_mul, abs_of_nonneg (hw n)]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (hpair _)) (hw n)
  have hcs : HasCompactSupport (fun t => ‖f.1 t‖ ^ 2) :=
    hfs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hnorm : Integrable (fun t => ‖f.1 t‖ ^ 2) :=
    (hfc.norm.pow 2).integrable_of_hasCompactSupport hcs
  calc |∑ n ∈ Finset.Ico 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) * logValue f.1 n|
      ≤ ∑ n ∈ Finset.Ico 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
          ∫ t, F (Real.log n) t :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = ∫ t, ∑ n ∈ Finset.Ico 2 N,
          (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * F (Real.log n) t := by
        rw [integral_finsetSum _ fun n _ => (hI _).const_mul _]
        exact Finset.sum_congr rfl fun n _ => (integral_const_mul _ _).symm
    _ ≤ ∫ t, C * ‖f.1 t‖ ^ 2 := by
        refine integral_mono (integrable_finsetSum _ fun n _ => (hI _).const_mul _)
          (hnorm.const_mul _) fun t => ?_
        by_cases h0 : f.1 t = 0
        · simp [hF, h0]
        have hS' := hS t (hsupp t h0)
        have e : ∑ n ∈ Finset.Ico 2 N,
            (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * F (Real.log n) t =
              ‖f.1 t‖ ^ 2 / φ t * ∑ n ∈ Finset.Ico 2 N,
                (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
                  (I.indicator φ (t - Real.log n) + I.indicator φ (t + Real.log n)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hF]; field_simp
        rw [e, div_mul_eq_mul_div, div_le_iff₀ (hφpos t)]
        calc ‖f.1 t‖ ^ 2 * (∑ n ∈ Finset.Ico 2 N,
              (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
                (I.indicator φ (t - Real.log n) + I.indicator φ (t + Real.log n)))
            ≤ ‖f.1 t‖ ^ 2 * (C * φ t) := mul_le_mul_of_nonneg_left hS' (sq_nonneg _)
          _ = C * ‖f.1 t‖ ^ 2 * φ t := by ring
    _ = C * ∫ u, ‖f.1 u‖ ^ 2 := integral_const_mul _ _

/-! ### 3. The polar weight is a supersolution -/

theorem exp_add_half_log {n : ℕ} (hn : 0 < n) (x : ℝ) :
    Real.exp (x + Real.log n / 2) = Real.exp x * Real.sqrt n := by
  have hs : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [← Real.sqrt_sq (Real.exp_pos _).le, sq, ← Real.exp_add, add_halves,
      Real.exp_log (by exact_mod_cast hn)]
  rw [Real.exp_add, hs]

theorem exp_sub_half_log {n : ℕ} (hn : 0 < n) (x : ℝ) :
    Real.exp (x - Real.log n / 2) = Real.exp x / Real.sqrt n := by
  have h := exp_add_half_log hn (x - Real.log n / 2)
  rw [sub_add_cancel] at h
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  rw [h, mul_div_assoc, div_self hs.ne', mul_one]

/-- The prime mass below `x` is at most `ψ(x)`. -/
theorem sum_vonMangoldt_le_psi {S : Finset ℕ} {x : ℝ} (hS : ∀ n ∈ S, (n : ℝ) ≤ x) :
    ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Chebyshev.psi x := by
  rw [Chebyshev.psi_eq_sum_Icc]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
    fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
  rw [Finset.mem_Icc]
  exact ⟨Nat.zero_le _, Nat.le_floor (hS n hn)⟩

/-- `Σ Λ(n)/n ≤ (1 + τ)²` over integers `1 ≤ n < e^τ`. -/
theorem sum_vonMangoldt_div_le_of_lt_exp {S : Finset ℕ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ (n : ℝ) < Real.exp τ) :
    ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) / n ≤ (1 + τ) ^ 2 := by
  have hsub : S ⊆ Finset.Icc 1 ⌊Real.exp τ⌋₊ := fun n hn => by
    rw [Finset.mem_Icc]; exact ⟨(hS n hn).1, Nat.le_floor (hS n hn).2.le⟩
  have hterm : ∀ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) / n ≤ τ * (1 / (n : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (hS n hn).1
    have hlog : Real.log n ≤ τ := by
      rw [← Real.log_exp τ]; exact Real.log_le_log hn0 (hS n hn).2.le
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (ArithmeticFunction.vonMangoldt_le_log.trans hlog) hn0.le
  have hharm : ∑ n ∈ Finset.Icc 1 ⌊Real.exp τ⌋₊, 1 / (n : ℝ) ≤ 1 + τ := by
    have h := harmonic_le_one_add_log ⌊Real.exp τ⌋₊
    rw [_root_.harmonic_eq_sum_Icc] at h
    push_cast at h
    simp only [one_div]
    refine h.trans ?_
    have : Real.log ⌊Real.exp τ⌋₊ ≤ τ := by
      rcases Nat.eq_zero_or_pos ⌊Real.exp τ⌋₊ with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]; exact hτ
      · calc Real.log ⌊Real.exp τ⌋₊ ≤ Real.log (Real.exp τ) :=
            Real.log_le_log (by exact_mod_cast h0) (Nat.floor_le (Real.exp_pos τ).le)
          _ = τ := Real.log_exp τ
    linarith
  calc ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) / n
      ≤ ∑ n ∈ S, τ * (1 / (n : ℝ)) := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊Real.exp τ⌋₊, τ * (1 / (n : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ = τ * ∑ n ∈ Finset.Icc 1 ⌊Real.exp τ⌋₊, 1 / (n : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ τ * (1 + τ) := mul_le_mul_of_nonneg_left hharm hτ
    _ ≤ (1 + τ) ^ 2 := by nlinarith

/-- The neighbour of `t` at distance `log n` towards the left end, weighted by the atom. -/
theorem atom_mul_indicator_sub {a L t : ℝ} (ht : t ∈ Ioo a (a + L)) {n : ℕ}
    (hn : 2 ≤ n) :
    (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        (Ioo a (a + L)).indicator (polarWeight a L) (t - Real.log n) =
      if Real.log n < t - a then
        Real.exp (-(t - a) / 2) * ArithmeticFunction.vonMangoldt n +
          Real.exp (-(L - (t - a)) / 2) * (ArithmeticFunction.vonMangoldt n / n)
      else 0 := by
  have hn0 : 0 < n := by omega
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  split_ifs with h
  · have hmem : t - Real.log n ∈ Ioo a (a + L) := ⟨by linarith, by linarith [ht.2]⟩
    rw [Set.indicator_of_mem hmem, polarWeight, clampWindow_of_mem (Ioo_subset_Icc_self hmem)]
    rw [show -(t - Real.log n - a) / 2 = -(t - a) / 2 + Real.log n / 2 by ring,
      show -(a + L - (t - Real.log n)) / 2 = -(L - (t - a)) / 2 - Real.log n / 2 by ring,
      exp_add_half_log hn0, exp_sub_half_log hn0]
    field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  · rw [Set.indicator_of_notMem (fun hmem => h (by linarith [hmem.1])), mul_zero]

/-- The neighbour of `t` at distance `log n` towards the right end, weighted by the atom. -/
theorem atom_mul_indicator_add {a L t : ℝ} (ht : t ∈ Ioo a (a + L)) {n : ℕ}
    (hn : 2 ≤ n) :
    (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        (Ioo a (a + L)).indicator (polarWeight a L) (t + Real.log n) =
      if Real.log n < L - (t - a) then
        Real.exp (-(t - a) / 2) * (ArithmeticFunction.vonMangoldt n / n) +
          Real.exp (-(L - (t - a)) / 2) * ArithmeticFunction.vonMangoldt n
      else 0 := by
  have hn0 : 0 < n := by omega
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  split_ifs with h
  · have hmem : t + Real.log n ∈ Ioo a (a + L) := ⟨by linarith [ht.1], by linarith⟩
    rw [Set.indicator_of_mem hmem, polarWeight, clampWindow_of_mem (Ioo_subset_Icc_self hmem)]
    rw [show -(t + Real.log n - a) / 2 = -(t - a) / 2 - Real.log n / 2 by ring,
      show -(a + L - (t + Real.log n)) / 2 = -(L - (t - a)) / 2 + Real.log n / 2 by ring,
      exp_add_half_log hn0, exp_sub_half_log hn0]
    field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  · rw [Set.indicator_of_notMem (fun hmem => h (by linarith [hmem.2])), mul_zero]

/-- **The polar supersolution.** If `ψ(x) ≤ Kx + B` for `x ≥ 0`, then on the window
`Σ_n w_n (φ(t − log n) + φ(t + log n)) ≤ (K e^{L/2} + B + (1 + L)²) φ(t)`. -/
theorem polar_schur_le {a L t : ℝ} (ht : t ∈ Ioo a (a + L)) (N : ℕ) {K B : ℝ}
    (hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ K * x + B) :
    ∑ n ∈ Finset.Ico 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        ((Ioo a (a + L)).indicator (polarWeight a L) (t - Real.log n) +
          (Ioo a (a + L)).indicator (polarWeight a L) (t + Real.log n)) ≤
      (K * Real.exp (L / 2) + B + (1 + L) ^ 2) * polarWeight a L t := by
  classical
  set τ := t - a with hτdef
  have hτ0 : 0 < τ := by rw [hτdef]; linarith [ht.1]
  have hτL : τ < L := by rw [hτdef]; linarith [ht.2]
  set e₁ := Real.exp (-τ / 2)
  set e₂ := Real.exp (-(L - τ) / 2)
  have he₁ : 0 < e₁ := Real.exp_pos _
  have he₂ : 0 < e₂ := Real.exp_pos _
  have hφ : polarWeight a L t = e₁ + e₂ := by
    rw [polarWeight, clampWindow_of_mem (Ioo_subset_Icc_self ht)]
    simp only [e₁, e₂, hτdef]
    congr 2; ring
  set Λ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)
  set S := Finset.Ico 2 N
  have hsplit : ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
      ((Ioo a (a + L)).indicator (polarWeight a L) (t - Real.log n) +
        (Ioo a (a + L)).indicator (polarWeight a L) (t + Real.log n)) =
      (e₁ * ∑ n ∈ S.filter (fun n : ℕ => Real.log n < τ), Λ n +
        e₂ * ∑ n ∈ S.filter (fun n : ℕ => Real.log n < τ), Λ n / n) +
      (e₁ * ∑ n ∈ S.filter (fun n : ℕ => Real.log n < L - τ), Λ n / n +
        e₂ * ∑ n ∈ S.filter (fun n : ℕ => Real.log n < L - τ), Λ n) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 := (Finset.mem_Ico.mp hn).1
    rw [mul_add, atom_mul_indicator_sub ht hn2, atom_mul_indicator_add ht hn2]
  have hexp : ∀ {n : ℕ} {y : ℝ}, 2 ≤ n → Real.log n < y → (n : ℝ) < Real.exp y := by
    intro n y hn h
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hpos).symm
      _ < Real.exp y := Real.exp_lt_exp.mpr h
  have hP1 : ∑ n ∈ S.filter (fun n : ℕ => Real.log n < τ), Λ n ≤ K * Real.exp τ + B :=
    (sum_vonMangoldt_le_psi fun n hn => by
      rw [Finset.mem_filter] at hn
      exact (hexp (Finset.mem_Ico.mp hn.1).1 hn.2).le).trans (hψ _ (Real.exp_pos τ).le)
  have hP2 : ∑ n ∈ S.filter (fun n : ℕ => Real.log n < L - τ), Λ n ≤ K * Real.exp (L - τ) + B :=
    (sum_vonMangoldt_le_psi fun n hn => by
      rw [Finset.mem_filter] at hn
      exact (hexp (Finset.mem_Ico.mp hn.1).1 hn.2).le).trans (hψ _ (Real.exp_pos _).le)
  have hM1 : ∑ n ∈ S.filter (fun n : ℕ => Real.log n < τ), Λ n / n ≤ (1 + L) ^ 2 :=
    (sum_vonMangoldt_div_le_of_lt_exp hτ0.le fun n hn => by
      rw [Finset.mem_filter] at hn
      exact ⟨by have := (Finset.mem_Ico.mp hn.1).1; omega,
        hexp (Finset.mem_Ico.mp hn.1).1 hn.2⟩).trans
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hτL.le) (by linarith : (0 : ℝ) ≤ 2 + L + τ)])
  have hM2 : ∑ n ∈ S.filter (fun n : ℕ => Real.log n < L - τ), Λ n / n ≤ (1 + L) ^ 2 :=
    (sum_vonMangoldt_div_le_of_lt_exp (τ := L - τ) (by linarith) fun n hn => by
      rw [Finset.mem_filter] at hn
      exact ⟨by have := (Finset.mem_Ico.mp hn.1).1; omega,
        hexp (Finset.mem_Ico.mp hn.1).1 hn.2⟩).trans
      (by nlinarith [mul_pos hτ0 (by linarith : (0 : ℝ) < 2 + 2 * L - τ)])
  -- the Chebyshev terms pay the polar weight at the far end
  have hc1 : e₁ * Real.exp τ = Real.exp (L / 2) * e₂ := by
    simp only [e₁, e₂]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hc2 : e₂ * Real.exp (L - τ) = Real.exp (L / 2) * e₁ := by
    simp only [e₁, e₂]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hsplit, hφ]
  have h1 := mul_le_mul_of_nonneg_left hP1 he₁.le
  have h2 := mul_le_mul_of_nonneg_left hP2 he₂.le
  have h3 := mul_le_mul_of_nonneg_left hM1 he₂.le
  have h4 := mul_le_mul_of_nonneg_left hM2 he₁.le
  calc _ ≤ e₁ * (K * Real.exp τ + B) + e₂ * (1 + L) ^ 2 + (e₁ * (1 + L) ^ 2 +
        e₂ * (K * Real.exp (L - τ) + B)) := by linarith
    _ = (K * Real.exp (L / 2) + B + (1 + L) ^ 2) * (e₁ + e₂) := by
        linear_combination K * hc1 + K * hc2

/-! ### 4. The ceiling bound -/

/-- **The polar ceiling.** If `ψ(x) ≤ Kx + B` for `x ≥ 0`, then for every nonnegative combination
of tests supported in intervals of length `L ≥ 0`, `|A − W| ≤ (K e^{L/2} + B + (1 + L)²) ‖c‖²`. -/
theorem abs_nodeArchEnergy_sub_weilEnergy_le_polar {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    {L : ℝ} (hL : 0 ≤ L) (hsupp : ∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L))
    {K B : ℝ} (hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ K * x + B) :
    |nodeArchEnergy c - weilEnergy c| ≤ (K * Real.exp (L / 2) + B + (1 + L) ^ 2) * massOf c := by
  set C := K * Real.exp (L / 2) + B + (1 + L) ^ 2
  have hN : L ≤ Real.log ⌈Real.exp L⌉₊ :=
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ Real.log ⌈Real.exp L⌉₊ := Real.log_le_log (Real.exp_pos L) (Nat.le_ceil _)
  rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_eq,
    linearCombination_apply ℝ (v := logVector), map_finsuppSum]
  have hX : ∀ f ∈ c.support,
      |linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (c f • logVector f)| ≤ c f * (C * ∫ u, ‖f.1 u‖ ^ 2) := by
    intro f hf
    obtain ⟨a, ha⟩ := hsupp f hf
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (hc f)]
    refine mul_le_mul_of_nonneg_left (abs_primeSide_le_of_window_schur ha hN
      (continuous_polarWeight a L).measurable (Real.exp_pos (-L / 2))
      (polarWeight_pos_lower hL) (polarWeight_le hL) fun t ht => polar_schur_le ht _ hψ) (hc f)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [WeilOneSided.massOf, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun f hf => ?_
  have := hX f hf
  linarith

/-- **Chebyshev's polar ceiling**, valid for every window length: `|A − W| ≤
((log 4 + 4) e^{L/2} + (1 + L)²) ‖c‖²`. -/
theorem abs_nodeArchEnergy_sub_weilEnergy_le_chebyshev {c : WeilTestFn →₀ ℝ}
    (hc : ∀ f, 0 ≤ c f) {L : ℝ} (hL : 0 ≤ L)
    (hsupp : ∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) :
    |nodeArchEnergy c - weilEnergy c| ≤
      ((Real.log 4 + 4) * Real.exp (L / 2) + (1 + L) ^ 2) * massOf c := by
  have h := abs_nodeArchEnergy_sub_weilEnergy_le_polar hc hL hsupp (K := Real.log 4 + 4) (B := 0)
    fun x hx => by rw [add_zero]; exact Chebyshev.psi_le_const_mul_self hx
  rwa [add_zero] at h

/-! ### 5. The prime number theorem in the forms used -/

/-- `ψ(x) ≤ (1 + η)x + B` for all `x ≥ 0`. -/
theorem exists_psi_le_linear {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ (1 + η) * x + B := by
  obtain ⟨X₀, hX₀⟩ := (RHTower.tendsto_psi_div_self.eventually
    (Iio_mem_nhds (by linarith : (1 : ℝ) < 1 + η))).exists_forall_of_atTop
  refine ⟨Chebyshev.psi (max X₀ 1), fun x hx => ?_⟩
  have hB := Chebyshev.psi_nonneg (max X₀ 1)
  by_cases hxX : max X₀ 1 ≤ x
  · have h := hX₀ x (le_trans (le_max_left _ _) hxX)
    have hx0 : 0 < x := by linarith [le_max_right X₀ 1]
    rw [div_lt_iff₀ hx0] at h
    linarith
  · push Not at hxX
    have := Chebyshev.psi_mono hxX.le
    nlinarith

/-- `ψ(x) ≥ (1 − η)x` for all large `x`. -/
theorem exists_psi_ge_linear {η : ℝ} (hη : 0 < η) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → (1 - η) * x ≤ Chebyshev.psi x := by
  obtain ⟨X₀, hX₀⟩ := (RHTower.tendsto_psi_div_self.eventually
    (Ioi_mem_nhds (by linarith : 1 - η < (1 : ℝ)))).exists_forall_of_atTop
  refine ⟨max X₀ 1, by positivity, fun x hx => ?_⟩
  have h := hX₀ x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 < x := by linarith [le_max_right X₀ 1]
  rw [lt_div_iff₀ hx0] at h
  exact h.le

/-- `ψ(x)` counts the prime mass below `x` inside `[1, Y]`. -/
theorem psi_le_sum_ite {x Y : ℝ} (hxY : x ≤ Y) :
    Chebyshev.psi x ≤ ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
      if (n : ℝ) ≤ x then (ArithmeticFunction.vonMangoldt n : ℝ) else 0 := by
  classical
  rw [Chebyshev.psi_eq_sum_Icc, ← Finset.sum_filter,
    ← Finset.sum_filter_of_ne (p := fun n => 1 ≤ n) (s := Finset.Icc 0 ⌊x⌋₊)]
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
      fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    have hx1 : (1 : ℝ) ≤ x := Nat.floor_pos.mp (by omega)
    refine ⟨⟨hn.2, hn.1.2.trans (Nat.floor_le_floor hxY)⟩, ?_⟩
    exact (Nat.cast_le.mpr hn.1.2).trans (Nat.floor_le (by linarith))
  · intro n _ hn
    by_contra h
    push Not at h
    have : n = 0 := by omega
    subst this
    exact hn (by simp)

/-- **Riemann sum for the Riesz mean.** `δ Σ_{1≤j≤J} ψ(e^{−jδ}Y) ≤ Σ_{n≤Y} Λ(n) log(Y/n)`. -/
theorem riesz_ge_sum_psi {Y δ : ℝ} (hY : 1 ≤ Y) (hδ : 0 < δ) (J : ℕ) :
    δ * ∑ j ∈ Finset.Icc 1 J, Chebyshev.psi (Real.exp (-(j * δ)) * Y) ≤
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n) := by
  classical
  have hθ : ∀ j : ℕ, Real.exp (-(j * δ)) * Y ≤ Y := fun j => by
    have : Real.exp (-(j * δ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := Nat.cast_nonneg (α := ℝ) j; nlinarith)
    nlinarith
  calc δ * ∑ j ∈ Finset.Icc 1 J, Chebyshev.psi (Real.exp (-(j * δ)) * Y)
      ≤ δ * ∑ j ∈ Finset.Icc 1 J, ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
          (if (n : ℝ) ≤ Real.exp (-(j * δ)) * Y then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => psi_le_sum_ite (hθ j)) hδ.le
    _ = ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (δ * ((Finset.Icc 1 J).filter
            (fun j : ℕ => (n : ℝ) ≤ Real.exp (-(j * δ)) * Y)).card) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n) := by
        refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_
          ArithmeticFunction.vonMangoldt_nonneg
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hlog : 0 ≤ Real.log (Y / n) := Real.log_nonneg (by
          rw [le_div_iff₀ (by linarith)]
          have := (Nat.cast_le (α := ℝ)).mpr (Finset.mem_Icc.mp hn).2
          linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ Y)])
        have hsub : (Finset.Icc 1 J).filter (fun j : ℕ => (n : ℝ) ≤ Real.exp (-(j * δ)) * Y) ⊆
            Finset.Icc 1 ⌊Real.log (Y / n) / δ⌋₊ := by
          intro j hj
          rw [Finset.mem_filter, Finset.mem_Icc] at hj
          rw [Finset.mem_Icc]
          refine ⟨hj.1.1, Nat.le_floor ?_⟩
          rw [le_div_iff₀ hδ, Real.log_div (by linarith) (by linarith),
            le_sub_iff_add_le]
          have h1 := Real.log_le_log (by linarith) hj.2
          rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp] at h1
          linarith
        have hcard := Finset.card_le_card hsub
        rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
        have hc : (((Finset.Icc 1 J).filter
            (fun j : ℕ => (n : ℝ) ≤ Real.exp (-(j * δ)) * Y)).card : ℝ) ≤ Real.log (Y / n) / δ :=
          (Nat.cast_le.mpr hcard).trans (Nat.floor_le (div_nonneg hlog hδ.le))
        rw [le_div_iff₀ hδ] at hc
        linarith

/-- The telescoping `(1 − q) Σ_{1≤j≤J} q^j = q − q^{J+1}`. -/
theorem one_sub_mul_sum_Icc_pow (q : ℝ) (J : ℕ) :
    (1 - q) * ∑ j ∈ Finset.Icc 1 J, q ^ j = q - q ^ (J + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

/-- **The Riesz mean of the von Mangoldt function**: `Σ_{n≤Y} Λ(n) log(Y/n) ≥ (1 − η)Y` for all
large `Y`. -/
theorem exists_riesz_ge {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      (1 - η) * Y ≤ ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) *
        Real.log (Y / n) := by
  set δ := η / 4 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨X₀, hX₀, hpsi⟩ := exists_psi_ge_linear hδ
  set J : ℕ := ⌈16 / η ^ 2⌉₊
  set q := Real.exp (-δ)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : 1 - δ ≤ q := Real.one_sub_le_exp_neg δ
  have hqd : 1 - q ≤ δ := by linarith
  -- the tail of the Riemann sum is small
  have hqJ : q ^ J ≤ δ := by
    have hJ : 16 / η ^ 2 ≤ (J : ℝ) := Nat.le_ceil _
    have : q ^ J = Real.exp (-(J * δ)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [this]
    have h1 : 1 + J * δ ≤ Real.exp (J * δ) := by linarith [Real.add_one_le_exp (J * δ)]
    have hJδ : 4 / η ≤ J * δ := by
      rw [hδdef]
      have : 16 / η ^ 2 * (η / 4) = 4 / η := by field_simp; ring
      nlinarith
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hδ]
    calc δ⁻¹ = 4 / η := by rw [hδdef]; field_simp
      _ ≤ J * δ := hJδ
      _ ≤ Real.exp (J * δ) := by linarith
  refine ⟨max 1 (X₀ * Real.exp (J * δ)), le_max_left _ _, fun Y hY => ?_⟩
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYX : X₀ * Real.exp (J * δ) ≤ Y := (le_max_right _ _).trans hY
  have hstep : ∀ j ∈ Finset.Icc 1 J, (1 - δ) * (q ^ j * Y) ≤
      Chebyshev.psi (Real.exp (-(j * δ)) * Y) := by
    intro j hj
    have hqj : Real.exp (-(j * δ)) = q ^ j := by rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hqj]
    apply hpsi
    have hjJ : (j : ℝ) ≤ J := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    have : Real.exp (-(J * δ)) ≤ q ^ j := by
      rw [← hqj]; exact Real.exp_le_exp.mpr (by nlinarith)
    have hE : X₀ = X₀ * Real.exp (J * δ) * Real.exp (-(J * δ)) := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rw [hE]
    calc X₀ * Real.exp (J * δ) * Real.exp (-(J * δ)) ≤ Y * Real.exp (-(J * δ)) :=
          mul_le_mul_of_nonneg_right hYX (Real.exp_pos _).le
      _ ≤ Y * q ^ j := mul_le_mul_of_nonneg_left this (by linarith)
      _ = q ^ j * Y := mul_comm _ _
  have hsum := riesz_ge_sum_psi hY1 hδ J
  have hlow : δ * ((1 - δ) * Y * ∑ j ∈ Finset.Icc 1 J, q ^ j) ≤
      δ * ∑ j ∈ Finset.Icc 1 J, Chebyshev.psi (Real.exp (-(j * δ)) * Y) := by
    refine mul_le_mul_of_nonneg_left ?_ hδ.le
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => by have := hstep j hj; linarith
  have htel := one_sub_mul_sum_Icc_pow q J
  have hS0 : 0 ≤ ∑ j ∈ Finset.Icc 1 J, q ^ j := Finset.sum_nonneg fun j _ => by positivity
  -- `δ Σ q^j ≥ (1 − q) Σ q^j = q − q^{J+1} ≥ (1 − δ)(1 − δ)`
  have hgeo : (1 - δ) * (1 - δ) ≤ δ * ∑ j ∈ Finset.Icc 1 J, q ^ j := by
    have h1 : (1 - q) * ∑ j ∈ Finset.Icc 1 J, q ^ j ≤ δ * ∑ j ∈ Finset.Icc 1 J, q ^ j :=
      mul_le_mul_of_nonneg_right hqd hS0
    have h2 : q ^ (J + 1) ≤ q * δ := by
      rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_left hqJ hq0.le
    have hq1' : q ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  have hδ4 : δ = η / 4 := hδdef
  have key : (1 - δ) * (1 - δ) * (1 - δ) * Y ≤
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n) := by
    have : (1 - δ) * Y * ((1 - δ) * (1 - δ)) ≤ (1 - δ) * Y * (δ * ∑ j ∈ Finset.Icc 1 J, q ^ j) :=
      mul_le_mul_of_nonneg_left hgeo (by nlinarith)
    nlinarith
  have hcube : 1 - η ≤ (1 - δ) * (1 - δ) * (1 - δ) := by
    rw [hδ4]; nlinarith [mul_nonneg (sq_nonneg η) (by linarith : (0 : ℝ) ≤ 12 - η)]
  nlinarith [mul_le_mul_of_nonneg_right hcube (by linarith : (0 : ℝ) ≤ Y)]

/-! ### 6. The polar test -/

/-- The polar profile `e^{−t/2} + e^{−(L−t)/2}`. -/
def polarProfile (L t : ℝ) : ℝ := Real.exp (-t / 2) + Real.exp (-(L - t) / 2)

theorem contDiff_polarProfile (L : ℝ) : ContDiff ℝ 2 (polarProfile L) :=
  (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2)).add
    (Real.contDiff_exp.comp ((contDiff_const.sub contDiff_id).neg.div_const 2))

theorem polarProfile_pos (L t : ℝ) : 0 < polarProfile L t := by
  unfold polarProfile; positivity

section PolarTest

variable {L δ : ℝ} (hδ : 0 < δ) (hLδ : 2 * δ < L)

/-- The cutoff: a smooth bump equal to `1` on `[δ, L − δ]` and supported in `(δ/2, L − δ/2)`. -/
def polarCutoff : ContDiffBump (L / 2) := ⟨L / 2 - δ, L / 2 - δ / 2, by linarith, by linarith⟩

/-- The polar test `(e^{−t/2} + e^{−(L−t)/2}) χ(t)`. -/
def polarTestReal (t : ℝ) : ℝ := polarProfile L t * polarCutoff hδ hLδ t

theorem polarCutoff_eq_one {t : ℝ} (ht : t ∈ Icc δ (L - δ)) : polarCutoff hδ hLδ t = 1 := by
  refine (polarCutoff hδ hLδ).one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  show -(L / 2 - δ) ≤ t - L / 2 ∧ t - L / 2 ≤ L / 2 - δ
  constructor <;> linarith [ht.1, ht.2]

theorem mem_of_polarCutoff_ne_zero {t : ℝ} (ht : polarCutoff hδ hLδ t ≠ 0) : t ∈ Ioo 0 L := by
  have h : t ∈ Function.support (polarCutoff hδ hLδ) := ht
  rw [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at h
  change -(L / 2 - δ / 2) < t - L / 2 ∧ t - L / 2 < L / 2 - δ / 2 at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem polarTestReal_nonneg (t : ℝ) : 0 ≤ polarTestReal hδ hLδ t :=
  mul_nonneg (polarProfile_pos L t).le (polarCutoff hδ hLδ).nonneg

theorem polarTestReal_le (t : ℝ) : polarTestReal hδ hLδ t ≤ polarProfile L t :=
  mul_le_of_le_one_right (polarProfile_pos L t).le (polarCutoff hδ hLδ).le_one

theorem polarTestReal_eq {t : ℝ} (ht : t ∈ Icc δ (L - δ)) :
    polarTestReal hδ hLδ t = polarProfile L t := by
  rw [polarTestReal, polarCutoff_eq_one hδ hLδ ht, mul_one]

theorem mem_of_polarTestReal_ne_zero {t : ℝ} (ht : polarTestReal hδ hLδ t ≠ 0) : t ∈ Ioo 0 L :=
  mem_of_polarCutoff_ne_zero hδ hLδ (right_ne_zero_of_mul ht)

theorem contDiff_polarTestReal : ContDiff ℝ 2 (polarTestReal hδ hLδ) :=
  (contDiff_polarProfile L).mul (polarCutoff hδ hLδ).contDiff

theorem hasCompactSupport_polarTestReal : HasCompactSupport (polarTestReal hδ hLδ) :=
  (polarCutoff hδ hLδ).hasCompactSupport.mul_left

/-- The polar test as a Weil test. -/
def polarTestFn : WeilTestFn :=
  ⟨fun t => (polarTestReal hδ hLδ t : ℂ), Complex.ofRealCLM.contDiff.comp (contDiff_polarTestReal hδ hLδ),
    (hasCompactSupport_polarTestReal hδ hLδ).comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero⟩

theorem polarTestFn_supp : ∀ u, (polarTestFn hδ hLδ).1 u ≠ 0 → u ∈ Ioo 0 (0 + L) := by
  intro u hu
  rw [zero_add]
  exact mem_of_polarTestReal_ne_zero hδ hLδ fun h => hu (by simp [polarTestFn, h])

theorem integrable_polarTestReal_mul (y : ℝ) :
    Integrable fun t => polarTestReal hδ hLδ t * polarTestReal hδ hLδ (t - y) :=
  ((contDiff_polarTestReal hδ hLδ).continuous.mul ((contDiff_polarTestReal hδ hLδ).continuous.comp
    (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (hasCompactSupport_polarTestReal hδ hLδ).mul_right

/-- The correlation of the polar test is real. -/
theorem weilTest_polarTestFn (y : ℝ) :
    EF.weilTest (polarTestFn hδ hLδ).1 (polarTestFn hδ hLδ).1 y =
      ((∫ t, polarTestReal hδ hLδ t * polarTestReal hδ hLδ (t - y) : ℝ) : ℂ) := by
  rw [WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
  congr 1; funext t
  simp only [polarTestFn, Complex.conj_ofReal, Complex.ofReal_mul]

/-- The correlation is even. -/
theorem integral_polarTestReal_mul_neg (y : ℝ) :
    ∫ t, polarTestReal hδ hLδ t * polarTestReal hδ hLδ (t - -y) =
      ∫ t, polarTestReal hδ hLδ t * polarTestReal hδ hLδ (t - y) := by
  have := integral_add_right_eq_self (μ := volume)
    (fun t => polarTestReal hδ hLδ t * polarTestReal hδ hLδ (t + y)) (-y)
  simp only [sub_neg_eq_add]
  rw [← this]
  congr 1; funext t
  rw [show t + -y + y = t by ring, show t + -y = t - y by ring, mul_comm]

/-- **The end-to-end correlation.** For `0 ≤ y ≤ L − 2δ`, the far ends of the polar test pair up:
`k(y) ≥ e^{−(L−y)/2} (L − y − 2δ)`. -/
theorem correlation_polarTest_ge {y : ℝ} (hy : 0 ≤ y) (hyL : y + 2 * δ ≤ L) :
    Real.exp (-(L - y) / 2) * (L - y - 2 * δ) ≤
      ∫ t, polarTestReal hδ hLδ t * polarTestReal hδ hLδ (t - y) := by
  have hg : ∫ t, (Icc (y + δ) (L - δ)).indicator (fun _ => Real.exp (-(L - y) / 2)) t =
      Real.exp (-(L - y) / 2) * (L - y - 2 * δ) := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rw [← hg]
  refine integral_mono (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc)
    (integrable_polarTestReal_mul hδ hLδ y) fun t => ?_
  by_cases ht : t ∈ Icc (y + δ) (L - δ)
  · rw [Set.indicator_of_mem ht]
    have h1 : t ∈ Icc δ (L - δ) := ⟨by linarith [ht.1], ht.2⟩
    have h2 : t - y ∈ Icc δ (L - δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [polarTestReal_eq hδ hLδ h1, polarTestReal_eq hδ hLδ h2]
    have e : Real.exp (-(L - y) / 2) = Real.exp (-(L - t) / 2) * Real.exp (-(t - y) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e, polarProfile, polarProfile]
    have := Real.exp_pos (-t / 2)
    have := Real.exp_pos (-(L - (t - y)) / 2)
    have := Real.exp_pos (-(L - t) / 2)
    have := Real.exp_pos (-(t - y) / 2)
    nlinarith
  · rw [Set.indicator_of_notMem ht]
    exact mul_nonneg (polarTestReal_nonneg hδ hLδ _) (polarTestReal_nonneg hδ hLδ _)

theorem hasCompactSupport_polarTestReal_sq :
    HasCompactSupport fun u => polarTestReal hδ hLδ u ^ 2 :=
  HasCompactSupport.intro (isCompact_Icc (a := 0) (b := L)) fun u hu => by
    by_cases h : polarTestReal hδ hLδ u = 0
    · rw [h]; norm_num
    · exact absurd (Ioo_subset_Icc_self (mem_of_polarTestReal_ne_zero hδ hLδ h)) hu

/-- The antiderivative of the squared polar profile. -/
theorem hasDerivAt_polarProfile_sq_primitive (L t : ℝ) :
    HasDerivAt (fun t => -Real.exp (-t) + Real.exp (-(L - t)) + 2 * Real.exp (-L / 2) * t)
      (Real.exp (-t) + Real.exp (-(L - t)) + 2 * Real.exp (-L / 2)) t := by
  have h1 : HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-t)) t :=
    ((hasDerivAt_neg t).exp.neg).congr_deriv (by ring)
  have h2 : HasDerivAt (fun t => Real.exp (-(L - t))) (Real.exp (-(L - t))) t :=
    (((hasDerivAt_id t).const_sub L).neg.exp).congr_deriv (by simp)
  have h3 : HasDerivAt (fun t => 2 * Real.exp (-L / 2) * t) (2 * Real.exp (-L / 2)) t :=
    ((hasDerivAt_id t).const_mul (2 * Real.exp (-L / 2))).congr_deriv (mul_one _)
  exact (h1.add h2).add h3

/-- **The mass of the polar test**: `‖f‖² ≤ 2 + 2L e^{−L/2}`. -/
theorem massOf_polarTest_le :
    massOf (Finsupp.single (polarTestFn hδ hLδ) 1) ≤ 2 + 2 * L * Real.exp (-L / 2) := by
  have hL : 0 < L := by linarith
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  have hnorm : ∀ u, ‖(polarTestFn hδ hLδ).1 u‖ ^ 2 = polarTestReal hδ hLδ u ^ 2 := fun u => by
    change ‖(polarTestReal hδ hLδ u : ℂ)‖ ^ 2 = _
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hnorm]
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ,
      g = fun t => Real.exp (-t) + Real.exp (-(L - t)) + 2 * Real.exp (-L / 2) := ⟨_, rfl⟩
  have hg : ∀ t, polarProfile L t ^ 2 = g t := fun t => by
    rw [hgdef, polarProfile]
    have e1 : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by rw [← Real.exp_nat_mul]; congr 1; ring
    have e2 : Real.exp (-(L - t) / 2) ^ 2 = Real.exp (-(L - t)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have e3 : Real.exp (-t / 2) * Real.exp (-(L - t) / 2) = Real.exp (-L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [e1, e2, e3]
  have hgc : Continuous g := by rw [hgdef]; fun_prop
  have hg0 : ∀ t, 0 ≤ g t := fun t => by rw [hgdef]; positivity
  have hint : ∫ t in (0 : ℝ)..L, g t = 2 - 2 * Real.exp (-L) + 2 * L * Real.exp (-L / 2) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => by rw [hgdef]; exact hasDerivAt_polarProfile_sq_primitive L t)
      (hgc.intervalIntegrable _ _)]
    simp only [neg_zero, Real.exp_zero, sub_zero, mul_zero, add_zero, sub_self]
    ring
  calc ∫ u, polarTestReal hδ hLδ u ^ 2
      ≤ ∫ u, (Ioc 0 L).indicator g u := by
        refine integral_mono (((contDiff_polarTestReal hδ hLδ).continuous.pow 2).integrable_of_hasCompactSupport
          (hasCompactSupport_polarTestReal_sq hδ hLδ))
          (hgc.integrableOn_Icc.mono_set Ioc_subset_Icc_self |>.integrable_indicator measurableSet_Ioc)
          fun u => ?_
        by_cases hu : polarTestReal hδ hLδ u = 0
        · rw [hu, sq, zero_mul]
          exact Set.indicator_nonneg (fun t _ => hg0 t) u
        · have hmem := mem_of_polarTestReal_ne_zero hδ hLδ hu
          rw [Set.indicator_of_mem (Ioo_subset_Ioc_self hmem), ← hg]
          exact pow_le_pow_left₀ (polarTestReal_nonneg hδ hLδ u) (polarTestReal_le hδ hLδ u) 2
    _ = ∫ t in (0 : ℝ)..L, g t := by
        rw [integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hL.le]
    _ ≤ 2 + 2 * L * Real.exp (-L / 2) := by rw [hint]; linarith [Real.exp_pos (-L)]

end PolarTest

/-! ### 7. The polar test reaches the polar ceiling -/

section PolarTestDeviation

variable {L δ : ℝ} (hδ : 0 < δ) (hLδ : 2 * δ < L)

theorem logValue_polarTest_eq (n : ℕ) :
    logValue (polarTestFn hδ hLδ).1 n =
      2 * (∫ t, polarTestReal hδ hLδ t * polarTestReal hδ hLδ (t - Real.log n)) / Real.sqrt n := by
  rw [logValue, weilTest_polarTestFn, weilTest_polarTestFn, ← Complex.ofReal_add,
    Complex.ofReal_re, integral_polarTestReal_mul_neg]
  ring

theorem logValue_polarTest_nonneg (n : ℕ) : 0 ≤ logValue (polarTestFn hδ hLδ).1 n := by
  rw [logValue_polarTest_eq]
  exact div_nonneg (mul_nonneg zero_le_two (integral_nonneg fun t =>
    mul_nonneg (polarTestReal_nonneg hδ hLδ _) (polarTestReal_nonneg hδ hLδ _))) (Real.sqrt_nonneg _)

/-- At a node `n` with `log n ≤ L − 2δ`: `L_n ≥ 2 e^{−L/2} (L − 2δ − log n)`. -/
theorem logValue_polarTest_ge {n : ℕ} (hn : 1 ≤ n) (hnL : Real.log n + 2 * δ ≤ L) :
    2 * Real.exp (-L / 2) * (L - 2 * δ - Real.log n) ≤ logValue (polarTestFn hδ hLδ).1 n := by
  have hn0 : 0 < n := hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk := correlation_polarTest_ge hδ hLδ hlog hnL
  rw [logValue_polarTest_eq, le_div_iff₀ hs]
  have e : Real.exp (-(L - Real.log n) / 2) = Real.exp (-L / 2) * Real.sqrt n := by
    rw [show -(L - Real.log n) / 2 = -L / 2 + Real.log n / 2 by ring, exp_add_half_log hn0]
  rw [e] at hk
  nlinarith [Real.exp_pos (-L / 2)]

/-- **The polar test sees the Riesz mean.** The prime side of the polar test is at least
`2 e^{−L/2} Σ_{n≤Y} Λ(n) log(Y/n)` with `Y = e^{L−2δ}`. -/
theorem primeSide_polarTest_ge :
    2 * Real.exp (-L / 2) * ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L - 2 * δ)⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Real.exp (L - 2 * δ) / n) ≤
      linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector (polarTestFn hδ hLδ)) := by
  classical
  set Y := Real.exp (L - 2 * δ)
  set N := ⌈Real.exp L⌉₊
  have hN : L ≤ Real.log N :=
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos L) (Nat.le_ceil _)
  rw [primeSide_eq_sum_of_window (polarTestFn_supp hδ hLδ) hN]
  have hYN : ⌊Y⌋₊ < N := by
    have h1 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (Real.exp_pos _).le
    have h2 : Y < Real.exp L := Real.exp_lt_exp.mpr (by linarith)
    have h3 : Real.exp L ≤ (N : ℝ) := Nat.le_ceil _
    exact_mod_cast h1.trans_lt (h2.trans_le h3)
  have hT : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * logValue (polarTestFn hδ hLδ).1 n :=
    fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (logValue_polarTest_nonneg hδ hLδ n)
  -- drop `n = 1` (where `Λ = 0`) and every node beyond `Y`
  have h1 : ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n) =
      ∑ n ∈ Finset.Icc 2 ⌊Y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n) := by
    refine (Finset.sum_subset (fun n hn => ?_) fun n hn hn2 => ?_).symm
    · rw [Finset.mem_Icc] at hn ⊢; omega
    · have : n = 1 := by rw [Finset.mem_Icc] at hn hn2; omega
      subst this; simp
  rw [h1, Finset.mul_sum]
  calc ∑ n ∈ Finset.Icc 2 ⌊Y⌋₊, 2 * Real.exp (-L / 2) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (Y / n))
      ≤ ∑ n ∈ Finset.Icc 2 ⌊Y⌋₊,
          (ArithmeticFunction.vonMangoldt n : ℝ) * logValue (polarTestFn hδ hLδ).1 n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn2 := (Finset.mem_Icc.mp hn).1
        have hnY : (n : ℝ) ≤ Y := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans
          (Nat.floor_le (Real.exp_pos _).le)
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hlogY : Real.log n ≤ L - 2 * δ := by
          calc Real.log n ≤ Real.log Y := Real.log_le_log hn0 hnY
            _ = L - 2 * δ := Real.log_exp _
        have hge := logValue_polarTest_ge hδ hLδ (n := n) (by omega) (by linarith)
        have hlogdiv : Real.log (Y / n) = L - 2 * δ - Real.log n := by
          rw [Real.log_div (Real.exp_pos _).ne' hn0.ne', Real.log_exp]
        rw [hlogdiv]
        have := mul_le_mul_of_nonneg_left hge (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        linarith
    _ ≤ ∑ n ∈ Finset.Ico 2 N,
          (ArithmeticFunction.vonMangoldt n : ℝ) * logValue (polarTestFn hδ hLδ).1 n :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
          rw [Finset.mem_Icc] at hn; rw [Finset.mem_Ico]; omega) fun n _ _ => hT n

end PolarTestDeviation

/-- `(1 + L)² e^{−L/2} → 0`. -/
theorem tendsto_one_add_sq_mul_exp_neg_half :
    Tendsto (fun L : ℝ => (1 + L) ^ 2 * Real.exp (-(L / 2))) atTop (𝓝 0) := by
  have hc : Tendsto (fun L : ℝ => L / 2) atTop atTop := tendsto_id.atTop_div_const two_pos
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hc
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hc
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hc
  have := (h0.add (h1.const_mul 4)).add (h2.const_mul 4)
  simp only [mul_zero, add_zero] at this
  refine this.congr fun L => ?_
  simp only [Function.comp_apply]
  ring

/-- The window ceiling `c(L) = sup (A − W)/‖c‖²` over windows of length `L`. -/
def windowCeiling (L : ℝ) : ℝ := sSup (windowDeviations L)

/-- **Upper half of the asymptotics.** For every `η > 0`, eventually every window deviation has
`|x| ≤ (1 + η) e^{L/2}`. -/
theorem eventually_abs_windowDeviations_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ L in atTop, ∀ x ∈ windowDeviations L, |x| ≤ (1 + η) * Real.exp (L / 2) := by
  obtain ⟨B, hB⟩ := exists_psi_le_linear (η := η / 2) (by positivity)
  have hexp : Tendsto (fun L : ℝ => Real.exp (-(L / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const two_pos)
  have hsmall := (tendsto_one_add_sq_mul_exp_neg_half.add (hexp.const_mul |B|)).eventually
    (Iio_mem_nhds (by simp; positivity : (0 : ℝ) + |B| * 0 < η / 2))
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  rintro x ⟨c, hc, hs, hm, rfl⟩
  have h := abs_nodeArchEnergy_sub_weilEnergy_le_polar hc hL0 hs hB
  rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
  have he : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hinv : Real.exp (-(L / 2)) * Real.exp (L / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hL' : (1 + L) ^ 2 + B ≤ η / 2 * Real.exp (L / 2) := by
    have h1 : ((1 + L) ^ 2 * Real.exp (-(L / 2)) + |B| * Real.exp (-(L / 2))) * Real.exp (L / 2) ≤
        η / 2 * Real.exp (L / 2) := mul_le_mul_of_nonneg_right hL.le he.le
    have h2 : ((1 + L) ^ 2 * Real.exp (-(L / 2)) + |B| * Real.exp (-(L / 2))) * Real.exp (L / 2) =
        (1 + L) ^ 2 + |B| := by
      rw [add_mul, mul_assoc, mul_assoc, hinv, mul_one, mul_one]
    linarith [le_abs_self B]
  nlinarith

/-- **Lower half of the asymptotics.** For every `η ∈ (0, 1]`, eventually some window deviation is
at least `(1 − η) e^{L/2}`: the polar test, whose two ends pair across the window at every prime
power near `e^L`. -/
theorem eventually_exists_windowDeviation_ge {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ L in atTop, ∃ x ∈ windowDeviations L, (1 - η) * Real.exp (L / 2) ≤ x := by
  classical
  set δ := η / 8 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨Y₀, hY₀1, hY₀⟩ := exists_riesz_ge (η := η / 4) (by positivity) (by linarith)
  have hLe : Tendsto (fun L : ℝ => L * Real.exp (-(L / 2))) atTop (𝓝 0) := by
    have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.atTop_div_const two_pos)).const_mul 2
    simp only [mul_zero] at this
    refine this.congr fun L => ?_
    simp only [Function.comp_apply, id, pow_one]; ring
  have hsmall := hLe.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < η / 4))
  filter_upwards [hsmall, eventually_ge_atTop (Real.log Y₀ + 2 * δ + 1)] with L hL hLY
  have hlogY₀ : 0 ≤ Real.log Y₀ := Real.log_nonneg hY₀1
  have hLδ : 2 * δ < L := by linarith
  -- the polar test of the window `(0, L)`
  set f := polarTestFn hδ hLδ
  set c : WeilTestFn →₀ ℝ := Finsupp.single f 1
  have hc : ∀ g, 0 ≤ c g := fun g => by
    simp only [c]; rw [Finsupp.single_apply]; split_ifs <;> norm_num
  have hsupp : ∀ g ∈ c.support, ∃ a, ∀ u, g.1 u ≠ 0 → u ∈ Ioo a (a + L) := fun g hg => by
    have : g = f := by
      by_contra h; exact (Finsupp.mem_support_iff.mp hg) (by simp [c, Ne.symm h])
    exact ⟨0, this ▸ polarTestFn_supp hδ hLδ⟩
  have hdev : nodeArchEnergy c - weilEnergy c =
      linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector f) := by
    rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_single_test]
  set Y := Real.exp (L - 2 * δ)
  have hYY₀ : Y₀ ≤ Y := by
    calc Y₀ = Real.exp (Real.log Y₀) := (Real.exp_log (by linarith)).symm
      _ ≤ Y := Real.exp_le_exp.mpr (by linarith)
  have hR := hY₀ Y hYY₀
  have hP := primeSide_polarTest_ge hδ hLδ
  have hmass := massOf_polarTest_le hδ hLδ
  have he : 0 < Real.exp (-L / 2) := Real.exp_pos _
  have hY0 : 0 < Y := Real.exp_pos _
  -- the prime side is large
  have hPlow : 2 * Real.exp (-L / 2) * ((1 - η / 4) * Y) ≤ nodeArchEnergy c - weilEnergy c := by
    rw [hdev]
    exact (mul_le_mul_of_nonneg_left hR (by positivity)).trans hP
  -- hence the mass is positive
  have hm : 0 < massOf c := by
    have hcheb := abs_nodeArchEnergy_sub_weilEnergy_le_chebyshev hc (by linarith) hsupp
    have hpos : 0 < nodeArchEnergy c - weilEnergy c :=
      lt_of_lt_of_le (by have : 0 < 1 - η / 4 := by linarith
                         positivity) hPlow
    by_contra h0
    push Not at h0
    have hm0 : massOf c = 0 := le_antisymm h0 (by
      rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
      exact integral_nonneg fun u => sq_nonneg _)
    rw [hm0, mul_zero] at hcheb
    linarith [le_abs_self (nodeArchEnergy c - weilEnergy c)]
  refine ⟨(nodeArchEnergy c - weilEnergy c) / massOf c, ⟨c, hc, hsupp, hm, rfl⟩, ?_⟩
  rw [le_div_iff₀ hm]
  -- `2 e^{−L/2} Y = 2 e^{−2δ} e^{L/2}` and `‖f‖² ≤ 2(1 + L e^{−L/2})`
  have hYe : Real.exp (-L / 2) * Y = Real.exp (-(2 * δ)) * Real.exp (L / 2) := by
    simp only [Y]; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hδe : 1 - η / 4 ≤ Real.exp (-(2 * δ)) := by
    have := Real.one_sub_le_exp_neg (2 * δ); rw [hδdef] at this ⊢; linarith
  have hLsmall : L * Real.exp (-L / 2) < η / 4 := by
    have : -L / 2 = -(L / 2) := by ring
    rw [this]; exact hL
  have hEL := Real.exp_pos (L / 2)
  have key : (1 - η) * Real.exp (L / 2) * (2 + 2 * L * Real.exp (-L / 2)) ≤
      2 * (1 - η / 4) * ((1 - η / 4) * Real.exp (L / 2)) := by
    have h1 : (1 - η) * (2 + 2 * L * Real.exp (-L / 2)) ≤ 2 * (1 - η / 4) * (1 - η / 4) := by
      nlinarith [mul_le_mul_of_nonneg_left hLsmall.le (by linarith : (0 : ℝ) ≤ 1 - η)]
    nlinarith
  have hfin : 2 * (1 - η / 4) * ((1 - η / 4) * Real.exp (L / 2)) ≤
      2 * Real.exp (-L / 2) * ((1 - η / 4) * Y) := by
    have : 2 * Real.exp (-L / 2) * ((1 - η / 4) * Y) =
        2 * (1 - η / 4) * (Real.exp (-(2 * δ)) * Real.exp (L / 2)) := by rw [← hYe]; ring
    rw [this]
    have : 0 ≤ 1 - η / 4 := by linarith
    have := mul_le_mul_of_nonneg_right hδe hEL.le
    nlinarith
  calc (1 - η) * Real.exp (L / 2) * massOf c
      ≤ (1 - η) * Real.exp (L / 2) * (2 + 2 * L * Real.exp (-L / 2)) :=
        mul_le_mul_of_nonneg_left hmass (mul_nonneg (by linarith) hEL.le)
    _ ≤ 2 * (1 - η / 4) * ((1 - η / 4) * Real.exp (L / 2)) := key
    _ ≤ 2 * Real.exp (-L / 2) * ((1 - η / 4) * Y) := hfin
    _ ≤ nodeArchEnergy c - weilEnergy c := hPlow

/-- **The window ceiling is asymptotic to the polar ceiling:** `c(L)/e^{L/2} → 1`, i.e. the
prime side on windows of length `log X` reaches exactly `√X (1 + o(1))`. -/
theorem tendsto_windowCeiling_div_exp :
    Tendsto (fun L => windowCeiling L / Real.exp (L / 2)) atTop (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    set η := min ((1 - a) / 2) 1
    have hη : 0 < η := lt_min (by linarith) one_pos
    have hη1 : η ≤ 1 := min_le_right _ _
    have hηa : a < 1 - η := by
      have : η ≤ (1 - a) / 2 := min_le_left _ _
      linarith
    filter_upwards [eventually_exists_windowDeviation_ge hη hη1,
      eventually_ge_atTop (0 : ℝ)] with L ⟨x, hx, hxge⟩ hL0
    have hbdd : BddAbove (windowDeviations L) :=
      ⟨(Real.log 4 + 4) * Real.exp (L / 2) + (1 + L) ^ 2, fun y ⟨c, hc, hs, hm, hy⟩ => by
        rw [hy, div_le_iff₀ hm]
        exact (le_abs_self _).trans (abs_nodeArchEnergy_sub_weilEnergy_le_chebyshev hc hL0 hs)⟩
    have hsup := le_csSup hbdd hx
    rw [lt_div_iff₀ (Real.exp_pos _)]
    unfold windowCeiling
    nlinarith [mul_lt_mul_of_pos_right hηa (Real.exp_pos (L / 2))]
  · intro b hb
    set η := (b - 1) / 2
    have hη : 0 < η := by simp only [η]; linarith
    filter_upwards [eventually_abs_windowDeviations_le hη,
      eventually_exists_windowDeviation_ge (η := 1) one_pos le_rfl] with L hle ⟨x, hx, _⟩
    have hsup : windowCeiling L ≤ (1 + η) * Real.exp (L / 2) :=
      csSup_le ⟨x, hx⟩ fun y hy => (le_abs_self y).trans (hle y hy)
    rw [div_lt_iff₀ (Real.exp_pos _)]
    have hηb : 1 + η < b := by simp only [η]; linarith
    nlinarith [mul_lt_mul_of_pos_right hηb (Real.exp_pos (L / 2))]

end

end GaloisForLFunctions.BiScaleUncertainty
