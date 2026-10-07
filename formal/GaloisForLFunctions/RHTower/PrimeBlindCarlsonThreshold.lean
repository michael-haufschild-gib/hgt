import Mathlib

/-!
# Blindness at `log ℕ` at the Carlson rate `π/2`

Let `w` be integrable on `ℝ` and `N` a set of integers `≥ 2`.  Call `w` *blind* on `N` if its
Dirichlet moments `∫ w(t) n^{-it} dt` vanish for `n ∈ N`.  The transform
`G(ζ) = ∫ w(t) e^{-it log ζ} dt` is analytic on `Re ζ > 0` as soon as `w` decays like `e^{-(π/2)|t|}`
up to a subexponential factor; `G(n)` is the `n`-th moment and `G(e^x)` the Fourier transform at `x`.

**Bounded transform** (`fourier_eq_zero_of_dirichletMoment_eq_zero`).  If `∫ |w| e^{(π/2)|t|} < ∞`
and `Σ_{n ∈ N} 1/n = ∞`, then `G` is bounded on `Re ζ > 0`, the Blaschke condition fails at the
nodes, and `ŵ ≡ 0`.

**Polynomial room, divergent node sets** (`fourier_eq_zero_of_dirichletMoment_eq_zero_room`).  The
same holds under `∫ |w| e^{(π/2)|t|} (1+|t|)^{-a} < ∞` for any `a ≥ 0`, for instance at the primes
(`fourier_eq_zero_of_primeMoment_eq_zero_room`).  On `Re ζ ≥ 1` the angle to the imaginary axis is at
least `1/|ζ|`, so `G(ξ + 1)/(ξ + 1)^{⌈a⌉}` is bounded on `Re ξ > 0` and vanishes at `n - 1`.

**Subexponential room, log-dense node sets** (`fourier_eq_zero_of_dirichletMoment_eq_zero_density`,
`fourier_eq_zero_of_integerMoment_eq_zero_room`).  If `∫ |w| e^{(π/2)|t| - K√|t|} < ∞` for some `K`
and `Σ_{n ∈ N, n ≤ X} 1/(n+1) ≥ κ log X - C₀` with `κ > 0` (for instance all `n ≥ 2`), then
`ŵ ≡ 0`.  This is Carlson's theorem in the variable `log ζ`.  After the shift
`ζ = m + (1+z)/(1-z)` with `m > K²/(4κ)`, `log |G| ≤ C + (K²/(2m))/|1 - z|`; the circle averages of
`1/|1 - z|` grow like `log(1/(1-R))` (`circleAverage_inv_norm_one_sub_le`), while Jensen's formula
receives `2κ log(1/(1-R))` from the nodes (`eqOn_zero_of_discNode_zeros_density`).

The rate `π/2` is the decay rate of `Ξ(t)² = ξ(1/2+it)²`.  A weight `Ξ² h` blind at every integer
`n ≥ 2` (the dual certificate of Weil-cone uniqueness) therefore has
`∫ Ξ² |h| e^{(π/2)|t| - K√|t|} = ∞` for every `K`: its multiplier `h` is not tempered, and not even
of order `e^{O(√|t|)}`.
-/

open Metric Real Filter Topology MeasureTheory Set Complex

noncomputable section

namespace RHTower.PrimeBlindCarlson

/-! ## Jensen's bound on the unit disc -/

private theorem finsum_ge_sum {φ : ℂ → ℝ} (hφ : ∀ u, 0 ≤ φ u) (hfin : (Function.support φ).Finite)
    (T : Finset ℂ) : ∑ u ∈ T, φ u ≤ ∑ᶠ u, φ u := by
  rw [finsum_eq_sum φ hfin]
  calc ∑ u ∈ T, φ u = ∑ u ∈ T.filter (fun u => φ u ≠ 0), φ u := by
        rw [Finset.sum_filter_ne_zero]
    _ ≤ ∑ u ∈ hfin.toFinset, φ u := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) (fun u _ _ => hφ u)
        rw [Finset.mem_filter] at hu
        simpa using hu.2


/-- **Jensen's bound.**  Let `f` be analytic on the unit disc with finite order at every point, and
let `avg_{|z| = R} log |f| ≤ B`, `0 < R < 1`.  Then for every finite set `T` of nonzero zeros of `f`
with `|u| ≤ R`: `Σ_{u ∈ T} log(R/|u|) ≤ B - k log R - log |c|`, where `k` is the order and `c` the
leading coefficient at `0`. -/
theorem sum_log_le_of_circleAverage_le {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hord : ∀ u ∈ ball (0 : ℂ) 1, analyticOrderAt f u ≠ ⊤) {R B : ℝ} (hR0 : 0 < R)
    (hR1 : R < 1) (hint : Real.circleAverage (fun x => Real.log ‖f x‖) 0 R ≤ B)
    (T : Finset ℂ) (hT : ∀ u ∈ T, ‖u‖ ≤ R ∧ u ≠ 0 ∧ f u = 0) :
    ∑ u ∈ T, Real.log (R * ‖u‖⁻¹) ≤
      B - (MeromorphicOn.divisor f (closedBall 0 |R|) 0 : ℝ) * Real.log R -
        Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hRabs : |R| = R := abs_of_pos hR0
  have hsub : closedBall (0 : ℂ) |R| ⊆ ball 0 1 := by
    rw [hRabs]; exact closedBall_subset_ball hR1
  have hfc : AnalyticOnNhd ℂ f (closedBall 0 |R|) := hf.mono hsub
  have jensen := hfc.meromorphicOn.circleAverage_log_norm hR0.ne'
  set D := MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) with hD
  have hnn : ∀ u, 0 ≤ (D u : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) |R|
    · refine mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfc u) ?_
      rcases eq_or_ne u 0 with h0 | h0
      · simp [h0]
      · rw [zero_sub, norm_neg]
        have hu' : ‖u‖ ≤ R := by simpa [hRabs] using hu
        have hpos : 0 < ‖u‖ := norm_pos_iff.mpr h0
        exact Real.log_nonneg (by rw [← div_eq_mul_inv, le_div_iff₀ hpos]; linarith)
    · simp [D, hu]
  have hfin : (Function.support fun u => (D u : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹)).Finite := by
    refine (D.finiteSupport (isCompact_closedBall 0 |R|)).subset fun u hu => ?_
    rw [Function.mem_support] at hu ⊢
    intro h; apply hu; simp [h]
  have hT' : ∑ u ∈ T, Real.log (R * ‖u‖⁻¹) ≤
      ∑ u ∈ T, (D u : ℝ) * Real.log (R * ‖(0 : ℂ) - u‖⁻¹) := by
    refine Finset.sum_le_sum fun u hu => ?_
    obtain ⟨huR, hu0, hfu⟩ := hT u hu
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hlog : 0 ≤ Real.log (R * ‖u‖⁻¹) :=
      Real.log_nonneg (by rw [← div_eq_mul_inv, le_div_iff₀ hpos]; linarith)
    have hmem : u ∈ closedBall (0 : ℂ) |R| := by simpa [hRabs] using huR
    have hD1 : (1 : ℝ) ≤ D u := by
      rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply hfc hmem]
      have hzero : analyticOrderAt f u ≠ 0 := by
        rw [Ne, (hfc u hmem).analyticOrderAt_eq_zero]; simpa using hfu
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hord u (hsub hmem))
      rw [← hk] at hzero ⊢
      have hk0 : k ≠ 0 := by intro h0; apply hzero; rw [h0]; rfl
      simp only [ENat.map_coe, WithTop.untop₀_coe]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
    rw [zero_sub, norm_neg]
    exact le_mul_of_one_le_left hlog hD1
  have hfs := finsum_ge_sum hnn hfin T
  linarith

/-- **Jensen's bound with a bound on the circle.**  The same with `|f| ≤ M`, `M ≥ 1`, on
`|z| = R`. -/
theorem sum_log_le_of_jensen {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1)) {M : ℝ}
    (hM : 1 ≤ M) (hord : ∀ u ∈ ball (0 : ℂ) 1, analyticOrderAt f u ≠ ⊤) {R : ℝ} (hR0 : 0 < R)
    (hR1 : R < 1) (hb : ∀ z ∈ sphere (0 : ℂ) |R|, ‖f z‖ ≤ M)
    (T : Finset ℂ) (hT : ∀ u ∈ T, ‖u‖ ≤ R ∧ u ≠ 0 ∧ f u = 0) :
    ∑ u ∈ T, Real.log (R * ‖u‖⁻¹) ≤
      Real.log M - (MeromorphicOn.divisor f (closedBall 0 |R|) 0 : ℝ) * Real.log R -
        Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hRabs : |R| = R := abs_of_pos hR0
  have hfc : AnalyticOnNhd ℂ f (closedBall 0 |R|) :=
    hf.mono (by rw [hRabs]; exact closedBall_subset_ball hR1)
  refine sum_log_le_of_circleAverage_le hf hord hR0 hR1 ?_ T hT
  apply Real.circleAverage_mono_on_of_le_circle
  · exact (hfc.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  · intro z hz
    rcases eq_or_ne (f z) 0 with h | h
    · rw [h, norm_zero, Real.log_zero]; exact Real.log_nonneg hM
    · exact Real.log_le_log (norm_pos_iff.mpr h) (hb z hz)


/-! ## Zeros at `(n-1)/(n+1)` with `Σ 1/n = ∞` -/

/-- The disc point corresponding to `n` under `ζ = (1+z)/(1-z)`. -/
def discNode (n : ℕ) : ℂ := ((n : ℂ) - 1) / ((n : ℂ) + 1)

theorem discNode_eq_ofReal (n : ℕ) : discNode n = (((n : ℝ) - 1) / ((n : ℝ) + 1) : ℝ) := by
  unfold discNode; push_cast; rfl

theorem norm_discNode {n : ℕ} (hn : 1 ≤ n) : ‖discNode n‖ = ((n : ℝ) - 1) / ((n : ℝ) + 1) := by
  rw [discNode_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (by linarith) (by linarith)

theorem discNode_ne_zero {n : ℕ} (hn : 2 ≤ n) : discNode n ≠ 0 := by
  intro h
  have := norm_discNode (by omega : 1 ≤ n)
  rw [h, norm_zero] at this
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : ((n : ℝ) - 1) / ((n : ℝ) + 1) > 0 := div_pos (by linarith) (by linarith)
  linarith

theorem discNode_injective : Function.Injective discNode := by
  intro m n h
  rw [discNode_eq_ofReal, discNode_eq_ofReal, Complex.ofReal_inj] at h
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [div_eq_div_iff hm.ne' hn.ne'] at h
  have : (m : ℝ) = n := by nlinarith
  exact_mod_cast this

/-- `log((n+1)/(n-1)) ≥ 1/n` for `n ≥ 2`. -/
theorem one_div_le_log_inv_discNode {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / n ≤ Real.log (‖discNode n‖⁻¹) := by
  rw [norm_discNode (by omega : 1 ≤ n), inv_div]
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < ((n : ℝ) + 1) / ((n : ℝ) - 1) := div_pos (by linarith) (by linarith)
  have hlog := Real.add_one_le_exp (-(1 / (n : ℝ)))
  -- `log x ≥ 1 - 1/x` with `1/x = (n-1)/(n+1) ≤ 1 - 1/n`
  have key : 1 - ((n : ℝ) - 1) / ((n : ℝ) + 1) ≥ 1 / n := by
    rw [show 1 - ((n : ℝ) - 1) / ((n : ℝ) + 1) = 2 / ((n : ℝ) + 1) by field_simp; ring,
      ge_iff_le, div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have hl : 1 - (((n : ℝ) + 1) / ((n : ℝ) - 1))⁻¹ ≤ Real.log (((n : ℝ) + 1) / ((n : ℝ) - 1)) := by
    have := Real.one_sub_inv_le_log_of_pos hpos
    exact this
  rw [inv_div] at hl
  linarith

/-- **Rigidity on the disc.**  A bounded analytic function on the unit disc that vanishes at
`(n-1)/(n+1)` for every `n` in a set `N ⊆ [2, ∞)` with `Σ_{n ∈ N} 1/n = ∞` vanishes identically. -/
theorem eqOn_zero_of_discNode_zeros {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1)) {M : ℝ}
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M) {N : Set ℕ} (hN2 : ∀ n ∈ N, 2 ≤ n)
    (hdiv : ¬ Summable (N.indicator fun n : ℕ => (1 : ℝ) / n))
    (hz : ∀ n ∈ N, f (discNode n) = 0) : EqOn f 0 (ball 0 1) := by
  classical
  by_contra hne
  have hconn : IsConnected (ball (0 : ℂ) 1) := (convex_ball 0 1).isConnected (by simp)
  obtain ⟨z₀, hz₀, hfz₀⟩ : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0 := by
    by_contra h; push Not at h; exact hne fun z hz => h z hz
  have hord : ∀ u ∈ ball (0 : ℂ) 1, analyticOrderAt f u ≠ ⊤ := by
    have h0 : analyticOrderAt f z₀ ≠ ⊤ := by
      rw [(hf z₀ hz₀).analyticOrderAt_eq_zero.mpr hfz₀]; exact ENat.zero_ne_top
    intro u hu
    exact (hf.exists_analyticOrderAt_ne_top_iff_forall hconn).mp ⟨⟨z₀, hz₀⟩, h0⟩ ⟨u, hu⟩
  set M' := max M 1
  have hM' : 1 ≤ M' := le_max_right _ _
  have hb' : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M' := fun z hz => (hb z hz).trans (le_max_left _ _)
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hmer0 : meromorphicOrderAt f 0 ≠ ⊤ := by
    rw [(hf 0 h0ball).meromorphicOrderAt_eq]
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hord 0 h0ball)
    rw [← hk]; simp
  have hc : meromorphicTrailingCoeffAt f 0 ≠ 0 :=
    (hf 0 h0ball).meromorphicAt.meromorphicTrailingCoeffAt_ne_zero hmer0
  -- the divisor at `0` does not depend on the radius
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hord 0 h0ball)
  have hdiv0 : ∀ R : ℝ, 0 < R → R < 1 →
      (MeromorphicOn.divisor f (closedBall 0 |R|) 0 : ℝ) = k := by
    intro R hR0 _
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hf.mono (by
        rw [abs_of_pos hR0]; exact closedBall_subset_ball (by assumption))) (by simp), ← hk]
    simp
  set C := Real.log M' + k * Real.log 2 - Real.log ‖meromorphicTrailingCoeffAt f 0‖ + 1
  -- bounded partial sums
  have hpartial : ∀ S : Finset ℕ, (∀ n ∈ S, n ∈ N) →
      ∑ n ∈ S, Real.log (‖discNode n‖⁻¹) ≤ C := by
    intro S hS
    set m := S.sup id with hm
    set R : ℝ := max (max (1 / 2) (Real.exp (-(1 / ((S.card : ℝ) + 1)))))
      (1 - 1 / ((m : ℝ) + 1)) with hR
    have hRhalf : 1 / 2 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
    have hRexp : Real.exp (-(1 / ((S.card : ℝ) + 1))) ≤ R :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hRm : 1 - 1 / ((m : ℝ) + 1) ≤ R := le_max_right _ _
    have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hRhalf
    have hR1 : R < 1 := by
      refine max_lt (max_lt (by norm_num) ?_) ?_
      · have : (0 : ℝ) < 1 / ((S.card : ℝ) + 1) := by positivity
        have h := Real.exp_lt_exp.mpr (show -(1 / ((S.card : ℝ) + 1)) < 0 by linarith)
        rwa [Real.exp_zero] at h
      · have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        linarith
    have hT : ∀ u ∈ S.image discNode, ‖u‖ ≤ R ∧ u ≠ 0 ∧ f u = 0 := by
      intro u hu
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
      have hn2 := hN2 n (hS n hn)
      refine ⟨?_, discNode_ne_zero hn2, hz n (hS n hn)⟩
      rw [norm_discNode (by omega)]
      have hnm : (n : ℝ) ≤ m := by exact_mod_cast (Finset.le_sup (f := id) hn)
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      refine le_trans ?_ hRm
      rw [show ((n : ℝ) - 1) / ((n : ℝ) + 1) = 1 - 2 / ((n : ℝ) + 1) by field_simp; ring]
      have : 1 / ((m : ℝ) + 1) ≤ 2 / ((n : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      linarith
    have hJ := sum_log_le_of_jensen hf hM' hord hR0 hR1 (fun z hz => hb' z (by
      rw [abs_of_pos hR0] at hz
      simpa [mem_sphere_zero_iff_norm.mp hz] using hR1)) (S.image discNode) hT
    rw [hdiv0 R hR0 hR1, Finset.sum_image (fun a _ b _ h => discNode_injective h)] at hJ
    have hsplit : ∑ n ∈ S, Real.log (R * ‖discNode n‖⁻¹) =
        S.card * Real.log R + ∑ n ∈ S, Real.log (‖discNode n‖⁻¹) := by
      rw [Finset.sum_congr rfl (fun n hn => Real.log_mul hR0.ne'
        (inv_ne_zero (norm_ne_zero_iff.mpr (discNode_ne_zero (hN2 n (hS n hn)))))),
        Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hlogR : -1 ≤ (S.card : ℝ) * Real.log R := by
      have h1 : -(1 / ((S.card : ℝ) + 1)) ≤ Real.log R := by
        rw [← Real.log_exp (-(1 / ((S.card : ℝ) + 1)))]
        exact Real.log_le_log (Real.exp_pos _) hRexp
      have hc : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
      have h2 : (S.card : ℝ) * (1 / ((S.card : ℝ) + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
      nlinarith
    have hklog : -((k : ℝ) * Real.log R) ≤ k * Real.log 2 := by
      have h1 : -Real.log 2 ≤ Real.log R := by
        rw [← Real.log_inv, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
        exact Real.log_le_log (by norm_num) hRhalf
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      nlinarith
    simp only [C]
    linarith
  apply hdiv
  have hlog_nn : ∀ n ∈ N, 0 ≤ Real.log (‖discNode n‖⁻¹) := fun n hn =>
    le_trans (by positivity) (one_div_le_log_inv_discNode (hN2 n hn))
  have hsum : Summable (N.indicator fun n : ℕ => Real.log (‖discNode n‖⁻¹)) := by
    refine summable_of_sum_le (c := C) (fun n => ?_) (fun s => ?_)
    · by_cases hn : n ∈ N
      · rw [Set.indicator_of_mem hn]; exact hlog_nn n hn
      · simp [hn]
    · have : ∑ n ∈ s, N.indicator (fun n : ℕ => Real.log (‖discNode n‖⁻¹)) n =
          ∑ n ∈ s.filter (· ∈ N), Real.log (‖discNode n‖⁻¹) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun n _ => by simp [Set.indicator_apply]
      rw [this]
      exact hpartial _ fun n hn => (Finset.mem_filter.mp hn).2
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
  · by_cases hn : n ∈ N
    · rw [Set.indicator_of_mem hn]; positivity
    · simp [hn]
  · by_cases hn : n ∈ N
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
      exact one_div_le_log_inv_discNode (hN2 n hn)
    · simp [hn]

/-! ## The right half-plane -/

/-- The right half-plane `Re ζ > 0`. -/
def rightHalf : Set ℂ := {ζ | 0 < ζ.re}

theorem isOpen_rightHalf : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re

/-- The Cayley map `z ↦ (1+z)/(1-z)` from the unit disc onto the right half-plane. -/
def cayley (z : ℂ) : ℂ := (1 + z) / (1 - z)

theorem one_sub_ne_zero_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this, norm_one] at hz
  exact lt_irrefl _ hz

theorem re_cayley_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (cayley z).re := by
  have hne := one_sub_ne_zero_of_norm_lt hz
  have hns : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hne
  have hz2 : z.re ^ 2 + z.im ^ 2 < 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at h
    have : ‖z‖ ^ 2 < 1 := by
      have := norm_nonneg z
      nlinarith
    nlinarith
  unfold cayley
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im]
  rw [← add_div]
  apply div_pos _ hns
  nlinarith

theorem cayley_discNode (n : ℕ) : cayley (discNode n) = n := by
  unfold cayley discNode
  have h1 : (n : ℂ) + 1 ≠ 0 := by
    have : (0 : ℝ) < n + 1 := by positivity
    exact_mod_cast this.ne'
  field_simp
  ring

theorem norm_inverseCayley_lt {ζ : ℂ} (hζ : 0 < ζ.re) : ‖(ζ - 1) / (ζ + 1)‖ < 1 := by
  have hne : ζ + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hne)]
  have h1 : ‖ζ - 1‖ ^ 2 < ‖ζ + 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, Complex.add_re,
      Complex.add_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

theorem cayley_inverseCayley {ζ : ℂ} (hζ : 0 < ζ.re) : cayley ((ζ - 1) / (ζ + 1)) = ζ := by
  have hne : ζ + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold cayley
  field_simp
  ring

/-- `G ∘ cayley` is analytic on the unit disc. -/
theorem analyticOnNhd_comp_cayley {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G rightHalf) :
    AnalyticOnNhd ℂ (G ∘ cayley) (ball 0 1) := by
  intro z hz1
  have hz1' : ‖z‖ < 1 := by simpa using hz1
  have hc : AnalyticAt ℂ cayley z :=
    (analyticAt_const.add analyticAt_id).div (analyticAt_const.sub analyticAt_id)
      (one_sub_ne_zero_of_norm_lt hz1')
  exact (hG (cayley z) (re_cayley_pos hz1')).comp hc

/-- A function vanishing on the disc after `cayley` vanishes on the half-plane. -/
theorem eqOn_rightHalf_of_comp_cayley {G : ℂ → ℂ} (h0 : EqOn (G ∘ cayley) 0 (ball 0 1)) :
    EqOn G 0 rightHalf := by
  intro ζ hζ
  have hζ' : 0 < ζ.re := hζ
  have := h0 (show (ζ - 1) / (ζ + 1) ∈ ball (0 : ℂ) 1 by
    simpa using norm_inverseCayley_lt hζ')
  simpa [Function.comp, cayley_inverseCayley hζ'] using this

/-- **Rigidity on the half-plane.**  A bounded analytic function on `Re ζ > 0` that vanishes at
every `n ∈ N`, with `Σ_{n ∈ N} 1/n = ∞`, vanishes identically. -/
theorem eqOn_zero_of_halfPlane_zeros {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G rightHalf) {M : ℝ}
    (hb : ∀ ζ ∈ rightHalf, ‖G ζ‖ ≤ M) {N : Set ℕ} (hN2 : ∀ n ∈ N, 2 ≤ n)
    (hdiv : ¬ Summable (N.indicator fun n : ℕ => (1 : ℝ) / n))
    (hz : ∀ n ∈ N, G n = 0) : EqOn G 0 rightHalf :=
  eqOn_rightHalf_of_comp_cayley (eqOn_zero_of_discNode_zeros (analyticOnNhd_comp_cayley hG)
    (fun z hz1 => hb _ (re_cayley_pos (by simpa using hz1))) hN2 hdiv
    (fun n hn => by simp only [Function.comp, cayley_discNode]; exact hz n hn))

/-! ## The Fourier transform at the critical decay -/

/-- `G(ζ) = ∫ w(t) e^{-it log ζ} dt`; at `ζ = n` it is the Dirichlet moment `∫ w(t) n^{-it} dt`,
at `ζ = e^x` the Fourier transform at `x`. -/
def logFourier (w : ℝ → ℂ) (ζ : ℂ) : ℂ := ∫ t, w t * cexp (-(I * t) * Complex.log ζ)

theorem re_neg_I_mul_log (t : ℝ) (ζ : ℂ) : (-(I * t) * Complex.log ζ).re = t * ζ.arg := by
  simp [Complex.mul_re, Complex.log_im]

theorem norm_cexp_log_le_of_abs_arg_le {ζ : ℂ} {a : ℝ} (ha : |ζ.arg| ≤ a) (t : ℝ) :
    ‖cexp (-(I * t) * Complex.log ζ)‖ ≤ Real.exp (a * |t|) := by
  rw [Complex.norm_exp, re_neg_I_mul_log]
  refine Real.exp_le_exp.mpr ?_
  calc t * ζ.arg ≤ |t * ζ.arg| := le_abs_self _
    _ = |t| * |ζ.arg| := abs_mul _ _
    _ ≤ |t| * a := mul_le_mul_of_nonneg_left ha (abs_nonneg t)
    _ = a * |t| := mul_comm _ _

theorem abs_arg_le_of_re_pos {ζ : ℂ} (hζ : 0 < ζ.re) : |ζ.arg| ≤ Real.pi / 2 :=
  (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζ)).le

/-! ### Elementary bounds -/

/-- `x^b e^{-x}` is bounded on `x ≥ 0` for `b ≥ 0`. -/
theorem exists_rpow_mul_exp_neg_le {b : ℝ} (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 ≤ x → x ^ b * Real.exp (-x) ≤ K := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero b 1 one_pos).eventually
      (Iic_mem_nhds one_pos))
  set X' := max X 1
  have hcont : ContinuousOn (fun x : ℝ => x ^ b * Real.exp (-x)) (Icc 1 X') := fun x hx =>
    ((Real.continuousAt_rpow_const x b (Or.inl (by linarith [hx.1]))).mul
      (Real.continuous_exp.comp continuous_neg).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  rcases le_total x 1 with h1 | h1
  · have hxb : x ^ b ≤ 1 := Real.rpow_le_one hx h1 hb
    have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc x ^ b * Real.exp (-x) ≤ 1 * 1 :=
          mul_le_mul hxb he (Real.exp_pos _).le zero_le_one
      _ ≤ max C 1 := by rw [mul_one]; exact le_max_right _ _
  rcases le_total x X' with h2 | h2
  · have := hC x ⟨h1, h2⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  · have h : x ^ b * Real.exp (-1 * x) ≤ 1 := hX x (le_trans (le_max_left _ _) h2)
    rw [neg_one_mul] at h
    exact h.trans (le_max_right _ _)

/-- `(1+s)^b e^{-ηs} ≤ e^η η^{-b} K` for `s ≥ 0`, if `x^b e^{-x} ≤ K` on `x ≥ 0`. -/
theorem one_add_rpow_mul_exp_neg_le {b K η : ℝ}
    (hK : ∀ x : ℝ, 0 ≤ x → x ^ b * Real.exp (-x) ≤ K) (hη : 0 < η) {s : ℝ} (hs : 0 ≤ s) :
    (1 + s) ^ b * Real.exp (-(η * s)) ≤ Real.exp η * η ^ (-b) * K := by
  have hx := hK (η * (1 + s)) (by positivity)
  rw [Real.mul_rpow hη.le (by linarith)] at hx
  have hηb : 0 < η ^ b := Real.rpow_pos_of_pos hη b
  have heq : (1 + s) ^ b * Real.exp (-(η * s)) =
      Real.exp η * η ^ (-b) * (η ^ b * (1 + s) ^ b * Real.exp (-(η * (1 + s)))) := by
    rw [Real.rpow_neg hη.le, show -(η * s) = η + -(η * (1 + s)) by ring, Real.exp_add]
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left hx (by positivity)

/-- The critical weight with polynomial room `a`: `e^{(π/2)|t|} (1+|t|)^{-a}`. -/
def roomWeight (a t : ℝ) : ℝ := Real.exp (Real.pi / 2 * |t|) * (1 + |t|) ^ (-a)

theorem roomWeight_zero (t : ℝ) : roomWeight 0 t = Real.exp (Real.pi / 2 * |t|) := by
  simp [roomWeight]

theorem roomWeight_nonneg (a t : ℝ) : 0 ≤ roomWeight a t := by
  unfold roomWeight
  have := abs_nonneg t
  positivity

/-- `e^{(π/2 - η)|t|} ≤ w_a(t) e^η η^{-a} K`. -/
theorem exp_le_roomWeight_mul {a K η : ℝ}
    (hK : ∀ x : ℝ, 0 ≤ x → x ^ a * Real.exp (-x) ≤ K) (hη : 0 < η) (t : ℝ) :
    Real.exp ((Real.pi / 2 - η) * |t|) ≤ roomWeight a t * (Real.exp η * η ^ (-a) * K) := by
  have h1 : 0 < 1 + |t| := by have := abs_nonneg t; linarith
  have hkey := one_add_rpow_mul_exp_neg_le hK hη (abs_nonneg t)
  have heq : Real.exp ((Real.pi / 2 - η) * |t|) =
      roomWeight a t * ((1 + |t|) ^ a * Real.exp (-(η * |t|))) := by
    unfold roomWeight
    rw [Real.rpow_neg h1.le, show (Real.pi / 2 - η) * |t| = Real.pi / 2 * |t| + -(η * |t|) by
      ring, Real.exp_add]
    have : (1 + |t|) ^ a ≠ 0 := (Real.rpow_pos_of_pos h1 a).ne'
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left hkey (roomWeight_nonneg a t)


/-- A weight `ω` dominates every subcritical exponential: for each `c > 0`,
`(1+|t|) e^{(π/2 - c)|t|} ≤ D ω(t)`. -/
def DominatesSubcritical (ω : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ D : ℝ, ∀ t : ℝ, (1 + |t|) * Real.exp ((Real.pi / 2 - c) * |t|) ≤ ω t * D

theorem dominatesSubcritical_roomWeight {a : ℝ} (ha : 0 ≤ a) :
    DominatesSubcritical (roomWeight a) := by
  intro c hc
  obtain ⟨K, -, hK⟩ := exists_rpow_mul_exp_neg_le (b := a + 1) (by linarith)
  refine ⟨Real.exp c * c ^ (-(a + 1)) * K, fun t => ?_⟩
  have h1 : 0 < 1 + |t| := by have := abs_nonneg t; linarith
  have hkey := one_add_rpow_mul_exp_neg_le hK hc (abs_nonneg t)
  have heq : (1 + |t|) * Real.exp ((Real.pi / 2 - c) * |t|) =
      roomWeight a t * ((1 + |t|) ^ (a + 1) * Real.exp (-(c * |t|))) := by
    unfold roomWeight
    rw [Real.rpow_neg h1.le, Real.rpow_add h1, Real.rpow_one,
      show (Real.pi / 2 - c) * |t| = Real.pi / 2 * |t| + -(c * |t|) by ring, Real.exp_add]
    have : (1 + |t|) ^ a ≠ 0 := (Real.rpow_pos_of_pos h1 a).ne'
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left hkey (roomWeight_nonneg a t)

/-! ### Analyticity and growth -/

variable {w : ℝ → ℂ}

theorem integrable_logFourier_integrand {ω : ℝ → ℝ} (hω : DominatesSubcritical ω)
    (hwm : AEStronglyMeasurable w volume) (hint : Integrable fun t => ‖w t‖ * ω t)
    {ζ : ℂ} (hζ : 0 < ζ.re) :
    Integrable fun t : ℝ => w t * cexp (-(I * t) * Complex.log ζ) := by
  set η := Real.pi / 2 - |ζ.arg| with hη
  have hη0 : 0 < η := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζ); linarith
  obtain ⟨D, hD⟩ := hω η hη0
  refine Integrable.mono' (hint.mul_const D)
    (hwm.mul (by fun_prop : Continuous fun t : ℝ =>
      cexp (-(I * t) * Complex.log ζ)).aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_cexp_log_le_of_abs_arg_le (a := Real.pi / 2 - η) (by rw [hη]; ring_nf; rfl) t).trans
    (le_trans ?_ (hD t))
  have := Real.exp_pos ((Real.pi / 2 - η) * |t|)
  have := abs_nonneg t
  nlinarith

theorem differentiableAt_logFourier {ω : ℝ → ℝ} (hω : DominatesSubcritical ω)
    (hwm : AEStronglyMeasurable w volume) (hint : Integrable fun t => ‖w t‖ * ω t) {ζ₀ : ℂ}
    (hζ₀ : 0 < ζ₀.re) : DifferentiableAt ℂ (logFourier w) ζ₀ := by
  set r := ζ₀.re / 2 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall ζ₀ r ⊆ {ζ : ℂ | r ≤ ζ.re} := by
    intro ζ hζ
    have h := Complex.abs_re_le_norm (ζ - ζ₀)
    rw [mem_closedBall, dist_eq_norm] at hζ
    simp only [Set.mem_setOf_eq, Complex.sub_re] at h ⊢
    have := abs_le.mp (h.trans hζ)
    linarith [this.1]
  have hslit : ∀ ζ ∈ closedBall ζ₀ r, ζ ∈ Complex.slitPlane := fun ζ hζ =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le hr0 (hK hζ)))
  obtain ⟨ζ₁, hζ₁K, hmax⟩ := (isCompact_closedBall ζ₀ r).exists_isMaxOn
    (nonempty_closedBall.mpr hr0.le)
    (fun ζ hζ => (continuous_abs.continuousAt.comp
      (Complex.continuousAt_arg (hslit ζ hζ))).continuousWithinAt)
  set θ₀ := |ζ₁.arg| with hθ₀
  have hθ₀2 : θ₀ < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (lt_of_lt_of_le hr0 (hK hζ₁K)))
  have hθK : ∀ ζ ∈ closedBall ζ₀ r, |ζ.arg| ≤ θ₀ := fun ζ hζ => hmax hζ
  obtain ⟨D, hD⟩ := hω (Real.pi / 2 - θ₀) (by linarith)
  set F : ℂ → ℝ → ℂ := fun ζ t => w t * cexp (-(I * t) * Complex.log ζ) with hF
  set F' : ℂ → ℝ → ℂ := fun ζ t => w t * (cexp (-(I * t) * Complex.log ζ) * (-(I * t) * ζ⁻¹))
    with hF'
  have hball : ball ζ₀ r ∈ 𝓝 ζ₀ := ball_mem_nhds ζ₀ hr0
  have hmeasF : ∀ᶠ ζ in 𝓝 ζ₀, AEStronglyMeasurable (F ζ) volume :=
    Filter.Eventually.of_forall fun ζ => hwm.mul (by fun_prop : Continuous fun t : ℝ =>
      cexp (-(I * t) * Complex.log ζ)).aestronglyMeasurable
  have hintF : Integrable (F ζ₀) := integrable_logFourier_integrand hω hwm hint hζ₀
  have hmeasF' : AEStronglyMeasurable (F' ζ₀) volume :=
    hwm.mul (by fun_prop : Continuous fun t : ℝ =>
      cexp (-(I * t) * Complex.log ζ₀) * (-(I * t) * ζ₀⁻¹)).aestronglyMeasurable
  set bound : ℝ → ℝ := fun t => ‖w t‖ * ω t * D / r with hbound
  have hbd : ∀ᵐ t ∂volume, ∀ ζ ∈ ball ζ₀ r, ‖F' ζ t‖ ≤ bound t := by
    filter_upwards with t ζ hζ
    have hζK : ζ ∈ closedBall ζ₀ r := ball_subset_closedBall hζ
    have hre : r ≤ ζ.re := hK hζK
    have hnorm : r ≤ ‖ζ‖ := hre.trans (Complex.re_le_norm ζ)
    have hζ0 : 0 < ‖ζ‖ := lt_of_lt_of_le hr0 hnorm
    simp only [hF', norm_mul, norm_neg, norm_inv, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have he := norm_cexp_log_le_of_abs_arg_le (hθK ζ hζK) t
    have hkey := hD t
    rw [show Real.pi / 2 - (Real.pi / 2 - θ₀) = θ₀ by ring] at hkey
    have hkey' : |t| * Real.exp (θ₀ * |t|) ≤ ω t * D := by
      have := Real.exp_pos (θ₀ * |t|)
      nlinarith
    have hw0 := norm_nonneg (w t)
    calc ‖w t‖ * (‖cexp (-(I * ↑t) * Complex.log ζ)‖ * (|t| * ‖ζ‖⁻¹))
        ≤ ‖w t‖ * (Real.exp (θ₀ * |t|) * (|t| * r⁻¹)) := by
          gcongr
      _ = ‖w t‖ * (|t| * Real.exp (θ₀ * |t|)) / r := by field_simp
      _ ≤ ‖w t‖ * (ω t * D) / r := by gcongr
      _ = bound t := by simp only [hbound]; ring
  have hintb : Integrable bound := ((hint.mul_const D).div_const r)
  have hderiv : ∀ᵐ t ∂volume, ∀ ζ ∈ ball ζ₀ r, HasDerivAt (fun ζ => F ζ t) (F' ζ t) ζ := by
    filter_upwards with t ζ hζ
    have hlog := Complex.hasDerivAt_log (hslit ζ (ball_subset_closedBall hζ))
    have := ((hlog.const_mul (-(I * (t : ℂ)))).cexp).const_mul (w t)
    simpa [hF, hF', mul_comm, mul_assoc, mul_left_comm] using this
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hmeasF hintF hmeasF' hbd hintb
    hderiv
  exact this.2.differentiableAt

theorem analyticOnNhd_logFourier {ω : ℝ → ℝ} (hω : DominatesSubcritical ω)
    (hwm : AEStronglyMeasurable w volume) (hint : Integrable fun t => ‖w t‖ * ω t) :
    AnalyticOnNhd ℂ (logFourier w) rightHalf := by
  have hd : DifferentiableOn ℂ (logFourier w) rightHalf := fun ζ hζ =>
    (differentiableAt_logFourier hω hwm hint hζ).differentiableWithinAt
  exact hd.analyticOnNhd isOpen_rightHalf

theorem norm_logFourier_le (hwexp : Integrable fun t => ‖w t‖ * Real.exp (Real.pi / 2 * |t|))
    {ζ : ℂ} (hζ : 0 < ζ.re) :
    ‖logFourier w ζ‖ ≤ ∫ t, ‖w t‖ * Real.exp (Real.pi / 2 * |t|) := by
  unfold logFourier
  refine norm_integral_le_of_norm_le hwexp ?_
  filter_upwards with t
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_log_le_of_abs_arg_le (abs_arg_le_of_re_pos hζ) t)
    (norm_nonneg _)

/-- **Growth at the boundary.**  `|G(ζ)| ≤ B e^{π/2} K (π/2 - |arg ζ|)^{-a}`. -/
theorem norm_logFourier_le_room {a K : ℝ} (hK : ∀ x : ℝ, 0 ≤ x → x ^ a * Real.exp (-x) ≤ K)
    (hroom : Integrable fun t => ‖w t‖ * roomWeight a t) {ζ : ℂ} (hζ : 0 < ζ.re) :
    ‖logFourier w ζ‖ ≤ (∫ t, ‖w t‖ * roomWeight a t) *
      (Real.exp (Real.pi / 2) * K * (Real.pi / 2 - |ζ.arg|) ^ (-a)) := by
  set η := Real.pi / 2 - |ζ.arg| with hη
  have hη0 : 0 < η := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζ); linarith
  have hηle : η ≤ Real.pi / 2 := by have := abs_nonneg ζ.arg; linarith
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 0 le_rfl)
  unfold logFourier
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hroom.mul_const _) ?_
  filter_upwards with t
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_cexp_log_le_of_abs_arg_le (a := Real.pi / 2 - η) (by rw [hη]; ring_nf; rfl) t).trans
    ((exp_le_roomWeight_mul hK hη0 t).trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (roomWeight_nonneg a t)
  have he : Real.exp η ≤ Real.exp (Real.pi / 2) := Real.exp_le_exp.mpr hηle
  have hηa : 0 ≤ η ^ (-a) := (Real.rpow_pos_of_pos hη0 _).le
  calc Real.exp η * η ^ (-a) * K ≤ Real.exp (Real.pi / 2) * η ^ (-a) * K := by gcongr
    _ = Real.exp (Real.pi / 2) * K * η ^ (-a) := by ring


theorem integrable_room_zero (hwexp : Integrable fun t => ‖w t‖ * Real.exp (Real.pi / 2 * |t|)) :
    Integrable fun t => ‖w t‖ * roomWeight 0 t := by
  simpa only [roomWeight_zero] using hwexp

theorem logFourier_natCast (n : ℕ) :
    logFourier w n = ∫ t, w t * cexp (-(I * t) * Real.log n) := by
  unfold logFourier
  rw [show Complex.log (n : ℂ) = (Real.log n : ℂ) by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]]

theorem fourier_eq_zero_of_eqOn (hG : EqOn (logFourier w) 0 rightHalf) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 := by
  have hx : ((Real.exp x : ℝ) : ℂ) ∈ rightHalf := by
    show 0 < ((Real.exp x : ℝ) : ℂ).re
    rw [Complex.ofReal_re]; exact Real.exp_pos x
  have := hG hx
  unfold logFourier at this
  rw [← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp] at this
  simpa using this

/-- **Prime-blind measures at the critical decay vanish.**  If `∫ |w| e^{(π/2)|t|} < ∞` and
`∫ w(t) n^{-it} dt = 0` for all `n` in a set `N ⊆ [2, ∞)` with `Σ_{n ∈ N} 1/n = ∞`, then the
Fourier transform `∫ w(t) e^{-itx} dt` vanishes for every real `x`. -/
theorem fourier_eq_zero_of_dirichletMoment_eq_zero (hwm : AEStronglyMeasurable w volume)
    (hwexp : Integrable fun t => ‖w t‖ * Real.exp (Real.pi / 2 * |t|)) {N : Set ℕ}
    (hN2 : ∀ n ∈ N, 2 ≤ n) (hdiv : ¬ Summable (N.indicator fun n : ℕ => (1 : ℝ) / n))
    (hmom : ∀ n ∈ N, ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 :=
  fourier_eq_zero_of_eqOn (eqOn_zero_of_halfPlane_zeros
    (analyticOnNhd_logFourier (dominatesSubcritical_roomWeight le_rfl) hwm
      (integrable_room_zero hwexp))
    (fun ζ hζ => norm_logFourier_le hwexp hζ) hN2 hdiv (fun n hn => by
      rw [logFourier_natCast]; exact hmom n hn)) x

/-- **The primes suffice.**  If `∫ |w| e^{(π/2)|t|} < ∞` and `∫ w(t) p^{-it} dt = 0` for every
prime `p`, the Fourier transform of `w` vanishes. -/
theorem fourier_eq_zero_of_primeMoment_eq_zero (hwm : AEStronglyMeasurable w volume)
    (hwexp : Integrable fun t => ‖w t‖ * Real.exp (Real.pi / 2 * |t|))
    (hmom : ∀ p : ℕ, p.Prime → ∫ t, w t * cexp (-(I * t) * Real.log p) = 0) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 :=
  fourier_eq_zero_of_dirichletMoment_eq_zero hwm hwexp (N := {p | p.Prime})
    (fun _ hp => hp.two_le) not_summable_one_div_on_primes hmom x

/-! ## Angles in shifted half-planes -/

/-- `Re ζ/|ζ| ≤ π/2 - |arg ζ|` on the right half-plane. -/
theorem re_div_norm_le_pi_div_two_sub_abs_arg {ζ : ℂ} (hζ : 0 < ζ.re) :
    ζ.re / ‖ζ‖ ≤ Real.pi / 2 - |ζ.arg| := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hθ : |ζ.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζ)
  have h1 : Real.cos ζ.arg ≤ Real.pi / 2 - |ζ.arg| := by
    have := Real.sin_le (show 0 ≤ Real.pi / 2 - |ζ.arg| by linarith)
    rwa [Real.sin_pi_div_two_sub, Real.cos_abs] at this
  rwa [Complex.cos_arg hζ0] at h1

/-- In the half-plane `Re ζ ≥ 1`, the angular distance to the imaginary axis is at least `1/|ζ|`. -/
theorem inv_norm_le_pi_div_two_sub_abs_arg {ζ : ℂ} (hζ : 1 ≤ ζ.re) :
    ‖ζ‖⁻¹ ≤ Real.pi / 2 - |ζ.arg| := by
  have hpos : 0 < ζ.re := by linarith
  have hn : 0 < ‖ζ‖ := lt_of_lt_of_le hpos (Complex.re_le_norm _)
  refine le_trans ?_ (re_div_norm_le_pi_div_two_sub_abs_arg hpos)
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hζ hn.le

/-- The right half-plane is preconnected. -/
theorem isPreconnected_rightHalf : IsPreconnected rightHalf :=
  (convex_halfSpace_re_gt 0).isPreconnected

/-- An analytic function on `Re ζ > 0` that vanishes on `Re ζ > c` vanishes identically. -/
theorem eqOn_rightHalf_of_eqOn_shift {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G rightHalf) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ ζ : ℂ, c < ζ.re → G ζ = 0) : EqOn G 0 rightHalf := by
  have hopen : IsOpen {ζ : ℂ | c < ζ.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((c + 1 : ℝ) : ℂ) ∈ rightHalf := by
    show 0 < ((c + 1 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith
  refine hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_rightHalf hmem ?_
  filter_upwards [hopen.mem_nhds (show c < ((c + 1 : ℝ) : ℂ).re by
    rw [Complex.ofReal_re]; linarith)] with ζ hζ
  exact h ζ hζ

/-! ## Every polynomial room, every divergent node set -/

/-- **Polynomial room never rescues blindness.**  If `∫ |w(t)| e^{(π/2)|t|} (1+|t|)^{-a} dt < ∞`
for some `a ≥ 0`, and `∫ w(t) n^{-it} dt = 0` for all `n` in a set `N ⊆ [2, ∞)` with
`Σ_{n ∈ N} 1/n = ∞` (for instance the primes), then the Fourier transform of `w` vanishes.

On `Re ζ ≥ 1` the angular distance to the imaginary axis is at least `1/|ζ|`, so `G(ζ + 1)`
grows at most like `|ζ + 1|^a`; dividing by `(ζ + 1)^{⌈a⌉}` leaves a bounded function vanishing at
`n - 1`, `n ∈ N`, and the Blaschke condition fails. -/
theorem fourier_eq_zero_of_dirichletMoment_eq_zero_room {a : ℝ} (ha0 : 0 ≤ a)
    (hwm : AEStronglyMeasurable w volume) (hroom : Integrable fun t => ‖w t‖ * roomWeight a t)
    {N : Set ℕ} (hdiv : ¬ Summable (N.indicator fun n : ℕ => (1 : ℝ) / n))
    (hmom : ∀ n ∈ N, ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_rpow_mul_exp_neg_le ha0
  have hG := analyticOnNhd_logFourier (dominatesSubcritical_roomWeight ha0) hwm hroom
  set p := ⌈a⌉₊ with hp
  set F : ℂ → ℂ := fun ξ => logFourier w (ξ + 1) / (ξ + 1) ^ p with hF
  have hre1 : ∀ ξ ∈ rightHalf, 1 ≤ (ξ + 1).re := fun ξ hξ => by
    have : 0 < ξ.re := hξ
    rw [Complex.add_re, Complex.one_re]; linarith
  have hshift : ∀ ξ ∈ rightHalf, ξ + 1 ∈ rightHalf := fun ξ hξ =>
    show 0 < (ξ + 1).re by linarith [hre1 ξ hξ]
  have hne : ∀ ξ ∈ rightHalf, ξ + 1 ≠ 0 := fun ξ hξ h => by
    have := hre1 ξ hξ; rw [h, Complex.zero_re] at this; linarith
  have hFan : AnalyticOnNhd ℂ F rightHalf := by
    intro ξ hξ
    have hadd : AnalyticAt ℂ (fun ξ : ℂ => ξ + 1) ξ := analyticAt_id.add analyticAt_const
    have h1 : AnalyticAt ℂ (fun ξ : ℂ => logFourier w (ξ + 1)) ξ :=
      AnalyticAt.comp (g := logFourier w) (f := fun ξ : ℂ => ξ + 1) (hG (ξ + 1) (hshift ξ hξ)) hadd
    exact h1.div (hadd.pow p) (pow_ne_zero _ (hne ξ hξ))
  set Bc := (∫ t, ‖w t‖ * roomWeight a t) * (Real.exp (Real.pi / 2) * K) with hBc
  have hBc0 : 0 ≤ Bc :=
    mul_nonneg (integral_nonneg fun t => mul_nonneg (norm_nonneg _) (roomWeight_nonneg a t))
      (by positivity)
  have hFb : ∀ ξ ∈ rightHalf, ‖F ξ‖ ≤ Bc := by
    intro ξ hξ
    have hgr := norm_logFourier_le_room hK hroom (hshift ξ hξ)
    have hn1 : 1 ≤ ‖ξ + 1‖ := (hre1 ξ hξ).trans (Complex.re_le_norm _)
    have hδ := inv_norm_le_pi_div_two_sub_abs_arg (hre1 ξ hξ)
    have hpow : (Real.pi / 2 - |(ξ + 1).arg|) ^ (-a) ≤ ‖ξ + 1‖ ^ a := by
      calc (Real.pi / 2 - |(ξ + 1).arg|) ^ (-a) ≤ (‖ξ + 1‖⁻¹) ^ (-a) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hδ (by linarith)
        _ = ‖ξ + 1‖ ^ a := by
            rw [Real.inv_rpow (norm_nonneg _), Real.rpow_neg (by positivity), inv_inv]
    have hpa : ‖ξ + 1‖ ^ a ≤ ‖ξ + 1‖ ^ p := by
      have := Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil a)
      rwa [Real.rpow_natCast] at this
    have hnp : 0 < ‖ξ + 1‖ ^ p := by positivity
    simp only [hF, norm_div, norm_pow]
    rw [div_le_iff₀ hnp]
    calc ‖logFourier w (ξ + 1)‖
        ≤ (∫ t, ‖w t‖ * roomWeight a t) *
            (Real.exp (Real.pi / 2) * K * (Real.pi / 2 - |(ξ + 1).arg|) ^ (-a)) := hgr
      _ = Bc * (Real.pi / 2 - |(ξ + 1).arg|) ^ (-a) := by rw [hBc]; ring
      _ ≤ Bc * ‖ξ + 1‖ ^ a := mul_le_mul_of_nonneg_left hpow hBc0
      _ ≤ Bc * ‖ξ + 1‖ ^ p := mul_le_mul_of_nonneg_left hpa hBc0
  -- the shifted nodes
  set N' : Set ℕ := {k | 2 ≤ k ∧ k + 1 ∈ N} with hN'
  have hFz : ∀ k ∈ N', F k = 0 := by
    intro k hk
    simp only [hF]
    have hcast : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, logFourier_natCast, hmom _ hk.2, zero_div]
  have hdiv' : ¬ Summable (N'.indicator fun n : ℕ => (1 : ℝ) / n) := by
    intro hs
    apply hdiv
    rw [← summable_nat_add_iff 1]
    have hfin : Summable fun n : ℕ => if n < 2 then (1 : ℝ) else 0 :=
      summable_of_ne_finset_zero (s := Finset.range 2) fun n hn => by
        rw [Finset.mem_range] at hn; simp [hn]
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hs.add hfin)
    · by_cases hn : n + 1 ∈ N
      · rw [Set.indicator_of_mem hn]; positivity
      · simp [hn]
    · by_cases h2 : n < 2
      · have h1 : N.indicator (fun n : ℕ => (1 : ℝ) / n) (n + 1) ≤ 1 := by
          by_cases hn : n + 1 ∈ N
          · rw [Set.indicator_of_mem hn, div_le_one (by positivity)]; push_cast; linarith
          · simp [hn]
        have h0 : 0 ≤ N'.indicator (fun n : ℕ => (1 : ℝ) / n) n := by
          by_cases hn : n ∈ N'
          · rw [Set.indicator_of_mem hn]; positivity
          · simp [hn]
        simp only [h2, if_true]; linarith
      · have hn2 : 2 ≤ n := by omega
        by_cases hn : n + 1 ∈ N
        · have hmem : n ∈ N' := ⟨hn2, hn⟩
          rw [Set.indicator_of_mem hn, Set.indicator_of_mem hmem]
          simp only [h2, if_false, add_zero]
          have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; push_cast; linarith
        · rw [Set.indicator_of_notMem hn]
          have h0 : 0 ≤ N'.indicator (fun n : ℕ => (1 : ℝ) / n) n := by
            by_cases hn' : n ∈ N'
            · rw [Set.indicator_of_mem hn']; positivity
            · simp [hn']
          simp only [h2, if_false, add_zero]; exact h0
  have hF0 := eqOn_zero_of_halfPlane_zeros hFan hFb (fun k hk => hk.1) hdiv' hFz
  refine fourier_eq_zero_of_eqOn (eqOn_rightHalf_of_eqOn_shift hG zero_le_one fun ζ hζ => ?_) x
  have hξ : ζ - 1 ∈ rightHalf := show 0 < (ζ - 1).re by
    rw [Complex.sub_re, Complex.one_re]; linarith
  have h := hF0 hξ
  simp only [hF, sub_add_cancel, Pi.zero_apply, div_eq_zero_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd h (pow_ne_zero _ (by simpa using hne _ hξ))

/-- **The primes, with polynomial room.**  If `∫ |w| e^{(π/2)|t|} (1+|t|)^{-a} < ∞` for some
`a ≥ 0` and `∫ w(t) p^{-it} dt = 0` for every prime `p`, the Fourier transform of `w` vanishes. -/
theorem fourier_eq_zero_of_primeMoment_eq_zero_room {a : ℝ} (ha0 : 0 ≤ a)
    (hwm : AEStronglyMeasurable w volume) (hroom : Integrable fun t => ‖w t‖ * roomWeight a t)
    (hmom : ∀ p : ℕ, p.Prime → ∫ t, w t * cexp (-(I * t) * Real.log p) = 0) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 :=
  fourier_eq_zero_of_dirichletMoment_eq_zero_room ha0 hwm hroom (N := {p | p.Prime})
    not_summable_one_div_on_primes hmom x

/-! ## Subexponential room on log-dense node sets -/


/-- `log((n+1)/(n-1)) ≥ 2/(n+1)` for `n ≥ 2`. -/
theorem two_div_succ_le_log_inv_discNode {n : ℕ} (hn : 2 ≤ n) :
    2 / ((n : ℝ) + 1) ≤ Real.log (‖discNode n‖⁻¹) := by
  rw [norm_discNode (by omega), inv_div]
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < ((n : ℝ) + 1) / ((n : ℝ) - 1) := div_pos (by linarith) (by linarith)
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  rw [inv_div] at hl
  have : 1 - ((n : ℝ) - 1) / ((n : ℝ) + 1) = 2 / ((n : ℝ) + 1) := by field_simp; ring
  linarith

/-- `Σ_{n=2}^{X} 1/(n+1) ≥ log((X+2)/3)`. -/
theorem log_le_sum_inv_succ (X : ℕ) (hX : 1 ≤ X) :
    Real.log (((X : ℝ) + 2) / 3) ≤ ∑ n ∈ Finset.Icc 2 X, 1 / ((n : ℝ) + 1) := by
  induction X, hX using Nat.le_induction with
  | base => norm_num
  | succ X hX ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hstep : Real.log (((X : ℝ) + 1 + 2) / 3) ≤
        Real.log (((X : ℝ) + 2) / 3) + 1 / ((X : ℝ) + 1 + 1) := by
      rw [← sub_le_iff_le_add', ← Real.log_div (by positivity) (by positivity)]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
      field_simp; ring
    push_cast
    linarith

/-! ## Circle averages of `1/|1 - z|` -/

theorem norm_one_sub_circleMap_sq (R θ : ℝ) :
    ‖1 - circleMap 0 R θ‖ ^ 2 = (1 - R) ^ 2 + 2 * R * (1 - Real.cos θ) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [circleMap, zero_add, Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
  linear_combination R ^ 2 * Real.sin_sq_add_cos_sq θ

theorem one_sub_cos_ge {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ≤ 2 * π) :
    2 / π ^ 2 * (min θ (2 * π - θ)) ^ 2 ≤ 1 - Real.cos θ := by
  rcases le_total θ π with h | h
  · have := Real.cos_le_one_sub_mul_cos_sq (x := θ) (by rw [abs_of_nonneg h0]; exact h)
    rw [min_eq_left (by linarith)]; linarith
  · have := Real.cos_le_one_sub_mul_cos_sq (x := θ - 2 * π)
      (by rw [abs_of_nonpos (by linarith)]; linarith)
    rw [Real.cos_sub_two_pi] at this
    rw [min_eq_right (by linarith), show (2 * π - θ) ^ 2 = (θ - 2 * π) ^ 2 by ring]
    linarith

/-- On the circle `|z| = R ≥ 1/2`: `1/|1 - z| ≤ π/(2(1-R) + θ) + π/(2(1-R) + 2π - θ)`. -/
theorem inv_norm_one_sub_circleMap_le {R θ : ℝ} (hR : 1 / 2 ≤ R) (hR1 : R < 1) (h0 : 0 ≤ θ)
    (h2 : θ ≤ 2 * π) :
    ‖1 - circleMap 0 R θ‖⁻¹ ≤ π / (2 * (1 - R) + θ) + π / (2 * (1 - R) + (2 * π - θ)) := by
  set u := min θ (2 * π - θ) with hu
  have hu0 : 0 ≤ u := le_min h0 (by linarith)
  have hπ := Real.pi_gt_three
  have hL0 : 0 < (2 * (1 - R) + u) / π := div_pos (by linarith) (by linarith)
  have hsq := norm_one_sub_circleMap_sq R θ
  have hcos := one_sub_cos_ge h0 h2
  have hL : (2 * (1 - R) + u) / π ≤ ‖1 - circleMap 0 R θ‖ := by
    refine (pow_le_pow_iff_left₀ hL0.le (norm_nonneg _) two_ne_zero).mp ?_
    rw [hsq, div_pow]
    have hπ2 : 9 < π ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have h1 : 2 * R * (1 - Real.cos θ) ≥ 2 / π ^ 2 * u ^ 2 := by
      have : 2 / π ^ 2 * u ^ 2 ≤ 2 * R * (2 / π ^ 2 * u ^ 2) := by
        have : 0 ≤ 2 / π ^ 2 * u ^ 2 := by positivity
        nlinarith
      nlinarith
    have h3 : 2 / π ^ 2 * u ^ 2 * π ^ 2 = 2 * u ^ 2 := by field_simp
    nlinarith [sq_nonneg (2 * (1 - R) - u)]
  have hinv : ‖1 - circleMap 0 R θ‖⁻¹ ≤ π / (2 * (1 - R) + u) := by
    rw [← inv_div]; exact inv_anti₀ hL0 hL
  refine hinv.trans ?_
  have hA : 0 ≤ π / (2 * (1 - R) + θ) := div_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ π / (2 * (1 - R) + (2 * π - θ)) := div_nonneg (by linarith) (by linarith)
  rcases min_choice θ (2 * π - θ) with h | h <;> rw [hu, h] <;> linarith

theorem integral_inv_shift {ε : ℝ} (hε : 0 < ε) :
    ∫ θ in (0 : ℝ)..2 * π, (ε + θ)⁻¹ = Real.log ((ε + 2 * π) / ε) := by
  have h := intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) ε (a := 0) (b := 2 * π)
  simp only [add_zero] at h
  rw [h, integral_inv_of_pos hε (by positivity)]

theorem integral_inv_shift_reflect {ε : ℝ} (hε : 0 < ε) :
    ∫ θ in (0 : ℝ)..2 * π, (ε + (2 * π - θ))⁻¹ = Real.log ((ε + 2 * π) / ε) := by
  have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) (ε + 2 * π)
    (a := 0) (b := 2 * π)
  simp only [sub_zero, add_sub_cancel_right] at h
  rw [show (fun θ : ℝ => (ε + (2 * π - θ))⁻¹) = fun θ => (ε + 2 * π - θ)⁻¹ by
    funext θ; ring_nf]
  rw [h, integral_inv_of_pos hε (by positivity)]

/-- **The circle average of `1/|1 - z|` grows logarithmically**:
`avg_{|z| = R} 1/|1 - z| ≤ log(1/(1-R)) + 4` for `1/2 ≤ R < 1`. -/
theorem circleAverage_inv_norm_one_sub_le {R : ℝ} (hR : 1 / 2 ≤ R) (hR1 : R < 1) :
    Real.circleAverage (fun z => ‖1 - z‖⁻¹) 0 R ≤ Real.log (1 / (1 - R)) + 4 := by
  set ε := 2 * (1 - R) with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hπ := Real.pi_gt_three
  have hne : ∀ θ : ℝ, 1 - circleMap 0 R θ ≠ 0 := by
    intro θ h
    have : circleMap 0 R θ = 1 := by linear_combination -h
    have hn := norm_circleMap_zero R θ
    rw [this, norm_one, abs_of_pos (by linarith)] at hn
    linarith
  have hi1 : IntervalIntegrable (fun θ => ‖1 - circleMap 0 R θ‖⁻¹) volume 0 (2 * π) := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact Continuous.inv₀ (continuous_const.sub (continuous_circleMap 0 R)).norm
      fun θ => norm_ne_zero_iff.mpr (hne θ)
  have hcA : ContinuousOn (fun θ : ℝ => π / (ε + θ)) (uIcc 0 (2 * π)) := by
    refine continuousOn_const.div (continuousOn_const.add continuousOn_id) fun θ hθ => ?_
    rw [uIcc_of_le (by positivity)] at hθ; linarith [hθ.1]
  have hcB : ContinuousOn (fun θ : ℝ => π / (ε + (2 * π - θ))) (uIcc 0 (2 * π)) := by
    refine continuousOn_const.div (continuousOn_const.add (continuousOn_const.sub continuousOn_id))
      fun θ hθ => ?_
    rw [uIcc_of_le (by positivity)] at hθ; linarith [hθ.2]
  have hi2 : IntervalIntegrable (fun θ => π / (ε + θ) + π / (ε + (2 * π - θ))) volume 0 (2 * π) :=
    (hcA.intervalIntegrable).add (hcB.intervalIntegrable)
  have hmono := intervalIntegral.integral_mono_on Real.two_pi_pos.le hi1 hi2 fun θ hθ =>
    inv_norm_one_sub_circleMap_le hR hR1 hθ.1 hθ.2
  have hI : ∫ θ in (0 : ℝ)..2 * π, (π / (ε + θ) + π / (ε + (2 * π - θ))) =
      2 * π * Real.log ((ε + 2 * π) / ε) := by
    rw [intervalIntegral.integral_add hcA.intervalIntegrable hcB.intervalIntegrable]
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_inv_shift hε0, integral_inv_shift_reflect hε0, ← div_eq_mul_inv]
    ring
  have hlog : Real.log ((ε + 2 * π) / ε) ≤ Real.log (1 / (1 - R)) + 4 := by
    have h1R : 0 < 1 - R := by linarith
    have heq : (ε + 2 * π) / ε = (1 - R + π) * (1 / (1 - R)) := by
      rw [hε]; field_simp
    rw [heq, Real.log_mul (by linarith) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 - R + π by linarith)
    linarith [Real.pi_le_four]
  rw [Real.circleAverage_def, smul_eq_mul]
  calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖1 - circleMap 0 R θ‖⁻¹
      ≤ (2 * π)⁻¹ * (2 * π * Real.log ((ε + 2 * π) / ε)) :=
        mul_le_mul_of_nonneg_left (hmono.trans hI.le) (by positivity)
    _ = Real.log ((ε + 2 * π) / ε) := by field_simp
    _ ≤ _ := hlog

/-- A pointwise bound `log |f| ≤ A + D/|1 - z|` on `|z| = R` bounds the circle average of
`log |f|` by `A + D (log(1/(1-R)) + 4)`. -/
theorem circleAverage_log_norm_le_of_le {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    {A D R : ℝ} (hD : 0 ≤ D) (hR : 1 / 2 ≤ R) (hR1 : R < 1)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, Real.log ‖f z‖ ≤ A + D * ‖1 - z‖⁻¹) :
    Real.circleAverage (fun z => Real.log ‖f z‖) 0 R ≤
      A + D * (Real.log (1 / (1 - R)) + 4) := by
  have hR0 : 0 < R := by linarith
  have hRabs : |R| = R := abs_of_pos hR0
  have hsph : sphere (0 : ℂ) |R| ⊆ ball 0 1 := by
    rw [hRabs]; exact sphere_subset_ball hR1
  have hcf : CircleIntegrable (fun z => Real.log ‖f z‖) 0 R :=
    (hf.mono hsph).meromorphicOn.circleIntegrable_log_norm
  have hcg : CircleIntegrable (fun z : ℂ => ‖1 - z‖⁻¹) 0 R := by
    refine ContinuousOn.circleIntegrable hR0.le ?_
    refine ContinuousOn.inv₀ (f := fun z : ℂ => ‖1 - z‖) (by fun_prop) fun z hz => ?_
    rw [mem_sphere_zero_iff_norm] at hz
    refine norm_ne_zero_iff.mpr fun h => ?_
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz; linarith
  have hsum : (fun z : ℂ => A + D * ‖1 - z‖⁻¹) = (fun _ => A) + D • (fun z : ℂ => ‖1 - z‖⁻¹) := by
    funext z; simp [smul_eq_mul]
  have hcs : CircleIntegrable (fun z : ℂ => A + D * ‖1 - z‖⁻¹) 0 R := by
    rw [hsum]; exact (circleIntegrable_const A 0 R).add (hcg.const_smul)
  have hmono := Real.circleAverage_mono hcf hcs fun z hz => hb z (by rwa [hRabs] at hz)
  have havg : Real.circleAverage (fun z : ℂ => A + D * ‖1 - z‖⁻¹) 0 R =
      A + D * Real.circleAverage (fun z : ℂ => ‖1 - z‖⁻¹) 0 R := by
    rw [hsum, Real.circleAverage_add (circleIntegrable_const A 0 R) hcg.const_smul,
      Real.circleAverage_const, Real.circleAverage_smul, smul_eq_mul]
  rw [havg] at hmono
  have := circleAverage_inv_norm_one_sub_le hR hR1
  have := mul_le_mul_of_nonneg_left this hD
  linarith

/-! ## Rigidity from logarithmic circle averages -/

/-- **Rigidity on the disc.**  Let `f` be analytic on the unit disc with
`avg_{|z| = R} log |f| ≤ B + D log(1/(1-R))` for `1/2 ≤ R < 1`, vanishing at `(n-1)/(n+1)` for every
`n` in a set `N ⊆ [2, ∞)` of logarithmic density `κ`:
`Σ_{n ∈ N, 2 ≤ n ≤ X} 1/(n+1) ≥ κ log X - C₀`.  If `0 ≤ D < 2κ` then `f ≡ 0`. -/
theorem eqOn_zero_of_discNode_zeros_density {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    {B D κ C₀ : ℝ} (hD0 : 0 ≤ D) (hκ : D < 2 * κ) {N : Set ℕ} [DecidablePred (· ∈ N)]
    (hdens : ∀ X : ℕ, 2 ≤ X →
      κ * Real.log X - C₀ ≤ ∑ n ∈ (Finset.Icc 2 X).filter (· ∈ N), 1 / ((n : ℝ) + 1))
    (havg : ∀ R : ℝ, 1 / 2 ≤ R → R < 1 →
      Real.circleAverage (fun z => Real.log ‖f z‖) 0 R ≤ B + D * Real.log (1 / (1 - R)))
    (hz : ∀ n ∈ N, f (discNode n) = 0) : EqOn f 0 (ball 0 1) := by
  by_contra hne
  have hconn : IsConnected (ball (0 : ℂ) 1) := (convex_ball 0 1).isConnected (by simp)
  obtain ⟨z₀, hz₀, hfz₀⟩ : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0 := by
    by_contra h; push Not at h; exact hne fun z hz => h z hz
  have hord : ∀ u ∈ ball (0 : ℂ) 1, analyticOrderAt f u ≠ ⊤ := by
    have h0 : analyticOrderAt f z₀ ≠ ⊤ := by
      rw [(hf z₀ hz₀).analyticOrderAt_eq_zero.mpr hfz₀]; exact ENat.zero_ne_top
    intro u hu
    exact (hf.exists_analyticOrderAt_ne_top_iff_forall hconn).mp ⟨⟨z₀, hz₀⟩, h0⟩ ⟨u, hu⟩
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hord 0 h0ball)
  set Q := B + k * Real.log 3 - Real.log ‖meromorphicTrailingCoeffAt f 0‖ + 2 + 2 * C₀ with hQ
  have hlim : Tendsto (fun X : ℕ => (2 * κ - D) * Real.log X) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by linarith)
  obtain ⟨X, hXbig, hX3⟩ := ((hlim.eventually (eventually_gt_atTop Q)).and
    (eventually_ge_atTop 3)).exists
  have hX1 : (3 : ℝ) ≤ X := by exact_mod_cast hX3
  set R : ℝ := ((X : ℝ) - 1) / ((X : ℝ) + 1) with hR
  have hR0 : 0 < R := div_pos (by linarith) (by linarith)
  have hR1 : R < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hRhalf : 1 / 2 ≤ R := by rw [hR, le_div_iff₀ (by linarith)]; linarith
  have hRabs : |R| = R := abs_of_pos hR0
  -- zeros up to level `X`
  set S := (Finset.Icc 2 X).filter (· ∈ N) with hS
  have hSmem : ∀ n ∈ S, 2 ≤ n ∧ n ≤ X ∧ n ∈ N := fun n hn => by
    rw [Finset.mem_filter, Finset.mem_Icc] at hn; exact ⟨hn.1.1, hn.1.2, hn.2⟩
  have hT : ∀ u ∈ S.image discNode, ‖u‖ ≤ R ∧ u ≠ 0 ∧ f u = 0 := by
    intro u hu
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hn2, hnX, hnN⟩ := hSmem n hn
    refine ⟨?_, discNode_ne_zero hn2, hz n hnN⟩
    rw [norm_discNode (by omega), hR, div_le_div_iff₀ (by positivity) (by linarith)]
    have : (n : ℝ) ≤ X := by exact_mod_cast hnX
    nlinarith
  have hJ := sum_log_le_of_circleAverage_le hf hord hR0 hR1 (havg R hRhalf hR1) _ hT
  have hcb : closedBall (0 : ℂ) |R| ⊆ ball 0 1 := by
    rw [hRabs]; exact closedBall_subset_ball hR1
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hf.mono hcb) (by simp), ← hk,
    Finset.sum_image (fun a _ b _ h => discNode_injective h)] at hJ
  simp only [ENat.map_coe, WithTop.untop₀_coe, Int.cast_natCast] at hJ
  have hsplit : ∑ n ∈ S, Real.log (R * ‖discNode n‖⁻¹) =
      S.card * Real.log R + ∑ n ∈ S, Real.log (‖discNode n‖⁻¹) := by
    rw [Finset.sum_congr rfl (fun n hn => Real.log_mul hR0.ne'
      (inv_ne_zero (norm_ne_zero_iff.mpr (discNode_ne_zero (hSmem n hn).1)))),
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hsplit] at hJ
  -- elementary estimates
  have hcard : (S.card : ℝ) ≤ (X : ℝ) - 1 := by
    have h1 : S.card ≤ (Finset.Icc 2 X).card := Finset.card_filter_le _ _
    rw [Nat.card_Icc] at h1
    have : (S.card : ℝ) ≤ ((X + 1 - 2 : ℕ) : ℝ) := by exact_mod_cast h1
    rw [show X + 1 - 2 = X - 1 by omega, Nat.cast_sub (by omega : 1 ≤ X)] at this
    simpa using this
  have hlogR : -(2 : ℝ) ≤ S.card * Real.log R := by
    have h := Real.add_one_le_exp (2 / ((X : ℝ) - 1))
    have hpos : 0 < (X : ℝ) - 1 := by linarith
    have hlog : Real.log (((X : ℝ) + 1) / ((X : ℝ) - 1)) ≤ 2 / ((X : ℝ) - 1) := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      refine le_trans (le_of_eq ?_) h
      field_simp; ring
    have hRl : Real.log R = -Real.log (((X : ℝ) + 1) / ((X : ℝ) - 1)) := by
      rw [hR, ← Real.log_inv, inv_div]
    have h2 : -(2 : ℝ) ≤ ((X : ℝ) - 1) * Real.log R := by
      rw [hRl]
      have := mul_le_mul_of_nonneg_left hlog hpos.le
      rw [mul_div_cancel₀ _ hpos.ne'] at this
      linarith
    have hlogR0 : Real.log R ≤ 0 := Real.log_nonpos hR0.le hR1.le
    nlinarith
  have hsum : 2 * (κ * Real.log X - C₀) ≤ ∑ n ∈ S, Real.log (‖discNode n‖⁻¹) := by
    calc 2 * (κ * Real.log X - C₀) ≤ 2 * ∑ n ∈ S, 1 / ((n : ℝ) + 1) := by
          have := hdens X (by omega); linarith
      _ = ∑ n ∈ S, 2 / ((n : ℝ) + 1) := by rw [Finset.mul_sum]; congr 1; ext n; ring
      _ ≤ _ := Finset.sum_le_sum fun n hn => two_div_succ_le_log_inv_discNode (hSmem n hn).1
  have hkR : -((k : ℝ) * Real.log R) ≤ k * Real.log 3 := by
    have h1 : -Real.log R ≤ Real.log 3 := by
      rw [← Real.log_inv, hR, inv_div]
      refine Real.log_le_log (div_pos (by linarith) (by linarith)) ?_
      rw [div_le_iff₀ (by linarith)]; linarith
    have := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
    linarith
  have hDlog : D * Real.log (1 / (1 - R)) ≤ D * Real.log X := by
    refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) hD0
    · have : 0 < 1 - R := by linarith
      positivity
    · rw [show 1 - R = 2 / ((X : ℝ) + 1) by rw [hR]; field_simp; ring, one_div_div,
        div_le_iff₀ (by norm_num)]
      linarith
  have hfinal : (2 * κ - D) * Real.log X ≤ Q := by
    simp only [hQ]; nlinarith
  exact absurd hfinal (not_le.mpr hXbig)

/-- Logarithmic density survives a shift of the node set: if `N` has density `κ`, so does
`{k ≥ 2 : k + m ∈ N}`, with the constant `C₀ + m`. -/
theorem density_shift {κ C₀ : ℝ} {N : Set ℕ} [DecidablePred (· ∈ N)] (m : ℕ)
    (hdens : ∀ X : ℕ, 2 ≤ X →
      κ * Real.log X - C₀ ≤ ∑ n ∈ (Finset.Icc 2 X).filter (· ∈ N), 1 / ((n : ℝ) + 1))
    (X : ℕ) (hX : 2 ≤ X) :
    κ * Real.log X - (C₀ + m) ≤
      ∑ k ∈ (Finset.Icc 2 X).filter (fun k => 2 ≤ k ∧ k + m ∈ N), 1 / ((k : ℝ) + 1) := by
  have h := hdens X hX
  set S := (Finset.Icc 2 X).filter (· ∈ N) with hS
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun n => n < m + 2)
    (fun n => 1 / ((n : ℝ) + 1))
  have hlow : ∑ n ∈ S.filter (fun n => n < m + 2), 1 / ((n : ℝ) + 1) ≤ m := by
    have hsub : S.filter (fun n => n < m + 2) ⊆ Finset.Icc 2 (m + 1) := by
      intro n hn
      simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega
    calc ∑ n ∈ S.filter (fun n => n < m + 2), 1 / ((n : ℝ) + 1)
        ≤ ∑ n ∈ S.filter (fun n => n < m + 2), (1 : ℝ) := Finset.sum_le_sum fun n _ => by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      _ = (S.filter (fun n => n < m + 2)).card := by simp
      _ ≤ (Finset.Icc 2 (m + 1)).card := by exact_mod_cast Finset.card_le_card hsub
      _ = m := by rw [Nat.card_Icc]; push_cast; ring_nf
  have hhigh : ∑ n ∈ S.filter (fun n => ¬ n < m + 2), 1 / ((n : ℝ) + 1) ≤
      ∑ k ∈ (Finset.Icc 2 X).filter (fun k => 2 ≤ k ∧ k + m ∈ N), 1 / ((k : ℝ) + 1) := by
    set T := S.filter (fun n => ¬ n < m + 2) with hT
    have hTmem : ∀ n ∈ T, m + 2 ≤ n ∧ n ≤ X ∧ n ∈ N := fun n hn => by
      simp only [hT, hS, Finset.mem_filter, Finset.mem_Icc] at hn
      exact ⟨by omega, hn.1.1.2, hn.1.2⟩
    have hinj : Set.InjOn (fun n => n - m) (T : Set ℕ) := by
      intro a ha b hb hab
      have := (hTmem a ha).1; have := (hTmem b hb).1
      simp only at hab; omega
    have hsubset : T.image (fun n => n - m) ⊆
        (Finset.Icc 2 X).filter (fun k => 2 ≤ k ∧ k + m ∈ N) := by
      intro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨h1, h2, h3⟩ := hTmem n hn
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
      rwa [Nat.sub_add_cancel (by omega)]
    calc ∑ n ∈ T, 1 / ((n : ℝ) + 1) ≤ ∑ n ∈ T, 1 / (((n - m : ℕ) : ℝ) + 1) :=
          Finset.sum_le_sum fun n _ => one_div_le_one_div_of_le (by positivity)
            (by have : ((n - m : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n m
                linarith)
      _ = ∑ k ∈ T.image (fun n => n - m), 1 / ((k : ℝ) + 1) :=
        (Finset.sum_image (f := fun k : ℕ => 1 / ((k : ℝ) + 1)) hinj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
  linarith

/-- The critical weight with subexponential room `K`: `e^{(π/2)|t| - K√|t|}`. -/
def sqrtRoomWeight (K t : ℝ) : ℝ := Real.exp (Real.pi / 2 * |t| - K * Real.sqrt |t|)

theorem sqrtRoomWeight_nonneg (K t : ℝ) : 0 ≤ sqrtRoomWeight K t := (Real.exp_pos _).le

/-- `K s - δ s² ≤ K²/(4δ)`. -/
theorem mul_sub_mul_sq_le {K δ s : ℝ} (hδ : 0 < δ) : K * s - δ * s ^ 2 ≤ K ^ 2 / (4 * δ) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * δ * s - K)]

theorem dominatesSubcritical_sqrtRoomWeight (K : ℝ) :
    DominatesSubcritical (sqrtRoomWeight K) := by
  intro c hc
  obtain ⟨K₁, -, hK₁⟩ := exists_rpow_mul_exp_neg_le (b := 1) zero_le_one
  refine ⟨Real.exp (K ^ 2 / (2 * c)) * (Real.exp (c / 2) * (c / 2) ^ (-(1 : ℝ)) * K₁),
    fun t => ?_⟩
  have hs : 0 ≤ |t| := abs_nonneg t
  have hkey := one_add_rpow_mul_exp_neg_le hK₁ (half_pos hc) hs
  rw [Real.rpow_one] at hkey
  have hsq : K * Real.sqrt |t| ≤ K ^ 2 / (2 * c) + c / 2 * |t| := by
    rw [show K ^ 2 / (2 * c) + c / 2 * |t| = (K ^ 2 + c ^ 2 * |t|) / (2 * c) by
      field_simp, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (c * Real.sqrt |t| - K), Real.sq_sqrt hs]
  have heq : (1 + |t|) * Real.exp ((Real.pi / 2 - c) * |t|) =
      sqrtRoomWeight K t * ((1 + |t|) * Real.exp (K * Real.sqrt |t| - c * |t|)) := by
    unfold sqrtRoomWeight
    rw [show (Real.pi / 2 - c) * |t| =
      (Real.pi / 2 * |t| - K * Real.sqrt |t|) + (K * Real.sqrt |t| - c * |t|) by ring,
      Real.exp_add]
    ring
  rw [heq]
  refine mul_le_mul_of_nonneg_left ?_ (sqrtRoomWeight_nonneg K t)
  calc (1 + |t|) * Real.exp (K * Real.sqrt |t| - c * |t|)
      ≤ (1 + |t|) * (Real.exp (K ^ 2 / (2 * c)) * Real.exp (-(c / 2 * |t|))) := by
        rw [← Real.exp_add]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by linarith)
    _ = Real.exp (K ^ 2 / (2 * c)) * ((1 + |t|) * Real.exp (-(c / 2 * |t|))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le

/-- **Growth with subexponential room.**  `|G(ζ)| ≤ B e^{K²/(4(π/2 - |arg ζ|))}`. -/
theorem norm_logFourier_le_sqrtRoom {K : ℝ}
    (hroom : Integrable fun t => ‖w t‖ * sqrtRoomWeight K t) {ζ : ℂ} (hζ : 0 < ζ.re) :
    ‖logFourier w ζ‖ ≤ (∫ t, ‖w t‖ * sqrtRoomWeight K t) *
      Real.exp (K ^ 2 / (4 * (Real.pi / 2 - |ζ.arg|))) := by
  set η := Real.pi / 2 - |ζ.arg| with hη
  have hη0 : 0 < η := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hζ); linarith
  unfold logFourier
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hroom.mul_const _) ?_
  filter_upwards with t
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_cexp_log_le_of_abs_arg_le (a := Real.pi / 2 - η) (by rw [hη]; ring_nf; rfl) t).trans
    ?_
  unfold sqrtRoomWeight
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h := mul_sub_mul_sq_le (K := K) (s := Real.sqrt |t|) hη0
  rw [Real.sq_sqrt (abs_nonneg t)] at h
  linarith

/-- The growth of `G(m + cayley z)` on the disc under subexponential room:
`|G(m + cayley z)| ≤ B e^{K²/4 + (K²/(2m))/|1 - z|}`. -/
theorem norm_logFourier_shift_cayley_le {K : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hroom : Integrable fun t => ‖w t‖ * sqrtRoomWeight K t) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖logFourier w ((m : ℂ) + cayley z)‖ ≤ (∫ t, ‖w t‖ * sqrtRoomWeight K t) *
      Real.exp (K ^ 2 / 4 + K ^ 2 / (2 * m) * ‖1 - z‖⁻¹) := by
  set ζ := (m : ℂ) + cayley z with hζ
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcre := re_cayley_pos hz
  have hre : (m : ℝ) ≤ ζ.re := by
    rw [hζ, Complex.add_re, Complex.natCast_re]; linarith
  have hre0 : 0 < ζ.re := by linarith
  have hB0 : 0 ≤ ∫ t, ‖w t‖ * sqrtRoomWeight K t :=
    integral_nonneg fun t => mul_nonneg (norm_nonneg _) (sqrtRoomWeight_nonneg K t)
  refine (norm_logFourier_le_sqrtRoom hroom hre0).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB0)
  set δ := Real.pi / 2 - |ζ.arg| with hδ
  have hnζ : 0 < ‖ζ‖ := lt_of_lt_of_le hre0 (Complex.re_le_norm _)
  have hmδ : (m : ℝ) / ‖ζ‖ ≤ δ :=
    le_trans (div_le_div_of_nonneg_right hre hnζ.le) (re_div_norm_le_pi_div_two_sub_abs_arg hre0)
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hmδ
  have hinv : δ⁻¹ ≤ ‖ζ‖ / m := by
    rw [← inv_div]; exact inv_anti₀ (by positivity) hmδ
  -- `|ζ| ≤ m + 2/|1 - z|`
  have hne := one_sub_ne_zero_of_norm_lt hz
  have hn1 : 0 < ‖1 - z‖ := norm_pos_iff.mpr hne
  have hcay : ‖cayley z‖ ≤ 2 * ‖1 - z‖⁻¹ := by
    rw [cayley, norm_div, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have hnorm : ‖ζ‖ ≤ m + 2 * ‖1 - z‖⁻¹ := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_natCast]; linarith
  have hK2 : 0 ≤ K ^ 2 / 4 := by positivity
  calc K ^ 2 / (4 * δ) = K ^ 2 / 4 * δ⁻¹ := by field_simp
    _ ≤ K ^ 2 / 4 * (‖ζ‖ / m) := mul_le_mul_of_nonneg_left hinv hK2
    _ ≤ K ^ 2 / 4 * ((m + 2 * ‖1 - z‖⁻¹) / m) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnorm (by positivity)) hK2
    _ = K ^ 2 / 4 + K ^ 2 / (2 * m) * ‖1 - z‖⁻¹ := by field_simp; ring

/-- **Carlson's threshold for log-dense node sets.**  If
`∫ |w(t)| e^{(π/2)|t| - K√|t|} dt < ∞` for some `K`, and `∫ w(t) n^{-it} dt = 0` for every `n` in a
set `N` of positive logarithmic density `κ`, then the Fourier transform of `w` vanishes.

Shift by an integer `m > K²/(4κ)` and use `ζ = m + (1+z)/(1-z)`: then
`log |G(ζ)| ≤ C + (K²/(2m))/|1 - z|`, whose circle averages grow like `(K²/(2m)) log(1/(1-R))`,
while the zeros at the shifted nodes contribute `2κ log(1/(1-R))` to Jensen's formula. -/
theorem fourier_eq_zero_of_dirichletMoment_eq_zero_density {K κ C₀ : ℝ} (hκ : 0 < κ)
    {N : Set ℕ} [DecidablePred (· ∈ N)]
    (hdens : ∀ X : ℕ, 2 ≤ X →
      κ * Real.log X - C₀ ≤ ∑ n ∈ (Finset.Icc 2 X).filter (· ∈ N), 1 / ((n : ℝ) + 1))
    (hwm : AEStronglyMeasurable w volume)
    (hroom : Integrable fun t => ‖w t‖ * sqrtRoomWeight K t)
    (hmom : ∀ n ∈ N, ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 := by
  classical
  have hG := analyticOnNhd_logFourier (dominatesSubcritical_sqrtRoomWeight K) hwm hroom
  -- the shift
  set m : ℕ := ⌈K ^ 2 / (4 * κ)⌉₊ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmK : K ^ 2 / (4 * κ) < m := by
    have := Nat.le_ceil (K ^ 2 / (4 * κ))
    rw [hm]; push_cast; linarith
  set D := K ^ 2 / (2 * m) with hD
  have hD0 : 0 ≤ D := by positivity
  have hDκ : D < 2 * κ := by
    rw [hD, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hmK
    linarith
  -- the disc function
  set f : ℂ → ℂ := fun z => logFourier w ((m : ℂ) + cayley z) with hf
  have hmem : ∀ z : ℂ, ‖z‖ < 1 → (m : ℂ) + cayley z ∈ rightHalf := fun z hz => by
    show 0 < ((m : ℂ) + cayley z).re
    rw [Complex.add_re, Complex.natCast_re]; linarith [re_cayley_pos hz]
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := by
    intro z hz1
    have hz1' : ‖z‖ < 1 := by simpa using hz1
    have hc : AnalyticAt ℂ (fun z : ℂ => (m : ℂ) + cayley z) z :=
      analyticAt_const.add ((analyticAt_const.add analyticAt_id).div
        (analyticAt_const.sub analyticAt_id) (one_sub_ne_zero_of_norm_lt hz1'))
    exact AnalyticAt.comp (g := logFourier w) (f := fun z : ℂ => (m : ℂ) + cayley z)
      (hG _ (hmem z hz1')) hc
  -- the shifted nodes
  set N' : Set ℕ := {k | 2 ≤ k ∧ k + m ∈ N} with hN'
  have hfz : ∀ k ∈ N', f (discNode k) = 0 := by
    intro k hk
    simp only [hf, cayley_discNode]
    have hcast : ((m : ℂ) + k) = ((k + m : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, logFourier_natCast, hmom _ hk.2]
  have hdens' : ∀ X : ℕ, 2 ≤ X → κ * Real.log X - (C₀ + m) ≤
      ∑ n ∈ (Finset.Icc 2 X).filter (· ∈ N'), 1 / ((n : ℝ) + 1) :=
    fun X hX => density_shift m hdens X hX
  -- circle averages
  set A := max (∫ t, ‖w t‖ * sqrtRoomWeight K t) 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  have havg : ∀ R : ℝ, 1 / 2 ≤ R → R < 1 →
      Real.circleAverage (fun z => Real.log ‖f z‖) 0 R ≤
        (Real.log A + K ^ 2 / 4 + 4 * D) + D * Real.log (1 / (1 - R)) := by
    intro R hR hR1
    have h := circleAverage_log_norm_le_of_le hfan (A := Real.log A + K ^ 2 / 4) hD0 hR hR1
      (fun z hz => ?_)
    · linarith
    rw [mem_sphere_zero_iff_norm] at hz
    have hz1 : ‖z‖ < 1 := by rw [hz]; exact hR1
    have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
    have hrest : 0 ≤ K ^ 2 / 4 + D * ‖1 - z‖⁻¹ := by positivity
    rcases eq_or_ne (f z) 0 with h0 | h0
    · rw [h0, norm_zero, Real.log_zero]; linarith
    · have hb := norm_logFourier_shift_cayley_le hm1 hroom hz1
      have hb' : ‖f z‖ ≤ A * Real.exp (K ^ 2 / 4 + D * ‖1 - z‖⁻¹) :=
        hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      calc Real.log ‖f z‖ ≤ Real.log (A * Real.exp (K ^ 2 / 4 + D * ‖1 - z‖⁻¹)) :=
            Real.log_le_log (norm_pos_iff.mpr h0) hb'
        _ = Real.log A + K ^ 2 / 4 + D * ‖1 - z‖⁻¹ := by
            rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]; ring
  have hf0 := eqOn_zero_of_discNode_zeros_density hfan hD0 hDκ hdens' havg hfz
  refine fourier_eq_zero_of_eqOn (eqOn_rightHalf_of_eqOn_shift hG (c := m) (by positivity)
    fun ζ hζ => ?_) x
  have hξ : 0 < (ζ - m).re := by rw [Complex.sub_re, Complex.natCast_re]; linarith
  have hz : (ζ - m - 1) / (ζ - m + 1) ∈ ball (0 : ℂ) 1 := by
    simpa using norm_inverseCayley_lt hξ
  have h := hf0 hz
  simp only [hf, cayley_inverseCayley hξ, add_sub_cancel, Pi.zero_apply] at h
  exact h

/-- **Carlson's threshold at the integers.**  If `∫ |w(t)| e^{(π/2)|t| - K√|t|} dt < ∞` for some `K`
and `∫ w(t) n^{-it} dt = 0` for every integer `n ≥ 2`, the Fourier transform of `w` vanishes. -/
theorem fourier_eq_zero_of_integerMoment_eq_zero_room {K : ℝ}
    (hwm : AEStronglyMeasurable w volume)
    (hroom : Integrable fun t => ‖w t‖ * sqrtRoomWeight K t)
    (hmom : ∀ n : ℕ, 2 ≤ n → ∫ t, w t * cexp (-(I * t) * Real.log n) = 0) (x : ℝ) :
    ∫ t, w t * cexp (-(I * t) * x) = 0 := by
  classical
  refine fourier_eq_zero_of_dirichletMoment_eq_zero_density (κ := 1) (C₀ := Real.log 3) one_pos
    (N := {n | 2 ≤ n}) (fun X hX => ?_) hwm hroom (fun n hn => hmom n hn) x
  have hall : ∀ n ∈ Finset.Icc 2 X, n ∈ ({n | 2 ≤ n} : Set ℕ) :=
    fun n hn => (Finset.mem_Icc.mp hn).1
  rw [Finset.filter_true_of_mem hall]
  refine le_trans ?_ (log_le_sum_inv_succ X (by omega))
  have hX : (2 : ℝ) ≤ X := by exact_mod_cast hX
  rw [one_mul, Real.log_div (by positivity) (by norm_num)]
  have := Real.log_le_log (by positivity) (show (X : ℝ) ≤ X + 2 by linarith)
  linarith

end RHTower.PrimeBlindCarlson
