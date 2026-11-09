import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveTailFilters
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Infinite positive deletion of exponential tails

Square-summable shifts make the deletion multiplier converge at every fixed exponent.
A sufficiently late tail preserves any specified exponent. Finite positive averages
commute with absolutely convergent exponential series, with a bound independent of
how many factors have been used.
-/

open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Square summability makes every fixed exponent small relative to all late shifts. -/
theorem eventually_small_shift (h : ℕ → ℝ) (hsq : Summable fun i => h i ^ 2) (w : ℂ) :
    ∀ᶠ n : ℕ in atTop, |h n| * ‖w‖ ≤ 1 := by
  have ht := (hsq.mul_right (‖w‖ ^ 2)).tendsto_atTop_zero
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn
  have he : (|h n| * ‖w‖) ^ 2 = h n ^ 2 * ‖w‖ ^ 2 := by rw [mul_pow, sq_abs]
  have hp : 0 ≤ |h n| * ‖w‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  nlinarith only [he, hn, hp]

/-- The full multiplier converges even when a finite initial set of factors is large. -/
theorem multipliable_quartetFactor (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (w : ℂ) :
    Multipliable fun i => quartetFactor (a i) (h i) w := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_small_shift h hsq w)
  have hs : Summable fun i => ‖quartetFactor (a i) (h i) w - 1‖ := by
    apply (summable_nat_add_iff N).mp
    exact summable_quartetFactor_sub_one (fun i => a (i + N)) (fun i => h (i + N)) w
      ((summable_nat_add_iff N).mpr hsq) (fun i => hN (i + N) (Nat.le_add_left N i))
  have he : (fun i => 1 + (quartetFactor (a i) (h i) w - 1)) =
      fun i => quartetFactor (a i) (h i) w := by funext i; ring
  simpa only [he] using multipliable_one_add_of_summable hs

/-- Every fixed exponent survives deletion of a sufficiently late tail. -/
theorem exists_nonzero_tail_multiplier (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (w : ℂ) :
    ∃ N : ℕ, (∏' i : ℕ, quartetFactor (a (i + N)) (h (i + N)) w) ≠ 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_small_shift h hsq w)
  exact ⟨N, (multipliable_quartetFactor_ne_zero
    (fun i => a (i + N)) (fun i => h (i + N)) w
    ((summable_nat_add_iff N).mpr hsq) (fun i => hN (i + N) (Nat.le_add_left N i))).2⟩

theorem tailFactor_append (l r : List (ℝ × ℝ)) (w : ℂ) :
    tailFactor (l ++ r) w = tailFactor l w * tailFactor r w := by
  induction l with
  | nil => simp [tailFactor]
  | cons p l ih => simp only [List.cons_append, tailFactor, ih, mul_assoc]

/-- The first `N` factors of the deletion sequence. -/
def filterPrefix (a h : ℕ → ℝ) (N : ℕ) : List (ℝ × ℝ) :=
  (List.range N).map fun i => (a i, h i)

theorem tailFactor_filterPrefix (a h : ℕ → ℝ) (w : ℂ) (N : ℕ) :
    tailFactor (filterPrefix a h N) w = ∏ i ∈ Finset.range N, quartetFactor (a i) (h i) w := by
  induction N with
  | zero => simp [filterPrefix, tailFactor]
  | succ N ih =>
      simp only [filterPrefix, List.range_succ, List.map_append, List.map_cons,
        List.map_nil, tailFactor_append, tailFactor, mul_one, Finset.prod_range_succ] at *
      rw [ih]

theorem squareCost_append (l r : List (ℝ × ℝ)) :
    squareCost (l ++ r) = squareCost l + squareCost r := by
  simp [squareCost]

theorem squareCost_filterPrefix (a h : ℕ → ℝ) (N : ℕ) :
    squareCost (filterPrefix a h N) = ∑ i ∈ Finset.range N, h i ^ 2 := by
  induction N with
  | zero => simp [filterPrefix, squareCost]
  | succ N ih =>
      simp only [filterPrefix, List.range_succ, List.map_append, List.map_cons,
        List.map_nil, squareCost_append, Finset.sum_range_succ] at *
      rw [ih]
      simp [squareCost]

/-- Prefix multipliers converge at every exponent. -/
theorem tendsto_tailFactor (a h : ℕ → ℝ) (hsq : Summable fun i => h i ^ 2) (w : ℂ) :
    Tendsto (fun N => tailFactor (filterPrefix a h N) w) atTop
      (𝓝 (∏' i, quartetFactor (a i) (h i) w)) := by
  simpa only [tailFactor_filterPrefix] using
    (multipliable_quartetFactor a h hsq w).hasProd.tendsto_prod_nat

/-- One positive average commutes with an absolutely convergent real series. -/
theorem quartetAverage_tsum {ι : Type*} (a h : ℝ) (F : ι → ℝ → ℝ)
    (hF : ∀ u, Summable fun i => F i u) (t : ℝ) :
    Summable (fun i => quartetAverage a h (F i) t) ∧
      quartetAverage a h (fun u => ∑' i, F i u) t =
        ∑' i, quartetAverage a h (F i) t := by
  have hleft := (hF (t - h)).div_const 2
  have hmid := (hF t).mul_left (Real.cosh (h * a))
  have hright := (hF (t + h)).div_const 2
  refine ⟨((hleft.add hmid).add hright).div_const _, ?_⟩
  unfold quartetAverage
  rw [tsum_div_const, (hleft.add hmid).tsum_add hright, hleft.tsum_add hmid,
    tsum_div_const, tsum_mul_left, tsum_div_const]

theorem tailAverage_tsum {ι : Type*} (l : List (ℝ × ℝ)) (F : ι → ℝ → ℝ)
    (hF : ∀ u, Summable fun i => F i u) (t : ℝ) :
    Summable (fun i => tailAverage l (F i) t) ∧
      tailAverage l (fun u => ∑' i, F i u) t = ∑' i, tailAverage l (F i) t := by
  induction l generalizing t with
  | nil => exact ⟨hF t, rfl⟩
  | cons p l ih =>
      have hq := quartetAverage_tsum p.1 p.2 (fun i => tailAverage l (F i)) (fun u => (ih u).1) t
      refine ⟨hq.1, ?_⟩
      change quartetAverage p.1 p.2 (tailAverage l (fun u => ∑' i, F i u)) t = _
      rw [show tailAverage l (fun u => ∑' i, F i u) =
        fun u => ∑' i, tailAverage l (F i) u from funext fun u => (ih u).2]
      exact hq.2

/-- Real parts of complex exponential modes diagonalize each positive average. -/
theorem quartetAverage_cexp_re (a h : ℝ) (c w : ℂ) (t : ℝ) :
    quartetAverage a h (fun u => (c * Complex.exp (w * u)).re) t =
      (c * quartetFactor a h w * Complex.exp (w * t)).re := by
  have he : ((c * Complex.exp (w * ((t - h : ℝ) : ℂ))) / (2 : ℝ) +
        (Real.cosh (h * a) : ℂ) * (c * Complex.exp (w * t)) +
        (c * Complex.exp (w * ((t + h : ℝ) : ℂ))) / (2 : ℝ)) /
        ((1 + Real.cosh (h * a) : ℝ) : ℂ) =
      c * quartetFactor a h w * Complex.exp (w * t) := by
    have hl : w * ((t - h : ℝ) : ℂ) = w * t + -((h : ℂ) * w) := by push_cast; ring
    have hr : w * ((t + h : ℝ) : ℂ) = w * t + (h : ℂ) * w := by push_cast; ring
    rw [hl, hr, Complex.exp_add, Complex.exp_add, quartetFactor, Complex.cosh]
    push_cast
    ring
  have hre := congrArg Complex.re he
  simpa only [quartetAverage, Complex.add_re, Complex.div_ofReal_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hre

/-- A finite deletion multiplies each mode by the product of its factors. -/
theorem tailAverage_cexp_re (l : List (ℝ × ℝ)) (c w : ℂ) (t : ℝ) :
    tailAverage l (fun u => (c * Complex.exp (w * u)).re) t =
      (c * tailFactor l w * Complex.exp (w * t)).re := by
  induction l generalizing c t with
  | nil => simp [tailAverage, tailFactor]
  | cons p l ih =>
      rw [tailAverage, show tailAverage l (fun u => (c * Complex.exp (w * u)).re) =
        (fun u : ℝ => (c * tailFactor l w * Complex.exp (w * u)).re) from funext (ih c),
        quartetAverage_cexp_re, tailFactor]
      congr 1
      ring

/-- Every prefix spends at most the total square cost. -/
theorem squareCost_filterPrefix_le (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (N : ℕ) :
    squareCost (filterPrefix a h N) ≤ ∑' i, h i ^ 2 := by
  rw [squareCost_filterPrefix]
  exact Summable.sum_le_tsum (Finset.range N) (fun i _ => sq_nonneg _) hsq

private theorem norm_exp_le_strip {w : ℂ} {D : ℝ}
    (hw : |w.re| ≤ D) (t : ℝ) :
    ‖Complex.exp (w * t)‖ ≤ Real.exp (D * |t|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc w.re * t ≤ |w.re * t| := le_abs_self _
    _ = |w.re| * |t| := abs_mul _ _
    _ ≤ D * |t| := mul_le_mul_of_nonneg_right hw (abs_nonneg _)

/-- A summable coefficient sequence defines an absolutely convergent trace in a strip. -/
theorem summable_cexp_re {ι : Type*} (c w : ι → ℂ) {D : ℝ}
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D) (t : ℝ) :
    Summable fun i => (c i * Complex.exp (w i * t)).re := by
  apply Summable.of_norm_bounded (hc.mul_right (Real.exp (D * |t|)))
  intro i
  by_cases hi : c i = 0
  · simp [hi]
  calc ‖(c i * Complex.exp (w i * t)).re‖ ≤ ‖c i * Complex.exp (w i * t)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖c i‖ * Real.exp (D * |t|) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_exp_le_strip (hw i hi) t) (norm_nonneg _)

/-- A strip bound controls all filtered modes independently of the prefix length. -/
theorem norm_filtered_mode_le (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (c w : ℂ) {D : ℝ}
    (hw : |w.re| ≤ D) (t : ℝ) (N : ℕ) :
    ‖c * tailFactor (filterPrefix a h N) w * Complex.exp (w * t)‖ ≤
      ‖c‖ * (Real.exp (D ^ 2 * (∑' i, h i ^ 2) / 2) * Real.exp (D * |t|)) := by
  have hsqD : w.re ^ 2 ≤ D ^ 2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg w.re) hw
  have hm : ‖tailFactor (filterPrefix a h N) w‖ ≤
      Real.exp (D ^ 2 * (∑' i, h i ^ 2) / 2) := by
    apply (norm_tailFactor_le _ _).trans
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (mul_le_mul hsqD (squareCost_filterPrefix_le a h hsq N)
        (squareCost_nonneg _) (sq_nonneg _)) (by norm_num)
  rw [norm_mul, norm_mul, ← mul_assoc]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hm (norm_nonneg _))
    (norm_exp_le_strip hw t) (norm_nonneg _) (by positivity)

/-- Positive prefix averages converge termwise on every absolutely convergent strip trace. -/
theorem tendsto_tailAverage_series {ι : Type*} (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (c w : ι → ℂ) {D : ℝ}
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D) (t : ℝ) :
    Tendsto (fun N => tailAverage (filterPrefix a h N)
      (fun u => ∑' i, (c i * Complex.exp (w i * u)).re) t) atTop
      (𝓝 (∑' i, (c i * (∏' n, quartetFactor (a n) (h n) (w i)) *
        Complex.exp (w i * t)).re)) := by
  have he (N : ℕ) : tailAverage (filterPrefix a h N)
      (fun u => ∑' i, (c i * Complex.exp (w i * u)).re) t =
      ∑' i, (c i * tailFactor (filterPrefix a h N) (w i) * Complex.exp (w i * t)).re := by
    rw [(tailAverage_tsum _ _ (summable_cexp_re c w hc hw) t).2]
    simp only [tailAverage_cexp_re]
  simp_rw [he]
  apply tendsto_tsum_of_dominated_convergence
    (hc.mul_right (Real.exp (D ^ 2 * (∑' i, h i ^ 2) / 2) * Real.exp (D * |t|)))
  · intro i
    exact (Complex.continuous_re.tendsto _).comp
      ((tendsto_const_nhds.mul (tendsto_tailFactor a h hsq (w i))).mul tendsto_const_nhds)
  · apply Filter.Eventually.of_forall
    intro N i
    by_cases hi : c i = 0
    · simp [hi]
    exact (Complex.abs_re_le_norm _).trans
      (norm_filtered_mode_le a h hsq (c i) (w i) (hw i hi) t N)

/-- Once its own factor occurs, a prescribed exponent vanishes in every longer prefix. -/
theorem eventually_tailFactor_root (a h : ℕ → ℝ) (n : ℕ) {γ : ℝ}
    (hphase : h n * γ = Real.pi) :
    ∀ᶠ N in atTop, tailFactor (filterPrefix a h N) ((a n : ℂ) + (γ : ℂ) * I) = 0 := by
  filter_upwards [eventually_gt_atTop n] with N hN
  apply tailFactor_root _ _ hphase
  simp only [filterPrefix, List.mem_map]
  exact ⟨n, List.mem_range.mpr hN, rfl⟩

/-- The limiting multiplier deletes every exponent assigned a half-period factor. -/
theorem tprod_quartetFactor_root (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (n : ℕ) {γ : ℝ}
    (hphase : h n * γ = Real.pi) :
    (∏' i, quartetFactor (a i) (h i) ((a n : ℂ) + (γ : ℂ) * I)) = 0 := by
  have he : (fun _ : ℕ => (0 : ℂ)) =ᶠ[atTop]
      (fun N => tailFactor (filterPrefix a h N) ((a n : ℂ) + (γ : ℂ) * I)) :=
    (eventually_tailFactor_root a h n hphase).mono fun _ hn => hn.symm
  exact tendsto_nhds_unique (tendsto_tailFactor a h hsq _)
    (tendsto_const_nhds.congr' he)

/-- Deleting every exponent outside a finite set leaves exactly its filtered finite sum. -/
theorem tendsto_tailAverage_finite_head {ι : Type*} (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (c w : ι → ℂ) {D : ℝ}
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D)
    (S : Finset ι)
    (hdelete : ∀ i ∉ S, c i ≠ 0 → ∃ n, (w i).re = a n ∧ h n * (w i).im = Real.pi)
    (t : ℝ) :
    Tendsto (fun N => tailAverage (filterPrefix a h N)
      (fun u => ∑' i, (c i * Complex.exp (w i * u)).re) t) atTop
      (𝓝 (∑ i ∈ S, (c i * (∏' n, quartetFactor (a n) (h n) (w i)) *
        Complex.exp (w i * t)).re)) := by
  have hzero : ∀ i ∉ S, (c i * (∏' n, quartetFactor (a n) (h n) (w i)) *
      Complex.exp (w i * t)).re = 0 := by
    intro i hi
    by_cases hci : c i = 0
    · simp [hci]
    obtain ⟨n, hn, hp⟩ := hdelete i hi hci
    have he : (a n : ℂ) + ((w i).im : ℂ) * I = w i := by
      rw [← hn, Complex.re_add_im]
    have hz := tprod_quartetFactor_root a h hsq n hp
    rw [he] at hz
    simp only [hz, mul_zero, zero_mul, Complex.zero_re]
  simpa only [tsum_eq_sum hzero] using tendsto_tailAverage_series a h hsq c w hc hw t

/-- Arbitrarily late deletion tails have arbitrarily small total square cost. -/
theorem tendsto_tail_squareCost (h : ℕ → ℝ) (hsq : Summable fun i => h i ^ 2) :
    Tendsto (fun N => ∑' i, h (i + N) ^ 2) atTop (𝓝 0) := by
  have he (N : ℕ) : (∑' i, h (i + N) ^ 2) = (∑' i, h i ^ 2) -
      ∑ i ∈ Finset.range N, h i ^ 2 := by
    linarith only [hsq.sum_add_tsum_nat_add N]
  simp_rw [he]
  have hc : Tendsto (fun _ : ℕ => ∑' i, h i ^ 2) atTop (𝓝 (∑' i, h i ^ 2)) :=
    tendsto_const_nhds
  simpa only [sub_self] using hc.sub hsq.hasSum.tendsto_sum_nat

/-- Deletion can preserve a specified exponent while spending any prescribed positive cost. -/
theorem exists_small_nonzero_tail_multiplier (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (w : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, (∑' i, h (i + N) ^ 2) < ε ∧
      (∏' i : ℕ, quartetFactor (a (i + N)) (h (i + N)) w) ≠ 0 := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_small_shift h hsq w)
  obtain ⟨N, hN, hcost⟩ := ((eventually_ge_atTop N₀).and
    ((tendsto_tail_squareCost h hsq).eventually_lt_const hε)).exists
  refine ⟨N, hcost, ?_⟩
  exact (multipliable_quartetFactor_ne_zero
    (fun i => a (i + N)) (fun i => h (i + N)) w
    ((summable_nat_add_iff N).mpr hsq)
    (fun i => hN₀ (i + N) (hN.trans (Nat.le_add_left N i)))).2

/-- The local Gaussian leakage bound survives infinitely many exact deletions. -/
theorem infinite_tail_local_floor {ι : Type*} (a h : ℕ → ℝ)
    (hsq : Summable fun i => h i ^ 2) (c w : ι → ℂ) {D₀ : ℝ}
    (hc : Summable fun i => ‖c i‖) (hw : ∀ i, c i ≠ 0 → |(w i).re| ≤ D₀)
    {K C D q L : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hglobal : ∀ u, -C * Real.exp (D * |u|) ≤ ∑' i, (c i * Complex.exp (w i * u)).re)
    (hlocal : ∀ u, |u| ≤ L → -K ≤ ∑' i, (c i * Complex.exp (w i * u)).re) :
    -K - 2 * C * Real.exp (-q * L + (D + q) ^ 2 * (∑' i, h i ^ 2) / 2) ≤
      ∑' i, (c i * (∏' n, quartetFactor (a n) (h n) (w i))).re := by
  have hlim := tendsto_tailAverage_series a h hsq c w hc hw 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hlim
  apply ge_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro N
  apply le_trans _ (tailAverage_local_floor (filterPrefix a h N) hK hC hq hglobal hlocal)
  have he : Real.exp (-q * L + (D + q) ^ 2 * squareCost (filterPrefix a h N) / 2) ≤
      Real.exp (-q * L + (D + q) ^ 2 * (∑' i, h i ^ 2) / 2) := by
    apply Real.exp_le_exp.mpr
    gcongr
    exact squareCost_filterPrefix_le a h hsq N
  nlinarith only [mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * C by positivity)]

#print axioms multipliable_quartetFactor
#print axioms exists_nonzero_tail_multiplier
#print axioms tendsto_tailFactor
#print axioms tailAverage_tsum
#print axioms tailAverage_cexp_re
#print axioms tendsto_tailAverage_series
#print axioms tprod_quartetFactor_root
#print axioms tendsto_tailAverage_finite_head
#print axioms exists_small_nonzero_tail_multiplier
#print axioms infinite_tail_local_floor

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
