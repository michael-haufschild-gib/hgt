import GaloisForLFunctions.RHTower.ExponentialTypeNotSummableOnPrimeLogsNaturalRate

/-!
# Prime-log divergence of entire functions of exponential type: second-order windows

For `Φ ≢ 0` entire with `‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}` and `0 ≤ σ`, the partial sums
`Σ_{p<N} p^{−σ} ‖Φ(log p)‖` are unbounded as soon as `ρ < 1 − σ` and `ρ < 5/12`
(`exists_primeLogWeightedSum_gt_of_lt_one_sub_of_lt_five_twelfths`).  Compared with
`exists_primeLogWeightedSum_gt_of_lt_one_sub`, which needs `2ρ < 5/12`, the cap inherited from the
`7/12` short-interval theorem moves from `5/24` to `5/12`; in the Pechersky application `ρ < 1/4`,
so no cap remains there.

The first-order method compares the window integral of `‖Φ‖` with a lower Riemann sum on windows
of log-length `≍ y^{−2ρ}` (`y = e^x`): the derivative bound `‖Φ'‖ ≍ y^{ρ}` against values
`≍ y^{−ρ}` forces that length.  Two second-order facts replace it.

* **Midpoint rule** (`norm_integral_sub_midpoint_le`, `norm_sum_midpoint_sub_integral_le`): the
  *signed* window average of `g = Φ e^{(ρ+δ/2)·}` is large by the signed window two-ray theorem,
  and the midpoint rule on windows of length `h ≍ y^{−ρ−δ/2}` has error `≍ ‖g''‖ h²`, so the
  midpoint values of `‖Φ‖` carry the full mass (`sum_norm_midpoint_ge_of_window_average`).
* **One-sided second-order propagation** (`exists_side_norm_ge_of_norm_deriv_deriv_le`): around
  any point `c`, on one of the two sides `[c, c+ℓ]`, `[c−ℓ, c]` one has `‖Φ‖ ≥ ‖Φ c‖ − ‖Φ''‖ ℓ²`,
  because the linear term of the Taylor expansion has the favourable sign on one side
  (`norm_le_norm_add_mul_of_nonneg`).  With `ℓ = h/2` the loss `≍ y^{ρ} y^{−2ρ−δ} = y^{−ρ−δ}` is a
  small multiple of the midpoint values.

Each half-window of log-length `≍ y^{−ρ−δ/2}` carries Chebyshev mass by the `7/12` theorem as soon
as `ρ + δ/2 < 5/12` (`primeWindow_sum_ge_of_lower_bound`), and the window bounds sum to
`≥ c y^{1−σ−ρ−δ} / log y` (`exists_primeLogWeightedSum_gt_of_midpoint_data`).
-/

open Complex Filter Topology Set Finset Metric MeasureTheory
open scoped Real

noncomputable section

namespace RHTower

/-! ## Cauchy estimates for the first two derivatives -/

/-- Cauchy's estimate on the unit disc about any point: `‖Φ' z‖ ≤ C e^{ρ} e^{ρ‖z‖}`. -/
theorem norm_deriv_le_of_exponentialType_at {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    (z : ℂ) : ‖deriv Φ z‖ ≤ (C * Real.exp ρ) * Real.exp (ρ * ‖z‖) := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z)
    (C := C * Real.exp ρ * Real.exp (ρ * ‖z‖)) one_pos hΦ.diffContOnCl fun w hw => ?_
  · simpa using h
  · rw [mem_sphere_iff_norm] at hw
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      calc ‖w‖ ≤ ‖z‖ + ‖w - z‖ := norm_le_insert' _ _
        _ = ‖z‖ + 1 := by rw [hw]
    calc ‖Φ w‖ ≤ C * Real.exp (ρ * ‖w‖) := hgrow w
      _ ≤ C * Real.exp (ρ * (‖z‖ + 1)) := by gcongr
      _ = C * Real.exp ρ * Real.exp (ρ * ‖z‖) := by
          rw [mul_add, mul_one, Real.exp_add, mul_assoc, mul_comm (Real.exp (ρ * ‖z‖))]

/-- The derivative of an entire function is entire. -/
theorem differentiable_deriv_of_differentiable {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) :
    Differentiable ℂ (deriv Φ) := fun z => ((hΦ.analyticAt z).deriv).differentiableAt

/-- Cauchy's estimate for the second derivative: `‖Φ'' z‖ ≤ C e^{2ρ} e^{ρ‖z‖}`. -/
theorem norm_deriv_deriv_le_of_exponentialType {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    (z : ℂ) : ‖deriv (deriv Φ) z‖ ≤ (C * Real.exp (2 * ρ)) * Real.exp (ρ * ‖z‖) := by
  have h := norm_deriv_le_of_exponentialType_at (differentiable_deriv_of_differentiable hΦ)
    (C := C * Real.exp ρ) (by positivity) hρ (norm_deriv_le_of_exponentialType_at hΦ hC hρ hgrow) z
  calc ‖deriv (deriv Φ) z‖ ≤ (C * Real.exp ρ * Real.exp ρ) * Real.exp (ρ * ‖z‖) := h
    _ = (C * Real.exp (2 * ρ)) * Real.exp (ρ * ‖z‖) := by
        rw [mul_assoc C, ← Real.exp_add, two_mul]

/-- The second-derivative bound at the real points of `[x − 1, x + 2]`, `x ≥ 0`. -/
theorem norm_deriv_deriv_le_on_window {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    {x : ℝ} (hx0 : 0 ≤ x) {s : ℝ} (hs1 : x - 1 ≤ s) (hs2 : s ≤ x + 2) :
    ‖deriv (deriv Φ) s‖ ≤ (C * Real.exp (2 * ρ)) * Real.exp (ρ * (x + 2)) := by
  calc ‖deriv (deriv Φ) s‖ ≤ (C * Real.exp (2 * ρ)) * Real.exp (ρ * ‖(s : ℂ)‖) :=
        norm_deriv_deriv_le_of_exponentialType hΦ hC hρ hgrow s
    _ ≤ (C * Real.exp (2 * ρ)) * Real.exp (ρ * (x + 2)) := by
        gcongr
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith

/-! ## Second-order Taylor bound along the real axis -/

/-- For entire `Φ` with `‖Φ''‖ ≤ S` at the real points within `|u − c|` of `c`:
`‖Φ u − Φ c − (u − c) Φ' c‖ ≤ S (u − c)²`. -/
theorem norm_sub_sub_mul_deriv_le_of_norm_deriv_deriv_le {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {c u S : ℝ} (hS : 0 ≤ S)
    (hbound : ∀ s : ℝ, |s - c| ≤ |u - c| → ‖deriv (deriv Φ) s‖ ≤ S) :
    ‖Φ u - Φ c - ((u - c : ℝ) : ℂ) * deriv Φ c‖ ≤ S * (u - c) ^ 2 := by
  have hΦ' := differentiable_deriv_of_differentiable hΦ
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Φ s) (deriv Φ s) s :=
    fun s => (hΦ (s : ℂ)).hasDerivAt.comp_ofReal
  have hd' : ∀ s : ℝ, HasDerivAt (fun s : ℝ => deriv Φ s) (deriv (deriv Φ) s) s :=
    fun s => (hΦ' (s : ℂ)).hasDerivAt.comp_ofReal
  have hc1 : Continuous fun s : ℝ => deriv Φ (s : ℂ) :=
    hΦ'.continuous.comp Complex.continuous_ofReal
  -- the fundamental theorem of calculus
  have hftc : ∫ s in c..u, deriv Φ s = Φ u - Φ c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hc1.intervalIntegrable _ _)
  have hconst : ∫ s in c..u, deriv Φ (c : ℂ) = ((u - c : ℝ) : ℂ) * deriv Φ c := by
    rw [intervalIntegral.integral_const, Complex.real_smul]
  have hid : Φ u - Φ c - ((u - c : ℝ) : ℂ) * deriv Φ c
      = ∫ s in c..u, (deriv Φ s - deriv Φ (c : ℂ)) := by
    rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) intervalIntegrable_const, hftc,
      hconst]
  rw [hid]
  -- the mean value inequality for `Φ'` on the segment between `c` and `s`
  have hmv : ∀ s ∈ Ι c u, ‖deriv Φ s - deriv Φ (c : ℂ)‖ ≤ S * |u - c| := by
    intro s hs
    have hs' : |s - c| ≤ |u - c| := by
      rcases Set.mem_uIoc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
        linarith
      · rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
        linarith
    rcases le_or_gt c s with hcs | hcs
    · have hsc : s - c = |s - c| := (abs_of_nonneg (by linarith)).symm
      have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t : ℝ => deriv Φ t)
        (f' := fun t : ℝ => deriv (deriv Φ) t) (a := c) (b := s) (C := S)
        (fun t _ => (hd' t).hasDerivWithinAt)
        (fun t ht => hbound t (by
          rw [abs_of_nonneg (by linarith [ht.1])]
          linarith [ht.2, abs_nonneg (s - c)])) s ⟨hcs, le_rfl⟩
      calc ‖deriv Φ s - deriv Φ (c : ℂ)‖ ≤ S * (s - c) := h
        _ ≤ S * |u - c| := by rw [hsc]; gcongr
    · have hsc : c - s = |s - c| := by rw [abs_sub_comm]; exact (abs_of_pos (by linarith)).symm
      have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t : ℝ => deriv Φ t)
        (f' := fun t : ℝ => deriv (deriv Φ) t) (a := s) (b := c) (C := S)
        (fun t _ => (hd' t).hasDerivWithinAt)
        (fun t ht => hbound t (by
          rw [abs_of_nonpos (by linarith [ht.2])]
          linarith [ht.1, abs_nonneg (s - c)])) c ⟨hcs.le, le_rfl⟩
      rw [norm_sub_rev]
      calc ‖deriv Φ (c : ℂ) - deriv Φ s‖ ≤ S * (c - s) := h
        _ ≤ S * |u - c| := by rw [hsc]; gcongr
  calc ‖∫ s in c..u, (deriv Φ s - deriv Φ (c : ℂ))‖ ≤ S * |u - c| * |u - c| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hmv
    _ = S * (u - c) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-! ## The midpoint rule -/

/-- **Midpoint rule.**  If `‖Φ''‖ ≤ S` at the real points within `r` of `c`, then
`‖∫_{c−r}^{c+r} Φ − 2r Φ(c)‖ ≤ 2 S r³`. -/
theorem norm_integral_sub_midpoint_le {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {c r S : ℝ}
    (hr : 0 ≤ r) (hS : 0 ≤ S) (hbound : ∀ s : ℝ, |s - c| ≤ r → ‖deriv (deriv Φ) s‖ ≤ S) :
    ‖(∫ s in (c - r)..(c + r), Φ s) - ((2 * r : ℝ) : ℂ) * Φ c‖ ≤ 2 * S * r ^ 3 := by
  have hcΦ : Continuous fun s : ℝ => Φ (s : ℂ) := hΦ.continuous.comp Complex.continuous_ofReal
  have hlin : Continuous fun s : ℝ => ((s - c : ℝ) : ℂ) * deriv Φ c :=
    (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).mul continuous_const
  -- the Taylor remainder is bounded by `S r²` on the window
  have hRbound : ∀ s ∈ Ι (c - r) (c + r),
      ‖Φ s - Φ c - ((s - c : ℝ) : ℂ) * deriv Φ c‖ ≤ S * r ^ 2 := by
    intro s hs
    have hsr : |s - c| ≤ r := by
      rcases Set.mem_uIoc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_le]
        constructor <;> linarith
      · linarith
    have h := norm_sub_sub_mul_deriv_le_of_norm_deriv_deriv_le hΦ hS (c := c) (u := s)
      (fun t ht => hbound t (le_trans ht hsr))
    have hsq : (s - c) ^ 2 ≤ r ^ 2 :=
      sq_le_sq' (by linarith [(abs_le.mp hsr).1]) (by linarith [(abs_le.mp hsr).2])
    calc ‖Φ s - Φ c - ((s - c : ℝ) : ℂ) * deriv Φ c‖ ≤ S * (s - c) ^ 2 := h
      _ ≤ S * r ^ 2 := by gcongr
  -- the linear term integrates to zero over the symmetric window
  have hlin0 : ∫ s in (c - r)..(c + r), ((s - c : ℝ) : ℂ) * deriv Φ c = 0 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_comp_sub_right (fun s : ℝ => s) c,
      show c - r - c = -r by ring, show c + r - c = r by ring, integral_id]
    simp
  -- decomposition of the integral
  have hsplit : (∫ s in (c - r)..(c + r), Φ s) - ((2 * r : ℝ) : ℂ) * Φ c
      = ∫ s in (c - r)..(c + r), (Φ s - Φ c - ((s - c : ℝ) : ℂ) * deriv Φ c) := by
    rw [intervalIntegral.integral_sub ((hcΦ.sub continuous_const).intervalIntegrable _ _)
      (hlin.intervalIntegrable _ _), intervalIntegral.integral_sub (hcΦ.intervalIntegrable _ _)
      intervalIntegrable_const, hlin0, intervalIntegral.integral_const, Complex.real_smul]
    congr 2
    push_cast
    ring
  rw [hsplit]
  calc ‖∫ s in (c - r)..(c + r), (Φ s - Φ c - ((s - c : ℝ) : ℂ) * deriv Φ c)‖
      ≤ S * r ^ 2 * |c + r - (c - r)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hRbound
    _ = 2 * S * r ^ 3 := by
        rw [show c + r - (c - r) = 2 * r by ring, abs_of_nonneg (by linarith)]
        ring

/-- **Midpoint Riemann sum.**  For entire `g` with `‖g''‖ ≤ S` at the real points of
`[x − 1, x + 2]` and `N h = 1`, the midpoint sum `Σ_{k<N} h g(x + kh + h/2)` differs from
`∫_0^1 g(x+t) dt` by at most `S h²/4`. -/
theorem norm_sum_midpoint_sub_integral_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {x h S : ℝ}
    (hx0 : 0 ≤ x) (hh0 : 0 < h) {N : ℕ} (hNh : (N : ℝ) * h = 1) (hS : 0 ≤ S)
    (hbound : ∀ s : ℝ, x - 1 ≤ s → s ≤ x + 2 → ‖deriv (deriv g) s‖ ≤ S) :
    ‖(∑ k ∈ range N, (h : ℂ) * g ((x + k * h + h / 2 : ℝ) : ℂ)) - ∫ t in (0 : ℝ)..1, g (x + t)‖
      ≤ S * h ^ 2 / 4 := by
  have hgc : Continuous fun s : ℝ => g (s : ℂ) := hg.continuous.comp Complex.continuous_ofReal
  -- shift the integral to `[x, x+1]` and split it along the windows
  have hshift : ∫ t in (0 : ℝ)..1, g (x + t) = ∫ s in x..(x + 1), g s := by
    have h := intervalIntegral.integral_comp_add_left (fun s : ℝ => g (s : ℂ)) x (a := 0) (b := 1)
    simp only [Complex.ofReal_add, add_zero] at h
    exact h
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun s : ℝ => g (s : ℂ)) (a := fun k : ℕ => x + k * h) (n := N)
    (fun k _ => hgc.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_mul, add_zero, hNh] at hsplit
  rw [hshift, ← hsplit, ← sum_sub_distrib]
  -- each window is a midpoint-rule error
  have hwin : ∀ k ∈ range N,
      ‖(h : ℂ) * g ((x + k * h + h / 2 : ℝ) : ℂ)
          - ∫ s in (x + k * h)..(x + ((k + 1 : ℕ) : ℝ) * h), g s‖ ≤ S * h ^ 3 / 4 := by
    intro k hk
    have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hkh : (k : ℝ) * h + h ≤ 1 := by
      calc (k : ℝ) * h + h = ((k : ℝ) + 1) * h := by ring
        _ ≤ N * h := by gcongr
        _ = 1 := hNh
    have hmid := norm_integral_sub_midpoint_le hg (c := x + k * h + h / 2) (r := h / 2)
      (by positivity) hS (fun s hs => hbound s (by linarith [(abs_le.mp hs).1])
        (by linarith [(abs_le.mp hs).2]))
    rw [show x + k * h + h / 2 - h / 2 = x + k * h by ring,
      show x + k * h + h / 2 + h / 2 = x + ((k + 1 : ℕ) : ℝ) * h by push_cast; ring,
      show ((2 * (h / 2) : ℝ) : ℂ) = (h : ℂ) by push_cast; ring, norm_sub_rev] at hmid
    calc ‖(h : ℂ) * g ((x + k * h + h / 2 : ℝ) : ℂ)
          - ∫ s in (x + k * h)..(x + ((k + 1 : ℕ) : ℝ) * h), g s‖ ≤ 2 * S * (h / 2) ^ 3 := hmid
      _ = S * h ^ 3 / 4 := by ring
  calc ‖∑ k ∈ range N, ((h : ℂ) * g ((x + k * h + h / 2 : ℝ) : ℂ)
          - ∫ s in (x + k * h)..(x + ((k + 1 : ℕ) : ℝ) * h), g s)‖
      ≤ ∑ k ∈ range N, ‖(h : ℂ) * g ((x + k * h + h / 2 : ℝ) : ℂ)
          - ∫ s in (x + k * h)..(x + ((k + 1 : ℕ) : ℝ) * h), g s‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range N, S * h ^ 3 / 4 := sum_le_sum hwin
    _ = S * h ^ 2 / 4 := by
        rw [sum_const, card_range, nsmul_eq_mul]
        calc (N : ℝ) * (S * h ^ 3 / 4) = (N * h) * (S * h ^ 2 / 4) := by ring
          _ = S * h ^ 2 / 4 := by rw [hNh, one_mul]

/-! ## One-sided second-order propagation -/

/-- `‖A‖ ≤ ‖A + t B‖` whenever `0 ≤ t · Re(conj A · B)`. -/
theorem norm_le_norm_add_mul_of_nonneg {A B : ℂ} {t : ℝ}
    (h : 0 ≤ t * (starRingEnd ℂ A * B).re) : ‖A‖ ≤ ‖A + (t : ℂ) * B‖ := by
  rcases eq_or_ne A 0 with hA | hA
  · simp [hA]
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hre : (starRingEnd ℂ A * (A + (t : ℂ) * B)).re
      = ‖A‖ ^ 2 + t * (starRingEnd ℂ A * B).re := by
    rw [mul_add, Complex.add_re, Complex.conj_mul', ← mul_assoc, mul_comm (starRingEnd ℂ A) (t : ℂ),
      mul_assoc, Complex.re_ofReal_mul, ← Complex.ofReal_pow, Complex.ofReal_re]
  have h1 : ‖A‖ * ‖A‖ ≤ ‖A‖ * ‖A + (t : ℂ) * B‖ := by
    calc ‖A‖ * ‖A‖ = ‖A‖ ^ 2 := (sq _).symm
      _ ≤ ‖A‖ ^ 2 + t * (starRingEnd ℂ A * B).re := by linarith
      _ = (starRingEnd ℂ A * (A + (t : ℂ) * B)).re := hre.symm
      _ ≤ ‖starRingEnd ℂ A * (A + (t : ℂ) * B)‖ := Complex.re_le_norm _
      _ = ‖A‖ * ‖A + (t : ℂ) * B‖ := by rw [norm_mul, Complex.norm_conj]
  exact le_of_mul_le_mul_left h1 hApos

/-- **One-sided second-order propagation.**  If `‖Φ''‖ ≤ S` at the real points within `ℓ` of `c`,
then on one of the intervals `[c, c + ℓ]`, `[c − ℓ, c]` one has `‖Φ‖ ≥ ‖Φ c‖ − S ℓ²`. -/
theorem exists_side_norm_ge_of_norm_deriv_deriv_le {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {c ℓ S : ℝ} (hℓ : 0 ≤ ℓ) (hS : 0 ≤ S)
    (hbound : ∀ s : ℝ, |s - c| ≤ ℓ → ‖deriv (deriv Φ) s‖ ≤ S) :
    ∃ α : ℝ, (α = c ∨ α = c - ℓ) ∧ ∀ u ∈ Icc α (α + ℓ), ‖Φ c‖ - S * ℓ ^ 2 ≤ ‖Φ u‖ := by
  have key : ∀ u : ℝ, |u - c| ≤ ℓ → 0 ≤ (u - c) * (starRingEnd ℂ (Φ c) * deriv Φ c).re →
      ‖Φ c‖ - S * ℓ ^ 2 ≤ ‖Φ u‖ := by
    intro u hu hsign
    have h1 := norm_sub_sub_mul_deriv_le_of_norm_deriv_deriv_le hΦ hS (c := c) (u := u)
      (fun t ht => hbound t (le_trans ht hu))
    have h2 : ‖Φ c‖ ≤ ‖Φ c + ((u - c : ℝ) : ℂ) * deriv Φ c‖ :=
      norm_le_norm_add_mul_of_nonneg hsign
    have h3 : ‖Φ c + ((u - c : ℝ) : ℂ) * deriv Φ c‖ ≤ ‖Φ u‖ + S * (u - c) ^ 2 := by
      calc ‖Φ c + ((u - c : ℝ) : ℂ) * deriv Φ c‖
          = ‖Φ u - (Φ u - Φ c - ((u - c : ℝ) : ℂ) * deriv Φ c)‖ := by
            congr 1
            ring
        _ ≤ ‖Φ u‖ + ‖Φ u - Φ c - ((u - c : ℝ) : ℂ) * deriv Φ c‖ := norm_sub_le _ _
        _ ≤ ‖Φ u‖ + S * (u - c) ^ 2 := by gcongr
    have h4 : (u - c) ^ 2 ≤ ℓ ^ 2 :=
      sq_le_sq' (by linarith [(abs_le.mp hu).1]) (by linarith [(abs_le.mp hu).2])
    have h5 : S * (u - c) ^ 2 ≤ S * ℓ ^ 2 := mul_le_mul_of_nonneg_left h4 hS
    linarith
  rcases le_or_gt 0 (starRingEnd ℂ (Φ c) * deriv Φ c).re with hpos | hneg
  · refine ⟨c, Or.inl rfl, fun u hu => key u ?_ ?_⟩
    · rw [abs_of_nonneg (by linarith [hu.1])]
      linarith [hu.2]
    · exact mul_nonneg (by linarith [hu.1]) hpos
  · refine ⟨c - ℓ, Or.inr rfl, fun u hu => key u ?_ ?_⟩
    · rw [abs_of_nonpos (by linarith [hu.2])]
      linarith [hu.1]
    · nlinarith [hu.2, hneg]

/-! ## Signed window largeness and the midpoint sum of `‖Φ‖` -/

/-- **Signed window largeness.**  An entire `Φ ≢ 0` of exponential type `ρ` has
`‖∫_0^1 Φ(x+t) e^{(ρ+δ/2)(x+t)} dt‖ ≥ e^{−δx/2}` at arbitrarily large real `x`: otherwise
`Φ(w) e^{(ρ+δ/2)w}` has two-ray window-average decay and vanishes. -/
theorem exists_window_average_ge_of_exponentialType {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    (hne : Φ ≠ 0) {δ : ℝ} (hδ : 0 < δ) (X : ℝ) :
    ∃ x : ℝ, X ≤ x ∧ Real.exp (-(δ / 2 * x)) ≤
      ‖∫ t in (0 : ℝ)..1, Φ (x + t) * Complex.exp (((ρ + δ / 2 : ℝ) : ℂ) * (x + t))‖ := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hC : 0 ≤ C := by
    have h := hgrow 0
    simp only [norm_zero, mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (norm_nonneg _) h
  set X' : ℝ := max X 0 with hX'
  have hX'0 : 0 ≤ X' := le_max_right _ _
  set a : ℝ := ρ + δ / 2 with ha
  have ha0 : 0 ≤ a := by positivity
  set τ : ℝ := 2 * ρ + δ / 2 with hτ
  have hτ0 : 0 ≤ τ := by positivity
  set g : ℂ → ℂ := fun w => Φ w * Complex.exp ((a : ℂ) * w) with hg
  have hgdiff : Differentiable ℂ g :=
    hΦ.mul (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))
  have hgnorm : ∀ w, ‖g w‖ = ‖Φ w‖ * Real.exp (a * w.re) := fun w => by
    rw [hg]
    simp only
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  have hgrow' : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (τ * ‖z‖) := fun z => by
    rw [hgnorm]
    calc ‖Φ z‖ * Real.exp (a * z.re)
        ≤ (C * Real.exp (ρ * ‖z‖)) * Real.exp (a * ‖z‖) := by
          gcongr
          · exact hgrow z
          · exact Complex.re_le_norm z
      _ = C * Real.exp (τ * ‖z‖) := by
          rw [mul_assoc, ← Real.exp_add, ha, hτ]
          congr 2
          ring
  set C₂ : ℝ := max 1 (C * Real.exp (τ * (X' + 1)) * Real.exp (δ / 2 * X')) with hC₂
  have hCC₂ : C ≤ C₂ := by
    refine le_trans ?_ (le_max_right _ _)
    calc C = C * 1 * 1 := by ring
      _ ≤ C * Real.exp (τ * (X' + 1)) * Real.exp (δ / 2 * X') := by
          gcongr
          · exact Real.one_le_exp (by positivity)
          · exact Real.one_le_exp (by positivity)
  have hminus : ∀ x : ℝ, x ≤ 0 → ‖g x‖ ≤ C₂ * Real.exp (δ / 2 * x) := fun x hx => by
    rw [hgnorm, Complex.ofReal_re]
    calc ‖Φ x‖ * Real.exp (a * x)
        ≤ (C * Real.exp (ρ * ‖(x : ℂ)‖)) * Real.exp (a * x) := by
          gcongr
          exact hgrow x
      _ = C * Real.exp (δ / 2 * x) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hx, mul_assoc, ← Real.exp_add, ha]
          congr 2
          ring
      _ ≤ C₂ * Real.exp (δ / 2 * x) := by gcongr
  have hplus : ∀ x : ℝ, 0 ≤ x → ‖unitWindowAverage g x‖ ≤ C₂ * Real.exp (-(δ / 2 * x)) :=
    fun x hx => by
    rcases le_or_gt X' x with hXx | hXx
    · have h1 := hcon x (le_trans (le_max_left _ _) hXx)
      calc ‖unitWindowAverage g x‖
          = ‖∫ t in (0 : ℝ)..1, Φ (x + t) * Complex.exp (((ρ + δ / 2 : ℝ) : ℂ) * (x + t))‖ := rfl
        _ ≤ Real.exp (-(δ / 2 * x)) := h1.le
        _ ≤ C₂ * Real.exp (-(δ / 2 * x)) := by
            rw [← one_mul (Real.exp (-(δ / 2 * x)))]
            gcongr
            · simp
            · exact le_max_left _ _
    · refine norm_unitWindowAverage_le fun t ht => ?_
      calc ‖g (x + t)‖ ≤ C * Real.exp (τ * ‖(x : ℂ) + t‖) := hgrow' _
        _ ≤ C * Real.exp (τ * (X' + 1)) := by
            gcongr
            rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by linarith [ht.1])]
            linarith [ht.2]
        _ = (C * Real.exp (τ * (X' + 1)) * Real.exp (δ / 2 * X')) * Real.exp (-(δ / 2 * X')) := by
            rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ C₂ * Real.exp (-(δ / 2 * x)) :=
            mul_le_mul (le_max_right _ _)
              (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hXx.le (by positivity))))
              (Real.exp_pos _).le (le_trans zero_le_one (le_max_left _ _))
  have hg0 : g = 0 := eq_zero_of_two_ray_window_average_decay hgdiff hC hτ0 (half_pos hδ) hgrow'
    hplus hminus
  apply hne
  funext w
  have h := congrFun hg0 w
  rw [hg] at h
  simp only [Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at h
  exact h

/-- **The midpoint sum of `‖Φ‖` carries the mass of the signed window average.**  With
`g = Φ e^{a·}`, `‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}`, and the midpoint error `C e^{2(ρ+a)} e^{(ρ+a)(x+2)} h²/4`
at most `m₁/2`: if `‖∫_0^1 g(x+t) dt‖ ≥ m₁` then `Σ_{k<N} h ‖Φ(x + kh + h/2)‖ ≥ (m₁/2) e^{−a(x+1)}`. -/
theorem sum_norm_midpoint_ge_of_window_average {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    {a x h : ℝ} (ha : 0 ≤ a) (hx0 : 0 ≤ x) (hh0 : 0 < h) {N : ℕ} (hNh : (N : ℝ) * h = 1)
    {m₁ : ℝ}
    (hint : m₁ ≤ ‖∫ t in (0 : ℝ)..1, Φ (x + t) * Complex.exp ((a : ℂ) * (x + t))‖)
    (herr : (C * Real.exp (2 * (ρ + a))) * Real.exp ((ρ + a) * (x + 2)) * h ^ 2 / 4 ≤ m₁ / 2) :
    m₁ / 2 * Real.exp (-(a * (x + 1))) ≤ ∑ k ∈ range N, h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖ := by
  set g : ℂ → ℂ := fun w => Φ w * Complex.exp ((a : ℂ) * w) with hg
  have hgdiff : Differentiable ℂ g :=
    hΦ.mul (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))
  have hgnorm : ∀ w, ‖g w‖ = ‖Φ w‖ * Real.exp (a * w.re) := fun w => by
    rw [hg]
    simp only
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  have hgrow' : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp ((ρ + a) * ‖z‖) := fun z => by
    rw [hgnorm]
    calc ‖Φ z‖ * Real.exp (a * z.re)
        ≤ (C * Real.exp (ρ * ‖z‖)) * Real.exp (a * ‖z‖) := by
          gcongr
          · exact hgrow z
          · exact Complex.re_le_norm z
      _ = C * Real.exp ((ρ + a) * ‖z‖) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  set S : ℝ := (C * Real.exp (2 * (ρ + a))) * Real.exp ((ρ + a) * (x + 2)) with hS
  have hS0 : 0 ≤ S := by positivity
  have hbound : ∀ s : ℝ, x - 1 ≤ s → s ≤ x + 2 → ‖deriv (deriv g) s‖ ≤ S := fun s hs1 hs2 =>
    norm_deriv_deriv_le_on_window hgdiff hC (by positivity) hgrow' hx0 hs1 hs2
  have hmid := norm_sum_midpoint_sub_integral_le hgdiff hx0 hh0 hNh hS0 hbound
  have hint' : m₁ ≤ ‖∫ t in (0 : ℝ)..1, g (x + t)‖ := hint
  -- the midpoint sum of `g` is large
  have hsum : m₁ / 2 ≤ ‖∑ k ∈ range N, (h : ℂ) * g ((x + k * h + h / 2 : ℝ) : ℂ)‖ := by
    have h1 := norm_sub_norm_le (∑ k ∈ range N, (h : ℂ) * g ((x + k * h + h / 2 : ℝ) : ℂ))
      (∫ t in (0 : ℝ)..1, g (x + t))
    linarith
  -- pass to the moduli and remove the exponential weight
  have hterm : ∀ k ∈ range N,
      ‖(h : ℂ) * g ((x + k * h + h / 2 : ℝ) : ℂ)‖
        ≤ Real.exp (a * (x + 1)) * (h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖) := by
    intro k hk
    have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hkh : (k : ℝ) * h + h / 2 ≤ 1 := by
      calc (k : ℝ) * h + h / 2 ≤ ((k : ℝ) + 1) * h := by nlinarith
        _ ≤ N * h := by gcongr
        _ = 1 := hNh
    rw [norm_mul, hgnorm, Complex.norm_real, Real.norm_of_nonneg hh0.le, Complex.ofReal_re]
    calc h * (‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖ * Real.exp (a * (x + k * h + h / 2)))
        ≤ h * (‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖ * Real.exp (a * (x + 1))) := by
          gcongr
          linarith
      _ = Real.exp (a * (x + 1)) * (h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖) := by ring
  have h2 : m₁ / 2 ≤ Real.exp (a * (x + 1)) * ∑ k ∈ range N, h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖ := by
    calc m₁ / 2 ≤ ‖∑ k ∈ range N, (h : ℂ) * g ((x + k * h + h / 2 : ℝ) : ℂ)‖ := hsum
      _ ≤ ∑ k ∈ range N, ‖(h : ℂ) * g ((x + k * h + h / 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ range N, Real.exp (a * (x + 1)) * (h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖) :=
          sum_le_sum hterm
      _ = Real.exp (a * (x + 1)) * ∑ k ∈ range N, h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖ := by
          rw [mul_sum]
  calc m₁ / 2 * Real.exp (-(a * (x + 1)))
      ≤ (Real.exp (a * (x + 1)) * ∑ k ∈ range N, h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖)
          * Real.exp (-(a * (x + 1))) := by gcongr
    _ = ∑ k ∈ range N, h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖ := by
        rw [mul_comm, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-! ## The prime mass of a logarithmic window with a given lower bound -/

/-- **Prime mass of a logarithmic window with a given lower bound.**  Let `[α, α + ℓ] ⊂ [x, x+1]`
with `ℓ > 0` and `m ≤ ‖Φ(u)‖` on it.  If the short-interval theorem holds from `X₁ ≤ e^x` on
and `e^{(x+1)α'} ≤ e^x ℓ/2`, the primes `p ∈ (e^α, e^{α+ℓ}]` contribute at least
`e^{−σ(x+1)} m (e^x ℓ/4)/(x+1)` to the prime sum. -/
theorem primeWindow_sum_ge_of_lower_bound (Φ : ℂ → ℂ) {σ x α ℓ m : ℝ} (hσ : 0 ≤ σ)
    (hx0 : 0 ≤ x) (hα : x ≤ α) (hℓ : 0 < ℓ) (hαℓ : α + ℓ ≤ x + 1) (hm : 0 ≤ m)
    (hlow : ∀ u : ℝ, α ≤ u → u ≤ α + ℓ → m ≤ ‖Φ u‖) {α' X₁ : ℝ}
    (hθ : ∀ y L : ℝ, X₁ ≤ y → 0 ≤ L →
      (L - (y + L) ^ α') / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y)
    (hα'0 : 0 ≤ α') (hX₁ : X₁ ≤ Real.exp x) (hwin : Real.exp (x + 1) ^ α' ≤ Real.exp x * ℓ / 2) :
    Real.exp (-(σ * (x + 1))) * m / (x + 1) * (Real.exp x * ℓ / 4)
      ≤ ∑ p ∈ Finset.Ioc ⌊Real.exp α⌋₊ ⌊Real.exp (α + ℓ)⌋₊,
          if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0 := by
  set y : ℝ := Real.exp x with hy
  have hy0 : 0 < y := Real.exp_pos x
  set Yk : ℝ := Real.exp α with hYk
  set Yk1 : ℝ := Real.exp (α + ℓ) with hYk1
  have hYk0 : 0 < Yk := Real.exp_pos _
  have hYk10 : 0 < Yk1 := Real.exp_pos _
  have hYk1gt : 1 < Yk1 := Real.one_lt_exp_iff.mpr (by linarith)
  have hYkge : y ≤ Yk := Real.exp_le_exp.mpr hα
  have hYk1le : Yk1 ≤ Real.exp (x + 1) := Real.exp_le_exp.mpr hαℓ
  have hYsucc : Yk1 = Yk * Real.exp ℓ := by rw [hYk1, hYk, ← Real.exp_add]
  set L : ℝ := Yk1 - Yk with hL
  have hLk : Yk * ℓ ≤ L := by
    rw [hL, hYsucc]
    have h1 := Real.add_one_le_exp ℓ
    nlinarith
  have hyhL : y * ℓ ≤ L := le_trans (mul_le_mul_of_nonneg_right hYkge hℓ.le) hLk
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hyhL
  have hYL : Yk + L = Yk1 := by rw [hL]; ring
  have hlogYk : Real.log Yk = α := by rw [hYk]; exact Real.log_exp _
  have hlogYk1 : Real.log Yk1 = α + ℓ := by rw [hYk1]; exact Real.log_exp _
  clear_value y Yk Yk1 L
  -- the values of `Φ` at the primes of the window
  have hlow' : ∀ p : ℕ, p.Prime → Yk < p → (p : ℝ) ≤ Yk + L → m ≤ ‖Φ (Real.log p)‖ := by
    intro p hp hp1 hp2
    rw [hYL] at hp2
    have hp0 : (0 : ℝ) < p := lt_trans hYk0 hp1
    refine hlow _ ?_ ?_
    · rw [← hlogYk]
      exact (Real.log_lt_log hYk0 hp1).le
    · rw [← hlogYk1]
      exact Real.log_le_log hp0 hp2
  -- the Chebyshev mass of the window
  have hθwin : y * ℓ / 4 ≤ Chebyshev.theta (Yk + L) - Chebyshev.theta Yk := by
    have h1 := hθ Yk L (le_trans hX₁ hYkge) hL0.le
    have h2 : (Yk + L) ^ α' ≤ L / 2 := by
      rw [hYL]
      calc Yk1 ^ α' ≤ Real.exp (x + 1) ^ α' := Real.rpow_le_rpow hYk10.le hYk1le hα'0
        _ ≤ y * ℓ / 2 := hwin
        _ ≤ L / 2 := by linarith
    linarith
  have hsum := window_sum_ge_theta_window Φ hσ (by rw [hYL]; exact hYk1gt) hL0.le hm hlow'
  rw [hYL] at hsum hθwin
  have hlogpos : 0 < Real.log Yk1 := by rw [hlogYk1]; linarith
  have hlogle : Real.log Yk1 ≤ x + 1 := by rw [hlogYk1]; linarith
  have hrp : Real.exp (-(σ * (x + 1))) ≤ Yk1 ^ (-σ) := by
    calc Real.exp (-(σ * (x + 1))) = Real.exp (x + 1) ^ (-σ) := by
          rw [← Real.exp_mul]
          congr 1
          ring
      _ ≤ Yk1 ^ (-σ) := Real.rpow_le_rpow_of_nonpos hYk10 hYk1le (by linarith)
  have hnum : Real.exp (-(σ * (x + 1))) * m ≤ Yk1 ^ (-σ) * m := mul_le_mul_of_nonneg_right hrp hm
  have hnn : 0 ≤ Yk1 ^ (-σ) * m := mul_nonneg (Real.rpow_nonneg hYk10.le _) hm
  have hA : Real.exp (-(σ * (x + 1))) * m / (x + 1) ≤ Yk1 ^ (-σ) * m / Real.log Yk1 :=
    calc Real.exp (-(σ * (x + 1))) * m / (x + 1) ≤ Yk1 ^ (-σ) * m / (x + 1) :=
          div_le_div_of_nonneg_right hnum (by linarith)
      _ ≤ Yk1 ^ (-σ) * m / Real.log Yk1 := div_le_div_of_nonneg_left hnn hlogpos hlogle
  calc Real.exp (-(σ * (x + 1))) * m / (x + 1) * (y * ℓ / 4)
      ≤ Yk1 ^ (-σ) * m / Real.log Yk1 * (y * ℓ / 4) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ ≤ Yk1 ^ (-σ) * m / Real.log Yk1 * (Chebyshev.theta Yk1 - Chebyshev.theta Yk) :=
        mul_le_mul_of_nonneg_left hθwin (div_nonneg hnn hlogpos.le)
    _ ≤ _ := hsum

/-! ## Assembly from midpoint data -/

/-- **Assembly.**  Let `[x, x+1]` be cut into `N` windows of length `h = 1/N`, with midpoints
`c_k = x + kh + h/2`, let `‖Φ''‖ ≤ S` at the real points of `[x − 1, x + 2]`, and suppose the
midpoint sum `Σ h ‖Φ(c_k)‖` is at least `m` with `S (h/2)² ≤ m/2`.  If every half-window of
`(e^x, e^{x+1}]` carries the Chebyshev mass of the short-interval theorem, the prime sum up to
`e^{x+1}` is at least `e^{−σ(x+1)} e^x (m/2) / (8(x+1))`; so if this exceeds `M + 1`, the prime
sum exceeds `M`. -/
theorem exists_primeLogWeightedSum_gt_of_midpoint_data {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {σ : ℝ} (hσ : 0 ≤ σ) {x h : ℝ} (hx0 : 0 ≤ x) (hh0 : 0 < h) {N : ℕ} (hNh : (N : ℝ) * h = 1)
    {α' X₁ : ℝ}
    (hθ : ∀ y L : ℝ, X₁ ≤ y → 0 ≤ L →
      (L - (y + L) ^ α') / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y)
    (hα'0 : 0 ≤ α') (hX₁ : X₁ ≤ Real.exp x)
    (hwin : Real.exp (x + 1) ^ α' ≤ Real.exp x * (h / 2) / 2)
    {S : ℝ} (hS : 0 ≤ S) (hbound : ∀ s : ℝ, x - 1 ≤ s → s ≤ x + 2 → ‖deriv (deriv Φ) s‖ ≤ S)
    {m : ℝ} (hmid : m ≤ ∑ k ∈ range N, h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖)
    (hloss : S * (h / 2) ^ 2 ≤ m / 2) {M : ℝ}
    (hM : M + 1 ≤ Real.exp (-(σ * (x + 1))) * Real.exp x / (8 * (x + 1)) * (m / 2)) :
    ∃ N' : ℕ, M < primeLogWeightedSum Φ σ N' := by
  -- the window values and the losses
  obtain ⟨V, hVdef⟩ : ∃ V : ℕ → ℝ, ∀ k : ℕ, V k = ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨mk, hmkdef⟩ : ∃ mk : ℕ → ℝ, ∀ k : ℕ, mk k = max 0 (V k - S * (h / 2) ^ 2) :=
    ⟨_, fun _ => rfl⟩
  have hmk0 : ∀ k, 0 ≤ mk k := fun k => by rw [hmkdef]; exact le_max_left _ _
  have hmksum : m / 2 ≤ ∑ k ∈ range N, h * mk k := by
    have h1 : ∑ k ∈ range N, h * (V k - S * (h / 2) ^ 2) ≤ ∑ k ∈ range N, h * mk k :=
      sum_le_sum fun k _ => by
        rw [hmkdef]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) hh0.le
    have h2 : ∑ k ∈ range N, h * (V k - S * (h / 2) ^ 2)
        = (∑ k ∈ range N, h * V k) - S * (h / 2) ^ 2 := by
      simp only [mul_sub, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      rw [← mul_assoc, hNh, one_mul]
    have h3 : ∑ k ∈ range N, h * V k = ∑ k ∈ range N, h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖ :=
      sum_congr rfl fun k _ => by rw [hVdef]
    linarith
  clear hmid
  -- the prime windows `(Y k, Y (k+1)]`
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ → ℝ, ∀ k : ℕ, Y k = Real.exp (x + k * h) := ⟨_, fun _ => rfl⟩
  have hYmono : Monotone Y := fun i j hij => by
    rw [hYdef, hYdef]
    exact Real.exp_le_exp.mpr
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hh0.le))
  -- the lower bound for each prime window
  have hwin' : ∀ k ∈ range N,
      Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (Real.exp x * (h / 2) / 4)
        ≤ ∑ p ∈ Finset.Ioc ⌊Y k⌋₊ ⌊Y (k + 1)⌋₊,
            if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0 := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ k * h := by positivity
    have hkh : (k : ℝ) * h + h ≤ 1 := by
      have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Finset.mem_range.mp hk
      calc (k : ℝ) * h + h = ((k + 1 : ℕ) : ℝ) * h := by push_cast; ring
        _ ≤ N * h := mul_le_mul_of_nonneg_right this hh0.le
        _ = 1 := hNh
    -- the favourable half-window about the midpoint
    obtain ⟨α, hα, hside⟩ := exists_side_norm_ge_of_norm_deriv_deriv_le hΦ
      (c := x + k * h + h / 2) (ℓ := h / 2) (by positivity) hS
      (fun s hs => hbound s (by linarith [(abs_le.mp hs).1]) (by linarith [(abs_le.mp hs).2]))
    have hαx : x + k * h ≤ α := by
      rcases hα with rfl | rfl <;> linarith
    have hαℓ : α + h / 2 ≤ x + ((k + 1 : ℕ) : ℝ) * h := by
      rcases hα with rfl | rfl <;> push_cast <;> linarith
    have hlow : ∀ u : ℝ, α ≤ u → u ≤ α + h / 2 → mk k ≤ ‖Φ u‖ := fun u hu1 hu2 => by
      rw [hmkdef, hVdef]
      exact max_le (norm_nonneg _) (hside u ⟨hu1, hu2⟩)
    have h1 := primeWindow_sum_ge_of_lower_bound Φ hσ hx0 (le_trans (le_add_of_nonneg_right hk0) hαx)
      (by positivity) (by push_cast at hαℓ; linarith) (hmk0 k) hlow hθ hα'0 hX₁ hwin
    refine le_trans h1 (sum_le_sum_of_subset_of_nonneg
      (Finset.Ioc_subset_Ioc (Nat.floor_le_floor ?_) (Nat.floor_le_floor ?_)) fun p _ _ => ?_)
    · rw [hYdef]
      exact Real.exp_le_exp.mpr hαx
    · rw [hYdef]
      exact Real.exp_le_exp.mpr hαℓ
    · split_ifs
      · positivity
      · exact le_rfl
  -- the window sums merge into one prime sum
  have hmerge := sum_range_sum_Ioc_eq_sum_Ioc
    (f := fun p : ℕ => if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0)
    (b := fun k => ⌊Y k⌋₊) (fun i j hij => Nat.floor_le_floor (hYmono hij)) N
  have hchain : ∑ k ∈ range N,
      Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (Real.exp x * (h / 2) / 4)
      ≤ primeLogWeightedSum Φ σ (⌊Y N⌋₊ + 1) := by
    calc ∑ k ∈ range N, Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (Real.exp x * (h / 2) / 4)
        ≤ ∑ k ∈ range N, ∑ p ∈ Finset.Ioc ⌊Y k⌋₊ ⌊Y (k + 1)⌋₊,
            (if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0) := sum_le_sum hwin'
      _ = ∑ p ∈ Finset.Ioc ⌊Y 0⌋₊ ⌊Y N⌋₊,
            (if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0) := hmerge
      _ ≤ primeLogWeightedSum Φ σ (⌊Y N⌋₊ + 1) := window_sum_le_primeLogWeightedSum Φ σ _ _
  refine ⟨⌊Y N⌋₊ + 1, lt_of_lt_of_le ?_ hchain⟩
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hfactor : ∑ k ∈ range N,
      Real.exp (-(σ * (x + 1))) * mk k / (x + 1) * (Real.exp x * (h / 2) / 4)
      = Real.exp (-(σ * (x + 1))) * Real.exp x / (8 * (x + 1)) * ∑ k ∈ range N, h * mk k := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    field_simp
    ring
  rw [hfactor]
  calc M < M + 1 := by linarith
    _ ≤ Real.exp (-(σ * (x + 1))) * Real.exp x / (8 * (x + 1)) * (m / 2) := hM
    _ ≤ Real.exp (-(σ * (x + 1))) * Real.exp x / (8 * (x + 1)) * ∑ k ∈ range N, h * mk k :=
        mul_le_mul_of_nonneg_left hmksum (by positivity)

/-! ## The prime sums are unbounded for `ρ < 1 − σ`, `ρ < 5/12` -/

/-- **The prime-sum lower bound without the first-order cap.**  For `Φ ≢ 0` entire with
`‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}`, `0 ≤ σ`, `ρ < 1 − σ` and `ρ < 5/12`, the sums `Σ_{p<N} p^{−σ} ‖Φ(log p)‖`
are unbounded. -/
theorem exists_primeLogWeightedSum_gt_of_lt_one_sub_of_lt_five_twelfths {Φ : ℂ → ℂ}
    (hΦ : Differentiable ℂ Φ) {C ρ σ : ℝ} (hρ : 0 ≤ ρ)
    (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) (hne : Φ ≠ 0)
    (hσ : 0 ≤ σ) (hρσ : ρ < 1 - σ) (hρ5 : ρ < 5 / 12) (M : ℝ) :
    ∃ N : ℕ, M < primeLogWeightedSum Φ σ N := by
  -- the growth constant is positive, since `Φ ≢ 0`
  have hC : 0 < C := by
    by_contra hC
    simp only [not_lt] at hC
    apply hne
    funext ξ
    have h := hgrow ξ
    have h2 : C * Real.exp (ρ * ‖ξ‖) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le
    exact norm_le_zero_iff.mp (le_trans h h2)
  have hC0 : C ≠ 0 := hC.ne'
  -- the exponents
  obtain ⟨δ, hδ0, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ (1 - σ - ρ) / 4 ∧ δ ≤ (5 / 12 - ρ) / 2 :=
    ⟨min ((1 - σ - ρ) / 4) ((5 / 12 - ρ) / 2), lt_min (by linarith) (by linarith),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 1 - (ρ + δ / 2) := ⟨_, rfl⟩
  have hβ7 : 7 / 12 < β := by rw [hβ]; linarith
  obtain ⟨α', hα'⟩ : ∃ α' : ℝ, α' = (7 / 12 + β) / 2 := ⟨_, rfl⟩
  have hα'7 : 7 / 12 < α' := by rw [hα']; linarith
  have hα'β : α' < β := by rw [hα']; linarith
  have hα'1 : α' < 1 := by rw [hα', hβ]; linarith
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 - σ - ρ - δ := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; linarith
  -- the prime-mass window theorem
  obtain ⟨X₁, hX₁1, hθ⟩ := exists_theta_window_lower_seven_twelfths hα'7 hα'1
  -- constants
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * (ρ + (ρ + δ / 2)) + 4 * ρ + (ρ + δ / 2) := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = Real.exp (-K) / (C + 1) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = Real.exp (-(ρ + δ / 2)) / 2 := ⟨_, rfl⟩
  have hm₀0 : 0 < m₀ := by rw [hm₀]; positivity
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = Real.exp (-σ) * m₀ / 16 := ⟨_, rfl⟩
  have hc₂0 : 0 < c₂ := by rw [hc₂]; positivity
  obtain ⟨c₃, hc₃⟩ : ∃ c₃ : ℝ, c₃ = c₂ * (e / 2) * Real.exp (-(e / 2)) := ⟨_, rfl⟩
  have hc₃0 : 0 < c₃ := by rw [hc₃]; positivity
  -- the thresholds in `y`
  have hev : ∀ᶠ y : ℝ in atTop, X₁ ≤ y ∧ 1 ≤ y ∧ c₁ ≤ y ^ (ρ + δ / 2) ∧
      8 * Real.exp α' / c₁ ≤ y ^ (β - α') ∧ (M + 1) / c₃ ≤ y ^ (e / 2) := by
    refine (eventually_ge_atTop X₁).and ((eventually_ge_atTop 1).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop c₁).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      ((tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _))))
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hev
  clear hev
  -- a large window with a large signed window average
  obtain ⟨x, hxY, hint⟩ :=
    exists_window_average_ge_of_exponentialType hΦ hρ hgrow hne hδ0 (max Y₀ 0)
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hxY
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.exp x := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; exact Real.exp_pos x
  have hxy : x + 1 ≤ y := by rw [hy]; exact Real.add_one_le_exp x
  have hyY : Y₀ ≤ y := by
    calc Y₀ ≤ max Y₀ 0 := le_max_left _ _
      _ ≤ x := hxY
      _ ≤ y := by linarith
  obtain ⟨hyX₁, hy1, hyc₁, hyαβ, hyM⟩ := hY₀ y hyY
  clear hY₀
  have hlogy : Real.log y = x := by rw [hy]; exact Real.log_exp x
  have hypow : ∀ s : ℝ, y ^ s = Real.exp (s * x) := fun s => by
    rw [Real.rpow_def_of_pos hy0, hlogy, mul_comm]
  -- the window length `η` and the window count `N`
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = c₁ * Real.exp (-((ρ + δ / 2) * x)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hexpa : Real.exp (-((ρ + δ / 2) * x)) = (y ^ (ρ + δ / 2))⁻¹ := by
    rw [hypow, ← Real.exp_neg]
  have hη1 : η ≤ 1 := by
    rw [hη, hexpa, mul_inv_le_iff₀ (by positivity), one_mul]
    exact hyc₁
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈1 / η⌉₊ := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; exact Nat.ceil_pos.mpr (by positivity)
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 / N := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hNh : (N : ℝ) * h = 1 := by rw [hh]; field_simp
  have hhη : h ≤ η := by
    rw [hh, div_le_iff₀ (by positivity)]
    have h1 := Nat.le_ceil (1 / η)
    rw [← hN, div_le_iff₀ hη0] at h1
    linarith
  have hηh : η / 2 ≤ h := by
    rw [hh, le_div_iff₀ (by positivity)]
    have h1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / η)
    rw [← hN] at h1
    have h2 : (N : ℝ) ≤ 2 / η := by
      calc (N : ℝ) ≤ 1 / η + 1 := h1.le
        _ ≤ 1 / η + 1 / η := by
            gcongr
            rw [le_div_iff₀ hη0]
            linarith
        _ = 2 / η := by ring
    calc η / 2 * N ≤ η / 2 * (2 / η) := by gcongr
      _ = 1 := by field_simp
  have hh2 : h ^ 2 ≤ η ^ 2 := by gcongr
  have hη2 : η ^ 2 = c₁ ^ 2 * Real.exp (-(2 * (ρ + δ / 2) * x)) := by
    rw [hη, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hCc₁ : C * c₁ ^ 2 ≤ Real.exp (-(2 * K)) := by
    rw [hc₁, div_pow, ← Real.exp_nat_mul, mul_div_assoc', div_le_iff₀ (by positivity)]
    have hCle : C ≤ (C + 1) ^ 2 := by nlinarith
    calc C * Real.exp (((2 : ℕ) : ℝ) * -K) = Real.exp (-(2 * K)) * C := by
          rw [mul_comm]
          congr 1
          push_cast
          ring
      _ ≤ Real.exp (-(2 * K)) * (C + 1) ^ 2 := by gcongr
  -- the midpoint error of `g = Φ e^{(ρ+δ/2)·}` is at most half of the window average
  have herr : (C * Real.exp (2 * (ρ + (ρ + δ / 2)))) * Real.exp ((ρ + (ρ + δ / 2)) * (x + 2))
      * h ^ 2 / 4 ≤ Real.exp (-(δ / 2 * x)) / 2 := by
    calc (C * Real.exp (2 * (ρ + (ρ + δ / 2)))) * Real.exp ((ρ + (ρ + δ / 2)) * (x + 2))
          * h ^ 2 / 4
        ≤ (C * Real.exp (2 * (ρ + (ρ + δ / 2)))) * Real.exp ((ρ + (ρ + δ / 2)) * (x + 2))
          * η ^ 2 / 4 := by gcongr
      _ = (C * c₁ ^ 2) * (Real.exp (2 * (ρ + (ρ + δ / 2))) * Real.exp ((ρ + (ρ + δ / 2)) * (x + 2))
          * Real.exp (-(2 * (ρ + δ / 2) * x))) / 4 := by
          rw [hη2]
          ring
      _ ≤ Real.exp (-(2 * K)) * (Real.exp (2 * (ρ + (ρ + δ / 2)))
          * Real.exp ((ρ + (ρ + δ / 2)) * (x + 2)) * Real.exp (-(2 * (ρ + δ / 2) * x))) / 4 := by
          gcongr
      _ = Real.exp (-(2 * K) + (2 * (ρ + (ρ + δ / 2)) + (ρ + (ρ + δ / 2)) * (x + 2)
          + -(2 * (ρ + δ / 2) * x))) / 4 := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (-(δ / 2 * x)) / 4 := by
          gcongr
          rw [hK]
          nlinarith [hx0, hρ, hδ0]
      _ ≤ Real.exp (-(δ / 2 * x)) / 2 := by
          have := Real.exp_pos (-(δ / 2 * x))
          linarith
  -- the midpoint sum of `‖Φ‖`
  obtain ⟨m, hm⟩ : ∃ m : ℝ,
      m = Real.exp (-(δ / 2 * x)) / 2 * Real.exp (-((ρ + δ / 2) * (x + 1))) := ⟨_, rfl⟩
  have hmid : m ≤ ∑ k ∈ range N, h * ‖Φ ((x + k * h + h / 2 : ℝ) : ℂ)‖ := by
    rw [hm]
    exact sum_norm_midpoint_ge_of_window_average hΦ hC.le hρ hgrow (a := ρ + δ / 2) (by positivity)
      hx0 hh0 hNh hint herr
  have hm' : m = m₀ * Real.exp (-((ρ + δ) * x)) := by
    rw [hm, hm₀, div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  -- the second-order loss is at most half of the midpoint mass
  obtain ⟨SΦ, hSΦ⟩ : ∃ SΦ : ℝ, SΦ = (C * Real.exp (2 * ρ)) * Real.exp (ρ * (x + 2)) := ⟨_, rfl⟩
  have hSΦ0 : 0 ≤ SΦ := by rw [hSΦ]; positivity
  have hboundΦ : ∀ s : ℝ, x - 1 ≤ s → s ≤ x + 2 → ‖deriv (deriv Φ) s‖ ≤ SΦ := fun s hs1 hs2 => by
    rw [hSΦ]
    exact norm_deriv_deriv_le_on_window hΦ hC.le hρ hgrow hx0 hs1 hs2
  have hloss : SΦ * (h / 2) ^ 2 ≤ m / 2 := by
    rw [hm', hm₀, hSΦ, div_pow]
    calc C * Real.exp (2 * ρ) * Real.exp (ρ * (x + 2)) * (h ^ 2 / 2 ^ 2)
        ≤ C * Real.exp (2 * ρ) * Real.exp (ρ * (x + 2)) * (η ^ 2 / 2 ^ 2) := by gcongr
      _ = (C * c₁ ^ 2) * (Real.exp (2 * ρ) * Real.exp (ρ * (x + 2))
          * Real.exp (-(2 * (ρ + δ / 2) * x))) / 4 := by
          rw [hη2]
          ring
      _ ≤ Real.exp (-(2 * K)) * (Real.exp (2 * ρ) * Real.exp (ρ * (x + 2))
          * Real.exp (-(2 * (ρ + δ / 2) * x))) / 4 := by gcongr
      _ = Real.exp (-(2 * K) + (2 * ρ + ρ * (x + 2) + -(2 * (ρ + δ / 2) * x))) / 4 := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (-(ρ + δ / 2) + -((ρ + δ) * x)) / 4 := by
          gcongr
          rw [hK]
          nlinarith [hx0, hρ, hδ0]
      _ = Real.exp (-(ρ + δ / 2)) / 2 * Real.exp (-((ρ + δ) * x)) / 2 := by
          rw [Real.exp_add]
          ring
  -- the window-size condition `e^{(x+1)α'} ≤ y (h/2) / 2`
  have hwin : Real.exp (x + 1) ^ α' ≤ Real.exp x * (h / 2) / 2 := by
    rw [← hy]
    calc Real.exp (x + 1) ^ α' = Real.exp α' * y ^ α' := by
          rw [Real.exp_add, Real.mul_rpow (Real.exp_pos x).le (Real.exp_pos 1).le, ← hy,
            ← Real.exp_mul, one_mul, mul_comm]
      _ ≤ c₁ / 8 * y ^ β := by
          have h3 : 8 * Real.exp α' / c₁ * y ^ α' ≤ y ^ (β - α') * y ^ α' :=
            mul_le_mul_of_nonneg_right hyαβ (Real.rpow_nonneg hy0.le _)
          rw [← Real.rpow_add hy0, sub_add_cancel] at h3
          have hc₁ne : c₁ ≠ 0 := hc₁0.ne'
          calc Real.exp α' * y ^ α' = (8 * Real.exp α' / c₁ * y ^ α') * c₁ / 8 := by
                field_simp
            _ ≤ y ^ β * c₁ / 8 :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hc₁0.le) (by norm_num)
            _ = c₁ / 8 * y ^ β := by ring
      _ = η * y / 8 := by
          rw [hη, hβ, hexpa, Real.rpow_sub hy0, Real.rpow_one, div_eq_mul_inv]
          ring
      _ = (η / 2) * y / 4 := by ring
      _ ≤ h * y / 4 := by gcongr
      _ = y * (h / 2) / 2 := by ring
  -- the explicit power lower bound `M + 1 ≤ e^{−σ(x+1)} y (m/2) / (8(x+1))`
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hlog3 : x + 1 ≤ (Real.exp 1 * y) ^ (e / 2) / (e / 2) := by
    have := Real.log_le_rpow_div (by positivity : 0 ≤ Real.exp 1 * y) (by positivity : 0 < e / 2)
    rwa [Real.log_mul (Real.exp_pos 1).ne' hy0.ne', Real.log_exp, hlogy, add_comm] at this
  have hye : y ^ e = y ^ (e / 2) * y ^ (e / 2) := by
    rw [← Real.rpow_add hy0]
    congr 1
    ring
  have hexp3 : Real.exp (-(σ * (x + 1))) * Real.exp x * Real.exp (-((ρ + δ) * x))
      = Real.exp (-σ) * Real.exp ((1 - σ - ρ - δ) * x) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hid : Real.exp (-(σ * (x + 1))) * y / (8 * (x + 1)) * (m / 2) = c₂ * y ^ e / (x + 1) := by
    have h1 : Real.exp (-(σ * (x + 1))) * y * m / 16 = c₂ * y ^ e := by
      rw [hm', hc₂, hypow, he, hy]
      linear_combination (m₀ / 16) * hexp3
    rw [← h1, div_mul_div_comm, div_div]
    congr 1
    ring
  have hM : M + 1 ≤ Real.exp (-(σ * (x + 1))) * Real.exp x / (8 * (x + 1)) * (m / 2) := by
    rw [← hy, hid]
    calc M + 1 ≤ c₃ * y ^ (e / 2) := by
          rw [mul_comm]
          exact (div_le_iff₀ hc₃0).mp hyM
      _ = c₂ * y ^ e / ((Real.exp 1 * y) ^ (e / 2) / (e / 2)) := by
          rw [hc₃, Real.mul_rpow (Real.exp_pos 1).le hy0.le, ← Real.exp_mul, one_mul, hye,
            Real.exp_neg]
          field_simp
      _ ≤ c₂ * y ^ e / (x + 1) := div_le_div_of_nonneg_left (by positivity) hx1 hlog3
  exact exists_primeLogWeightedSum_gt_of_midpoint_data hΦ hσ hx0 hh0 hNh hθ
    (le_trans (by norm_num) hα'7.le) (hy ▸ hyX₁) hwin hSΦ0 hboundΦ hmid hloss hM

end RHTower
