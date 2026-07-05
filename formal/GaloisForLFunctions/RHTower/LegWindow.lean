/-
# LegWindow — the lattice comparison via the paired sum

Setting: `φ = rphi = csch²·coth` on two arithmetic progressions with common step `δ/2`:
the *ahead* points `a_k = (θ + k)·δ/2` for `k < M` and the *behind* points
`b_k = (1 − θ + k)·δ/2` for `k < N`, with `0 < θ < 1/2` and `M ≤ N`. The object of study is
the sign of `Σ_{k<N} φ(b_k) − Σ_{k<M} φ(a_k)`.

`LegComparison` proves the ahead sum wins when `θ ≤ 1/8` using only the `k = 0` pair. This
module treats general `θ < 1/2` by summing ALL `M` pair gains through the mean value theorem
applied to `φ' = −(2csch² + 3csch⁴)`, and shows the phenomenon is sharp:

* `dW_dtheta_neg_seam` — if `(1 − 2θ)·M·δ² > 1` the ahead sum wins for every `N ≥ M`.
* `dW_dtheta_neg_window` — if `3(1 − 2θ)·δ·[coth((1−θ)δ/2) − coth((1−θ+M)δ/2)] > 1` the
  ahead sum wins for every `N ≥ M`; as `δ → 0` this condition tends to
  `6(1−2θ)·M/((1−θ)(1−θ+M)) > 1`, so it covers `θ` up to `5/11` for large `M`.
* `l1_fails_near_crossing` — some hypothesis of this kind is NECESSARY: for `θ` close enough
  to `1/2` (exhibited at `δ = 1, M = 1, N = 2`) the inequality reverses, because every pair
  gain `φ(a_k) − φ(b_k)` vanishes as `θ → 1/2` while the unpaired behind terms do not.

Mechanism (exact, no integrals): the MVT pair gain
`φ(a_k) − φ(b_k) ≥ (1−2θ)(δ/2)·(2csch²(b_k) + 3csch⁴(b_k))` (`rphi_pair_gain`); the unpaired
behind tail telescopes against the antiderivative `csch²/2` of `−φ` (`rphi_tail_le`); the
paired `csch²` sum telescopes against the antiderivative `−coth` of `csch²`
(`csch_sq_sum_ge`). Head and tail then share the common factor `csch²((M−θ)δ/2)` and the
hypothesis of each theorem is exactly the surviving ratio.
-/
import GaloisForLFunctions.RHTower.LegComparison
import GaloisForLFunctions.RHTower.SpurLattice

noncomputable section

namespace RHTower

open Finset Filter

/-- `coth² = 1 + csch²`, from `cosh² − sinh² = 1`. -/
theorem rcoth_sq_eq {x : ℝ} (hx : 0 < x) : (rcoth x) ^ 2 = 1 + (rcsch x) ^ 2 := by
  have hs := (sinh_pos_of_pos hx).ne'
  simp only [rcoth, rcsch]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- `φ' = −(2csch² + 3csch⁴)` on `(0, ∞)`: product rule on `φ = csch²·coth`, then
`coth² = 1 + csch²`. -/
theorem rphi_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt rphi (-(2 * (rcsch x) ^ 2 + 3 * (rcsch x) ^ 4)) x := by
  have hc := rcoth_sq_eq hx
  have h1 : HasDerivAt (fun t => (rcsch t) ^ 2 * rcoth t)
      (((2 : ℕ) : ℝ) * rcsch x ^ (2 - 1) * (-rcoth x * rcsch x) * rcoth x
        + rcsch x ^ 2 * -(rcsch x) ^ 2) x :=
    ((rcsch_hasDerivAt hx.ne').pow 2).mul (rcoth_hasDerivAt hx.ne')
  have heq : ((2 : ℕ) : ℝ) * rcsch x ^ (2 - 1) * (-rcoth x * rcsch x) * rcoth x
      + rcsch x ^ 2 * -(rcsch x) ^ 2
      = -(2 * (rcsch x) ^ 2 + 3 * (rcsch x) ^ 4) := by
    push_cast
    nlinarith [hc, sq_nonneg (rcsch x)]
  rw [heq] at h1
  exact h1

/-- The energy density `2csch² + 3csch⁴` is antitone on `(0, ∞)`. -/
theorem csch_energy_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    2 * (rcsch t) ^ 2 + 3 * (rcsch t) ^ 4 ≤ 2 * (rcsch s) ^ 2 + 3 * (rcsch s) ^ 4 := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have h1 : rcsch t ≤ rcsch s := by
    rcases eq_or_lt_of_le hst with h | h
    · rw [h]
    · exact (rcsch_strictAntiOn_pos (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr ht) h).le
  have h2 := rcsch_pos_of_pos ht
  have h3 : (rcsch t) ^ 2 ≤ (rcsch s) ^ 2 := pow_le_pow_left₀ h2.le h1 2
  have h4 : (rcsch t) ^ 4 ≤ (rcsch s) ^ 4 := pow_le_pow_left₀ h2.le h1 4
  linarith

/-- **Pair gain**: for `0 < a < b`,
`φ(a) − φ(b) ≥ (b − a)·(2csch²(b) + 3csch⁴(b))`. MVT for `φ` on `[a, b]` plus antitonicity
of `−φ' = 2csch² + 3csch⁴`, evaluated at the right endpoint. -/
theorem rphi_pair_gain {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (b - a) * (2 * (rcsch b) ^ 2 + 3 * (rcsch b) ^ 4) ≤ rphi a - rphi b := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hcont : ContinuousOn rphi (Set.Icc a b) := fun y hy =>
    (rphi_hasDerivAt (lt_of_lt_of_le ha hy.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ y ∈ Set.Ioo a b,
      HasDerivAt rphi (-(2 * (rcsch y) ^ 2 + 3 * (rcsch y) ^ 4)) y := fun y hy =>
    rphi_hasDerivAt (lt_trans ha hy.1)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope rphi
    (fun y => -(2 * (rcsch y) ^ 2 + 3 * (rcsch y) ^ 4)) hab hcont hderiv
  have hc0 : 0 < c := lt_trans ha hc.1
  rw [eq_div_iff hba.ne'] at hslope
  have hkey : rphi a - rphi b = (b - a) * (2 * (rcsch c) ^ 2 + 3 * (rcsch c) ^ 4) := by
    linear_combination hslope
  rw [hkey]
  exact mul_le_mul_of_nonneg_left (csch_energy_antitone hc0 hc.2.le) hba.le

/-- **Coth step**: for `0 < a < b`, `coth(a) − coth(b) ≤ (b − a)·csch²(a)`. MVT for `coth`
plus antitonicity of `csch²`, evaluated at the left endpoint. -/
theorem rcoth_pair_le {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    rcoth a - rcoth b ≤ (b - a) * (rcsch a) ^ 2 := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hcont : ContinuousOn rcoth (Set.Icc a b) := fun y hy =>
    (rcoth_hasDerivAt (lt_of_lt_of_le ha hy.1).ne').continuousAt.continuousWithinAt
  have hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt rcoth (-(rcsch y) ^ 2) y := fun y hy =>
    rcoth_hasDerivAt (lt_trans ha hy.1).ne'
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope rcoth
    (fun y => -(rcsch y) ^ 2) hab hcont hderiv
  have hc0 : 0 < c := lt_trans ha hc.1
  rw [eq_div_iff hba.ne'] at hslope
  have hkey : rcoth a - rcoth b = (b - a) * (rcsch c) ^ 2 := by
    linear_combination hslope
  rw [hkey]
  have hcsch : (rcsch c) ^ 2 ≤ (rcsch a) ^ 2 := by
    have h1 : rcsch c ≤ rcsch a :=
      (rcsch_strictAntiOn_pos (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hc0) hc.1).le
    exact pow_le_pow_left₀ (rcsch_pos_of_pos hc0).le h1 2
  exact mul_le_mul_of_nonneg_left hcsch hba.le

/-- **Tail step**: for `0 < a < b`, `2(b − a)·φ(b) ≤ csch²(a) − csch²(b)`. MVT for `csch²`
(whose derivative is `−2φ`) plus antitonicity of `φ`, evaluated at the right endpoint. -/
theorem rphi_pair_tail {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    2 * (b - a) * rphi b ≤ (rcsch a) ^ 2 - (rcsch b) ^ 2 := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hcont : ContinuousOn (fun t => (rcsch t) ^ 2) (Set.Icc a b) := fun y hy =>
    (rcsch_sq_hasDerivAt (lt_of_lt_of_le ha hy.1).ne').continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => (rcsch t) ^ 2)
    (fun y => -2 * rphi y) hab hcont (fun y hy => rcsch_sq_hasDerivAt (lt_trans ha hy.1).ne')
  have hc0 : 0 < c := lt_trans ha hc.1
  rw [eq_div_iff hba.ne'] at hslope
  have hkey : (rcsch a) ^ 2 - (rcsch b) ^ 2 = 2 * (b - a) * rphi c := by
    linear_combination hslope
  rw [hkey]
  have hphi : rphi b ≤ rphi c := by
    have := rphi_strictAntiOn_pos.antitoneOn (Set.mem_Ioi.mpr hc0)
      (Set.mem_Ioi.mpr (lt_trans hc0 hc.2)) hc.2.le
    linarith
  nlinarith [hphi, hba]

/-- **The csch² sum telescopes against coth**: for `x, h > 0`,
`coth(x·h) − coth((x+M)·h) ≤ h·Σ_{k<M} csch²((x+k)h)`. Each coth step is one `rcoth_pair_le`. -/
theorem csch_sq_sum_ge {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (M : ℕ) :
    rcoth (x * h) - rcoth ((x + M) * h) ≤ h * ∑ k ∈ range M, (rcsch ((x + k) * h)) ^ 2 := by
  have hstep : ∀ k ∈ range M,
      rcoth ((x + k) * h) - rcoth ((x + (k + 1 : ℕ)) * h) ≤ h * (rcsch ((x + k) * h)) ^ 2 := by
    intro k _
    have ha : 0 < (x + (k : ℝ)) * h := by positivity
    have hab : (x + (k : ℝ)) * h < (x + ((k : ℝ) + 1)) * h := by nlinarith
    have hpair := rcoth_pair_le ha hab
    have hba : (x + ((k : ℝ) + 1)) * h - (x + (k : ℝ)) * h = h := by ring
    rw [hba] at hpair
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact hpair
  calc rcoth (x * h) - rcoth ((x + M) * h)
      = ∑ k ∈ range M, (rcoth ((x + k) * h) - rcoth ((x + (k + 1 : ℕ)) * h)) := by
        rw [Finset.sum_range_sub' (fun k => rcoth ((x + (k : ℝ)) * h)) M]
        norm_num
    _ ≤ ∑ k ∈ range M, h * (rcsch ((x + k) * h)) ^ 2 := Finset.sum_le_sum hstep
    _ = h * ∑ k ∈ range M, (rcsch ((x + k) * h)) ^ 2 := by rw [Finset.mul_sum]

/-- **The φ tail telescopes against csch²/2**: for `h > 0` and `x + M − 1 > 0`,
`2h·Σ_{k∈[M,N)} φ((x+k)h) ≤ csch²((x+M−1)h)`. Each step is one `rphi_pair_tail`; the bound
is uniform in `N`. -/
theorem rphi_tail_le {x h : ℝ} (hh : 0 < h) {M N : ℕ}
    (hxM : 0 < x + (M : ℝ) - 1) :
    2 * h * ∑ k ∈ Ico M N, rphi ((x + k) * h) ≤ (rcsch ((x + (M : ℝ) - 1) * h)) ^ 2 := by
  set g : ℕ → ℝ := fun i => (rcsch ((x + (M : ℝ) - 1 + i) * h)) ^ 2 with hg
  have hterm : ∀ i ∈ range (N - M),
      2 * h * rphi ((x + ((M + i : ℕ) : ℝ)) * h) ≤ g i - g (i + 1) := by
    intro i _
    have ha : 0 < (x + (M : ℝ) - 1 + i) * h := by
      have : (0 : ℝ) ≤ (i : ℝ) := by positivity
      nlinarith
    have hab : (x + (M : ℝ) - 1 + (i : ℝ)) * h < (x + (M : ℝ) - 1 + ((i : ℝ) + 1)) * h := by
      nlinarith
    have hpair := rphi_pair_tail ha hab
    have hba : (x + (M : ℝ) - 1 + ((i : ℝ) + 1)) * h - (x + (M : ℝ) - 1 + (i : ℝ)) * h = h := by
      ring
    rw [hba] at hpair
    have harg : (x + ((M + i : ℕ) : ℝ)) * h = (x + (M : ℝ) - 1 + ((i : ℝ) + 1)) * h := by
      push_cast; ring
    rw [harg]
    have hgi : g (i + 1) = (rcsch ((x + (M : ℝ) - 1 + ((i : ℝ) + 1)) * h)) ^ 2 := by
      simp only [hg]
      push_cast
      ring_nf
    rw [hgi]
    simp only [hg]
    linarith [hpair]
  have hsum : ∑ i ∈ range (N - M), (g i - g (i + 1)) = g 0 - g (N - M) :=
    Finset.sum_range_sub' g (N - M)
  have hgN : 0 ≤ g (N - M) := by simp only [hg]; positivity
  have hg0 : g 0 = (rcsch ((x + (M : ℝ) - 1) * h)) ^ 2 := by
    simp only [hg, Nat.cast_zero, add_zero]
  calc 2 * h * ∑ k ∈ Ico M N, rphi ((x + k) * h)
      = ∑ i ∈ range (N - M), 2 * h * rphi ((x + ((M + i : ℕ) : ℝ)) * h) := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    _ ≤ ∑ i ∈ range (N - M), (g i - g (i + 1)) := Finset.sum_le_sum hterm
    _ = g 0 - g (N - M) := hsum
    _ ≤ (rcsch ((x + (M : ℝ) - 1) * h)) ^ 2 := by rw [← hg0]; linarith [hgN]

/-- **The ahead sum wins whenever `(1 − 2θ)·M·δ² > 1`** (any `N ≥ M`). Every pair
contributes at least `(1−2θ)(δ/2)·2csch²(b_{M−1})` (pair gain + antitonicity), so the head
gain is at least `M(1−2θ)δ·csch²(b_{M−1})`; the unpaired tail is at most
`csch²(b_{M−1})/δ` (`rphi_tail_le`); the common factor `csch²(b_{M−1})` cancels and the
hypothesis is the surviving ratio. -/
theorem dW_dtheta_neg_seam {θ δ : ℝ} {M N : ℕ} (hMN : M ≤ N) (hM1 : 1 ≤ M)
    (hθ0 : 0 < θ) (hθhalf : θ < 1 / 2) (hδ0 : 0 < δ)
    (hB : 1 < (1 - 2 * θ) * M * δ ^ 2) :
    (∑ k ∈ range N, rphi ((1 - θ + k) * (δ / 2)))
      < ∑ k ∈ range M, rphi ((θ + k) * (δ / 2)) := by
  have hM : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  set fa : ℕ → ℝ := fun k => rphi ((θ + k) * (δ / 2)) with hfa
  set fb : ℕ → ℝ := fun k => rphi ((1 - θ + k) * (δ / 2)) with hfb
  have h2θ : (0 : ℝ) < 1 - 2 * θ := by linarith
  have hbM : (0 : ℝ) < ((M : ℝ) - θ) * (δ / 2) := by nlinarith
  have hcsch2pos : 0 < (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2 := by
    have := rcsch_pos_of_pos hbM
    positivity
  -- per-pair gain, uniform over k < M
  have hterm : ∀ k ∈ range M,
      (1 - 2 * θ) * δ * (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2 ≤ fa k - fb k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkM : (k : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hk
    have ha0 : 0 < (θ + (k : ℝ)) * (δ / 2) := by positivity
    have hab : (θ + (k : ℝ)) * (δ / 2) < (1 - θ + (k : ℝ)) * (δ / 2) := by nlinarith
    have hgain := rphi_pair_gain ha0 hab
    have hba : (1 - θ + (k : ℝ)) * (δ / 2) - (θ + (k : ℝ)) * (δ / 2)
        = (1 - 2 * θ) * (δ / 2) := by ring
    rw [hba] at hgain
    have hb0 : 0 < (1 - θ + (k : ℝ)) * (δ / 2) := by
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      nlinarith
    have hle : (1 - θ + (k : ℝ)) * (δ / 2) ≤ ((M : ℝ) - θ) * (δ / 2) := by nlinarith
    have hmono : (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2
        ≤ (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2 := by
      rcases eq_or_lt_of_le hle with h | h
      · rw [h]
      · have h1 : rcsch (((M : ℝ) - θ) * (δ / 2)) ≤ rcsch ((1 - θ + (k : ℝ)) * (δ / 2)) :=
          (rcsch_strictAntiOn_pos (Set.mem_Ioi.mpr hb0) (Set.mem_Ioi.mpr hbM) h).le
        exact pow_le_pow_left₀ (rcsch_pos_of_pos hbM).le h1 2
    have hcsch4 : 0 ≤ (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 4 := by positivity
    have hchain : (1 - 2 * θ) * δ * (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2
        ≤ (1 - 2 * θ) * (δ / 2)
          * (2 * (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2
             + 3 * (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 4) := by
      nlinarith [mul_le_mul_of_nonneg_left hmono (mul_pos h2θ hδ0).le,
        mul_nonneg (mul_nonneg h2θ.le hδ0.le) hcsch4]
    simp only [hfa, hfb]
    linarith [hchain, hgain]
  -- head sum: M copies of the uniform bound
  have hheadsum : (M : ℝ) * ((1 - 2 * θ) * δ * (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2)
      ≤ ∑ k ∈ range M, (fa k - fb k) := by
    have h := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  -- tail, telescoped
  have htail : (∑ k ∈ Ico M N, fb k) ≤ (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2 / δ := by
    have h2 := rphi_tail_le (x := 1 - θ) (h := δ / 2) (N := N) (M := M) (by positivity)
      (by nlinarith : (0 : ℝ) < 1 - θ + (M : ℝ) - 1)
    rw [show (1 - θ + (M : ℝ) - 1) * (δ / 2) = ((M : ℝ) - θ) * (δ / 2) from by ring] at h2
    simp only [hfb]
    rw [le_div_iff₀ hδ0]
    nlinarith [h2]
  refine l1_neg_of_head_gt_tail hMN fa fb ?_
  have hbeat : (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2 / δ
      < (M : ℝ) * ((1 - 2 * θ) * δ * (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2) := by
    rw [div_lt_iff₀ hδ0]
    nlinarith [mul_pos hcsch2pos (by linarith : (0 : ℝ) < (1 - 2 * θ) * M * δ ^ 2 - 1)]
  calc (∑ k ∈ Ico M N, fb k)
      ≤ (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2 / δ := htail
    _ < (M : ℝ) * ((1 - 2 * θ) * δ * (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2) := hbeat
    _ ≤ ∑ k ∈ range M, (fa k - fb k) := hheadsum

/-- **The ahead sum wins whenever
`3(1 − 2θ)·δ·[coth((1−θ)δ/2) − coth((1−θ+M)δ/2)] > 1`** (any `N ≥ M`). The `csch⁴` part of
every pair gain is bounded below by `csch²(b_{M−1})·csch²(b_k)`; the `csch²` sum telescopes
to the coth difference (`csch_sq_sum_ge`); the unpaired tail is at most `csch²(b_{M−1})/δ`.
As `δ → 0` the coth difference grows like `2M/((1−θ)(1−θ+M)δ)`, so the hypothesis survives
at every lattice scale. -/
theorem dW_dtheta_neg_window {θ δ : ℝ} {M N : ℕ} (hMN : M ≤ N) (hM1 : 1 ≤ M)
    (hθ0 : 0 < θ) (hθhalf : θ < 1 / 2) (hδ0 : 0 < δ)
    (hA : 1 < 3 * (1 - 2 * θ) * δ
      * (rcoth ((1 - θ) * (δ / 2)) - rcoth ((1 - θ + M) * (δ / 2)))) :
    (∑ k ∈ range N, rphi ((1 - θ + k) * (δ / 2)))
      < ∑ k ∈ range M, rphi ((θ + k) * (δ / 2)) := by
  have hM : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  set fa : ℕ → ℝ := fun k => rphi ((θ + k) * (δ / 2)) with hfa
  set fb : ℕ → ℝ := fun k => rphi ((1 - θ + k) * (δ / 2)) with hfb
  have h2θ : (0 : ℝ) < 1 - 2 * θ := by linarith
  have hbM : (0 : ℝ) < ((M : ℝ) - θ) * (δ / 2) := by nlinarith
  set cM : ℝ := (rcsch (((M : ℝ) - θ) * (δ / 2))) ^ 2 with hcM
  have hcMpos : 0 < cM := by
    have := rcsch_pos_of_pos hbM
    simp only [hcM]
    positivity
  -- per-pair: fa k − fb k ≥ 3(1−2θ)(δ/2)·cM·csch²(b_k)
  have hterm : ∀ k ∈ range M,
      3 * (1 - 2 * θ) * (δ / 2) * cM * (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2
        ≤ fa k - fb k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkM : (k : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hk
    have ha0 : 0 < (θ + (k : ℝ)) * (δ / 2) := by positivity
    have hab : (θ + (k : ℝ)) * (δ / 2) < (1 - θ + (k : ℝ)) * (δ / 2) := by nlinarith
    have hgain := rphi_pair_gain ha0 hab
    have hba : (1 - θ + (k : ℝ)) * (δ / 2) - (θ + (k : ℝ)) * (δ / 2)
        = (1 - 2 * θ) * (δ / 2) := by ring
    rw [hba] at hgain
    have hb0 : 0 < (1 - θ + (k : ℝ)) * (δ / 2) := by
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      nlinarith
    have hle : (1 - θ + (k : ℝ)) * (δ / 2) ≤ ((M : ℝ) - θ) * (δ / 2) := by nlinarith
    have hmono : cM ≤ (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2 := by
      simp only [hcM]
      rcases eq_or_lt_of_le hle with h | h
      · rw [h]
      · have h1 : rcsch (((M : ℝ) - θ) * (δ / 2)) ≤ rcsch ((1 - θ + (k : ℝ)) * (δ / 2)) :=
          (rcsch_strictAntiOn_pos (Set.mem_Ioi.mpr hb0) (Set.mem_Ioi.mpr hbM) h).le
        exact pow_le_pow_left₀ (rcsch_pos_of_pos hbM).le h1 2
    have hck : 0 ≤ (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2 := by positivity
    -- csch⁴(b_k) = (csch²(b_k))² ≥ cM·csch²(b_k); the 2csch² part of the gain is dropped
    have hchain : 3 * (1 - 2 * θ) * (δ / 2) * cM * (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2
        ≤ (1 - 2 * θ) * (δ / 2)
          * (2 * (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2
             + 3 * (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 4) := by
      nlinarith [mul_le_mul_of_nonneg_right hmono hck, mul_pos h2θ hδ0,
        mul_nonneg (mul_pos h2θ hδ0).le hck]
    simp only [hfa, hfb]
    linarith [hchain, hgain]
  have hsum := Finset.sum_le_sum hterm
  have hfactor : ∑ k ∈ range M,
      3 * (1 - 2 * θ) * (δ / 2) * cM * (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2
      = 3 * (1 - 2 * θ) * cM
        * ((δ / 2) * ∑ k ∈ range M, (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hcothtel := csch_sq_sum_ge (x := 1 - θ) (h := δ / 2)
    (by linarith : (0 : ℝ) < 1 - θ) (by positivity) M
  have hheadsum : 3 * (1 - 2 * θ) * cM
      * (rcoth ((1 - θ) * (δ / 2)) - rcoth ((1 - θ + M) * (δ / 2)))
      ≤ ∑ k ∈ range M, (fa k - fb k) := by
    have hc3 : (0 : ℝ) ≤ 3 * (1 - 2 * θ) * cM := by positivity
    calc 3 * (1 - 2 * θ) * cM
        * (rcoth ((1 - θ) * (δ / 2)) - rcoth ((1 - θ + M) * (δ / 2)))
        ≤ 3 * (1 - 2 * θ) * cM
          * ((δ / 2) * ∑ k ∈ range M, (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2) :=
          mul_le_mul_of_nonneg_left hcothtel hc3
      _ = ∑ k ∈ range M,
          3 * (1 - 2 * θ) * (δ / 2) * cM * (rcsch ((1 - θ + (k : ℝ)) * (δ / 2))) ^ 2 := by
          rw [hfactor]
      _ ≤ ∑ k ∈ range M, (fa k - fb k) := hsum
  have htail : (∑ k ∈ Ico M N, fb k) ≤ cM / δ := by
    have h2 := rphi_tail_le (x := 1 - θ) (h := δ / 2) (N := N) (M := M) (by positivity)
      (by nlinarith : (0 : ℝ) < 1 - θ + (M : ℝ) - 1)
    rw [show (1 - θ + (M : ℝ) - 1) * (δ / 2) = ((M : ℝ) - θ) * (δ / 2) from by ring] at h2
    simp only [hfb, hcM]
    rw [le_div_iff₀ hδ0]
    nlinarith [h2]
  refine l1_neg_of_head_gt_tail hMN fa fb ?_
  have hbeat : cM / δ < 3 * (1 - 2 * θ) * cM
      * (rcoth ((1 - θ) * (δ / 2)) - rcoth ((1 - θ + M) * (δ / 2))) := by
    rw [div_lt_iff₀ hδ0]
    nlinarith [mul_pos hcMpos (by linarith : (0 : ℝ) < 3 * (1 - 2 * θ) * δ
      * (rcoth ((1 - θ) * (δ / 2)) - rcoth ((1 - θ + M) * (δ / 2))) - 1)]
  calc (∑ k ∈ Ico M N, fb k) ≤ cM / δ := htail
    _ < 3 * (1 - 2 * θ) * cM
        * (rcoth ((1 - θ) * (δ / 2)) - rcoth ((1 - θ + M) * (δ / 2))) := hbeat
    _ ≤ ∑ k ∈ range M, (fa k - fb k) := hheadsum

/-- **Near the crossing the comparison REVERSES**: at `δ = 1, M = 1, N = 2` there is
`θ ∈ (0, 1/2)` with the behind sum strictly exceeding the ahead sum. At `θ = 1/2` the single
pair cancels exactly (`a_0 = b_0 = 1/4`) while the unpaired behind term `φ(3/4) > 0`
survives; continuity of `φ` extends the reversal to `θ < 1/2`. Hence any theorem giving the
ahead sum the win on `θ < 1/2` MUST couple `1 − 2θ` to the configuration, as
`dW_dtheta_neg_seam` and `dW_dtheta_neg_window` do. -/
theorem l1_fails_near_crossing :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 2 ∧
      (∑ k ∈ range 1, rphi ((θ + k) * ((1 : ℝ) / 2)))
        < ∑ k ∈ range 2, rphi ((1 - θ + k) * ((1 : ℝ) / 2)) := by
  set f : ℝ → ℝ := fun θ =>
    (rphi ((1 - θ) * (1 / 2)) + rphi ((2 - θ) * (1 / 2))) - rphi (θ * (1 / 2)) with hf
  -- continuity at θ = 1/2 (all three arguments are positive there)
  have hcont : ContinuousAt f (1 / 2) := by
    have haff1 : ContinuousAt (fun θ : ℝ => (1 - θ) * (1 / 2)) (1 / 2) := by fun_prop
    have haff2 : ContinuousAt (fun θ : ℝ => (2 - θ) * (1 / 2)) (1 / 2) := by fun_prop
    have haff3 : ContinuousAt (fun θ : ℝ => θ * (1 / 2)) (1 / 2) := by fun_prop
    have hr1 : ContinuousAt rphi ((fun θ : ℝ => (1 - θ) * (1 / 2)) (1 / 2)) :=
      (rphi_hasDerivAt (by norm_num)).continuousAt
    have hr2 : ContinuousAt rphi ((fun θ : ℝ => (2 - θ) * (1 / 2)) (1 / 2)) :=
      (rphi_hasDerivAt (by norm_num)).continuousAt
    have hr3 : ContinuousAt rphi ((fun θ : ℝ => θ * (1 / 2)) (1 / 2)) :=
      (rphi_hasDerivAt (by norm_num)).continuousAt
    have c1 : ContinuousAt (fun θ : ℝ => rphi ((1 - θ) * (1 / 2))) (1 / 2) :=
      ContinuousAt.comp (g := rphi) (f := fun θ : ℝ => (1 - θ) * (1 / 2)) hr1 haff1
    have c2 : ContinuousAt (fun θ : ℝ => rphi ((2 - θ) * (1 / 2))) (1 / 2) :=
      ContinuousAt.comp (g := rphi) (f := fun θ : ℝ => (2 - θ) * (1 / 2)) hr2 haff2
    have c3 : ContinuousAt (fun θ : ℝ => rphi (θ * (1 / 2))) (1 / 2) :=
      ContinuousAt.comp (g := rphi) (f := fun θ : ℝ => θ * (1 / 2)) hr3 haff3
    exact (c1.add c2).sub c3
  -- positivity at θ = 1/2: the pair cancels, φ(3/4) survives
  have hpos : 0 < f (1 / 2) := by
    have e1 : ((1 : ℝ) - 1 / 2) * (1 / 2) = 1 / 2 * (1 / 2) := by norm_num
    have hval : f (1 / 2) = rphi ((2 - (1 : ℝ) / 2) * (1 / 2)) := by
      simp only [hf, e1]
      ring
    rw [hval]
    exact rphi_pos_of_pos (by norm_num)
  -- extract θ < 1/2 with f θ > 0, staying above 1/4
  have hev : ∀ᶠ x in nhdsWithin (1 / 2 : ℝ) (Set.Iio (1 / 2)), 0 < f x :=
    nhdsWithin_le_nhds (hcont.eventually (eventually_gt_nhds hpos))
  have hev4 : ∀ᶠ x in nhdsWithin (1 / 2 : ℝ) (Set.Iio (1 / 2)), (1 : ℝ) / 4 < x :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num))
  have hmem : ∀ᶠ x in nhdsWithin (1 / 2 : ℝ) (Set.Iio (1 / 2)), x ∈ Set.Iio (1 / 2 : ℝ) :=
    eventually_mem_nhdsWithin
  obtain ⟨θ, ⟨hθf, hθ4⟩, hθlt⟩ := ((hev.and hev4).and hmem).exists
  refine ⟨θ, by linarith, Set.mem_Iio.mp hθlt, ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    add_zero, zero_add]
  rw [show (1 - θ + 1 : ℝ) = 2 - θ from by ring]
  simp only [hf] at hθf
  linarith [hθf]

end RHTower
