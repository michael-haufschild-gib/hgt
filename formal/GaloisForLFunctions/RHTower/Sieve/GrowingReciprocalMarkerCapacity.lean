import GaloisForLFunctions.RHTower.Sieve.GrowingMarkerCountExplicit
import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerSubpowerSchedule

/-!
# Growing-block reciprocal-marker capacity

For `log h = o(log X)` and `log h/(log log X)² → ∞` the window `(X, X + √X h]` contains
`≫ √X h log h/log X` integers of each Möbius sign, each of the form `a·p` with `p` a prime above
`√X > a` and `μ(a) = -μ(n)`.

The construction is a ladder of `≍ log h` dyadic blocks of reciprocal markers, grouped into
super-blocks of a fixed size.  The markers over exceptional starts are discarded inside each
super-block by the mean-square device, whose loss is governed by the fibre second moment — the
shifted prime pairs of the two-dimensional sieve — so a bounded *density* of exceptional starts
suffices.  That density comes from the Matomäki–Radziwiłł mean square for `μ` at every length,
made uniform in the length by `Sieve/BadOuterUniformWindow`.  No rate of decay is needed.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology

noncomputable section

/-- The smallest start of the ladder: every block window is then at least `(log Z)⁴`. -/
def gmStart (Z H : ℕ) : ℕ := ⌈4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) / (H : ℝ)⌉₊ + 2

/-- The largest admissible top start: `C₂ m² log Z ≤ Z`. -/
def gmTop (C₂ : ℝ) (Z : ℕ) : ℕ := Nat.sqrt ⌊(Z : ℝ) / (C₂ * Real.log Z)⌋₊

/-- The number of super-blocks of `K₀+1` dyadic blocks. -/
def gmBlocks (K₀ : ℕ) (C₂ : ℝ) (Z H : ℕ) : ℕ :=
  Nat.log 2 (gmTop C₂ Z / gmStart Z H) / (K₀ + 1)

theorem two_le_gmStart (Z H : ℕ) : 2 ≤ gmStart Z H := by
  rw [gmStart]; omega

theorem gmStart_lower {Z H : ℕ} (hH : 0 < H) :
    4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) ≤ (H : ℝ) * (gmStart Z H : ℝ) := by
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hc := Nat.le_ceil (4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) / (H : ℝ))
  have hu : (⌈4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) / (H : ℝ)⌉₊ : ℝ) ≤ (gmStart Z H : ℝ) := by
    rw [gmStart]; push_cast; linarith
  rw [div_le_iff₀ hHR] at hc
  nlinarith [hc, hu, hHR]

theorem gmStart_upper {Z H : ℕ}
    (h3 : 3 ≤ 4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) / (H : ℝ)) :
    (gmStart Z H : ℝ) ≤ 2 * (4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) / (H : ℝ)) := by
  have hc := Nat.ceil_lt_add_one (le_trans (by norm_num) h3 :
    (0 : ℝ) ≤ 4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) / (H : ℝ))
  rw [gmStart]; push_cast
  linarith

theorem gmTop_sq_le {C₂ : ℝ} {Z : ℕ} (hpos : 0 < C₂ * Real.log Z) :
    ((gmTop C₂ Z : ℕ) : ℝ) ^ (2 : ℕ) * (C₂ * Real.log Z) ≤ (Z : ℝ) := by
  have h1 : ((gmTop C₂ Z) ^ 2 : ℕ) ≤ ⌊(Z : ℝ) / (C₂ * Real.log Z)⌋₊ := Nat.sqrt_le' _
  have h2 : ((⌊(Z : ℝ) / (C₂ * Real.log Z)⌋₊ : ℕ) : ℝ) ≤ (Z : ℝ) / (C₂ * Real.log Z) :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hpos.le)
  have h3 : ((gmTop C₂ Z : ℕ) : ℝ) ^ (2 : ℕ) ≤ (Z : ℝ) / (C₂ * Real.log Z) := by
    have : (((gmTop C₂ Z) ^ 2 : ℕ) : ℝ) ≤ ((⌊(Z : ℝ) / (C₂ * Real.log Z)⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at this
    linarith
  rwa [le_div_iff₀ hpos] at h3

theorem gmTop_lower {C₂ : ℝ} {Z : ℕ}
    (h9 : 9 ≤ (Z : ℝ) / (C₂ * Real.log Z)) :
    Real.sqrt ((Z : ℝ) / (C₂ * Real.log Z)) / 2 ≤ ((gmTop C₂ Z : ℕ) : ℝ) := by
  set z : ℝ := (Z : ℝ) / (C₂ * Real.log Z) with hz
  have hlt : ⌊z⌋₊ < (gmTop C₂ Z + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hfl : z - 1 < ((⌊z⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one z
    linarith
  have hltR : ((⌊z⌋₊ : ℕ) : ℝ) < (((gmTop C₂ Z : ℕ) : ℝ) + 1) ^ (2 : ℕ) := by
    exact_mod_cast hlt
  set s : ℝ := Real.sqrt z with hs
  have hs3 : 3 ≤ s := by
    rw [hs, show (3 : ℝ) = Real.sqrt 9 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h9
  have hss : s * s = z := Real.mul_self_sqrt (by linarith)
  by_contra hcon
  push Not at hcon
  have hq0 : (0 : ℝ) ≤ ((gmTop C₂ Z : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [hcon, hltR, hfl, hss, hs3, hq0]

/-- **The top start of the ladder is admissible.** -/
theorem ladderTop_le_gmTop (K₀ : ℕ) (C₂ : ℝ) (Z H : ℕ)
    (hR : 1 ≤ gmTop C₂ Z / gmStart Z H) :
    2 ^ (gmBlocks K₀ C₂ Z H * (K₀ + 1)) * gmStart Z H ≤ gmTop C₂ Z := by
  set R : ℕ := gmTop C₂ Z / gmStart Z H with hRdef
  have hn : gmBlocks K₀ C₂ Z H * (K₀ + 1) ≤ Nat.log 2 R := by
    rw [gmBlocks, ← hRdef]
    exact Nat.div_mul_le_self _ _
  have hpow : 2 ^ (gmBlocks K₀ C₂ Z H * (K₀ + 1)) ≤ R :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hn) (Nat.pow_log_le_self 2 (by omega))
  calc 2 ^ (gmBlocks K₀ C₂ Z H * (K₀ + 1)) * gmStart Z H ≤ R * gmStart Z H :=
        Nat.mul_le_mul_right _ hpow
    _ ≤ gmTop C₂ Z := Nat.div_mul_le_self _ _

/-- **The number of super-blocks from a lower bound on the ladder span.**  If the span
`gmTop/gmStart` is at least `√h`, there are at least `(log h/(2 log 2) − 1)/(K₀+1) − 1`
super-blocks. -/
theorem gmBlocks_lower (K₀ : ℕ) (C₂ : ℝ) (Z H : ℕ) {h : ℝ} (hh : 0 < h)
    (hR : Real.sqrt h ≤ ((gmTop C₂ Z / gmStart Z H : ℕ) : ℝ)) :
    (Real.log h / (2 * Real.log 2) - 1) / ((K₀ : ℝ) + 1) - 1 ≤ (gmBlocks K₀ C₂ Z H : ℝ) := by
  set R : ℕ := gmTop C₂ Z / gmStart Z H with hRdef
  set n₀ : ℕ := Nat.log 2 R with hn₀
  have hlt : R < 2 ^ (n₀ + 1) := Nat.lt_pow_succ_log_self (by norm_num) R
  have hltR : Real.sqrt h < (2 : ℝ) ^ (n₀ + 1) := by
    refine lt_of_le_of_lt hR ?_
    exact_mod_cast hlt
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsq0 : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hlogsq : Real.log (Real.sqrt h) = Real.log h / 2 := by
    rw [Real.log_sqrt hh.le]
  have hmono : Real.log (Real.sqrt h) < ((n₀ : ℝ) + 1) * Real.log 2 := by
    have := Real.log_lt_log hsq0 hltR
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  rw [hlogsq] at hmono
  have hn₀R : Real.log h / (2 * Real.log 2) - 1 ≤ (n₀ : ℝ) := by
    rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [hmono]
  have hdiv : (n₀ : ℝ) < ((gmBlocks K₀ C₂ Z H : ℕ) + 1 : ℝ) * ((K₀ : ℝ) + 1) := by
    have h1 : n₀ < (n₀ / (K₀ + 1) + 1) * (K₀ + 1) := by
      have := Nat.lt_div_mul_add (a := n₀) (b := K₀ + 1) (by omega)
      nlinarith [this]
    have : (n₀ : ℝ) < (((n₀ / (K₀ + 1) + 1) * (K₀ + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    rw [gmBlocks, ← hRdef, ← hn₀]
    push_cast at this ⊢
    linarith
  have hK : (0 : ℝ) < (K₀ : ℝ) + 1 := by positivity
  rw [sub_le_iff_le_add, div_le_iff₀ hK]
  nlinarith [hn₀R, hdiv]

/-- A super-block size whose harmonic constant is at least one. -/
theorem exists_multiHarmConst_ge_one : ∃ K₀ : ℕ, 1 ≤ multiHarmConst K₀ := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := 2 * (2 * mertensFirstConst + 1 / 2) with hc
  refine ⟨⌈2 * (1 + c) / Real.log 2⌉₊, ?_⟩
  have hceil : 2 * (1 + c) / Real.log 2 ≤ (⌈2 * (1 + c) / Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
  have hstep : 2 * (1 + c) ≤ (⌈2 * (1 + c) / Real.log 2⌉₊ : ℝ) * Real.log 2 := by
    rw [div_le_iff₀ hlog2] at hceil
    exact hceil
  rw [multiHarmConst, ← hc]
  nlinarith [hstep, hlog2]

/-- **The base conditions of a super-block, eventually in the base.** -/
theorem eventually_superblock_base (K₀ : ℕ) {ε A : ℝ} (hA : 0 < A) :
    ∀ᶠ M : ℕ in atTop, 2 ≤ M ∧ markerLogBound K₀ ≤ Real.log (M : ℝ)
      ∧ Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5
          ≤ 32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4)
      ∧ 12 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (Real.log (M : ℝ)) ^ 2
          ≤ A ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4) := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbt := eventually_btError (32 * 2 ^ (K₀ + 2)) (by positivity)
  have hlo : (fun y : ℝ => Real.log y ^ (2 : ℝ)) =o[atTop] fun y : ℝ => y ^ ((1 : ℝ) / 4) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num)
  set κ : ℝ := |12 * ε * (2 : ℝ) ^ (2 * K₀ + 4)| + 1 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hT3 : ∀ᶠ M : ℕ in atTop, 12 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (Real.log (M : ℝ)) ^ 2
      ≤ A ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4) := by
    have hev : ∀ᶠ y : ℝ in atTop, κ * Real.log y ^ (2 : ℝ) ≤ A ^ 2 * y ^ ((1 : ℝ) / 4) := by
      filter_upwards [hlo.bound (show (0 : ℝ) < A ^ 2 / κ by positivity),
        eventually_ge_atTop (1 : ℝ)] with y hy hy1
      have hy0 : (0 : ℝ) < y := by linarith
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hy1) _),
        Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _)] at hy
      rw [div_mul_eq_mul_div, le_div_iff₀ hκ0] at hy
      linarith
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hev, eventually_ge_atTop 1]
      with M hM hM1
    have hl0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
    have hpow : Real.log (M : ℝ) ^ (2 : ℝ) = (Real.log (M : ℝ)) ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hpow] at hM
    have hle : 12 * ε * (2 : ℝ) ^ (2 * K₀ + 4) ≤ κ := by
      rw [hκ]; linarith [le_abs_self (12 * ε * (2 : ℝ) ^ (2 * K₀ + 4))]
    nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg (Real.log (M : ℝ)))]
  filter_upwards [eventually_ge_atTop 2, hlog.eventually_ge_atTop (markerLogBound K₀), hbt, hT3]
    with M h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- **The exceptional outer factors, with an explicit threshold.** -/
theorem exists_badOuter_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ L : ℝ, (Real.log y) ^ (4 : ℕ) ≤ L →
      L ≤ Real.sqrt y / Real.log y → (((badOuter y L).card : ℕ) : ℝ) ≤ ε / 2 * Real.sqrt y := by
  have hD := squarefreeDensity_pos
  have hunif := eventually_card_badOuter_le_uniform
    (ε := ε * squarefreeDensity ^ (2 : ℕ) / 4096) (by positivity)
  have hlog : Tendsto (fun y : ℝ => Real.log y) atTop atTop := Real.tendsto_log_atTop
  have hsmall : ∀ᶠ y : ℝ in atTop, 1 / (Real.log y) ^ (2 : ℕ) ≤ ε / 4 := by
    have ht : Tendsto (fun y : ℝ => 1 / (Real.log y) ^ (2 : ℕ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp hlog)
    exact ht.eventually (ge_mem_nhds (by positivity))
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.1 ((hunif.and hsmall).and
    (eventually_gt_atTop (0 : ℝ)))
  refine ⟨y₀, fun y hy L hL1 hL2 => ?_⟩
  obtain ⟨⟨hb, hs⟩, hy0⟩ := hy₀ y hy
  refine (hb L hL1 hL2).trans ?_
  have hsq : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
  have h1 : 1024 * (ε * squarefreeDensity ^ (2 : ℕ) / 4096) * Real.sqrt y
      / squarefreeDensity ^ (2 : ℕ) = ε / 4 * Real.sqrt y := by
    field_simp
    ring
  have h2 : Real.sqrt y / (Real.log y) ^ (2 : ℕ) ≤ ε / 4 * Real.sqrt y := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hs hsq
  linarith [h1, h2]

/-- `√X · h ≤ exp(0.6 log X)` when `log h ≤ log X/10`. -/
theorem sqrt_mul_le_exp {X h : ℝ} (hX : 0 < X) (hh : 0 < h)
    (hhigh : Real.log h ≤ Real.log X / 10) :
    Real.sqrt X * h ≤ Real.exp (6 / 10 * Real.log X) := by
  have hs : Real.sqrt X = Real.exp (Real.log X / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX]
    ring_nf
  rw [hs, ← Real.exp_log hh, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

/-- Arithmetic of the smallest start: `u ≥ exp(0.4 t)` from `H u ≥ 4 Z (log Z)⁴`. -/
theorem gm_start_ge_exp {X Z H u L t : ℝ} (hZhalf : X / 2 ≤ Z) (hL : 256 ≤ L)
    (hlo : 4 * Z * L ≤ H * u) (hHexp : H ≤ Real.exp (6 / 10 * t))
    (hu0 : 0 ≤ u) (hexpt : Real.exp t = X) :
    Real.exp (4 / 10 * t) ≤ u := by
  have hZ0 : 0 ≤ Z := le_trans (by
    have : 0 < Real.exp t := Real.exp_pos t
    linarith) hZhalf
  have h1 : 512 * X ≤ H * u := by
    have : 256 * Z ≤ Z * L := by nlinarith only [hZ0, hL]
    linarith only [this, hlo, hZhalf]
  have h2 : H * u ≤ Real.exp (6 / 10 * t) * u := mul_le_mul_of_nonneg_right hHexp hu0
  have hX' : X = Real.exp (4 / 10 * t) * Real.exp (6 / 10 * t) := by
    rw [← Real.exp_add, ← hexpt]; ring_nf
  have hpos : 0 < Real.exp (6 / 10 * t) := Real.exp_pos _
  have h4 : 0 < Real.exp (4 / 10 * t) := Real.exp_pos _
  have : Real.exp (4 / 10 * t) * Real.exp (6 / 10 * t) ≤ u * Real.exp (6 / 10 * t) := by
    rw [← hX']
    have : 0 ≤ X := by rw [← hexpt]; exact (Real.exp_pos t).le
    linarith only [h1, h2, this]
  exact le_of_mul_le_mul_right this hpos

/-- Arithmetic of the ladder span: `u(√h + 1) ≤ Q` from the square bounds. -/
theorem gm_span_ge {Z H u Q L C h W X : ℝ} (hZ0 : 0 < Z) (hH0 : 0 < H) (hL0 : 0 < L)
    (hC0 : 0 < C) (hh1 : 1 ≤ h) (hu0 : 0 ≤ u) (hQ0 : 0 ≤ Q)
    (hu_up : u ≤ 2 * (4 * Z * L ^ (4 : ℕ) / H))
    (hQsq : Z / (4 * (C * L)) ≤ Q ^ (2 : ℕ))
    (hW0 : 0 ≤ W) (hHge : W / 2 ≤ H) (hW : W ^ (2 : ℕ) = X * h ^ (2 : ℕ)) (hZX : Z ≤ X)
    (hbig : 4096 * C * L ^ (9 : ℕ) ≤ h) :
    u * (Real.sqrt h + 1) ≤ Q := by
  set sq : ℝ := Real.sqrt h with hsq
  have hsq1 : 1 ≤ sq := by
    rw [hsq, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hh1
  have hsqsq : sq * sq = h := Real.mul_self_sqrt (by linarith)
  have hsq4 : (sq + 1) ^ (2 : ℕ) ≤ 4 * h := by nlinarith only [hsq1, hsqsq]
  have hu2' : u ^ (2 : ℕ) ≤ (2 * (4 * Z * L ^ (4 : ℕ) / H)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hu0 hu_up 2
  have hH2 : Z * h ^ (2 : ℕ) / 4 ≤ H ^ (2 : ℕ) := by
    have hW2 : W ^ (2 : ℕ) / 4 ≤ H ^ (2 : ℕ) := by
      have := pow_le_pow_left₀ (by linarith) hHge 2
      rw [div_pow] at this; norm_num at this; linarith
    have : Z * h ^ (2 : ℕ) ≤ X * h ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hZX (by positivity)
    linarith only [hW2, this, hW]
  have hkey : (u * (sq + 1)) ^ (2 : ℕ) ≤ Q ^ (2 : ℕ) := by
    refine le_trans ?_ hQsq
    rw [mul_pow]
    have hA1 : u ^ (2 : ℕ) * (sq + 1) ^ (2 : ℕ)
        ≤ (2 * (4 * Z * L ^ (4 : ℕ) / H)) ^ (2 : ℕ) * (4 * h) :=
      mul_le_mul hu2' hsq4 (by positivity) (by positivity)
    refine hA1.trans ?_
    rw [le_div_iff₀ (by positivity)]
    have hexp : (2 * (4 * Z * L ^ (4 : ℕ) / H)) ^ (2 : ℕ) * (4 * h) * (4 * (C * L))
        = 1024 * C * Z ^ (2 : ℕ) * L ^ (9 : ℕ) * h / H ^ (2 : ℕ) := by
      field_simp
      ring
    rw [hexp, div_le_iff₀ (by positivity)]
    have hstep : 1024 * C * Z ^ (2 : ℕ) * L ^ (9 : ℕ) * h ≤ Z * (Z * h ^ (2 : ℕ) / 4) := by
      have := mul_le_mul_of_nonneg_left hbig
        (show (0 : ℝ) ≤ Z ^ (2 : ℕ) * h / 4 by positivity)
      have e1 : Z ^ (2 : ℕ) * h / 4 * (4096 * C * L ^ (9 : ℕ))
          = 1024 * C * Z ^ (2 : ℕ) * L ^ (9 : ℕ) * h := by ring
      have e2 : Z ^ (2 : ℕ) * h / 4 * h = Z * (Z * h ^ (2 : ℕ) / 4) := by ring
      linarith only [this, e1, e2]
    have := mul_le_mul_of_nonneg_left hH2 hZ0.le
    linarith only [hstep, this]
  exact le_of_pow_le_pow_left₀ (by norm_num) hQ0 hkey

/-- `n = a·p` with `p` a prime above `√X`, `a` below `√X`, and `μ(a) = -σ`. -/
def ReciprocalMarkerForm (X : ℝ) (σ : ℤ) (n : ℕ) : Prop :=
  ∃ a p : ℕ, p.Prime ∧ Real.sqrt X < (p : ℝ) ∧ (a : ℝ) < Real.sqrt X ∧ a * p = n
    ∧ moebius a = -σ

/-- **Unique decoding.**  A positive integer has at most one factorisation `a·p` with `p` a prime
above `√X` and `a` below `√X`: a second one `a'·p'` with `a' < √X < p` forces `p = p'`. -/
theorem reciprocalMarker_decoding_unique {X : ℝ} {a p a' p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hpX : Real.sqrt X < (p : ℝ)) (ha'X : (a' : ℝ) < Real.sqrt X)
    (hpos : 0 < a * p) (heq : a * p = a' * p') : a = a' ∧ p = p' := by
  have ha' : 0 < a' := by
    rcases Nat.eq_zero_or_pos a' with h | h
    · rw [h, zero_mul] at heq; omega
    · exact h
  have hpa' : ¬ p ∣ a' := by
    intro hdvd
    have := Nat.le_of_dvd ha' hdvd
    have : (p : ℝ) ≤ (a' : ℝ) := by exact_mod_cast this
    linarith
  have hpp' : p = p' := by
    have hdvd : p ∣ a' * p' := heq ▸ Dvd.intro_left a rfl
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact absurd h hpa'
    · exact (Nat.prime_dvd_prime_iff_eq hp hp').1 h
  subst hpp'
  exact ⟨Nat.eq_of_mul_eq_mul_right hp.pos heq, rfl⟩

/-- The absolute constant of the growing-marker count. -/
def gmConst (K₀ : ℕ) : ℝ :=
  3 * squarefreeDensity / (256 * (32 * (((K₀ : ℝ) + 1) * Real.log 2)))

theorem gmConst_pos (K₀ : ℕ) : 0 < gmConst K₀ := by
  have := squarefreeDensity_pos
  have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [gmConst]; positivity

open Classical in
/-- **The growing reciprocal-marker count at one scale, from explicit largeness conditions.** -/
theorem growingMarker_count_at {K₀ N₀ : ℕ} {σ : ℤ} {ε y₀ C₂ X h : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hK₀ : 1 ≤ multiHarmConst K₀) (hε : 0 < ε)
    (hbad : ∀ y : ℝ, y₀ ≤ y → ∀ L : ℝ, (Real.log y) ^ (4 : ℕ) ≤ L →
      L ≤ Real.sqrt y / Real.log y → (((badOuter y L).card : ℕ) : ℝ) ≤ ε / 2 * Real.sqrt y)
    (hMstar : ∀ M : ℕ, (N₀ : ℝ) ≤ (M : ℝ) → 2 ≤ M ∧ markerLogBound K₀ ≤ Real.log (M : ℝ)
      ∧ Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5
          ≤ 32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4)
      ∧ 12 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (Real.log (M : ℝ)) ^ 2
          ≤ (multiHarmConst K₀ / 2) ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4))
    (hT2 : 6 * ε * pairMainConst * (2 : ℝ) ^ (3 * K₀ + 6) ≤ (multiHarmConst K₀ / 2) ^ 2)
    (hC₂9 : 9 ≤ C₂)
    (hC₂T : 384 * ε * (2 : ℝ) ^ (2 * K₀ + 4) ≤ C₂ * (multiHarmConst K₀ / 2) ^ 2)
    (hX16 : 16 ≤ X) (hXlog : 4 + Real.log 2 ≤ Real.log X)
    (hX3 : Real.exp (6 / 10 * Real.log X) * Real.log X ≤ X)
    (hX4 : y₀ ≤ Real.exp (8 / 10 * Real.log X)) (hX5 : 18 * C₂ * Real.log X ≤ X)
    (hX7 : (N₀ : ℝ) + 1 ≤ Real.sqrt (X / 2))
    (hX8 : Real.log (4096 * C₂) + 9 * Real.log (Real.log X) ≤ (Real.log (Real.log X)) ^ (2 : ℕ))
    (hX9 : 4 * ((K₀ : ℝ) + 2) * Real.log 2 + 1 ≤ (Real.log (Real.log X)) ^ (2 : ℕ))
    (hX10 : 8 * ((K₀ : ℝ) + 1) * Real.log 2 ≤ (Real.log X - Real.log 2) ^ (3 : ℕ))
    (hh0 : 0 < h) (hlow : (Real.log (Real.log X)) ^ (2 : ℕ) ≤ Real.log h)
    (hhigh : Real.log h ≤ Real.log X / 10) :
    gmConst K₀ * (Real.sqrt X * h * Real.log h / Real.log X)
      ≤ ((((Finset.Ioc ⌊X⌋₊ ⌊X + Real.sqrt X * h⌋₊).filter
          (fun n => moebius n = σ ∧ ReciprocalMarkerForm X σ n)).card : ℕ) : ℝ) := by
  classical
  have hX0 : 0 < X := by linarith only [hX16]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith only [this]
  have hharm : 0 < multiHarmConst K₀ := by linarith only [hK₀]
  obtain ⟨A, hA⟩ : ∃ A, multiHarmConst K₀ / 2 = A := ⟨_, rfl⟩
  rw [hA] at hMstar hT2 hC₂T
  have hA0 : 0 < A := by rw [← hA]; linarith only [hharm]
  obtain ⟨t, ht⟩ : ∃ t, Real.log X = t := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Real.log h = ℓ := ⟨_, rfl⟩
  rw [ht] at hXlog hX3 hX4 hX5 hX8 hX9 hX10 hlow hhigh
  rw [hℓ] at hlow hhigh
  rw [ht, hℓ]
  have ht4 : 4 ≤ t := by linarith only [hXlog, hlog2]
  have hexpt : Real.exp t = X := by rw [← ht]; exact Real.exp_log hX0
  -- the physical scale
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ, ⌊X⌋₊ = Z := ⟨_, rfl⟩
  rw [hZ]
  have hZle : (Z : ℝ) ≤ X := hZ ▸ Nat.floor_le hX0.le
  have hZgt : X - 1 < (Z : ℝ) := by
    have := Nat.lt_floor_add_one X; rw [hZ] at this; linarith only [this]
  have hZhalf : X / 2 ≤ (Z : ℝ) := by linarith only [hZgt, hX16]
  have hZ0 : (0 : ℝ) < (Z : ℝ) := by linarith only [hZhalf, hX0]
  obtain ⟨LZ, hLZ⟩ : ∃ LZ, Real.log (Z : ℝ) = LZ := ⟨_, rfl⟩
  have hLZt : LZ ≤ t := by rw [← hLZ, ← ht]; exact Real.log_le_log hZ0 hZle
  have hLZlow : t - Real.log 2 ≤ LZ := by
    have h1 := Real.log_le_log (by positivity) hZhalf
    rw [Real.log_div hX0.ne' (by norm_num), ht, hLZ] at h1
    linarith only [h1]
  have hLZ4 : 4 ≤ LZ := by linarith only [hLZlow, hXlog, ht]
  have hLZhalf : t / 2 ≤ LZ := by linarith only [hLZlow, hlog2le, ht4]
  -- the length
  have hℓ1 : 1 ≤ ℓ := by
    have : 0 ≤ 4 * ((K₀ : ℝ) + 2) * Real.log 2 := by positivity
    linarith only [hX9, hlow, this]
  have hexpℓ : Real.exp ℓ = h := by rw [← hℓ]; exact Real.exp_log hh0
  have hh1 : 1 ≤ h := by rw [← hexpℓ]; exact Real.one_le_exp (by linarith only [hℓ1])
  have hsX : 4 ≤ Real.sqrt X := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hX16
  obtain ⟨W, hW⟩ : ∃ W, Real.sqrt X * h = W := ⟨_, rfl⟩
  rw [hW]
  have hW4 : 4 ≤ W := by
    rw [← hW]; exact le_trans hsX (le_mul_of_one_le_right (by positivity) hh1)
  have hWexp : W ≤ Real.exp (6 / 10 * t) := by
    rw [← hW, ← ht]; exact sqrt_mul_le_exp hX0 hh0 (by rw [ht, hℓ]; exact hhigh)
  have hWt : W * t ≤ X :=
    le_trans (mul_le_mul_of_nonneg_right hWexp (by linarith only [ht4])) hX3
  have hWsq : W ^ (2 : ℕ) = X * h ^ (2 : ℕ) := by
    rw [← hW, mul_pow, Real.sq_sqrt hX0.le]
  obtain ⟨H, hH⟩ : ∃ H : ℕ, ⌊W⌋₊ = H := ⟨_, rfl⟩
  have hHle : (H : ℝ) ≤ W := hH ▸ Nat.floor_le (by linarith only [hW4])
  have hHge : W / 2 ≤ (H : ℝ) := by
    have := Nat.lt_floor_add_one W; rw [hH] at this; linarith only [this, hW4]
  have hHR0 : (0 : ℝ) < (H : ℝ) := by linarith only [hHge, hW4]
  have hH0 : 0 < H := by exact_mod_cast hHR0
  have hhi : (H : ℝ) * LZ ≤ 4 * (Z : ℝ) := by
    have : (H : ℝ) * LZ ≤ W * t := mul_le_mul hHle hLZt (by linarith only [hLZ4])
      (by linarith only [hW4])
    linarith only [this, hWt, hZhalf]
  have hHZ : (H : ℝ) ≤ (Z : ℝ) := by nlinarith only [hhi, hLZ4, hHR0]
  -- the smallest start
  obtain ⟨u, hu⟩ : ∃ u : ℕ, gmStart Z H = u := ⟨_, rfl⟩
  have hu2 : 2 ≤ u := hu ▸ two_le_gmStart Z H
  have huR : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
  have hlo : 4 * (Z : ℝ) * LZ ^ (4 : ℕ) ≤ (H : ℝ) * (u : ℝ) := by
    rw [← hLZ, ← hu]; exact gmStart_lower hH0
  have hLZ4pow : (256 : ℝ) ≤ LZ ^ (4 : ℕ) := by
    have := pow_le_pow_left₀ (by norm_num) hLZ4 4
    norm_num at this
    linarith only [this]
  have hq3 : 3 ≤ 4 * (Z : ℝ) * LZ ^ (4 : ℕ) / (H : ℝ) := by
    rw [le_div_iff₀ hHR0]
    have : (Z : ℝ) * 256 ≤ (Z : ℝ) * LZ ^ (4 : ℕ) := mul_le_mul_of_nonneg_left hLZ4pow hZ0.le
    linarith only [this, hHZ, hZ0]
  have hu_up : (u : ℝ) ≤ 2 * (4 * (Z : ℝ) * LZ ^ (4 : ℕ) / (H : ℝ)) := by
    rw [← hu]; rw [← hLZ] at hq3 ⊢; exact gmStart_upper hq3
  have hy₀u : y₀ ≤ (u : ℝ) ^ (2 : ℕ) := by
    have h3 := gm_start_ge_exp hZhalf hLZ4pow hlo (le_trans hHle hWexp) (by linarith only [huR])
      hexpt
    have hsq : Real.exp (8 / 10 * t) = Real.exp (4 / 10 * t) ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h4 : Real.exp (8 / 10 * t) ≤ (u : ℝ) ^ (2 : ℕ) := by
      rw [hsq]; exact pow_le_pow_left₀ (Real.exp_pos _).le h3 2
    linarith only [h4, hX4]
  -- the top start
  have hCL : 0 < C₂ * LZ := by
    have : (0 : ℝ) < C₂ := by linarith only [hC₂9]
    positivity
  have hCL9 : 9 ≤ C₂ * LZ := by nlinarith only [hC₂9, hLZ4]
  have hz9 : 9 ≤ (Z : ℝ) / (C₂ * LZ) := by
    rw [le_div_iff₀ hCL]
    have : C₂ * LZ ≤ C₂ * t := mul_le_mul_of_nonneg_left hLZt (by linarith only [hC₂9])
    linarith only [this, hX5, hZhalf]
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, gmTop C₂ Z = Q := ⟨_, rfl⟩
  have hQlow : Real.sqrt ((Z : ℝ) / (C₂ * LZ)) / 2 ≤ (Q : ℝ) := by
    rw [← hQ, ← hLZ]; rw [← hLZ] at hz9; exact gmTop_lower hz9
  have hQsq : (Z : ℝ) / (4 * (C₂ * LZ)) ≤ (Q : ℝ) ^ (2 : ℕ) := by
    have h0 : 0 ≤ Real.sqrt ((Z : ℝ) / (C₂ * LZ)) / 2 := by positivity
    have := pow_le_pow_left₀ h0 hQlow 2
    rw [div_pow, Real.sq_sqrt (by positivity)] at this
    have e : (Z : ℝ) / (4 * (C₂ * LZ)) = (Z : ℝ) / (C₂ * LZ) / 2 ^ 2 := by
      rw [div_div]; norm_num; ring
    rw [e]; exact this
  -- the length beats the ladder
  have hbig : 4096 * C₂ * LZ ^ (9 : ℕ) ≤ h := by
    have hC0 : (0 : ℝ) < C₂ := by linarith only [hC₂9]
    have hpos : 0 < 4096 * C₂ * LZ ^ (9 : ℕ) := by positivity
    rw [← hexpℓ, ← Real.exp_log hpos]
    refine Real.exp_le_exp.2 ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hlogLZ : Real.log LZ ≤ Real.log t := Real.log_le_log (by linarith only [hLZ4]) hLZt
    push_cast
    linarith only [hX8, hlow, hlogLZ]
  have hQu : (u : ℝ) * (Real.sqrt h + 1) ≤ (Q : ℝ) :=
    gm_span_ge hZ0 hHR0 (by linarith only [hLZ4]) (by linarith only [hC₂9]) hh1
      (by linarith only [huR]) (Nat.cast_nonneg _) hu_up hQsq (by linarith only [hW4]) hHge hWsq
      hZle hbig
  have hsq1 : 1 ≤ Real.sqrt h := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hh1
  obtain ⟨R, hR⟩ : ∃ R : ℕ, Q / u = R := ⟨_, rfl⟩
  have hRs : Real.sqrt h ≤ (R : ℝ) := by
    have hlt : Q < (R + 1) * u := by
      have := Nat.lt_div_mul_add (a := Q) (b := u) (by omega)
      rw [hR] at this; linarith only [this]
    have hltR : (Q : ℝ) < ((R : ℝ) + 1) * (u : ℝ) := by exact_mod_cast hlt
    nlinarith only [hQu, hltR, huR]
  have hR1 : 1 ≤ gmTop C₂ Z / gmStart Z H := by
    rw [hQ, hu, hR]
    have : (1 : ℝ) ≤ (R : ℝ) := le_trans hsq1 hRs
    exact_mod_cast this
  -- the number of super-blocks
  have hIlow := gmBlocks_lower K₀ C₂ Z H hh0 (by rw [hQ, hu, hR]; exact hRs)
  have hmQ := ladderTop_le_gmTop K₀ C₂ Z H hR1
  obtain ⟨I, hI⟩ : ∃ I : ℕ, gmBlocks K₀ C₂ Z H = I := ⟨_, rfl⟩
  rw [hI, hℓ] at hIlow
  rw [hI, hu, hQ] at hmQ
  have hK1 : (0 : ℝ) < (K₀ : ℝ) + 1 := by positivity
  have hIge : ℓ / (4 * ((K₀ : ℝ) + 1) * Real.log 2) ≤ (I : ℝ) := by
    refine le_trans ?_ hIlow
    have hℓK : 4 * ((K₀ : ℝ) + 2) * Real.log 2 ≤ ℓ := by linarith only [hX9, hlow]
    rw [div_le_iff₀ (by positivity)]
    have hexp : ((ℓ / (2 * Real.log 2) - 1) / ((K₀ : ℝ) + 1) - 1)
        * (4 * ((K₀ : ℝ) + 1) * Real.log 2)
        = 2 * ℓ - 4 * Real.log 2 * ((K₀ : ℝ) + 2) := by
      field_simp
      ring
    rw [hexp]
    linarith only [hℓK]
  have hI0 : 0 < I := by
    have hℓK : 4 * ((K₀ : ℝ) + 2) * Real.log 2 + 1 ≤ ℓ := le_trans hX9 hlow
    have h1 : (1 : ℝ) ≤ ℓ / (4 * ((K₀ : ℝ) + 1) * Real.log 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [hlog2, hℓK]
    have : (1 : ℝ) ≤ (I : ℝ) := le_trans h1 hIge
    exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
  -- the top of the ladder
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 ^ (I * (K₀ + 1)) * u = m := ⟨_, rfl⟩
  rw [hm] at hmQ
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by
    have : u ≤ m := hm ▸ Nat.le_mul_of_pos_left u (by positivity)
    exact le_trans huR (by exact_mod_cast this)
  have hmsq : (m : ℝ) ^ (2 : ℕ) * (C₂ * LZ) ≤ (Z : ℝ) := by
    have hmQR : (m : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hmQ
    have := gmTop_sq_le (C₂ := C₂) (Z := Z) (by rw [hLZ]; exact hCL)
    rw [hQ, hLZ] at this
    exact le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by linarith only [hm2]) hmQR 2) hCL.le) this
  have hmZ : m * m ≤ Z := by
    have : (m : ℝ) * (m : ℝ) ≤ (Z : ℝ) := by nlinarith only [hmsq, hCL9]
    exact_mod_cast this
  have hsZ : 1 ≤ Real.sqrt (Z : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith only [hZhalf, hX16])
  have hsZsq : Real.sqrt (Z : ℝ) * Real.sqrt (Z : ℝ) = (Z : ℝ) := Real.mul_self_sqrt hZ0.le
  have h3m : 3 * (m : ℝ) ≤ Real.sqrt (Z : ℝ) := by
    have h9 : (3 * (m : ℝ)) ^ (2 : ℕ) ≤ (Z : ℝ) := by nlinarith only [hmsq, hCL9]
    calc 3 * (m : ℝ) = Real.sqrt ((3 * (m : ℝ)) ^ (2 : ℕ)) := by
          rw [Real.sqrt_sq (by linarith only [hm2])]
      _ ≤ Real.sqrt (Z : ℝ) := Real.sqrt_le_sqrt h9
  have hZm3 : 3 * Real.sqrt (Z : ℝ) ≤ (Z : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ (by linarith only [hm2])]
    nlinarith only [h3m, hsZsq, hsZ]
  have hm0 : 0 < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm2 : (0 : ℝ) < m)
  obtain ⟨q, hq⟩ : ∃ q : ℕ, Z / m = q := ⟨_, rfl⟩
  have hqlow : (Z : ℝ) / (m : ℝ) - 1 ≤ (q : ℝ) := by
    have hlt : Z < (q + 1) * m := by
      have := Nat.lt_div_mul_add (a := Z) (b := m) (by omega)
      rw [hq] at this; linarith only [this]
    have hltR : (Z : ℝ) < ((q : ℝ) + 1) * (m : ℝ) := by exact_mod_cast hlt
    rw [div_sub_one (by linarith only [hm2]), div_le_iff₀ (by linarith only [hm2])]
    linarith only [hltR]
  have hq2 : 2 * Real.sqrt (Z : ℝ) ≤ (q : ℝ) := by linarith only [hqlow, hZm3, hsZ]
  have hXH : Z + H ≤ q * q := by
    have : (Z : ℝ) + (H : ℝ) ≤ (q : ℝ) * (q : ℝ) := by nlinarith only [hq2, hsZsq, hHZ, hsZ]
    exact_mod_cast this
  have hZmN : (N₀ : ℝ) ≤ (q : ℝ) := by
    have h1 : Real.sqrt (X / 2) ≤ Real.sqrt (Z : ℝ) := Real.sqrt_le_sqrt hZhalf
    linarith only [h1, hX7, hq2, hsZ]
  have hT1 : 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * ((m : ℕ) : ℝ) * LZ ≤ (q : ℝ) * A ^ 2 := by
    have hZm : (m : ℝ) * (C₂ * LZ) ≤ (Z : ℝ) / (m : ℝ) := by
      rw [le_div_iff₀ (by linarith only [hm2])]
      nlinarith only [hmsq]
    have hq' : (Z : ℝ) / (m : ℝ) / 2 ≤ (q : ℝ) := by
      have : 2 ≤ (Z : ℝ) / (m : ℝ) := by linarith only [hZm3, hsZ]
      linarith only [this, hqlow]
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
    have hml : 0 ≤ (m : ℝ) * LZ := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ LZ := by linarith only [hLZ4]
      positivity
    have s1 := mul_le_mul_of_nonneg_right hC₂T hml
    have s2 : (m : ℝ) * (C₂ * LZ) / 2 * A ^ 2 ≤ (Z : ℝ) / (m : ℝ) / 2 * A ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hZm]) hA2
    have s3 := mul_le_mul_of_nonneg_right hq' hA2
    have e1 : 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * ((m : ℕ) : ℝ) * LZ
        = (384 * ε * (2 : ℝ) ^ (2 * K₀ + 4)) * ((m : ℝ) * LZ) / 2 := by ring
    have e2 : C₂ * A ^ 2 * ((m : ℝ) * LZ) / 2 = (m : ℝ) * (C₂ * LZ) / 2 * A ^ 2 := by ring
    linarith only [s1, s2, s3, e1, e2]
  -- the explicit count
  have key := growingMarker_count_explicit (K₀ := K₀) (Z := Z) (H := H) (u := u) (I := I)
    (σ := σ) (ε := ε) (y₀ := y₀) (Mstar := N₀) hσ hu2 hI0 hε.le hharm hbad hy₀u
    (by rw [hA]; exact hMstar) (by rw [hA]; exact hT2) (by rw [hm, hq]; exact hZmN)
    (by rw [hm, hq, hA, hLZ]; exact hT1) (by rw [hLZ]; exact hlo) (by rw [hLZ]; exact hhi)
    (by rw [hLZ]; linarith only [hLZ4]) (by rw [hm]; exact hmZ) (by rw [hm, hq]; exact hXH)
  rw [hLZ] at key
  -- the window of the statement contains `(Z, Z+H]`, and the targets decode
  have hsXZ : Real.sqrt X ≤ 2 * Real.sqrt (Z : ℝ) := by
    have h1 : Real.sqrt (X / 2) ≤ Real.sqrt (Z : ℝ) := Real.sqrt_le_sqrt hZhalf
    have h2 : Real.sqrt X ≤ 2 * Real.sqrt (X / 2) := by
      have hs2 : Real.sqrt (X / 2) * Real.sqrt 2 = Real.sqrt X := by
        rw [← Real.sqrt_mul (by linarith only [hX0]), div_mul_cancel₀ _ (by norm_num)]
      have hsqrt2 : Real.sqrt 2 ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      rw [← hs2]
      have : 0 ≤ Real.sqrt (X / 2) := Real.sqrt_nonneg _
      nlinarith only [this, hsqrt2]
    linarith only [h1, h2]
  have hsub : ((Finset.Ioc Z (Z + H)).filter
        (fun n => moebius n = σ ∧ MarkerDecoded (Z / (2 ^ (I * (K₀ + 1)) * u)) σ n))
      ⊆ ((Finset.Ioc Z ⌊X + W⌋₊).filter
        (fun n => moebius n = σ ∧ ReciprocalMarkerForm X σ n)) := by
    have hZH : Z + H ≤ ⌊X + W⌋₊ := by
      refine Nat.le_floor ?_
      push_cast
      linarith only [hZle, hHle]
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    obtain ⟨⟨hn1, hn2⟩, hsig, a, p, hp, hpM, hap, hasig⟩ := hn
    rw [hm, hq] at hpM
    have hpR : (q : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hpM
    have hpX : Real.sqrt X < (p : ℝ) := by linarith only [hpR, hq2, hsXZ]
    have hnR : (n : ℝ) ≤ (Z : ℝ) + (H : ℝ) := by exact_mod_cast hn2
    have haX : (a : ℝ) < Real.sqrt X := by
      have hapR : (a : ℝ) * (p : ℝ) = (n : ℝ) := by exact_mod_cast hap
      have hp2 : 2 * Real.sqrt (Z : ℝ) < (p : ℝ) := by linarith only [hpR, hq2]
      have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
      have hsZX : Real.sqrt (Z : ℝ) ≤ Real.sqrt X := Real.sqrt_le_sqrt hZle
      by_contra hcon
      push Not at hcon
      have h1 : Real.sqrt (Z : ℝ) * (2 * Real.sqrt (Z : ℝ)) < (a : ℝ) * (p : ℝ) := by
        have hsZ0 : 0 < Real.sqrt (Z : ℝ) := by linarith only [hsZ]
        calc Real.sqrt (Z : ℝ) * (2 * Real.sqrt (Z : ℝ))
            < Real.sqrt (Z : ℝ) * (p : ℝ) := mul_lt_mul_of_pos_left hp2 hsZ0
          _ ≤ (a : ℝ) * (p : ℝ) :=
            mul_le_mul_of_nonneg_right (le_trans hsZX hcon) (by linarith only [hp2, hsZ])
      linarith only [h1, hapR, hnR, hsZsq, hHZ]
    exact ⟨⟨hn1, le_trans hn2 hZH⟩, hsig, a, p, hp, hpX, haX, hap, hasig⟩
  have hcard : ((((Finset.Ioc Z (Z + H)).filter
        (fun n => moebius n = σ ∧ MarkerDecoded (Z / (2 ^ (I * (K₀ + 1)) * u)) σ n)).card : ℕ)
          : ℝ)
      ≤ ((((Finset.Ioc Z ⌊X + W⌋₊).filter
        (fun n => moebius n = σ ∧ ReciprocalMarkerForm X σ n)).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine le_trans ?_ (le_trans key hcard)
  -- the final arithmetic
  have hZu : ((Z / u : ℕ) : ℝ) ≤ (H : ℝ) / (4 * LZ ^ (4 : ℕ)) := by
    have h1 : ((Z / u : ℕ) : ℝ) ≤ (Z : ℝ) / (u : ℝ) := Nat.cast_div_le
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by linarith only [huR]) (by positivity)]
    linarith only [hlo]
  have hterm1 : (H : ℝ) * (ℓ / (8 * ((K₀ : ℝ) + 1) * Real.log 2 * t))
      ≤ (H : ℝ) * ((I : ℝ) * (multiHarmConst K₀ / (2 * LZ))) := by
    refine mul_le_mul_of_nonneg_left ?_ hHR0.le
    have h1 : ℓ / (8 * ((K₀ : ℝ) + 1) * Real.log 2 * t)
        = ℓ / (4 * ((K₀ : ℝ) + 1) * Real.log 2) * (1 / (2 * t)) := by
      rw [div_mul_div_comm, mul_one]
      ring_nf
    have h2 : 1 / (2 * t) ≤ multiHarmConst K₀ / (2 * LZ) := by
      rw [div_le_div_iff₀ (by linarith only [ht4]) (by linarith only [hLZ4])]
      nlinarith only [hLZt, hK₀, hLZ4]
    rw [h1]
    exact mul_le_mul hIge h2 (by positivity) (by positivity)
  have hterm2 : (H : ℝ) / (4 * LZ ^ (4 : ℕ))
      ≤ (H : ℝ) * (ℓ / (8 * ((K₀ : ℝ) + 1) * Real.log 2 * t)) / 2 := by
    have hcube : 8 * ((K₀ : ℝ) + 1) * Real.log 2 ≤ LZ ^ (3 : ℕ) :=
      le_trans hX10 (pow_le_pow_left₀ (by linarith only [ht4, hlog2le]) hLZlow 3)
    rw [div_le_iff₀ (by positivity)]
    have hexp : (H : ℝ) * (ℓ / (8 * ((K₀ : ℝ) + 1) * Real.log 2 * t)) / 2 * (4 * LZ ^ (4 : ℕ))
        = (H : ℝ) * (ℓ * LZ ^ (4 : ℕ)) / (4 * ((K₀ : ℝ) + 1) * Real.log 2 * t) := by
      field_simp
      ring
    rw [hexp, le_div_iff₀ (by positivity)]
    have h4 : 4 * ((K₀ : ℝ) + 1) * Real.log 2 * t ≤ ℓ * LZ ^ (4 : ℕ) := by
      have e : LZ ^ (4 : ℕ) = LZ ^ (3 : ℕ) * LZ := by ring
      have hc0 : 0 ≤ 8 * ((K₀ : ℝ) + 1) * Real.log 2 := by positivity
      have s1 : 8 * ((K₀ : ℝ) + 1) * Real.log 2 * (t / 2) ≤ LZ ^ (3 : ℕ) * LZ :=
        mul_le_mul hcube hLZhalf (by linarith only [ht4]) (by positivity)
      have s2 : LZ ^ (3 : ℕ) * LZ ≤ ℓ * (LZ ^ (3 : ℕ) * LZ) := by
        have : 0 ≤ LZ ^ (3 : ℕ) * LZ := by
          have : (0 : ℝ) ≤ LZ := by linarith only [hLZ4]
          positivity
        nlinarith only [this, hℓ1]
      rw [e]
      linarith only [s1, s2]
    have := mul_le_mul_of_nonneg_left h4 hHR0.le
    linarith only [this]
  have hD3 : 0 ≤ 3 * squarefreeDensity / 256 := by
    have := squarefreeDensity_pos; positivity
  have hfinal : gmConst K₀ * (W * ℓ / t)
      ≤ 3 * squarefreeDensity / 256
        * ((H : ℝ) * (ℓ / (8 * ((K₀ : ℝ) + 1) * Real.log 2 * t)) / 2) := by
    rw [gmConst]
    have hexp1 : 3 * squarefreeDensity / (256 * (32 * (((K₀ : ℝ) + 1) * Real.log 2)))
          * (W * ℓ / t)
        = 3 * squarefreeDensity / 256
          * ((W / 2) * (ℓ / (8 * ((K₀ : ℝ) + 1) * Real.log 2 * t)) / 2) := by
      field_simp
      ring
    rw [hexp1]
    have hpos : 0 ≤ ℓ / (8 * ((K₀ : ℝ) + 1) * Real.log 2 * t) := by
      have : (0 : ℝ) ≤ ℓ := by linarith only [hℓ1]
      have : (0 : ℝ) < t := by linarith only [ht4]
      positivity
    have := mul_le_mul_of_nonneg_right hHge hpos
    exact mul_le_mul_of_nonneg_left (by linarith only [this]) hD3
  refine hfinal.trans (mul_le_mul_of_nonneg_left ?_ hD3)
  linarith only [hterm1, hterm2, hZu]

open Classical in
/-- **The growing reciprocal-marker count, uniformly in the length.**  There is an absolute
`c > 0` such that for all large `X` and every `h` with `(log log X)² ≤ log h ≤ (log X)/10`, the
window `(X, X + √X h]` contains at least `c·√X h log h/log X` integers of each Möbius sign. -/
theorem growingMarker_count_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ σ : ℤ, (σ = 1 ∨ σ = -1) → ∀ᶠ X : ℝ in atTop, ∀ h : ℝ, 0 < h →
      (Real.log (Real.log X)) ^ (2 : ℕ) ≤ Real.log h → Real.log h ≤ Real.log X / 10 →
      c * (Real.sqrt X * h * Real.log h / Real.log X)
        ≤ ((((Finset.Ioc ⌊X⌋₊ ⌊X + Real.sqrt X * h⌋₊).filter
            (fun n => moebius n = σ ∧ ReciprocalMarkerForm X σ n)).card : ℕ) : ℝ) := by
  classical
  obtain ⟨K₀, hK₀⟩ := exists_multiHarmConst_ge_one
  have hharm : 0 < multiHarmConst K₀ := by linarith
  have hA0 : 0 < multiHarmConst K₀ / 2 := by linarith
  have hpc := pairMainConst_pos
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ,
      ε = (multiHarmConst K₀ / 2) ^ 2 / (6 * pairMainConst * (2 : ℝ) ^ (3 * K₀ + 6)) :=
    ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hT2 : 6 * ε * pairMainConst * (2 : ℝ) ^ (3 * K₀ + 6) ≤ (multiHarmConst K₀ / 2) ^ 2 := by
    rw [hεdef]
    apply le_of_eq
    field_simp
  obtain ⟨y₀, hbad⟩ := exists_badOuter_threshold hε
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (eventually_superblock_base K₀ (ε := ε) hA0)
  have hMstar : ∀ M : ℕ, (N₀ : ℝ) ≤ (M : ℝ) → 2 ≤ M ∧ markerLogBound K₀ ≤ Real.log (M : ℝ)
      ∧ Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5
          ≤ 32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4)
      ∧ 12 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (Real.log (M : ℝ)) ^ 2
          ≤ (multiHarmConst K₀ / 2) ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4) :=
    fun M hM => hN₀ M (by exact_mod_cast hM)
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ,
      C₂ = 400 * ε * (2 : ℝ) ^ (2 * K₀ + 4) / (multiHarmConst K₀ / 2) ^ 2 + 9 := ⟨_, rfl⟩
  have hC₂9 : 9 ≤ C₂ := by
    have : 0 ≤ 400 * ε * (2 : ℝ) ^ (2 * K₀ + 4) / (multiHarmConst K₀ / 2) ^ 2 := by positivity
    rw [hC₂]; linarith
  have hC₂T : 384 * ε * (2 : ℝ) ^ (2 * K₀ + 4) ≤ C₂ * (multiHarmConst K₀ / 2) ^ 2 := by
    rw [hC₂, add_mul, div_mul_cancel₀ _ (by positivity)]
    have : 0 ≤ 9 * (multiHarmConst K₀ / 2) ^ 2 := by positivity
    have : 0 ≤ ε * (2 : ℝ) ^ (2 * K₀ + 4) := by positivity
    linarith
  refine ⟨gmConst K₀, gmConst_pos K₀, fun σ hσ => ?_⟩
  have hlogX : Tendsto (fun X : ℝ => Real.log X) atTop atTop := Real.tendsto_log_atTop
  have hloglog : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogX
  have hF3 : ∀ᶠ X : ℝ in atTop, Real.exp (6 / 10 * Real.log X) * Real.log X ≤ X := by
    have hlo : (fun t : ℝ => t) =o[atTop] fun t : ℝ => Real.exp ((4 / 10) * t) := by
      have := isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 4 / 10 by norm_num)
      simpa using this
    have hev : ∀ᶠ t : ℝ in atTop, Real.exp (6 / 10 * t) * t ≤ Real.exp t := by
      filter_upwards [hlo.bound (show (0 : ℝ) < 1 by norm_num), eventually_ge_atTop (0 : ℝ)]
        with t ht ht0
      rw [Real.norm_of_nonneg ht0, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] at ht
      calc Real.exp (6 / 10 * t) * t ≤ Real.exp (6 / 10 * t) * Real.exp (4 / 10 * t) :=
            mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
        _ = Real.exp t := by rw [← Real.exp_add]; ring_nf
    filter_upwards [hlogX.eventually hev, eventually_gt_atTop (0 : ℝ)] with X hX hX0
    rwa [Real.exp_log hX0] at hX
  have hF4 : ∀ᶠ X : ℝ in atTop, y₀ ≤ Real.exp (8 / 10 * Real.log X) := by
    have : Tendsto (fun X : ℝ => Real.exp (8 / 10 * Real.log X)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (hlogX.const_mul_atTop (by norm_num))
    exact this.eventually_ge_atTop y₀
  have hF5 : ∀ᶠ X : ℝ in atTop, 18 * C₂ * Real.log X ≤ X := by
    have hlo : (fun X : ℝ => Real.log X) =o[atTop] fun X : ℝ => X := Real.isLittleO_log_id_atTop
    have hC : 0 < 18 * C₂ := by linarith
    filter_upwards [hlo.bound (show (0 : ℝ) < 1 / (18 * C₂) by positivity),
      eventually_ge_atTop (1 : ℝ)] with X hX hX1
    rw [Real.norm_of_nonneg (Real.log_nonneg hX1), Real.norm_of_nonneg (by linarith)] at hX
    calc 18 * C₂ * Real.log X ≤ 18 * C₂ * (1 / (18 * C₂) * X) :=
          mul_le_mul_of_nonneg_left hX hC.le
      _ = X := by field_simp
  have hF7 : ∀ᶠ X : ℝ in atTop, (N₀ : ℝ) + 1 ≤ Real.sqrt (X / 2) := by
    have : Tendsto (fun X : ℝ => Real.sqrt (X / 2)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
    exact this.eventually_ge_atTop _
  have hF8 : ∀ᶠ X : ℝ in atTop, Real.log (4096 * C₂) + 9 * Real.log (Real.log X)
      ≤ (Real.log (Real.log X)) ^ (2 : ℕ) := by
    have hev : ∀ᶠ s : ℝ in atTop, Real.log (4096 * C₂) + 9 * s ≤ s ^ (2 : ℕ) := by
      filter_upwards [eventually_ge_atTop (|Real.log (4096 * C₂)| + 10)] with s hs
      have h0 : 0 ≤ |Real.log (4096 * C₂)| := abs_nonneg _
      nlinarith [le_abs_self (Real.log (4096 * C₂))]
    exact hloglog.eventually hev
  have hF9 : ∀ᶠ X : ℝ in atTop, 4 * ((K₀ : ℝ) + 2) * Real.log 2 + 1
      ≤ (Real.log (Real.log X)) ^ (2 : ℕ) :=
    ((tendsto_pow_atTop (by norm_num)).comp hloglog).eventually_ge_atTop _
  have hF10 : ∀ᶠ X : ℝ in atTop, 8 * ((K₀ : ℝ) + 1) * Real.log 2
      ≤ (Real.log X - Real.log 2) ^ (3 : ℕ) := by
    have : Tendsto (fun X : ℝ => (Real.log X - Real.log 2) ^ (3 : ℕ)) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_right _ _ hlogX)
    exact this.eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (16 : ℝ), hlogX.eventually_ge_atTop (4 + Real.log 2),
    hF3, hF4, hF5, hF7, hF8, hF9, hF10] with X hX16 hXlog hX3 hX4 hX5 hX7 hX8 hX9 hX10
  intro h hh0 hlow hhigh
  exact growingMarker_count_at hσ hK₀ hε hbad hMstar hT2 hC₂9 hC₂T hX16 hXlog hX3 hX4 hX5 hX7
    hX8 hX9 hX10 hh0 hlow hhigh

open Classical in
/-- **Growing-block reciprocal-marker capacity.**  Let `log h = o(log X)` and let an auxiliary `w`
satisfy `√(log X)(log log X)² = o(w)` and `w = o(log h)`.  An absolute `c > 0` gives, for both
signs and all large `X`, at least `c·H log h/log X` integers `n ∈ (X, X+H]`, `H = √X h`, with
`μ(n) = σ`; every one of them is `n = a·p` with `p` prime, `p > √X > a` and `μ(a) = -σ`. -/
theorem growing_reciprocal_marker_capacity :
    ∃ c : ℝ, 0 < c ∧ ∀ h w : ℝ → ℝ, (∀ᶠ X in atTop, 0 < h X) →
      (fun X => Real.log (h X)) =o[atTop] Real.log →
      (fun X => Real.sqrt (Real.log X) * (Real.log (Real.log X)) ^ (2 : ℕ)) =o[atTop] w →
      w =o[atTop] (fun X => Real.log (h X)) →
      ∀ σ : ℤ, (σ = 1 ∨ σ = -1) → ∀ᶠ X : ℝ in atTop,
        c * (Real.sqrt X * h X * Real.log (h X) / Real.log X)
          ≤ ((((Finset.Ioc ⌊X⌋₊ ⌊X + Real.sqrt X * h X⌋₊).filter
              (fun n => moebius n = σ ∧ ReciprocalMarkerForm X σ n)).card : ℕ) : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := growingMarker_count_uniform
  refine ⟨c, hc, fun h w hpos h1 h2a h2b σ hσ => ?_⟩
  have h2 := h2a.trans h2b
  have hlogX : Tendsto (fun X : ℝ => Real.log X) atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hcount σ hσ, hpos, h2.bound (show (0 : ℝ) < 1 by norm_num),
    h1.bound (show (0 : ℝ) < 1 / 10 by norm_num), hlogX.eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℝ)] with X hX hh0 hb2 hb1 hlog1 hX0
  have hlogX0 : 0 < Real.log X := by linarith
  by_cases hlh : Real.log (h X) ≤ 0
  · have : c * (Real.sqrt X * h X * Real.log (h X) / Real.log X) ≤ 0 := by
      have h1' : Real.sqrt X * h X * Real.log (h X) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hlh
      exact mul_nonpos_of_nonneg_of_nonpos hc.le (div_nonpos_of_nonpos_of_nonneg h1' hlogX0.le)
    exact le_trans this (Nat.cast_nonneg _)
  · push Not at hlh
    rw [Real.norm_of_nonneg (by positivity), one_mul, Real.norm_of_nonneg hlh.le] at hb2
    rw [Real.norm_of_nonneg hlh.le, Real.norm_of_nonneg hlogX0.le] at hb1
    have hs1 : 1 ≤ Real.sqrt (Real.log X) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlog1
    have hlow : (Real.log (Real.log X)) ^ (2 : ℕ) ≤ Real.log (h X) := by
      have hsq0 : 0 ≤ (Real.log (Real.log X)) ^ (2 : ℕ) := sq_nonneg _
      nlinarith only [hb2, hs1, hsq0]
    exact hX (h X) hh0 hlow (by linarith)

open Classical in
/-- **The near-maximal subpower schedule.**  For `h(X) = exp(log X/log log X)` the window
`H = √X h = X^{1/2+o(1)}` contains `≫ H/log log X` integers of each Möbius sign, each a decoded
reciprocal-marker product. -/
theorem growing_reciprocal_marker_subpower_schedule :
    Tendsto (fun x : ℝ => Real.log (growingReciprocalMarkerWindow x) / Real.log x) atTop
        (𝓝 ((1 : ℝ) / 2))
      ∧ ∃ c : ℝ, 0 < c ∧ ∀ σ : ℤ, (σ = 1 ∨ σ = -1) → ∀ᶠ X : ℝ in atTop,
        c * (growingReciprocalMarkerWindow X / Real.log (Real.log X))
          ≤ ((((Finset.Ioc ⌊X⌋₊ ⌊X + growingReciprocalMarkerWindow X⌋₊).filter
              (fun n => moebius n = σ ∧ ReciprocalMarkerForm X σ n)).card : ℕ) : ℝ) := by
  refine ⟨tendsto_log_growingReciprocalMarkerWindow_div_log_half, ?_⟩
  obtain ⟨c, hc, hcap⟩ := growing_reciprocal_marker_capacity
  refine ⟨c, hc, fun σ hσ => ?_⟩
  have hlogX : Tendsto (fun X : ℝ => Real.log X) atTop atTop := Real.tendsto_log_atTop
  have hloglog : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogX
  have h1 : (fun X => Real.log (growingReciprocalMarkerH X)) =o[atTop] Real.log := by
    refine Asymptotics.isLittleO_of_tendsto' ?_ tendsto_log_growingReciprocalMarkerH_div_log
    filter_upwards [hlogX.eventually_gt_atTop 0] with X hX hX0
    exact absurd hX0 hX.ne'
  have h2a : (fun X => Real.sqrt (Real.log X) * (Real.log (Real.log X)) ^ (2 : ℕ))
      =o[atTop] growingReciprocalMarkerW := by
    refine Asymptotics.isLittleO_of_tendsto' ?_
      tendsto_sqrtLog_mul_logLog_sq_div_growingReciprocalMarkerW
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX hX0
    exact absurd hX0 (growingReciprocalMarkerW_pos hX).ne'
  have h2b : growingReciprocalMarkerW =o[atTop] (fun X => Real.log (growingReciprocalMarkerH X)) := by
    refine Asymptotics.isLittleO_of_tendsto' ?_ tendsto_growingReciprocalMarkerW_div_logH
    filter_upwards [hloglog.eventually_gt_atTop 0, hlogX.eventually_gt_atTop 0] with X hX hX' hX0
    rw [log_growingReciprocalMarkerH] at hX0
    exact absurd hX0 (div_pos hX' hX).ne'
  filter_upwards [hcap growingReciprocalMarkerH growingReciprocalMarkerW
      (Filter.Eventually.of_forall growingReciprocalMarkerH_pos) h1 h2a h2b σ hσ,
    hlogX.eventually_gt_atTop 0, hloglog.eventually_gt_atTop 0] with X hX hl0 hll0
  have hW : growingReciprocalMarkerWindow X = Real.sqrt X * growingReciprocalMarkerH X := rfl
  rw [hW]
  rw [log_growingReciprocalMarkerH] at hX
  have e : Real.sqrt X * growingReciprocalMarkerH X
        * (Real.log X / Real.log (Real.log X)) / Real.log X
      = Real.sqrt X * growingReciprocalMarkerH X / Real.log (Real.log X) := by
    field_simp
  rw [e] at hX
  exact hX

end

end RHTower.Sieve
