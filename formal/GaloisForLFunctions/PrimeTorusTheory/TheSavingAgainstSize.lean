import GaloisForLFunctions.PrimeTorusTheory.UniqueFactorizationPaysForNonAlignment

/-!
# The saving against size

How long does the orbit need to enter a half-space at length `y = (log T)^A`, `A > 1`? Is there any saving against size? Below the
Kronecker scale there is none: `exists_column_ge_of_primesUpTo` enters every half-space at level `m/(m+1)`. Past it:

**Theorem** (`saving_against_size`). For every `A > 1` and `δ > 0` and all large `T`, every `t ∈ [T, 2T]` satisfies

`Σ_{p ≤ (log T)^A} p^{−½} (1 − cos(t log p)) ≥ T^{−2/(A−1) − δ}`.

So the column sum of the critical weights never reaches its size on `[T, 2T]`, and the distance is a power of `T`. With `A = 2K` the
exponent is `2/(2K − 1)`. The saving is unconditional, it holds at every length past the Kronecker scale, and it is
polynomially small.

**Mechanism.** `le_of_aligned` at the last scale where squarefree products of `k` primes overflow the boxes of width `1/T`:
`k ≈ log T / ((A − 1) log log T)`, where `y^k = T^{A/(A−1)+o(1)}`. The distance of `t` to alignment is then at least `t/y^k`.

Nothing here is specific to `p^{−½}` beyond its lower bound `y^{−½}`: only the polylogarithmic factors change with the weight.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- Sublinear terms lose against any linear term. -/
theorem eventually_small {a : ℝ} (ha : 0 < a) (b c d : ℝ) :
    ∀ᶠ L : ℝ in atTop, b * (L / Real.log L) + c * Real.log L + d < a * L := by
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have h1 : Tendsto (fun L : ℝ => b / Real.log L) atTop (𝓝 0) :=
    hlog.const_div_atTop b
  have h2 : Tendsto (fun L : ℝ => c * (Real.log L / L)) atTop (𝓝 (c * 0)) := by
    have := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    exact this.const_mul c
  have h3 : Tendsto (fun L : ℝ => d / L) atTop (𝓝 0) := tendsto_id.const_div_atTop d
  have hsum := ((h1.add h2).add h3)
  have hlim : (0 + c * 0 + 0 : ℝ) = 0 := by ring
  rw [hlim] at hsum
  have hev := hsum.eventually (gt_mem_nhds ha)
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with L hL hL1
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL1
  have e : b * (L / Real.log L) + c * Real.log L + d =
      (b / Real.log L + c * (Real.log L / L) + d / L) * L := by
    field_simp
  rw [e]
  exact mul_lt_mul_of_pos_right hL hL0

/-- `C(d, k) ≥ (d/(2k))^k` for `2k ≤ d`. -/
theorem div_pow_le_choose {d k : ℕ} (hk : 1 ≤ k) (hkd : 2 * k ≤ d) :
    ((d : ℝ) / (2 * k)) ^ k ≤ (d.choose k : ℝ) := by
  have h := Nat.pow_le_choose (α := ℝ) k d
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hsub : (d : ℝ) / 2 ≤ ((d + 1 - k : ℕ) : ℝ) := by
    have h1 : k ≤ d + 1 := by omega
    rw [Nat.cast_sub h1]
    push_cast
    have : (2 : ℝ) * k ≤ d := by exact_mod_cast hkd
    linarith
  have hfac : ((k.factorial : ℕ) : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast Nat.factorial_le_pow k
  have hfac0 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  refine le_trans ?_ h
  rw [le_div_iff₀ hfac0]
  have e : ((d : ℝ) / (2 * k)) ^ k * (k : ℝ) ^ k = ((d : ℝ) / 2) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc
    ((d : ℝ) / (2 * k)) ^ k * (k.factorial : ℝ) ≤ ((d : ℝ) / (2 * k)) ^ k * (k : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = ((d : ℝ) / 2) ^ k := e
    _ ≤ ((d + 1 - k : ℕ) : ℝ) ^ k := pow_le_pow_left₀ hd0 hsub k

/-- The number of primes up to `y`, from Chebyshev's lower bound. -/
theorem card_primesUpTo_ge {y : ℕ} (hy : 2 ≤ y)
    (h : (y : ℝ) / 2 ≤ y * Real.log 2 - Real.log ((y : ℝ) + 1)) :
    (y : ℝ) / (2 * Real.log y) ≤ ((primesUpTo y).card : ℝ) := by
  have hcard : (primesUpTo y).card = Nat.primeCounting y := by
    unfold primesUpTo Nat.primeCounting Nat.primeCounting'
    rw [Nat.count_eq_card_filter_range]
  have hpi := Chebyshev.pi_ge y
  have hlog : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  rw [hcard]
  refine le_trans ?_ hpi
  rw [div_le_div_iff₀ (by positivity) hlog]
  nlinarith

/-- Chebyshev's elementary inequality, eventually. -/
theorem exists_chebyshev_threshold :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → x / 2 ≤ x * Real.log 2 - Real.log (x + 1) := by
  have hlog2 := Real.log_two_gt_d9
  have h := eventually_small (a := Real.log 2 - 1 / 2) (by linarith) 0 1 (Real.log 2)
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp (h.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max x₁ 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₁ x ((le_max_left _ _).trans hx)
  have hx0 : 0 < x := by linarith
  have hlog : Real.log (x + 1) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) hx0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  simp only [zero_mul, zero_add, one_mul] at h1
  nlinarith

/-- The parameters at which the pigeonhole applies, all eventually satisfied. -/
structure SavingConditions (A B δ c x₀ L : ℝ) : Prop where
  log_one : 1 ≤ Real.log L
  ratio_one : 1 ≤ B * L / Real.log L
  pow_large : 4 ≤ L ^ A
  pow_cheb : x₀ ≤ L ^ A / 2
  base : c ≤ (A - 1) * Real.log L
  pigeon : Real.log 2 + L + Real.log (4 * A * B * L) <
    B * L / Real.log L * ((A - 1) * Real.log L - c)
  gap : L + Real.log 2 ≤ B * L / Real.log L * (A * Real.log L - Real.log 2)
  product : 1 ≤ 4 * A * B * L
  decay : Real.exp (-(δ / 2 * L)) ≤
    1 / (32 * Real.pi ^ 2 * B ^ 2) * L ^ (-(A / 2 + 2 + 2 * A))

theorem eventually_savingConditions {A B δ c x₀ : ℝ} (hA : 1 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hmain : 1 < B * (A - 1)) (hAB : 1 < A * B) :
    ∀ᶠ L : ℝ in atTop, SavingConditions A B δ c x₀ L := by
  have hA0 : 0 < A := by linarith
  have hA1 : 0 < A - 1 := by linarith
  have hlog := Real.tendsto_log_atTop
  have h1 : ∀ᶠ L : ℝ in atTop, 1 ≤ Real.log L := hlog.eventually_ge_atTop 1
  have h2 := eventually_small hB 0 1 0
  have hpow := tendsto_rpow_atTop hA0
  have h3 : ∀ᶠ L : ℝ in atTop, 4 ≤ L ^ A := hpow.eventually_ge_atTop 4
  have h3' : ∀ᶠ L : ℝ in atTop, x₀ ≤ L ^ A / 2 := by
    filter_upwards [hpow.eventually_ge_atTop (2 * x₀)] with L hL
    linarith
  have h4 : ∀ᶠ L : ℝ in atTop, c ≤ (A - 1) * Real.log L :=
    (hlog.const_mul_atTop hA1).eventually_ge_atTop c
  have h5 := eventually_small (a := B * (A - 1) - 1) (by linarith) (c * B) 1
    (Real.log 2 + Real.log (4 * A * B))
  have h6 := eventually_small (a := A * B - 1) (by linarith) (B * Real.log 2) 0 (Real.log 2)
  have h7 : ∀ᶠ L : ℝ in atTop, 1 ≤ 4 * A * B * L :=
    (tendsto_id.const_mul_atTop (by positivity : 0 < 4 * A * B)).eventually_ge_atTop 1
  have h8 : ∀ᶠ L : ℝ in atTop, Real.exp (-(δ / 2 * L)) ≤
      1 / (32 * Real.pi ^ 2 * B ^ 2) * L ^ (-(A / 2 + 2 + 2 * A)) := by
    have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / 2 + 2 + 2 * A) (δ / 2)
      (by positivity)
    have hc : 0 < 1 / (32 * Real.pi ^ 2 * B ^ 2) := by positivity
    filter_upwards [hlim.eventually (gt_mem_nhds hc), eventually_gt_atTop (0 : ℝ)] with L hL hL0
    have hp : 0 < L ^ (A / 2 + 2 + 2 * A) := Real.rpow_pos_of_pos hL0 _
    rw [Real.rpow_neg hL0.le, mul_comm _ ((L ^ (A / 2 + 2 + 2 * A))⁻¹), ← div_eq_inv_mul,
      le_div_iff₀ hp, mul_comm]
    rw [neg_mul] at hL
    exact hL.le
  filter_upwards [h1, h2, h3, h3', h4, h5, h6, h7, h8, eventually_gt_atTop (1 : ℝ)]
    with L h1 h2 h3 h3' h4 h5 h6 h7 h8 hL1
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := by linarith
  refine ⟨h1, ?_, h3, h3', h4, ?_, ?_, h7, h8⟩
  · rw [le_div_iff₀ hlogL]
    simp only [zero_mul, zero_add, add_zero, one_mul] at h2
    linarith
  · have e : B * L / Real.log L * ((A - 1) * Real.log L - c) =
        B * (A - 1) * L - c * B * (L / Real.log L) := by
      field_simp
    have hl : Real.log (4 * A * B * L) = Real.log (4 * A * B) + Real.log L :=
      Real.log_mul (by positivity) hL0.ne'
    rw [e, hl]
    nlinarith
  · have e : B * L / Real.log L * (A * Real.log L - Real.log 2) =
        A * B * L - B * Real.log 2 * (L / Real.log L) := by
      field_simp
    rw [e]
    nlinarith

/-- The floor of `L^A` and its logarithm. -/
theorem floor_bounds {A L : ℝ} (hL : 1 < L) (hA : 0 < A) (hp : 4 ≤ L ^ A) :
    ((⌊L ^ A⌋₊ : ℕ) : ℝ) ≤ L ^ A ∧ L ^ A / 2 ≤ ((⌊L ^ A⌋₊ : ℕ) : ℝ) ∧ 2 ≤ ⌊L ^ A⌋₊ ∧
      Real.log ((⌊L ^ A⌋₊ : ℕ) : ℝ) ≤ A * Real.log L ∧
      A * Real.log L - Real.log 2 ≤ Real.log ((⌊L ^ A⌋₊ : ℕ) : ℝ) := by
  have hL0 : 0 < L := by linarith
  have hu : ((⌊L ^ A⌋₊ : ℕ) : ℝ) ≤ L ^ A := Nat.floor_le (by linarith)
  have hl : L ^ A / 2 ≤ ((⌊L ^ A⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (L ^ A)
    linarith
  have h2 : 2 ≤ ⌊L ^ A⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hpos : (0 : ℝ) < ((⌊L ^ A⌋₊ : ℕ) : ℝ) := by
    have : 0 < ⌊L ^ A⌋₊ := by omega
    exact_mod_cast this
  refine ⟨hu, hl, h2, ?_, ?_⟩
  · calc
      Real.log ((⌊L ^ A⌋₊ : ℕ) : ℝ) ≤ Real.log (L ^ A) := Real.log_le_log hpos hu
      _ = A * Real.log L := Real.log_rpow hL0 A
  · have hlow : Real.log (L ^ A / 2) ≤ Real.log ((⌊L ^ A⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hl
    rwa [Real.log_div (by positivity) (by norm_num), Real.log_rpow hL0 A] at hlow

/-- The pigeonhole condition at the chosen parameters. -/
theorem pigeon_of_conditions {A B δ x₀ T L t : ℝ} {y k : ℕ} (hA : 1 < A) (hB : 0 < B)
    (hcond : SavingConditions A B δ (Real.log (16 * A * B)) x₀ L) (hL1 : 1 < L) (hTL : T = Real.exp L)
    (ht : t ≤ 2 * T) (ht0 : 0 < t) (hyl : L ^ A / 2 ≤ (y : ℝ)) (hyu : (y : ℝ) ≤ L ^ A) (hy2 : 2 ≤ y)
    (hlogu : Real.log y ≤ A * Real.log L) (hkl : B * L / Real.log L ≤ (k : ℝ))
    (hk2 : (k : ℝ) ≤ 2 * (B * L / Real.log L)) (hk1 : 1 ≤ k)
    (hcheb : (y : ℝ) / 2 ≤ y * Real.log 2 - Real.log ((y : ℝ) + 1)) :
    ⌊t * k * Real.log y / Real.pi⌋₊ + 1 < (primesUpTo y).card.choose k := by
  have hA0 : 0 < A := by linarith
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := by linarith [hcond.log_one]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  -- The number of primes.
  have hd := card_primesUpTo_ge hy2 hcheb
  set d := (primesUpTo y).card with hddef
  have hLA : L ^ A = L ^ (A - 1) * L := by
    rw [← Real.rpow_add_one hL0.ne']
    congr 1
    ring
  have hZpos : 0 < L ^ (A - 1) / (16 * A * B) := by positivity
  have hdlow : L ^ A / (4 * A * Real.log L) ≤ (d : ℝ) := by
    refine le_trans ?_ hd
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (L ^ A / 2) * (2 * Real.log y) ≤ (y : ℝ) * (2 * Real.log y) :=
      mul_le_mul_of_nonneg_right hyl (by positivity)
    have h2 : L ^ A * Real.log y ≤ L ^ A * (A * Real.log L) :=
      mul_le_mul_of_nonneg_left hlogu (by positivity)
    nlinarith
  -- The base of the count.
  have hbase : L ^ (A - 1) / (16 * A * B) ≤ (d : ℝ) / (2 * k) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have e : L ^ A / (4 * A * Real.log L) * (16 * A * B) = L ^ A * (4 * B) / Real.log L := by
      rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
      ring
    calc
      L ^ (A - 1) * (2 * (k : ℝ)) ≤ L ^ (A - 1) * (4 * (B * L / Real.log L)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = L ^ A / (4 * A * Real.log L) * (16 * A * B) := by
        rw [e, hLA]
        ring
      _ ≤ (d : ℝ) * (16 * A * B) := mul_le_mul_of_nonneg_right hdlow (by positivity)
  have hlogZ : Real.log (L ^ (A - 1) / (16 * A * B)) = (A - 1) * Real.log L - Real.log (16 * A * B) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_rpow hL0]
  have hZ1 : 1 ≤ L ^ (A - 1) / (16 * A * B) := by
    rw [← Real.log_nonneg_iff hZpos, hlogZ]
    linarith [hcond.base]
  have h2kd : 2 * k ≤ d := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) / (2 * k) := hZ1.trans hbase
    rw [le_div_iff₀ (by positivity)] at h1
    have : ((2 * k : ℕ) : ℝ) ≤ (d : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hchoose := div_pow_le_choose hk1 h2kd
  have hpowZ : (L ^ (A - 1) / (16 * A * B)) ^ k ≤ (d.choose k : ℝ) :=
    (pow_le_pow_left₀ hZpos.le hbase k).trans hchoose
  -- The lower bound of the count in exponential form.
  have hexpZ : Real.exp (B * L / Real.log L * ((A - 1) * Real.log L - Real.log (16 * A * B))) ≤
      (L ^ (A - 1) / (16 * A * B)) ^ k := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hZpos, hlogZ]
    refine Real.exp_le_exp.mpr ?_
    have hnn : 0 ≤ (A - 1) * Real.log L - Real.log (16 * A * B) := by linarith [hcond.base]
    rw [mul_comm ((A - 1) * Real.log L - Real.log (16 * A * B))]
    exact mul_le_mul_of_nonneg_right hkl hnn
  -- The number of boxes.
  have hTpos : 0 < T := by rw [hTL]; exact Real.exp_pos _
  have hT1 : 1 ≤ T := by
    rw [hTL]
    exact Real.one_le_exp hL0.le
  have hboxes : (⌊t * k * Real.log y / Real.pi⌋₊ : ℝ) + 1 ≤ 2 * T * (4 * A * B * L) := by
    have hx0 : 0 ≤ t * k * Real.log y / Real.pi := by positivity
    have h1 := Nat.floor_le hx0
    have hpi := Real.pi_gt_three
    have h2 : (k : ℝ) * Real.log y ≤ 2 * (A * B * L) := by
      have e : 2 * (B * L / Real.log L) * (A * Real.log L) = 2 * (A * B * L) := by
        field_simp
      calc
        (k : ℝ) * Real.log y ≤ 2 * (B * L / Real.log L) * (A * Real.log L) :=
          mul_le_mul hk2 hlogu hlogy.le (by positivity)
        _ = 2 * (A * B * L) := e
    have h3 : t * k * Real.log y / Real.pi ≤ t * k * Real.log y := by
      refine div_le_self (by positivity) (by linarith)
    have h4 : t * k * Real.log y ≤ 2 * T * (2 * (A * B * L)) := by
      rw [mul_assoc t]
      exact mul_le_mul ht h2 (by positivity) (by positivity)
    have h5 := hcond.product
    have h6 : (1 : ℝ) ≤ T * (4 * A * B * L) := by nlinarith
    nlinarith
  have hexpB : 2 * T * (4 * A * B * L) = Real.exp (Real.log 2 + L + Real.log (4 * A * B * L)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), ← hTL,
      Real.exp_log (by positivity)]
  have hlt : (⌊t * k * Real.log y / Real.pi⌋₊ : ℝ) + 1 < (d.choose k : ℝ) := by
    calc
      (⌊t * k * Real.log y / Real.pi⌋₊ : ℝ) + 1 ≤ 2 * T * (4 * A * B * L) := hboxes
      _ = Real.exp (Real.log 2 + L + Real.log (4 * A * B * L)) := hexpB
      _ < Real.exp (B * L / Real.log L * ((A - 1) * Real.log L - Real.log (16 * A * B))) :=
        Real.exp_lt_exp.mpr hcond.pigeon
      _ ≤ _ := hexpZ.trans hpowZ
  exact_mod_cast hlt

/-- The cancellation in the final lower bound. -/
theorem final_algebra {a b c d e f p B : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) (hp : p ≠ 0) (hB : B ≠ 0)
    (h : e * f * (c * d) = a * b) :
    a * (2 / p ^ 2 * (b / (64 * B ^ 2 * c * d))) = 1 / (32 * p ^ 2 * B ^ 2) * e * f := by
  have e1 : a * (2 / p ^ 2 * (b / (64 * B ^ 2 * c * d))) = (a * b) * (2 / (p ^ 2 * (64 * B ^ 2 * c * d))) := by
    field_simp
  rw [e1, ← h]
  field_simp
  try ring

/-- The exponential size of the final lower bound. -/
theorem final_lower_bound {A B δ T L w ε : ℝ} (hA : 1 < A) (hB : 0 < B)
    (hcond : Real.exp (-(δ / 2 * L)) ≤ 1 / (32 * Real.pi ^ 2 * B ^ 2) * L ^ (-(A / 2 + 2 + 2 * A)))
    (hL0 : 0 < L) (hTL : T = Real.exp L) (hw : Real.exp (-(A / 2 * Real.log L)) ≤ w)
    (hε : T / (8 * B * L * Real.exp (A * B * L + A * Real.log L)) ≤ ε) :
    Real.exp (-((2 * (A * B) - 2 + δ / 2) * L)) ≤ w * (2 / Real.pi ^ 2 * ε ^ 2) := by
  have hA0 : 0 < A := by linarith
  have hpi := Real.pi_pos
  set E := Real.exp (A * B * L + A * Real.log L) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hT0 : 0 < T := by rw [hTL]; exact Real.exp_pos _
  have hε0 : 0 ≤ T / (8 * B * L * E) := by positivity
  have hε2 : (T / (8 * B * L * E)) ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hε0 hε 2
  have hw0 : 0 ≤ Real.exp (-(A / 2 * Real.log L)) := (Real.exp_pos _).le
  have hstep : Real.exp (-(A / 2 * Real.log L)) * (2 / Real.pi ^ 2 * (T / (8 * B * L * E)) ^ 2) ≤
      w * (2 / Real.pi ^ 2 * ε ^ 2) := by
    refine mul_le_mul hw ?_ (by positivity) ((Real.exp_pos _).le.trans hw)
    exact mul_le_mul_of_nonneg_left hε2 (by positivity)
  refine le_trans ?_ hstep
  -- Everything in exponentials of `L` and `log L`.
  have hLexp : L = Real.exp (Real.log L) := (Real.exp_log hL0).symm
  have hrp : L ^ (-(A / 2 + 2 + 2 * A)) = Real.exp (-(A / 2 + 2 + 2 * A) * Real.log L) := by
    rw [Real.rpow_def_of_pos hL0]
    congr 1
    ring
  rw [hrp] at hcond
  have hval : Real.exp (-(A / 2 * Real.log L)) * (2 / Real.pi ^ 2 * (T / (8 * B * L * E)) ^ 2) =
      1 / (32 * Real.pi ^ 2 * B ^ 2) * Real.exp (-(A / 2 + 2 + 2 * A) * Real.log L) *
        Real.exp (-((2 * (A * B) - 2) * L)) := by
    have e1 : (T / (8 * B * L * E)) ^ 2 = T ^ 2 / (64 * B ^ 2 * L ^ 2 * E ^ 2) := by
      rw [div_pow]
      congr 1
      ring
    have e2 : T ^ 2 = Real.exp (2 * L) := by
      rw [hTL, sq, ← Real.exp_add]
      congr 1
      ring
    have e3 : E ^ 2 = Real.exp (2 * (A * B * L) + 2 * (A * Real.log L)) := by
      rw [hE, sq, ← Real.exp_add]
      congr 1
      ring
    have e4 : L ^ 2 = Real.exp (2 * Real.log L) := by
      have h4 : Real.exp (2 * Real.log L) = Real.exp (Real.log L) * Real.exp (Real.log L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h4, Real.exp_log hL0, sq]
    have hcomb : Real.exp (-(A / 2 + 2 + 2 * A) * Real.log L) * Real.exp (-((2 * (A * B) - 2) * L)) *
        (Real.exp (2 * Real.log L) * Real.exp (2 * (A * B * L) + 2 * (A * Real.log L))) =
        Real.exp (-(A / 2 * Real.log L)) * Real.exp (2 * L) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [e1, e2, e3, e4]
    exact final_algebra (Real.exp_pos _).ne' (Real.exp_pos _).ne' hpi.ne' hB.ne' hcomb
  rw [hval]
  have hsplit : Real.exp (-((2 * (A * B) - 2 + δ / 2) * L)) =
      Real.exp (-(δ / 2 * L)) * Real.exp (-((2 * (A * B) - 2) * L)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hcond (Real.exp_pos _).le

/-- The saving at fixed parameters. -/
theorem saving_at_parameters {A B δ x₀ T L t : ℝ} {y k : ℕ} (hA : 1 < A) (hB : 0 < B)
    (hcond : SavingConditions A B δ (Real.log (16 * A * B)) x₀ L) (hL1 : 1 < L) (hTL : T = Real.exp L)
    (ht : t ∈ Set.Icc T (2 * T)) (hyl : L ^ A / 2 ≤ (y : ℝ)) (hyu : (y : ℝ) ≤ L ^ A) (hy2 : 2 ≤ y)
    (hlogu : Real.log y ≤ A * Real.log L) (hlogl : A * Real.log L - Real.log 2 ≤ Real.log y)
    (hkl : B * L / Real.log L ≤ (k : ℝ)) (hku : (k : ℝ) ≤ B * L / Real.log L + 1) (hk1 : 1 ≤ k)
    (hcheb : (y : ℝ) / 2 ≤ y * Real.log 2 - Real.log ((y : ℝ) + 1)) :
    Real.exp (-((2 * (A * B) - 2 + δ / 2) * L)) ≤
      ∑ p ∈ primesUpTo y, (p : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.cos (t * Real.log p)) := by
  have hA0 : 0 < A := by linarith
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by rw [hTL]; exact Real.exp_pos _
  have hlogL : 1 ≤ Real.log L := hcond.log_one
  have hlogpos : 0 < Real.log L := by linarith
  have hy1 : 1 ≤ y := by omega
  have hyr0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy1
  have hlogy : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hratio := hcond.ratio_one
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hk2 : (k : ℝ) ≤ 2 * (B * L / Real.log L) := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le hT0 ht.1
  have hpig := pigeon_of_conditions hA hB hcond hL1 hTL ht.2 ht0 hyl hyu hy2 hlogu hkl hk2 hk1 hcheb
  have hykexp : (y : ℝ) ^ k = Real.exp (k * Real.log y) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hyr0, mul_comm]
  have hyk0 : 0 < (y : ℝ) ^ k := by positivity
  have hgap : 2 * T ≤ (y : ℝ) ^ k := by
    have h1 : L + Real.log 2 ≤ k * Real.log y := by
      refine hcond.gap.trans ?_
      calc
        B * L / Real.log L * (A * Real.log L - Real.log 2) ≤ B * L / Real.log L * Real.log y :=
          mul_le_mul_of_nonneg_left hlogl (by positivity)
        _ ≤ k * Real.log y := mul_le_mul_of_nonneg_right hkl hlogy.le
    have h2 : Real.exp (L + Real.log 2) ≤ (y : ℝ) ^ k := by
      rw [hykexp]
      exact Real.exp_le_exp.mpr h1
    rw [Real.exp_add, ← hTL, Real.exp_log (show (0 : ℝ) < 2 by norm_num)] at h2
    linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (A * B * L + A * Real.log L) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hykE : (y : ℝ) ^ k ≤ E := by
    rw [hykexp, hE]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (k : ℝ) * Real.log y ≤ (B * L / Real.log L + 1) * (A * Real.log L) :=
      mul_le_mul hku hlogu hlogy.le (by positivity)
    have e : (B * L / Real.log L + 1) * (A * Real.log L) = A * B * L + A * Real.log L := by
      field_simp
    linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = t / (4 * k * (y : ℝ) ^ k) := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hεeq : 2 * (k : ℝ) * ε = t / (2 * (y : ℝ) ^ k) := by
    rw [hε]
    field_simp
    ring
  have hεpi : 2 * (k : ℝ) * ε < Real.pi := by
    rw [hεeq]
    have h1 : t / (2 * (y : ℝ) ^ k) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [ht.2]
    linarith [Real.pi_gt_three]
  have hεlt : 2 * (k : ℝ) * ε * (y : ℝ) ^ k < t := by
    rw [hεeq]
    have e : t / (2 * (y : ℝ) ^ k) * (y : ℝ) ^ k = t / 2 := by
      field_simp
    rw [e]
    linarith
  have hha : ∀ r ∈ primesUpTo y, 0 ≤ (r : ℝ) ^ (-(1 / 2 : ℝ)) := fun r _ =>
    Real.rpow_nonneg (Nat.cast_nonneg r) _
  have hw : ∀ p ∈ primesUpTo y, (y : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro p hp
    refine Real.rpow_le_rpow_of_nonpos ?_ ?_ (by norm_num)
    · exact_mod_cast (prime_of_mem_primesUpTo hp).pos
    · exact_mod_cast le_of_mem_primesUpTo hp
  have hD := defect_ge_of_pigeonhole (Q := primesUpTo y) (a := fun p : ℕ => (p : ℝ) ^ (-(1 / 2 : ℝ)))
    hha (y := y) (k := k) (t := t) (ε := ε) (w := (y : ℝ) ^ (-(1 / 2 : ℝ))) ht0 hy1 hε0
    (fun r hr => prime_of_mem_primesUpTo hr) (fun r hr => le_of_mem_primesUpTo hr) hw hεpi hεlt hpig
  rw [primeSystem_defect] at hD
  refine le_trans ?_ hD
  have hwlow : Real.exp (-(A / 2 * Real.log L)) ≤ (y : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hyr0]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hεlow : T / (8 * B * L * E) ≤ ε := by
    rw [hε]
    have hkL : (k : ℝ) ≤ 2 * (B * L) := by
      refine hk2.trans ?_
      have : B * L / Real.log L ≤ B * L := div_le_self (by positivity) hlogL
      linarith
    have hden : 4 * (k : ℝ) * (y : ℝ) ^ k ≤ 8 * B * L * E := by
      have := mul_le_mul hkL hykE hyk0.le (by positivity)
      nlinarith
    calc
      T / (8 * B * L * E) ≤ t / (8 * B * L * E) :=
        div_le_div_of_nonneg_right ht.1 (by positivity)
      _ ≤ t / (4 * k * (y : ℝ) ^ k) :=
        div_le_div_of_nonneg_left ht0.le (by positivity) hden
  rw [hE] at hεlow
  exact final_lower_bound hA hB hcond.decay hL0 hTL hwlow hεlow

/-- **The saving against size.** See the module docstring. -/
theorem saving_against_size {A δ : ℝ} (hA : 1 < A) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, ∀ T, T₀ ≤ T → ∀ t ∈ Set.Icc T (2 * T),
      T ^ (-(2 / (A - 1) + δ)) ≤
        ∑ p ∈ primesUpTo ⌊Real.log T ^ A⌋₊,
          (p : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - Real.cos (t * Real.log p)) := by
  have hA0 : 0 < A := by linarith
  have hA1 : 0 < A - 1 := by linarith
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : ℝ, δ₁ = δ * (A - 1) / (4 * A) := ⟨_, rfl⟩
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (1 + δ₁) / (A - 1) := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  have hBA : B * (A - 1) = 1 + δ₁ := by
    rw [hB]
    field_simp
  have hAB : A * B = A / (A - 1) + δ / 4 := by
    rw [hB, hδ₁]
    field_simp
  have hABgt : 1 < A * B := by
    rw [hAB]
    have : 1 < A / (A - 1) := by
      rw [lt_div_iff₀ hA1]
      linarith
    linarith
  have hexp2 : 2 * (A * B) - 2 + δ / 2 = 2 / (A - 1) + δ := by
    rw [hAB]
    field_simp
    ring
  obtain ⟨x₀, -, hx₀⟩ := exists_chebyshev_threshold
  have hev := Real.tendsto_log_atTop.eventually
    (eventually_savingConditions (A := A) (B := B) (δ := δ) (c := Real.log (16 * A * B)) (x₀ := x₀)
      hA hB0 hδ (by rw [hBA]; linarith) hABgt)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hev.and (eventually_gt_atTop (1 : ℝ)))
  refine ⟨T₁, fun T hT t ht => ?_⟩
  obtain ⟨hcond, hT1⟩ := hT₁ T hT
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := Real.log_pos hT1
  have hL1 : 1 < Real.log T := by
    have h1 := (Real.le_log_iff_exp_le hL0).mp hcond.log_one
    have h2 := Real.exp_one_gt_d9
    linarith
  obtain ⟨hyu, hyl, hy2, hlogu, hlogl⟩ := floor_bounds hL1 hA0 hcond.pow_large
  have hlogpos : 0 < Real.log (Real.log T) := by linarith [hcond.log_one]
  have hkl := Nat.le_ceil (B * Real.log T / Real.log (Real.log T))
  have hku : ((⌈B * Real.log T / Real.log (Real.log T)⌉₊ : ℕ) : ℝ) ≤
      B * Real.log T / Real.log (Real.log T) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : 1 ≤ ⌈B * Real.log T / Real.log (Real.log T)⌉₊ := by
    have : (1 : ℝ) ≤ ((⌈B * Real.log T / Real.log (Real.log T)⌉₊ : ℕ) : ℝ) :=
      hcond.ratio_one.trans hkl
    exact_mod_cast this
  have hcheb := hx₀ _ (hcond.pow_cheb.trans hyl)
  have hfin := saving_at_parameters hA hB0 hcond hL1 (Real.exp_log hT0).symm ht hyl hyu hy2 hlogu
    hlogl hkl hku hk1 hcheb
  rw [Real.rpow_def_of_pos hT0, ← hexp2]
  have e : Real.log T * -(2 * (A * B) - 2 + δ / 2) = -((2 * (A * B) - 2 + δ / 2) * Real.log T) := by
    ring
  rw [e]
  exact hfin

end

end GaloisForLFunctions.PrimeTorusTheory
