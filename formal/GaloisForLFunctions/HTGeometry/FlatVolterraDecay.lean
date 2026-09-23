import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The flat backward Volterra decay lemma

A nonnegative sequence whose backward tail satisfies

`q n ≤ A · ∑_{m ≥ n} q m / m + C e^{-δ n}`

and which is already superpolynomially small is in fact exponentially small at every rate below
`δ`.  The mechanism is a discrete integrating factor: the tail `Q n = ∑_{m ≥ n} q m / m` obeys
`Q (n+1) ≥ (1 - A/n) Q n - C e^{-δ n}/n`, and for a natural `B > A` the polynomial weight `n^B`
satisfies `(n/(n+1))^B ≤ 1 - A/n` on a terminal ray.  Hence `n ↦ Q n · n^B` decreases up to a
summable exponential defect; superpolynomial flatness kills the terminal term of the telescoping
sum, and what is left is the exponential tail.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The polynomial weight compares to the Volterra factor on a terminal ray. -/
theorem pow_div_succ_le_one_sub {A : ℝ} (hA : 0 ≤ A) {B : ℕ} (hAB : A < B) {n : ℕ}
    (hn : 0 < n) (hlarge : A * B ≤ (B - A) * n) :
    ((n : ℝ) / (n + 1)) ^ B ≤ 1 - A / n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hB0 : (0:ℝ) < B := lt_of_le_of_lt hA hAB
  have hbern : 1 + (B : ℝ) * (1 / (n:ℝ)) ≤ (1 + 1 / (n:ℝ)) ^ B := by
    have hge : (-2 : ℝ) ≤ 1 / (n:ℝ) := by
      have : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
      linarith
    exact one_add_mul_le_pow hge B
  have hpos : (0:ℝ) < 1 + 1 / (n:ℝ) := by positivity
  have hstep : ((n : ℝ) / (n + 1)) ^ B ≤ (n : ℝ) / (n + B) := by
    have hfrac : (n : ℝ) / ((n:ℝ) + 1) = (1 + 1 / (n:ℝ))⁻¹ := by
      rw [eq_comm, inv_eq_iff_eq_inv, inv_div]
      field_simp
    rw [hfrac, inv_pow]
    have hle : (1 : ℝ) + (B:ℝ) / (n:ℝ) ≤ (1 + 1 / (n:ℝ)) ^ B := by
      have hBn : (B : ℝ) * (1 / (n:ℝ)) = (B:ℝ) / (n:ℝ) := by ring
      linarith [hbern, hBn]
    have hbpos : (0:ℝ) < 1 + (B:ℝ) / n := by positivity
    have hppos : (0:ℝ) < (1 + 1 / (n:ℝ)) ^ B := by positivity
    have hinv : ((1 + 1 / (n:ℝ)) ^ B)⁻¹ ≤ (1 + (B:ℝ) / n)⁻¹ := by
      exact inv_anti₀ hbpos hle
    have hval : (1 + (B:ℝ) / (n:ℝ))⁻¹ = (n : ℝ) / ((n:ℝ) + B) := by
      rw [eq_div_iff (by positivity), inv_mul_eq_div, div_eq_iff (by positivity)]
      field_simp
    rw [← hval]
    exact hinv
  have hfinal : (n : ℝ) / (n + B) ≤ 1 - A / n := by
    rw [div_le_iff₀ (by positivity)]
    have hexpand : (1 - A / n) * ((n:ℝ) + B) = (n + B) - A * (n + B) / n := by
      field_simp
    rw [hexpand]
    have hkey : A * ((n:ℝ) + B) / n ≤ B := by
      rw [div_le_iff₀ hn0]
      nlinarith [hlarge]
    linarith
  exact le_trans hstep hfinal

/-- **The flat Volterra decay lemma.**  A superpolynomially flat sequence controlled by its own
weighted backward tail plus an exponential source decays at every rate below the source rate. -/
theorem flat_volterra_decay {q Q : ℕ → ℝ} {A C δ δ' : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hδ' : 0 < δ') (hlt : δ' < δ)
    (hQ0 : ∀ n, 0 ≤ Q n)
    (hstep : ∀ᶠ n : ℕ in atTop, Q (n + 1) = Q n - q n / n)
    (hrec : ∀ᶠ n : ℕ in atTop, q n ≤ A * Q n + C * Real.exp (-δ * n))
    (hflat : ∀ N : ℕ, Tendsto (fun n : ℕ => (n : ℝ) ^ N * Q n) atTop (𝓝 0)) :
    ∃ C' : ℝ, ∀ᶠ n : ℕ in atTop, q n ≤ C' * Real.exp (-δ' * n) := by
  classical
  set B : ℕ := ⌈A⌉₊ + 1 with hBdef
  have hAB : A < B := by
    have h := Nat.le_ceil A
    have : (⌈A⌉₊ : ℝ) < (⌈A⌉₊ : ℝ) + 1 := by linarith
    calc A ≤ (⌈A⌉₊ : ℝ) := h
      _ < (⌈A⌉₊ : ℝ) + 1 := this
      _ = B := by rw [hBdef]; push_cast; ring
  have hε : 0 < δ - δ' := by linarith
  -- the defect sequence and its summability
  set c : ℕ → ℝ := fun m => C * Real.exp (-δ * m) * ((m : ℝ) + 1) ^ B / m with hcdef
  have hcnn : ∀ m : ℕ, 0 ≤ c m := by
    intro m
    rw [hcdef]
    positivity
  have hcsummable : Summable c := by
    have hbase : Summable fun m : ℕ => ((m : ℝ) + 1) ^ B * Real.exp (-δ * ((m : ℝ) + 1)) := by
      have h := Real.summable_pow_mul_exp_neg_nat_mul B (r := δ) (by linarith)
      have hshift := (summable_nat_add_iff 1).mpr h
      refine hshift.congr fun m => ?_
      push_cast
      ring
    have hmul : Summable fun m : ℕ =>
        (C * Real.exp δ) * (((m : ℝ) + 1) ^ B * Real.exp (-δ * ((m : ℝ) + 1))) :=
      hbase.mul_left _
    refine Summable.of_nonneg_of_le hcnn (fun m => ?_) hmul
    rw [hcdef]
    have hexp : Real.exp (-δ * ((m : ℝ) + 1)) * Real.exp δ = Real.exp (-δ * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [Nat.cast_zero, div_zero]
      positivity
    · have hm0 : (1:ℝ) ≤ m := by exact_mod_cast hm
      have hden : C * Real.exp (-δ * m) * ((m : ℝ) + 1) ^ B / m
          ≤ C * Real.exp (-δ * m) * ((m : ℝ) + 1) ^ B :=
        div_le_self (by positivity) hm0
      refine le_trans hden (le_of_eq ?_)
      rw [← hexp]
      ring
  -- a terminal ray on which every ingredient is available
  have hgoal : ∀ᶠ n : ℕ in atTop,
      Q n * (n : ℝ) ^ B ≤ Q (n + 1) * ((n : ℝ) + 1) ^ B + c n := by
    have hbig : ∀ᶠ n : ℕ in atTop, (A * B ≤ ((B : ℝ) - A) * n ∧ 0 < n) := by
      have hBA : 0 < (B : ℝ) - A := by linarith
      have hlin : Tendsto (fun n : ℕ => ((B : ℝ) - A) * n) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hBA tendsto_natCast_atTop_atTop
      filter_upwards [hlin.eventually_ge_atTop (A * B), eventually_gt_atTop 0] with n h1 h2
      exact ⟨h1, h2⟩
    filter_upwards [hstep, hrec, hbig] with n hs hr ⟨hlarge, hn⟩
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    have hcomp := pow_div_succ_le_one_sub hA hAB hn hlarge
    have hlow : Q (n + 1) ≥ (1 - A / n) * Q n - C * Real.exp (-δ * n) / n := by
      rw [hs]
      have hdiv : q n / n ≤ (A * Q n + C * Real.exp (-δ * n)) / n := by
        gcongr
      have hsplit : (A * Q n + C * Real.exp (-δ * n)) / n
          = (A / n) * Q n + C * Real.exp (-δ * n) / n := by
        field_simp
      rw [hsplit] at hdiv
      have : (1 - A / n) * Q n = Q n - (A / n) * Q n := by ring
      linarith
    have hweight : ((n : ℝ) / (n + 1)) ^ B * Q n ≤ (1 - A / n) * Q n :=
      mul_le_mul_of_nonneg_right hcomp (hQ0 n)
    have hlow' : Q (n + 1) ≥ ((n : ℝ) / (n + 1)) ^ B * Q n - C * Real.exp (-δ * n) / n := by
      linarith
    have hmul := mul_le_mul_of_nonneg_right hlow'
      (le_of_lt (by positivity : (0:ℝ) < ((n : ℝ) + 1) ^ B))
    have hexpand : (((n : ℝ) / (n + 1)) ^ B * Q n - C * Real.exp (-δ * n) / n)
        * ((n : ℝ) + 1) ^ B = Q n * (n : ℝ) ^ B - c n := by
      rw [hcdef, div_pow]
      field_simp
    rw [hexpand] at hmul
    linarith
  -- telescoping to the terminal limit
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hgoal
  have htele : ∀ n, n₁ ≤ n → ∀ N, n ≤ N →
      Q n * (n : ℝ) ^ B ≤ Q N * (N : ℝ) ^ B + ∑ m ∈ Finset.Ico n N, c m := by
    intro n hn N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
        have hstepN := hn₁ N (le_trans hn hN)
        have hIco : ∑ m ∈ Finset.Ico n (N + 1), c m = (∑ m ∈ Finset.Ico n N, c m) + c N := by
          rw [Finset.sum_Ico_succ_top hN]
        rw [hIco]
        have hcast : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [hcast] at hstepN
        linarith
  have hzero : Tendsto (fun N : ℕ => Q N * (N : ℝ) ^ B) atTop (𝓝 0) := by
    have h := hflat B
    refine h.congr fun N => ?_
    ring
  have hTail : ∀ n, n₁ ≤ n → Q n * (n : ℝ) ^ B ≤ ∑' k : ℕ, c (n + k) := by
    intro n hn
    have hlim : Tendsto (fun N : ℕ => Q N * (N : ℝ) ^ B + ∑' k : ℕ, c (n + k)) atTop
        (𝓝 (0 + ∑' k : ℕ, c (n + k))) := hzero.add tendsto_const_nhds
    rw [zero_add] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    refine le_trans (htele n hn N hN) ?_
    have hpart : ∑ m ∈ Finset.Ico n N, c m ≤ ∑' k : ℕ, c (n + k) := by
      have hshift : Summable fun k : ℕ => c (n + k) := by
        have h := (summable_nat_add_iff n).mpr hcsummable
        exact h.congr fun k => by rw [Nat.add_comm]
      have hsub : ∑ m ∈ Finset.Ico n N, c m
          = ∑ k ∈ Finset.range (N - n), c (n + k) := by
        rw [Finset.sum_Ico_eq_sum_range]
      rw [hsub]
      exact Summable.sum_le_tsum _ (fun k _ => hcnn (n + k)) hshift
    linarith
  -- the exponential bound for the tail
  have hsmall : ∀ᶠ m : ℕ in atTop, ((m : ℝ) + 1) ^ B * Real.exp (-(δ - δ') * m) ≤ 1 := by
    have hlim : Tendsto (fun m : ℕ => ((m : ℝ) + 1) ^ B * Real.exp (-(δ - δ') * m)) atTop
        (𝓝 0) := by
      have hsum := Real.summable_pow_mul_exp_neg_nat_mul B (r := δ - δ') hε
      have hshift := (summable_nat_add_iff 1).mpr hsum
      have hcongr : ∀ m : ℕ, ((m + 1 : ℕ) : ℝ) ^ B * Real.exp (-(δ - δ') * ((m + 1 : ℕ) : ℝ))
          = ((m : ℝ) + 1) ^ B * Real.exp (-(δ - δ') * ((m : ℝ) + 1)) := by
        intro m
        push_cast
        ring
      have hsum2 : Summable fun m : ℕ => ((m : ℝ) + 1) ^ B * Real.exp (-(δ - δ') * ((m : ℝ) + 1)) :=
        hshift.congr hcongr
      have hz := hsum2.tendsto_atTop_zero
      have hfac : ∀ m : ℕ, ((m : ℝ) + 1) ^ B * Real.exp (-(δ - δ') * m)
          = (((m : ℝ) + 1) ^ B * Real.exp (-(δ - δ') * ((m : ℝ) + 1))) * Real.exp (δ - δ') := by
        intro m
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      have := hz.mul_const (Real.exp (δ - δ'))
      rw [zero_mul] at this
      exact this.congr fun m => (hfac m).symm
    filter_upwards [hlim.eventually_le_const (show (0:ℝ) < 1 by norm_num)] with m hm
    exact hm
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp hsmall
  set K : ℝ := C / (1 - Real.exp (-δ')) with hKdef
  have hgeo : Real.exp (-δ') < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeopos : (0:ℝ) < 1 - Real.exp (-δ') := by linarith
  have hbound : ∀ n, max n₁ (max n₂ 1) ≤ n →
      (∑' k : ℕ, c (n + k)) ≤ K * Real.exp (-δ' * n) := by
    intro n hn
    have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right n₁ _)) hn
    have hnpos : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right n₁ _)) hn
    have hterm : ∀ k : ℕ, c (n + k) ≤ C * Real.exp (-δ' * (n + k)) := by
      intro k
      have hm2 : n₂ ≤ n + k := le_trans hn2 (Nat.le_add_right n k)
      have hmpos : (1:ℝ) ≤ ((n + k : ℕ) : ℝ) := by
        have : 1 ≤ n + k := le_trans hnpos (Nat.le_add_right n k)
        exact_mod_cast this
      have hsm := hn₂ (n + k) hm2
      have hcm : c (n + k) ≤ C * Real.exp (-δ * ((n + k : ℕ) : ℝ)) * (((n + k : ℕ) : ℝ) + 1) ^ B := by
        rw [hcdef]
        exact div_le_self (by positivity) hmpos
      have hsplit : Real.exp (-δ * ((n + k : ℕ) : ℝ))
          = Real.exp (-δ' * ((n + k : ℕ) : ℝ)) * Real.exp (-(δ - δ') * ((n + k : ℕ) : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hfinal : C * Real.exp (-δ * ((n + k : ℕ) : ℝ)) * (((n + k : ℕ) : ℝ) + 1) ^ B
          ≤ C * Real.exp (-δ' * ((n + k : ℕ) : ℝ)) := by
        rw [hsplit]
        have hpos : (0:ℝ) ≤ C * Real.exp (-δ' * ((n + k : ℕ) : ℝ)) := by positivity
        nlinarith [hsm, Real.exp_pos (-(δ - δ') * ((n + k : ℕ) : ℝ)),
          pow_nonneg (by positivity : (0:ℝ) ≤ ((n + k : ℕ) : ℝ) + 1) B]
      have hcast : ((n + k : ℕ) : ℝ) = (n : ℝ) + k := by push_cast; ring
      rw [hcast] at hfinal hcm
      linarith
    have hgeosum : Summable fun k : ℕ => C * Real.exp (-δ' * ((n : ℝ) + k)) := by
      have hbase : Summable fun k : ℕ => (Real.exp (-δ')) ^ k :=
        summable_geometric_of_lt_one (Real.exp_pos _).le hgeo
      have hmul := (hbase.mul_left (C * Real.exp (-δ' * n)))
      refine hmul.congr fun k => ?_
      rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 2
      ring
    have hshift : Summable fun k : ℕ => c (n + k) := by
      have h := (summable_nat_add_iff n).mpr hcsummable
      exact h.congr fun k => by rw [Nat.add_comm]
    have hle := Summable.tsum_le_tsum hterm hshift hgeosum
    refine le_trans hle (le_of_eq ?_)
    have hval : ∀ k : ℕ, C * Real.exp (-δ' * ((n : ℝ) + k))
        = (C * Real.exp (-δ' * n)) * (Real.exp (-δ')) ^ k := by
      intro k
      rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 2
      ring
    rw [tsum_congr hval, tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hgeo, hKdef]
    field_simp
  -- assemble
  refine ⟨A * K + C, ?_⟩
  filter_upwards [hrec, eventually_ge_atTop (max n₁ (max n₂ 1))] with n hr hn
  have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right n₁ _)) hn
  have hnR : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have hQbound : Q n ≤ K * Real.exp (-δ' * n) := by
    have h1 := hTail n hn1
    have h2 := hbound n hn
    have hpow : (1:ℝ) ≤ (n : ℝ) ^ B := one_le_pow₀ hnR
    nlinarith [hQ0 n, h1, h2]
  have hexpmono : Real.exp (-δ * n) ≤ Real.exp (-δ' * n) := by
    apply Real.exp_le_exp.mpr
    have : (0:ℝ) ≤ (n:ℝ) := by positivity
    nlinarith
  nlinarith [hr, hQbound, hexpmono, Real.exp_pos (-δ' * (n:ℝ)), hA]

/-! ## The tail of a superpolynomially flat sequence -/

/-- Superpolynomial flatness: every polynomial rate is eventually beaten. -/
def SuperpolynomiallyFlat (q : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, ∃ M : ℝ, ∀ n : ℕ, 1 ≤ n → q n ≤ M / (n : ℝ) ^ N

/-- The weighted term of the backward tail. -/
noncomputable def volterraTerm (q : ℕ → ℝ) (k : ℕ) : ℝ := q k / (k : ℝ)

/-- The weighted backward tail of a sequence. -/
noncomputable def volterraTail (q : ℕ → ℝ) (n : ℕ) : ℝ := ∑' m : ℕ, volterraTerm q (n + m)

theorem summable_inv_succ_sq_flatVolterraDecay : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ (2 : ℕ) := by
  have h : Summable fun m : ℕ => 1 / ((m : ℝ)) ^ (2 : ℕ) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr h
  refine hshift.congr fun m => ?_
  push_cast
  ring

theorem volterraTerm_nonneg {q : ℕ → ℝ} (hq0 : ∀ n, 0 ≤ q n) (k : ℕ) :
    0 ≤ volterraTerm q k :=
  div_nonneg (hq0 k) (by positivity)

theorem flat_nonneg {q : ℕ → ℝ} (hq0 : ∀ n, 0 ≤ q n) {M : ℝ} {N : ℕ}
    (hM : ∀ n : ℕ, 1 ≤ n → q n ≤ M / (n : ℝ) ^ N) : 0 ≤ M := by
  have h := hM 1 le_rfl
  have hq := hq0 1
  simp only [Nat.cast_one, one_pow, div_one] at h
  linarith

/-- The weighted sequence is summable. -/
theorem summable_volterraTerm {q : ℕ → ℝ} (hq0 : ∀ n, 0 ≤ q n)
    (hflat : SuperpolynomiallyFlat q) : Summable (volterraTerm q) := by
  obtain ⟨M, hM⟩ := hflat 1
  have hM0 : 0 ≤ M := flat_nonneg hq0 hM
  refine Summable.of_nonneg_of_le (fun k => volterraTerm_nonneg hq0 k) (fun k => ?_)
    (summable_inv_succ_sq_flatVolterraDecay.mul_left (4 * M))
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [volterraTerm]
    simp only [Nat.cast_zero, div_zero]
    positivity
  · have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hq := hM k hk
    have hstep : volterraTerm q k ≤ M / (k : ℝ) / (k : ℝ) := by
      rw [volterraTerm]
      gcongr
      simpa using hq
    refine le_trans hstep ?_
    rw [div_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hM0, sq_nonneg ((k:ℝ) - 1), hk1]

/-- A superpolynomially flat nonnegative sequence is summable. -/
theorem summable_of_flat {q : ℕ → ℝ} (hq0 : ∀ n, 0 ≤ q n)
    (hflat : SuperpolynomiallyFlat q) : Summable q := by
  obtain ⟨M, hM⟩ := hflat 2
  have hM0 : 0 ≤ M := flat_nonneg hq0 hM
  have hshift : Summable fun k : ℕ => q (k + 1) := by
    refine Summable.of_nonneg_of_le (fun k => hq0 _) (fun k => ?_)
      (summable_inv_succ_sq_flatVolterraDecay.mul_left (4 * M))
    have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hq := hM (k + 1) hk
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hq
    have hpos : (0:ℝ) < (k : ℝ) + 1 := by positivity
    rw [mul_one_div]
    refine le_trans hq ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hM0, sq_nonneg ((k:ℝ) + 1)]
  exact (summable_nat_add_iff 1).mp hshift

theorem summable_shifted_of_flat {q : ℕ → ℝ} (hq0 : ∀ n, 0 ≤ q n)
    (hflat : SuperpolynomiallyFlat q) (n : ℕ) : Summable fun k : ℕ => q (n + k) := by
  have h := (summable_nat_add_iff n).mpr (summable_of_flat hq0 hflat)
  exact h.congr fun k => by rw [Nat.add_comm]

theorem summable_shifted_volterraTerm {q : ℕ → ℝ} (hq0 : ∀ n, 0 ≤ q n)
    (hflat : SuperpolynomiallyFlat q) (n : ℕ) :
    Summable fun m : ℕ => volterraTerm q (n + m) := by
  have h := (summable_nat_add_iff n).mpr (summable_volterraTerm hq0 hflat)
  exact h.congr fun m => by rw [Nat.add_comm]

theorem volterraTail_nonneg {q : ℕ → ℝ} (hq0 : ∀ n, 0 ≤ q n) (n : ℕ) :
    0 ≤ volterraTail q n :=
  tsum_nonneg fun m => volterraTerm_nonneg hq0 (n + m)

/-- The tail obeys the backward recursion. -/
theorem volterraTail_step {q : ℕ → ℝ} (hq0 : ∀ n, 0 ≤ q n)
    (hflat : SuperpolynomiallyFlat q) (n : ℕ) :
    volterraTail q (n + 1) = volterraTail q n - q n / n := by
  have hsum := summable_shifted_volterraTerm hq0 hflat n
  have hsplit : volterraTail q n
      = volterraTerm q n + ∑' m : ℕ, volterraTerm q (n + (m + 1)) := by
    rw [volterraTail, hsum.tsum_eq_zero_add, Nat.add_zero]
  have hreindex : (∑' m : ℕ, volterraTerm q (n + (m + 1))) = volterraTail q (n + 1) := by
    rw [volterraTail]
    refine tsum_congr fun m => ?_
    congr 1
    omega
  rw [hsplit, hreindex, volterraTerm]
  ring

/-- The tail inherits superpolynomial flatness. -/
theorem volterraTail_flat {q : ℕ → ℝ} (hq0 : ∀ n, 0 ≤ q n)
    (hflat : SuperpolynomiallyFlat q) (N : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ N * volterraTail q n) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hflat (N + 4)
  have hM0 : 0 ≤ M := flat_nonneg hq0 hM
  set S : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ (2 : ℕ) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun m => by positivity
  have hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ N * volterraTail q n ≤ (M * S) / (n : ℝ) := by
    intro n hn
    have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsum := summable_shifted_volterraTerm hq0 hflat n
    have hterm : ∀ m : ℕ, volterraTerm q (n + m)
        ≤ (M / (n : ℝ) ^ (N + 1)) * (1 / ((m : ℝ) + 1) ^ (2 : ℕ)) := by
      intro m
      have hpos : 1 ≤ n + m := le_trans hn (Nat.le_add_right n m)
      have hcast : (1:ℝ) ≤ ((n + m : ℕ) : ℝ) := by exact_mod_cast hpos
      have hnm : ((n + m : ℕ) : ℝ) = (n : ℝ) + (m : ℝ) := by push_cast; ring
      have hq := hM (n + m) hpos
      rw [hnm] at hq hcast
      have hstep : volterraTerm q (n + m)
          ≤ (M / ((n : ℝ) + m) ^ (N + 4)) / ((n : ℝ) + m) := by
        rw [volterraTerm, hnm]
        gcongr
      refine le_trans hstep ?_
      rw [div_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hbig : (n : ℝ) ^ (N + 1) * ((m : ℝ) + 1) ^ (2 : ℕ)
          ≤ ((n : ℝ) + m) ^ (N + 4) * ((n : ℝ) + m) := by
        have h1 : (n : ℝ) ^ (N + 1) ≤ ((n : ℝ) + m) ^ (N + 1) := by
          apply pow_le_pow_left₀ (by positivity)
          have : (0:ℝ) ≤ (m:ℝ) := by positivity
          linarith
        have h2 : ((m : ℝ) + 1) ^ (2 : ℕ) ≤ ((n : ℝ) + m) ^ (2 : ℕ) := by
          apply pow_le_pow_left₀ (by positivity)
          linarith
        have h3 : ((n : ℝ) + m) ^ (N + 3) ≤ ((n : ℝ) + m) ^ (N + 5) :=
          pow_le_pow_right₀ hcast (by omega)
        calc (n : ℝ) ^ (N + 1) * ((m : ℝ) + 1) ^ (2 : ℕ)
            ≤ ((n : ℝ) + m) ^ (N + 1) * ((n : ℝ) + m) ^ (2 : ℕ) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = ((n : ℝ) + m) ^ (N + 3) := by ring
          _ ≤ ((n : ℝ) + m) ^ (N + 5) := h3
          _ = ((n : ℝ) + m) ^ (N + 4) * ((n : ℝ) + m) := by ring
      calc M * ((m : ℝ) + 1) ^ (2 : ℕ)
          = M / (n : ℝ) ^ (N + 1) * ((n : ℝ) ^ (N + 1) * ((m : ℝ) + 1) ^ (2 : ℕ)) := by
            field_simp
        _ ≤ M / (n : ℝ) ^ (N + 1) * (((n : ℝ) + m) ^ (N + 4) * ((n : ℝ) + m)) :=
            mul_le_mul_of_nonneg_left hbig (by positivity)
    have hmajor : Summable fun m : ℕ => (M / (n : ℝ) ^ (N + 1)) * (1 / ((m : ℝ) + 1) ^ (2 : ℕ)) :=
      summable_inv_succ_sq_flatVolterraDecay.mul_left _
    have htsum := Summable.tsum_le_tsum hterm hsum hmajor
    rw [tsum_mul_left, ← hSdef, ← volterraTail] at htsum
    have hfinal : (n : ℝ) ^ N * volterraTail q n
        ≤ (n : ℝ) ^ N * (M / (n : ℝ) ^ (N + 1) * S) :=
      mul_le_mul_of_nonneg_left htsum (by positivity)
    refine le_trans hfinal (le_of_eq ?_)
    rw [pow_succ]
    field_simp
  have hzero : Tendsto (fun n : ℕ => (M * S) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (M * S)
  have hnn : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℝ) ^ N * volterraTail q n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_nonneg (by positivity) (volterraTail_nonneg hq0 n)
  have hle : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ N * volterraTail q n ≤ (M * S) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hbound n hn
  exact squeeze_zero' hnn hle hzero

/-- **The card's flat Volterra lemma.**  A superpolynomially flat nonnegative sequence dominated by
its own weighted backward tail plus an exponential source is exponentially small at every rate
below the source rate. -/
theorem flat_volterra_decay_of_tail {q : ℕ → ℝ} {A C δ δ' : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hδ' : 0 < δ') (hlt : δ' < δ)
    (hq0 : ∀ n, 0 ≤ q n) (hflat : SuperpolynomiallyFlat q)
    (hrec : ∀ᶠ n : ℕ in atTop,
      q n ≤ A * volterraTail q n + C * Real.exp (-δ * n)) :
    ∃ C' : ℝ, ∀ᶠ n : ℕ in atTop, q n ≤ C' * Real.exp (-δ' * n) :=
  flat_volterra_decay hA hC hδ' hlt (volterraTail_nonneg hq0)
    (Filter.Eventually.of_forall fun n => volterraTail_step hq0 hflat n) hrec
    (volterraTail_flat hq0 hflat)

end GaloisForLFunctions.HTGeometry
