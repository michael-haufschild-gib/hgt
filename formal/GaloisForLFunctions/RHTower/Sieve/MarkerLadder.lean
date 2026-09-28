import GaloisForLFunctions.RHTower.Sieve.FreeScaleBudget

/-!
# Marker ladders with a growing number of super-blocks

A start ladder `m, m/2, m/4, …` cuts the marker primes into dyadic blocks: block `k` holds the
primes whose reciprocal start `X/p` lies in `[m/2^{k+1}, m/2^k)`.  Grouping `g` consecutive blocks
into a super-block and discarding, *inside each super-block separately*, the markers over that
super-block's exceptional starts, the good markers of all super-blocks together produce the sign
count of the window `(X, X+H]` through `Sieve/MarkerSignWindowCount.card_sign_window_ge'`.

Each block carries its own window, so the construction applies to an arbitrary short-interval
length; and the number of super-blocks is arbitrary, so the harmonic mass of the markers may grow
with the physical scale.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- **The cell bound at one good marker, for an arbitrary block window.** -/
theorem ladder_cell_bound {X m K₀ k p H : ℕ} {σ : ℤ} {rho w : ℝ}
    (hdvd : 2 ^ (K₀ + 1) ∣ m) (hk : k ≤ K₀) (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < freeStart m (K₀ + 1)) (hmk2 : 2 ≤ freeStart m k)
    (hp : p ∈ freeBlock X m k) (hw : 0 < w)
    (hfit : (w + 1) * (p : ℝ) ≤ (H : ℝ))
    (hsup : rho * ((H : ℝ) / (p : ℝ) - 1) ≤ (3 / 16) * squarefreeDensity * (w / 2 - 1))
    (hnot : X / p ∉ badStart (freeScale m k) w) :
    rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ ((((windowCell X H p).filter (fun b => moebius b = -σ)).card : ℕ) : ℝ) := by
  classical
  have hp0 : 0 < p := (prime_of_mem_bigPrimeSet hp).pos
  have hk1 : 0 < freeStart m (k + 1) := lt_of_lt_of_le hpos (freeStart_anti m (by omega))
  obtain ⟨hlowN, hhighN⟩ := start_mem_freeBlock hk1 hp
  have ht1 : 1 ≤ X / p := by omega
  obtain ⟨htlow, hthigh⟩ := freeBlock_start_bounds hdvd hk hpos hp
  have hmk2R : (2 : ℝ) ≤ ((freeStart m k : ℕ) : ℝ) := by exact_mod_cast hmk2
  have hmk0 : (0 : ℝ) < ((freeStart m k : ℕ) : ℝ) := by linarith
  have hy4 : (4 : ℝ) ≤ freeScale m k := by
    rw [freeScale]
    nlinarith [hmk2R]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hfit' : (w * (((X / p : ℕ) : ℝ) + 1) / ((freeStart m k : ℕ) : ℝ) + 1)
      * (p : ℝ) ≤ (H : ℝ) := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hpR.le) hfit
    have hquot : w * (((X / p : ℕ) : ℝ) + 1) / ((freeStart m k : ℕ) : ℝ) ≤ w := by
      rw [div_le_iff₀ hmk0]
      exact mul_le_mul_of_nonneg_left hthigh hw.le
    linarith
  have hsup' : rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity
          * (w * ((X / p : ℕ) : ℝ) / ((freeStart m k : ℕ) : ℝ) - 1) := by
    refine le_trans hsup (mul_le_mul_of_nonneg_left ?_ (by
      have := squarefreeDensity_pos
      positivity))
    have hfib : w / 2 ≤ w * ((X / p : ℕ) : ℝ) / ((freeStart m k : ℕ) : ℝ) := by
      rw [le_div_iff₀ hmk0, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [htlow, hw, hmk0]
    linarith
  exact cell_bound_of_good_start hy4 hw (sqrt_freeScale m k) hp0 hσ ht1 htlow hthigh hnot
    hfit' hsup'

/-! ## Decoded targets -/

/-- `n` is a product `a·p` of a prime `p > M₀` and a cofactor `a` of Möbius sign `-σ`. -/
def MarkerDecoded (M₀ : ℕ) (σ : ℤ) (n : ℕ) : Prop :=
  ∃ a p : ℕ, p.Prime ∧ M₀ < p ∧ a * p = n ∧ moebius a = -σ

open Classical in
/-- **The window receives the marker family's sign count, as decoded targets.**  The integers
counted have Möbius sign `σ` and are products `a·p` of a marker prime `p > M₀` and a cofactor of
sign `-σ`. -/
theorem card_sign_window_decoded_ge {X H M₀ : ℕ} {σ : ℤ} {rho S B : ℝ}
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, M₀ < p)
    (hXH : X + H ≤ M₀ * M₀) (hrho : 0 ≤ rho)
    (hcell : ∀ p ∈ P, rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ ((((windowCell X H p).filter (fun b => moebius b = -σ)).card : ℕ) : ℝ))
    (hS : S ≤ ∑ p ∈ P, 1 / (p : ℝ)) (hB : ((P.card : ℕ) : ℝ) ≤ B) :
    rho * ((H : ℝ) * S - B)
      ≤ ((((Finset.Ioc X (X + H)).filter
          (fun n => moebius n = σ ∧ MarkerDecoded M₀ σ n)).card : ℕ) : ℝ) := by
  classical
  set C : ℕ → Finset ℕ :=
    fun p => (windowCell X H p).filter (fun b => moebius b = -σ) with hC
  have hposW : ∀ p ∈ P, ∀ a ∈ windowCell X H p, 0 < a := fun p hp a ha =>
    pos_of_mem_windowCell (hprime p hp).pos ha
  have hposC : ∀ p ∈ P, ∀ a ∈ C p, 0 < a := by
    intro p hp a ha
    exact hposW p hp a (Finset.mem_filter.1 ha).1
  have hsmallW := cofactor_lt_marker' hprime hlarge hXH
  have hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r := by
    intro p hp a ha r hr
    exact hsmallW p hp a (Finset.mem_filter.1 ha).1 r hr
  have hexact : ((RHTower.markerBlockTargets P C).card : ℕ) = ∑ p ∈ P, (C p).card :=
    RHTower.card_markerBlockTargets P C hprime hposC hsmall
  have hsub : RHTower.markerBlockTargets P C
      ⊆ (Finset.Ioc X (X + H)).filter (fun n => moebius n = σ ∧ MarkerDecoded M₀ σ n) := by
    intro n hn
    obtain ⟨p, hp, a, ha, rfl, hsign⟩ :=
      moebius_of_mem_markerBlockTargets hprime hposC hsmall hn
    have haW : a ∈ windowCell X H p := (Finset.mem_filter.1 ha).1
    have hasign : moebius a = -σ := (Finset.mem_filter.1 ha).2
    have hw := (mem_windowCell_iff (hprime p hp).pos).1 haW
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨hw.1, hw.2⟩, ?_, a, p, hprime p hp, hlarge p hp, rfl, hasign⟩
    rw [hsign, hasign]
    ring
  have hsum : rho * ((H : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) - ((P.card : ℕ) : ℝ))
      ≤ ∑ p ∈ P, (((C p).card : ℕ) : ℝ) := by
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hcell)
    rw [Finset.mul_sum, mul_sub, Finset.mul_sum]
    rw [show ∑ p ∈ P, rho * ((H : ℝ) / (p : ℝ) - 1)
        = ∑ p ∈ P, (rho * ((H : ℝ) * (1 / (p : ℝ))) - rho * 1) from
      Finset.sum_congr rfl fun p _ => by rw [mul_one_div]; ring]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hmono : rho * ((H : ℝ) * S - B)
      ≤ rho * ((H : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) - ((P.card : ℕ) : ℝ)) := by
    have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
    have h1 : (H : ℝ) * S ≤ (H : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hS hH
    exact mul_le_mul_of_nonneg_left (by linarith) hrho
  have hcast : ((∑ p ∈ P, (C p).card : ℕ) : ℝ) = ∑ p ∈ P, (((C p).card : ℕ) : ℝ) := by
    push_cast
    ring
  have hcard : (((RHTower.markerBlockTargets P C).card : ℕ) : ℝ)
      ≤ ((((Finset.Ioc X (X + H)).filter
          (fun n => moebius n = σ ∧ MarkerDecoded M₀ σ n)).card : ℕ) : ℝ) :=
    Nat.cast_le.2 (Finset.card_le_card hsub)
  have hchain : rho * ((H : ℝ) * S - B)
      ≤ (((RHTower.markerBlockTargets P C).card : ℕ) : ℝ) := by
    rw [hexact, hcast]
    linarith [hmono, hsum]
  linarith [hchain, hcard]

/-! ## The ladder -/

/-- The marker range of the blocks `a ≤ k < b` of a start ladder. -/
def ladderRange (X m a b : ℕ) : Finset ℕ :=
  bigPrimeSet (X / freeStart m a) (X / freeStart m b)

open Classical in
/-- The exceptional starts of the blocks `a ≤ k < b`, each block with its own window. -/
def ladderBad (win : ℕ → ℝ) (m a b : ℕ) : Finset ℕ :=
  (Finset.Ico a b).biUnion (fun k => badStart (freeScale m k) (win k))

open Classical in
/-- The markers of the blocks `a ≤ k < b` whose start is not exceptional for those blocks. -/
def ladderGood (win : ℕ → ℝ) (X m a b : ℕ) : Finset ℕ :=
  (ladderRange X m a b).filter (fun p => X / p ∉ ladderBad win m a b)

open Classical in
/-- The good markers of `I` consecutive super-blocks of `g` blocks each. -/
def ladderMarkers (win : ℕ → ℝ) (X m g I : ℕ) : Finset ℕ :=
  (Finset.range I).biUnion (fun i => ladderGood win X m (i * g) ((i + 1) * g))

/-- **Every prime of a ladder range lies in one of its blocks.** -/
theorem exists_freeBlock_of_mem_ladderRange {X m a b p : ℕ} (hab : a ≤ b)
    (hb : 0 < freeStart m b) (hp : p ∈ ladderRange X m a b) :
    ∃ k, a ≤ k ∧ k < b ∧ p ∈ freeBlock X m k := by
  induction b with
  | zero =>
      exfalso
      have ha : a = 0 := by omega
      subst ha
      rw [ladderRange, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
      omega
  | succ b ih =>
      have hb' : 0 < freeStart m b := lt_of_lt_of_le hb (freeStart_anti m (by omega))
      rcases Nat.eq_or_lt_of_le hab with hEq | hlt
      · exfalso
        subst hEq
        rw [ladderRange, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
        omega
      rw [ladderRange, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨hlow, hhigh⟩, hpp⟩ := hp
      by_cases hle : p ≤ X / freeStart m b
      · obtain ⟨k, hak, hkb, hk⟩ := ih (by omega) hb' (by
          rw [ladderRange, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hlow, hle⟩, hpp⟩)
        exact ⟨k, hak, by omega, hk⟩
      · refine ⟨b, by omega, by omega, ?_⟩
        rw [freeBlock, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, hhigh⟩, hpp⟩

/-- Ladder ranges of disjoint block intervals `[a, b)`, `[c, d)` with `b ≤ c` are disjoint. -/
theorem disjoint_ladderRange {X m a b c d : ℕ} (hbc : b ≤ c) (hc : 0 < freeStart m c) :
    Disjoint (ladderRange X m a b) (ladderRange X m c d) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [ladderRange, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp hq
  have hmono : X / freeStart m b ≤ X / freeStart m c :=
    Nat.div_le_div_left (freeStart_anti m hbc) hc
  omega

/-- **The harmonic mass of the ladder markers is the sum over the super-blocks.** -/
theorem sum_inv_ladderMarkers {win : ℕ → ℝ} {X m g I : ℕ} (hpos : 0 < freeStart m (I * g)) :
    ∑ p ∈ ladderMarkers win X m g I, (1 : ℝ) / (p : ℝ)
      = ∑ i ∈ Finset.range I,
          ∑ p ∈ ladderGood win X m (i * g) ((i + 1) * g), (1 : ℝ) / (p : ℝ) := by
  classical
  rw [ladderMarkers]
  refine Finset.sum_biUnion ?_
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : (i + 1) * g ≤ j * g := Nat.mul_le_mul_right g (by omega)
    have hjpos : 0 < freeStart m (j * g) :=
      lt_of_lt_of_le hpos (freeStart_anti m (Nat.mul_le_mul_right g (by omega)))
    exact (disjoint_ladderRange hle hjpos).mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
  · have hle : (j + 1) * g ≤ i * g := Nat.mul_le_mul_right g (by omega)
    have hipos : 0 < freeStart m (i * g) :=
      lt_of_lt_of_le hpos (freeStart_anti m (Nat.mul_le_mul_right g (by omega)))
    exact ((disjoint_ladderRange hle hipos).mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)).symm

open Classical in
/-- **The sign count of the window from a ladder of super-blocks.** -/
theorem ladder_card_sign_window_ge {win : ℕ → ℝ} {X m g I H : ℕ} {σ : ℤ} {rho B : ℝ}
    {c : ℕ → ℝ} (hIg : 0 < I * g) (hdvd : 2 ^ (I * g) ∣ m) (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < freeStart m (I * g))
    (hXH : X + H ≤ (X / freeStart m 0) * (X / freeStart m 0)) (hrho : 0 ≤ rho)
    (hmk2 : ∀ k, k < I * g → 2 ≤ freeStart m k)
    (hw : ∀ k, k < I * g → 0 < win k)
    (hfit : ∀ k, k < I * g → ∀ p ∈ freeBlock X m k, (win k + 1) * (p : ℝ) ≤ (H : ℝ))
    (hsup : ∀ k, k < I * g → ∀ p ∈ freeBlock X m k,
      rho * ((H : ℝ) / (p : ℝ) - 1) ≤ (3 / 16) * squarefreeDensity * (win k / 2 - 1))
    (hmass : ∀ i, i < I →
      c i ≤ ∑ p ∈ ladderGood win X m (i * g) ((i + 1) * g), (1 : ℝ) / (p : ℝ))
    (hB : (((ladderMarkers win X m g I).card : ℕ) : ℝ) ≤ B) :
    rho * ((H : ℝ) * ∑ i ∈ Finset.range I, c i - B)
      ≤ ((((Finset.Ioc X (X + H)).filter
          (fun n => moebius n = σ ∧ MarkerDecoded (X / freeStart m 0) σ n)).card : ℕ) : ℝ) := by
  classical
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, I * g = K₀ + 1 := ⟨I * g - 1, by omega⟩
  have hdvd' : 2 ^ (K₀ + 1) ∣ m := hK₀ ▸ hdvd
  have hpos' : 0 < freeStart m (K₀ + 1) := hK₀ ▸ hpos
  have hmem : ∀ p ∈ ladderMarkers win X m g I, ∃ i, i < I ∧ ∃ k, i * g ≤ k ∧ k < (i + 1) * g
      ∧ p ∈ freeBlock X m k ∧ X / p ∉ badStart (freeScale m k) (win k) := by
    intro p hp
    rw [ladderMarkers, Finset.mem_biUnion] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    rw [Finset.mem_range] at hi
    rw [ladderGood, Finset.mem_filter] at hpi
    obtain ⟨hpr, hnot⟩ := hpi
    have hposi : 0 < freeStart m ((i + 1) * g) :=
      lt_of_lt_of_le hpos (freeStart_anti m (Nat.mul_le_mul_right g (by omega)))
    obtain ⟨k, hik, hki, hk⟩ :=
      exists_freeBlock_of_mem_ladderRange (Nat.mul_le_mul_right g (by omega)) hposi hpr
    refine ⟨i, hi, k, hik, hki, hk, fun hc => hnot ?_⟩
    rw [ladderBad, Finset.mem_biUnion]
    exact ⟨k, Finset.mem_Ico.2 ⟨hik, hki⟩, hc⟩
  refine card_sign_window_decoded_ge (M₀ := X / freeStart m 0) (ladderMarkers win X m g I) ?_ ?_ hXH
    hrho ?_ ?_ hB
  · intro p hp
    obtain ⟨i, -, k, -, -, hk, -⟩ := hmem p hp
    exact prime_of_mem_bigPrimeSet hk
  · intro p hp
    obtain ⟨i, hi, k, -, hki, hk, -⟩ := hmem p hp
    have hk1 : 0 < freeStart m (k + 1) :=
      lt_of_lt_of_le hpos (freeStart_anti m (by
        have : (i + 1) * g ≤ I * g := Nat.mul_le_mul_right g (by omega)
        omega))
    have hk0 : 0 < freeStart m k := lt_of_lt_of_le hk1 (freeStart_anti m (by omega))
    have hmono : X / freeStart m 0 ≤ X / freeStart m k :=
      Nat.div_le_div_left (freeStart_anti m (Nat.zero_le k)) hk0
    exact lt_of_le_of_lt hmono (lt_of_mem_bigPrimeSet hk)
  · intro p hp
    obtain ⟨i, hi, k, -, hki, hk, hnot⟩ := hmem p hp
    have hkI : k < I * g := by
      have : (i + 1) * g ≤ I * g := Nat.mul_le_mul_right g (by omega)
      omega
    exact ladder_cell_bound hdvd' (by omega) hσ hpos' (hmk2 k hkI) hk (hw k hkI)
      (hfit k hkI p hk) (hsup k hkI p hk) hnot
  · rw [sum_inv_ladderMarkers hpos]
    exact Finset.sum_le_sum fun i hi => hmass i (Finset.mem_range.1 hi)

/-! ## The harmonic mass of one super-block -/

/-- **The good markers of one super-block keep half its harmonic mass.**  The super-block spans the
markers `(X/(2^{K₀+1}u), X/u]`; `S` is any set of exceptional starts of density `ε` against the top
start `2^{K₀+1}u`.  `T₁`, `T₂`, `T₃` are the three numerical conditions of the device: the marker
count, the shifted-pair budget, and the sieve remainder, each against the squared harmonic mass. -/
theorem good_mass_ge_of_budget {K₀ X u M Mt K : ℕ} {S : Finset ℕ} {ε : ℝ}
    (hMdef : M = X / (2 ^ (K₀ + 1) * u)) (hMt : Mt = X / u) (hKdef : K = X / (u * u))
    (hu : 0 < u) (hε : 0 ≤ ε) (hharm : 0 < multiHarmConst K₀) (hM2 : 2 ≤ M)
    (hlogM : markerLogBound K₀ ≤ Real.log (M : ℝ))
    (hbt : Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5
      ≤ 32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4))
    (hEbad : ((S.card : ℕ) : ℝ) ≤ ε * ((2 ^ (K₀ + 1) * u : ℕ) : ℝ))
    (hT1 : 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (u : ℝ) * Real.log (M : ℝ)
      ≤ (M : ℝ) * (multiHarmConst K₀ / 2) ^ 2)
    (hT2 : 6 * ε * pairMainConst * (2 : ℝ) ^ (3 * K₀ + 6) ≤ (multiHarmConst K₀ / 2) ^ 2)
    (hT3 : 12 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (Real.log (M : ℝ)) ^ 2
      ≤ (multiHarmConst K₀ / 2) ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4)) :
    multiHarmConst K₀ / (2 * Real.log (M : ℝ))
      ≤ ∑ p ∈ (bigPrimeSet M Mt).filter (fun p => X / p ∉ S), (1 : ℝ) / (p : ℝ) := by
  classical
  set m : ℕ := 2 ^ (K₀ + 1) * u with hm
  have hM1 : 1 ≤ M := by omega
  -- the two-sided span of the super-block
  have hlo : 2 ^ (K₀ + 1) * M ≤ Mt := by
    rw [hMdef, hMt, hm, mul_comm (2 ^ (K₀ + 1)) u, ← Nat.div_div_eq_div_mul, mul_comm]
    exact Nat.div_mul_le_self _ _
  have hhi : Mt ≤ 2 ^ (K₀ + 2) * M := by
    rw [hMt, hMdef]
    exact freeRange_top_le hu (by rw [← hMdef]; exact hM1)
  have hMMt : M ≤ Mt := le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hlo
  -- the logarithm of the base
  set L : ℝ := Real.log (M : ℝ) with hL
  have hbase := markerLogBase_le_bound K₀
  have hbasepos := markerLogBase_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hc1 := mertensFirstConst_nonneg
  have hbaseL : markerLogBase ≤ L := le_trans hbase hlogM
  have hL1 : 1 ≤ L := by rw [markerLogBase] at hbaseL; linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hMR0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hMtR : (Mt : ℝ) ≤ 2 ^ (K₀ + 2) * (M : ℝ) := by exact_mod_cast hhi
  have hMtR0 : (0 : ℝ) ≤ (Mt : ℝ) := Nat.cast_nonneg _
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have huR0 : (0 : ℝ) < (u : ℝ) := by linarith
  set D : ℝ := (2 : ℝ) ^ (K₀ + 2) with hD
  have hD0 : (0 : ℝ) < D := by rw [hD]; positivity
  -- the number of markers
  have hN : (((bigPrimeSet M Mt).card : ℕ) : ℝ) ≤ 64 * D * (M : ℝ) / L := by
    have hbig16 : 16 * Real.log 2 ≤ L := by rw [markerLogBase] at hbaseL; linarith
    exact count_le_generic hM2 hMMt hhi hbig16 hbt
  -- markers sharing a start are close
  have hsep : ∀ p ∈ bigPrimeSet M Mt, ∀ q ∈ bigPrimeSet M Mt, p < q → X / q = X / p →
      q ≤ p + K := by
    intro p hp q _ hpq heq
    have hp0 : 0 < p := (prime_of_mem_bigPrimeSet hp).pos
    have hpMt : p ≤ Mt := (Finset.mem_Icc.1 (Finset.mem_filter.1 hp).1).2
    have hAt : u ≤ X / p := by
      rw [Nat.le_div_iff_mul_le hp0]
      have := (Nat.le_div_iff_mul_le hu).1 (hMt ▸ hpMt)
      linarith [this]
    have := reciprocal_separation hu hp0 hpq hAt heq
    rw [hKdef]
    exact this
  -- the shifted-pair budget
  have hKle : (K : ℝ) ≤ D * (M : ℝ) / (u : ℝ) := by
    have hsplit : K = X / u / u := by rw [hKdef, Nat.div_div_eq_div_mul]
    have hstep : ((X / u / u : ℕ) : ℝ) ≤ ((X / u : ℕ) : ℝ) / (u : ℝ) := Nat.cast_div_le
    rw [hsplit]
    refine hstep.trans ?_
    rw [div_le_div_iff₀ huR0 huR0, ← hMt]
    nlinarith [hMtR, huR0]
  have hpair : ∑ d ∈ Finset.Icc 1 K,
      ((((bigPrimeSet M Mt).filter (fun p => p + d ∈ bigPrimeSet M Mt)).card : ℕ) : ℝ)
      ≤ pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)
        + 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ) := by
    refine (generic_pair_le' hM2 hbaseL).trans ?_
    have h34 : (0 : ℝ) ≤ (M : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hMR0.le _
    have hpc := pairMainConst_pos
    have hone : pairMainConst * (K : ℝ) * (Mt : ℝ) / L ^ 2
        ≤ pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : pairMainConst * (K : ℝ) * (Mt : ℝ)
          ≤ pairMainConst * (D * (M : ℝ) / (u : ℝ)) * (D * (M : ℝ)) := by
        have ha : pairMainConst * (K : ℝ) ≤ pairMainConst * (D * (M : ℝ) / (u : ℝ)) :=
          mul_le_mul_of_nonneg_left hKle hpc.le
        have hb : (0 : ℝ) ≤ pairMainConst * (D * (M : ℝ) / (u : ℝ)) := by positivity
        exact mul_le_mul ha hMtR hMtR0 hb
      have hval : pairMainConst * (D * (M : ℝ) / (u : ℝ)) * (D * (M : ℝ)) * ((u : ℝ) * L ^ 2)
          = pairMainConst * D ^ 2 * (M : ℝ) ^ 2 * L ^ 2 := by
        field_simp
      have hmul := mul_le_mul_of_nonneg_right h1 (mul_nonneg huR0.le (sq_nonneg L))
      rw [hval] at hmul
      exact hmul
    have htwo : (K : ℝ) * (2 * (M : ℝ) ^ ((3 : ℝ) / 4))
        ≤ 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ) := by
      have hstep : (K : ℝ) * (2 * (M : ℝ) ^ ((3 : ℝ) / 4))
          ≤ (D * (M : ℝ) / (u : ℝ)) * (2 * (M : ℝ) ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right hKle (by positivity)
      refine hstep.trans (le_of_eq ?_)
      field_simp
    linarith [hone, htwo]
  -- the device threshold
  set A : ℝ := multiHarmConst K₀ / 2 with hA
  have hA0 : (0 : ℝ) < A := by rw [hA]; linarith
  set b : ℝ := (M : ℝ) * A / L with hb
  have hb0 : (0 : ℝ) ≤ b := by
    rw [hb]; exact div_nonneg (mul_nonneg hMR0.le hA0.le) hL0.le
  have hmD : ((m : ℕ) : ℝ) = D / 2 * (u : ℝ) := by
    rw [hm, hD]; push_cast; rw [pow_succ]; ring
  have hLsq : (0 : ℝ) < L ^ 2 := pow_pos hL0 2
  have h3L2 : (0 : ℝ) < 3 * L ^ 2 := by linarith
  have hthr : (ε * ((m : ℕ) : ℝ))
      * (64 * D * (M : ℝ) / L
        + 2 * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)
          + 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ))) ≤ b ^ 2 := by
    have hDsq : D ^ 2 = (2 : ℝ) ^ (2 * K₀ + 4) := by
      rw [hD, ← pow_mul]; congr 1; ring
    have hDcube : D ^ 3 = (2 : ℝ) ^ (3 * K₀ + 6) := by
      rw [hD, ← pow_mul]; congr 1; ring
    have h34 : (0 : ℝ) < (M : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hMR0 _
    have hprod : (M : ℝ) ^ ((3 : ℝ) / 4) * (M : ℝ) ^ ((1 : ℝ) / 4) = (M : ℝ) := by
      rw [← Real.rpow_add hMR0]; norm_num
    have hkey1 : 192 * ε * D ^ 2 * (u : ℝ) * L ≤ (M : ℝ) * A ^ 2 := by rw [hDsq, hA]; exact hT1
    have hkey2 : 6 * ε * pairMainConst * D ^ 3 ≤ A ^ 2 := by rw [hDcube, hA]; exact hT2
    have hkey3 : 12 * ε * D ^ 2 * L ^ 2 ≤ A ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [hDsq, hA]; exact hT3
    have hpiece1 : ε * ((m : ℕ) : ℝ) * (64 * D * (M : ℝ) / L)
        ≤ (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2) := by
      rw [hmD, le_div_iff₀ h3L2]
      have hexp : ε * (D / 2 * (u : ℝ)) * (64 * D * (M : ℝ) / L) * (3 * L ^ 2)
          = 96 * (ε * D ^ 2 * (u : ℝ) * L * (M : ℝ)) := by
        field_simp
        ring
      rw [hexp]
      have hnn : (0 : ℝ) ≤ ε * D ^ 2 * (u : ℝ) * L * (M : ℝ) := by positivity
      linarith [mul_le_mul_of_nonneg_right hkey1 hMR0.le, hnn]
    have hpiece2 : ε * ((m : ℕ) : ℝ)
          * (2 * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)))
        ≤ (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2) := by
      rw [hmD, le_div_iff₀ h3L2]
      have hexp : ε * (D / 2 * (u : ℝ))
          * (2 * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2))) * (3 * L ^ 2)
          = 3 * (ε * pairMainConst * D ^ 3 * (M : ℝ) ^ 2) := by
        field_simp
      rw [hexp]
      have hnn : (0 : ℝ) ≤ ε * pairMainConst * D ^ 3 * (M : ℝ) ^ 2 := by
        have := pairMainConst_pos
        positivity
      linarith [mul_le_mul_of_nonneg_right hkey2 (sq_nonneg ((M : ℝ))), hnn]
    have hpiece3 : ε * ((m : ℕ) : ℝ)
          * (2 * (2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ)))
        ≤ (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2) := by
      rw [hmD, le_div_iff₀ h3L2]
      have hexp : ε * (D / 2 * (u : ℝ))
            * (2 * (2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ))) * (3 * L ^ 2)
          = 6 * (ε * D ^ 2 * L ^ 2 * ((M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4))) := by
        field_simp
        ring
      rw [hexp]
      have hmul := mul_le_mul_of_nonneg_right hkey3 (mul_nonneg hMR0.le h34.le)
      have hRHS : A ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4) * ((M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4))
          = A ^ 2 * (M : ℝ) ^ 2 := by
        rw [show A ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4) * ((M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4))
            = A ^ 2 * (M : ℝ) * ((M : ℝ) ^ ((3 : ℝ) / 4) * (M : ℝ) ^ ((1 : ℝ) / 4)) by ring,
          hprod]
        ring
      rw [hRHS] at hmul
      have hnn : (0 : ℝ) ≤ ε * D ^ 2 * L ^ 2 * ((M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4)) := by
        positivity
      linarith [hmul, hnn]
    have hbsq : b ^ 2 = (M : ℝ) ^ 2 * A ^ 2 / L ^ 2 := by
      rw [hb, div_pow, mul_pow]
    have hsum : (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2) + (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2)
        + (M : ℝ) ^ 2 * A ^ 2 / (3 * L ^ 2) = (M : ℝ) ^ 2 * A ^ 2 / L ^ 2 := by
      field_simp
      ring
    rw [hbsq, ← hsum]
    have hexpand : ε * ((m : ℕ) : ℝ)
        * (64 * D * (M : ℝ) / L
          + 2 * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)
            + 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ)))
        = ε * ((m : ℕ) : ℝ) * (64 * D * (M : ℝ) / L)
          + ε * ((m : ℕ) : ℝ) * (2 * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)))
          + ε * ((m : ℕ) : ℝ)
            * (2 * (2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ))) := by
      ring
    rw [hexpand]
    linarith [hpiece1, hpiece2, hpiece3]
  have hbthr : ((S.card : ℕ) : ℝ) * ((((bigPrimeSet M Mt).card : ℕ) : ℝ) + 2
      * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)
        + 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ))) ≤ b ^ 2 := by
    have hP0 : (0 : ℝ) ≤ pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)
        + 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ) := by
      have := pairMainConst_pos
      have h34 : (0 : ℝ) ≤ (M : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hMR0.le _
      positivity
    have hnn : (0 : ℝ) ≤ (((bigPrimeSet M Mt).card : ℕ) : ℝ) + 2
        * (pairMainConst * D ^ 2 * (M : ℝ) ^ 2 / ((u : ℝ) * L ^ 2)
          + 2 * D * (M : ℝ) * (M : ℝ) ^ ((3 : ℝ) / 4) / (u : ℝ)) := by positivity
    refine le_trans (mul_le_mul hEbad (by linarith [hN]) hnn (by positivity)) hthr
  have hgood := sum_inv_good_markers_ge (X := X) (M₀ := M) (K := K) (S := S)
    (M := bigPrimeSet M Mt) (by omega) (fun p hp => lt_of_mem_bigPrimeSet hp) hsep hpair
    hbthr hb0
  -- the harmonic mass of the whole super-block
  have hbig : ((K₀ : ℝ) + 1) * Real.log 2 ≤ L := by
    rw [markerLogBound] at hlogM
    linarith [hbasepos]
  have hharmge := harm_ge_generic (K₀ := K₀) hM2 hlo hbig hL1
  have hbM : b / (M : ℝ) = A / L := by
    rw [hb]
    field_simp
  have hgoal : multiHarmConst K₀ / (2 * L) = multiHarmConst K₀ / L - A / L := by
    rw [hA]
    field_simp
    ring
  rw [hgoal]
  linarith [hgood, hharmge, hbM]

end

end RHTower.Sieve
