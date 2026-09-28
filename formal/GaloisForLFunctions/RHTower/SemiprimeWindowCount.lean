import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# Squarefree semiprimes and triprimes in windows of length `R/(log R)^B`

For a window `(u, v] ⊆ [R, 2R]` of length at least `R/(log R)^B`:

* every squarefree semiprime `pr ∈ (u, v]`, `p < r`, has `p ≤ √v`, so the semiprime count is at
  most `∑_{p ≤ √v} #{r ∈ (u/p, v/p]}`; with `1/(L - log p) ≤ 1/L + 3 log p/L²`, Mertens' two
  theorems and the log-power prime number theorem this is
  `≤ (v - u)/log R · (log log R + K)`;
* for `q ∈ [2, 5]` the triprimes `qpr` with `5 < p ≤ √(u/q) < r` form disjoint families indexed by
  `p`, and their number is `≥ (1 - ε)(v - u)/(q log R) · (log log R - K)`.
-/

open Finset Filter Topology

noncomputable section

namespace RHTower.PrimeCells

/-- The squarefree semiprimes of the window `(u, v]`. -/
def semiprimesIn (u v : ℝ) : Finset ℕ :=
  (Ioc ⌊u⌋₊ ⌊v⌋₊).filter fun n => Squarefree n ∧ n.primeFactors.card = 2

/-- A squarefree integer with two prime factors is a product `pr` of primes `p < r`. -/
theorem squarefree_card_primeFactors_two_iff {n : ℕ} :
    (Squarefree n ∧ n.primeFactors.card = 2) ↔
      ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p < r ∧ n = p * r := by
  constructor
  · rintro ⟨hsq, hcard⟩
    obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.mp hcard
    have hn : n = x * y := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq, hxy', Finset.prod_pair hxy]
    have hx : x.Prime := Nat.prime_of_mem_primeFactors (by rw [hxy']; simp)
    have hy : y.Prime := Nat.prime_of_mem_primeFactors (by rw [hxy']; simp)
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, y, hx, hy, h, hn⟩
    · exact ⟨y, x, hy, hx, h, by rw [hn, mul_comm]⟩
  · rintro ⟨p, r, hp, hr, hpr, rfl⟩
    refine ⟨Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hp hr).mpr hpr.ne,
      Irreducible.squarefree hp, Irreducible.squarefree hr⟩, ?_⟩
    rw [Nat.primeFactors_mul hp.ne_zero hr.ne_zero, hp.primeFactors, hr.primeFactors]
    exact Finset.card_pair hpr.ne

theorem mem_semiprimesIn {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) {n : ℕ} :
    n ∈ semiprimesIn u v ↔ u < n ∧ (n : ℝ) ≤ v ∧
      ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p < r ∧ n = p * r := by
  unfold semiprimesIn
  rw [mem_filter, mem_Ioc, squarefree_card_primeFactors_two_iff, Nat.floor_lt hu, Nat.le_floor_iff hv]
  tauto

/-- Every semiprime `pr ∈ (u, v]` with `p < r` has `p ≤ √v` and `r ∈ (u/p, v/p]`. -/
theorem semiprimesIn_subset {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    semiprimesIn u v ⊆ (Nat.primesLE ⌊Real.sqrt v⌋₊).biUnion
      fun p => (windowPrimes (u / p) (v / p)).image (p * ·) := by
  intro n hn
  obtain ⟨hun, hnv, p, r, hp, hr, hpr, rfl⟩ := (mem_semiprimesIn hu hv).mp hn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpr' : (p : ℝ) < r := by exact_mod_cast hpr
  push_cast at hun hnv
  have hpp : (p : ℝ) ^ 2 ≤ v := by nlinarith
  have hpsq : (p : ℝ) ≤ Real.sqrt v := Real.le_sqrt hp0.le hv |>.mpr hpp
  rw [mem_biUnion]
  refine ⟨p, Nat.mem_primesLE.mpr ⟨Nat.le_floor hpsq, hp⟩, mem_image.mpr ⟨r, ?_, rfl⟩⟩
  rw [mem_windowPrimes (by positivity) (by positivity)]
  refine ⟨hr, ?_, ?_⟩
  · rw [div_lt_iff₀ hp0]; linarith
  · rw [le_div_iff₀ hp0]; linarith

/-- The semiprime count is at most `∑_{p ≤ √v} #{r ∈ (u/p, v/p]}`. -/
theorem card_semiprimesIn_le_sum {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (semiprimesIn u v).card ≤
      ∑ p ∈ Nat.primesLE ⌊Real.sqrt v⌋₊, (windowPrimes (u / p) (v / p)).card :=
  (card_le_card (semiprimesIn_subset hu hv)).trans
    (card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le))

/-- `k (log log R + c) ≤ log R` for all large `R`. -/
theorem eventually_mul_logLog_add_le {k : ℝ} (hk : 0 < k) (c : ℝ) :
    ∀ᶠ R : ℝ in atTop, k * (Real.log (Real.log R) + c) ≤ Real.log R := by
  have h1 : ∀ᶠ L : ℝ in atTop, Real.log L ≤ L / (2 * k) := by
    have ho := Real.isLittleO_log_id_atTop.def (c := 1 / (2 * k)) (by positivity)
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with L hL hL1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
      id, abs_of_nonneg (by linarith)] at hL
    calc Real.log L ≤ 1 / (2 * k) * L := hL
      _ = L / (2 * k) := by ring
  have h2 : ∀ᶠ L : ℝ in atTop, 2 * k * |c| ≤ L := eventually_ge_atTop _
  have h3 : ∀ᶠ L : ℝ in atTop, k * (Real.log L + c) ≤ L := by
    filter_upwards [h1, h2] with L hL1 hL2
    have hc := le_abs_self c
    have e : k * (L / (2 * k)) = L / 2 := by field_simp
    have : k * c ≤ k * |c| := mul_le_mul_of_nonneg_left hc hk.le
    nlinarith
  exact Real.tendsto_log_atTop.eventually h3

/-- One prime `p` with `p² ≤ 2R` of the semiprime cover:
`#{r ∈ (u/p, v/p]} ≤ (v-u)/(pL) + 3(v-u) log p/(pL²) + 4C 3^{A+1} R/(p L^{A+2})`. -/
theorem card_windowPrimes_div_prime_le {C T : ℝ} {A : ℕ} (hC : 0 < C) (hT : 3 ≤ T)
    (hθ : ∀ t : ℝ, T ≤ t → |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ A)
    {R u v : ℝ} (hR0 : 0 < R) (hRT : 2 * T ^ 2 ≤ R) (hL2 : 3 * Real.log 2 ≤ Real.log R)
    (hRu : R ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * R) {p : ℕ} (hpp : p.Prime)
    (hpsq : (p : ℝ) ^ 2 ≤ 2 * R) :
    ((windowPrimes (u / p) (v / p)).card : ℝ) ≤
      (v - u) / Real.log R * (1 / p) + 3 * (v - u) / Real.log R ^ 2 * (Real.log p / p) +
        4 * C * 3 ^ (A + 1) * (R / Real.log R ^ A) / Real.log R * (1 / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hL0 : 0 < Real.log R := by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); linarith
  have hvu : 0 ≤ v - u := by linarith
  -- `T ≤ u/p`
  have hpT : (p : ℝ) * T ≤ R := by
    have h1 : ((p : ℝ) * T) ^ 2 ≤ R ^ 2 := by
      calc ((p : ℝ) * T) ^ 2 = (p : ℝ) ^ 2 * T ^ 2 := by ring
        _ ≤ 2 * R * T ^ 2 := by gcongr
        _ ≤ R * R := by have := mul_le_mul_of_nonneg_left hRT hR0.le; linarith
        _ = R ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) hR0.le two_ne_zero).mp h1
  have haT : T ≤ u / p := by
    rw [le_div_iff₀ hp0]
    calc T * p = p * T := by ring
      _ ≤ R := hpT
      _ ≤ u := hRu
  have hab : u / p ≤ v / p := by gcongr
  have hinc := abs_theta_increment_le hC.le hT hθ haT hab
  -- `log (u/p) ≥ L - log p ≥ L/3`
  have hlogp : Real.log p ≤ (Real.log R + Real.log 2) / 2 := by
    have h1 : Real.log ((p : ℝ) ^ 2) ≤ Real.log (2 * R) := Real.log_le_log (by positivity) hpsq
    rw [Real.log_pow, Real.log_mul (by norm_num) hR0.ne'] at h1
    push_cast at h1
    linarith
  have hloga : Real.log R - Real.log p ≤ Real.log (u / p) := by
    rw [Real.log_div (by linarith) hp0.ne']
    have := Real.log_le_log hR0 hRu
    linarith
  have hL3 : Real.log R / 3 ≤ Real.log R - Real.log p := by linarith
  have hla0 : 0 < Real.log R - Real.log p := by linarith
  have hla : 0 < Real.log (u / p) := by linarith
  have hθ' : Chebyshev.theta (v / p) - Chebyshev.theta (u / p) ≤
      (v - u) / p + 2 * C * (v / p) / Real.log (u / p) ^ A := by
    have := (abs_le.mp hinc).2
    have e : v / p - u / p = (v - u) / p := by ring
    linarith
  have hcard := card_windowPrimes_mul_log_le (show 1 ≤ u / p by linarith) hab
  have hc : ((windowPrimes (u / p) (v / p)).card : ℝ) ≤
      (v - u) / p / Real.log (u / p) + 2 * C * (v / p) / Real.log (u / p) ^ (A + 1) := by
    rw [pow_succ, ← div_div, ← add_div, le_div_iff₀ hla]
    linarith
  have hc1 : (v - u) / p / Real.log (u / p) ≤ (v - u) / p / (Real.log R - Real.log p) :=
    div_le_div_of_nonneg_left (by positivity) hla0 hloga
  have hinv : 1 / (Real.log R - Real.log p) ≤ 1 / Real.log R + 3 * Real.log p / Real.log R ^ 2 := by
    have hlp0 : 0 ≤ Real.log p := Real.log_nonneg hp1.le
    have h23 : 0 ≤ 2 * Real.log R - 3 * Real.log p := by linarith
    have hprod := mul_nonneg (mul_nonneg hlp0 hL0.le) h23
    rw [div_add_div _ _ hL0.ne' (by positivity), div_le_div_iff₀ hla0 (by positivity)]
    nlinarith
  have hc1' : (v - u) / p / (Real.log R - Real.log p) ≤
      (v - u) / Real.log R * (1 / p) + 3 * (v - u) / Real.log R ^ 2 * (Real.log p / p) := by
    calc (v - u) / p / (Real.log R - Real.log p) = (v - u) / p * (1 / (Real.log R - Real.log p)) := by
          ring
      _ ≤ (v - u) / p * (1 / Real.log R + 3 * Real.log p / Real.log R ^ 2) := by gcongr
      _ = _ := by ring
  have hc2 : 2 * C * (v / p) / Real.log (u / p) ^ (A + 1) ≤
      4 * C * 3 ^ (A + 1) * (R / Real.log R ^ A) / Real.log R * (1 / p) := by
    have hpow : (Real.log R / 3) ^ (A + 1) ≤ Real.log (u / p) ^ (A + 1) := by
      gcongr
      linarith
    have hpow0 : 0 < (Real.log R / 3) ^ (A + 1) := by positivity
    have hv0 : 0 ≤ v := by linarith
    calc 2 * C * (v / p) / Real.log (u / p) ^ (A + 1)
        ≤ 2 * C * (v / p) / (Real.log R / 3) ^ (A + 1) :=
          div_le_div_of_nonneg_left (by positivity) hpow0 hpow
      _ ≤ 2 * C * (2 * R / p) / (Real.log R / 3) ^ (A + 1) := by gcongr
      _ = 4 * C * 3 ^ (A + 1) * (R / Real.log R ^ A) / Real.log R * (1 / p) := by
          rw [div_pow, pow_succ (Real.log R)]; field_simp; ring
  linarith

/-- The summed semiprime bound: with `S₁ = ∑ 1/p ≤ log L + c`, `S₂ = ∑ log p/p ≤ 2L` and
`k(log L + c) ≤ L`, the three sums total at most `(v-u)/L · (log L + c + 7)`. -/
theorem semiprime_sum_arith {L w E S₁ S₂ lL c k : ℝ} (hL : 0 < L) (hw : 0 ≤ w) (hk : 0 ≤ k)
    (hE : E ≤ w / L) (hS₁0 : 0 ≤ S₁) (hS₁ : S₁ ≤ lL + c) (hS₂ : S₂ ≤ 2 * L)
    (hkL : k * (lL + c) ≤ L) :
    w / L * S₁ + 3 * w / L ^ 2 * S₂ + k * E / L * S₁ ≤ w / L * (lL + (c + 7)) := by
  have h1 : 0 ≤ w / L := by positivity
  have h2 : w / L * S₁ ≤ w / L * (lL + c) := mul_le_mul_of_nonneg_left hS₁ h1
  have h3 : 3 * w / L ^ 2 * S₂ ≤ w / L * 6 := by
    calc 3 * w / L ^ 2 * S₂ ≤ 3 * w / L ^ 2 * (2 * L) := by gcongr
      _ = w / L * 6 := by field_simp; ring
  have h4 : k * E / L * S₁ ≤ w / L * 1 := by
    have hlc : 0 ≤ lL + c := hS₁0.trans hS₁
    calc k * E / L * S₁ ≤ k * (w / L) / L * (lL + c) := by gcongr
      _ = w / L * (k * (lL + c) / L) := by ring
      _ ≤ w / L * 1 := by
          gcongr
          rw [div_le_one hL]; exact hkL
  nlinarith

/-- **Semiprime counts from above.**  Uniformly for `(u, v] ⊆ [R, 2R]` of length at least
`R/(log R)^B`: `#{squarefree pr ∈ (u, v]} ≤ (v - u)/log R · (log log R + K)`. -/
theorem exists_card_semiprimesIn_le (B : ℝ) :
    ∃ K R₀ : ℝ, 3 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ u v : ℝ, R ≤ u → u ≤ v → v ≤ 2 * R →
      R / Real.log R ^ B ≤ v - u →
      ((semiprimesIn u v).card : ℝ) ≤ (v - u) / Real.log R * (Real.log (Real.log R) + K) := by
  obtain ⟨A, hAB⟩ : ∃ A : ℕ, B + 1 ≤ A := ⟨⌈B⌉₊ + 1, by push_cast; linarith [Nat.le_ceil B]⟩
  obtain ⟨C, hC, T, hT, hθ⟩ := exists_abs_theta_sub_le A
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 4 * C * 3 ^ (A + 1) := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; positivity
  have hev : ∀ᶠ R : ℝ in atTop, 2 * T ^ 2 ≤ R ∧ 16 ≤ R ∧ 1 ≤ Real.log R ∧
      3 * Real.log 2 ≤ Real.log R ∧ Real.log 4 ≤ Real.log R ∧
      k * (Real.log (Real.log R) + Sieve.mertensSecondUpperConst) ≤ Real.log R :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
        ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
          ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
            (eventually_mul_logLog_add_le hk0 _)))))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨Sieve.mertensSecondUpperConst + 7, max X 3, le_max_right _ _,
    fun R hR u v hRu huv hv hgap => ?_⟩
  obtain ⟨hRT, hR16, hL1, hL2, hL4, hLk⟩ := hX R ((le_max_left _ _).trans hR)
  have hR0 : 0 < R := by linarith
  have hL0 : 0 < Real.log R := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hvu : 0 ≤ v - u := by linarith
  -- the prime range `p ≤ N = ⌊√v⌋`
  have hsv : 4 ≤ Real.sqrt v := (Real.le_sqrt (by norm_num) hv0).mpr (by nlinarith)
  have hN2 : 2 ≤ ⌊Real.sqrt v⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hNsq : (⌊Real.sqrt v⌋₊ : ℝ) ≤ Real.sqrt v := Nat.floor_le (Real.sqrt_nonneg _)
  have hN0 : (0 : ℝ) < ⌊Real.sqrt v⌋₊ := by exact_mod_cast (show 0 < ⌊Real.sqrt v⌋₊ by omega)
  have hsqrtR : Real.sqrt v ≤ R := (Real.sqrt_le_left hR0.le).mpr (by nlinarith)
  have hlogN : Real.log ⌊Real.sqrt v⌋₊ ≤ Real.log R := Real.log_le_log hN0 (hNsq.trans hsqrtR)
  have hlogN0 : 0 < Real.log ⌊Real.sqrt v⌋₊ :=
    Real.log_pos (by exact_mod_cast (show 1 < ⌊Real.sqrt v⌋₊ by omega))
  have hS1 : ∑ p ∈ Nat.primesLE ⌊Real.sqrt v⌋₊, 1 / (p : ℝ) ≤
      Real.log (Real.log R) + Sieve.mertensSecondUpperConst := by
    have h := Sieve.mertensS_le hN2
    have hll : Sieve.logLog ⌊Real.sqrt v⌋₊ ≤ Real.log (Real.log R) := Real.log_le_log hlogN0 hlogN
    unfold Sieve.mertensS at h
    linarith
  have hS1' : 0 ≤ ∑ p ∈ Nat.primesLE ⌊Real.sqrt v⌋₊, 1 / (p : ℝ) :=
    sum_nonneg fun p _ => by positivity
  have hS2 : ∑ p ∈ Nat.primesLE ⌊Real.sqrt v⌋₊, Real.log p / (p : ℝ) ≤ 2 * Real.log R := by
    have h := Sieve.mertensFirst_upper (show 1 ≤ ⌊Real.sqrt v⌋₊ by omega)
    linarith
  have hterm : ∀ p ∈ Nat.primesLE ⌊Real.sqrt v⌋₊, ((windowPrimes (u / p) (v / p)).card : ℝ) ≤
      (v - u) / Real.log R * (1 / p) + 3 * (v - u) / Real.log R ^ 2 * (Real.log p / p) +
        k * (R / Real.log R ^ A) / Real.log R * (1 / p) := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpv : (p : ℝ) ≤ Real.sqrt v := (Nat.cast_le.mpr hpN).trans hNsq
    have hpsq : (p : ℝ) ^ 2 ≤ 2 * R := by
      have h1 : (p : ℝ) ^ 2 ≤ Real.sqrt v ^ 2 := by gcongr
      rw [Real.sq_sqrt hv0] at h1
      linarith
    rw [hk]
    exact card_windowPrimes_div_prime_le hC hT hθ hR0 hRT hL2 hRu huv hv hpp hpsq
  have hRA : R / Real.log R ^ A ≤ (v - u) / Real.log R :=
    (rpow_logPow_le hR0.le hL1 hAB).trans (by gcongr)
  calc ((semiprimesIn u v).card : ℝ)
      ≤ ∑ p ∈ Nat.primesLE ⌊Real.sqrt v⌋₊, ((windowPrimes (u / p) (v / p)).card : ℝ) := by
        exact_mod_cast card_semiprimesIn_le_sum hu0 hv0
    _ ≤ ∑ p ∈ Nat.primesLE ⌊Real.sqrt v⌋₊, ((v - u) / Real.log R * (1 / p) +
          3 * (v - u) / Real.log R ^ 2 * (Real.log p / p) +
          k * (R / Real.log R ^ A) / Real.log R * (1 / p)) := sum_le_sum hterm
    _ = (v - u) / Real.log R * ∑ p ∈ Nat.primesLE ⌊Real.sqrt v⌋₊, 1 / (p : ℝ) +
          3 * (v - u) / Real.log R ^ 2 * ∑ p ∈ Nat.primesLE ⌊Real.sqrt v⌋₊, Real.log p / (p : ℝ) +
          k * (R / Real.log R ^ A) / Real.log R *
            ∑ p ∈ Nat.primesLE ⌊Real.sqrt v⌋₊, 1 / (p : ℝ) := by
        rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum, mul_sum]
    _ ≤ _ := semiprime_sum_arith hL0 hvu hk0.le hRA hS1' hS1 hS2 hLk

/-! ### Triprimes -/

/-- The primes `5 < p ≤ N`. -/
def largePrimesLE (N : ℕ) : Finset ℕ := (Nat.primesLE N).filter (5 < ·)

/-- The triprimes `qpr ∈ (u, v]` with `5 < p ≤ √(u/q) < r` primes. -/
def triprimeTargets (q : ℕ) (u v : ℝ) : Finset ℕ :=
  (largePrimesLE ⌊Real.sqrt (u / q)⌋₊).biUnion fun p =>
    (windowPrimes (u / (q * p)) (v / (q * p))).image fun r => q * p * r

/-- `pr = p'r'` with primes `p < r`, `p' < r'` forces `p = p'`. -/
theorem prime_eq_of_mul_eq {p r p' r' : ℕ} (hp : p.Prime) (hr : r.Prime) (hp' : p'.Prime)
    (hr' : r'.Prime) (hpr : p < r) (hpr' : p' < r') (h : p * r = p' * r') : p = p' := by
  have h1 : p ∣ p' * r' := h ▸ dvd_mul_right p r
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
  · exact (Nat.prime_dvd_prime_iff_eq hp hp').mp h2
  · have e : p = r' := (Nat.prime_dvd_prime_iff_eq hp hr').mp h2
    have h3 : p' ∣ p * r := h ▸ dvd_mul_right p' r'
    rcases (Nat.Prime.dvd_mul hp').mp h3 with h4 | h4
    · exact ((Nat.prime_dvd_prime_iff_eq hp' hp).mp h4).symm
    · have e' : p' = r := (Nat.prime_dvd_prime_iff_eq hp' hr).mp h4
      omega

theorem mem_triprimeTargets {q : ℕ} (hq : 0 < q) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) {n : ℕ}
    (hn : n ∈ triprimeTargets q u v) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ 5 < p ∧ p < r ∧ n = q * p * r ∧ u < n ∧ (n : ℝ) ≤ v := by
  unfold triprimeTargets at hn
  obtain ⟨p, hp, hn⟩ := mem_biUnion.mp hn
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hn
  obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp (mem_filter.mp hp).1
  have hp5 : 5 < p := (mem_filter.mp hp).2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hqp : (0 : ℝ) < q * p := by positivity
  obtain ⟨hrp, hlt, hle⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hr
  have hpsq : (p : ℝ) ≤ Real.sqrt (u / q) :=
    (Nat.cast_le.mpr hpN).trans (Nat.floor_le (Real.sqrt_nonneg _))
  have hpp2 : (p : ℝ) ^ 2 ≤ u / q := by
    have := Real.sq_sqrt (show 0 ≤ u / q by positivity)
    nlinarith [Real.sqrt_nonneg (u / q)]
  have hlt' : u < q * p * r := by
    rw [div_lt_iff₀ hqp] at hlt; linarith
  have hle' : (q * p * r : ℝ) ≤ v := by
    rw [le_div_iff₀ hqp] at hle; linarith
  have hpr : p < r := by
    have h1 : (p : ℝ) * (q * p) ≤ u := by
      rw [le_div_iff₀ hq0] at hpp2; nlinarith
    have h2 : (p : ℝ) < r := by
      by_contra h
      push Not at h
      have : (q * p * r : ℝ) ≤ q * p * p := by gcongr
      nlinarith
    exact_mod_cast h2
  exact ⟨p, r, hpp, hrp, hp5, hpr, rfl, by push_cast; linarith, by push_cast; linarith⟩

/-- The triprime families indexed by `p` are disjoint, so the target count is the sum of the prime
counts `#{r ∈ (u/(qp), v/(qp)]}`. -/
theorem card_triprimeTargets {q : ℕ} (hq : 0 < q) {u v : ℝ} (hu : 0 ≤ u) :
    (triprimeTargets q u v).card =
      ∑ p ∈ largePrimesLE ⌊Real.sqrt (u / q)⌋₊, (windowPrimes (u / (q * p)) (v / (q * p))).card := by
  unfold triprimeTargets
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  -- every `r` in the family of `p` exceeds `p`
  have hbig : ∀ p ∈ largePrimesLE ⌊Real.sqrt (u / q)⌋₊, ∀ r ∈ windowPrimes (u / (q * p)) (v / (q * p)),
      p.Prime ∧ r.Prime ∧ p < r := by
    intro p hp r hr
    obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp (mem_filter.mp hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hqp : (0 : ℝ) < q * p := by positivity
    by_cases hv : 0 ≤ v
    · obtain ⟨hrp, hlt, -⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hr
      have hpsq : (p : ℝ) ≤ Real.sqrt (u / q) :=
        (Nat.cast_le.mpr hpN).trans (Nat.floor_le (Real.sqrt_nonneg _))
      have hpp2 : (p : ℝ) ^ 2 ≤ u / q := by
        have := Real.sq_sqrt (show 0 ≤ u / q by positivity)
        nlinarith [Real.sqrt_nonneg (u / q)]
      have h1 : (p : ℝ) * (q * p) ≤ u := by
        rw [le_div_iff₀ hq0] at hpp2; nlinarith
      have h2 : (p : ℝ) < r := by
        rw [div_lt_iff₀ hqp] at hlt
        by_contra h
        push Not at h
        have : (r : ℝ) * (q * p) ≤ p * (q * p) := by gcongr
        linarith
      exact ⟨hpp, hrp, by exact_mod_cast h2⟩
    · push Not at hv
      have : ⌊v / (q * p)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by
        have : v / (q * p) < 0 := div_neg_of_neg_of_pos hv hqp
        linarith)
      simp [windowPrimes, this] at hr
  rw [card_biUnion]
  · refine sum_congr rfl fun p hp => card_image_of_injOn fun r _ r' _ h => ?_
    have hqp : 0 < q * p := Nat.mul_pos hq (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.pos
    exact Nat.eq_of_mul_eq_mul_left hqp h
  · intro p hp p' hp' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hn
    obtain ⟨r', hr', h⟩ := mem_image.mp hn'
    obtain ⟨hpp, hrp, hpr⟩ := hbig p hp r hr
    obtain ⟨hpp', hrp', hpr'⟩ := hbig p' hp' r' hr'
    have h' : p' * r' = p * r := by
      have : q * (p' * r') = q * (p * r) := by rw [← mul_assoc, ← mul_assoc]; exact h
      exact Nat.eq_of_mul_eq_mul_left hq this
    exact hne (prime_eq_of_mul_eq hpp' hrp' hpp hrp hpr' hpr h').symm

/-- `∑_{5 < p ≤ N} 1/p ≥ ∑_{p ≤ N} 1/p - 31/30`. -/
theorem sum_largePrimesLE_ge (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, 1 / (p : ℝ) - 31 / 30 ≤ ∑ p ∈ largePrimesLE N, 1 / (p : ℝ) := by
  unfold largePrimesLE
  rw [← sum_filter_add_sum_filter_not (Nat.primesLE N) (5 < ·)]
  have hsmall : ∑ p ∈ (Nat.primesLE N).filter (fun p => ¬ 5 < p), 1 / (p : ℝ) ≤ 31 / 30 := by
    have hsub : (Nat.primesLE N).filter (fun p => ¬ 5 < p) ⊆ {2, 3, 5} := by
      intro p hp
      obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp (mem_filter.mp hp).1
      have hp5 : p ≤ 5 := by have := (mem_filter.mp hp).2; omega
      have h2 := hpp.two_le
      interval_cases p <;> simp_all (config := { decide := true })
    calc ∑ p ∈ (Nat.primesLE N).filter (fun p => ¬ 5 < p), 1 / (p : ℝ)
        ≤ ∑ p ∈ ({2, 3, 5} : Finset ℕ), 1 / (p : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 31 / 30 := by norm_num
  linarith

/-- One prime `5 < p` with `p² ≤ u/q` of the triprime supply:
`#{r ∈ (u/(qp), v/(qp)]} ≥ (1 - ε)(v - u)/(q p log R)`. -/
theorem card_windowPrimes_triprime_ge {C T ε : ℝ} {A : ℕ} (hC : 0 < C) (hT : 3 ≤ T)
    (hθ : ∀ t : ℝ, T ≤ t → |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ A)
    {R u v : ℝ} (hR0 : 0 < R) (hRT : 5 * T ^ 2 ≤ R) (hL1 : 1 ≤ Real.log R)
    (hL5 : 3 * Real.log 5 ≤ Real.log R) (hRu : R ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * R)
    (hRA : 4 * C * 3 ^ A * (R / Real.log R ^ A) ≤ ε * (v - u))
    {q : ℕ} (hq2 : 2 ≤ q) (hq5 : q ≤ 5) {p : ℕ} (hpp : p.Prime) (hp5 : 5 < p)
    (hpp2 : (p : ℝ) ^ 2 ≤ u / q) :
    (1 - ε) * (v - u) / (q * Real.log R) * (1 / p) ≤
      ((windowPrimes (u / (q * p)) (v / (q * p))).card : ℝ) := by
  have hL0 : 0 < Real.log R := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq5' : (q : ℝ) ≤ 5 := by exact_mod_cast hq5
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp6 : (6 : ℝ) ≤ p := by exact_mod_cast hp5
  have hqp : (0 : ℝ) < q * p := by positivity
  have hu0 : 0 ≤ u := by linarith
  have hv0 : 0 ≤ v := by linarith
  have huq : R / 5 ≤ u / q := by
    rw [div_le_div_iff₀ (by norm_num) hq0]; nlinarith
  -- `a = u/(qp)` satisfies `p ≤ a` and `u/q ≤ a²`
  have hap : u / (q * p) * p = u / q := by field_simp
  have hpa : (p : ℝ) ≤ u / (q * p) := by
    rw [le_div_iff₀ hqp]
    rw [le_div_iff₀ hq0] at hpp2
    nlinarith
  have ha2 : u / q ≤ (u / (q * p)) ^ 2 := by
    rw [← hap, sq]
    exact mul_le_mul_of_nonneg_left hpa (by positivity)
  have haT : T ≤ u / (q * p) := by
    have h1 : T ^ 2 ≤ (u / (q * p)) ^ 2 := by
      have : T ^ 2 ≤ R / 5 := by rw [le_div_iff₀ (by norm_num)]; linarith
      linarith
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).mp h1
  have hab : u / (q * p) ≤ v / (q * p) := by gcongr
  have hinc := abs_theta_increment_le hC.le hT hθ haT hab
  -- `log a ≥ L/3` and `log b ≤ L`
  have hloga : Real.log R / 3 ≤ Real.log (u / (q * p)) := by
    have h1 : Real.log (R / 5) ≤ Real.log ((u / (q * p)) ^ 2) :=
      Real.log_le_log (by positivity) (huq.trans ha2)
    rw [Real.log_pow, Real.log_div hR0.ne' (by norm_num)] at h1
    push_cast at h1
    linarith
  have hlogb : Real.log (v / (q * p)) ≤ Real.log R := by
    have hv0' : 0 < v := by linarith
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hqp]
    have : (12 : ℝ) ≤ q * p := by nlinarith
    nlinarith
  have hLA0 : 0 < (Real.log R / 3) ^ A := by positivity
  have hLA : (Real.log R / 3) ^ A ≤ Real.log (u / (q * p)) ^ A := by
    gcongr
  have herr : 2 * C * (v / (q * p)) / Real.log (u / (q * p)) ^ A ≤
      1 / (q * p) * (4 * C * 3 ^ A * (R / Real.log R ^ A)) := by
    calc 2 * C * (v / (q * p)) / Real.log (u / (q * p)) ^ A
        ≤ 2 * C * (v / (q * p)) / (Real.log R / 3) ^ A :=
          div_le_div_of_nonneg_left (by positivity) hLA0 hLA
      _ ≤ 2 * C * (2 * R / (q * p)) / (Real.log R / 3) ^ A := by gcongr
      _ = 1 / (q * p) * (4 * C * 3 ^ A * (R / Real.log R ^ A)) := by
          rw [div_pow]; field_simp; ring
  have hθge : (1 - ε) * (v - u) / (q * p) ≤
      Chebyshev.theta (v / (q * p)) - Chebyshev.theta (u / (q * p)) := by
    have h1 := (abs_le.mp hinc).1
    have e : v / (q * p) - u / (q * p) = (v - u) / (q * p) := by ring
    have h2 : 1 / (q * p) * (4 * C * 3 ^ A * (R / Real.log R ^ A)) ≤
        1 / (q * p) * (ε * (v - u)) := by gcongr
    have e2 : (1 - ε) * (v - u) / (q * p) = (v - u) / (q * p) - 1 / (q * p) * (ε * (v - u)) := by
      ring
    linarith
  have hcard := theta_sub_le_card_mul_log (show 0 ≤ u / (q * p) by positivity) hab
  have hc0 : (0 : ℝ) ≤ (windowPrimes (u / (q * p)) (v / (q * p))).card := Nat.cast_nonneg _
  have hmain : (1 - ε) * (v - u) / (q * p) ≤
      ((windowPrimes (u / (q * p)) (v / (q * p))).card : ℝ) * Real.log R :=
    hθge.trans (hcard.trans (mul_le_mul_of_nonneg_left hlogb hc0))
  calc (1 - ε) * (v - u) / (q * Real.log R) * (1 / p) = (1 - ε) * (v - u) / (q * p) / Real.log R := by
        field_simp
    _ ≤ ((windowPrimes (u / (q * p)) (v / (q * p))).card : ℝ) * Real.log R / Real.log R := by
        gcongr
    _ = _ := by field_simp

/-- **Triprime counts from below.**  Uniformly for `(u, v] ⊆ [R, 2R]` of length at least
`R/(log R)^B` and `2 ≤ q ≤ 5`:
`#{qpr ∈ (u, v] : 5 < p ≤ √(u/q) < r} ≥ (1 - ε)(v - u)/(q log R) · (log log R - K)`. -/
theorem exists_card_triprimeTargets_ge (B : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K R₀ : ℝ, 3 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ q : ℕ, 2 ≤ q → q ≤ 5 →
      ∀ u v : ℝ, R ≤ u → u ≤ v → v ≤ 2 * R → R / Real.log R ^ B ≤ v - u →
      (1 - ε) * (v - u) / (q * Real.log R) * (Real.log (Real.log R) - K) ≤
        ((triprimeTargets q u v).card : ℝ) := by
  obtain ⟨A, hAB⟩ : ∃ A : ℕ, B + 1 ≤ A := ⟨⌈B⌉₊ + 1, by push_cast; linarith [Nat.le_ceil B]⟩
  obtain ⟨C, hC, T, hT, hθ⟩ := exists_abs_theta_sub_le A
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Sieve.mertensSecondLowerConst + 31 / 30 + Real.log 3 := ⟨_, rfl⟩
  have hev : ∀ᶠ R : ℝ in atTop, 5 * T ^ 2 ≤ R ∧ 80 ≤ R ∧ 1 ≤ Real.log R ∧
      3 * Real.log 5 ≤ Real.log R ∧ 3 * Real.log 5 + 6 * Real.log 2 ≤ Real.log R ∧
      4 * C * 3 ^ A / ε ≤ Real.log R :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
        ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
          ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
            (Real.tendsto_log_atTop.eventually_ge_atTop _)))))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨K, max X 3, le_max_right _ _, fun R hR q hq2 hq5 u v hRu huv hv hgap => ?_⟩
  obtain ⟨hRT, hR80, hL1, hL5, hL52, hLC⟩ := hX R ((le_max_left _ _).trans hR)
  have hR0 : 0 < R := by linarith
  have hL0 : 0 < Real.log R := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hvu : 0 ≤ v - u := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have huq : R / 5 ≤ u / q := by
    have hq5' : (q : ℝ) ≤ 5 := by exact_mod_cast hq5
    rw [div_le_div_iff₀ (by norm_num) hq0]; nlinarith
  -- `log N ≥ L/3` for `N = ⌊√(u/q)⌋`
  have hsq : Real.sqrt (R / 5) ≤ Real.sqrt (u / q) := Real.sqrt_le_sqrt huq
  have hsR : 4 ≤ Real.sqrt (R / 5) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by
    have : (16 : ℝ) ≤ R / 5 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith)
  have hNge : Real.sqrt (R / 5) / 2 ≤ ⌊Real.sqrt (u / q)⌋₊ := by
    have := Nat.lt_floor_add_one (Real.sqrt (u / q))
    linarith
  have hN2 : 2 ≤ ⌊Real.sqrt (u / q)⌋₊ := by
    have : (2 : ℝ) ≤ ⌊Real.sqrt (u / q)⌋₊ := by linarith
    exact_mod_cast this
  have hlogN : Real.log R / 3 ≤ Real.log ⌊Real.sqrt (u / q)⌋₊ := by
    have h1 : Real.log (Real.sqrt (R / 5) / 2) ≤ Real.log ⌊Real.sqrt (u / q)⌋₊ :=
      Real.log_le_log (by positivity) hNge
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by positivity),
      Real.log_div hR0.ne' (by norm_num)] at h1
    linarith
  have hS : Real.log (Real.log R) - K ≤ ∑ p ∈ largePrimesLE ⌊Real.sqrt (u / q)⌋₊, 1 / (p : ℝ) := by
    have h1 := Sieve.le_mertensS hN2
    have h2 := sum_largePrimesLE_ge ⌊Real.sqrt (u / q)⌋₊
    have h3 : Real.log (Real.log R / 3) ≤ Sieve.logLog ⌊Real.sqrt (u / q)⌋₊ :=
      Real.log_le_log (by positivity) hlogN
    rw [Real.log_div hL0.ne' (by norm_num)] at h3
    unfold Sieve.mertensS at h1
    linarith
  have hRA : 4 * C * 3 ^ A * (R / Real.log R ^ A) ≤ ε * (v - u) := by
    have h2 : R / Real.log R ^ A ≤ R / Real.log R ^ B / Real.log R := rpow_logPow_le hR0.le hL1 hAB
    have h3 : 4 * C * 3 ^ A * (R / Real.log R ^ B / Real.log R) ≤ ε * (R / Real.log R ^ B) := by
      rw [div_le_iff₀ hε] at hLC
      have hq : 0 ≤ R / Real.log R ^ B := by positivity
      rw [mul_div_assoc', div_le_iff₀ hL0]
      nlinarith
    have h4 : ε * (R / Real.log R ^ B) ≤ ε * (v - u) := by gcongr
    have : 0 ≤ 4 * C * 3 ^ A := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 this]
  have hterm : ∀ p ∈ largePrimesLE ⌊Real.sqrt (u / q)⌋₊,
      (1 - ε) * (v - u) / (q * Real.log R) * (1 / p) ≤
        ((windowPrimes (u / (q * p)) (v / (q * p))).card : ℝ) := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp (mem_filter.mp hp).1
    have hpsq : (p : ℝ) ≤ Real.sqrt (u / q) :=
      (Nat.cast_le.mpr hpN).trans (Nat.floor_le (Real.sqrt_nonneg _))
    have hpp2 : (p : ℝ) ^ 2 ≤ u / q := by
      have h1 : (p : ℝ) ^ 2 ≤ Real.sqrt (u / q) ^ 2 := by gcongr
      rwa [Real.sq_sqrt (by positivity)] at h1
    exact card_windowPrimes_triprime_ge hC hT hθ hR0 hRT hL1 hL5 hRu huv hv hRA hq2 hq5 hpp
      (mem_filter.mp hp).2 hpp2
  have hf0 : 0 ≤ (1 - ε) * (v - u) / (q * Real.log R) := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  calc (1 - ε) * (v - u) / (q * Real.log R) * (Real.log (Real.log R) - K)
      ≤ (1 - ε) * (v - u) / (q * Real.log R) *
          ∑ p ∈ largePrimesLE ⌊Real.sqrt (u / q)⌋₊, 1 / (p : ℝ) := by gcongr
    _ = ∑ p ∈ largePrimesLE ⌊Real.sqrt (u / q)⌋₊, (1 - ε) * (v - u) / (q * Real.log R) * (1 / p) := by
        rw [mul_sum]
    _ ≤ ∑ p ∈ largePrimesLE ⌊Real.sqrt (u / q)⌋₊,
          ((windowPrimes (u / (q * p)) (v / (q * p))).card : ℝ) := sum_le_sum hterm
    _ = _ := by rw [card_triprimeTargets (by omega) hu0]; push_cast; rfl

end RHTower.PrimeCells
