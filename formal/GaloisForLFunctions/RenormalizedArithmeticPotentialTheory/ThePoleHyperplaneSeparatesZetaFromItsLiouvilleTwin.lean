import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeFormHasASpectralGapBelowItsPole
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSelfIntersectionFamilyObeysAFixedPointLaw
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheLiouvilleGaugeFlipsThePolarDivergence
import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries

/-!
# The pole hyperplane separates `ζ` from its Liouville twin

Weil's pole term reads a test only through its pole moment `Σ x_n/√n`. On the pole hyperplane
`Σ_{n ≤ N} x_n/√n = 0` it vanishes, and what remains of the atomic Weil form is the archimedean
diagonal minus the prime form; the diagonal is gauge blind. The prime forms of `ζ` and of its
Liouville twin, `P_N(x)` and `P_N(λx)`, are unitarily equivalent, but their tops point in different
directions: `n^{−1/2}` for `ζ` and `λ(n) n^{−1/2}` for the twin. The pole hyperplane cuts off the
first and not the second.

* **Selective margin** (`exists_pole_hyperplane_separates_liouville`): there is `g > 0` such that for
  every `ε > 0`, eventually in `N`, `P_N ≤ (log N − γ − g + ε)|·|²` on the pole hyperplane
  (`ThePrimeFormHasASpectralGapBelowItsPole`), while the Liouville twin's prime form reaches
  `(log N − γ − ε)|x|²` at some `x` on it.

The twin's witness is its own top `λ(n) n^{−1/2}` projected onto the hyperplane. It moves little
because `|Σ_{n ≤ N} λ(n)/n| ≤ 2` (`abs_sum_liouvilleSign_div_le`, from `Σ_{d | m} λ(d) = 1_{□}(m)`),
and the cost of the projection is read off the ground-state identity, polarized at the pole
(`atomicWeilForm_truncPole_add`): `P_N(b + u) = P_N(b) + P_N(u) + 2 Σ R_n b_n u_n`.
So the margin `g` between `ζ` and the twin is uniform in `N`, and it is carried by the pole term.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticElectrostatics ArithmeticFunction

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 1. The Liouville harmonic sum -/

theorem sum_divisors_liouvilleSign {m : ℕ} (hm : m ≠ 0) :
    ∑ d ∈ m.divisors, liouvilleSign d = if IsSquare m then 1 else 0 := by
  have h := RHTower.sum_divisors_liouvilleC hm
  have e : ∀ d ∈ m.divisors, ((liouvilleSign d : ℝ) : ℂ) = RHTower.liouvilleC d := by
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    simp [liouvilleSign, RHTower.liouvilleC, ArithmeticFunction.liouville_apply hd0]
  have h2 : ((∑ d ∈ m.divisors, liouvilleSign d : ℝ) : ℂ) =
      ((if IsSquare m then 1 else 0 : ℝ) : ℂ) := by
    push_cast
    rw [sum_congr rfl e, h, RHTower.squareIndicator]
    split_ifs <;> simp
  exact_mod_cast h2

theorem abs_liouvilleSign (n : ℕ) : |liouvilleSign n| = 1 := by
  simp [liouvilleSign, abs_pow]

/-- `Σ_{n ≤ N} λ(n) ⌊N/n⌋` counts the squares in `[1, N]`. -/
theorem sum_liouvilleSign_mul_div (N : ℕ) :
    ∑ n ∈ Icc 1 N, liouvilleSign n * ((N / n : ℕ) : ℝ) =
      ∑ m ∈ Icc 1 N, (if IsSquare m then (1 : ℝ) else 0) := by
  have h1 : ∀ m ∈ Icc 1 N, (if IsSquare m then (1 : ℝ) else 0) =
      ∑ d ∈ m.divisors, liouvilleSign d := fun m hm =>
    (sum_divisors_liouvilleSign (by have := (mem_Icc.mp hm).1; omega)).symm
  rw [sum_congr rfl h1]
  have h2 : ∑ m ∈ Icc 1 N, ∑ d ∈ m.divisors, liouvilleSign d =
      ∑ d ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).filter (fun m => d ∣ m), liouvilleSign d := by
    refine sum_comm' fun m d => ?_
    simp only [mem_Icc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨a1, a2⟩, hd, -⟩
      exact ⟨⟨⟨a1, a2⟩, hd⟩, Nat.pos_of_dvd_of_pos hd (by omega),
        (Nat.le_of_dvd (by omega) hd).trans a2⟩
    · rintro ⟨⟨⟨a1, a2⟩, hd⟩, -, -⟩
      exact ⟨⟨a1, a2⟩, hd, by omega⟩
  rw [h2]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have : (Icc 1 N).filter (fun m => d ∣ m) = (Ioc 0 N).filter (fun m => d ∣ m) := by
    rw [← Finset.Icc_add_one_left_eq_Ioc]
    rfl
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

/-- **The Liouville harmonic sum is bounded**: `|Σ_{n ≤ N} λ(n)/n| ≤ 2`. -/
theorem abs_sum_liouvilleSign_div_le (N : ℕ) : |∑ n ∈ Icc 1 N, liouvilleSign n / n| ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcount := sum_liouvilleSign_mul_div N
  have hc0 : 0 ≤ ∑ m ∈ Icc 1 N, (if IsSquare m then (1 : ℝ) else 0) :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hcN : ∑ m ∈ Icc 1 N, (if IsSquare m then (1 : ℝ) else 0) ≤ N := by
    calc ∑ m ∈ Icc 1 N, (if IsSquare m then (1 : ℝ) else 0) ≤ ∑ _m ∈ Icc 1 N, (1 : ℝ) :=
          sum_le_sum fun _ _ => by split_ifs <;> norm_num
      _ = N := by simp
  -- the fractional parts
  have hfrac : |∑ n ∈ Icc 1 N, liouvilleSign n * ((N : ℝ) / n - ((N / n : ℕ) : ℝ))| ≤ N := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Icc 1 N, |liouvilleSign n * ((N : ℝ) / n - ((N / n : ℕ) : ℝ))|
        ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) := sum_le_sum fun n hn => by
          have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
          rw [abs_mul, abs_liouvilleSign, one_mul]
          have hlo : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := Nat.cast_div_le
          have hhi : (N : ℝ) / n < ((N / n : ℕ) : ℝ) + 1 := by
            rw [div_lt_iff₀ hn0]
            have := Nat.lt_div_mul_add (a := N) (show 0 < n by exact_mod_cast hn0)
            have h' : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n := by exact_mod_cast this
            linarith
          rw [abs_of_nonneg (by linarith)]
          linarith
      _ = N := by simp
  have hsplit : (N : ℝ) * ∑ n ∈ Icc 1 N, liouvilleSign n / n =
      ∑ n ∈ Icc 1 N, liouvilleSign n * ((N / n : ℕ) : ℝ) +
        ∑ n ∈ Icc 1 N, liouvilleSign n * ((N : ℝ) / n - ((N / n : ℕ) : ℝ)) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  have hbound : |(N : ℝ) * ∑ n ∈ Icc 1 N, liouvilleSign n / n| ≤ 2 * N := by
    rw [hsplit, hcount]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hc0]
    linarith
  rw [abs_mul, abs_of_pos hN0, mul_comm 2] at hbound
  exact le_of_mul_le_mul_left hbound hN0

/-! ### 2. The ground-state identity polarized at the pole -/

theorem atomicWeilForm_smul (N : ℕ) (c : ℝ) (x : ℕ → ℝ) :
    atomicWeilForm N (fun n => c * x n) = c ^ 2 * atomicWeilForm N x := by
  rw [atomicWeilForm, atomicWeilForm, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun n _ => by ring

theorem truncPole_edge {N m t : ℕ} (hm : 1 ≤ m) (ht : 1 ≤ t) (hmt : m * t ≤ N) :
    truncPole N (m * t) = truncPole N m / Real.sqrt t := by
  have hmN : m ≤ N := (Nat.le_mul_of_pos_right m (by omega)).trans hmt
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [truncPole, truncPole, if_pos hmt, if_pos hmN, poleVector, poleVector, Nat.cast_mul,
    Real.sqrt_mul hm0]
  field_simp

/-- The pole is in the kernel of the defect: `D_N(b + u) = D_N(u)`. -/
theorem poleDefect_truncPole_add (N : ℕ) (u : ℕ → ℝ) :
    poleDefect N (fun n => truncPole N n + u n) = poleDefect N u := by
  refine sum_congr rfl fun m hm => sum_congr rfl fun t ht => ?_
  have hm1 := (mem_Icc.mp hm).1
  have ht1 := (mem_Icc.mp ht).1
  have hmt : m * t ≤ N := by
    have := (mem_Icc.mp ht).2
    rw [Nat.le_div_iff_mul_le (by omega)] at this
    linarith [mul_comm m t]
  show Λ t * ((truncPole N (m * t) + u (m * t)) - (truncPole N m + u m) / Real.sqrt t) ^ 2 = _
  rw [truncPole_edge hm1 ht1 hmt]
  congr 2
  ring

/-- **Polarization at the pole**: `P_N(b + u) = P_N(b) + P_N(u) + 2 Σ R_n b_n u_n`, `b` the pole. -/
theorem atomicWeilForm_truncPole_add (N : ℕ) (u : ℕ → ℝ) :
    atomicWeilForm N (fun n => truncPole N n + u n) =
      atomicWeilForm N (truncPole N) + atomicWeilForm N u +
        2 * ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * u n := by
  have h1 := atomicWeilForm_add_poleDefect N (fun n => truncPole N n + u n)
  have h2 := atomicWeilForm_add_poleDefect N u
  have h3 := atomicWeilForm_add_poleDefect N (truncPole N)
  have hD : poleDefect N (truncPole N) = 0 := by
    have := poleDefect_truncPole_add N (fun _ => 0)
    simp only [add_zero] at this
    rw [this]
    simp [poleDefect]
  rw [poleDefect_truncPole_add] at h1
  have hsum : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * (truncPole N n + u n) ^ 2 =
      ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n ^ 2 +
        ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * u n ^ 2 +
          2 * ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * truncPole N n * u n := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  linarith

/-! ### 3. The selective margin -/

/-- The rows sit within a constant of `log N − γ`. -/
theorem abs_row_sub_le {N n : ℕ} (hn : n ∈ Icc 1 N) :
    |mertensSum (N / n) + Real.log n - (Real.log N - γ)| ≤ Real.log 4 + 4 + Real.log 2 + γ := by
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hq : 1 ≤ N / n := (Nat.le_div_iff_mul_le hn1).mpr (by linarith)
  have hq0 : (0 : ℝ) < ((N / n : ℕ) : ℝ) := by exact_mod_cast hq
  have hmert := RHTower.Mertens.mertens_first (N / n) hq
  have hupper : ((N / n : ℕ) : ℝ) * n ≤ N := by exact_mod_cast Nat.div_mul_le_self N n
  have hlower : (N : ℝ) ≤ 2 * (((N / n : ℕ) : ℝ) * n) := by
    have h1 := Nat.lt_div_mul_add (a := N) (show 0 < n by omega)
    have h3 : n ≤ N / n * n := Nat.le_mul_of_pos_left n hq
    have h2 : N ≤ 2 * (N / n * n) := by linarith
    exact_mod_cast h2
  have hN0 : (0 : ℝ) < N := by linarith [mul_pos hq0 hn0]
  have hl1 : Real.log (((N / n : ℕ) : ℝ) * n) ≤ Real.log N := Real.log_le_log (by positivity) hupper
  have hl2 : Real.log N ≤ Real.log 2 + Real.log (((N / n : ℕ) : ℝ) * n) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log hN0 hlower
  rw [Real.log_mul hq0.ne' hn0.ne'] at hl1 hl2
  have hγ : 0 ≤ γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  simp only [mertensSum] at hmert ⊢
  rw [abs_le] at hmert ⊢
  constructor <;> linarith [hmert.1, hmert.2]

/-- **The pole hyperplane separates `ζ` from its Liouville twin.** There is `g > 0` such that for
every `ε > 0`, eventually in `N`: on the pole hyperplane `Σ_{n ≤ N} x_n/√n = 0`, `ζ`'s prime form is
at most `(log N − γ − g + ε)|x|²`, while the Liouville twin's prime form `P_N(λx)` reaches
`(log N − γ − ε)|x|²` at some nonzero `x` of the hyperplane. -/
theorem exists_pole_hyperplane_separates_liouville : ∃ g : ℝ, 0 < g ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      (∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
        atomicWeilForm N x ≤ (Real.log N - γ - g + ε) * ∑ n ∈ Icc 1 N, x n ^ 2) ∧
      (∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧ 0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
        (Real.log N - γ - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
          atomicWeilForm N (fun n => liouvilleSign n * x n)) := by
  obtain ⟨g, hg, hgap⟩ := exists_atomicWeilForm_le_of_pole_orthogonal
  refine ⟨g, hg, fun ε hε => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hgap ε hε
  obtain ⟨N₂, hN₂⟩ := eventually_atomicWeilForm_truncPole_ge (show 0 < ε / 2 by positivity)
  set C₀ := Real.log 4 + 4
  set B := Real.log 4 + 4 + Real.log 2 + γ
  have hC₀ : 0 ≤ C₀ := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hB : 0 ≤ B := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  set K := 4 + 4 * C₀ + 8 + 8 * γ + 4 * B
  -- eventually `log N` exceeds what the projection costs
  obtain ⟨N₃, hN₃⟩ : ∃ N₃ : ℕ, ∀ N, N₃ ≤ N → γ + ε ≤ Real.log N ∧ 2 * K / ε ≤ Real.log N ∧
      3 ≤ Real.log N := by
    obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop |>.eventually_ge_atTop
        (max (γ + ε) (max (2 * K / ε) 3)))
    exact ⟨N₃, fun N hN => by
      have := hN₃ N hN
      simp only [Function.comp] at this
      exact ⟨(le_max_left _ _).trans this, ((le_max_left _ _).trans (le_max_right _ _)).trans this,
        ((le_max_right _ _).trans (le_max_right _ _)).trans this⟩⟩
  refine ⟨max N₁ (max N₂ N₃), fun N hN => ⟨fun x hx => hN₁ N (le_of_max_le_left hN) x hx, ?_⟩⟩
  have hN2 : N₂ ≤ N := (le_max_left _ _).trans (le_of_max_le_right hN)
  have hN3 : N₃ ≤ N := (le_max_right _ _).trans (le_of_max_le_right hN)
  obtain ⟨hLγ, hLK, hL3⟩ := hN₃ N hN3
  have hN1 : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    rw [this, Nat.cast_zero, Real.log_zero] at hL3
    linarith
  -- the pole, its harmonic mass and the Liouville sum
  set b := truncPole N
  set H := ∑ n ∈ Icc 1 N, (1 : ℝ) / n
  set S := ∑ n ∈ Icc 1 N, liouvilleSign n / n
  set L := Real.log N
  have hb2 : ∀ n ∈ Icc 1 N, b n ^ 2 = 1 / n := fun n hn => by
    simp only [b, truncPole, if_pos (mem_Icc.mp hn).2, poleVector_sq]
  have hbsq : ∑ n ∈ Icc 1 N, b n ^ 2 = H := sum_congr rfl hb2
  have hbs : ∀ n ∈ Icc 1 N, b n / Real.sqrt n = 1 / n := fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [b, truncPole, if_pos (mem_Icc.mp hn).2, poleVector]
    rw [div_div, Real.mul_self_sqrt hn0.le]
  have hHL : L ≤ H := by
    have h := log_add_one_le_harmonic N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    have : L ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log (by exact_mod_cast hN1) (by linarith)
    simp only [H, one_div]
    linarith
  have hH3 : 3 ≤ H := hL3.trans hHL
  have hH0 : 0 < H := by linarith
  have hS := abs_sum_liouvilleSign_div_le N
  have hS2 : S ^ 2 ≤ 4 := by
    rw [← sq_abs, show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact pow_le_pow_left₀ (abs_nonneg S) hS 2
  set s := S / H
  -- the witness: the twin's top projected onto the pole hyperplane
  set x : ℕ → ℝ := fun n => (liouvilleSign n - s) * b n
  have horth : ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 := by
    have : ∀ n ∈ Icc 1 N, x n / Real.sqrt n = liouvilleSign n / n - s * (1 / n) := fun n hn => by
      rw [show x n / Real.sqrt n = (liouvilleSign n - s) * (b n / Real.sqrt n) by
        simp only [x]; ring, hbs n hn]
      ring
    rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum]
    show S - s * H = 0
    rw [div_mul_cancel₀ S hH0.ne', sub_self]
  have hxsq : ∑ n ∈ Icc 1 N, x n ^ 2 = H - S ^ 2 / H := by
    have : ∀ n ∈ Icc 1 N, x n ^ 2 = 1 / n - 2 * s * (liouvilleSign n / n) + s ^ 2 * (1 / n) :=
      fun n hn => by
        have hl := liouvilleSign_mul_self n
        simp only [x]
        rw [mul_pow, hb2 n hn]
        have : (liouvilleSign n - s) ^ 2 = 1 - 2 * s * liouvilleSign n + s ^ 2 := by
          linear_combination hl
        rw [this]
        ring
    rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
    simp only [s]
    field_simp
    ring
  have hxpos : 0 < ∑ n ∈ Icc 1 N, x n ^ 2 := by
    rw [hxsq]
    have : S ^ 2 / H < H := by
      rw [div_lt_iff₀ hH0]
      have : (3 : ℝ) * 3 ≤ H * H := mul_le_mul hH3 hH3 (by norm_num) hH0.le
      linarith
    linarith
  refine ⟨x, horth, hxpos, ?_⟩
  -- the twin of the witness is the pole minus `s` times the twin's top
  set u : ℕ → ℝ := fun n => -s * (liouvilleSign n * b n)
  have hlx : (fun n => liouvilleSign n * x n) = fun n => b n + u n := by
    funext n
    have hl := liouvilleSign_mul_self n
    simp only [x, u]
    linear_combination b n * hl
  rw [hlx, atomicWeilForm_truncPole_add N u]
  -- the three pieces
  have hPb : (L - γ - ε / 2) * H ≤ atomicWeilForm N b := by
    have := hN₂ N hN2
    rwa [hbsq] at this
  have hlb2 : ∑ n ∈ Icc 1 N, (liouvilleSign n * b n) ^ 2 = H := by
    rw [← hbsq]
    exact sum_congr rfl fun n _ => by rw [mul_pow, show liouvilleSign n ^ 2 = 1 by
      rw [sq, liouvilleSign_mul_self], one_mul]
  have hPu : -(s ^ 2 * ((L + C₀) * H)) ≤ atomicWeilForm N u := by
    have hu : u = fun n => (-s) * (liouvilleSign n * b n) := rfl
    rw [hu, atomicWeilForm_smul, neg_sq]
    have hbot := fixedPoint_bottom_ge (κ := -1) (by norm_num) N (fun n => liouvilleSign n * b n)
    rw [hlb2] at hbot
    have e : ((-1 : ℝ) - 1 / -1) = 0 := by norm_num
    rw [e, zero_mul, zero_add] at hbot
    have : -((L + C₀) * H) ≤ atomicWeilForm N (fun n => liouvilleSign n * b n) := by
      simp only [L, C₀] at hbot ⊢; linarith
    have := mul_le_mul_of_nonneg_left this (sq_nonneg s)
    linarith
  have hcross : |∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * b n * u n| ≤
      |s| * ((L + γ) * 2 + B * H) := by
    have e : ∀ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * b n * u n =
        -s * ((L - γ) * (liouvilleSign n / n) +
          (mertensSum (N / n) + Real.log n - (L - γ)) * (liouvilleSign n * (1 / n))) := by
      intro n hn
      simp only [u]
      have : b n * b n = 1 / n := by rw [← sq, hb2 n hn]
      have : (mertensSum (N / n) + Real.log n) * b n * (-s * (liouvilleSign n * b n)) =
          -s * ((mertensSum (N / n) + Real.log n) * liouvilleSign n * (b n * b n)) := by ring
      rw [this, ‹b n * b n = 1 / n›]
      ring
    rw [sum_congr rfl e, ← mul_sum, abs_mul, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
    rw [sum_add_distrib, ← mul_sum]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      have : |L - γ| ≤ L + γ := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul this hS (abs_nonneg _) (by linarith)
    · refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [show B * H = ∑ n ∈ Icc 1 N, B * (1 / (n : ℝ)) by rw [← mul_sum]]
      refine sum_le_sum fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [abs_mul, abs_mul, abs_liouvilleSign, one_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
      exact mul_le_mul_of_nonneg_right (abs_row_sub_le hn) (by positivity)
  -- assemble
  have hs : |s| ≤ 2 / H := by
    rw [abs_div, abs_of_pos hH0]
    exact div_le_div_of_nonneg_right hS hH0.le
  have hs2 : s ^ 2 ≤ 4 / H ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right hS2 (by positivity)
  have hT1 : s ^ 2 * ((L + C₀) * H) ≤ 4 + 4 * C₀ := by
    calc s ^ 2 * ((L + C₀) * H) ≤ 4 / H ^ 2 * ((L + C₀) * H) :=
          mul_le_mul_of_nonneg_right hs2 (by positivity)
      _ = 4 * L / H + 4 * C₀ / H := by field_simp
      _ ≤ 4 + 4 * C₀ := by
          have h1 : 4 * L / H ≤ 4 := by rw [div_le_iff₀ hH0]; linarith
          have h2 : 4 * C₀ / H ≤ 4 * C₀ := div_le_self (by positivity) (by linarith)
          linarith
  have hT2 : 2 * (|s| * ((L + γ) * 2 + B * H)) ≤ 8 + 8 * γ + 4 * B := by
    calc 2 * (|s| * ((L + γ) * 2 + B * H)) ≤ 2 * (2 / H * ((L + γ) * 2 + B * H)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (by positivity)) (by norm_num)
      _ = 8 * L / H + 8 * γ / H + 4 * B := by field_simp; ring
      _ ≤ 8 + 8 * γ + 4 * B := by
          have h1 : 8 * L / H ≤ 8 := by rw [div_le_iff₀ hH0]; linarith
          have h2 : 8 * γ / H ≤ 8 * γ := div_le_self (by positivity) (by linarith)
          linarith
  have hεH : K ≤ ε / 2 * H := by
    have : 2 * K / ε ≤ H := hLK.trans hHL
    rw [div_le_iff₀ hε] at this
    linarith
  have hxH : ∑ n ∈ Icc 1 N, x n ^ 2 ≤ H := by
    rw [hxsq]
    have : 0 ≤ S ^ 2 / H := div_nonneg (sq_nonneg _) hH0.le
    linarith
  have hcoef : 0 ≤ L - γ - ε := by linarith
  have hcr := (abs_le.mp hcross).1
  calc (L - γ - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ (L - γ - ε) * H :=
        mul_le_mul_of_nonneg_left hxH hcoef
    _ ≤ atomicWeilForm N b + atomicWeilForm N u +
        2 * ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * b n * u n := by
        linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
