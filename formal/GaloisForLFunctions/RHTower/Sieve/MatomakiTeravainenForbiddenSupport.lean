import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAllIntervalTheorem
import GaloisForLFunctions.RHTower.RouteEForbiddenSupportStability

/-!
# Forbidden-support stability of the all-interval `E₃` theorem

Deleting the prime divisors of an adversarial `A ≤ x^B` from all three prime variables of the
Matomäki–Teräväinen all-interval `E₃` count keeps its order of magnitude.

* **The small prime.**  The deleted part `D₁` of `P₁` has `|D₁(1+it)| ≤ #S₁/P₁ ≪ L^{1-a}`, so by
  `(FS6)` the mixed mean square of `(P₁ - D₁)P` is at most twice that of `P₁P` plus
  `2|D₁|²∫|P|²`; the source mean square `∫_{-T}^{T}|P|² ≪ (1 + T/T₁)/L²` holds up to the Perron
  height through the sifted mean value theorem at the scale `Y^{100/99}`.  The Perron comparison
  therefore survives, and the long window keeps `20/21` of its harmonic mass.
* **The large primes and the cofactor.**  A large prime `q ∣ A` confines the remaining variable
  to a window of `≤ 2L + 1` integers, there are `≤ 3B` such primes, and the diagonal `n = p₂`
  carries `≤ L/2 + 1` integers per `p₁`; since `ρ⁻ ≤ 1_prime` on the cofactor windows and
  `|ρ⁻| ≤ 156`, all these deletions cost `≪_B (log x)^{O(1)}`.

The result (`eventually_mtCoprimeE3Sum_ge`): at `a = 11/10`, `h = √x (log x)^{1.55}`, the coprime
`E₃` sum is `≥ h/(40000 log P₁ (log x)²)`; in particular every interval `(x, x + h]` contains a
squarefree `E₃` number coprime to `A` (`eventually_exists_coprime_threePrime`).  The analytic
inputs of (5.2), the Deshouillers–Iwaniec and Watt bounds, enter as the hypotheses
`MTDeshouillersIwaniecBound` and `MTWattBound`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory Filter

noncomputable section

/-- **The source mean value up to height `Y^{100/99}`.**  The sifted mean value theorem at the
auxiliary scale `X = Y^{100/99}`: `∫_{-T}^{T}|P(1+it)|² ≤ C(T/(Y log Y) + (log Y)^{-2})` for
`1 ≤ T ≤ Y^{100/99}`, whenever `z > Y^{10/99}`, `2 ≤ z` and `4Y < z⁶`. -/
theorem exists_integral_normSq_LSeries_harmanSource_tall_le :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℝ, ∀ (z Q D E Y : ℕ), Y₀ ≤ Y → (Y : ℝ) ^ (10 / 99 : ℝ) < z →
      2 ≤ z → 4 * Y < z ^ 6 → ∀ T : ℝ, 1 ≤ T → T ≤ (Y : ℝ) ^ (100 / 99 : ℝ) →
        ∫ t in Set.Icc (-T) T, ‖LSeries (fun n => mtHarmanProposition22SourceAF z Q D E Y n)
            (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          C * (T / (Y * Real.log Y) + 1 / Real.log Y ^ 2) := by
  obtain ⟨C, hC, hev⟩ := eventually_integral_normSq_LSeries_rough_le
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨C, hC, max X₀ 3, fun z Q D E Y hY hz hz2 hz6 T hT hTY => ?_⟩
  have hY3 : (3 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hYX : (Y : ℝ) ≤ (Y : ℝ) ^ (100 / 99 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Y)
      (by norm_num : (1 : ℝ) ≤ 100 / 99)
    rwa [Real.rpow_one] at this
  have hXY : ((Y : ℝ) ^ (100 / 99 : ℝ)) ^ (99 / 100 : ℝ) = Y := by
    rw [← Real.rpow_mul hY0.le]; norm_num
  have hX₀X : X₀ ≤ (Y : ℝ) ^ (100 / 99 : ℝ) := le_trans (le_max_left _ _) (hY.trans hYX)
  have hz' : ((Y : ℝ) ^ (100 / 99 : ℝ)) ^ (1 / 10 : ℝ) < z := by
    rw [← Real.rpow_mul hY0.le]; norm_num; exact hz
  have hmain := hX₀ _ hX₀X _ z Y hz' (fun n hn => mtRealIntervalAF_scaleSupported _ _ _ hn)
    (fun n hn p hp hpz => harmanSource_rough (Q := Q) (D := D) (E := E) hn hp hpz)
    (norm_harmanSource_le hz2 hz6) hXY.le hYX T hT hTY
  refine hmain.trans ?_
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogXY : Real.log Y ≤ Real.log ((Y : ℝ) ^ (100 / 99 : ℝ)) := Real.log_le_log hY0 hYX
  have hT0 : 0 ≤ T := by linarith
  gcongr

/-- **(FS6) in affine form.**  Deleting from `P_{B₁}` the primes of `B₁` failing `q` perturbs the
one-sided mixed mean square by at most `2d²` times the source mean square, where `d` bounds the
deleted polynomial: from `16 L^{-(2+ε/10)}(1 + T/T₁)` to `64 L^{-(2+ε/10)}(1 + T/T₁)` as soon as
`d²K ≤ 16 L^{-(2+ε/10)}`. -/
theorem integral_normSq_filter_mul_le {B₁ : Finset ℕ} (q : ℕ → Prop) [DecidablePred q]
    (hB₁0 : 0 ∉ B₁) {F : ℝ → ℂ} (hFc : Continuous F) {T₀ T T₁ Λ d K : ℝ} (hT₀ : 0 ≤ T₀)
    (hT₀T : T₀ ≤ T)
    (hd : ∀ t : ℝ, ‖∑ p ∈ B₁.filter (fun p => ¬ q p),
      (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ≤ d)
    (hfull : ∫ t in Set.Icc T₀ T, ‖(∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
      F t‖ ^ 2 ≤ 16 * Λ * (1 + T / T₁))
    (hF : ∫ t in Set.Icc (-T) T, ‖F t‖ ^ 2 ≤ K * (1 + T / T₁))
    (hdK : d ^ 2 * K ≤ 16 * Λ) (hT₁ : 0 < T₁) :
    ∫ t in Set.Icc T₀ T, ‖(∑ p ∈ B₁.filter q,
      (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * F t‖ ^ 2 ≤
        64 * Λ * (1 + T / T₁) := by
  classical
  have hsplit : ∀ t : ℝ, ∑ p ∈ B₁.filter q, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) =
      (∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) -
        ∑ p ∈ B₁.filter (fun p => ¬ q p), (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) := by
    intro t
    rw [← Finset.sum_filter_add_sum_filter_not B₁ q]
    ring
  have hpt : ∀ t : ℝ, ‖(∑ p ∈ B₁.filter q, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
      F t‖ ^ 2 ≤ 2 * ‖(∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * F t‖ ^ 2 +
        2 * d ^ 2 * ‖F t‖ ^ 2 := fun t => by
    rw [hsplit t]; exact ForbiddenSupport.norm_sq_sub_mul_le (hd t)
  have huc : Continuous fun t : ℝ =>
      ∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) :=
    continuous_primeSetPoly B₁ hB₁0
  have hqc : Continuous fun t : ℝ =>
      ∑ p ∈ B₁.filter q, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) :=
    continuous_primeSetPoly _ fun h => hB₁0 (Finset.mem_filter.1 h).1
  have hq : 0 ≤ 1 + T / T₁ := by
    have : 0 ≤ T := hT₀.trans hT₀T
    positivity
  have hc1 : Continuous fun t : ℝ =>
      2 * ‖(∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * F t‖ ^ 2 :=
    continuous_const.mul ((huc.mul hFc).norm.pow 2)
  have hc2 : Continuous fun t : ℝ => 2 * d ^ 2 * ‖F t‖ ^ 2 :=
    continuous_const.mul (hFc.norm.pow 2)
  have hFsub : ∫ t in Set.Icc T₀ T, ‖F t‖ ^ 2 ≤ ∫ t in Set.Icc (-T) T, ‖F t‖ ^ 2 := by
    refine setIntegral_mono_set ?_ ?_ ?_
    · exact (hFc.norm.pow 2).integrableOn_Icc
    · exact Filter.Eventually.of_forall fun t => by positivity
    · exact (Set.Icc_subset_Icc (by linarith) le_rfl).eventuallyLE
  have hmono : ∫ t in Set.Icc T₀ T, ‖(∑ p ∈ B₁.filter q,
        (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * F t‖ ^ 2 ≤
      ∫ t in Set.Icc T₀ T, (2 * ‖(∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
        F t‖ ^ 2 + 2 * d ^ 2 * ‖F t‖ ^ 2) :=
    setIntegral_mono_on (((hqc.mul hFc).norm.pow 2).integrableOn_Icc)
      ((hc1.add hc2).integrableOn_Icc) measurableSet_Icc fun t _ => hpt t
  rw [integral_add (hc1.integrableOn_Icc (μ := volume)) (hc2.integrableOn_Icc (μ := volume)),
    integral_const_mul, integral_const_mul] at hmono
  refine hmono.trans ?_
  have h1 : 2 * ∫ t in Set.Icc T₀ T,
      ‖(∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * F t‖ ^ 2 ≤
        2 * (16 * Λ * (1 + T / T₁)) := by linarith
  have h2 : 2 * d ^ 2 * ∫ t in Set.Icc T₀ T, ‖F t‖ ^ 2 ≤ 2 * (16 * Λ * (1 + T / T₁)) := by
    have : d ^ 2 * ∫ t in Set.Icc T₀ T, ‖F t‖ ^ 2 ≤ d ^ 2 * (K * (1 + T / T₁)) :=
      mul_le_mul_of_nonneg_left (hFsub.trans hF) (sq_nonneg d)
    have h' : d ^ 2 * (K * (1 + T / T₁)) ≤ 16 * Λ * (1 + T / T₁) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hdK hq
    linarith
  linarith
/-! ### Windows -/

/-- Membership in a scaled natural window: `n ∈ (⌊x/d⌋, ⌊y/d⌋]` iff `x < dn ≤ y`. -/
theorem mem_Ioc_natFloor_div_iff {x y d : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hd : 0 < d) {n : ℕ} :
    n ∈ Finset.Ioc ⌊x / d⌋₊ ⌊y / d⌋₊ ↔ x < d * n ∧ d * n ≤ y := by
  rw [Finset.mem_Ioc, Nat.floor_lt (div_nonneg hx hd.le),
    Nat.le_floor_iff (div_nonneg (hx.trans hxy) hd.le), div_lt_iff₀ hd, le_div_iff₀ hd]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- A natural window `(⌊α⌋, ⌊β⌋]` carries at most `β - α + 1` integers. -/
theorem card_Ioc_natFloor_le {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    ((Finset.Ioc ⌊α⌋₊ ⌊β⌋₊).card : ℝ) ≤ β - α + 1 := by
  rw [Nat.card_Ioc]
  have hle : ⌊α⌋₊ ≤ ⌊β⌋₊ := Nat.floor_mono hαβ
  rw [Nat.cast_sub hle]
  have h1 : (⌊β⌋₊ : ℝ) ≤ β := Nat.floor_le (hα.trans hαβ)
  have h2 : α - 1 < (⌊α⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one α; linarith
  linarith

/-- A scaled natural window of length `y - x` carries at most `(y - x)/d + 1` integers. -/
theorem card_Ioc_natFloor_div_le {x y d : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hd : 0 < d) :
    ((Finset.Ioc ⌊x / d⌋₊ ⌊y / d⌋₊).card : ℝ) ≤ (y - x) / d + 1 := by
  have := card_Ioc_natFloor_le (div_nonneg hx hd.le) (div_le_div_of_nonneg_right hxy hd.le)
  have e : (y - x) / d = y / d - x / d := by ring
  linarith

/-- **Deleting bad large primes and bad cofactors.**  For weights `f ≤ 1_prime` with `|f| ≤ K` on
the windows, restricting `p₂` to `P` and the cofactor `n` to `G p₂` costs at most `K` times the
windows of the deleted `p₂`, plus the number of primes `n` failing `G p₂`. -/
theorem sum_sub_sum_filter_le {B₂ : Finset ℕ} {W : ℕ → Finset ℕ} {f : ℕ → ℝ} {K : ℝ}
    (P : ℕ → Prop) [DecidablePred P] (G : ℕ → ℕ → Prop) [∀ p, DecidablePred (G p)]
    (hfK : ∀ p ∈ B₂, ∀ n ∈ W p, |f n| ≤ K)
    (hf1 : ∀ p ∈ B₂, ∀ n ∈ W p, f n ≤ if n.Prime then 1 else 0) :
    ∑ p ∈ B₂, ∑ n ∈ W p, f n - ∑ p ∈ B₂.filter P, ∑ n ∈ (W p).filter (G p), f n ≤
      K * ∑ p ∈ B₂.filter (fun p => ¬ P p), ((W p).card : ℝ) +
        ∑ p ∈ B₂, (((W p).filter (fun n => n.Prime ∧ ¬ G p n)).card : ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not B₂ P]
  -- the deleted `p₂`
  have h1 : ∑ p ∈ B₂.filter (fun p => ¬ P p), ∑ n ∈ W p, f n ≤
      K * ∑ p ∈ B₂.filter (fun p => ¬ P p), ((W p).card : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpB := (Finset.mem_filter.1 hp).1
    calc ∑ n ∈ W p, f n ≤ ∑ _n ∈ W p, K :=
          Finset.sum_le_sum fun n hn => (le_abs_self _).trans (hfK p hpB n hn)
      _ = K * ((W p).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- the deleted cofactors
  have h2 : ∀ p ∈ B₂, ∑ n ∈ W p, f n - ∑ n ∈ (W p).filter (G p), f n ≤
      (((W p).filter (fun n => n.Prime ∧ ¬ G p n)).card : ℝ) := by
    intro p hp
    rw [← Finset.sum_filter_add_sum_filter_not (W p) (G p), add_sub_cancel_left]
    calc ∑ n ∈ (W p).filter (fun n => ¬ G p n), f n
        ≤ ∑ n ∈ (W p).filter (fun n => ¬ G p n), (if n.Prime then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun n hn => hf1 p hp n (Finset.mem_filter.1 hn).1
      _ = (((W p).filter (fun n => n.Prime ∧ ¬ G p n)).card : ℝ) := by
          rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
          congr 2
          ext n; simp [and_comm]
  have h3 : ∑ p ∈ B₂.filter P, (∑ n ∈ W p, f n - ∑ n ∈ (W p).filter (G p), f n) ≤
      ∑ p ∈ B₂, (((W p).filter (fun n => n.Prime ∧ ¬ G p n)).card : ℝ) := by
    calc ∑ p ∈ B₂.filter P, (∑ n ∈ W p, f n - ∑ n ∈ (W p).filter (G p), f n)
        ≤ ∑ p ∈ B₂.filter P, (((W p).filter (fun n => n.Prime ∧ ¬ G p n)).card : ℝ) :=
          Finset.sum_le_sum fun p hp => h2 p (Finset.mem_filter.1 hp).1
      _ ≤ ∑ p ∈ B₂, (((W p).filter (fun n => n.Prime ∧ ¬ G p n)).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => Nat.cast_nonneg _
  rw [Finset.sum_sub_distrib] at h3
  linarith

/-- The cofactor windows are symmetric in the two large variables:
`n ∈ W(p₁p₂)` iff `p₂ ∈ W(p₁n)`, both meaning `x < p₁p₂n ≤ x+h`. -/
theorem mem_window_comm {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {p₁ p₂ n : ℕ} (hp₁ : 0 < p₁)
    (hp₂ : 0 < p₂) (hn : 0 < n) :
    n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊ ↔
      p₂ ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * n)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * n)⌋₊ := by
  have h1 : (0 : ℝ) < (p₁ : ℝ) * p₂ := by positivity
  have h2 : (0 : ℝ) < (p₁ : ℝ) * n := by positivity
  rw [mem_Ioc_natFloor_div_iff hx (by linarith) h1, mem_Ioc_natFloor_div_iff hx (by linarith) h2]
  have e : (p₁ : ℝ) * p₂ * n = (p₁ : ℝ) * n * p₂ := by ring
  rw [e]

/-- **The bad prime cofactors are few.**  For a fixed `p₁`, the primes `n` in the windows
`W(p₂)`, `p₂ ∈ B₂`, that divide `A` or equal `p₂` number at most
`#{q ∣ A prime, q > R} (h/(p₁R) + 1) + h/(2√(xp₁)) + 1`, when every window element exceeds `R`. -/
theorem sum_card_badCofactor_le {B₂ : Finset ℕ} {A p₁ : ℕ} {x h R : ℝ} (hA : A ≠ 0)
    (hx : 0 < x) (hh : 0 ≤ h) (hp₁ : 0 < p₁) (hR : 0 < R) (hB₂ : ∀ p ∈ B₂, 0 < p)
    (hWR : ∀ p₂ ∈ B₂, ∀ n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊,
      R < n) :
    ∑ p₂ ∈ B₂, (((Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊).filter
        (fun n => n.Prime ∧ ¬ (Nat.Coprime n A ∧ n ≠ p₂))).card : ℝ) ≤
      ((A.primeFactors.filter (fun q : ℕ => R < (q : ℝ))).card : ℝ) * (h / (p₁ * R) + 1) +
        (h / (2 * Real.sqrt (x * p₁)) + 1) := by
  classical
  set W : ℕ → Finset ℕ := fun p₂ =>
    Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊ with hWdef
  set T := A.primeFactors.filter (fun q : ℕ => R < (q : ℝ)) with hTdef
  have hp₁R : (0 : ℝ) < p₁ := by exact_mod_cast hp₁
  -- split the bad primes
  have hsplit : ∀ p₂ ∈ B₂, (((W p₂).filter (fun n => n.Prime ∧ ¬ (Nat.Coprime n A ∧ n ≠ p₂))).card
      : ℝ) ≤ (((W p₂).filter (fun n => n ∈ T)).card : ℝ) +
        (((W p₂).filter (fun n => n = p₂)).card : ℝ) := by
    intro p₂ hp₂
    have hsub : (W p₂).filter (fun n => n.Prime ∧ ¬ (Nat.Coprime n A ∧ n ≠ p₂)) ⊆
        (W p₂).filter (fun n => n ∈ T) ∪ (W p₂).filter (fun n => n = p₂) := by
      intro n hn
      obtain ⟨hnW, hnp, hbad⟩ := Finset.mem_filter.1 hn
      rw [not_and_or, not_not] at hbad
      rcases hbad with hcop | heq
      · refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hnW, ?_⟩)
        have hdvd : n ∣ A := by
          by_contra hnd
          exact hcop ((Nat.Prime.coprime_iff_not_dvd hnp).2 hnd)
        exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hnp, hdvd, hA⟩, hWR p₂ hp₂ n hnW⟩
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hnW, heq⟩)
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · -- divisors of `A`: swap the order of summation
    have hswap : ∑ p₂ ∈ B₂, (((W p₂).filter (fun n => n ∈ T)).card : ℝ) =
        ∑ q ∈ T, ((B₂.filter (fun p₂ => q ∈ W p₂)).card : ℝ) := by
      have e1 : ∀ p₂, ((W p₂).filter (fun n => n ∈ T)).card = (T.filter (fun q => q ∈ W p₂)).card :=
        fun p₂ => by rw [Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Finset.inter_comm]
      simp only [e1, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_comm
    rw [hswap]
    have hq : ∀ q ∈ T, ((B₂.filter (fun p₂ => q ∈ W p₂)).card : ℝ) ≤ h / (p₁ * R) + 1 := by
      intro q hq
      obtain ⟨hqA, hqR⟩ := Finset.mem_filter.1 hq
      have hq0 : 0 < q := (Nat.prime_of_mem_primeFactors hqA).pos
      have hqR' : (0 : ℝ) < q := by exact_mod_cast hq0
      have hsub : B₂.filter (fun p₂ => q ∈ W p₂) ⊆
          Finset.Ioc ⌊x / ((p₁ : ℝ) * q)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * q)⌋₊ := by
        intro p₂ hp₂
        obtain ⟨hp₂B, hqW⟩ := Finset.mem_filter.1 hp₂
        exact (mem_window_comm hx.le hh hp₁ (hB₂ p₂ hp₂B) hq0).1 hqW
      calc ((B₂.filter (fun p₂ => q ∈ W p₂)).card : ℝ)
          ≤ ((Finset.Ioc ⌊x / ((p₁ : ℝ) * q)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * q)⌋₊).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ (x + h - x) / ((p₁ : ℝ) * q) + 1 :=
            card_Ioc_natFloor_div_le hx.le (by linarith) (by positivity)
        _ ≤ h / (p₁ * R) + 1 := by
            rw [add_sub_cancel_left]
            gcongr
    calc ∑ q ∈ T, ((B₂.filter (fun p₂ => q ∈ W p₂)).card : ℝ)
        ≤ ∑ _q ∈ T, (h / (p₁ * R) + 1) := Finset.sum_le_sum hq
      _ = (T.card : ℝ) * (h / (p₁ * R) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
  · -- the diagonal `n = p₂`
    have hdiag : ∀ p₂ ∈ B₂, (((W p₂).filter (fun n => n = p₂)).card : ℝ) =
        (if p₂ ∈ W p₂ then 1 else 0) := by
      intro p₂ _
      rw [Finset.filter_eq']
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hdiag, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : B₂.filter (fun p₂ => p₂ ∈ W p₂) ⊆
        Finset.Ioc ⌊Real.sqrt (x / p₁)⌋₊ ⌊Real.sqrt ((x + h) / p₁)⌋₊ := by
      intro p₂ hp₂
      obtain ⟨hp₂B, hW⟩ := Finset.mem_filter.1 hp₂
      have hp₂0 : (0 : ℝ) < p₂ := by exact_mod_cast hB₂ p₂ hp₂B
      obtain ⟨h1, h2⟩ := (mem_Ioc_natFloor_div_iff hx.le (by linarith)
        (by positivity : (0 : ℝ) < (p₁ : ℝ) * p₂)).1 hW
      rw [Finset.mem_Ioc, Nat.floor_lt (Real.sqrt_nonneg _), Nat.le_floor_iff (Real.sqrt_nonneg _)]
      constructor
      · rw [Real.sqrt_lt' hp₂0, div_lt_iff₀ hp₁R]; nlinarith
      · rw [Real.le_sqrt hp₂0.le (by positivity), le_div_iff₀ hp₁R]; nlinarith
    have hmono : Real.sqrt (x / p₁) ≤ Real.sqrt ((x + h) / p₁) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hp₁R.le)
    have hcard := card_Ioc_natFloor_le (Real.sqrt_nonneg _) hmono
    have hstep : Real.sqrt ((x + h) / p₁) - Real.sqrt (x / p₁) ≤ h / (2 * Real.sqrt (x * p₁)) := by
      have h1 := ForbiddenSupport.sqrt_add_sub_sqrt_le (x := x / p₁) (h := h / p₁) (by positivity)
        (by positivity)
      rw [show x / p₁ + h / p₁ = (x + h) / p₁ by ring] at h1
      refine h1.trans (le_of_eq ?_)
      rw [Real.sqrt_div' x hp₁R.le, Real.sqrt_mul hx.le]
      have : 0 < Real.sqrt (p₁ : ℝ) := Real.sqrt_pos.2 hp₁R
      have hs : Real.sqrt (p₁ : ℝ) * Real.sqrt (p₁ : ℝ) = p₁ := Real.mul_self_sqrt hp₁R.le
      field_simp
      nlinarith [hs]
    calc (((B₂.filter (fun p₂ => p₂ ∈ W p₂)).card : ℕ) : ℝ)
        ≤ ((Finset.Ioc ⌊Real.sqrt (x / p₁)⌋₊ ⌊Real.sqrt ((x + h) / p₁)⌋₊).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ h / (2 * Real.sqrt (x * p₁)) + 1 := by linarith
/-! ### The deleted support -/

/-- The long-window sum over any subsets of the prime ranges, from the pair bounds. -/
theorem mtAllIntervalSumOn_ge_of_pairs {B₁ B₂ : Finset ℕ} {z Q D E : ℕ} {x h₁ L : ℝ}
    (hB₁ : ∀ p ∈ B₁, 0 < p) (hB₂ : ∀ p ∈ B₂, 0 < p)
    (hpair : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂, 1 / 250 * (h₁ / ((p₁ * p₂ : ℕ) : ℝ)) / L ≤
      ∑ n ∈ Finset.Ioc ⌊x / (p₁ * p₂)⌋₊ ⌊(x + h₁) / (p₁ * p₂)⌋₊, (rhoMinus z Q D E n : ℝ)) :
    1 / 250 * (h₁ / L) * ((∑ p ∈ B₁, 1 / (p : ℝ)) * ∑ p ∈ B₂, 1 / (p : ℝ)) ≤
      mtAllIntervalSumOn B₁ B₂ z Q D E x h₁ := by
  unfold mtAllIntervalSumOn
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p₁ hp₁ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun p₂ hp₂ => ?_)
  refine le_trans (le_of_eq ?_) (hpair p₁ hp₁ p₂ hp₂)
  have h1 : (0 : ℝ) < p₁ := by exact_mod_cast hB₁ p₁ hp₁
  have h2 : (0 : ℝ) < p₂ := by exact_mod_cast hB₂ p₂ hp₂
  push_cast
  field_simp

/-- The primes of `B` failing to be coprime to `A`, all at least `T > 1`, number at most
`log A / log T`. -/
theorem card_filter_not_coprime_le {B : Finset ℕ} {A : ℕ} (hA : A ≠ 0) {T : ℝ} (hT : 1 < T)
    (hB : ∀ p ∈ B, p.Prime ∧ T ≤ (p : ℝ)) :
    ((B.filter (fun p => ¬ Nat.Coprime p A)).card : ℝ) ≤ Real.log A / Real.log T := by
  classical
  refine ForbiddenSupport.card_le_log_div_log hA ?_ hT fun p hp => (hB p (Finset.mem_filter.1 hp).1).2
  intro p hp
  obtain ⟨hpB, hcop⟩ := Finset.mem_filter.1 hp
  have hpp := (hB p hpB).1
  exact Nat.mem_primeFactors.2 ⟨hpp, by
    by_contra hnd; exact hcop ((Nat.Prime.coprime_iff_not_dvd hpp).2 hnd), hA⟩

/-- The deleted prime polynomial is uniformly at most `#S/T` on the line `σ = 1`. -/
theorem norm_primeSetPoly_le_card_div {S : Finset ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hS : ∀ p ∈ S, T ≤ (p : ℝ)) (t : ℝ) :
    ‖∑ p ∈ S, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ≤ (S.card : ℝ) / T := by
  have h := ForbiddenSupport.norm_supportSum_le_card_div hT hS
    (s := ((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) (by simp)
  simpa [Complex.ofReal_natCast] using h

/-- The harmonic mass of the coprime part: `∑_{B, (p,A)=1} 1/p ≥ ∑_B 1/p - #S/T` when the deleted
primes are at least `T > 0`. -/
theorem sum_inv_filter_coprime_ge {B : Finset ℕ} {A : ℕ} {T : ℝ} (hT : 0 < T)
    (hB : ∀ p ∈ B, T ≤ (p : ℝ)) :
    (∑ p ∈ B, 1 / (p : ℝ)) - ((B.filter (fun p => ¬ Nat.Coprime p A)).card : ℝ) / T ≤
      ∑ p ∈ B.filter (fun p => Nat.Coprime p A), 1 / (p : ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not B (fun p => Nat.Coprime p A)]
  have h : ∑ p ∈ B.filter (fun p => ¬ Nat.Coprime p A), 1 / (p : ℝ) ≤
      ((B.filter (fun p => ¬ Nat.Coprime p A)).card : ℝ) / T := by
    calc ∑ p ∈ B.filter (fun p => ¬ Nat.Coprime p A), 1 / (p : ℝ)
        ≤ ∑ _p ∈ B.filter (fun p => ¬ Nat.Coprime p A), 1 / T :=
          Finset.sum_le_sum fun p hp =>
            one_div_le_one_div_of_le hT (hB p (Finset.mem_filter.1 hp).1)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  linarith

/-- **The deleted-support comparison at one `x`.**  Deleting from the small primes those dividing
`A ≤ x^B` keeps the short/long comparison of the all-interval theorem: the perturbed mean square
of `(P₁ - D₁)P` is at most `64 L^{-(2+ε/10)}(1 + T/T₁)` by `(FS6)`, since `|D₁| ≤ #S₁/P₁ ≪ L^{1-a}`
and the source mean square is `≪ (1 + T/T₁)/L²` up to the Perron height. -/
theorem mt_forbidden_compare_small {x L a c C₂ C_F ε B P₁ R₀ Y₀ : ℝ} {z Q D E A : ℕ}
    (hx : 0 < x) (hL : L = Real.log x) (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) (hP : P₁ = L ^ a)
    (hc : 0 < c) (hC₂ : 0 < C₂) (hCF : 0 < C_F) (hε0 : 0 < ε) (hε10 : ε ≤ 10) (hB : 0 < B)
    (hL16 : 16 ≤ L)
    (hLf2 : (11 + 96 * Real.log L) * Real.log L * 1296000 * Real.sqrt (4 * C₂) ≤ L ^ (ε / 20))
    (hLf3 : 26000 * Real.exp (-(c / 16) * Real.sqrt L) * (108000 * Real.log L * L ^ 2) ≤ 1)
    (hLf4 : 124800 * 108000 * Real.log L ≤ L ^ 3)
    (hLf5 : Real.exp (-(c / 8) * Real.sqrt L) ≤ 1 / 2) (hLc : c ^ 2 / 4 ≤ L)
    (h64 : 64 * L ^ 2 ≤ x) (hL2x : L ^ 2 ≤ x ^ (1 / 4 : ℝ)) (hLε : 4 * L ^ 2 ≤ x ^ (ε / 200))
    (hL6 : 2 * L ≤ x ^ (1 / 6 : ℝ)) (hL10 : 4 * L ^ 10 ≤ x ^ (1 / 600 : ℝ))
    (hsx1 : 1 ≤ Real.sqrt x) (hRx : max R₀ 1 ^ 3 ≤ x) (hYx : max Y₀ 1 ^ 3 ≤ x)
    (hdsmall : 9 * C_F * B ^ 2 ≤ 16 * L ^ (2 * a - 2 - ε / 10))
    (hz2 : 2 ≤ z) (hz6 : 4 * Real.sqrt (x * P₁) < (z : ℝ) ^ 6)
    (hA1 : 1 ≤ A) (hAB : (A : ℝ) ≤ x ^ B)
    (h52 : ∀ (P : ℝ) (B : Finset ℕ), Real.log (Real.sqrt (x * P₁)) ^ a ≤ P →
      P ≤ 3 * Real.log (Real.sqrt (x * P₁)) ^ (11 / 10 : ℝ) →
      (∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ Y : ℕ, Real.sqrt (x * P₁) ^ (1 - ε / 100) < Y → (Y : ℝ) ≤ Real.sqrt (x * P₁) / 2 →
      Real.sqrt (x * P₁) ≤ 2 * P * Y → ∀ T : ℝ, 1 ≤ T →
        ∫ t in Set.Icc (Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2))) T,
            ‖(∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
              LSeries (fun n => mtHarmanProposition22SourceAF z Q D E Y n)
                (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          2 * Real.log (Real.sqrt (x * P₁)) ^ (-(2 + ε / 10)) +
            2 * Real.log (Real.sqrt (x * P₁)) ^ (-(1 + ε / 10)) * P * T / Real.sqrt (x * P₁))
    (hP2 : ∀ R' : ℝ, R₀ ≤ R' → ∀ T : ℝ, 1 ≤ T → T ≤ R' ^ (201 / 200 : ℝ) →
      ∫ t in Set.Icc (-T) T,
          ‖∑ p ∈ (Finset.Ioc ⌊R'⌋₊ ⌊2 * R'⌋₊).filter Nat.Prime,
            (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ^ 2 ≤
        C₂ * (T / (R' * Real.log R') + 1 / Real.log R' ^ 2))
    (hFt : ∀ Y : ℕ, Y₀ ≤ Y → (Y : ℝ) ^ (10 / 99 : ℝ) < z → 4 * Y < z ^ 6 → ∀ T : ℝ, 1 ≤ T →
      T ≤ (Y : ℝ) ^ (100 / 99 : ℝ) →
        ∫ t in Set.Icc (-T) T, ‖LSeries (fun n => mtHarmanProposition22SourceAF z Q D E Y n)
            (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          C_F * (T / (Y * Real.log Y) + 1 / Real.log Y ^ 2)) :
    |mtAllIntervalSumOn (((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime).filter
          (fun p => Nat.Coprime p A)) ((Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊
          ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime) z Q D E x (Real.sqrt (x * P₁) * L) -
        (((⌊x + Real.sqrt (x * P₁) * L⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) /
          ((⌊x + x * Real.exp (-(c / 8) * Real.sqrt L)⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) *
          mtAllIntervalSumOn (((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime).filter
            (fun p => Nat.Coprime p A)) ((Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊
            ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime) z Q D E x
            (x * Real.exp (-(c / 8) * Real.sqrt L))|
      ≤ 3 * (Real.sqrt (x * P₁) * L / (108000 * Real.log L * L ^ 2)) := by
  classical
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨hP2', hPL2, -, hsX, hXle, hXsq, hlogXlo, hlogXhi, hXP⟩ :=
    mt_all_interval_scale_X hx hL hL16 ha1 ha11 hP rfl h64
  have hP0 : 0 < P₁ := by linarith
  obtain ⟨hRX, hRge, hx13, -⟩ := mt_all_interval_scale_R hx hL hL1 hP0 hPL2 rfl rfl hL6
  have hlogX0 : 0 ≤ Real.log (Real.sqrt (x * P₁)) := by linarith
  obtain ⟨-, hT₁le, -, hT₁L, -, -, -, hT₀1, -, -⟩ :=
    mt_all_interval_scale_h (T₀ := Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2)))
      hx hL hL1 hc hLc hsX hXle hXsq hlogX0 hlogXhi hRX hsx1 hL2x hLf5 rfl
  obtain ⟨hY1, -, hYX2, hYX3⟩ := mt_all_interval_scale_Y hε0 hP2' hPL2 hL1 hx hXP hsX hLε
  obtain ⟨-, -, hJ9⟩ := ceil_twelve_log_facts hL1
  have hX0 : 0 < Real.sqrt (x * P₁) := by linarith
  have hT₁0 : 0 < x / (Real.sqrt (x * P₁) * L) := by positivity
  set Y := ⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1 with hYdef
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY1
  -- `R ≤ Y`, so `Y ≥ x^{1/3}`
  have hRY : Real.sqrt (x / P₁) / 2 ≤ Y := by
    have hR : Real.sqrt (x / P₁) / 2 = Real.sqrt (x * P₁) / (2 * P₁) := by
      have : Real.sqrt (x / P₁) / 2 * Real.sqrt (x * P₁) = Real.sqrt (x * P₁) / (2 * P₁) *
          Real.sqrt (x * P₁) := by
        rw [hRX, div_mul_eq_mul_div, ← sq, hXsq]; field_simp
      exact mul_right_cancel₀ hX0.ne' this
    rw [hR, div_le_iff₀ (by positivity)]; linarith
  have hYx13 : x ^ (1 / 3 : ℝ) ≤ Y := hx13.trans hRY
  have hlogY : L / 3 ≤ Real.log Y := by
    have := Real.log_le_log (by positivity) hYx13
    rwa [Real.log_rpow hx, ← hL, show 1 / 3 * L = L / 3 by ring] at this
  have hYY₀ : Y₀ ≤ Y := by
    have h1 : max Y₀ 1 ≤ x ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hYx (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at this
    linarith [le_max_left Y₀ 1]
  have hYz6 : (Y : ℝ) < (z : ℝ) ^ 6 := by linarith
  have hYz : 4 * Y < z ^ 6 := by
    have : ((4 * Y : ℕ) : ℝ) < ((z ^ 6 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hYz' : (Y : ℝ) ^ (10 / 99 : ℝ) < z := by
    have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg _
    have h1 : (Y : ℝ) ^ (1 / 6 : ℝ) < ((z : ℝ) ^ 6) ^ (1 / 6 : ℝ) :=
      Real.rpow_lt_rpow hY0.le hYz6 (by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz0, show ((6 : ℕ) : ℝ) * (1 / 6) = 1 by norm_num,
      Real.rpow_one] at h1
    have h2 : (Y : ℝ) ^ (10 / 99 : ℝ) ≤ (Y : ℝ) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hY1) (by norm_num)
    linarith
  have hheightY := mt_all_interval_height_le hx hL1 hT₁le hJ9 (hRge.trans hRY) hYx13 hL10
  have hYexp : (Y : ℝ) ^ (201 / 200 : ℝ) ≤ (Y : ℝ) ^ (100 / 99 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hY1) (by norm_num)
  -- the source mean square in affine form
  have hFa : ∀ T, 1 ≤ T → T ≤ x / (Real.sqrt (x * P₁) * L) * 2 ^ ⌈12 * Real.log L⌉₊ →
      ∫ t in Set.Icc (-T) T, ‖LSeries (fun n => mtHarmanProposition22SourceAF z Q D E Y n)
          (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
        9 * C_F / L ^ 2 * (1 + T / (x / (Real.sqrt (x * P₁) * L))) := by
    intro T hT hTJ
    refine (hFt Y hYY₀ hYz' hYz T hT ((hTJ.trans hheightY).trans hYexp)).trans ?_
    exact mt_meanSquare_affine_beta hCF.le hL0 hY0 hlogY hT₁0 (hT₁L.le.trans (by linarith))
      (by linarith)
  -- the deleted polynomial
  set S₁ := ((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime).filter (fun p => ¬ Nat.Coprime p A)
    with hS₁def
  have hA0 : A ≠ 0 := by omega
  have hP1 : 1 < P₁ := by linarith
  have hS₁card : (S₁.card : ℝ) ≤ Real.log A / Real.log P₁ :=
    card_filter_not_coprime_le hA0 hP1 fun p hp =>
      ⟨(Finset.mem_filter.1 hp).2, ((mem_primes_Ioc_floor_iff hP0.le).1 hp).2.1.le⟩
  have hPL : L ≤ P₁ := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 ha1
    rwa [Real.rpow_one, ← hP] at this
  have hlogP1 : 1 ≤ Real.log P₁ := by
    rw [Real.le_log_iff_exp_le hP0]
    have := Real.exp_one_lt_d9; linarith
  have hlogA : Real.log A ≤ B * L := by
    have h1 := Real.log_le_log (by exact_mod_cast (by omega : 0 < A)) hAB
    rwa [Real.log_rpow hx, ← hL] at h1
  have hd : ∀ t : ℝ, ‖∑ p ∈ S₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ≤
      B * L / P₁ := by
    intro t
    refine (norm_primeSetPoly_le_card_div hP1.le (fun p hp =>
      (((mem_primes_Ioc_floor_iff hP0.le).1 (Finset.mem_filter.1 hp).1).2.1).le) t).trans ?_
    rw [div_le_div_iff_of_pos_right hP0]
    calc (S₁.card : ℝ) ≤ Real.log A / Real.log P₁ := hS₁card
      _ ≤ Real.log A := div_le_self (Real.log_nonneg (by exact_mod_cast hA1)) hlogP1
      _ ≤ B * L := hlogA
  have hdK : (B * L / P₁) ^ 2 * (9 * C_F / L ^ 2) ≤ 16 * L ^ (-(2 + ε / 10)) := by
    have hPa : P₁ ^ 2 = L ^ (2 * a) := by
      rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; push_cast; ring_nf
    have e : (B * L / P₁) ^ 2 * (9 * C_F / L ^ 2) = 9 * C_F * B ^ 2 * L ^ (-(2 * a)) := by
      rw [div_pow, hPa, Real.rpow_neg hL0.le]; field_simp
    have e2 : L ^ (2 * a - 2 - ε / 10) * L ^ (-(2 * a)) = L ^ (-(2 + ε / 10)) := by
      rw [← Real.rpow_add hL0]; ring_nf
    rw [e]
    calc 9 * C_F * B ^ 2 * L ^ (-(2 * a)) ≤ 16 * L ^ (2 * a - 2 - ε / 10) * L ^ (-(2 * a)) :=
          mul_le_mul_of_nonneg_right hdsmall (by positivity)
      _ = 16 * L ^ (-(2 + ε / 10)) := by rw [mul_assoc, e2]
  have h16 := mt_all_interval_harman_affine (z := z) (Q := Q) (D := D) (E := E) hx hL ha1 ha11 hP
    hc hε0 hε10 hL16 hLf5 hLc h64 hL2x hLε hL6 hsx1 h52
  have hsupp : ∀ m, mtHarmanProposition22SourceAF z Q D E Y m ≠ 0 → m ∈ Finset.Icc 1 (4 * Y) := by
    intro m hm
    obtain ⟨hm0, -, hhi⟩ := mtRealIntervalAF_scaleSupported _ _ _ hm
    exact Finset.mem_Icc.2 ⟨hm0, by
      exact_mod_cast (show (m : ℝ) ≤ ((4 * Y : ℕ) : ℝ) by push_cast; exact hhi)⟩
  have hFc := continuous_LSeries_one_line_of_support hsupp
  have hB₁0 : 0 ∉ (Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime := by simp
  have hαB : ∀ T, Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2)) ≤ T →
      T ≤ x / (Real.sqrt (x * P₁) * L) * 2 ^ ⌈12 * Real.log L⌉₊ →
      ∫ t in Set.Icc (Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2))) T,
          ‖(∑ p ∈ ((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime).filter
              (fun p => Nat.Coprime p A), (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
            LSeries (fun n => mtHarmanProposition22SourceAF z Q D E Y n)
              (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
        64 * L ^ (-(2 + ε / 10)) * (1 + T / (x / (Real.sqrt (x * P₁) * L))) := by
    intro T hT hTJ
    exact integral_normSq_filter_mul_le (fun p => Nat.Coprime p A) hB₁0 hFc (Real.exp_pos _).le hT
      hd (h16 T hT) (hFa T (hT₀1.trans hT) hTJ) hdK hT₁0
  exact mt_all_interval_compare_small_on hx hL ha1 ha11 hP hc hC₂ hε0 hL16
    (fun p hp => (mem_primes_Ioc_floor_iff hP0.le).1 (Finset.mem_filter.1 hp).1) hLf2 hLf3 hLf4
    hLf5 hLc h64 hL2x hLε hL6 hL10 hsx1 hRx hz2 hz6 hαB hP2

/-- **The deleted-support long window.**  Deleting from the small primes those dividing `A` removes
harmonic mass at most `#S₁/P₁ ≤ log A/(P₁ log P₁)`; when `63 B L ≤ P₁` and `log A ≤ BL` this keeps
`20/21` of the reciprocal sum, so the long window keeps `h₁/(2250 ((21/20) log P₁) L²)`. -/
theorem mt_forbidden_long_ge {B₁ B₂ : Finset ℕ} {A z Q D E : ℕ} {x h₁ L P₁ B : ℝ}
    (hB₁ : ∀ p ∈ B₁, p.Prime ∧ P₁ < p) (hB₂ : ∀ p ∈ B₂, 0 < p) (hA : A ≠ 0) (hP₁ : 1 < P₁)
    (hL : 0 < L) (hlogP : 0 < Real.log P₁) (hh₁ : 0 ≤ h₁)
    (hpair : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂, 1 / 250 * (h₁ / ((p₁ * p₂ : ℕ) : ℝ)) / L ≤
      ∑ n ∈ Finset.Ioc ⌊x / (p₁ * p₂)⌋₊ ⌊(x + h₁) / (p₁ * p₂)⌋₊, (rhoMinus z Q D E n : ℝ))
    (hS₁ : 1 / (3 * Real.log P₁) ≤ ∑ p ∈ B₁, 1 / (p : ℝ))
    (hS₂ : 1 / (3 * L) ≤ ∑ p ∈ B₂, 1 / (p : ℝ))
    (hAB : Real.log A ≤ B * L) (h63 : 63 * B * L ≤ P₁) :
    h₁ / (2250 * (21 / 20 * Real.log P₁) * L ^ 2) ≤
      mtAllIntervalSumOn (B₁.filter (fun p => Nat.Coprime p A)) B₂ z Q D E x h₁ := by
  classical
  have hP0 : 0 < P₁ := by linarith
  have hcard : ((B₁.filter (fun p => ¬ Nat.Coprime p A)).card : ℝ) / P₁ ≤ 1 / (63 * Real.log P₁) := by
    have h1 := card_filter_not_coprime_le (B := B₁) hA hP₁ fun p hp =>
      ⟨(hB₁ p hp).1, (hB₁ p hp).2.le⟩
    rw [div_le_div_iff₀ hP0 (by positivity)]
    calc ((B₁.filter (fun p => ¬ Nat.Coprime p A)).card : ℝ) * (63 * Real.log P₁)
        ≤ Real.log A / Real.log P₁ * (63 * Real.log P₁) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 63 * Real.log A := by field_simp
      _ ≤ 63 * (B * L) := by linarith
      _ ≤ 1 * P₁ := by linarith
  have hsum : 20 / (63 * Real.log P₁) ≤
      ∑ p ∈ B₁.filter (fun p => Nat.Coprime p A), 1 / (p : ℝ) := by
    have h := sum_inv_filter_coprime_ge (B := B₁) (A := A) hP0 fun p hp => (hB₁ p hp).2.le
    have e : 20 / (63 * Real.log P₁) = 1 / (3 * Real.log P₁) - 1 / (63 * Real.log P₁) := by
      field_simp; ring
    linarith
  have hlong := mtAllIntervalSumOn_ge_of_pairs (B₁ := B₁.filter (fun p => Nat.Coprime p A))
    (B₂ := B₂) (z := z) (Q := Q) (D := D) (E := E) (x := x) (h₁ := h₁) (L := L)
    (fun p hp => (hB₁ p (Finset.mem_filter.1 hp).1).1.pos) hB₂
    (fun p₁ hp₁ p₂ hp₂ => hpair p₁ (Finset.mem_filter.1 hp₁).1 p₂ hp₂)
  refine le_trans ?_ hlong
  have hprod : 20 / (63 * Real.log P₁) * (1 / (3 * L)) ≤
      (∑ p ∈ B₁.filter (fun p => Nat.Coprime p A), 1 / (p : ℝ)) * ∑ p ∈ B₂, 1 / (p : ℝ) :=
    mul_le_mul hsum hS₂ (by positivity) ((by positivity : (0 : ℝ) ≤ _).trans hsum)
  calc h₁ / (2250 * (21 / 20 * Real.log P₁) * L ^ 2)
      = 1 / 250 * (h₁ / L) * (20 / (63 * Real.log P₁) * (1 / (3 * L))) := by
        field_simp; ring
    _ ≤ 1 / 250 * (h₁ / L) * ((∑ p ∈ B₁.filter (fun p => Nat.Coprime p A), 1 / (p : ℝ)) *
          ∑ p ∈ B₂, 1 / (p : ℝ)) := mul_le_mul_of_nonneg_left hprod (by positivity)

/-- The Harman parameters at scale `X ≥ 1`: `z, D ≤ Q`, `2√X ≤ Q ≤ 2√X + 1`. -/
theorem mtProposition22_parameters_le {X ε : ℝ} (hX : 1 ≤ X) (hε : 0 < ε) :
    mtProposition22ZNat X ≤ mtProposition22QNat X ∧ mtProposition22DNat X ε ≤ mtProposition22QNat X ∧
      2 * Real.sqrt X ≤ (mtProposition22QNat X : ℝ) ∧
      (mtProposition22QNat X : ℝ) ≤ 2 * Real.sqrt X + 1 := by
  have hs : X ^ (1 / 2 : ℝ) = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mtProposition22ZNat mtProposition22QNat mtProposition22ZReal mtProposition22QReal
    refine Nat.ceil_mono ?_
    have : X ^ (2 / 11 : ℝ) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    have h0 : 0 ≤ X ^ (1 / 2 : ℝ) := by positivity
    linarith
  · unfold mtProposition22DNat mtProposition22QNat mtProposition22DReal mtProposition22QReal
    refine Nat.ceil_mono ?_
    have : X ^ (1 / 4 - 2 * ε) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    have h0 : 0 ≤ X ^ (1 / 2 : ℝ) := by positivity
    linarith
  · have := Nat.le_ceil (mtProposition22QReal X)
    unfold mtProposition22QNat mtProposition22QReal at *; rw [hs] at this ⊢; exact this
  · have := (Nat.ceil_lt_add_one (by unfold mtProposition22QReal; positivity :
      (0 : ℝ) ≤ mtProposition22QReal X)).le
    unfold mtProposition22QNat mtProposition22QReal at *; rw [hs] at this ⊢; exact this

/-- The coprime `E₃` window sum: `∑_{p₁ ∈ B₁} ∑_{p₂ ∈ B₂, (p₂,A)=1} ∑ ρ⁻(n)` over the cofactors
`x < p₁p₂n ≤ x+h` with `(n, A) = 1` and `n ≠ p₂`. -/
def mtCoprimeE3Sum (B₁ B₂ : Finset ℕ) (A z Q D E : ℕ) (x h : ℝ) : ℝ :=
  ∑ p₁ ∈ B₁, ∑ p₂ ∈ B₂.filter (fun p => Nat.Coprime p A),
    ∑ n ∈ (Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊).filter
      (fun n => Nat.Coprime n A ∧ n ≠ p₂), (rhoMinus z Q D E n : ℝ)

/-- **The deletions at one `x`.**  Restricting the large primes to those coprime to `A` and the
cofactor to integers coprime to `A` and distinct from `p₂` changes the `E₃` window sum over
`B₁ × B₂` by at most `#B₁ (157 K + 1) W`, when every window has at most `W` integers, at most `K`
primes of `B₂` and at most `K` prime divisors of `A` above `R` exist, the cofactor windows lie
above `R`, and the weights satisfy `|ρ⁻| ≤ 156`, `ρ⁻ ≤ 1_prime`. -/
theorem mtAllIntervalSumOn_sub_delete_le {B₁ B₂ : Finset ℕ} {A z Q D E : ℕ} {x h R Wm K : ℝ}
    (hA : A ≠ 0) (hx : 0 < x) (hh : 0 ≤ h) (hR : 0 < R) (hB₁ : ∀ p ∈ B₁, 0 < p)
    (hB₂ : ∀ p ∈ B₂, 0 < p)
    (hWR : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂,
      ∀ n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊, R < n)
    (hρK : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂,
      ∀ n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊,
        |(rhoMinus z Q D E n : ℝ)| ≤ 156)
    (hρ1 : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂,
      ∀ n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊,
        (rhoMinus z Q D E n : ℝ) ≤ if n.Prime then 1 else 0)
    (hWm : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂,
      ((Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊).card : ℝ) ≤ Wm)
    (hK₂ : ((B₂.filter (fun p => ¬ Nat.Coprime p A)).card : ℝ) ≤ K)
    (hKT : ((A.primeFactors.filter (fun q : ℕ => R < (q : ℝ))).card : ℝ) ≤ K)
    (hsmall : ∀ p₁ ∈ B₁, h / (p₁ * R) + 1 ≤ Wm)
    (hdiag : ∀ p₁ ∈ B₁, h / (2 * Real.sqrt (x * p₁)) + 1 ≤ Wm) (hK0 : 0 ≤ K) :
    mtAllIntervalSumOn B₁ B₂ z Q D E x h - mtCoprimeE3Sum B₁ B₂ A z Q D E x h ≤
      (B₁.card : ℝ) * ((157 * K + 1) * Wm) := by
  classical
  unfold mtAllIntervalSumOn mtCoprimeE3Sum
  rw [← Finset.sum_sub_distrib]
  have hper : ∀ p₁ ∈ B₁,
      ∑ p₂ ∈ B₂, ∑ n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊,
          (rhoMinus z Q D E n : ℝ) -
        ∑ p₂ ∈ B₂.filter (fun p => Nat.Coprime p A),
          ∑ n ∈ (Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊).filter
            (fun n => Nat.Coprime n A ∧ n ≠ p₂), (rhoMinus z Q D E n : ℝ) ≤
      (157 * K + 1) * Wm := by
    intro p₁ hp₁
    have hstep := sum_sub_sum_filter_le (B₂ := B₂)
      (W := fun p₂ => Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊)
      (f := fun n => (rhoMinus z Q D E n : ℝ)) (K := 156) (fun p => Nat.Coprime p A)
      (fun p₂ n => Nat.Coprime n A ∧ n ≠ p₂) (hρK p₁ hp₁) (hρ1 p₁ hp₁)
    refine hstep.trans ?_
    have hbad := sum_card_badCofactor_le (B₂ := B₂) (A := A) (p₁ := p₁) hA hx hh (hB₁ p₁ hp₁) hR
      hB₂ (hWR p₁ hp₁)
    have hWm0 : 0 ≤ Wm := le_trans (by positivity) (hsmall p₁ hp₁)
    have h1 : 156 * ∑ p ∈ B₂.filter (fun p => ¬ Nat.Coprime p A),
        ((Finset.Ioc ⌊x / ((p₁ : ℝ) * p)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p)⌋₊).card : ℝ) ≤
          156 * (K * Wm) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc ∑ p ∈ B₂.filter (fun p => ¬ Nat.Coprime p A),
            ((Finset.Ioc ⌊x / ((p₁ : ℝ) * p)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p)⌋₊).card : ℝ)
          ≤ ∑ _p ∈ B₂.filter (fun p => ¬ Nat.Coprime p A), Wm :=
            Finset.sum_le_sum fun p hp => hWm p₁ hp₁ p (Finset.mem_filter.1 hp).1
        _ = ((B₂.filter (fun p => ¬ Nat.Coprime p A)).card : ℝ) * Wm := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ K * Wm := mul_le_mul_of_nonneg_right hK₂ hWm0
    have h2 : ((A.primeFactors.filter (fun q : ℕ => R < (q : ℝ))).card : ℝ) *
        (h / (p₁ * R) + 1) + (h / (2 * Real.sqrt (x * p₁)) + 1) ≤ K * Wm + Wm := by
      have := mul_le_mul hKT (hsmall p₁ hp₁) (by positivity) hK0
      linarith [hdiag p₁ hp₁]
    linarith
  calc ∑ p₁ ∈ B₁, (∑ p₂ ∈ B₂, ∑ n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊
          ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊, (rhoMinus z Q D E n : ℝ) -
        ∑ p₂ ∈ B₂.filter (fun p => Nat.Coprime p A),
          ∑ n ∈ (Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊).filter
            (fun n => Nat.Coprime n A ∧ n ≠ p₂), (rhoMinus z Q D E n : ℝ))
      ≤ ∑ _p₁ ∈ B₁, (157 * K + 1) * Wm := Finset.sum_le_sum hper
    _ = (B₁.card : ℝ) * ((157 * K + 1) * Wm) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The deleted-support short window at one `x`.**  With the small primes dividing `A` deleted,
the short window `h = XL` still carries `h/(18000 ((21/20) log P₁) L²)`: the perturbed comparison
plus the perturbed long window, which keeps `20/21` of its harmonic mass. -/
theorem mt_forbidden_short_ge {x L a c C₂ C_F ε B P₁ R₀ Y₀ : ℝ} {z Q D E A : ℕ}
    (hx : 0 < x) (hL : L = Real.log x) (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) (hP : P₁ = L ^ a)
    (hc : 0 < c) (hC₂ : 0 < C₂) (hCF : 0 < C_F) (hε0 : 0 < ε) (hε10 : ε ≤ 10) (hB : 0 < B)
    (hL16 : 16 ≤ L)
    (hLf2 : (11 + 96 * Real.log L) * Real.log L * 1296000 * Real.sqrt (4 * C₂) ≤ L ^ (ε / 20))
    (hLf3 : 26000 * Real.exp (-(c / 16) * Real.sqrt L) * (108000 * Real.log L * L ^ 2) ≤ 1)
    (hLf4 : 124800 * 108000 * Real.log L ≤ L ^ 3)
    (hLf5 : Real.exp (-(c / 8) * Real.sqrt L) ≤ 1 / 2) (hLc : c ^ 2 / 4 ≤ L)
    (h64 : 64 * L ^ 2 ≤ x) (hL2x : L ^ 2 ≤ x ^ (1 / 4 : ℝ)) (hLε : 4 * L ^ 2 ≤ x ^ (ε / 200))
    (hL6 : 2 * L ≤ x ^ (1 / 6 : ℝ)) (hL10 : 4 * L ^ 10 ≤ x ^ (1 / 600 : ℝ))
    (hsx1 : 1 ≤ Real.sqrt x) (hRx : max R₀ 1 ^ 3 ≤ x) (hYx : max Y₀ 1 ^ 3 ≤ x)
    (hdsmall : 9 * C_F * B ^ 2 ≤ 16 * L ^ (2 * a - 2 - ε / 10))
    (hz2 : 2 ≤ z) (hz6 : 4 * Real.sqrt (x * P₁) < (z : ℝ) ^ 6)
    (hA1 : 1 ≤ A) (hAB : (A : ℝ) ≤ x ^ B)
    (h52 : ∀ (P : ℝ) (B : Finset ℕ), Real.log (Real.sqrt (x * P₁)) ^ a ≤ P →
      P ≤ 3 * Real.log (Real.sqrt (x * P₁)) ^ (11 / 10 : ℝ) →
      (∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ Y : ℕ, Real.sqrt (x * P₁) ^ (1 - ε / 100) < Y → (Y : ℝ) ≤ Real.sqrt (x * P₁) / 2 →
      Real.sqrt (x * P₁) ≤ 2 * P * Y → ∀ T : ℝ, 1 ≤ T →
        ∫ t in Set.Icc (Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2))) T,
            ‖(∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
              LSeries (fun n => mtHarmanProposition22SourceAF z Q D E Y n)
                (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          2 * Real.log (Real.sqrt (x * P₁)) ^ (-(2 + ε / 10)) +
            2 * Real.log (Real.sqrt (x * P₁)) ^ (-(1 + ε / 10)) * P * T / Real.sqrt (x * P₁))
    (hP2 : ∀ R' : ℝ, R₀ ≤ R' → ∀ T : ℝ, 1 ≤ T → T ≤ R' ^ (201 / 200 : ℝ) →
      ∫ t in Set.Icc (-T) T,
          ‖∑ p ∈ (Finset.Ioc ⌊R'⌋₊ ⌊2 * R'⌋₊).filter Nat.Prime,
            (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ^ 2 ≤
        C₂ * (T / (R' * Real.log R') + 1 / Real.log R' ^ 2))
    (hFt : ∀ Y : ℕ, Y₀ ≤ Y → (Y : ℝ) ^ (10 / 99 : ℝ) < z → 4 * Y < z ^ 6 → ∀ T : ℝ, 1 ≤ T →
      T ≤ (Y : ℝ) ^ (100 / 99 : ℝ) →
        ∫ t in Set.Icc (-T) T, ‖LSeries (fun n => mtHarmanProposition22SourceAF z Q D E Y n)
            (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          C_F * (T / (Y * Real.log Y) + 1 / Real.log Y ^ 2))
    (hpair : ∀ p₁ ∈ (Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime,
      ∀ p₂ ∈ (Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊ ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime,
        1 / 250 * (x * Real.exp (-(c / 8) * Real.sqrt L) / ((p₁ * p₂ : ℕ) : ℝ)) / L ≤
          ∑ n ∈ Finset.Ioc ⌊x / (p₁ * p₂)⌋₊ ⌊(x + x * Real.exp (-(c / 8) * Real.sqrt L)) / (p₁ * p₂)⌋₊,
            (rhoMinus z Q D E n : ℝ))
    (hS₁ : 1 / (3 * Real.log P₁) ≤ ∑ p ∈ (Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime, 1 / (p : ℝ))
    (hS₂ : 1 / (3 * L) ≤ ∑ p ∈ (Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊
      ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime, 1 / (p : ℝ))
    (h63 : 63 * B * L ≤ P₁) :
    Real.sqrt (x * P₁) * L / (18000 * (21 / 20 * Real.log P₁) * L ^ 2) ≤
      mtAllIntervalSumOn (((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime).filter
          (fun p => Nat.Coprime p A)) ((Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊
          ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime) z Q D E x (Real.sqrt (x * P₁) * L) := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hcmp := mt_forbidden_compare_small hx hL ha1 ha11 hP hc hC₂ hCF hε0 hε10 hB hL16 hLf2 hLf3
    hLf4 hLf5 hLc h64 hL2x hLε hL6 hL10 hsx1 hRx hYx hdsmall hz2 hz6 hA1 hAB h52 hP2 hFt
  clear h52 hP2 hFt hLf2 hLf3 hLf4 hdsmall hL10 hLε
  obtain ⟨hP2', hPL2, -, hsX, hXle, hXsq, -, hlogXhi, -⟩ :=
    mt_all_interval_scale_X hx hL hL16 ha1 ha11 hP rfl h64
  have hP0 : 0 < P₁ := by linarith
  obtain ⟨hRX, -, -, -⟩ := mt_all_interval_scale_R hx hL hL1 hP0 hPL2 rfl rfl hL6
  have hlogX0 : 0 ≤ Real.log (Real.sqrt (x * P₁)) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ Real.sqrt (x * P₁)); linarith
  obtain ⟨hh1, -, -, -, -, hhh₁, -, -, -, -⟩ :=
    mt_all_interval_scale_h (T₀ := Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2)))
      hx hL hL1 hc hLc hsX hXle hXsq hlogX0 hlogXhi hRX hsx1 hL2x hLf5 rfl
  have hPL : L ≤ P₁ := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 ha1
    rwa [Real.rpow_one, ← hP] at this
  have hlogP : 0 < Real.log P₁ := Real.log_pos (by linarith)
  have hlogA : Real.log A ≤ B * L := by
    have h1 := Real.log_le_log (by exact_mod_cast (by omega : 0 < A)) hAB
    rwa [Real.log_rpow hx, ← hL] at h1
  have hR0 : 0 ≤ Real.sqrt (x / P₁) / 2 := by positivity
  have hlong := mt_forbidden_long_ge (z := z) (Q := Q) (D := D) (E := E)
    (fun p hp => ⟨((mem_primes_Ioc_floor_iff hP0.le).1 hp).1,
      ((mem_primes_Ioc_floor_iff hP0.le).1 hp).2.1⟩)
    (fun p hp => ((mem_primes_Ioc_floor_iff hR0).1 hp).1.pos) (by omega : A ≠ 0) (by linarith)
    hL0 hlogP (by positivity) hpair hS₁ hS₂ hlogA h63
  clear hpair hS₁ hS₂
  have hh2 : 2 ≤ Real.sqrt (x * P₁) * L := by
    have := mul_le_mul (hsx1.trans hsX) hL16 (by norm_num) (by positivity)
    linarith
  obtain ⟨hH, hH₁, hH₁0⟩ := mt_all_interval_window_counts hx.le hh2 hhh₁
  have hℓ2 : 21 / 20 * Real.log P₁ ≤ 2 * Real.log L := by
    have e : Real.log P₁ = a * Real.log L := by rw [hP, Real.log_rpow hL0]
    have hlL : 0 ≤ Real.log L := Real.log_nonneg hL1
    have h1 : a * Real.log L ≤ 11 / 10 * Real.log L := mul_le_mul_of_nonneg_right ha11 hlL
    rw [e]; linarith only [h1, hlL]
  exact mt_all_interval_final hcmp hlong hh2 hhh₁ hH hH₁ hH₁0 (by positivity) hℓ2 hL0

/-- The scales of the deleted-support theorem: with `X = √(xP₁)`, `R = √(x/P₁)/2`, `h = XL`:
`P₁R = X/2`, `x = 2RX`, `h ≤ x/2`, `2√X + 1 ≤ R`, `log R ≥ L/3`. -/
theorem mt_forbidden_scales {x L a P₁ : ℝ} (hx : 0 < x) (hL : L = Real.log x) (hL16 : 16 ≤ L)
    (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) (hP : P₁ = L ^ a) (h64 : 64 * L ^ 2 ≤ x)
    (hL2x : L ^ 2 ≤ x ^ (1 / 4 : ℝ)) (hL6 : 2 * L ≤ x ^ (1 / 6 : ℝ))
    (hL12 : 3 * L ≤ x ^ (1 / 12 : ℝ)) :
    1 ≤ Real.sqrt (x * P₁) ∧ P₁ * (Real.sqrt (x / P₁) / 2) = Real.sqrt (x * P₁) / 2 ∧
      x = 2 * (Real.sqrt (x / P₁) / 2) * Real.sqrt (x * P₁) ∧
      Real.sqrt (x * P₁) * L ≤ x / 2 ∧
      2 * Real.sqrt (Real.sqrt (x * P₁)) + 1 ≤ Real.sqrt (x / P₁) / 2 ∧
      L / 3 ≤ Real.log (Real.sqrt (x / P₁) / 2) ∧ 2 ≤ P₁ ∧ P₁ ≤ L ^ 2 ∧
      Real.sqrt x ≤ Real.sqrt (x * P₁) := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨hP2', hPL2, -, hsX, hXle, hXsq, -, -, -⟩ :=
    mt_all_interval_scale_X hx hL hL16 ha1 ha11 hP rfl h64
  have hP0 : 0 < P₁ := by linarith
  obtain ⟨hRX, -, hx13, hlogR⟩ := mt_all_interval_scale_R hx hL hL1 hP0 hPL2 rfl rfl hL6
  set X := Real.sqrt (x * P₁) with hXdef
  set R := Real.sqrt (x / P₁) / 2 with hRdef
  clear_value X R
  have hsx1 : 1 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx.le]; nlinarith
  have hX0 : 0 < X := by linarith
  have hPR : P₁ * R = X / 2 := by
    have : P₁ * R * X = X ^ 2 / 2 := by rw [mul_assoc, hRX, hXsq]; ring
    have h2 : P₁ * R * X = X / 2 * X := by rw [this]; ring
    exact mul_right_cancel₀ hX0.ne' h2
  have hs4 : Real.sqrt x = x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]; norm_num
  have hsx2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have h4 : (2 : ℝ) ≤ x ^ (1 / 4 : ℝ) := by nlinarith
  refine ⟨hsx1.trans hsX, hPR, by linarith [hRX], ?_, ?_, hlogR, hP2', hPL2, hsX⟩
  · have h1 : X * L ≤ Real.sqrt x * L ^ 2 := by
      calc X * L ≤ Real.sqrt x * L * L := mul_le_mul_of_nonneg_right hXle hL0.le
        _ = Real.sqrt x * L ^ 2 := by ring
    have h2 : Real.sqrt x * L ^ 2 ≤ Real.sqrt x * x ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hL2x (Real.sqrt_nonneg x)
    have h3 : Real.sqrt x * x ^ (1 / 4 : ℝ) * 2 ≤ x := by
      calc Real.sqrt x * x ^ (1 / 4 : ℝ) * 2 ≤ Real.sqrt x * x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
            gcongr
        _ = x := by rw [mul_assoc, ← hs4, hsx2]
    linarith
  · have h1 : Real.sqrt X ≤ x ^ (1 / 4 : ℝ) * L := by
      have hsL : Real.sqrt L ≤ L := by
        rw [Real.sqrt_le_left hL0.le]; nlinarith
      have e : Real.sqrt (Real.sqrt x * L) = x ^ (1 / 4 : ℝ) * Real.sqrt L := by
        rw [Real.sqrt_mul (Real.sqrt_nonneg _), Real.sqrt_eq_rpow (Real.sqrt x), Real.sqrt_eq_rpow x,
          ← Real.rpow_mul hx.le]
        norm_num
      calc Real.sqrt X ≤ Real.sqrt (Real.sqrt x * L) := Real.sqrt_le_sqrt hXle
        _ = x ^ (1 / 4 : ℝ) * Real.sqrt L := e
        _ ≤ x ^ (1 / 4 : ℝ) * L := mul_le_mul_of_nonneg_left hsL (by positivity)
    have h2 : x ^ (1 / 4 : ℝ) * (3 * L) ≤ x ^ (1 / 3 : ℝ) := by
      calc x ^ (1 / 4 : ℝ) * (3 * L) ≤ x ^ (1 / 4 : ℝ) * x ^ (1 / 12 : ℝ) :=
            mul_le_mul_of_nonneg_left hL12 (by positivity)
        _ = x ^ (1 / 3 : ℝ) := by rw [← Real.rpow_add hx]; norm_num
    have h3 : 1 ≤ x ^ (1 / 4 : ℝ) * L := one_le_mul_of_one_le_of_one_le (by linarith) hL1
    linarith

/-- The windows of the `E₃` sum over prime sets in `(P₁, 2P₁] × (R, 2R]`: `X/2 < p₁p₂ ≤ 2X`, and
every cofactor in `(x/(p₁p₂), (x+h)/(p₁p₂)]` lies in `(R, 6R] ⊆ (R, 4X)`. -/
theorem mt_window_facts {B₁ B₂ : Finset ℕ} {x h X R P₁ : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (hhx : h ≤ x / 2) (hX : 0 < X) (hP : 2 ≤ P₁) (hR : 0 < R) (hPR : P₁ * R = X / 2)
    (hxRX : x = 2 * R * X) (hB₁ : ∀ p ∈ B₁, P₁ < p ∧ (p : ℝ) ≤ 2 * P₁)
    (hB₂ : ∀ p ∈ B₂, R < p ∧ (p : ℝ) ≤ 2 * R) :
    ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂, X / 2 < (p₁ : ℝ) * p₂ ∧ (p₁ : ℝ) * p₂ ≤ 2 * X ∧
      ∀ n ∈ Finset.Ioc ⌊x / ((p₁ : ℝ) * p₂)⌋₊ ⌊(x + h) / ((p₁ : ℝ) * p₂)⌋₊,
        R < n ∧ (n : ℝ) < 4 * X ∧ (n : ℝ) ≤ 6 * R := by
  intro p₁ hp₁ p₂ hp₂
  obtain ⟨h1l, h1u⟩ := hB₁ p₁ hp₁
  obtain ⟨h2l, h2u⟩ := hB₂ p₂ hp₂
  have hP0 : 0 < P₁ := by linarith
  have hql : X / 2 < (p₁ : ℝ) * p₂ := by rw [← hPR]; exact mul_lt_mul'' h1l h2l hP0.le hR.le
  have hqu : (p₁ : ℝ) * p₂ ≤ 2 * X := by
    calc (p₁ : ℝ) * p₂ ≤ (2 * P₁) * (2 * R) := mul_le_mul h1u h2u (Nat.cast_nonneg _) (by linarith)
      _ = 2 * X := by rw [show 2 * P₁ * (2 * R) = 4 * (P₁ * R) by ring, hPR]; ring
  refine ⟨hql, hqu, fun n hn => ?_⟩
  have hq0 : (0 : ℝ) < (p₁ : ℝ) * p₂ := by linarith
  obtain ⟨hn1, hn2⟩ := (mem_Ioc_natFloor_div_iff hx.le (by linarith) hq0).1 hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  constructor
  · have h1 : x < 2 * X * n := lt_of_lt_of_le hn1 (mul_le_mul_of_nonneg_right hqu hn0)
    rw [hxRX] at h1
    have : 2 * X * R < 2 * X * n := by linarith
    exact lt_of_mul_lt_mul_left this (by linarith)
  · have h1 : X / 2 * n ≤ x + h := le_trans (mul_le_mul_of_nonneg_right hql.le hn0) hn2
    have hRX4 : 2 * R ≤ X / 2 := by nlinarith
    have h2 : x + h ≤ 3 * R * X := by rw [hxRX] at hhx ⊢; linarith
    have h3 : X / 2 * n ≤ X / 2 * (6 * R) := by nlinarith
    have h4 : (n : ℝ) ≤ 6 * R := le_of_mul_le_mul_left h3 (by linarith)
    exact ⟨by linarith, h4⟩

/-- `log L ≤ L/2` for `L ≥ 16`. -/
theorem log_le_half_of_sixteen_le {L : ℝ} (hL : 16 ≤ L) : Real.log L ≤ L / 2 := by
  have hL0 : 0 < L := by linarith
  have hsL : 4 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have e : Real.log L = 2 * Real.log (Real.sqrt L) := by
    rw [← Real.log_rpow (by linarith), show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, hsq]
  have h4 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt L by linarith)
  nlinarith

/-- The deletion count against the main term: if `#B₁ ≤ 2L²`, `log P₁ ≤ L`, `√x ≤ X` and
`216000(471B + 1)L⁵ ≤ √x`, then `#B₁ (471B + 1)(2L + 1)·36000 log P₁ L² ≤ XL`. -/
theorem mt_forbidden_count_le {c L B P₁ X x : ℝ} (hc : c ≤ 2 * L ^ 2) (hL : 1 ≤ L)
    (hB : 0 < B) (hlogP : Real.log P₁ ≤ L) (hlogP0 : 0 < Real.log P₁) (hsX : x ^ (1 / 2 : ℝ) ≤ X)
    (hpoly : 216000 * (471 * B + 1) * L ^ 5 ≤ x ^ (1 / 2 : ℝ)) :
    c * ((157 * (3 * B) + 1) * (2 * L + 1)) * (36000 * Real.log P₁ * L ^ 2) ≤ X * L := by
  have hL0 : 0 < L := by linarith
  have hK : (157 * (3 * B) + 1) * (2 * L + 1) ≤ (471 * B + 1) * (3 * L) := by
    have h1 : 2 * L + 1 ≤ 3 * L := by linarith
    have h2 : (0 : ℝ) ≤ 157 * (3 * B) + 1 := by positivity
    calc (157 * (3 * B) + 1) * (2 * L + 1) ≤ (157 * (3 * B) + 1) * (3 * L) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = (471 * B + 1) * (3 * L) := by ring
  calc c * ((157 * (3 * B) + 1) * (2 * L + 1)) * (36000 * Real.log P₁ * L ^ 2)
      ≤ (2 * L ^ 2) * ((471 * B + 1) * (3 * L)) * (36000 * L * L ^ 2) := by gcongr
    _ = 216000 * (471 * B + 1) * L ^ 5 * L := by ring
    _ ≤ x ^ (1 / 2 : ℝ) * L := mul_le_mul_of_nonneg_right hpoly hL0.le
    _ ≤ X * L := mul_le_mul_of_nonneg_right hsX hL0.le

/-- **The minorant on the cofactor windows.**  At the Proposition 2.2 parameters for `X ≥ 1`, a
cofactor `n ∈ (R, 4X)` with `2√X + 1 ≤ R` and `4X < z⁶` has `|ρ⁻(n)| ≤ 156` and
`ρ⁻(n) ≤ 1_prime(n)`: it lies below `z⁶` and in `[Q, Q²)`. -/
theorem mt_rhoMinus_window_bounds {X R ε : ℝ} {n : ℕ} (hX1 : 1 ≤ X) (hε : 0 < ε)
    (hQR : 2 * Real.sqrt X + 1 ≤ R) (hz2 : 2 ≤ mtProposition22ZNat X)
    (hz6 : 4 * X < (mtProposition22ZNat X : ℝ) ^ 6) (hnR : R < n) (hnX : (n : ℝ) < 4 * X) :
    |(rhoMinus (mtProposition22ZNat X) (mtProposition22QNat X) (mtProposition22DNat X ε)
        (mtProposition22ENat X ε) n : ℝ)| ≤ 156 ∧
      (rhoMinus (mtProposition22ZNat X) (mtProposition22QNat X) (mtProposition22DNat X ε)
        (mtProposition22ENat X ε) n : ℝ) ≤ if n.Prime then 1 else 0 := by
  obtain ⟨hzQ, hDQ, hQlo, hQhi⟩ := mtProposition22_parameters_le (ε := ε) hX1 hε
  have hX0 : 0 < X := by linarith
  have hs1 : 1 ≤ Real.sqrt X := Real.one_le_sqrt.2 hX1
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hQ2 : 2 ≤ mtProposition22QNat X := by
    have : (2 : ℝ) ≤ mtProposition22QNat X := by linarith
    exact_mod_cast this
  have hQsq : 4 * X ≤ (mtProposition22QNat X : ℝ) * mtProposition22QNat X := by
    have hs : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
    have h0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
    calc 4 * X = (2 * Real.sqrt X) * (2 * Real.sqrt X) := by
          rw [show (2 * Real.sqrt X) * (2 * Real.sqrt X) = 4 * (Real.sqrt X * Real.sqrt X) by ring, hs]
      _ ≤ (mtProposition22QNat X : ℝ) * mtProposition22QNat X :=
          mul_le_mul hQlo hQlo (by linarith) (Nat.cast_nonneg _)
  refine ⟨?_, ?_⟩
  · have hnz : n < mtProposition22ZNat X ^ 6 := by
      have : (n : ℝ) < ((mtProposition22ZNat X ^ 6 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact_mod_cast abs_rhoMinus_le_of_lt_pow (Q := mtProposition22QNat X)
      (D := mtProposition22DNat X ε) (E := mtProposition22ENat X ε) hz2 hn0 hnz
  · have hQn : mtProposition22QNat X ≤ n := by
      have : (mtProposition22QNat X : ℝ) ≤ n := by linarith
      exact_mod_cast this
    have hnQ : n < mtProposition22QNat X * mtProposition22QNat X := by
      have : (n : ℝ) < ((mtProposition22QNat X * mtProposition22QNat X : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    have h := rhoMinus_le_primeIndicator (D := mtProposition22DNat X ε)
      (E := mtProposition22ENat X ε) hn0 hQ2 hzQ hDQ hQn hnQ
    split_ifs at h ⊢ <;> exact_mod_cast h

/-- **The deletions are negligible at one `x`.**  Removing the large primes dividing `A`, the
cofactors sharing a prime with `A` and the diagonal `n = p₂` from the deleted-support `E₃` window
sum changes it by at most `h/(36000 log P₁ · L²)`. -/
theorem mt_forbidden_delete_small {x L a B P₁ ε : ℝ} {A : ℕ} (hx : 0 < x) (hL : L = Real.log x)
    (hL16 : 16 ≤ L) (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) (hP : P₁ = L ^ a) (hε : 0 < ε) (hB : 0 < B)
    (h64 : 64 * L ^ 2 ≤ x) (hL2x : L ^ 2 ≤ x ^ (1 / 4 : ℝ)) (hL6 : 2 * L ≤ x ^ (1 / 6 : ℝ))
    (hL12 : 3 * L ≤ x ^ (1 / 12 : ℝ))
    (hpoly : 216000 * (471 * B + 1) * L ^ 5 ≤ x ^ (1 / 2 : ℝ))
    (hz2 : 2 ≤ mtProposition22ZNat (Real.sqrt (x * P₁)))
    (hz6 : 4 * Real.sqrt (x * P₁) < (mtProposition22ZNat (Real.sqrt (x * P₁)) : ℝ) ^ 6)
    (hA1 : 1 ≤ A) (hAB : (A : ℝ) ≤ x ^ B) :
    mtAllIntervalSumOn (((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime).filter
          (fun p => Nat.Coprime p A)) ((Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊
          ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime)
          (mtProposition22ZNat (Real.sqrt (x * P₁))) (mtProposition22QNat (Real.sqrt (x * P₁)))
          (mtProposition22DNat (Real.sqrt (x * P₁)) ε) (mtProposition22ENat (Real.sqrt (x * P₁)) ε)
          x (Real.sqrt (x * P₁) * L) -
        mtCoprimeE3Sum (((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime).filter
          (fun p => Nat.Coprime p A)) ((Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊
          ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime) A
          (mtProposition22ZNat (Real.sqrt (x * P₁))) (mtProposition22QNat (Real.sqrt (x * P₁)))
          (mtProposition22DNat (Real.sqrt (x * P₁)) ε) (mtProposition22ENat (Real.sqrt (x * P₁)) ε)
          x (Real.sqrt (x * P₁) * L) ≤
      Real.sqrt (x * P₁) * L / (36000 * Real.log P₁ * L ^ 2) := by
  classical
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨hX1, hPR, hxRX, hhx, hQR, hlogR, hP2, hPL2, hsX⟩ :=
    mt_forbidden_scales hx hL hL16 ha1 ha11 hP h64 hL2x hL6 hL12
  have hP0 : 0 < P₁ := by linarith
  have hsqrtXP : ∀ p : ℝ, P₁ ≤ p → Real.sqrt (x * P₁) ≤ Real.sqrt (x * p) := fun p hp =>
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hp hx.le)
  generalize hXg : Real.sqrt (x * P₁) = X at *
  generalize hRg : Real.sqrt (x / P₁) / 2 = R at *
  have hX0 : 0 < X := by linarith
  have hR0 : 0 < R := by
    have h1 : 0 ≤ Real.sqrt (Real.sqrt (x * P₁)) := Real.sqrt_nonneg _
    rw [hXg] at h1; linarith
  have hlogA : Real.log A ≤ B * L := by
    have h1 := Real.log_le_log (by exact_mod_cast (by omega : 0 < A)) hAB
    rwa [Real.log_rpow hx, ← hL] at h1
  have hlogR0 : 0 < Real.log R := lt_of_lt_of_le (by positivity) hlogR
  have hR1 : 1 < R := by
    by_contra hc; push Not at hc
    have := Real.log_nonpos hR0.le hc; linarith
  have hA0 : A ≠ 0 := by omega
  have h3B : Real.log A / Real.log R ≤ 3 * B := by
    rw [div_le_iff₀ hlogR0]
    have := mul_le_mul_of_nonneg_left hlogR (by linarith : (0 : ℝ) ≤ 3 * B)
    linarith only [this, hlogA]
  set B₁ := ((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime).filter (fun p => Nat.Coprime p A)
    with hB₁def
  set B₂ := (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime with hB₂def
  have hB₁r : ∀ p ∈ B₁, P₁ < p ∧ (p : ℝ) ≤ 2 * P₁ := fun p hp =>
    ((mem_primes_Ioc_floor_iff hP0.le).1 (Finset.mem_filter.1 hp).1).2
  have hB₂r : ∀ p ∈ B₂, p.Prime ∧ R < p ∧ (p : ℝ) ≤ 2 * R := fun p hp =>
    (mem_primes_Ioc_floor_iff hR0.le).1 hp
  have hwin := mt_window_facts (B₁ := B₁) (B₂ := B₂) (h := X * L) hx (by positivity) hhx hX0 hP2
    hR0 hPR hxRX hB₁r fun p hp => (hB₂r p hp).2
  refine (mtAllIntervalSumOn_sub_delete_le (K := 3 * B) (Wm := 2 * L + 1) hA0 hx
    (by positivity) hR0 (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2.pos)
    (fun p hp => (hB₂r p hp).1.pos) (fun p₁ hp₁ p₂ hp₂ n hn => ((hwin p₁ hp₁ p₂ hp₂).2.2 n hn).1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by positivity)).trans ?_
  · intro p₁ hp₁ p₂ hp₂ n hn
    obtain ⟨hnR, hnX, -⟩ := (hwin p₁ hp₁ p₂ hp₂).2.2 n hn
    exact (mt_rhoMinus_window_bounds hX1 hε hQR hz2 hz6 hnR hnX).1
  · intro p₁ hp₁ p₂ hp₂ n hn
    obtain ⟨hnR, hnX, -⟩ := (hwin p₁ hp₁ p₂ hp₂).2.2 n hn
    exact (mt_rhoMinus_window_bounds hX1 hε hQR hz2 hz6 hnR hnX).2
  · -- window sizes
    intro p₁ hp₁ p₂ hp₂
    obtain ⟨hql, -, -⟩ := hwin p₁ hp₁ p₂ hp₂
    have hq0 : (0 : ℝ) < (p₁ : ℝ) * p₂ := by linarith
    have hXL : 0 ≤ X * L := (mul_pos hX0 hL0).le
    refine (card_Ioc_natFloor_div_le hx.le (by linarith only [hXL]) hq0).trans ?_
    rw [add_sub_cancel_left]
    have : X * L / ((p₁ : ℝ) * p₂) ≤ 2 * L := by
      rw [div_le_iff₀ hq0]
      have := mul_le_mul_of_nonneg_left hql.le (by linarith : (0 : ℝ) ≤ 2 * L)
      linarith only [this]
    linarith only [this]
  · -- large primes dividing `A`
    exact (card_filter_not_coprime_le hA0 hR1 fun p hp =>
      ⟨(hB₂r p hp).1, (hB₂r p hp).2.1.le⟩).trans h3B
  · -- prime divisors of `A` above `R`
    exact (ForbiddenSupport.card_le_log_div_log hA0 (Finset.filter_subset _ _) hR1
      fun p hp => (Finset.mem_filter.1 hp).2.le).trans h3B
  · intro p₁ hp₁
    have hp₁R : (X / 2) ≤ (p₁ : ℝ) * R := by
      rw [← hPR]; exact mul_le_mul_of_nonneg_right (hB₁r p₁ hp₁).1.le hR0.le
    have : X * L / ((p₁ : ℝ) * R) ≤ 2 * L := by
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hp₁R (by linarith : (0 : ℝ) ≤ 2 * L)
      linarith only [this]
    linarith only [this]
  · intro p₁ hp₁
    have hs : X ≤ Real.sqrt (x * p₁) := hsqrtXP _ (hB₁r p₁ hp₁).1.le
    have : X * L / (2 * Real.sqrt (x * p₁)) ≤ L / 2 := by
      rw [div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hs hL0.le
      linarith only [this]
    linarith only [this, hL0]
  · -- the count
    have hcard : (B₁.card : ℝ) ≤ 2 * L ^ 2 := by
      have h1 : B₁.card ≤ (Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).card :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans
          (Finset.card_le_card (Finset.filter_subset _ _))
      have h2 := card_Ioc_natFloor_le hP0.le (by linarith : P₁ ≤ 2 * P₁)
      have : (B₁.card : ℝ) ≤ 2 * P₁ - P₁ + 1 := (Nat.cast_le.2 h1).trans h2
      have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
      linarith only [this, hPL2, hL2]
    have hlogP : Real.log P₁ ≤ L := by
      have h1 := Real.log_le_log hP0 hPL2
      have h2 : Real.log (L ^ 2) = 2 * Real.log L := by
        rw [Real.log_pow]; push_cast; ring
      have h3 := log_le_half_of_sixteen_le hL16
      linarith only [h1, h2, h3]
    have hlogP0 : 0 < Real.log P₁ := Real.log_pos (by linarith)
    rw [le_div_iff₀ (by positivity)]
    exact mt_forbidden_count_le hcard hL1 hB hlogP hlogP0
      (by rw [← Real.sqrt_eq_rpow]; exact hsX) hpoly
/-- **Forbidden-support stability of the all-interval `E₃` theorem.**  Assume the
Deshouillers–Iwaniec bound `(E1)` and Watt's bound `(E2)`.  Fix `B > 0`.  For all large `x` and
all integers `1 ≤ A ≤ x^B`, with `L = log x`, `P₁ = L^{11/10}`, `X = √(xP₁)`, `R = √(x/P₁)/2` and
`h = XL = √x L^{1 + 11/20}`: the `E₃` count over `p₁ ∈ (P₁, 2P₁]`, `p₂ ∈ (R, 2R]` and cofactors
`x < p₁p₂n ≤ x + h`, with `p₁, p₂, n` coprime to `A` and `n ≠ p₂`, weighted by Harman's minorant
`ρ⁻(n)` (parameters of Proposition 2.2 at `X`, `ε = 10⁻⁷`), is at least `h/(40000 log P₁ · L²)`. -/
theorem eventually_mtCoprimeE3Sum_ge (hDI : MTDeshouillersIwaniecBound) (hW : MTWattBound)
    {B : ℝ} (hB : 0 < B) :
    ∀ᶠ x : ℝ in atTop, ∀ A : ℕ, 1 ≤ A → (A : ℝ) ≤ x ^ B →
      Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ)) * Real.log x /
          (40000 * Real.log (Real.log x ^ (11 / 10 : ℝ)) * Real.log x ^ 2) ≤
        mtCoprimeE3Sum (((Finset.Ioc ⌊Real.log x ^ (11 / 10 : ℝ)⌋₊
            ⌊2 * Real.log x ^ (11 / 10 : ℝ)⌋₊).filter Nat.Prime).filter (fun p => Nat.Coprime p A))
          ((Finset.Ioc ⌊Real.sqrt (x / Real.log x ^ (11 / 10 : ℝ)) / 2⌋₊
            ⌊2 * (Real.sqrt (x / Real.log x ^ (11 / 10 : ℝ)) / 2)⌋₊).filter Nat.Prime) A
          (mtProposition22ZNat (Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ))))
          (mtProposition22QNat (Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ))))
          (mtProposition22DNat (Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ))) (1 / 10 ^ 7))
          (mtProposition22ENat (Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ))) (1 / 10 ^ 7)) x
          (Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ)) * Real.log x) := by
  have hε0 : (0 : ℝ) < 1 / 10 ^ 7 := by positivity
  obtain ⟨c, hc, hlong⟩ := exists_mtAllInterval_long_pair_bounds
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (eventually_harmanProduct_meanSquare_le hDI hW (A := 5)
    le_rfl (by norm_num : (10999 / 10000 : ℝ) ≤ 11 / 10) hε0 (by norm_num)
    (by positivity : (0 : ℝ) < c / 32))
  obtain ⟨C₂, hC₂, hP2⟩ := eventually_integral_normSq_primeSet_floor_le
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hP2
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 eventually_mtProposition22ZNat_facts
  obtain ⟨C_F, hCF, Y₀, hFt⟩ := exists_integral_normSq_LSeries_harmanSource_tall_le
  have hpl : ∀ {C κ : ℝ} (m : ℕ), 0 ≤ C → 0 < κ →
      ∀ᶠ x : ℝ in atTop, C * Real.log x ^ m ≤ x ^ κ := by
    intro C κ m hC hκ
    filter_upwards [eventually_polylog_le_rpow m hC hκ, eventually_ge_atTop (1 : ℝ)] with x h hx
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    have hle : Real.log x ≤ 1 + Real.log (24 * x) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl hle m) hC) h
  have hLd : ∀ᶠ L : ℝ in atTop, 9 * C_F * B ^ 2 ≤ 16 * L ^ (2 * (11 / 10 : ℝ) - 2 - 1 / 10 ^ 7 / 10)
      ∧ 63 * B ≤ L ^ (1 / 10 : ℝ) := by
    have e : (2 * (11 / 10 : ℝ) - 2 - 1 / 10 ^ 7 / 10) = 1 / 5 - 1 / 10 ^ 8 := by norm_num
    rw [e]
    filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5 - 1 / 10 ^ 8)).eventually_ge_atTop
        (9 * C_F * B ^ 2 / 16),
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually_ge_atTop (63 * B)]
      with L h1 h2
    exact ⟨by linarith, h2⟩
  filter_upwards [hlong,
    Real.tendsto_log_atTop.eventually (mt_all_interval_log_facts (C := 4 * C₂) hc hε0),
    Real.tendsto_log_atTop.eventually hLd,
    Real.tendsto_log_atTop.eventually_ge_atTop (c ^ 2 / 4),
    hpl (C := 64) 2 (by norm_num) (by norm_num : (0 : ℝ) < 1),
    hpl (C := 1) 2 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4),
    hpl (C := 4) 2 (by norm_num) (by positivity : (0 : ℝ) < 1 / 10 ^ 7 / 200),
    hpl (C := 2) 1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 6),
    hpl (C := 4) 10 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 600),
    hpl (C := 3) 1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 12),
    hpl (C := 216000 * (471 * B + 1)) 5 (by positivity) (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (max (max X₀ X₁) 1 ^ 2), eventually_ge_atTop (max R₀ 1 ^ 3),
    eventually_ge_atTop (max Y₀ 1 ^ 3)]
    with x hlongx hLf hLdx hLc h64 hL2x hLε hL6 hL10 hL12 hpoly hxX hxR hxY
  intro A hA1 hAB
  obtain ⟨hL16, hLf2, hLf3, hLf4, hLf5⟩ := hLf
  obtain ⟨hdsmall, h63'⟩ := hLdx
  have hx1 : 1 ≤ x := by
    have hM : 1 ≤ max (max X₀ X₁) 1 ^ 2 := one_le_pow₀ (le_max_right _ _)
    linarith
  have hx0 : 0 < x := by linarith
  have hsxX : max (max X₀ X₁) 1 ≤ Real.sqrt x := (Real.le_sqrt (by positivity) hx0.le).2 hxX
  have hsx1 : 1 ≤ Real.sqrt x := le_trans (le_max_right _ _) hsxX
  obtain ⟨hP2', hPL2, -, hsX, -, -, -, -, -⟩ :=
    mt_all_interval_scale_X hx0 rfl hL16 (by norm_num : (1 : ℝ) ≤ 11 / 10) le_rfl rfl rfl
      (by simpa using h64)
  have hXX₀ : X₀ ≤ Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ)) := by
    have := le_trans (le_max_left X₀ X₁) (le_max_left _ 1); linarith
  have hXX₁ : X₁ ≤ Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ)) := by
    have := le_trans (le_max_right X₀ X₁) (le_max_left _ 1); linarith
  obtain ⟨hz2, hz6⟩ := hX₁ _ hXX₁
  have hL0 : 0 < Real.log x := by linarith
  obtain ⟨hpair, hS₁, hS₂⟩ := hlongx (11 / 10) ⟨by norm_num, by norm_num⟩ _ hε0 le_rfl
  have h63 : 63 * B * Real.log x ≤ Real.log x ^ (11 / 10 : ℝ) := by
    have e : Real.log x ^ (11 / 10 : ℝ) = Real.log x * Real.log x ^ (1 / 10 : ℝ) := by
      rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, Real.rpow_add hL0, Real.rpow_one]
    rw [e]
    have := mul_le_mul_of_nonneg_left h63' hL0.le
    linarith
  have hshort := mt_forbidden_short_ge (a := 11 / 10) (A := A) hx0 rfl (by norm_num) le_rfl rfl hc
    hC₂ hCF hε0 (by norm_num) hB hL16 hLf2 hLf3 hLf4 hLf5 hLc (by simpa using h64)
    (by simpa using hL2x) hLε (by simpa using hL6) hL10 hsx1 hxR hxY hdsmall hz2 hz6 hA1 hAB
    (fun P B' => hX₀ _ hXX₀ (11 / 10) P B' le_rfl le_rfl) hR₀
    (fun Y h1 h2 h3 => hFt _ _ _ _ Y h1 h2 hz2 h3) hpair hS₁ hS₂ h63
  have hdel := mt_forbidden_delete_small (a := 11 / 10) (B := B) (A := A) (ε := 1 / 10 ^ 7) hx0 rfl
    hL16 (by norm_num) le_rfl rfl hε0 hB (by simpa using h64) (by simpa using hL2x)
    (by simpa using hL6) (by simpa using hL12) (by simpa using hpoly) hz2 hz6 hA1 hAB
  clear hX₀ hR₀ hFt hlongx hpair
  have hlogP0 : 0 < Real.log (Real.log x ^ (11 / 10 : ℝ)) := Real.log_pos (by
    have : Real.log x ≤ Real.log x ^ (11 / 10 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Real.log x)
        (by norm_num : (1 : ℝ) ≤ 11 / 10)
      rwa [Real.rpow_one] at this
    linarith)
  set S := mtAllIntervalSumOn (((Finset.Ioc ⌊Real.log x ^ (11 / 10 : ℝ)⌋₊
      ⌊2 * Real.log x ^ (11 / 10 : ℝ)⌋₊).filter Nat.Prime).filter (fun p => Nat.Coprime p A))
    ((Finset.Ioc ⌊Real.sqrt (x / Real.log x ^ (11 / 10 : ℝ)) / 2⌋₊
      ⌊2 * (Real.sqrt (x / Real.log x ^ (11 / 10 : ℝ)) / 2)⌋₊).filter Nat.Prime)
    (mtProposition22ZNat (Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ))))
    (mtProposition22QNat (Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ))))
    (mtProposition22DNat (Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ))) (1 / 10 ^ 7))
    (mtProposition22ENat (Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ))) (1 / 10 ^ 7)) x
    (Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ)) * Real.log x) with hSdef
  clear_value S
  have hhpos : 0 ≤ Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ)) * Real.log x := by positivity
  set hh := Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ)) * Real.log x
  set ℓ := Real.log (Real.log x ^ (11 / 10 : ℝ))
  set L := Real.log x
  have e1 : hh / (18000 * (21 / 20 * ℓ) * L ^ 2) = hh / (ℓ * L ^ 2) / 18900 := by
    field_simp; ring
  have e2 : hh / (36000 * ℓ * L ^ 2) = hh / (ℓ * L ^ 2) / 36000 := by field_simp
  have e3 : hh / (40000 * ℓ * L ^ 2) = hh / (ℓ * L ^ 2) / 40000 := by field_simp
  have hq : 0 ≤ hh / (ℓ * L ^ 2) := by positivity
  rw [e1] at hshort
  rw [e2] at hdel
  rw [e3]
  linarith

/-- **A positive coprime `E₃` sum exhibits a squarefree `E₃` number.**  If the coprime `E₃` sum of
the deleted-support theorem is positive, some `p₁p₂p₃ ∈ (x, x+h]` is a product of three distinct
primes, `p₁ ∈ (P₁, 2P₁]`, `p₂ ∈ (R, 2R]`, `p₃ ∈ (R, 6R]`, coprime to `A`. -/
theorem exists_coprime_threePrime_of_pos {x L a P₁ ε : ℝ} {A : ℕ} (hx : 0 < x)
    (hL : L = Real.log x) (hL16 : 16 ≤ L) (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) (hP : P₁ = L ^ a)
    (hε : 0 < ε) (h64 : 64 * L ^ 2 ≤ x) (hL2x : L ^ 2 ≤ x ^ (1 / 4 : ℝ))
    (hL6 : 2 * L ≤ x ^ (1 / 6 : ℝ)) (hL12 : 3 * L ≤ x ^ (1 / 12 : ℝ))
    (hz2 : 2 ≤ mtProposition22ZNat (Real.sqrt (x * P₁)))
    (hz6 : 4 * Real.sqrt (x * P₁) < (mtProposition22ZNat (Real.sqrt (x * P₁)) : ℝ) ^ 6)
    (hpos : 0 < mtCoprimeE3Sum (((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime).filter
          (fun p => Nat.Coprime p A)) ((Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊
          ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime) A
          (mtProposition22ZNat (Real.sqrt (x * P₁))) (mtProposition22QNat (Real.sqrt (x * P₁)))
          (mtProposition22DNat (Real.sqrt (x * P₁)) ε) (mtProposition22ENat (Real.sqrt (x * P₁)) ε)
          x (Real.sqrt (x * P₁) * L)) :
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
      P₁ < p₁ ∧ (p₁ : ℝ) ≤ 2 * P₁ ∧ Real.sqrt (x / P₁) / 2 < p₂ ∧
      (p₂ : ℝ) ≤ 2 * (Real.sqrt (x / P₁) / 2) ∧ Real.sqrt (x / P₁) / 2 < p₃ ∧
      (p₃ : ℝ) ≤ 6 * (Real.sqrt (x / P₁) / 2) ∧ Nat.Coprime (p₁ * p₂ * p₃) A ∧
      x < ((p₁ * p₂ * p₃ : ℕ) : ℝ) ∧ ((p₁ * p₂ * p₃ : ℕ) : ℝ) ≤ x + Real.sqrt (x * P₁) * L := by
  classical
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨hX1, hPR, hxRX, hhx, hQR, -, hP2, hPL2, hsX⟩ :=
    mt_forbidden_scales hx hL hL16 ha1 ha11 hP h64 hL2x hL6 hL12
  have hP0 : 0 < P₁ := by linarith
  -- `2P₁ < R`
  have h2P : 2 * P₁ < Real.sqrt (x / P₁) / 2 := by
    have h1 : x ^ (1 / 4 : ℝ) ≤ Real.sqrt (Real.sqrt (x * P₁)) := by
      have e : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow (Real.sqrt x), Real.sqrt_eq_rpow x, ← Real.rpow_mul hx.le]; norm_num
      rw [← e]; exact Real.sqrt_le_sqrt hsX
    linarith
  unfold mtCoprimeE3Sum at hpos
  generalize hXg : Real.sqrt (x * P₁) = X at *
  generalize hRg : Real.sqrt (x / P₁) / 2 = R at *
  have hX0 : 0 < X := by linarith
  have hR0 : 0 < R := by linarith
  set B₁ := ((Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime).filter (fun p => Nat.Coprime p A)
    with hB₁def
  set B₂ := (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime with hB₂def
  have hB₁r : ∀ p ∈ B₁, p.Prime ∧ P₁ < p ∧ (p : ℝ) ≤ 2 * P₁ := fun p hp =>
    (mem_primes_Ioc_floor_iff hP0.le).1 (Finset.mem_filter.1 hp).1
  have hB₂r : ∀ p ∈ B₂, p.Prime ∧ R < p ∧ (p : ℝ) ≤ 2 * R := fun p hp =>
    (mem_primes_Ioc_floor_iff hR0.le).1 hp
  have hwin := mt_window_facts (B₁ := B₁) (B₂ := B₂) (h := X * L) hx (by positivity) hhx hX0 hP2
    hR0 hPR hxRX (fun p hp => (hB₁r p hp).2) fun p hp => (hB₂r p hp).2
  -- a positive term
  have hex : ∀ {s : Finset ℕ} {f : ℕ → ℝ}, 0 < ∑ i ∈ s, f i → ∃ i ∈ s, 0 < f i := by
    intro s f h
    by_contra hc
    push Not at hc
    exact absurd h (not_lt.2 (Finset.sum_nonpos hc))
  obtain ⟨p₁, hp₁, h1⟩ := hex hpos
  obtain ⟨p₂, hp₂, h2⟩ := hex h1
  obtain ⟨n, hn, h3⟩ := hex h2
  obtain ⟨hnW, hncop, hnp₂⟩ := Finset.mem_filter.1 hn
  obtain ⟨hp₂B, hp₂cop⟩ := Finset.mem_filter.1 hp₂
  obtain ⟨hql, hqu, hWn⟩ := hwin p₁ hp₁ p₂ hp₂B
  obtain ⟨hnR, hnX, hn6⟩ := hWn n hnW
  have hρ := (mt_rhoMinus_window_bounds hX1 hε hQR hz2 hz6 hnR hnX).2
  have hnp : n.Prime := by
    by_contra hnp
    rw [if_neg hnp] at hρ
    linarith
  obtain ⟨hp₁p, hp₁l, hp₁u⟩ := hB₁r p₁ hp₁
  obtain ⟨hp₂p, hp₂l, hp₂u⟩ := hB₂r p₂ hp₂B
  have hq0 : (0 : ℝ) < (p₁ : ℝ) * p₂ := by linarith
  obtain ⟨hw1, hw2⟩ := (mem_Ioc_natFloor_div_iff hx.le (by nlinarith) hq0).1 hnW
  refine ⟨p₁, p₂, n, hp₁p, hp₂p, hnp, ?_, ?_, fun h => hnp₂ h.symm, hp₁l, hp₁u, hp₂l, hp₂u, hnR, hn6, ?_, ?_, ?_⟩
  · intro h; rw [h] at hp₁u; linarith
  · intro h; rw [h] at hp₁u; linarith
  · exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (Finset.mem_filter.1 hp₁).2 hp₂cop) hncop
  · push_cast; linarith
  · push_cast; linarith

/-- Three distinct primes have a squarefree product. -/
theorem squarefree_mul_three_primes {p₁ p₂ p₃ : ℕ} (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) : Squarefree (p₁ * p₂ * p₃) := by
  rw [Nat.squarefree_mul_iff, Nat.squarefree_mul_iff]
  refine ⟨Nat.Coprime.mul_left ((Nat.coprime_primes h₁ h₃).2 h13) ((Nat.coprime_primes h₂ h₃).2 h23),
    ⟨(Nat.coprime_primes h₁ h₂).2 h12, h₁.squarefree, h₂.squarefree⟩, h₃.squarefree⟩

/-- An `E₃` token at scale `x` coprime to `A`: distinct primes `p₁ ∈ (P₁, 2P₁]`, `p₂ ∈ (R, 2R]`,
`p₃ ∈ (R, 6R]`, `P₁ = (log x)^{11/10}`, `R = √(x/P₁)/2`, with `p₁p₂p₃` squarefree, coprime to `A` and
in `(x, x + √(xP₁) log x]`. -/
def IsCoprimeE3Token (x : ℝ) (A p₁ p₂ p₃ : ℕ) : Prop :=
  p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
    Real.log x ^ (11 / 10 : ℝ) < p₁ ∧ (p₁ : ℝ) ≤ 2 * Real.log x ^ (11 / 10 : ℝ) ∧
    Real.sqrt (x / Real.log x ^ (11 / 10 : ℝ)) / 2 < p₂ ∧
    (p₂ : ℝ) ≤ 2 * (Real.sqrt (x / Real.log x ^ (11 / 10 : ℝ)) / 2) ∧
    Real.sqrt (x / Real.log x ^ (11 / 10 : ℝ)) / 2 < p₃ ∧
    (p₃ : ℝ) ≤ 6 * (Real.sqrt (x / Real.log x ^ (11 / 10 : ℝ)) / 2) ∧
    Squarefree (p₁ * p₂ * p₃) ∧ Nat.Coprime (p₁ * p₂ * p₃) A ∧
    x < ((p₁ * p₂ * p₃ : ℕ) : ℝ) ∧
    ((p₁ * p₂ * p₃ : ℕ) : ℝ) ≤ x + Real.sqrt (x * Real.log x ^ (11 / 10 : ℝ)) * Real.log x

/-- **Every interval `(x, x + √x (log x)^{1.55}]` contains a squarefree `E₃` number coprime to any
`A ≤ x^B`.**  Assume `(E1)` and `(E2)`.  For all large `x` and all `1 ≤ A ≤ x^B` there are distinct
primes `p₁ ∈ (P₁, 2P₁]`, `p₂ ∈ (R, 2R]`, `p₃ ∈ (R, 6R]`, `P₁ = (log x)^{11/10}`,
`R = √(x/P₁)/2`, with `p₁p₂p₃` coprime to `A` and `x < p₁p₂p₃ ≤ x + √(xP₁) log x`. -/
theorem eventually_exists_coprime_threePrime (hDI : MTDeshouillersIwaniecBound) (hW : MTWattBound)
    {B : ℝ} (hB : 0 < B) :
    ∀ᶠ x : ℝ in atTop, ∀ A : ℕ, 1 ≤ A → (A : ℝ) ≤ x ^ B →
      ∃ p₁ p₂ p₃ : ℕ, IsCoprimeE3Token x A p₁ p₂ p₃ := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 eventually_mtProposition22ZNat_facts
  have hpl : ∀ {C κ : ℝ} (m : ℕ), 0 ≤ C → 0 < κ →
      ∀ᶠ x : ℝ in atTop, C * Real.log x ^ m ≤ x ^ κ := by
    intro C κ m hC hκ
    filter_upwards [eventually_polylog_le_rpow m hC hκ, eventually_ge_atTop (1 : ℝ)] with x h hx
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    have hle : Real.log x ≤ 1 + Real.log (24 * x) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl hle m) hC) h
  filter_upwards [eventually_mtCoprimeE3Sum_ge hDI hW hB,
    Real.tendsto_log_atTop.eventually_ge_atTop 16,
    hpl (C := 64) 2 (by norm_num) (by norm_num : (0 : ℝ) < 1),
    hpl (C := 1) 2 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4),
    hpl (C := 2) 1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 6),
    hpl (C := 3) 1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 12),
    eventually_ge_atTop (max X₁ 1 ^ 2)] with x hsum hL16 h64 hL2x hL6 hL12 hxX
  intro A hA1 hAB
  have hx1 : 1 ≤ x := le_trans (one_le_pow₀ (le_max_right _ _)) hxX
  have hx0 : 0 < x := by linarith
  have hsxX : max X₁ 1 ≤ Real.sqrt x := (Real.le_sqrt (by positivity) hx0.le).2 hxX
  obtain ⟨-, -, -, hsX, -, -, -, -, -⟩ :=
    mt_all_interval_scale_X hx0 rfl hL16 (by norm_num : (1 : ℝ) ≤ 11 / 10) le_rfl rfl rfl
      (by simpa using h64)
  obtain ⟨hz2, hz6⟩ := hX₁ _ (by linarith [le_max_left X₁ 1])
  have hlogP0 : 0 < Real.log (Real.log x ^ (11 / 10 : ℝ)) := Real.log_pos (by
    have : Real.log x ≤ Real.log x ^ (11 / 10 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Real.log x)
        (by norm_num : (1 : ℝ) ≤ 11 / 10)
      rwa [Real.rpow_one] at this
    linarith)
  have hpos := lt_of_lt_of_le (by positivity) (hsum A hA1 hAB)
  obtain ⟨p₁, p₂, p₃, h₁, h₂, h₃, h12, h13, h23, hr⟩ := exists_coprime_threePrime_of_pos hx0 rfl hL16
    (by norm_num : (1 : ℝ) ≤ 11 / 10) le_rfl rfl (by positivity : (0 : ℝ) < 1 / 10 ^ 7)
    (by simpa using h64) (by simpa using hL2x) (by simpa using hL6) (by simpa using hL12) hz2 hz6 hpos
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hr
  exact ⟨p₁, p₂, p₃, h₁, h₂, h₃, h12, h13, h23, a1, a2, a3, a4, a5, a6,
    squarefree_mul_three_primes h₁ h₂ h₃ h12 h13 h23, a7, a8, a9⟩

end

end RHTower.Sieve
