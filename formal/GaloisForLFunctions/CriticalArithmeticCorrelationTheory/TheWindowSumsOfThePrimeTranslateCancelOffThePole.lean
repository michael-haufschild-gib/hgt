import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePrimeCrossOfAPrefixAndATopIsADirichletConvolution
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheWindowAverageOfAnAtomicTest
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs
import GaloisForLFunctions.RHTower.SecondMoment
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass
import Zeta23.FromPNTPlus.Mertens

/-!
# The window sums of the prime translate cancel off the pole

For a prefix vector `x` on `[1, M]` and its prime translate
`(a ∗ x)(n) = Σ_{k m = n} Λ(k) k^{−1/2} x(m)`, restricted to a top window `A ≤ n ≤ B`
(`topWeight`), the window sums `W(s) = Σ_{log n ∈ (s − h, s]} (a ∗ x)(n)` are
`W(s) = Σ_m x(m) Ψ(s, m)` with `Ψ(s, m) = Σ_{e^{s−h} < k m ≤ e^s} Λ(k) k^{−1/2}`
(`windowSum_topWeight_primeConv`). By the prime number theorem with de la Vallée Poussin error
(`exists_vonMangoldtAtom_window_error`), `Ψ(s, m) = √(e^s/m)(1 − e^{−h}) + O(√(e^s/m)(ε + h²))`
once `e^s/m ≥ K'`, so the long rows sum to `e^{s/2}(1 − e^{−h}) σ` with `σ = Σ x(m)/√m`, the
pairing with the pole profile, up to the error. Short rows `e^s < K' m` are counted order by
order. This gives the pointwise majorant `abs_sum_windowPrimeSum_le` and, integrated over
`log A ≤ s ≤ log B + h`,

`∫ W² ≤ 8 B e^h (h²σ² + h² P (1 + log 2K') + (4Cε + h²)² P H) + 8 (e^h − 1)(A + B) h² P H
  + 2 (Σ_{k<K'} Λ(k)/k) Σ_{k<K'} Λ(k) (h B e^h/k + 1) h P`   (`integral_windowSum_primeConv_sq_le`),

with `P = Σ x(m)²` and `H = Σ 1/m`: below the frequency `1/h` the prime translate is the pole
coefficient `σ` plus `O(log K')` times the prefix. Unsmoothed, the translate has
`Σ_{A ≤ n ≤ B} (a ∗ x)(n)² ≤ log B (log(2B/A) + 2(log 4 + 4)) P`
(`sum_sq_topWeight_primeConv_le`), from `Σ_{k | n} Λ(k) = log n` and Mertens.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset ArithmeticFunction RHTower

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

theorem vonMangoldtAtom_eq (k : ℕ) : vonMangoldtAtom k = (Λ k : ℝ) / Real.sqrt k := by
  unfold vonMangoldtAtom
  split_ifs with hk
  · rfl
  · interval_cases k <;> simp

theorem vonMangoldtAtom_sq (k : ℕ) : vonMangoldtAtom k ^ 2 = (Λ k : ℝ) * ((Λ k : ℝ) / k) := by
  rw [vonMangoldtAtom_eq, div_pow, Real.sq_sqrt (Nat.cast_nonneg k)]; ring

/-- `1` on the top window `A ≤ n ≤ B`. -/
def topWeight (A : ℝ) (B n : ℕ) : ℝ := if A ≤ n ∧ n ≤ B then 1 else 0

theorem topWeight_nonneg (A : ℝ) (B n : ℕ) : 0 ≤ topWeight A B n := by
  unfold topWeight; split_ifs <;> norm_num

theorem topWeight_le_one (A : ℝ) (B n : ℕ) : topWeight A B n ≤ 1 := by
  unfold topWeight; split_ifs <;> norm_num

/-- A product `k m` lies in the window `(s − h, s]` of `log` exactly when
`e^{s−h}/m < k ≤ e^s/m`. -/
theorem windowKernel_log_mul {h s : ℝ} {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) =
      if k ∈ Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊ then 1 else 0 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hkm : (0 : ℝ) < ((k * m : ℕ) : ℝ) := by
    have : 0 < k * m := Nat.mul_pos hk hm
    exact_mod_cast this
  have e1 : 0 ≤ s - Real.log ((k * m : ℕ) : ℝ) ↔ k ≤ ⌊Real.exp s / m⌋₊ := by
    rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hm0, sub_nonneg,
      ← Real.exp_le_exp, Real.exp_log hkm]
    push_cast; exact Iff.rfl
  have e2 : s - Real.log ((k * m : ℕ) : ℝ) < h ↔ ⌊Real.exp (s - h) / m⌋₊ < k := by
    rw [Nat.floor_lt (by positivity), div_lt_iff₀ hm0, sub_lt_comm,
      ← Real.exp_lt_exp, Real.exp_log hkm]
    push_cast; exact Iff.rfl
  unfold windowKernel
  by_cases hmem : k ∈ Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊
  · rw [if_pos hmem, Set.indicator_of_mem]
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hmem
    exact ⟨e1.mpr h2, e2.mpr h1⟩
  · rw [if_neg hmem, Set.indicator_of_notMem]
    rintro ⟨h1, h2⟩
    exact hmem (mem_Ioc.mpr ⟨e2.mp h2, e1.mp h1⟩)

/-- At most `h e^s/k + 1` multiples `k m` lie in the window `(s − h, s]` of `log`. -/
theorem sum_windowKernel_log_mul_le {h s : ℝ} (hh : 0 ≤ h) {k : ℕ} (hk : 1 ≤ k) (M : ℕ) :
    ∑ m ∈ Icc 1 M, windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) ≤
      h * Real.exp s / k + 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : ∑ m ∈ Icc 1 M, windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) ≤
      ((Ioc ⌊Real.exp (s - h) / k⌋₊ ⌊Real.exp s / k⌋₊).card : ℝ) := by
    calc ∑ m ∈ Icc 1 M, windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))
        = ∑ m ∈ Icc 1 M, if m ∈ Ioc ⌊Real.exp (s - h) / k⌋₊ ⌊Real.exp s / k⌋₊ then (1 : ℝ)
            else 0 := sum_congr rfl fun m hm => by
          rw [mul_comm k m]; exact windowKernel_log_mul (mem_Icc.mp hm).1 hk
      _ = ((Icc 1 M).filter (· ∈ Ioc ⌊Real.exp (s - h) / k⌋₊ ⌊Real.exp s / k⌋₊)).card := by
          rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]
      _ ≤ _ := by
          exact_mod_cast card_le_card fun m hm => (mem_filter.mp hm).2
  refine hsum.trans ?_
  rw [Nat.card_Ioc]
  have hfl1 := Nat.floor_le (show 0 ≤ Real.exp s / k by positivity)
  have hfl2 := Nat.lt_floor_add_one (Real.exp (s - h) / k)
  have hsub : ((⌊Real.exp s / k⌋₊ - ⌊Real.exp (s - h) / k⌋₊ : ℕ) : ℝ) ≤
      Real.exp s / k - Real.exp (s - h) / k + 1 := by
    rcases le_total ⌊Real.exp s / k⌋₊ ⌊Real.exp (s - h) / k⌋₊ with hle | hle
    · rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero]
      have : Real.exp (s - h) / k ≤ Real.exp s / k :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hk0.le
      linarith
    · rw [Nat.cast_sub hle]; linarith
  have hexp : Real.exp s - Real.exp (s - h) ≤ h * Real.exp s := by
    rw [Real.exp_sub]
    have h1 : 1 - h ≤ Real.exp (-h) := by linarith [Real.add_one_le_exp (-h)]
    have h2 : Real.exp s * (1 - h) ≤ Real.exp s * Real.exp (-h) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos s).le
    rw [Real.exp_neg] at h2
    rw [div_eq_mul_inv]; nlinarith [Real.exp_pos s]
  have : Real.exp s / k - Real.exp (s - h) / k ≤ h * Real.exp s / k := by
    rw [← sub_div]; exact div_le_div_of_nonneg_right hexp hk0.le
  linarith

/-- Mertens from above: `Σ_{k ≤ x} Λ(k)/k ≤ log x + log 4 + 4` for `x ≥ 1`. -/
theorem sum_vonMangoldt_div_Icc_floor_le' {x : ℝ} (hx : 1 ≤ x) :
    ∑ k ∈ Icc 1 ⌊x⌋₊, (Λ k : ℝ) / k ≤ Real.log x + (Real.log 4 + 4) := by
  have h := (abs_le.mp (Mertens.sum_mangoldt_div_eq_log hx)).2
  have hIoc : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  rw [hIoc] at h
  linarith

/-- Mertens from below: `log x − (log 4 + 4) ≤ Σ_{k ≤ x} Λ(k)/k` for `x ≥ 1`. -/
theorem log_sub_le_sum_vonMangoldt_div_Icc_floor {x : ℝ} (hx : 1 ≤ x) :
    Real.log x - (Real.log 4 + 4) ≤ ∑ k ∈ Icc 1 ⌊x⌋₊, (Λ k : ℝ) / k := by
  have h := (abs_le.mp (Mertens.sum_mangoldt_div_eq_log hx)).1
  have hIoc : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  rw [hIoc] at h
  linarith

/-- The prime reciprocal mass of a ratio window: `Σ_{A ≤ k m ≤ B} Λ(k)/k ≤ log(2B/A) + 2(log 4 + 4)`. -/
theorem sum_vonMangoldt_div_window_le {A : ℝ} (hA : 0 < A) {B m : ℕ} (hm : 1 ≤ m)
    (hAB : A ≤ B) :
    ∑ k ∈ (Icc 1 B).filter (fun k => A ≤ ((k * m : ℕ) : ℝ) ∧ k * m ≤ B), (Λ k : ℝ) / k ≤
      Real.log (2 * B / A) + 2 * (Real.log 4 + 4) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hB0 : (0 : ℝ) < B := hA.trans_le hAB
  have hnn : ∀ k, 0 ≤ (Λ k : ℝ) / k := fun k => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  have hC : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  set X : ℝ := (B : ℝ) / m
  set Y : ℝ := A / (2 * m)
  have hY0 : 0 < Y := by positivity
  have hXY : Y < X := by
    simp only [X, Y]
    rw [div_lt_div_iff₀ (by positivity) hm0]
    nlinarith
  -- the window lies in `(Y, X]`
  have hsub : (Icc 1 B).filter (fun k => A ≤ ((k * m : ℕ) : ℝ) ∧ k * m ≤ B) ⊆
      (Icc 1 ⌊X⌋₊).filter (fun k => ⌊Y⌋₊ < k) := by
    intro k hk
    obtain ⟨hkB, hA', hB'⟩ := by simpa only [mem_filter] using hk
    have hk1 := (mem_Icc.mp hkB).1
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hk1, ?_⟩, ?_⟩
    · rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hm0]
      exact_mod_cast hB'
    · rw [Nat.floor_lt hY0.le]
      have : A ≤ (k : ℝ) * m := by exact_mod_cast hA'
      simp only [Y]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
  have hX1 : 1 ≤ X ∨ X < 1 := le_or_gt 1 X
  calc ∑ k ∈ (Icc 1 B).filter (fun k => A ≤ ((k * m : ℕ) : ℝ) ∧ k * m ≤ B), (Λ k : ℝ) / k
      ≤ ∑ k ∈ (Icc 1 ⌊X⌋₊).filter (fun k => ⌊Y⌋₊ < k), (Λ k : ℝ) / k :=
        sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hnn k
    _ ≤ Real.log (2 * B / A) + 2 * (Real.log 4 + 4) := by
        rcases hX1 with hX1 | hX1
        · -- split off the head `k ≤ ⌊Y⌋`
          have hsplit := sum_filter_add_sum_filter_not (Icc 1 ⌊X⌋₊) (fun k => ⌊Y⌋₊ < k)
            (fun k => (Λ k : ℝ) / k)
          have hup := sum_vonMangoldt_div_Icc_floor_le' hX1
          have hhead : Real.log Y - (Real.log 4 + 4) ≤
              ∑ k ∈ (Icc 1 ⌊X⌋₊).filter (fun k => ¬ ⌊Y⌋₊ < k), (Λ k : ℝ) / k := by
            rcases le_or_gt 1 Y with hY1 | hY1
            · have hlo := log_sub_le_sum_vonMangoldt_div_Icc_floor hY1
              have heq : (Icc 1 ⌊X⌋₊).filter (fun k => ¬ ⌊Y⌋₊ < k) = Icc 1 ⌊Y⌋₊ := by
                ext k
                simp only [mem_filter, mem_Icc, not_lt]
                constructor
                · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
                · rintro ⟨h1, h3⟩
                  exact ⟨⟨h1, h3.trans (Nat.floor_le_floor hXY.le)⟩, h3⟩
              rw [heq]; exact hlo
            · have hlogY : Real.log Y < 0 := Real.log_neg hY0 hY1
              have := sum_nonneg fun k (_ : k ∈ (Icc 1 ⌊X⌋₊).filter (fun k => ¬ ⌊Y⌋₊ < k)) =>
                hnn k
              linarith
          have hlog : Real.log X - Real.log Y = Real.log (2 * B / A) := by
            rw [← Real.log_div (by positivity) hY0.ne']
            congr 1; simp only [X, Y]; field_simp
          linarith
        · -- `X < 1`: the sum is empty
          have hfl : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr hX1
          rw [hfl, Icc_eq_empty (by norm_num), filter_empty, sum_empty]
          have h2BA : 1 ≤ 2 * (B : ℝ) / A := by
            rw [le_div_iff₀ hA]; linarith
          have := Real.log_nonneg h2BA
          linarith

/-- The harmonic tail above `M/(2K)`: `Σ_{M/(2K) < m ≤ M} 1/m ≤ 1 + log(2K)`. -/
theorem sum_inv_filter_gt_le {M : ℕ} (hM : 1 ≤ M) {K : ℝ} (hK : 1 ≤ K) :
    ∑ m ∈ (Icc 1 M).filter (fun m : ℕ => (M : ℝ) / (2 * K) < m), (1 : ℝ) / m ≤
      1 + Real.log (2 * K) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set a := (M : ℝ) / (2 * K)
  have ha : 0 < a := by positivity
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 M) (fun m : ℕ => a < (m : ℝ))
    (fun m => (1 : ℝ) / m)
  have hhead : (Icc 1 M).filter (fun m : ℕ => ¬ a < (m : ℝ)) = Icc 1 ⌊a⌋₊ := by
    have haM : ⌊a⌋₊ ≤ M := by
      have : a ≤ M := by
        simp only [a]; rw [div_le_iff₀ (by positivity)]; nlinarith
      exact (Nat.floor_le_floor this).trans (Nat.floor_natCast M).le
    ext m
    simp only [mem_filter, mem_Icc, not_lt]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, Nat.le_floor h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3.trans haM⟩, (Nat.le_floor_iff ha.le).mp h3⟩
  rw [hhead] at hsplit
  have hup := RHTower.sum_Icc_one_div_le hM
  have hlo := RHTower.harmonic_Icc_ge_log ⌊a⌋₊
  have hfl : a ≤ (⌊a⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one a).le
  have hloga : Real.log a ≤ Real.log ((⌊a⌋₊ : ℝ) + 1) := Real.log_le_log ha hfl
  have hlog : Real.log M - Real.log a = Real.log (2 * K) := by
    rw [← Real.log_div hM0.ne' ha.ne']; congr 1; simp only [a]; field_simp
  have hsum : ∑ m ∈ (Icc 1 M).filter (fun m : ℕ => a < (m : ℝ)), (1 : ℝ) / m =
      ∑ m ∈ Icc 1 M, (1 : ℝ) / m - ∑ m ∈ Icc 1 ⌊a⌋₊, (1 : ℝ) / m := by linarith
  rw [hsum]
  linarith

/-- **The window sums of the prime translate.** With `ρ = 1_{[A, B]}` and orders below `K > B`,
`W(s) = Σ_m x(m) Σ_k Λ(k) k^{−1/2} ρ(k m) 1[log(k m) ∈ (s − h, s]]`. -/
theorem windowSum_topWeight_primeConv {A : ℝ} (hA : 1 ≤ A) {B K M : ℕ} (x : ℕ → ℝ) (h s : ℝ) :
    windowSum B (fun n => topWeight A B n * primeConv K M x n) h s =
      ∑ m ∈ Icc 1 M, x m * ∑ k ∈ range K, vonMangoldtAtom k * topWeight A B (k * m) *
        windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := by
  unfold windowSum primeConv
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm]
  rw [sum_comm (s := Icc 1 M)]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  have hite : ∀ n : ℕ, topWeight A B n * (if k * m = n then vonMangoldtAtom k * x m else 0) *
      windowKernel h (s - Real.log n) = if k * m = n then
        x m * (vonMangoldtAtom k * topWeight A B (k * m) *
          windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))) else 0 := by
    intro n; split_ifs with he
    · subst he; ring
    · ring
  rw [sum_congr rfl fun n _ => hite n, sum_ite_eq]
  split_ifs with hmem
  · rfl
  · have : topWeight A B (k * m) = 0 := by
      unfold topWeight
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hmem
      refine mem_Icc.mpr ⟨?_, h2⟩
      by_contra h0
      have : k * m = 0 := by omega
      rw [this, Nat.cast_zero] at h1
      linarith
    rw [this]; ring

/-! ### Short windows of primes -/

theorem exp_half_sub_one_le {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : Real.exp (h / 2) - 1 ≤ h := by
  have habs : |h / 2| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le habs)).2
  nlinarith

theorem one_sub_exp_neg_le (h : ℝ) : 1 - Real.exp (-h) ≤ h := by
  linarith [Real.add_one_le_exp (-h)]

theorem one_sub_exp_neg_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ 1 - Real.exp (-h) := by
  have : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- **Primes in a short window (de la Vallée Poussin).** For `Y = X e^{−h}` above the threshold,
`Σ_{Y < k ≤ X} Λ(k) k^{−1/2} = √X (1 − e^{−h}) + O(√X (e^{−c₀ √log Y} + h²))`. -/
theorem exists_vonMangoldtAtom_window_error :
    ∃ C c₀ t₀ : ℝ, 0 ≤ C ∧ 0 < c₀ ∧ 1 ≤ t₀ ∧ ∀ ⦃h X Y : ℝ⦄, 0 < h → h ≤ 1 →
      Y = X * Real.exp (-h) → t₀ ≤ Y →
      |∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k - Real.sqrt X * (1 - Real.exp (-h))| ≤
        Real.sqrt X * (4 * C * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2) := by
  obtain ⟨C, c₀, hc₀, hC, hev⟩ := exists_psi_error_eventually
  obtain ⟨t₁, ht₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨C, c₀, max t₁ 1, hC, hc₀, le_max_right _ _, ?_⟩
  intro h X Y hh hh1 hYX hY
  have hY1 : 1 ≤ Y := (le_max_right _ _).trans hY
  have heh : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hYX' : Y ≤ X := by
    rw [hYX]; have hX0 : 0 ≤ X := by
      by_contra hneg; push Not at hneg
      have : X * Real.exp (-h) < 0 := mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
      linarith
    exact mul_le_of_le_one_right hX0 heh
  have hX1 : 1 ≤ X := hY1.trans hYX'
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  set ε := Real.exp (-c₀ * Real.sqrt (Real.log Y))
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hεX : Real.exp (-c₀ * Real.sqrt (Real.log X)) ≤ ε := by
    apply Real.exp_le_exp.mpr
    have : Real.sqrt (Real.log Y) ≤ Real.sqrt (Real.log X) :=
      Real.sqrt_le_sqrt (Real.log_le_log hY0 hYX')
    nlinarith
  have hψX := ht₁ X ((le_max_left _ _).trans (hY.trans hYX'))
  have hψY := ht₁ Y ((le_max_left _ _).trans hY)
  -- the window sum of `Λ`
  have hfl : ⌊Y⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor hYX'
  have hS : ∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, (Λ k : ℝ) = Chebyshev.psi X - Chebyshev.psi Y := by
    unfold Chebyshev.psi
    rw [← sum_Ioc_consecutive _ (Nat.zero_le ⌊Y⌋₊) hfl]
    ring
  set S := ∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, (Λ k : ℝ)
  have hSerr : |S - (X - Y)| ≤ 2 * C * X * ε := by
    rw [hS]
    have h1 : |Chebyshev.psi X - X| ≤ C * X * ε := by
      refine hψX.trans ?_
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hεX (by positivity)
    have h2 : |Chebyshev.psi Y - Y| ≤ C * X * ε := by
      refine hψY.trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYX' hC) hε0
    have := abs_sub (Chebyshev.psi X - X) (Chebyshev.psi Y - Y)
    rw [show Chebyshev.psi X - Chebyshev.psi Y - (X - Y) =
      (Chebyshev.psi X - X) - (Chebyshev.psi Y - Y) by ring]
    linarith
  -- comparison of `k^{−1/2}` with `X^{−1/2}` and `Y^{−1/2}`
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hlo : S / Real.sqrt X ≤ ∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k := by
    rw [sum_div]
    refine sum_le_sum fun k hk => ?_
    rw [vonMangoldtAtom_eq]
    have hk0 : (0 : ℝ) < k := by
      have := (mem_Ioc.mp hk).1; exact_mod_cast (Nat.zero_lt_of_lt this)
    have hkX : (k : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).mp (mem_Ioc.mp hk).2
    exact div_le_div_of_nonneg_left vonMangoldt_nonneg (Real.sqrt_pos.mpr hk0)
      (Real.sqrt_le_sqrt hkX)
  have hhi : ∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k ≤ S / Real.sqrt Y := by
    rw [sum_div]
    refine sum_le_sum fun k hk => ?_
    rw [vonMangoldtAtom_eq]
    have hYk : Y < k := (Nat.floor_lt hY0.le).mp (mem_Ioc.mp hk).1
    exact div_le_div_of_nonneg_left vonMangoldt_nonneg hsY (Real.sqrt_le_sqrt hYk.le)
  have hsYX : Real.sqrt Y = Real.sqrt X * Real.exp (-h / 2) := by
    rw [hYX, Real.sqrt_mul hX0.le, show -h / 2 = (-h) / 2 by ring]
    congr 1
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have hΨ0 : Real.sqrt X * (1 - Real.exp (-h)) = (X - Y) / Real.sqrt X := by
    rw [hYX]
    field_simp
    rw [Real.sq_sqrt hX0.le]; ring
  have hXε : X * ε / Real.sqrt X = Real.sqrt X * ε := by
    rw [div_eq_iff hsX.ne', mul_assoc, mul_comm ε, ← mul_assoc, Real.mul_self_sqrt hX0.le]
  have hehalf : Real.exp (h / 2) ≤ 2 := by
    have := exp_half_sub_one_le hh.le hh1; linarith
  have hXY0 : 0 ≤ X - Y := by linarith
  rw [abs_le]
  constructor
  · -- lower bound
    have h1 : S / Real.sqrt X - (X - Y) / Real.sqrt X ≥ -(2 * C * X * ε) / Real.sqrt X := by
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp hSerr).1]) hsX.le
    have h2 : -(2 * C * X * ε) / Real.sqrt X = -(2 * C * (Real.sqrt X * ε)) := by
      rw [← hXε]; ring
    have h3 : 0 ≤ Real.sqrt X * (2 * C * ε + h ^ 2) := by positivity
    rw [hΨ0]
    nlinarith [hlo, h1, h2, h3]
  · -- upper bound
    have hSup : S ≤ (X - Y) + 2 * C * X * ε := by linarith [(abs_le.mp hSerr).2]
    have h1 : S / Real.sqrt Y ≤ ((X - Y) + 2 * C * X * ε) / Real.sqrt Y :=
      div_le_div_of_nonneg_right hSup hsY.le
    have h2 : ((X - Y) + 2 * C * X * ε) / Real.sqrt Y =
        Real.exp (h / 2) * ((X - Y) / Real.sqrt X) +
          Real.exp (h / 2) * (2 * C * (Real.sqrt X * ε)) := by
      rw [hsYX, ← hXε]
      have he : Real.exp (-h / 2) = (Real.exp (h / 2))⁻¹ := by
        rw [← Real.exp_neg]; ring_nf
      rw [he]
      field_simp
    have h3 : (Real.exp (h / 2) - 1) * ((X - Y) / Real.sqrt X) ≤ Real.sqrt X * h ^ 2 := by
      rw [← hΨ0]
      have ha := exp_half_sub_one_le hh.le hh1
      have hb := one_sub_exp_neg_le h
      have hc := one_sub_exp_neg_nonneg hh.le
      have hd : 0 ≤ Real.exp (h / 2) - 1 := by linarith [Real.one_le_exp (by linarith : 0 ≤ h / 2)]
      calc (Real.exp (h / 2) - 1) * (Real.sqrt X * (1 - Real.exp (-h)))
          = Real.sqrt X * ((Real.exp (h / 2) - 1) * (1 - Real.exp (-h))) := by ring
        _ ≤ Real.sqrt X * (h * h) := mul_le_mul_of_nonneg_left
            (mul_le_mul ha hb hc hh.le) hsX.le
        _ = Real.sqrt X * h ^ 2 := by ring
    have h4 : Real.exp (h / 2) * (2 * C * (Real.sqrt X * ε)) ≤ 4 * C * (Real.sqrt X * ε) := by
      have : 0 ≤ 2 * C * (Real.sqrt X * ε) := by positivity
      nlinarith
    rw [hΨ0]
    have : Real.sqrt X * (4 * C * ε + h ^ 2) = 4 * C * (Real.sqrt X * ε) + Real.sqrt X * h ^ 2 := by
      ring
    rw [this]
    nlinarith [hhi, h1, h2, h3, h4]

/-! ### The window prime sum of one prefix index -/

/-- `Ψ(s, m) = Σ_{k < K} Λ(k) k^{−1/2} ρ(k m) 1[log(k m) ∈ (s − h, s]]`. -/
def windowPrimeSum (A : ℝ) (B K : ℕ) (h s : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range K, vonMangoldtAtom k * topWeight A B (k * m) *
    windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))

theorem windowPrimeSum_nonneg (A : ℝ) (B K : ℕ) (h s : ℝ) (m : ℕ) :
    0 ≤ windowPrimeSum A B K h s m :=
  sum_nonneg fun k _ => mul_nonneg (mul_nonneg (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
    (topWeight_nonneg _ _ _)) (windowKernel_nonneg _ _)

theorem windowPrimeSum_term {A : ℝ} {B : ℕ} {h s : ℝ} {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    vonMangoldtAtom k * topWeight A B (k * m) * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) =
      if k ∈ Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊ then
        vonMangoldtAtom k * topWeight A B (k * m) else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : vonMangoldtAtom 0 = 0 := by rw [vonMangoldtAtom_eq]; simp
    rw [this]; simp
  · rw [windowKernel_log_mul hk hm]; split_ifs <;> ring

theorem windowPrimeSum_le_all {A : ℝ} {B K : ℕ} {h s : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    windowPrimeSum A B K h s m ≤
      ∑ k ∈ Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊, vonMangoldtAtom k := by
  unfold windowPrimeSum
  simp_rw [windowPrimeSum_term hm]
  rw [← sum_filter]
  calc ∑ k ∈ (range K).filter (· ∈ Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊),
        vonMangoldtAtom k * topWeight A B (k * m)
      ≤ ∑ k ∈ (range K).filter (· ∈ Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊),
          vonMangoldtAtom k := sum_le_sum fun k _ =>
        mul_le_of_le_one_right (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
          (topWeight_le_one _ _ _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun k hk => (mem_filter.mp hk).2)
        fun k _ _ => SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k

/-- Inside the top window every order of the window is counted with weight one. -/
theorem windowPrimeSum_eq_all {A : ℝ} {B K : ℕ} {h s : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hAs : A ≤ Real.exp (s - h)) (hsB : Real.exp s ≤ B) (hBK : B < K) :
    windowPrimeSum A B K h s m =
      ∑ k ∈ Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊, vonMangoldtAtom k := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold windowPrimeSum
  simp_rw [windowPrimeSum_term hm]
  rw [← sum_filter]
  have hfilt : (range K).filter (· ∈ Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊) =
      Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊ := by
    ext k
    simp only [mem_filter, mem_range, and_iff_right_iff_imp]
    intro hk
    have hkX : (k : ℝ) ≤ Real.exp s / m := (Nat.le_floor_iff (by positivity)).mp (mem_Ioc.mp hk).2
    have : (k : ℝ) ≤ B := hkX.trans ((div_le_self (Real.exp_pos s).le
      (by exact_mod_cast hm)).trans hsB)
    have : k ≤ B := by exact_mod_cast this
    omega
  rw [hfilt]
  refine sum_congr rfl fun k hk => ?_
  have hkY : Real.exp (s - h) / m < k := (Nat.floor_lt (by positivity)).mp (mem_Ioc.mp hk).1
  have hkX : (k : ℝ) ≤ Real.exp s / m := (Nat.le_floor_iff (by positivity)).mp (mem_Ioc.mp hk).2
  have h1 : A ≤ ((k * m : ℕ) : ℝ) := by
    push_cast
    have := (div_lt_iff₀ hm0).mp hkY
    linarith
  have h2 : k * m ≤ B := by
    have : (k : ℝ) * m ≤ B := by
      have := (le_div_iff₀ hm0).mp hkX
      linarith
    exact_mod_cast this
  unfold topWeight
  rw [if_pos ⟨h1, h2⟩, mul_one]

/-- Short rows `e^s < K' m` only see orders below `K'`. -/
theorem windowPrimeSum_le_short {A : ℝ} {B K K' : ℕ} {h s : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hshort : Real.exp s < K' * m) :
    windowPrimeSum A B K h s m ≤
      ∑ k ∈ range K', vonMangoldtAtom k * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold windowPrimeSum
  have hterm : ∀ k ∈ range K, vonMangoldtAtom k * topWeight A B (k * m) *
      windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) ≤
      if k < K' then vonMangoldtAtom k * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) else 0 := by
    intro k _
    have hb : vonMangoldtAtom k * topWeight A B (k * m) *
        windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) ≤
        vonMangoldtAtom k * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := by
      have := mul_le_of_le_one_right (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
        (topWeight_le_one A B (k * m))
      exact mul_le_mul_of_nonneg_right this (windowKernel_nonneg _ _)
    split_ifs with hk
    · exact hb
    · rcases Nat.eq_zero_or_pos k with rfl | hk1
      · have : vonMangoldtAtom 0 = 0 := by rw [vonMangoldtAtom_eq]; simp
        rw [this]; simp
      · rw [windowKernel_log_mul hk1 hm]
        split_ifs with hmem
        · exfalso
          have hkX : (k : ℝ) ≤ Real.exp s / m :=
            (Nat.le_floor_iff (by positivity)).mp (mem_Ioc.mp hmem).2
          have : (k : ℝ) * m < K' * m := by
            have := (le_div_iff₀ hm0).mp hkX; linarith
          have : (k : ℝ) < K' := lt_of_mul_lt_mul_right this hm0.le
          exact hk (by exact_mod_cast this)
        · simp
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter]
  refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ =>
    mul_nonneg (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k) (windowKernel_nonneg _ _)
  exact mem_range.mpr (mem_filter.mp hk).2

/-- Cauchy–Schwarz against the harmonic weight. -/
theorem sum_abs_div_sqrt_le (S' : Finset ℕ) (x : ℕ → ℝ) :
    ∑ m ∈ S', |x m| / Real.sqrt m ≤ Real.sqrt ((∑ m ∈ S', x m ^ 2) * ∑ m ∈ S', (1 : ℝ) / m) := by
  apply Real.le_sqrt_of_sq_le
  have h := sum_mul_sq_le_sq_mul_sq S' (fun m => |x m|) (fun m => 1 / Real.sqrt m)
  have e1 : ∀ m, |x m| * (1 / Real.sqrt m) = |x m| / Real.sqrt m := fun m => by ring
  have e2 : ∀ m : ℕ, (1 / Real.sqrt m) ^ 2 = (1 : ℝ) / m := fun m => by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg m), one_pow]
  simp only [e1, e2, sq_abs] at h
  exact h

theorem sqrt_mul_sum_le_of_subset {S' : Finset ℕ} {M : ℕ} (hS : S' ⊆ Icc 1 M) (x : ℕ → ℝ) :
    Real.sqrt ((∑ m ∈ S', x m ^ 2) * ∑ m ∈ S', (1 : ℝ) / m) ≤
      Real.sqrt ((∑ m ∈ Icc 1 M, x m ^ 2) * ∑ m ∈ Icc 1 M, (1 : ℝ) / m) := by
  apply Real.sqrt_le_sqrt
  have hinv : ∀ m : ℕ, 0 ≤ (1 : ℝ) / m := fun m => by positivity
  exact mul_le_mul
    (sum_le_sum_of_subset_of_nonneg hS fun m _ _ => sq_nonneg _)
    (sum_le_sum_of_subset_of_nonneg hS fun m _ _ => hinv m)
    (sum_nonneg fun m _ => hinv m) (sum_nonneg fun m _ => sq_nonneg _)

/-- **Pointwise majorant of the window sums of the prime translate.** Writing
`P = Σ x(m)²`, `H = Σ 1/m` and `σ = Σ x(m)/√m`, for `e^s ≥ A`:
`|W(s)| ≤ e^{s/2} (h|σ| + h √(P(1 + log 2K')) + (4Cε + h²)√(PH) + 1_{edge}(s) h √(PH))
  + Σ_{k < K'} Λ(k) k^{−1/2} Σ_m |x(m)| 1[log(k m) ∈ (s − h, s]]`:
the coherent part carries `σ`, long rows `e^s ≥ K' m` pay the prime number theorem error, and
short rows are counted order by order. -/
theorem abs_sum_windowPrimeSum_le {C c₀ t₀ : ℝ} (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hpnt : ∀ ⦃h X Y : ℝ⦄, 0 < h → h ≤ 1 → Y = X * Real.exp (-h) → t₀ ≤ Y →
      |∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k - Real.sqrt X * (1 - Real.exp (-h))| ≤
        Real.sqrt X * (4 * C * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2))
    {A : ℝ} {B K M K' : ℕ} {h s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 1 ≤ M) (hMA : (M : ℝ) ≤ 2 * A) (hBK : B < K) (hK' : 1 ≤ K')
    (ht₀ : t₀ ≤ K' * Real.exp (-1)) (hAs : A ≤ Real.exp s) (x : ℕ → ℝ) :
    |∑ m ∈ Icc 1 M, x m * windowPrimeSum A B K h s m| ≤
      Real.sqrt (Real.exp s) * (h * |∑ m ∈ Icc 1 M, x m / Real.sqrt m| +
        h * Real.sqrt ((∑ m ∈ Icc 1 M, x m ^ 2) * (1 + Real.log (2 * K'))) +
        (4 * C * Real.exp (-c₀ * Real.sqrt (Real.log (K' * Real.exp (-1)))) + h ^ 2) *
          Real.sqrt ((∑ m ∈ Icc 1 M, x m ^ 2) * ∑ m ∈ Icc 1 M, (1 : ℝ) / m) +
        (if A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B then 0 else 1) * h *
          Real.sqrt ((∑ m ∈ Icc 1 M, x m ^ 2) * ∑ m ∈ Icc 1 M, (1 : ℝ) / m)) +
      ∑ k ∈ range K', vonMangoldtAtom k *
        ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := by
  set P := ∑ m ∈ Icc 1 M, x m ^ 2
  set H := ∑ m ∈ Icc 1 M, (1 : ℝ) / m
  set σ := ∑ m ∈ Icc 1 M, x m / Real.sqrt m
  set ε := Real.exp (-c₀ * Real.sqrt (Real.log (K' * Real.exp (-1))))
  set E := Real.sqrt (Real.exp s)
  set ψ := fun m => windowPrimeSum A B K h s m
  set Ψa := fun m : ℕ => ∑ k ∈ Ioc ⌊Real.exp (s - h) / m⌋₊ ⌊Real.exp s / m⌋₊, vonMangoldtAtom k
  set Ψ₀ := fun m : ℕ => E * (1 - Real.exp (-h)) / Real.sqrt m
  set shortS := (Icc 1 M).filter (fun m : ℕ => Real.exp s < K' * m)
  set longS := (Icc 1 M).filter (fun m : ℕ => ¬ Real.exp s < K' * m)
  have hE : 0 < E := Real.sqrt_pos.mpr (Real.exp_pos s)
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hH : 0 ≤ H := sum_nonneg fun m _ => by positivity
  have hε : 0 ≤ ε := (Real.exp_pos _).le
  have heh := one_sub_exp_neg_le h
  have heh0 := one_sub_exp_neg_nonneg hh.le
  have hK'0 : (0 : ℝ) < K' := by exact_mod_cast hK'
  have hA0 : 0 < A := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hsubS : shortS ⊆ Icc 1 M := filter_subset _ _
  have hsubL : longS ⊆ Icc 1 M := filter_subset _ _
  have hψ0 : ∀ m, 0 ≤ ψ m := fun m => windowPrimeSum_nonneg A B K h s m
  have hψa : ∀ m ∈ Icc 1 M, ψ m ≤ Ψa m := fun m hm => windowPrimeSum_le_all (mem_Icc.mp hm).1
  have hΨ₀ : ∀ m, 0 ≤ Ψ₀ m := fun m => by
    simp only [Ψ₀]; exact div_nonneg (mul_nonneg hE.le heh0) (Real.sqrt_nonneg _)
  -- the window prime number theorem on long rows
  have hlong : ∀ m ∈ longS, |Ψa m - Ψ₀ m| ≤ (4 * C * ε + h ^ 2) * (1 / Real.sqrt m) * E := by
    intro m hm
    obtain ⟨hmI, hml⟩ := mem_filter.mp hm
    have hm1 := (mem_Icc.mp hmI).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    push Not at hml
    set X := Real.exp s / m
    set Y := Real.exp (s - h) / m
    have hYX : Y = X * Real.exp (-h) := by
      simp only [X, Y]; rw [Real.exp_sub, Real.exp_neg]; ring
    have hXK : (K' : ℝ) ≤ X := by rw [le_div_iff₀ hm0]; exact hml
    have hYK : (K' : ℝ) * Real.exp (-1) ≤ Y := by
      rw [hYX]
      exact mul_le_mul hXK (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        (hK'0.le.trans hXK)
    have hb := hpnt hh hh1 hYX (ht₀.trans hYK)
    have hεY : Real.exp (-c₀ * Real.sqrt (Real.log Y)) ≤ ε := by
      apply Real.exp_le_exp.mpr
      have : Real.sqrt (Real.log (K' * Real.exp (-1))) ≤ Real.sqrt (Real.log Y) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by positivity) hYK)
      nlinarith
    have hsX : Real.sqrt X = E * (1 / Real.sqrt m) := by
      simp only [X, E]; rw [Real.sqrt_div (Real.exp_pos s).le]; ring
    have hΨ₀m : Ψ₀ m = Real.sqrt X * (1 - Real.exp (-h)) := by
      simp only [Ψ₀]; rw [hsX]; ring
    have hΨam : Ψa m = ∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k := rfl
    rw [hΨam, hΨ₀m]
    refine hb.trans ?_
    rw [hsX]
    have : 4 * C * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2 ≤ 4 * C * ε + h ^ 2 := by
      nlinarith
    have hpos : 0 ≤ E * (1 / Real.sqrt m) := by positivity
    calc E * (1 / Real.sqrt m) * (4 * C * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2)
        ≤ E * (1 / Real.sqrt m) * (4 * C * ε + h ^ 2) := mul_le_mul_of_nonneg_left this hpos
      _ = (4 * C * ε + h ^ 2) * (1 / Real.sqrt m) * E := by ring
  -- the coherent part
  have hcoh : ∑ m ∈ Icc 1 M, x m * Ψ₀ m = E * (1 - Real.exp (-h)) * σ := by
    simp only [Ψ₀, σ, mul_sum]
    exact sum_congr rfl fun m _ => by ring
  -- weighted Cauchy–Schwarz bounds
  have hCS : ∀ S' ⊆ Icc 1 M, ∑ m ∈ S', |x m| * (1 / Real.sqrt m) ≤ Real.sqrt (P * H) := by
    intro S' hS'
    have := sum_abs_div_sqrt_le S' x
    simp only [mul_one_div]
    exact this.trans (sqrt_mul_sum_le_of_subset hS' x)
  have hshortH : ∑ m ∈ shortS, (1 : ℝ) / m ≤ 1 + Real.log (2 * K') := by
    have hsub : shortS ⊆ (Icc 1 M).filter (fun m : ℕ => (M : ℝ) / (2 * K') < m) := by
      intro m hm
      obtain ⟨hmI, hms⟩ := mem_filter.mp hm
      refine mem_filter.mpr ⟨hmI, ?_⟩
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    exact (sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity).trans
      (sum_inv_filter_gt_le hM (by exact_mod_cast hK'))
  have hshortCS : ∑ m ∈ shortS, |x m| * (1 / Real.sqrt m) ≤
      Real.sqrt (P * (1 + Real.log (2 * K'))) := by
    have := sum_abs_div_sqrt_le shortS x
    simp only [mul_one_div]
    refine this.trans (Real.sqrt_le_sqrt (mul_le_mul
      (sum_le_sum_of_subset_of_nonneg hsubS fun m _ _ => sq_nonneg _) hshortH
      (sum_nonneg fun m _ => by positivity) hP))
  -- short rows, order by order
  have hshort : ∑ m ∈ shortS, |x m| * ψ m ≤ ∑ k ∈ range K', vonMangoldtAtom k *
      ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := by
    calc ∑ m ∈ shortS, |x m| * ψ m
        ≤ ∑ m ∈ shortS, |x m| * ∑ k ∈ range K', vonMangoldtAtom k *
            windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) :=
          sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
            (windowPrimeSum_le_short (mem_Icc.mp (mem_filter.mp hm).1).1 (mem_filter.mp hm).2)
            (abs_nonneg _)
      _ ≤ ∑ m ∈ Icc 1 M, |x m| * ∑ k ∈ range K', vonMangoldtAtom k *
            windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg hsubS fun m _ _ => mul_nonneg (abs_nonneg _)
            (sum_nonneg fun k _ => mul_nonneg (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
              (windowKernel_nonneg _ _))
      _ = _ := by
          simp_rw [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
  have hshortΨ₀ : ∑ m ∈ shortS, |x m| * Ψ₀ m ≤
      E * h * Real.sqrt (P * (1 + Real.log (2 * K'))) := by
    have e : ∀ m, |x m| * Ψ₀ m = E * (1 - Real.exp (-h)) * (|x m| * (1 / Real.sqrt m)) :=
      fun m => by simp only [Ψ₀]; ring
    simp_rw [e]
    rw [← mul_sum]
    exact mul_le_mul (mul_le_mul_of_nonneg_left heh hE.le) hshortCS
      (sum_nonneg fun m _ => by positivity) (by positivity)
  have hlongB : ∑ m ∈ longS, |x m| * |Ψa m - Ψ₀ m| ≤
      E * (4 * C * ε + h ^ 2) * Real.sqrt (P * H) := by
    calc ∑ m ∈ longS, |x m| * |Ψa m - Ψ₀ m|
        ≤ ∑ m ∈ longS, |x m| * ((4 * C * ε + h ^ 2) * (1 / Real.sqrt m) * E) :=
          sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hlong m hm) (abs_nonneg _)
      _ = E * (4 * C * ε + h ^ 2) * ∑ m ∈ longS, |x m| * (1 / Real.sqrt m) := by
          rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
      _ ≤ E * (4 * C * ε + h ^ 2) * Real.sqrt (P * H) :=
          mul_le_mul_of_nonneg_left (hCS longS hsubL) (by positivity)
  have hallΨ₀ : ∑ m ∈ Icc 1 M, |x m| * Ψ₀ m ≤ E * h * Real.sqrt (P * H) := by
    have e : ∀ m, |x m| * Ψ₀ m = E * (1 - Real.exp (-h)) * (|x m| * (1 / Real.sqrt m)) :=
      fun m => by simp only [Ψ₀]; ring
    simp_rw [e]
    rw [← mul_sum]
    exact mul_le_mul (mul_le_mul_of_nonneg_left heh hE.le) (hCS _ subset_rfl)
      (sum_nonneg fun m _ => by positivity) (by positivity)
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 M) (fun m : ℕ => Real.exp s < K' * m)
    (fun m => x m * ψ m)
  have habsShort : |∑ m ∈ shortS, x m * ψ m| ≤ ∑ m ∈ shortS, |x m| * ψ m := by
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun m _ => ?_))
    rw [abs_mul, abs_of_nonneg (hψ0 m)]
  have hT0 : 0 ≤ ∑ k ∈ range K', vonMangoldtAtom k *
      ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) :=
    sum_nonneg fun k _ => mul_nonneg (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
      (sum_nonneg fun m _ => mul_nonneg (abs_nonneg _) (windowKernel_nonneg _ _))
  have hPH : 0 ≤ Real.sqrt (P * H) := Real.sqrt_nonneg _
  have hPK : 0 ≤ Real.sqrt (P * (1 + Real.log (2 * K'))) := Real.sqrt_nonneg _
  have hσ : 0 ≤ |σ| := abs_nonneg σ
  change |∑ m ∈ Icc 1 M, x m * ψ m| ≤ E * (h * |σ| + h * Real.sqrt (P * (1 + Real.log (2 * K'))) +
      (4 * C * ε + h ^ 2) * Real.sqrt (P * H) +
      (if A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B then 0 else 1) * h * Real.sqrt (P * H)) +
    ∑ k ∈ range K', vonMangoldtAtom k *
      ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))
  by_cases hint : A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B
  · rw [if_pos hint, zero_mul, zero_mul, add_zero]
    have heq : ∀ m ∈ Icc 1 M, ψ m = Ψa m := fun m hm =>
      windowPrimeSum_eq_all (mem_Icc.mp hm).1 hint.1 hint.2 hBK
    -- `W = coherent − short model + short + long deviation`
    have hdec : ∑ m ∈ Icc 1 M, x m * ψ m =
        E * (1 - Real.exp (-h)) * σ - ∑ m ∈ shortS, x m * Ψ₀ m +
          ∑ m ∈ shortS, x m * ψ m + ∑ m ∈ longS, x m * (Ψa m - Ψ₀ m) := by
      have hs2 := sum_filter_add_sum_filter_not (Icc 1 M) (fun m : ℕ => Real.exp s < K' * m)
        (fun m => x m * Ψ₀ m)
      have hlongeq : ∑ m ∈ longS, x m * ψ m = ∑ m ∈ longS, x m * Ψa m :=
        sum_congr rfl fun m hm => by rw [heq m (hsubL hm)]
      have hlongsub : ∑ m ∈ longS, x m * (Ψa m - Ψ₀ m) =
          ∑ m ∈ longS, x m * Ψa m - ∑ m ∈ longS, x m * Ψ₀ m := by
        rw [← sum_sub_distrib]; exact sum_congr rfl fun m _ => by ring
      rw [← hcoh]
      change ∑ m ∈ Icc 1 M, x m * ψ m = ∑ m ∈ Icc 1 M, x m * Ψ₀ m -
        ∑ m ∈ shortS, x m * Ψ₀ m + ∑ m ∈ shortS, x m * ψ m +
        ∑ m ∈ longS, x m * (Ψa m - Ψ₀ m)
      linarith
    rw [hdec]
    have h1 : |E * (1 - Real.exp (-h)) * σ| ≤ E * h * |σ| := by
      rw [abs_mul, abs_mul, abs_of_pos hE, abs_of_nonneg heh0]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heh hE.le) hσ
    have h2 : |∑ m ∈ shortS, x m * Ψ₀ m| ≤ E * h * Real.sqrt (P * (1 + Real.log (2 * K'))) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans (le_of_eq (sum_congr rfl fun m _ => ?_)) hshortΨ₀
      rw [abs_mul, abs_of_nonneg (hΨ₀ m)]
    have h3 : |∑ m ∈ longS, x m * (Ψa m - Ψ₀ m)| ≤ E * (4 * C * ε + h ^ 2) * Real.sqrt (P * H) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans (le_of_eq (sum_congr rfl fun m _ => ?_)) hlongB
      rw [abs_mul]
    have htri : |E * (1 - Real.exp (-h)) * σ - ∑ m ∈ shortS, x m * Ψ₀ m +
        ∑ m ∈ shortS, x m * ψ m + ∑ m ∈ longS, x m * (Ψa m - Ψ₀ m)| ≤
        |E * (1 - Real.exp (-h)) * σ| + |∑ m ∈ shortS, x m * Ψ₀ m| +
          |∑ m ∈ shortS, x m * ψ m| + |∑ m ∈ longS, x m * (Ψa m - Ψ₀ m)| := by
      have t1 := abs_add_le (E * (1 - Real.exp (-h)) * σ - ∑ m ∈ shortS, x m * Ψ₀ m +
        ∑ m ∈ shortS, x m * ψ m) (∑ m ∈ longS, x m * (Ψa m - Ψ₀ m))
      have t2 := abs_add_le (E * (1 - Real.exp (-h)) * σ - ∑ m ∈ shortS, x m * Ψ₀ m)
        (∑ m ∈ shortS, x m * ψ m)
      have t3 := abs_sub (E * (1 - Real.exp (-h)) * σ) (∑ m ∈ shortS, x m * Ψ₀ m)
      linarith
    have hexpand : E * (h * |σ| + h * Real.sqrt (P * (1 + Real.log (2 * K'))) +
        (4 * C * ε + h ^ 2) * Real.sqrt (P * H)) = E * h * |σ| +
        E * h * Real.sqrt (P * (1 + Real.log (2 * K'))) +
        E * (4 * C * ε + h ^ 2) * Real.sqrt (P * H) := by ring
    linarith [htri, h1, h2, h3, habsShort, hshort, hexpand]
  · rw [if_neg hint, one_mul]
    have hlongψ : |∑ m ∈ longS, x m * ψ m| ≤ E * h * Real.sqrt (P * H) +
        E * (4 * C * ε + h ^ 2) * Real.sqrt (P * H) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hpt : ∀ m ∈ longS, |x m * ψ m| ≤ |x m| * Ψ₀ m + |x m| * |Ψa m - Ψ₀ m| := by
        intro m hm
        rw [abs_mul, abs_of_nonneg (hψ0 m), ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have := hψa m (hsubL hm)
        have := le_abs_self (Ψa m - Ψ₀ m)
        linarith
      refine (sum_le_sum hpt).trans ?_
      rw [sum_add_distrib]
      refine add_le_add ?_ hlongB
      exact (sum_le_sum_of_subset_of_nonneg hsubL fun m _ _ =>
        mul_nonneg (abs_nonneg _) (hΨ₀ m)).trans hallΨ₀
    have htot : |∑ m ∈ Icc 1 M, x m * ψ m| ≤
        |∑ m ∈ shortS, x m * ψ m| + |∑ m ∈ longS, x m * ψ m| := by
      rw [← hsplit]; exact abs_add_le _ _
    have hE0 : 0 ≤ E * h * |σ| := by positivity
    have hE1 : 0 ≤ E * h * Real.sqrt (P * (1 + Real.log (2 * K'))) := by positivity
    have hexpand : E * (h * |σ| + h * Real.sqrt (P * (1 + Real.log (2 * K'))) +
        (4 * C * ε + h ^ 2) * Real.sqrt (P * H) + h * Real.sqrt (P * H)) = E * h * |σ| +
        E * h * Real.sqrt (P * (1 + Real.log (2 * K'))) +
        E * (4 * C * ε + h ^ 2) * Real.sqrt (P * H) + E * h * Real.sqrt (P * H) := by ring
    linarith [htot, habsShort, hshort, hlongψ, hE0, hE1, hexpand]

/-! ### Integrating the majorant -/

theorem integral_exp_Icc {a b : ℝ} (hab : a ≤ b) :
    ∫ s in Set.Icc a b, Real.exp s = Real.exp b - Real.exp a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_exp]

theorem windowKernel_mul_self (h t : ℝ) : windowKernel h t * windowKernel h t = windowKernel h t := by
  unfold windowKernel
  by_cases ht : t ∈ Set.Ico 0 h
  · rw [Set.indicator_of_mem ht]; ring
  · rw [Set.indicator_of_notMem ht]; ring

theorem integral_windowKernel_sub {h : ℝ} (hh : 0 ≤ h) (c : ℝ) :
    ∫ s, windowKernel h (s - c) = h := by
  rw [integral_sub_right_eq_self (fun s => windowKernel h s) c]
  unfold windowKernel
  rw [integral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith), sub_zero]

/-- Cauchy–Schwarz over the prime orders: `(Σ Λ(k) k^{−1/2} u_k)² ≤ (Σ Λ(k)/k)(Σ Λ(k) u_k²)`. -/
theorem sq_sum_vonMangoldtAtom_mul_le (S' : Finset ℕ) (u : ℕ → ℝ) :
    (∑ k ∈ S', vonMangoldtAtom k * u k) ^ 2 ≤
      (∑ k ∈ S', (Λ k : ℝ) / k) * ∑ k ∈ S', (Λ k : ℝ) * u k ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq S' (fun k => Real.sqrt ((Λ k : ℝ) / k))
    (fun k => Real.sqrt (Λ k : ℝ) * u k)
  have e1 : ∀ k, Real.sqrt ((Λ k : ℝ) / k) * (Real.sqrt (Λ k : ℝ) * u k) =
      vonMangoldtAtom k * u k := fun k => by
    rw [vonMangoldtAtom_eq, ← mul_assoc, ← Real.sqrt_mul
      (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)), div_mul_eq_mul_div,
      Real.sqrt_div (mul_self_nonneg _), Real.sqrt_mul_self vonMangoldt_nonneg]
  have e2 : ∀ k, Real.sqrt ((Λ k : ℝ) / k) ^ 2 = (Λ k : ℝ) / k := fun k =>
    Real.sq_sqrt (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
  have e3 : ∀ k, (Real.sqrt (Λ k : ℝ) * u k) ^ 2 = (Λ k : ℝ) * u k ^ 2 := fun k => by
    rw [mul_pow, Real.sq_sqrt vonMangoldt_nonneg]
  simp only [e1, e2, e3] at h
  exact h

/-- `(E(a + b + c + d) + T)² ≤ 8E²(a² + b² + c² + d²) + 2T²`. -/
theorem sq_le_of_abs_le_four_add {W E a b c d T : ℝ} (hW : |W| ≤ E * (a + b + c + d) + T) :
    W ^ 2 ≤ 8 * E ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + 2 * T ^ 2 := by
  have h1 : W ^ 2 ≤ (E * (a + b + c + d) + T) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hW 2
  have h2 : (E * (a + b + c + d) + T) ^ 2 ≤ 2 * (E * (a + b + c + d)) ^ 2 + 2 * T ^ 2 := by
    nlinarith [sq_nonneg (E * (a + b + c + d) - T)]
  have h3 : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
      sq_nonneg (b - d), sq_nonneg (c - d)]
  have h4 : (E * (a + b + c + d)) ^ 2 ≤ E ^ 2 * (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left h3 (sq_nonneg E)
  linarith

/-- The short-order square function `Σ_{k<K'} Λ(k)(h B'/k + 1) Σ_m x(m)² 1[log(km) ∈ (s−h, s]]`. -/
def shortWindowSq (K' M : ℕ) (x : ℕ → ℝ) (B' h s : ℝ) : ℝ :=
  ∑ k ∈ range K', (Λ k : ℝ) * (h * B' / k + 1) *
    ∑ m ∈ Icc 1 M, x m ^ 2 * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))

/-- The short orders, squared: `T(s)² ≤ (Σ_{k<K'} Λ(k)/k) · shortWindowSq` once `e^s ≤ B'`. -/
theorem sq_shortOrders_le {K' M : ℕ} (x : ℕ → ℝ) {h s B' : ℝ} (hh : 0 ≤ h)
    (hsB : Real.exp s ≤ B') :
    (∑ k ∈ range K', vonMangoldtAtom k *
        ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))) ^ 2 ≤
      (∑ k ∈ range K', (Λ k : ℝ) / k) * shortWindowSq K' M x B' h s := by
  refine (sq_sum_vonMangoldtAtom_mul_le (range K') _).trans ?_
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => ?_)
    (sum_nonneg fun k _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [ArithmeticFunction.map_zero, Nat.cast_zero, zero_mul, le_refl]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 M)
    (fun m => windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)))
    (fun m => |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)))
  have e1 : ∀ m, windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) *
      (|x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))) =
      |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := fun m => by
    rw [mul_left_comm, windowKernel_mul_self]
  have e2 : ∀ m, windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) ^ 2 =
      windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := fun m => by
    rw [sq, windowKernel_mul_self]
  have e3 : ∀ m, (|x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))) ^ 2 =
      x m ^ 2 * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := fun m => by
    rw [mul_pow, sq_abs, e2]
  simp only [e1, e2, e3] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun m _ =>
    mul_nonneg (sq_nonneg _) (windowKernel_nonneg _ _)))
  have hcnt := sum_windowKernel_log_mul_le (s := s) hh hk M
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  refine hcnt.trans (add_le_add ?_ le_rfl)
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsB hk0.le) hh

/-- The edge of the top window, `log A ≤ s < log A + h` or `log B < s ≤ log B + h`. -/
theorem edge_mul_exp_le {A : ℝ} {B : ℕ} (hB0 : (0 : ℝ) < B) {h s : ℝ}
    (hs1 : Real.log A ≤ s) (hs2 : s ≤ Real.log B + h) :
    (if A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B then (0 : ℝ) else 1) * Real.exp s ≤
      (Set.Icc (Real.log A) (Real.log A + h)).indicator Real.exp s +
        (Set.Icc (Real.log (B : ℝ)) (Real.log B + h)).indicator Real.exp s := by
  have hi1 : 0 ≤ (Set.Icc (Real.log A) (Real.log A + h)).indicator Real.exp s :=
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) s
  have hi2 : 0 ≤ (Set.Icc (Real.log (B : ℝ)) (Real.log B + h)).indicator Real.exp s :=
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) s
  by_cases hint : A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B
  · rw [if_pos hint, zero_mul]; linarith
  · rw [if_neg hint, one_mul]
    rw [not_and_or] at hint
    rcases hint with hlow | hhigh
    · push Not at hlow
      have hm : s ∈ Set.Icc (Real.log A) (Real.log A + h) := by
        refine ⟨hs1, ?_⟩
        have := Real.log_lt_log (Real.exp_pos _) hlow
        rw [Real.log_exp] at this; linarith
      rw [Set.indicator_of_mem hm]; linarith
    · push Not at hhigh
      have hm : s ∈ Set.Icc (Real.log (B : ℝ)) (Real.log B + h) := by
        refine ⟨?_, hs2⟩
        have := Real.log_lt_log hB0 hhigh
        rw [Real.log_exp] at this; linarith
      rw [Set.indicator_of_mem hm]; linarith

theorem setIntegral_indicator_exp_le {I : Set ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∫ s in I, (Set.Icc a b).indicator Real.exp s ≤ Real.exp b - Real.exp a := by
  rw [setIntegral_indicator measurableSet_Icc, ← integral_exp_Icc hab]
  exact setIntegral_mono_set (Real.continuous_exp.integrableOn_Icc)
    (Filter.Eventually.of_forall fun s => (Real.exp_pos s).le)
    (Filter.Eventually.of_forall fun s hs => hs.2)

/-- `P = Σ_{m ≤ M} x(m)²`. -/
def prefixMass (M : ℕ) (x : ℕ → ℝ) : ℝ := ∑ m ∈ Icc 1 M, x m ^ 2

/-- `H = Σ_{m ≤ M} 1/m`. -/
def prefixHarmonic (M : ℕ) : ℝ := ∑ m ∈ Icc 1 M, (1 : ℝ) / m

/-- `σ = Σ_{m ≤ M} x(m)/√m`, the pairing with the pole profile. -/
def prefixPoleMoment (M : ℕ) (x : ℕ → ℝ) : ℝ := ∑ m ∈ Icc 1 M, x m / Real.sqrt m

/-- The de la Vallée Poussin rate at the short-row cutoff, `e^{−c₀ √log(K'/e)}`. -/
def pntRate (c₀ : ℝ) (K' : ℕ) : ℝ := Real.exp (-c₀ * Real.sqrt (Real.log (K' * Real.exp (-1))))

/-- `Σ_{k < K'} Λ(k)/k`. -/
def shortOrderWeight (K' : ℕ) : ℝ := ∑ k ∈ range K', (Λ k : ℝ) / k

/-- The bound for `∫ W²` assembled from the coherent, short-row, long-row and edge parts. -/
def windowSumBound (C c₀ A : ℝ) (B M K' : ℕ) (x : ℕ → ℝ) (h : ℝ) : ℝ :=
  8 * (h ^ 2 * prefixPoleMoment M x ^ 2 + h ^ 2 * (prefixMass M x * (1 + Real.log (2 * K'))) +
      (4 * C * pntRate c₀ K' + h ^ 2) ^ 2 * (prefixMass M x * prefixHarmonic M)) *
      (B * Real.exp h) +
    8 * (h ^ 2 * (prefixMass M x * prefixHarmonic M)) *
      ((A * Real.exp h - A) + (B * Real.exp h - B)) +
    2 * shortOrderWeight K' * ∑ k ∈ range K', (Λ k : ℝ) * (h * (B * Real.exp h) / k + 1) *
      (h * prefixMass M x)

/-- The pointwise square bound behind `integral_windowSum_primeConv_sq_le`. -/
theorem sq_windowSum_primeConv_le {C c₀ t₀ : ℝ} (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hpnt : ∀ ⦃h X Y : ℝ⦄, 0 < h → h ≤ 1 → Y = X * Real.exp (-h) → t₀ ≤ Y →
      |∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k - Real.sqrt X * (1 - Real.exp (-h))| ≤
        Real.sqrt X * (4 * C * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2))
    {A : ℝ} {B K M K' : ℕ} {h s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hA1 : 1 ≤ A)
    (hM : 1 ≤ M) (hMA : (M : ℝ) ≤ 2 * A) (hAB : A ≤ B) (hBK : B < K) (hK' : 1 ≤ K')
    (ht₀ : t₀ ≤ K' * Real.exp (-1)) (x : ℕ → ℝ) (hs1 : Real.log A ≤ s)
    (hs2 : s ≤ Real.log B + h) :
    windowSum B (fun n => topWeight A B n * primeConv K M x n) h s ^ 2 ≤
      8 * Real.exp s * (h ^ 2 * prefixPoleMoment M x ^ 2 +
        h ^ 2 * (prefixMass M x * (1 + Real.log (2 * K'))) +
        (4 * C * pntRate c₀ K' + h ^ 2) ^ 2 * (prefixMass M x * prefixHarmonic M)) +
      8 * ((Set.Icc (Real.log A) (Real.log A + h)).indicator Real.exp s +
          (Set.Icc (Real.log (B : ℝ)) (Real.log B + h)).indicator Real.exp s) *
        (h ^ 2 * (prefixMass M x * prefixHarmonic M)) +
      2 * shortOrderWeight K' * shortWindowSq K' M x (B * Real.exp h) h s := by
  have hA0 : 0 < A := by linarith
  have hB0 : (0 : ℝ) < B := hA0.trans_le hAB
  have hP : 0 ≤ prefixMass M x := sum_nonneg fun _ _ => sq_nonneg _
  have hHm : 0 ≤ prefixHarmonic M := sum_nonneg fun m _ => by positivity
  have hlog2K : 0 ≤ 1 + Real.log (2 * K') := by
    have h1 : (1 : ℝ) ≤ K' := by exact_mod_cast hK'
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * K' by linarith); linarith
  have hAs : A ≤ Real.exp s := by
    rw [← Real.exp_log hA0]; exact Real.exp_le_exp.mpr hs1
  have hsB : Real.exp s ≤ B * Real.exp h := by
    rw [← Real.exp_log hB0, ← Real.exp_add]; exact Real.exp_le_exp.mpr hs2
  have hmaj : |windowSum B (fun n => topWeight A B n * primeConv K M x n) h s| ≤
      Real.sqrt (Real.exp s) * (h * |prefixPoleMoment M x| +
        h * Real.sqrt (prefixMass M x * (1 + Real.log (2 * K'))) +
        (4 * C * pntRate c₀ K' + h ^ 2) * Real.sqrt (prefixMass M x * prefixHarmonic M) +
        (if A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B then 0 else 1) * h *
          Real.sqrt (prefixMass M x * prefixHarmonic M)) +
      ∑ k ∈ range K', vonMangoldtAtom k *
        ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) := by
    rw [windowSum_topWeight_primeConv hA1 x h s]
    exact abs_sum_windowPrimeSum_le hC hc₀ hpnt hh hh1 hM hMA hBK hK' ht₀ hAs x
  set L : ℝ := if A ≤ Real.exp (s - h) ∧ Real.exp s ≤ B then 0 else 1 with hLdef
  have hL01 : L = 0 ∨ L = 1 := by rw [hLdef]; split_ifs <;> simp
  have hLL : L ^ 2 = L := by rcases hL01 with h' | h' <;> rw [h'] <;> norm_num
  have hsq := sq_le_of_abs_le_four_add hmaj
  have hT := sq_shortOrders_le (K' := K') (M := M) x hh.le hsB
  have hE : Real.sqrt (Real.exp s) ^ 2 = Real.exp s := Real.sq_sqrt (Real.exp_pos s).le
  have hsum : (h * |prefixPoleMoment M x|) ^ 2 +
      (h * Real.sqrt (prefixMass M x * (1 + Real.log (2 * K')))) ^ 2 +
      ((4 * C * pntRate c₀ K' + h ^ 2) * Real.sqrt (prefixMass M x * prefixHarmonic M)) ^ 2 +
      (L * h * Real.sqrt (prefixMass M x * prefixHarmonic M)) ^ 2 =
      (h ^ 2 * prefixPoleMoment M x ^ 2 + h ^ 2 * (prefixMass M x * (1 + Real.log (2 * K'))) +
        (4 * C * pntRate c₀ K' + h ^ 2) ^ 2 * (prefixMass M x * prefixHarmonic M)) +
      L * (h ^ 2 * (prefixMass M x * prefixHarmonic M)) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, sq_abs,
      Real.sq_sqrt (mul_nonneg hP hlog2K), Real.sq_sqrt (mul_nonneg hP hHm), hLL]
    ring
  have hedge := edge_mul_exp_le (h := h) (A := A) hB0 hs1 hs2
  rw [← hLdef] at hedge
  have hT' : (∑ k ∈ range K', vonMangoldtAtom k *
      ∑ m ∈ Icc 1 M, |x m| * windowKernel h (s - Real.log ((k * m : ℕ) : ℝ))) ^ 2 ≤
      shortOrderWeight K' * shortWindowSq K' M x (B * Real.exp h) h s := hT
  rw [hE, hsum] at hsq
  have hc₂ : 0 ≤ h ^ 2 * (prefixMass M x * prefixHarmonic M) := by positivity
  have h2 := mul_le_mul_of_nonneg_right hedge hc₂
  linarith [hsq, hT', h2]

/-- **The window sums of the prime translate are small off the pole.** Integrating the pointwise
majorant `abs_sum_windowPrimeSum_le` over `log A ≤ s ≤ log B + h`, where they live. -/
theorem integral_windowSum_primeConv_sq_le {C c₀ t₀ : ℝ} (hC : 0 ≤ C) (hc₀ : 0 < c₀)
    (hpnt : ∀ ⦃h X Y : ℝ⦄, 0 < h → h ≤ 1 → Y = X * Real.exp (-h) → t₀ ≤ Y →
      |∑ k ∈ Ioc ⌊Y⌋₊ ⌊X⌋₊, vonMangoldtAtom k - Real.sqrt X * (1 - Real.exp (-h))| ≤
        Real.sqrt X * (4 * C * Real.exp (-c₀ * Real.sqrt (Real.log Y)) + h ^ 2))
    {A : ℝ} {B K M K' : ℕ} {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hA1 : 1 ≤ A)
    (hM : 1 ≤ M) (hMA : (M : ℝ) ≤ 2 * A) (hAB : A ≤ B) (hBK : B < K) (hK' : 1 ≤ K')
    (ht₀ : t₀ ≤ K' * Real.exp (-1)) (x : ℕ → ℝ) :
    ∫ s, windowSum B (fun n => topWeight A B n * primeConv K M x n) h s ^ 2 ≤
      windowSumBound C c₀ A B M K' x h := by
  have hA0 : 0 < A := by linarith
  have hB0 : (0 : ℝ) < B := hA0.trans_le hAB
  set P := prefixMass M x
  set Hm := prefixHarmonic M
  set σ := prefixPoleMoment M x
  set ε := pntRate c₀ K'
  set LK := shortOrderWeight K'
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hHm : 0 ≤ Hm := sum_nonneg fun m _ => by positivity
  have hLK : 0 ≤ LK := sum_nonneg fun k _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  have hε : 0 ≤ ε := (Real.exp_pos _).le
  have hlog2K : 0 ≤ 1 + Real.log (2 * K') := by
    have h1 : (1 : ℝ) ≤ K' := by exact_mod_cast hK'
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * K' by linarith); linarith
  set c₁ := h ^ 2 * σ ^ 2 + h ^ 2 * (P * (1 + Real.log (2 * K'))) +
    (4 * C * ε + h ^ 2) ^ 2 * (P * Hm)
  set c₂ := h ^ 2 * (P * Hm)
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  have hWeq : ∀ s, windowSum B (fun n => topWeight A B n * primeConv K M x n) h s =
      ∑ m ∈ Icc 1 M, x m * windowPrimeSum A B K h s m := fun s =>
    windowSum_topWeight_primeConv hA1 x h s
  set I := Set.Icc (Real.log A) (Real.log B + h)
  -- the window sums vanish off `I`
  have hzero : ∀ s ∉ I, windowSum B (fun n => topWeight A B n * primeConv K M x n) h s = 0 := by
    intro s hs
    rw [hWeq]
    refine sum_eq_zero fun m hm => ?_
    unfold windowPrimeSum
    rw [sum_eq_zero, mul_zero]
    intro k _
    by_cases ht : topWeight A B (k * m) = 0
    · rw [ht]; ring
    by_cases hw : windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) = 0
    · rw [hw]; ring
    exfalso
    apply hs
    unfold topWeight at ht
    split_ifs at ht with hAB'
    · obtain ⟨h1, h2⟩ := hAB'
      have hkm0 : (0 : ℝ) < ((k * m : ℕ) : ℝ) := hA0.trans_le h1
      unfold windowKernel at hw
      have hmem : s - Real.log ((k * m : ℕ) : ℝ) ∈ Set.Ico 0 h := by
        by_contra hn; exact hw (Set.indicator_of_notMem hn _)
      have hl1 : Real.log A ≤ Real.log ((k * m : ℕ) : ℝ) := Real.log_le_log hA0 h1
      have hl2 : Real.log ((k * m : ℕ) : ℝ) ≤ Real.log B :=
        Real.log_le_log hkm0 (by exact_mod_cast h2)
      exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    · exact absurd rfl ht
  have hWi := integrable_windowSum_sq B (fun n => topWeight A B n * primeConv K M x n) h
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := I) (fun s hs => by
    rw [hzero s hs]; ring)]
  set J₁ := Set.Icc (Real.log A) (Real.log A + h)
  set J₂ := Set.Icc (Real.log (B : ℝ)) (Real.log B + h)
  set F : ℝ → ℝ := fun s => 8 * Real.exp s * c₁ +
    8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂ +
    2 * LK * shortWindowSq K' M x (B * Real.exp h) h s
  -- the pointwise bound on `I`
  have hpt : ∀ s ∈ I,
      windowSum B (fun n => topWeight A B n * primeConv K M x n) h s ^ 2 ≤ F s := fun s hs =>
    sq_windowSum_primeConv_le hC hc₀ hpnt hh hh1 hA1 hM hMA hAB hBK hK' ht₀ x hs.1 hs.2
  -- integrability on `I`
  have hexpI : IntegrableOn Real.exp I := Real.continuous_exp.integrableOn_Icc
  have hwin : ∀ k m : ℕ, Integrable fun s => windowKernel h (s - Real.log ((k * m : ℕ) : ℝ)) :=
    fun k m => (integrable_windowKernel h).comp_sub_right _
  have hSWS : Integrable fun s => shortWindowSq K' M x (B * Real.exp h) h s := by
    unfold shortWindowSq
    refine integrable_finsetSum _ fun k _ => Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun m _ => (hwin k m).const_mul _
  have hf1 : IntegrableOn (fun s => 8 * Real.exp s * c₁) I :=
    (hexpI.const_mul 8).mul_const c₁
  have hf2 : IntegrableOn (fun s => 8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂) I :=
    (((hexpI.indicator measurableSet_Icc).add (hexpI.indicator measurableSet_Icc)).const_mul
      8).mul_const c₂
  have hf3 : IntegrableOn (fun s => 2 * LK * shortWindowSq K' M x (B * Real.exp h) h s) I :=
    (hSWS.const_mul _).integrableOn
  have hFi : IntegrableOn F I := (hf1.add hf2).add hf3
  have hmono := setIntegral_mono_on hWi.integrableOn hFi measurableSet_Icc hpt
  refine hmono.trans ?_
  -- the three integrals
  have hlogAB : Real.log A ≤ Real.log B + h := by
    have := Real.log_le_log hA0 hAB; linarith
  have i1 : ∫ s in I, 8 * Real.exp s * c₁ ≤ 8 * c₁ * (B * Real.exp h) := by
    have e : (fun s => 8 * Real.exp s * c₁) = fun s => (8 * c₁) * Real.exp s := by
      funext s; ring
    rw [e, integral_const_mul, integral_exp_Icc hlogAB, Real.exp_add, Real.exp_log hB0,
      Real.exp_log hA0]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have i2 : ∫ s in I, 8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂ ≤
      8 * c₂ * ((A * Real.exp h - A) + (B * Real.exp h - B)) := by
    have e : (fun s => 8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂) =
        fun s => (8 * c₂) * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) := by
      funext s; ring
    rw [e, integral_const_mul, integral_add (hexpI.indicator measurableSet_Icc)
      (hexpI.indicator measurableSet_Icc)]
    have b1 := setIntegral_indicator_exp_le (I := I)
      (show Real.log A ≤ Real.log A + h by linarith)
    have b2 := setIntegral_indicator_exp_le (I := I)
      (show Real.log (B : ℝ) ≤ Real.log B + h by linarith)
    rw [Real.exp_add, Real.exp_log hA0] at b1
    rw [Real.exp_add, Real.exp_log hB0] at b2
    exact mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by positivity)
  have i3 : ∫ s in I, 2 * LK * shortWindowSq K' M x (B * Real.exp h) h s ≤
      2 * LK * ∑ k ∈ range K', (Λ k : ℝ) * (h * (B * Real.exp h) / k + 1) * (h * P) := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hnn : 0 ≤ᵐ[volume.restrict I] fun s => shortWindowSq K' M x (B * Real.exp h) h s :=
      Filter.Eventually.of_forall fun s => sum_nonneg fun k _ => mul_nonneg
        (mul_nonneg vonMangoldt_nonneg (by positivity)) (sum_nonneg fun m _ =>
          mul_nonneg (sq_nonneg _) (windowKernel_nonneg _ _))
    refine (setIntegral_le_integral hSWS (Filter.Eventually.of_forall fun s =>
      sum_nonneg fun k _ => mul_nonneg (mul_nonneg vonMangoldt_nonneg (by positivity))
        (sum_nonneg fun m _ => mul_nonneg (sq_nonneg _) (windowKernel_nonneg _ _)))).trans
      (le_of_eq ?_)
    unfold shortWindowSq
    rw [integral_finsetSum _ fun k _ => Integrable.const_mul
      (integrable_finsetSum _ fun m _ => (hwin k m).const_mul _) _]
    refine sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun m _ => (hwin k m).const_mul _]
    congr 1
    simp only [P, prefixMass, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, integral_windowKernel_sub hh.le]
    ring
  have hsplitF : ∫ s in I, F s = (∫ s in I, 8 * Real.exp s * c₁) +
      (∫ s in I, 8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂) +
      (∫ s in I, 2 * LK * shortWindowSq K' M x (B * Real.exp h) h s) := by
    simp only [F]
    rw [integral_add (f := fun s => 8 * Real.exp s * c₁ +
        8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂)
        (g := fun s => 2 * LK * shortWindowSq K' M x (B * Real.exp h) h s) (hf1.add hf2) hf3,
      integral_add (f := fun s => 8 * Real.exp s * c₁)
        (g := fun s => 8 * (J₁.indicator Real.exp s + J₂.indicator Real.exp s) * c₂) hf1 hf2]
  rw [hsplitF]
  unfold windowSumBound
  change _ ≤ 8 * c₁ * (B * Real.exp h) + 8 * c₂ * ((A * Real.exp h - A) + (B * Real.exp h - B)) +
    2 * LK * ∑ k ∈ range K', (Λ k : ℝ) * (h * (B * Real.exp h) / k + 1) * (h * P)
  linarith [i1, i2, i3]

/-! ### The size of the prime translate -/

/-- Each coefficient of the prime translate is bounded through `Σ_{k | n} Λ(k) = log n`:
`((a ∗ x)(n))² ≤ log n · Σ_{k m = n} Λ(k)/k · x(m)²`. -/
theorem sq_primeConv_le (K M : ℕ) (x : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    primeConv K M x n ^ 2 ≤ Real.log n *
      ∑ k ∈ range K, ∑ m ∈ Icc 1 M, if k * m = n then (Λ k : ℝ) / k * x m ^ 2 else 0 := by
  unfold primeConv
  rw [← sum_product', ← sum_product']
  have hcs := sum_mul_sq_le_sq_mul_sq (range K ×ˢ Icc 1 M)
    (fun p => if p.1 * p.2 = n then Real.sqrt (Λ p.1 : ℝ) else 0)
    (fun p => if p.1 * p.2 = n then Real.sqrt ((Λ p.1 : ℝ) / p.1) * x p.2 else 0)
  have e1 : ∀ p : ℕ × ℕ, (if p.1 * p.2 = n then Real.sqrt (Λ p.1 : ℝ) else 0) *
      (if p.1 * p.2 = n then Real.sqrt ((Λ p.1 : ℝ) / p.1) * x p.2 else 0) =
      if p.1 * p.2 = n then vonMangoldtAtom p.1 * x p.2 else 0 := by
    intro p
    split_ifs
    · rw [vonMangoldtAtom_eq, ← mul_assoc, ← Real.sqrt_mul vonMangoldt_nonneg,
        ← mul_div_assoc, Real.sqrt_div (mul_self_nonneg _), Real.sqrt_mul_self vonMangoldt_nonneg]
    · ring
  have e2 : ∀ p : ℕ × ℕ, (if p.1 * p.2 = n then Real.sqrt (Λ p.1 : ℝ) else 0) ^ 2 =
      if p.1 * p.2 = n then (Λ p.1 : ℝ) else 0 := by
    intro p; split_ifs
    · exact Real.sq_sqrt vonMangoldt_nonneg
    · ring
  have e3 : ∀ p : ℕ × ℕ,
      (if p.1 * p.2 = n then Real.sqrt ((Λ p.1 : ℝ) / p.1) * x p.2 else 0) ^ 2 =
      if p.1 * p.2 = n then (Λ p.1 : ℝ) / p.1 * x p.2 ^ 2 else 0 := by
    intro p; split_ifs
    · rw [mul_pow, Real.sq_sqrt (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))]
    · ring
  simp only [e1, e2, e3] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun p _ => by
    split_ifs
    · exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (sq_nonneg _)
    · exact le_rfl))
  -- `Σ_{k m = n} Λ(k) ≤ Σ_{k | n} Λ(k) = log n`
  rw [sum_product]
  calc ∑ k ∈ range K, ∑ m ∈ Icc 1 M, (if k * m = n then (Λ k : ℝ) else 0)
      ≤ ∑ k ∈ (range K).filter (· ∣ n), (Λ k : ℝ) := by
        rw [sum_filter]
        refine sum_le_sum fun k _ => ?_
        split_ifs with hk
        · obtain ⟨m₀, hm₀⟩ := hk
          calc ∑ m ∈ Icc 1 M, (if k * m = n then (Λ k : ℝ) else 0)
              ≤ ∑ m ∈ ({m₀} : Finset ℕ), (if k * m = n then (Λ k : ℝ) else 0) := by
                rw [← sum_filter, ← sum_filter]
                refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun _ _ _ =>
                  vonMangoldt_nonneg
                obtain ⟨_, hm⟩ := mem_filter.mp hm
                have hk0 : 0 < k := by
                  rcases Nat.eq_zero_or_pos k with rfl | h'
                  · simp at hm; omega
                  · exact h'
                have : m = m₀ := Nat.eq_of_mul_eq_mul_left hk0 (hm.trans hm₀)
                exact mem_filter.mpr ⟨mem_singleton.mpr this, hm⟩
            _ ≤ (Λ k : ℝ) := by
                rw [sum_singleton]; split_ifs
                · exact le_rfl
                · exact vonMangoldt_nonneg
        · refine le_of_eq (sum_eq_zero fun m _ => ?_)
          rw [if_neg]
          rintro rfl
          exact hk (dvd_mul_right k m)
    _ ≤ ∑ k ∈ n.divisors, (Λ k : ℝ) := by
        refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => vonMangoldt_nonneg
        exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hk).2, by omega⟩
    _ = Real.log n := vonMangoldt_sum

/-- **The prime translate on the top window has `ℓ²` norm `≲ log B · log(B/A)` times the
prefix.** -/
theorem sum_sq_topWeight_primeConv_le {A : ℝ} (hA1 : 1 ≤ A) {B : ℕ} (hAB : A ≤ B) (K M : ℕ)
    (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 B, (topWeight A B n * primeConv K M x n) ^ 2 ≤
      Real.log B * (Real.log (2 * B / A) + 2 * (Real.log 4 + 4)) * prefixMass M x := by
  have hA0 : 0 < A := by linarith
  have hB1 : (1 : ℝ) ≤ B := hA1.trans hAB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  set Q : ℕ → ℝ := fun n => ∑ k ∈ range K, ∑ m ∈ Icc 1 M,
    if k * m = n then (Λ k : ℝ) / k * x m ^ 2 else 0
  have hQ0 : ∀ n, 0 ≤ Q n := fun n => sum_nonneg fun k _ => sum_nonneg fun m _ => by
    split_ifs
    · exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (sq_nonneg _)
    · exact le_rfl
  have hpt : ∀ n ∈ Icc 1 B, (topWeight A B n * primeConv K M x n) ^ 2 ≤
      Real.log B * (topWeight A B n * Q n) := by
    intro n hn
    obtain ⟨hn1, hnB⟩ := mem_Icc.mp hn
    have htw0 := topWeight_nonneg A B n
    have htw1 := topWeight_le_one A B n
    have hsq := sq_primeConv_le K M x hn1
    have hlogn : Real.log n ≤ Real.log B :=
      Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnB)
    have htw2 : topWeight A B n ^ 2 ≤ topWeight A B n := by nlinarith
    rw [mul_pow]
    calc topWeight A B n ^ 2 * primeConv K M x n ^ 2
        ≤ topWeight A B n * (Real.log n * Q n) :=
          mul_le_mul htw2 hsq (sq_nonneg _) htw0
      _ ≤ topWeight A B n * (Real.log B * Q n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlogn (hQ0 n)) htw0
      _ = Real.log B * (topWeight A B n * Q n) := by ring
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hlogB
  -- reindex: `Σ_n ρ(n) Σ_{km = n} Λ(k)/k x(m)² = Σ_m x(m)² Σ_k Λ(k)/k ρ(k m)`
  have hre : ∑ n ∈ Icc 1 B, topWeight A B n * Q n =
      ∑ m ∈ Icc 1 M, x m ^ 2 * ∑ k ∈ range K, (Λ k : ℝ) / k * topWeight A B (k * m) := by
    simp only [Q, mul_sum]
    rw [sum_comm]
    simp_rw [sum_comm (s := Icc 1 B) (t := Icc 1 M)]
    rw [sum_comm]
    refine sum_congr rfl fun m _ => sum_congr rfl fun k _ => ?_
    have hite : ∀ n : ℕ, topWeight A B n * (if k * m = n then (Λ k : ℝ) / k * x m ^ 2 else 0) =
        if k * m = n then x m ^ 2 * ((Λ k : ℝ) / k * topWeight A B (k * m)) else 0 := by
      intro n; split_ifs with he
      · subst he; ring
      · ring
    rw [sum_congr rfl fun n _ => hite n, sum_ite_eq]
    split_ifs with hmem
    · rfl
    · have : topWeight A B (k * m) = 0 := by
        unfold topWeight; rw [if_neg]
        rintro ⟨h1, h2⟩
        apply hmem
        refine mem_Icc.mpr ⟨?_, h2⟩
        by_contra h0
        have : k * m = 0 := by omega
        rw [this, Nat.cast_zero] at h1; linarith
      rw [this]; ring
  rw [hre, prefixMass, mul_sum]
  refine sum_le_sum fun m hm => ?_
  have hm1 := (mem_Icc.mp hm).1
  rw [mul_comm (x m ^ 2)]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  calc ∑ k ∈ range K, (Λ k : ℝ) / k * topWeight A B (k * m)
      ≤ ∑ k ∈ (Icc 1 B).filter (fun k => A ≤ ((k * m : ℕ) : ℝ) ∧ k * m ≤ B), (Λ k : ℝ) / k := by
        rw [sum_filter]
        have hsub : ∑ k ∈ range K, (Λ k : ℝ) / k * topWeight A B (k * m) ≤
            ∑ k ∈ range K, if A ≤ ((k * m : ℕ) : ℝ) ∧ k * m ≤ B then (Λ k : ℝ) / k else 0 := by
          refine sum_le_sum fun k _ => ?_
          unfold topWeight
          split_ifs <;> simp
        refine hsub.trans ?_
        rw [← sum_filter, ← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ =>
          div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
        obtain ⟨_, h1, h2⟩ := by simpa only [mem_filter] using hk
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, h1, h2⟩
        · by_contra h0
          have : k = 0 := by omega
          rw [this, zero_mul, Nat.cast_zero] at h1; linarith
        · exact (Nat.le_mul_of_pos_right k hm1).trans h2
    _ ≤ Real.log (2 * B / A) + 2 * (Real.log 4 + 4) :=
        sum_vonMangoldt_div_window_le hA0 hm1 hAB

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
