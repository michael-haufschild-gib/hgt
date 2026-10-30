import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCovariantCountertermIsTheAnomaly

/-!
# The prime form collapses on the pole profile

With the pole weights `x_n = n^{−1/2}`, every pair `(m, n)` of the prime form at the lag `log k`
meets the product `ℓ = km` with the same weight `Λ(k)(km)^{−1/2}·n^{−1/2}`. Summing over the
factorizations of `ℓ`, unique factorization `Σ_{d∣ℓ} Λ(d) = log ℓ` collapses the whole non-ratio
prime form of the atomic test to a sum over pairs `(n, ℓ)`:

`NR_g(x) = 2 Σ_{n ≤ N} Σ_{ℓ ≠ n} n^{−1/2} ℓ^{−1/2} Λ_N(ℓ) G(log ℓ − log n)`,

where `G` is the autocorrelation of the bump and `Λ_N(ℓ) = Σ_{d∣ℓ, ℓ/d ≤ N} Λ(d)`, which is
`log ℓ` whenever `ℓ ≤ N` (`nonRatioForm_poleProfile_eq`). The prime side of the shells becomes the
archimedean absolute value `log ℓ` at the point `0` of the gauge torus.
-/

noncomputable section

open MeasureTheory Finset
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
open _root_.RHTower (vonMangoldtAtom)

/-- The horizon divisor weight `Λ_N(ℓ) = Σ_{d ∣ ℓ, ℓ/d ≤ N} Λ(d)`. -/
def horizonDivisorMangoldt (N ℓ : ℕ) : ℝ :=
  ∑ d ∈ ℓ.divisors.filter (fun d => ℓ / d ≤ N), (ArithmeticFunction.vonMangoldt d : ℝ)

theorem horizonDivisorMangoldt_of_le {N ℓ : ℕ} (hℓ : ℓ ≤ N) :
    horizonDivisorMangoldt N ℓ = Real.log ℓ := by
  rw [horizonDivisorMangoldt, Finset.filter_true_of_mem fun d _ => (Nat.div_le_self ℓ d).trans hℓ,
    ArithmeticFunction.vonMangoldt_sum]

theorem horizonDivisorMangoldt_nonneg (N ℓ : ℕ) : 0 ≤ horizonDivisorMangoldt N ℓ :=
  sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem horizonDivisorMangoldt_le_log (N ℓ : ℕ) : horizonDivisorMangoldt N ℓ ≤ Real.log ℓ := by
  rw [← ArithmeticFunction.vonMangoldt_sum]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg

variable {g : ℝ → ℝ} {w : ℝ}

/-- The non-ratio lag form, with its two orientations combined by the evenness of `G`. -/
theorem nonRatioLag_eq_two_mul (N k : ℕ) (x : ℕ → ℝ) :
    nonRatioLag g N k x = 2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n *
      (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m))) := by
  unfold nonRatioLag
  simp only [mul_add, sum_add_distrib]
  have hswap : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n *
      (if m = k * n then 0 else bumpCorr g (-Real.log k - (Real.log n - Real.log m)))) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n *
        (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m))) := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rw [mul_comm (x n) (x m)]
    congr 1
    split_ifs
    · rfl
    · rw [show -Real.log k - (Real.log m - Real.log n) =
        -(Real.log k - (Real.log n - Real.log m)) by ring, bumpCorr_neg]
  rw [hswap]
  ring

/-- The Mangoldt atom times a pole weight is the Mangoldt weight of the product. -/
theorem vonMangoldtAtom_mul_poleVector (k m : ℕ) (hm : 1 ≤ m) :
    vonMangoldtAtom k * poleVector m =
      (ArithmeticFunction.vonMangoldt k : ℝ) * poleVector (k * m) := by
  rcases lt_or_ge k 2 with hk | hk
  · rw [vonMangoldtAtom_eq_zero_of_lt_two hk]
    interval_cases k
    · simp
    · simp
  · rw [vonMangoldtAtom_eq hk, poleVector, poleVector, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg k)]
    have hk0 : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
    have hm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    field_simp

/-- Products of a lag and a horizon index, grouped by their value: the multiplicity of `ℓ` is the
horizon divisor weight. -/
theorem sum_range_sum_vonMangoldt_mul_eq {N L : ℕ} (F : ℕ → ℝ) (hF : ∀ ℓ, L < ℓ → F ℓ = 0) :
    ∑ k ∈ range (L + 1), ∑ m ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt k : ℝ) * F (k * m) =
      ∑ ℓ ∈ Icc 1 L, horizonDivisorMangoldt N ℓ * F ℓ := by
  set S := range (L + 1) ×ˢ Icc 1 N with hS
  set f : ℕ × ℕ → ℝ := fun p => (ArithmeticFunction.vonMangoldt p.1 : ℝ) * F (p.1 * p.2) with hf
  have hprod : ∑ k ∈ range (L + 1), ∑ m ∈ Icc 1 N,
      (ArithmeticFunction.vonMangoldt k : ℝ) * F (k * m) = ∑ p ∈ S, f p := by
    rw [hS, Finset.sum_product]
  -- only products in `[1, L]` contribute
  have hrestrict : ∑ p ∈ S, f p = ∑ p ∈ S.filter (fun p => p.1 * p.2 ∈ Icc 1 L), f p := by
    rw [Finset.sum_filter]
    refine sum_congr rfl fun p hp => ?_
    split_ifs with h
    · rfl
    · simp only [mem_Icc, not_and_or, not_le] at h
      rcases h with h | h
      · have : p.1 * p.2 = 0 := by omega
        rcases Nat.mul_eq_zero.mp this with h0 | h0
        · simp [hf, h0]
        · have := (mem_Icc.mp (mem_product.mp hp).2).1
          omega
      · simp [hf, hF _ h]
  rw [hprod, hrestrict, ← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2)
    (t := Icc 1 L) (fun p hp => (mem_filter.mp hp).2)]
  refine sum_congr rfl fun ℓ hℓ => ?_
  have hℓ1 : 1 ≤ ℓ := (mem_Icc.mp hℓ).1
  have hℓL : ℓ ≤ L := (mem_Icc.mp hℓ).2
  rw [horizonDivisorMangoldt, Finset.sum_mul]
  refine Finset.sum_nbij' (fun p => p.1) (fun d => (d, ℓ / d)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [hS, mem_filter, mem_product, mem_range, mem_Icc] at hp
    obtain ⟨⟨⟨_, hm1, hmN⟩, _⟩, hpl⟩ := hp
    have hp1 : 0 < p.1 := by
      rcases Nat.eq_zero_or_pos p.1 with h | h
      · rw [h, zero_mul] at hpl; omega
      · exact h
    simp only [mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨p.2, by rw [← hpl]⟩, by omega⟩, ?_⟩
    rw [← hpl, Nat.mul_div_cancel_left _ hp1]
    exact hmN
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdl, _⟩, hdN⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdl (by omega)
    simp only [hS, mem_filter, mem_product, mem_range, mem_Icc]
    have hmul : d * (ℓ / d) = ℓ := Nat.mul_div_cancel' hdl
    refine ⟨⟨⟨by have := Nat.le_of_dvd (by omega) hdl; omega, ?_, hdN⟩, by omega, by omega⟩, hmul⟩
    rcases Nat.eq_zero_or_pos (ℓ / d) with h | h
    · rw [h, mul_zero] at hmul; omega
    · exact h
  · intro p hp
    simp only [mem_filter] at hp
    obtain ⟨hpS, hpl⟩ := hp
    have hp1 : 0 < p.1 := by
      rcases Nat.eq_zero_or_pos p.1 with h | h
      · rw [h, zero_mul] at hpl; omega
      · exact h
    ext
    · rfl
    · simp only
      rw [← hpl, Nat.mul_div_cancel_left _ hp1]
  · intro d _
    rfl
  · intro p hp
    simp only [mem_filter] at hp
    simp only [hf, hp.2]

/-- **The prime form collapses on the pole profile.** For a bump supported in `[0, w]`, `w ≥ 0`,
the non-ratio prime form of the pole profile is a pair sum with the horizon divisor weights. -/
theorem nonRatioForm_poleProfile_eq (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) (hx : ∀ n ∈ Icc 1 N, x n = poleVector n) :
    nonRatioForm g N x = 2 * ∑ n ∈ Icc 1 N, ∑ ℓ ∈ Icc 1 ⌈(N : ℝ) * Real.exp w⌉₊,
      poleVector n * poleVector ℓ * horizonDivisorMangoldt N ℓ *
        (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) := by
  set L := ⌈(N : ℝ) * Real.exp w⌉₊ with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNL : (N : ℝ) * Real.exp w ≤ L := Nat.le_ceil _
  -- the lag form vanishes at large lags
  have htsum : nonRatioForm g N x = ∑ k ∈ range (L + 1), vonMangoldtAtom k * nonRatioLag g N k x := by
    rw [nonRatioForm]
    refine tsum_eq_sum fun k hk => ?_
    have hkK : L + 1 ≤ k := by simpa using hk
    have hk : Real.log N + w < Real.log k := by
      have hkL : (L : ℝ) < k := by exact_mod_cast (by omega : L < k)
      have hpos : 0 < (N : ℝ) * Real.exp w := by positivity
      have := Real.log_lt_log hpos (lt_of_le_of_lt hNL hkL)
      rwa [Real.log_mul hN0.ne' (Real.exp_pos w).ne', Real.log_exp] at this
    rw [nonRatioLag_eq_zero_of_log_lt hgsupp hw hk, mul_zero]
  -- the support of the autocorrelation
  have hG0 : ∀ t : ℝ, w < |t| → bumpCorr g t = 0 := by
    intro t ht
    unfold bumpCorr
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun v => ?_)
    change g v * g (v + t) = 0
    by_cases hv : v ∈ Set.Icc 0 w
    · have hvt : v + t ∉ Set.Icc 0 w := by
        intro h
        rcases le_or_gt 0 t with h0 | h0
        · rw [abs_of_nonneg h0] at ht; linarith [hv.1, h.2]
        · rw [abs_of_neg h0] at ht; linarith [hv.2, h.1]
      rw [hgsupp _ hvt, mul_zero]
    · rw [hgsupp _ hv, zero_mul]
  set H : ℕ → ℕ → ℝ := fun n ℓ => if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)
    with hH
  have hHvan : ∀ n ∈ Icc 1 N, ∀ ℓ : ℕ, L < ℓ → H n ℓ = 0 := by
    intro n hn ℓ hℓ
    simp only [hH]
    split_ifs
    · rfl
    · apply hG0
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hℓR : (L : ℝ) < ℓ := by exact_mod_cast hℓ
      have hlt : (n : ℝ) * Real.exp w < ℓ :=
        lt_of_le_of_lt (le_trans (mul_le_mul_of_nonneg_right hnN (Real.exp_pos w).le) hNL) hℓR
      have := Real.log_lt_log (by positivity) hlt
      rw [Real.log_mul (by positivity) (Real.exp_pos w).ne', Real.log_exp] at this
      rw [abs_of_pos (by linarith)]
      linarith
  -- each lag term through the product `k m`
  have hterm : ∀ k m n : ℕ, 1 ≤ m → m ∈ Icc 1 N → n ∈ Icc 1 N →
      vonMangoldtAtom k * (x m * x n *
        (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))) =
      poleVector n * ((ArithmeticFunction.vonMangoldt k : ℝ) * (poleVector (k * m) * H n (k * m))) := by
    intro k m n hm1 hm hn
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [vonMangoldtAtom]
    · have hHk : (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m))) =
          H n (k * m) := by
        simp only [hH, eq_comm (a := n)]
        split_ifs
        · rfl
        · congr 1
          rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hk.ne') (by exact_mod_cast (by omega : m ≠ 0))]
          ring
      rw [hHk, hx m hm, hx n hn]
      have h := vonMangoldtAtom_mul_poleVector k m hm1
      calc vonMangoldtAtom k * (poleVector m * poleVector n * H n (k * m))
          = (vonMangoldtAtom k * poleVector m) * (poleVector n * H n (k * m)) := by ring
        _ = _ := by rw [h]; ring
  have hlag : ∀ k ∈ range (L + 1), vonMangoldtAtom k * nonRatioLag g N k x =
      2 * ∑ n ∈ Icc 1 N, poleVector n * ∑ m ∈ Icc 1 N,
        (ArithmeticFunction.vonMangoldt k : ℝ) * (poleVector (k * m) * H n (k * m)) := by
    intro k _
    rw [nonRatioLag_eq_two_mul, mul_left_comm]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun n hn => sum_congr rfl fun m hm => ?_
    exact hterm k m n (mem_Icc.mp hm).1 hm hn
  rw [htsum, Finset.sum_congr rfl hlag, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  have hfib := sum_range_sum_vonMangoldt_mul_eq (N := N) (L := L)
    (fun ℓ => poleVector ℓ * H n ℓ) (fun ℓ hℓ => by simp only [hHvan n hn ℓ hℓ, mul_zero])
  rw [← Finset.mul_sum, hfib, Finset.mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
