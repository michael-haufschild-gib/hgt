import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.PeriodicShellWindows

/-!
# Weighted base collapse on the top band

Grouping Mangoldt terms by their product preserves every base coefficient.
The top band never occurs as a nonzero shell base, so perturbing it produces
no quadratic shell term. The exact shell–pole expansion retains both pole
cross terms, the quadratic pole term, and the removed ratio diagonal.
-/

open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
open _root_.RHTower (vonMangoldtAtom)
noncomputable section

/-- The divisor convolution with a coefficient on the finite base horizon. -/
def horizonDivisorCoefficient (ψ : ℕ → ℝ) (N ℓ : ℕ) : ℝ :=
  ∑ d ∈ ℓ.divisors.filter (fun d => ℓ / d ≤ N),
    (ArithmeticFunction.vonMangoldt d : ℝ) * ψ (ℓ / d)

/-- Product fibres preserve every base coefficient in the Mangoldt convolution. -/
theorem sum_range_sum_weighted_vonMangoldt_mul_eq {N L : ℕ} (ψ F : ℕ → ℝ) (hF : ∀ ℓ, L < ℓ → F ℓ = 0) :
    ∑ k ∈ range (L + 1), ∑ m ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt k : ℝ) * ψ m * F (k * m) =
      ∑ ℓ ∈ Icc 1 L, horizonDivisorCoefficient ψ N ℓ * F ℓ := by
  set S := range (L + 1) ×ˢ Icc 1 N with hS
  set f : ℕ × ℕ → ℝ := fun p => (ArithmeticFunction.vonMangoldt p.1 : ℝ) * ψ p.2 * F (p.1 * p.2) with hf
  have hprod : ∑ k ∈ range (L + 1), ∑ m ∈ Icc 1 N,
      (ArithmeticFunction.vonMangoldt k : ℝ) * ψ m * F (k * m) = ∑ p ∈ S, f p := by
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
  rw [horizonDivisorCoefficient, Finset.sum_mul]
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
    have he : p.1 * p.2 = ℓ := (mem_filter.mp hp).2
    have hp1 : 0 < p.1 := by
      by_contra h
      have hz : p.1 = 0 := Nat.eq_zero_of_not_pos h
      rw [hz, zero_mul] at he
      omega
    simp only [hf]
    rw [← he, Nat.mul_div_cancel_left _ hp1]

#print axioms sum_range_sum_weighted_vonMangoldt_mul_eq

/-- The positive Mangoldt divisor mass bounds every bounded base coefficient. -/
theorem abs_horizonDivisorCoefficient_le (ψ : ℕ → ℝ) {B : ℝ}
    (hB : ∀ n, |ψ n| ≤ B) (N ℓ : ℕ) :
    |horizonDivisorCoefficient ψ N ℓ| ≤ B * Real.log ℓ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  unfold horizonDivisorCoefficient
  calc
    _ ≤ ∑ d ∈ ℓ.divisors.filter (fun d => ℓ / d ≤ N),
        |(ArithmeticFunction.vonMangoldt d : ℝ) * ψ (ℓ / d)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ ℓ.divisors.filter (fun d => ℓ / d ≤ N),
        (ArithmeticFunction.vonMangoldt d : ℝ) * B := by
      apply sum_le_sum
      intro d _
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_left (hB _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ d ∈ ℓ.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) * B :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hB0)
    _ = _ := by rw [← sum_mul, ArithmeticFunction.vonMangoldt_sum, mul_comm]

private theorem bumpCorr_eq_zero_of_topBand_base {g : ℝ → ℝ} {w : ℝ} (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {k m n : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n) {N : ℕ} (hnN : n ≤ N)
    (hm2 : (N : ℝ) * Real.exp w < 2 * m) :
    bumpCorr g (Real.log k - (Real.log n - Real.log m)) = 0 := by
  apply bumpCorr_eq_zero hgsupp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  -- `n e^w ≤ N e^w < 2m ≤ km`
  have hlt : (n : ℝ) * Real.exp w < k * m := by
    have h1 : (n : ℝ) * Real.exp w ≤ N * Real.exp w :=
      mul_le_mul_of_nonneg_right hnN' (Real.exp_pos w).le
    have h2 : 2 * (m : ℝ) ≤ k * m := mul_le_mul_of_nonneg_right hk2 hm0.le
    linarith only [h1, h2, hm2]
  have hlog := Real.log_lt_log (by positivity) hlt
  rw [Real.log_mul hn0.ne' (Real.exp_pos w).ne', Real.log_exp,
    Real.log_mul hk0.ne' hm0.ne'] at hlog
  exact lt_of_lt_of_le (by linarith only [hlog]) (le_abs_self _)

/-- A shell row with every finite-horizon base coefficient retained. -/
def shellCoefficientRow (g : ℝ → ℝ) (a : ℕ → ℝ) (N : ℕ) (w : ℝ) (n : ℕ) : ℝ :=
  ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)), poleVector ℓ * horizonDivisorCoefficient a N ℓ *
    (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n))

/-- Grouping by product preserves the bounded base profile exactly. -/
theorem nonRatioForm_eq_of_coefficient_on_bases {g : ℝ → ℝ} {w : ℝ}
    (a : ℕ → ℝ) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ)
    (hx : ∀ m ∈ Icc 1 N, 2 * (m : ℝ) ≤ N * Real.exp w → x m = poleVector m * a m) :
    nonRatioForm g N x = 2 * ∑ n ∈ Icc 1 N, x n * shellCoefficientRow g a N w n := by
  set L := ⌈(N : ℝ) * Real.exp w⌉₊ with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNL : (N : ℝ) * Real.exp w ≤ L := Nat.le_ceil _
  have htsum : nonRatioForm g N x =
      ∑ k ∈ range (L + 1), vonMangoldtAtom k * nonRatioLag g N k x := by
    rw [nonRatioForm]
    refine tsum_eq_sum fun k hk => ?_
    have hkK : L + 1 ≤ k := by simpa using hk
    have hk : Real.log N + w < Real.log k := by
      have hkL : (L : ℝ) < k := by exact_mod_cast (by omega : L < k)
      have hpos : 0 < (N : ℝ) * Real.exp w := by positivity
      have := Real.log_lt_log hpos (lt_of_le_of_lt hNL hkL)
      rwa [Real.log_mul hN0.ne' (Real.exp_pos w).ne', Real.log_exp] at this
    rw [nonRatioLag_eq_zero_of_log_lt hgsupp hw hk, mul_zero]
  set H : ℕ → ℕ → ℝ := fun n ℓ => if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)
    with hH
  have hHvan : ∀ n ∈ Icc 1 N, ∀ ℓ : ℕ, L < ℓ → H n ℓ = 0 := by
    intro n hn ℓ hℓ
    simp only [hH]
    split_ifs
    · rfl
    · apply bumpCorr_eq_zero hgsupp
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hℓR : (L : ℝ) < ℓ := by exact_mod_cast hℓ
      have hlt : (n : ℝ) * Real.exp w < ℓ :=
        lt_of_le_of_lt (le_trans (mul_le_mul_of_nonneg_right hnN (Real.exp_pos w).le) hNL) hℓR
      have := Real.log_lt_log (by positivity) hlt
      rw [Real.log_mul (by positivity) (Real.exp_pos w).ne', Real.log_exp] at this
      rw [abs_of_pos (by linarith)]
      linarith
  -- Each product fibre retains the base coefficient.
  have hterm : ∀ k m n : ℕ, m ∈ Icc 1 N → n ∈ Icc 1 N →
      vonMangoldtAtom k * (x m * x n *
        (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))) =
      x n * ((ArithmeticFunction.vonMangoldt k : ℝ) * a m * (poleVector (k * m) * H n (k * m))) := by
    intro k m n hm hn
    have hm1 := (mem_Icc.mp hm).1
    rcases lt_or_ge k 2 with hk | hk
    · have hΛ : (ArithmeticFunction.vonMangoldt k : ℝ) = 0 := by
        interval_cases k <;> simp
      have hA : vonMangoldtAtom k = 0 := by
        simp [vonMangoldtAtom, show ¬ 2 ≤ k by omega]
      rw [hA, hΛ]
      ring
    have hHk : (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m))) =
        H n (k * m) := by
      simp only [hH, eq_comm (a := n)]
      split_ifs
      · rfl
      · congr 1
        rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (by omega : k ≠ 0))
          (by exact_mod_cast (by omega : m ≠ 0))]
        ring
    by_cases hbase : 2 * (m : ℝ) ≤ N * Real.exp w
    · rw [hHk, hx m hm hbase]
      have h := vonMangoldtAtom_mul_poleVector k m hm1
      calc vonMangoldtAtom k * (poleVector m * a m * x n * H n (k * m))
          = (vonMangoldtAtom k * poleVector m) * (a m * x n * H n (k * m)) := by ring
        _ = _ := by rw [h]; ring
    · have h0 : bumpCorr g (Real.log k - (Real.log n - Real.log m)) = 0 :=
        bumpCorr_eq_zero_of_topBand_base hgsupp hk hm1 (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
          (not_le.mp hbase)
      have hH0 : H n (k * m) = 0 := by
        rw [← hHk]
        split_ifs
        · rfl
        · exact h0
      rw [hHk, hH0]
      ring
  have hlag : ∀ k ∈ range (L + 1), vonMangoldtAtom k * nonRatioLag g N k x =
      2 * ∑ n ∈ Icc 1 N, x n * ∑ m ∈ Icc 1 N,
        (ArithmeticFunction.vonMangoldt k : ℝ) * a m * (poleVector (k * m) * H n (k * m)) := by
    intro k _
    rw [nonRatioLag_eq_two_mul, mul_left_comm]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun n hn => sum_congr rfl fun m hm => hterm k m n hm hn
  rw [htsum, Finset.sum_congr rfl hlag, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  have hfib := sum_range_sum_weighted_vonMangoldt_mul_eq (N := N) (L := L) a
    (fun ℓ => poleVector ℓ * H n ℓ) (fun ℓ hℓ => by simp only [hHvan n hn ℓ hℓ, mul_zero])
  rw [← Finset.mul_sum, hfib, shellCoefficientRow]
  congr 1
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [hH]
  ring

#print axioms nonRatioForm_eq_of_coefficient_on_bases

/-- A bounded base profile with an independent top-band perturbation. -/
def topBandPerturbedProfile (a ψ : ℕ → ℝ) (N : ℕ) (w η : ℝ) (n : ℕ) : ℝ :=
  poleVector n * a n + η * (if n ∈ topBand N w then poleVector n * ψ n else 0)

/-- Half the linear shell coefficient along the top-band perturbation. -/
def shellTopCoefficient (g : ℝ → ℝ) (a ψ : ℕ → ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  ∑ n ∈ topBand N w, poleVector n * ψ n * shellCoefficientRow g a N w n

/-- Half the linear coefficient of the literal block `2 Pole − NR`. -/
def jointTopCoefficient (g : ℝ → ℝ) (a ψ : ℕ → ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  poleWeightMinus g * poleWeightPlus g *
    ((∑ n ∈ Icc 1 N, a n / (n : ℝ)) * (∑ n ∈ topBand N w, ψ n) +
      (∑ n ∈ Icc 1 N, a n) * (∑ n ∈ topBand N w, ψ n / (n : ℝ))) -
    shellTopCoefficient g a ψ N w

/-- Product regrouping leaves one smooth partner sum and the removed ratio diagonal. -/
theorem shellTopCoefficient_eq_product_sum {g : ℝ → ℝ} {w : ℝ} (hw : 0 ≤ w)
    (a ψ : ℕ → ℝ) (N : ℕ) :
    shellTopCoefficient g a ψ N w =
      (∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)), horizonDivisorCoefficient a N ℓ *
        (poleVector ℓ * ∑ n ∈ topBand N w, shellPartnerKernel g ℓ n * ψ n)) -
      (∫ u, g u ^ 2) * ∑ n ∈ topBand N w, ψ n * horizonDivisorCoefficient a N n / (n : ℝ) := by
  let L := Nat.ceil ((N : ℝ) * Real.exp w)
  have hnL (n : ℕ) (hn : n ∈ topBand N w) : n ∈ Icc 1 L := by
    have h := (mem_Icc.mp (mem_topBand.mp hn).1)
    refine mem_Icc.mpr ⟨h.1, ?_⟩
    have hN : (n : ℝ) ≤ N := by exact_mod_cast h.2
    have hNL : (N : ℝ) ≤ N * Real.exp w :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_exp_iff.mpr hw)
    exact_mod_cast hN.trans (hNL.trans (Nat.le_ceil _))
  have hkernel (ℓ n : ℕ) :
      shellPartnerKernel g ℓ n = poleVector n * bumpCorr g (Real.log ℓ - Real.log n) := by
    rw [shellPartnerKernel, poleVector, one_div,
      ← bumpCorr_neg (g := g) (Real.log n - Real.log ℓ), neg_sub]
  have hrow (n : ℕ) (hn : n ∈ topBand N w) :
      poleVector n * ψ n * shellCoefficientRow g a N w n =
      (∑ ℓ ∈ Icc 1 L, horizonDivisorCoefficient a N ℓ * poleVector ℓ *
        (shellPartnerKernel g ℓ n * ψ n)) -
      (∫ u, g u ^ 2) * (ψ n * horizonDivisorCoefficient a N n / (n : ℝ)) := by
    have hsplit : ∀ ℓ ∈ Icc 1 L,
        poleVector n * ψ n * (poleVector ℓ * horizonDivisorCoefficient a N ℓ *
          (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n))) =
        horizonDivisorCoefficient a N ℓ * poleVector ℓ * (shellPartnerKernel g ℓ n * ψ n) -
          if ℓ = n then (∫ u, g u ^ 2) * (ψ n * horizonDivisorCoefficient a N n / (n : ℝ)) else 0 := by
      intro ℓ _
      rw [hkernel]
      split_ifs with he
      · subst ℓ
        rw [sub_self, bumpCorr_zero]
        have hb := poleVector_sq n
        have heq : horizonDivisorCoefficient a N n * poleVector n *
            (poleVector n * (∫ u, g u ^ 2) * ψ n) =
            poleVector n ^ 2 * ((∫ u, g u ^ 2) * ψ n * horizonDivisorCoefficient a N n) := by ring
        rw [heq, hb]
        ring
      · ring
    rw [shellCoefficientRow, mul_sum, sum_congr rfl hsplit, sum_sub_distrib,
      sum_ite_eq' (Icc 1 L) n, if_pos (hnL n hn)]
  rw [shellTopCoefficient, sum_congr rfl hrow, sum_sub_distrib, ← mul_sum, sum_comm]
  congr 1
  apply sum_congr rfl
  intro ℓ _
  rw [← mul_sum]
  ring

#print axioms shellTopCoefficient_eq_product_sum

private theorem sum_topBand_indicator (N : ℕ) (w : ℝ) (F : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, if n ∈ topBand N w then F n else 0) =
      ∑ n ∈ topBand N w, F n := by
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨(mem_topBand.mp h).1, h⟩⟩

theorem nonRatioForm_topBandPerturbedProfile {g : ℝ → ℝ} {w : ℝ}
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N : ℕ} (hN : 1 ≤ N) (a ψ : ℕ → ℝ) (η : ℝ) :
    nonRatioForm g N (topBandPerturbedProfile a ψ N w η) =
      nonRatioForm g N (fun n => poleVector n * a n) + 2 * η * shellTopCoefficient g a ψ N w := by
  have hbase (m : ℕ) (_hm : m ∈ Icc 1 N) (hm : 2 * (m : ℝ) ≤ N * Real.exp w) :
      topBandPerturbedProfile a ψ N w η m = poleVector m * a m := by
    have hT : m ∉ topBand N w := fun h => (not_lt_of_ge hm) (mem_topBand.mp h).2
    simp only [topBandPerturbedProfile, if_neg hT, mul_zero, add_zero]
  rw [nonRatioForm_eq_of_coefficient_on_bases a hgsupp hw hN _ hbase,
    nonRatioForm_eq_of_coefficient_on_bases a hgsupp hw hN _ (fun _ _ _ => rfl)]
  have hsplit : (∑ n ∈ Icc 1 N,
      (if n ∈ topBand N w then poleVector n * ψ n else 0) * shellCoefficientRow g a N w n) =
      shellTopCoefficient g a ψ N w := by
    simp_rw [ite_mul, zero_mul]
    exact sum_topBand_indicator N w _
  simp only [topBandPerturbedProfile, add_mul, sum_add_distrib, mul_assoc, ← mul_sum, hsplit]
  ring

theorem poleMoments_topBandPerturbedProfile {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (a ψ : ℕ → ℝ) (η : ℝ) :
    (∫ u, atomicTest N (topBandPerturbedProfile a ψ N w η) g u * Real.exp (-(u / 2))) *
      (∫ u, atomicTest N (topBandPerturbedProfile a ψ N w η) g u * Real.exp (u / 2)) =
      poleWeightMinus g * poleWeightPlus g *
        ((∑ n ∈ Icc 1 N, a n / (n : ℝ)) + η * ∑ n ∈ topBand N w, ψ n / (n : ℝ)) *
        ((∑ n ∈ Icc 1 N, a n) + η * ∑ n ∈ topBand N w, ψ n) := by
  rw [poleMoments_atomicTest hg hgsupp]
  have hminus : (∑ n ∈ Icc 1 N, topBandPerturbedProfile a ψ N w η n * poleVector n) =
      (∑ n ∈ Icc 1 N, a n / (n : ℝ)) + η * ∑ n ∈ topBand N w, ψ n / (n : ℝ) := by
    rw [← sum_topBand_indicator N w, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    have hb := poleVector_sq n
    dsimp only [topBandPerturbedProfile]
    split_ifs
    · calc
        _ = poleVector n ^ 2 * (a n + η * ψ n) := by ring
        _ = _ := by rw [hb]; ring
    · calc
        _ = poleVector n ^ 2 * a n := by ring
        _ = _ := by rw [hb]; ring
  have hplus : (∑ n ∈ Icc 1 N, topBandPerturbedProfile a ψ N w η n * Real.sqrt n) =
      (∑ n ∈ Icc 1 N, a n) + η * ∑ n ∈ topBand N w, ψ n := by
    rw [← sum_topBand_indicator N w, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hn).1)).ne'
    have hb : poleVector n * Real.sqrt n = 1 := by rw [poleVector]; field_simp
    dsimp only [topBandPerturbedProfile]
    split_ifs
    · calc
        _ = (poleVector n * Real.sqrt n) * (a n + η * ψ n) := by ring
        _ = _ := by rw [hb, one_mul]
    · calc
        _ = (poleVector n * Real.sqrt n) * a n := by ring
        _ = _ := by rw [hb, one_mul, mul_zero, add_zero]
  rw [hminus, hplus]
  ring

/-- The literal shell–pole block has no quadratic shell contribution on the top band. -/
theorem jointBlock_topBandPerturbedProfile {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N : ℕ} (hN : 1 ≤ N) (a ψ : ℕ → ℝ) (η : ℝ) :
    2 * ((∫ u, atomicTest N (topBandPerturbedProfile a ψ N w η) g u * Real.exp (-(u / 2))) *
        (∫ u, atomicTest N (topBandPerturbedProfile a ψ N w η) g u * Real.exp (u / 2))) -
      nonRatioForm g N (topBandPerturbedProfile a ψ N w η) =
    (2 * ((∫ u, atomicTest N (fun n => poleVector n * a n) g u * Real.exp (-(u / 2))) *
        (∫ u, atomicTest N (fun n => poleVector n * a n) g u * Real.exp (u / 2))) -
      nonRatioForm g N (fun n => poleVector n * a n)) +
      2 * η * jointTopCoefficient g a ψ N w +
      2 * η ^ 2 * (poleWeightMinus g * poleWeightPlus g *
        (∑ n ∈ topBand N w, ψ n / (n : ℝ)) * ∑ n ∈ topBand N w, ψ n) := by
  have hzero : topBandPerturbedProfile a ψ N w 0 = (fun n => poleVector n * a n) := by
    funext n
    simp only [topBandPerturbedProfile, zero_mul, add_zero]
  have hbase := poleMoments_topBandPerturbedProfile hg hgsupp N a ψ 0
  rw [hzero] at hbase
  rw [poleMoments_topBandPerturbedProfile hg hgsupp N a ψ η, hbase,
    nonRatioForm_topBandPerturbedProfile hgsupp hw hN a ψ η, jointTopCoefficient]
  ring

#print axioms jointBlock_topBandPerturbedProfile

end
end GaloisForLFunctions.SuccessorShellArithmetic
