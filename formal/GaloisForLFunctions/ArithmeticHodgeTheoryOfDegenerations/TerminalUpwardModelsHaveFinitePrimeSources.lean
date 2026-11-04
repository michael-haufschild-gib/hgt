import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPrimeBoundaryMassHasFiniteSupport
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalPrimeMeansAreFiniteRiemannSums

/-!
# Terminal upward models have finite prime sources

Uniform shell errors can be summed against a terminal receiver before
letting the horizon grow. The polar shell retains the finite prime
mean; nonpolar shell errors disappear after division by the overlap.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CriticalArithmeticCorrelationTheory

local notation "Λ" => ArithmeticFunction.vonMangoldt

private theorem terminal_multiplier_le {δ : ℝ} (hδ : 0 < δ)
    {N n k K : ℕ} (hN : 1 ≤ N) (hn : δ * N ≤ n) (hkn : k * n ≤ N)
    (hK : 1 / δ ≤ K) : k ≤ K := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hprod : (k : ℝ) * δ * N ≤ N := by
    calc
      _ = (k : ℝ) * (δ * N) := by ring
      _ ≤ (k : ℝ) * n := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg k)
      _ ≤ _ := by exact_mod_cast hkn
  have hkd : (k : ℝ) * δ ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_right hN0).mp
    simpa only [one_mul] using hprod
  have hkK : (k : ℝ) ≤ K := ((le_div_iff₀ hδ).mpr hkd).trans hK
  exact_mod_cast hkK

private theorem abs_terminal_hyperbola_error_le
    {F : ℝ → ℝ} {B δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0)
    {N K : ℕ} (hN : 1 ≤ N) (hK : 1 / δ ≤ K)
    {V : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hV : ∀ p ∈ Icc 1 N, δ * N ≤ p → |V p| ≤ C) :
    |∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n *
      ∑ k ∈ Icc 1 (N / n), (Λ k : ℝ) / k * V (k * n)| ≤
      (B / δ) * C * ∑ k ∈ Icc 1 K, (Λ k : ℝ) / k := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hreceiver : ∀ n ∈ Icc 1 N, F ((n : ℝ) / N) ≠ 0 → δ * N ≤ n := by
    intro n _ hn
    have hx : δ < (n : ℝ) / N := lt_of_not_ge fun hx => hn (hzero _ hx)
    exact ((lt_div_iff₀ hN0).mp hx).le
  let P : ℝ := ∑ k ∈ Icc 1 K, (Λ k : ℝ) / k
  have hP : 0 ≤ P := sum_nonneg fun k _ => vonMangoldt_div_nonneg k
  have hpoint : ∀ n ∈ Icc 1 N,
      |F ((n : ℝ) / N) / n * ∑ k ∈ Icc 1 (N / n), (Λ k : ℝ) / k * V (k * n)| ≤
        |F ((n : ℝ) / N)| / n * (C * P) := by
    intro n hn
    by_cases hz : F ((n : ℝ) / N) = 0
    · rw [hz, zero_div, zero_mul, abs_zero, zero_div, zero_mul]
    have hnδ := hreceiver n hn hz
    have hn1 : 0 < n := (mem_Icc.mp hn).1
    have hcut : N / n ≤ K := terminal_multiplier_le hδ hN hnδ
      ((Nat.le_div_iff_mul_le hn1).mp le_rfl) hK
    have hrow : |∑ k ∈ Icc 1 (N / n), (Λ k : ℝ) / k * V (k * n)| ≤ C * P := by
      calc
        _ ≤ ∑ k ∈ Icc 1 (N / n), |(Λ k : ℝ) / k * V (k * n)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Icc 1 (N / n), C * ((Λ k : ℝ) / k) := by
          apply sum_le_sum
          intro k hk
          have hk1 : 0 < k := (mem_Icc.mp hk).1
          have hknN := (Nat.le_div_iff_mul_le hn1).mp (mem_Icc.mp hk).2
          have hkn1 : 1 ≤ k * n := Nat.mul_pos hk1 hn1
          have hnk : n ≤ k * n := by
            calc
              n = 1 * n := (one_mul n).symm
              _ ≤ k * n := Nat.mul_le_mul_right n (show 1 ≤ k from hk1)
          have hpδ : δ * N ≤ (k * n : ℕ) := hnδ.trans (by exact_mod_cast hnk)
          rw [abs_mul, abs_of_nonneg (vonMangoldt_div_nonneg k)]
          exact (mul_le_mul_of_nonneg_left (hV (k * n) (mem_Icc.mpr ⟨hkn1, hknN⟩) hpδ)
            (vonMangoldt_div_nonneg k)).trans_eq (by ring)
        _ ≤ ∑ k ∈ Icc 1 K, C * ((Λ k : ℝ) / k) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro k hk
            exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans hcut⟩
          · intro k _ _
            exact mul_nonneg hC (vonMangoldt_div_nonneg k)
        _ = C * P := by rw [← mul_sum]
    rw [abs_mul, abs_div, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left hrow (div_nonneg (abs_nonneg _) (Nat.cast_nonneg n))
  calc
    _ ≤ ∑ n ∈ Icc 1 N,
        |F ((n : ℝ) / N) / n * ∑ k ∈ Icc 1 (N / n), (Λ k : ℝ) / k * V (k * n)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 N, |F ((n : ℝ) / N)| / n * (C * P) := sum_le_sum hpoint
    _ = (∑ n ∈ Icc 1 N, |F ((n : ℝ) / N)| / n) * (C * P) := by rw [sum_mul]
    _ ≤ (B / δ) * (C * P) := mul_le_mul_of_nonneg_right
      (sum_terminal_abs_div_le hδ (fun n => hF _) hN hreceiver) (mul_nonneg hC hP)
    _ = _ := by ring

private theorem terminal_hyperbola_linear_mean_eq
    {F : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hzero : ∀ x, x ≤ δ → F x = 0)
    {N K : ℕ} (hN : 1 ≤ N) (hKN : K ≤ N) (hK : 1 / δ ≤ K) (a c : ℝ) :
    (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n *
      ∑ k ∈ Icc 1 (N / n), (Λ k : ℝ) / k * (a * c * (k * n : ℕ) / N)) =
      a * c * (∑ k ∈ Icc 1 K, (Λ k : ℝ) *
        ((∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N)) / N)) := by
  let W : ℕ → ℕ → ℝ := fun n k => (1 / n) * ((Λ k : ℝ) / k * (a * c * (k * n : ℕ) / N))
  have he : (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n *
      ∑ k ∈ Icc 1 (N / n), (Λ k : ℝ) / k * (a * c * (k * n : ℕ) / N)) =
      ∑ n ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / n), F ((n : ℝ) / N) * W n k := by
    apply sum_congr rfl
    intro n _
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by dsimp only [W]; ring
  rw [he, sum_terminal_hyperbola_eq_finite hδ hzero hN hKN hK, mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [sum_div, mul_sum, mul_sum]
  apply sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  dsimp only [W]
  push_cast
  field_simp [hn0.ne', hk0.ne', hN0.ne']

private theorem abs_terminal_upwardModel_sub_linear_mean_le
    {φ F : ℝ → ℝ} {B δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0)
    {N K H m : ℕ} (hN : 1 ≤ N) (hKN : K ≤ N) (hK : 1 / δ ≤ K)
    {a c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hshell : ∀ p ∈ Icc 1 N, δ * N ≤ p →
      |upwardShellModel φ c N m H p - a * c * p / N| ≤ C) :
    |(∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ c N m H n) / c -
      a * (∑ k ∈ Icc 1 K, (Λ k : ℝ) *
        ((∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N)) / N))| ≤
      ((B / δ) * C * ∑ k ∈ Icc 1 K, (Λ k : ℝ) / k) / c := by
  have hb := abs_terminal_hyperbola_error_le hδ hF hzero hN hK hC hshell
  have he : (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n *
      ∑ k ∈ Icc 1 (N / n), (Λ k : ℝ) / k *
        (upwardShellModel φ c N m H (k * n) - a * c * (k * n : ℕ) / N)) =
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ c N m H n) -
        a * c * (∑ k ∈ Icc 1 K, (Λ k : ℝ) *
          ((∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N)) / N)) := by
    rw [← terminal_hyperbola_linear_mean_eq hδ hzero hN hKN hK a c, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    unfold upwardModel
    rw [← mul_sub, ← sum_sub_distrib]
    congr 1
    exact sum_congr rfl fun _ _ => by ring
  rw [he] at hb
  have hid :
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ c N m H n) / c -
        a * (∑ k ∈ Icc 1 K, (Λ k : ℝ) *
          ((∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N)) / N)) =
      ((∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ c N m H n) -
        a * c * (∑ k ∈ Icc 1 K, (Λ k : ℝ) *
          ((∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N)) / N))) / c := by
    field_simp [hc.ne']
  rw [hid, abs_div, abs_of_pos hc]
  exact div_le_div_of_nonneg_right hb hc.le

private theorem terminal_shell_ratio_le {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    {N H p : ℕ} (hN : 1 ≤ N) (hp : 1 ≤ p) (hpδ : δ * N ≤ p)
    (hH : (H : ℝ) ≤ 3 * c) : (H : ℝ) / (c * p / N) ≤ 3 / δ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hr : 0 < c * p / N := div_pos (mul_pos hc hp0) hN0
  have hrlo : c * δ ≤ c * p / N := by
    apply (le_div_iff₀ hN0).mpr
    exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hpδ hc.le)
  apply (div_le_div_iff₀ hr hδ).mpr
  calc
    _ ≤ (3 * c) * δ := mul_le_mul_of_nonneg_right hH hδ.le
    _ = 3 * (c * δ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrlo (by norm_num)

/-- The polar model differs from its finite prime source by explicit shell and Riemann errors. -/
theorem abs_terminal_upwardModel_one_sub_source_le
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B LF δ L : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0) (hLF : 0 ≤ LF)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|) (hL : 0 ≤ L)
    (hGL : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ L * |x - y|)
    {N K H : ℕ} (hN : 1 ≤ N) (hKN : K ≤ N) (hK : 1 / δ ≤ K)
    {c : ℝ} (hc : 0 < c) (hHlo : c ≤ H) (hHhi : (H : ℝ) ≤ 3 * c) :
    let a := (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)
    |(∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ c N 1 H n) / c -
      a * finitePrimeTerminalMean F K| ≤
      (6 * B * L / ((∫ u, φ u ^ 2) * δ ^ 2) * (∑ k ∈ Icc 1 K, (Λ k : ℝ) / k)) / c +
      a * ((LF + B) / N) * (∑ k ∈ Icc 1 K, (Λ k : ℝ)) := by
  intro a
  have ha : 0 ≤ a := div_nonneg (sq_nonneg _) hM.le
  have hC : 0 ≤ 6 * L / ((∫ u, φ u ^ 2) * δ) := by positivity
  have hshell : ∀ p ∈ Icc 1 N, δ * N ≤ p →
      |upwardShellModel φ c N 1 H p - a * c * p / N| ≤
        6 * L / ((∫ u, φ u ^ 2) * δ) := by
    intro p hp hpδ
    have hb := abs_upwardShellModel_one_sub_mean_le hφ hsupp hM hc hL hGL
      (mem_Icc.mp hp).1 (mem_Icc.mp hp).2 hHlo
    have hrat := terminal_shell_ratio_le hδ hc hN (mem_Icc.mp hp).1 hpδ hHhi
    have he : a * c * p / N = a * (c * p / N) := by ring
    rw [he]
    apply hb.trans
    calc
      _ = (2 * L / (∫ u, φ u ^ 2)) * ((H : ℝ) / (c * p / N)) := by ring
      _ ≤ (2 * L / (∫ u, φ u ^ 2)) * (3 / δ) :=
        mul_le_mul_of_nonneg_left hrat (by positivity)
      _ = _ := by ring
  have hmodel := abs_terminal_upwardModel_sub_linear_mean_le hδ hF hzero hN hKN hK hc hC hshell
  have hriemann := abs_finitePrime_riemannSum_sub_mean_le hF hLF hFL hN K
  let S : ℝ := ∑ k ∈ Icc 1 K, (Λ k : ℝ) *
    ((∑ n ∈ Icc 1 (N / k), F ((n : ℝ) / N)) / N)
  have he :
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ c N 1 H n) / c -
        a * finitePrimeTerminalMean F K =
      ((∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ c N 1 H n) / c - a * S) +
        a * (S - finitePrimeTerminalMean F K) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  have htail : |a * (S - finitePrimeTerminalMean F K)| ≤
      a * ((LF + B) / N) * (∑ k ∈ Icc 1 K, (Λ k : ℝ)) := by
    rw [abs_mul, abs_of_nonneg ha]
    exact (mul_le_mul_of_nonneg_left hriemann ha).trans_eq (by ring)
  exact (add_le_add hmodel htail).trans_eq (by field_simp [hM.ne', hδ.ne', hc.ne'])

/-- Every nonpolar model has a reciprocal-overlap bound against a terminal receiver. -/
theorem abs_terminal_upwardModel_nonpolar_le
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B δ L : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0) (hL : 0 ≤ L)
    (hGL : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ L * |x - y|)
    {N K H m : ℕ} (hN : 1 ≤ N) (hKN : K ≤ N) (hK : 1 / δ ≤ K)
    (hH : 1 ≤ H) (hm : 2 ≤ m)
    {c : ℝ} (hc : 0 < c) (hHhi : (H : ℝ) ≤ 3 * c) :
    |(∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ c N m H n) / c| ≤
      ((B / δ) * (4 * m * m.totient * (1 + 3 * L / ((∫ u, φ u ^ 2) * δ))) *
        (∑ k ∈ Icc 1 K, (Λ k : ℝ) / k)) / c := by
  let C : ℝ := 4 * m * m.totient * (1 + 3 * L / ((∫ u, φ u ^ 2) * δ))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hshell : ∀ p ∈ Icc 1 N, δ * N ≤ p → |upwardShellModel φ c N m H p - 0 * c * p / N| ≤ C := by
    intro p hp hpδ
    simp only [zero_mul, zero_div, sub_zero]
    apply (abs_upwardShellModel_nonpolar_le hφ hsupp hM hc hL hGL hN hH (mem_Icc.mp hp).1 hm).trans
    have hrat := terminal_shell_ratio_le hδ hc hN (mem_Icc.mp hp).1 hpδ hHhi
    have hsmall : L * H / ((∫ u, φ u ^ 2) * (c * p / N)) ≤ 3 * L / ((∫ u, φ u ^ 2) * δ) := by
      calc
        _ = (L / (∫ u, φ u ^ 2)) * ((H : ℝ) / (c * p / N)) := by ring
        _ ≤ (L / (∫ u, φ u ^ 2)) * (3 / δ) := mul_le_mul_of_nonneg_left hrat (by positivity)
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hsmall) (by positivity)
  simpa only [zero_mul, sub_zero] using
    abs_terminal_upwardModel_sub_linear_mean_le hδ hF hzero hN hKN hK hc hC hshell

/-- The polar model retains exactly the finite prime mean on every growing overlap clock. -/
theorem tendsto_terminal_upwardModel_one
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B LF δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0) (hLF : 0 ≤ LF)
    (hFL : ∀ x y, |F x - F y| ≤ LF * |x - y|)
    {K : ℕ} (hK : 1 / δ ≤ K) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (hcTop : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ (c N) N 1 ⌈2 * c N⌉₊ n) / c N)
      atTop (𝓝 (((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) * finitePrimeTerminalMean F K)) := by
  obtain ⟨L, hL, hGL⟩ := exists_shellAutocorr_lipschitz hφ hsupp
  let a : ℝ := (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)
  let C : ℝ := 6 * B * L / ((∫ u, φ u ^ 2) * δ ^ 2) * (∑ k ∈ Icc 1 K, (Λ k : ℝ) / k)
  let D : ℝ := a * (LF + B) * (∑ k ∈ Icc 1 K, (Λ k : ℝ))
  have hlim := ((tendsto_inv_atTop_zero.comp hcTop).const_mul C).add
    (tendsto_const_div_atTop_nhds_zero_nat D)
  simp only [mul_zero, zero_add] at hlim
  have hz : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ (c N) N 1 ⌈2 * c N⌉₊ n) / c N -
        a * finitePrimeTerminalMean F K) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop K] with N hN hKN
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    have hHlo : c N ≤ (⌈2 * c N⌉₊ : ℝ) := (by linarith only [hc N] : c N ≤ 2 * c N).trans (Nat.le_ceil _)
    have hHhi : (⌈2 * c N⌉₊ : ℝ) ≤ 3 * c N := by
      have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 * c N by positivity)
      linarith only [hh, hc N]
    rw [Real.norm_eq_abs]
    exact (abs_terminal_upwardModel_one_sub_source_le hφ hsupp hM hδ hF hzero hLF hFL
      hL hGL hN hKN hK hc0 hHlo hHhi).trans_eq (by dsimp only [C, D, a, Function.comp_def]; ring)
  simpa only [zero_add, sub_add_cancel] using hz.add_const (a * finitePrimeTerminalMean F K)

/-- Every fixed nonpolar model vanishes on every growing overlap clock. -/
theorem tendsto_terminal_upwardModel_nonpolar
    {φ F : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {B δ : ℝ} (hδ : 0 < δ) (hF : ∀ x, |F x| ≤ B)
    (hzero : ∀ x, x ≤ δ → F x = 0)
    {m : ℕ} (hm : 2 ≤ m) {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    (hcTop : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F ((n : ℝ) / N) / n * upwardModel φ (c N) N m ⌈2 * c N⌉₊ n) / c N)
      atTop (𝓝 0) := by
  obtain ⟨L, hL, hGL⟩ := exists_shellAutocorr_lipschitz hφ hsupp
  let K : ℕ := ⌈1 / δ⌉₊
  let C : ℝ := (B / δ) * (4 * m * m.totient * (1 + 3 * L / ((∫ u, φ u ^ 2) * δ))) *
    (∑ k ∈ Icc 1 K, (Λ k : ℝ) / k)
  have hlim := (tendsto_inv_atTop_zero.comp hcTop).const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop K] with N hN hKN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hHlo : 2 * c N ≤ (⌈2 * c N⌉₊ : ℝ) := Nat.le_ceil _
  have hH1 : 1 ≤ ⌈2 * c N⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈2 * c N⌉₊ : ℝ) := by linarith only [hc N, hHlo]
    exact_mod_cast hh
  have hHhi : (⌈2 * c N⌉₊ : ℝ) ≤ 3 * c N := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 * c N by positivity)
    linarith only [hh, hc N]
  rw [Real.norm_eq_abs]
  exact (abs_terminal_upwardModel_nonpolar_le hφ hsupp hM hδ hF hzero hL hGL hN hKN
    (show 1 / δ ≤ (K : ℝ) from Nat.le_ceil _) hH1 hm hc0 hHhi).trans_eq
      (by dsimp only [C, Function.comp_def]; ring)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_upwardModel_one_sub_source_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_terminal_upwardModel_nonpolar_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_upwardModel_one
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_upwardModel_nonpolar
