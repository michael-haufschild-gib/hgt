import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFullDownwardPrimeRowCancelsTheNearGammaRow
import GaloisForLFunctions.RHTower.CHMDCompactSourceClass
import GaloisForLFunctions.HTGeometry.ArctanSinTaylor

/-!
# Uniform kernel bounds for the upward prime rows

The literal infinite upward action is exactly a finite sum over positive and
negative integer offsets, with both horizon cutoffs retained. Integer
separation puts every active kernel in a macroscopic product range. There,
logarithmic linearization and the square-root Jacobian have uniform `O(1/N)`
error. Fixed-width boundary prime indices have vanishing reciprocal Mangoldt
mass at the complementary horizon `N/n`.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Prime-power square mass of a product is bounded by its squared logarithmic divisor mass. -/
theorem sum_divisors_vonMangoldt_sq_div_le (ℓ : ℕ) :
    (∑ d ∈ ℓ.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) ^ 2 / d) ≤ (Real.log ℓ) ^ 2 := by
  have hterm (d : ℕ) (hd : d ∈ ℓ.divisors) :
      (ArithmeticFunction.vonMangoldt d : ℝ) ^ 2 / d ≤
        (ArithmeticFunction.vonMangoldt d : ℝ) * Real.log ℓ := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hΛ : (ArithmeticFunction.vonMangoldt d : ℝ) ≤ Real.log ℓ := by
      rw [← ArithmeticFunction.vonMangoldt_sum]
      exact single_le_sum (f := fun d : ℕ => (ArithmeticFunction.vonMangoldt d : ℝ))
        (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg) hd
    calc
      _ ≤ (ArithmeticFunction.vonMangoldt d : ℝ) ^ 2 := div_le_self (sq_nonneg _) hd1
      _ ≤ _ := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_left hΛ ArithmeticFunction.vonMangoldt_nonneg
  calc
    _ ≤ ∑ d ∈ ℓ.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) * Real.log ℓ := sum_le_sum hterm
    _ = _ := by rw [← sum_mul, ArithmeticFunction.vonMangoldt_sum, pow_two]

/-- A finite product strip retains divisor sparsity in the squared norm of its prime rows. -/
theorem sum_prime_product_strip_sq_le (S : Finset ℕ) (hS : ∀ ℓ ∈ S, 0 < ℓ)
    (N : ℕ) (F : ℕ → ℕ → ℝ) (K : ℝ)
    (hF : ∀ n ∈ Icc 1 N, ∀ ℓ ∈ S, |F n ℓ| ≤ K) :
    (∑ n ∈ Icc 1 N, (∑ ℓ ∈ S, if n ∣ ℓ then
      (ArithmeticFunction.vonMangoldt (ℓ / n) : ℝ) / Real.sqrt (ℓ / n : ℕ) * F n ℓ else 0) ^ 2) ≤
      (S.card : ℝ) * K ^ 2 * ∑ ℓ ∈ S, (Real.log ℓ) ^ 2 := by
  classical
  let A : ℕ → ℕ → ℝ := fun n ℓ => if n ∣ ℓ then
    (ArithmeticFunction.vonMangoldt (ℓ / n) : ℝ) / Real.sqrt (ℓ / n : ℕ) * F n ℓ else 0
  have hrow (n : ℕ) : (∑ ℓ ∈ S, A n ℓ) ^ 2 ≤ (S.card : ℝ) * ∑ ℓ ∈ S, A n ℓ ^ 2 := by
    have h := sum_mul_sq_le_sq_mul_sq S (A n) (fun _ => (1 : ℝ))
    simpa only [mul_one, one_mul, one_pow, sum_const, nsmul_eq_mul, mul_comm] using h
  have hcol (ℓ : ℕ) (hℓ : ℓ ∈ S) :
      (∑ n ∈ Icc 1 N, A n ℓ ^ 2) ≤ (Real.log ℓ) ^ 2 * K ^ 2 := by
    have hterm (n : ℕ) (hn : n ∈ Icc 1 N) : A n ℓ ^ 2 ≤
        if n ∣ ℓ then (ArithmeticFunction.vonMangoldt (ℓ / n) : ℝ) ^ 2 / (ℓ / n : ℕ) * K ^ 2 else 0 := by
      by_cases hdiv : n ∣ ℓ
      · dsimp only [A]
        rw [if_pos hdiv, if_pos hdiv, mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        have hf := mul_self_le_mul_self (abs_nonneg (F n ℓ)) (hF n hn ℓ hℓ)
        have hf' : F n ℓ ^ 2 ≤ K ^ 2 := by simpa only [← sq, sq_abs] using hf
        exact mul_le_mul_of_nonneg_left hf' (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      · simp only [A, if_neg hdiv, zero_pow (by norm_num : (2 : ℕ) ≠ 0), le_refl]
    have hsub : (Icc 1 N).filter (fun n => n ∣ ℓ) ⊆ ℓ.divisors := by
      intro n hn
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hn).2, (hS ℓ hℓ).ne'⟩
    calc
      _ ≤ ∑ n ∈ Icc 1 N, if n ∣ ℓ then
          (ArithmeticFunction.vonMangoldt (ℓ / n) : ℝ) ^ 2 / (ℓ / n : ℕ) * K ^ 2 else 0 := sum_le_sum hterm
      _ = ∑ n ∈ (Icc 1 N).filter (fun n => n ∣ ℓ),
          (ArithmeticFunction.vonMangoldt (ℓ / n) : ℝ) ^ 2 / (ℓ / n : ℕ) * K ^ 2 := by rw [sum_filter]
      _ ≤ ∑ n ∈ ℓ.divisors,
          (ArithmeticFunction.vonMangoldt (ℓ / n) : ℝ) ^ 2 / (ℓ / n : ℕ) * K ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg K)
      _ = (∑ d ∈ ℓ.divisors, (ArithmeticFunction.vonMangoldt d : ℝ) ^ 2 / d) * K ^ 2 := by
        rw [← sum_mul, Nat.sum_div_divisors ℓ
          (fun d => (ArithmeticFunction.vonMangoldt d : ℝ) ^ 2 / d)]
      _ ≤ _ := mul_le_mul_of_nonneg_right (sum_divisors_vonMangoldt_sq_div_le ℓ) (sq_nonneg K)
  change (∑ n ∈ Icc 1 N, (∑ ℓ ∈ S, A n ℓ) ^ 2) ≤ _
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (S.card : ℝ) * ∑ ℓ ∈ S, A n ℓ ^ 2 := sum_le_sum fun n _ => hrow n
    _ = (S.card : ℝ) * ∑ ℓ ∈ S, ∑ n ∈ Icc 1 N, A n ℓ ^ 2 := by rw [← mul_sum, sum_comm]
    _ ≤ (S.card : ℝ) * ∑ ℓ ∈ S, (Real.log ℓ) ^ 2 * K ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_le_sum hcol) (Nat.cast_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

theorem exists_lipschitz_shellAutocorr {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ K : NNReal, LipschitzWith K (shellAutocorr φ) := by
  have hgc : HasCompactSupport (shellAutocorr φ) := by
    apply HasCompactSupport.intro (show IsCompact (Set.Icc (-1 : ℝ) 1) from isCompact_Icc)
    intro t ht
    apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
    by_contra h
    exact ht (abs_le.mp (lt_of_not_ge h).le)
  exact _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz (contDiff_shellAutocorr hφ hsupp) hgc

theorem abs_sqrt_ratio_sub_one_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    |Real.sqrt x / Real.sqrt y - 1| ≤ |x - y| / y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hid : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    nlinarith only [Real.sq_sqrt hx, Real.sq_sqrt hy.le]
  have hsmall : |Real.sqrt x - Real.sqrt y| * Real.sqrt y ≤ |x - y| := by
    calc
      _ ≤ |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) :=
        mul_le_mul_of_nonneg_left (by linarith only [Real.sqrt_nonneg x]) (abs_nonneg _)
      _ = _ := by
        rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg x) hs.le), ← abs_mul, hid]
  rw [div_sub_one hs.ne', abs_div, abs_of_pos hs, div_le_div_iff₀ hs hy]
  have h := mul_le_mul_of_nonneg_right hsmall hs.le
  simpa only [mul_assoc, Real.mul_self_sqrt hy.le] using h

theorem lipschitz_log_linearization {G : ℝ → ℝ} {K : NNReal} (hG : LipschitzWith K G)
    (A : ℝ) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |G (A * Real.log (1 + x)) - G (A * x)| ≤ (K : ℝ) * |A| * (2 * x ^ 2) := by
  have h := hG.dist_le_mul (A * Real.log (1 + x)) (A * x)
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul] at h
  calc
    _ ≤ (K : ℝ) * (|A| * |Real.log (1 + x) - x|) := h
    _ ≤ (K : ℝ) * (|A| * (2 * x ^ 2)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (_root_.HTGeometry.abs_log_one_add_sub_self_le hx) (abs_nonneg _)) K.2
    _ = _ := by ring

/-- On a fixed macroscopic product strip, the logarithmic kernel and its square-root
Jacobian differ from the reciprocal-offset kernel by `O(1/N)`. -/
theorem abs_sqrt_log_kernel_sub_linear_le {G : ℝ → ℝ} {K : NNReal}
    (hG : LipschitzWith K G) {M : ℝ} (hM : ∀ t, |G t| ≤ M)
    {c N A B x y : ℝ} (hc : 0 < c) (hN : 0 < N) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : 0 < x) (hy : 0 < y) (hgap : |y - x| ≤ B)
    (hNx : N ≤ A * x) (hNy : N ≤ A * y) (hlarge : 2 * A * B ≤ N) :
    |Real.sqrt x / Real.sqrt y * G (N / c * (Real.log y - Real.log x)) -
      G (N / c * ((y - x) / x))| ≤ (4 * K * A ^ 2 * B ^ 2 / c + A * B * M) / N := by
  have hM0 : 0 ≤ M := (abs_nonneg (G 0)).trans (hM 0)
  have hxinv : 1 / x ≤ A / N := by
    rw [div_le_div_iff₀ hx hN]
    simpa only [one_mul] using hNx
  have hyinv : 1 / y ≤ A / N := by
    rw [div_le_div_iff₀ hy hN]
    simpa only [one_mul] using hNy
  have hz : |(y - x) / x| ≤ A * B / N := by
    rw [abs_div, abs_of_pos hx]
    calc
      _ ≤ B / x := div_le_div_of_nonneg_right hgap hx.le
      _ = B * (1 / x) := by ring
      _ ≤ B * (A / N) := mul_le_mul_of_nonneg_left hxinv hB
      _ = _ := by ring
  have hsmall : A * B / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hN]
    linarith only [hlarge]
  have hlog : Real.log y - Real.log x = Real.log (1 + (y - x) / x) := by
    rw [← Real.log_div hy.ne' hx.ne']
    congr 1
    field_simp
    ring
  have hlin : |G (N / c * (Real.log y - Real.log x)) -
      G (N / c * ((y - x) / x))| ≤ 2 * K * A ^ 2 * B ^ 2 / (c * N) := by
    rw [hlog]
    have h := lipschitz_log_linearization hG (N / c) (hz.trans hsmall)
    rw [abs_of_pos (div_pos hN hc)] at h
    have hzsq : ((y - x) / x) ^ 2 ≤ (A * B / N) ^ 2 := by
      have ht := mul_self_le_mul_self (abs_nonneg _) hz
      simpa only [← sq, sq_abs] using ht
    calc
      _ ≤ (K : ℝ) * (N / c) * (2 * ((y - x) / x) ^ 2) := h
      _ ≤ (K : ℝ) * (N / c) * (2 * (A * B / N) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzsq (by norm_num)) (by positivity)
      _ = _ := by field_simp
  have hratio : |Real.sqrt x / Real.sqrt y - 1| ≤ A * B / N := by
    calc
      _ ≤ |x - y| / y := abs_sqrt_ratio_sub_one_le hx.le hy
      _ ≤ B / y := div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using hgap) hy.le
      _ = B * (1 / y) := by ring
      _ ≤ B * (A / N) := mul_le_mul_of_nonneg_left hyinv hB
      _ = _ := by ring
  have hr0 : 0 ≤ Real.sqrt x / Real.sqrt y := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hr2 : Real.sqrt x / Real.sqrt y ≤ 2 := by
    have h := (le_abs_self (Real.sqrt x / Real.sqrt y - 1)).trans (hratio.trans hsmall)
    linarith only [h]
  have heq : Real.sqrt x / Real.sqrt y * G (N / c * (Real.log y - Real.log x)) -
      G (N / c * ((y - x) / x)) =
      Real.sqrt x / Real.sqrt y * (G (N / c * (Real.log y - Real.log x)) -
        G (N / c * ((y - x) / x))) +
      (Real.sqrt x / Real.sqrt y - 1) * G (N / c * ((y - x) / x)) := by ring
  rw [heq]
  calc
    _ ≤ |Real.sqrt x / Real.sqrt y * (G (N / c * (Real.log y - Real.log x)) -
          G (N / c * ((y - x) / x)))| +
        |(Real.sqrt x / Real.sqrt y - 1) * G (N / c * ((y - x) / x))| := abs_add_le _ _
    _ ≤ 2 * (2 * K * A ^ 2 * B ^ 2 / (c * N)) + A * B / N * M := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr0]
      exact add_le_add (mul_le_mul hr2 hlin (abs_nonneg _) (by norm_num))
        (mul_le_mul hratio (hM _) (abs_nonneg _) (by positivity))
    _ = _ := by ring

/-- Reciprocal prime-power mass in a fixed-width interval about a prime-index horizon. -/
def primeIndexBoundaryMass (B Y : ℕ) : ℝ :=
  ∑ k ∈ Icc (Y - B) (Y + B + 1), (ArithmeticFunction.vonMangoldt k : ℝ) / k

private theorem tendsto_vonMangoldt_div_self_zero :
    Tendsto (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℝ) / k) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  exact squeeze_zero (fun k => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
    (fun k => div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Nat.cast_nonneg k))
    (hlog.comp tendsto_natCast_atTop_atTop)

/-- A bounded number of boundary prime indices has vanishing reciprocal Mangoldt mass. -/
theorem tendsto_primeIndexBoundaryMass (B : ℕ) :
    Tendsto (primeIndexBoundaryMass B) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hden : (0 : ℝ) < 2 * B + 2 := by positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (tendsto_vonMangoldt_div_self_zero.eventually
      (gt_mem_nhds (div_pos (half_pos hε) hden)))
  refine ⟨K + B, ?_⟩
  intro Y hY
  have hcard : ((Icc (Y - B) (Y + B + 1)).card : ℝ) ≤ 2 * B + 2 := by
    rw [Nat.card_Icc]
    exact_mod_cast (show Y + B + 1 + 1 - (Y - B) ≤ 2 * B + 2 by omega)
  have hsum0 : 0 ≤ primeIndexBoundaryMass B Y :=
    sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsum0]
  calc
    _ ≤ ∑ _k ∈ Icc (Y - B) (Y + B + 1), (ε / 2) / (2 * B + 2) := by
      apply sum_le_sum
      intro k hk
      exact (hK k (by have := (mem_Icc.mp hk).1; omega)).le
    _ ≤ (2 * B + 2) * ((ε / 2) / (2 * B + 2)) := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (div_pos (half_pos hε) hden).le
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- A product within `B` of `N` has prime index within a fixed interval about `⌊N/n⌋`. -/
theorem prime_product_boundary_mem {B N n k : ℕ} (hn : 1 ≤ n)
    (hgap : |(k : ℝ) * n - N| ≤ B) :
    k ∈ Icc (N / n - B) (N / n + B + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdist : |(k : ℝ) - (N : ℝ) / n| ≤ B := by
    have heq : (k : ℝ) - (N : ℝ) / n = ((k : ℝ) * n - N) / n := by field_simp
    rw [heq, abs_div, abs_of_pos hn0]
    exact (div_le_div_of_nonneg_right hgap hn0.le).trans (div_le_self (Nat.cast_nonneg B) hn1)
  have hfloorlo : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := by
    rw [le_div_iff₀ hn0]
    exact_mod_cast Nat.div_mul_le_self N n
  have hfloorhi : (N : ℝ) / n < (N / n : ℕ) + 1 := by
    rw [div_lt_iff₀ hn0]
    have hmod := Nat.mod_lt N (by omega : 0 < n)
    have hid := Nat.mod_add_div N n
    have hlt : N < (N / n + 1) * n := by nlinarith only [hmod, hid]
    exact_mod_cast hlt
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdist
  have hnatlo : N / n ≤ k + B := by
    have : ((N / n : ℕ) : ℝ) ≤ (k : ℝ) + B := by linarith only [hfloorlo, hlo]
    exact_mod_cast this
  have hnathi : k ≤ N / n + B + 1 := by
    have : (k : ℝ) < (N / n : ℕ) + B + 1 := by linarith only [hfloorhi, hhi]
    exact_mod_cast this.le
  exact mem_Icc.mpr ⟨by omega, hnathi⟩

/-- The literal upward action has uniformly bounded square-root row size at fixed overlap. -/
theorem abs_sqrt_mul_upwardRamanujanRow_le {g : ℝ → ℝ} (hg : Continuous g)
    {w : ℝ} (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    (hM : 0 < ∫ u, g u ^ 2) {N n : ℕ} (hn : n ∈ Icc 1 N) (m : ℕ) :
    |Real.sqrt n * (upwardPrimeRow g N
      (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n / (∫ u, g u ^ 2))| ≤
      (m.totient : ℝ) *
        (2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N) := by
  let K := SpacingScaleHarmonicAnalysis.lagRange (Real.log N + w + 1)
  let F : ℕ → ℕ → ℝ := fun k j =>
    (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) /
      (∫ u, g u ^ 2)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hF (k j : ℕ) : |F k j| ≤ upInd w k n j := by
    dsimp only [F]
    rw [abs_div, abs_of_pos hM, div_le_iff₀ hM]
    simpa only [mul_comm] using abs_nonRatio_term_le hg
      (HasCompactSupport.intro isCompact_Icc hgsupp) hgsupp k n j
  have heq : Real.sqrt n * (upwardPrimeRow g N
      (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n / (∫ u, g u ^ 2)) =
      ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
        ∑ j ∈ Icc 1 N, Real.sqrt ((n : ℝ) / j) * ramanujanLagCoefficient m j * F k j := by
    rw [upwardPrimeRow_eq_sum hgsupp hw hn]
    simp only [sum_div, mul_sum]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro j _
    rw [Real.sqrt_div hn0]
    dsimp only [F]
    ring
  rw [heq]
  calc
    _ ≤ ∑ k ∈ range K, |(_root_.RHTower.vonMangoldtAtom k) *
        ∑ j ∈ Icc 1 N, Real.sqrt ((n : ℝ) / j) * ramanujanLagCoefficient m j * F k j| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
        ∑ j ∈ Icc 1 N, Real.sqrt ((n : ℝ) / j) * (m.totient : ℝ) * upInd w k n j := by
      apply sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' k)]
      apply mul_le_mul_of_nonneg_left _ (vonMangoldtAtom_nonneg' k)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j)
          (Real.sqrt_nonneg _)) (hF k j) (abs_nonneg _) (by positivity)
    _ = (m.totient : ℝ) * ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
        ∑ j ∈ Icc 1 N, Real.sqrt ((n : ℝ) / j) * upInd w k n j := by
      simp only [mul_sum]
      exact sum_congr rfl fun k _ => sum_congr rfl fun j _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (up_row_le hw (mem_Icc.mp hn).1 K) (Nat.cast_nonneg _)

/-- A finite off-diagonal row supported in an integer strip is exactly its positive
and negative offset sums, with the horizon cutoffs retained. -/
theorem sum_offDiagonal_eq_offset_sums (F : ℕ → ℝ) (N T B : ℕ) (hT : 1 ≤ T)
    (hband : ∀ j ∈ Icc 1 N, T + B < j ∨ j + B < T → F j = 0) :
    (∑ j ∈ Icc 1 N, if j = T then 0 else F j) =
      (∑ h ∈ Icc 1 B, if T + h ≤ N then F (T + h) else 0) +
      ∑ h ∈ Icc 1 B, if h < T ∧ T - h ≤ N then F (T - h) else 0 := by
  have hsplit : (∑ j ∈ Icc 1 N, if j = T then 0 else F j) =
      (∑ j ∈ (Icc 1 N).filter (fun j => T < j), F j) +
      ∑ j ∈ (Icc 1 N).filter (fun j => j < T), F j := by
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    split_ifs <;> first | omega | simp_all only [add_zero, zero_add]
  have hpos : (∑ j ∈ (Icc 1 N).filter (fun j => T < j), F j) =
      ∑ h ∈ (Icc 1 B).filter (fun h => T + h ≤ N), F (T + h) := by
    calc
      _ = ∑ j ∈ (Icc 1 N).filter (fun j => T < j ∧ j ≤ T + B), F j := by
        symm
        apply sum_subset
        · intro j hj
          exact mem_filter.mpr ⟨(mem_filter.mp hj).1, (mem_filter.mp hj).2.1⟩
        · intro j hj hjout
          apply hband j (mem_filter.mp hj).1
          left
          by_contra hb
          exact hjout (mem_filter.mpr ⟨(mem_filter.mp hj).1, (mem_filter.mp hj).2, by omega⟩)
      _ = _ := by
        apply sum_nbij' (fun j : ℕ => j - T) (fun h : ℕ => T + h)
        · intro j hj
          simp only [mem_filter, mem_Icc] at hj ⊢
          omega
        · intro h hh
          simp only [mem_filter, mem_Icc] at hh ⊢
          omega
        · intro j hj
          simp only [mem_filter, mem_Icc] at hj
          omega
        · intro h hh
          simp only [mem_filter, mem_Icc] at hh
          omega
        · intro j hj
          simp only [mem_filter, mem_Icc] at hj
          congr 1
          omega
  have hneg : (∑ j ∈ (Icc 1 N).filter (fun j => j < T), F j) =
      ∑ h ∈ (Icc 1 B).filter (fun h => h < T ∧ T - h ≤ N), F (T - h) := by
    calc
      _ = ∑ j ∈ (Icc 1 N).filter (fun j => j < T ∧ T ≤ j + B), F j := by
        symm
        apply sum_subset
        · intro j hj
          exact mem_filter.mpr ⟨(mem_filter.mp hj).1, (mem_filter.mp hj).2.1⟩
        · intro j hj hjout
          apply hband j (mem_filter.mp hj).1
          right
          by_contra hb
          exact hjout (mem_filter.mpr ⟨(mem_filter.mp hj).1, (mem_filter.mp hj).2, by omega⟩)
      _ = _ := by
        apply sum_nbij' (fun j : ℕ => T - j) (fun h : ℕ => T - h)
        · intro j hj
          simp only [mem_filter, mem_Icc] at hj ⊢
          omega
        · intro h hh
          simp only [mem_filter, mem_Icc] at hh ⊢
          omega
        · intro j hj
          simp only [mem_filter, mem_Icc] at hj
          omega
        · intro h hh
          simp only [mem_filter, mem_Icc] at hh
          omega
        · intro j hj
          simp only [mem_filter, mem_Icc] at hj
          congr 1
          omega
  rw [hsplit, hpos, hneg, sum_filter, sum_filter]

private theorem one_le_abs_nat_gap {T j : ℕ} (hne : T ≠ j) :
    (1 : ℝ) ≤ |(j : ℝ) - T| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hstep : (T : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_iff.mpr h
    rw [abs_of_nonneg (by linarith only [hstep])]
    linarith only [hstep]
  · have hstep : (j : ℝ) + 1 ≤ T := by exact_mod_cast Nat.succ_le_iff.mpr h
    rw [abs_of_nonpos (by linarith only [hstep])]
    linarith only [hstep]

/-- A nonzero integer log gap at scale `c/N` forces both indices to be macroscopic. -/
theorem logWindow_integer_separation {c : ℝ} (hc : 0 < c) {N T j : ℕ}
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hj : 1 ≤ j) (hne : T ≠ j)
    (hlog : |Real.log j - Real.log T| ≤ c / N) :
    (N : ℝ) ≤ c * Real.exp c * T ∧ (N : ℝ) ≤ c * Real.exp c * j := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have he : Real.exp (c / N) - 1 ≤ (c * Real.exp c) / N := by
    calc
      _ ≤ c / N * Real.exp (c / N) := exp_sub_one_le_mul_exp
      _ ≤ c / N * Real.exp c := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (div_le_self hc.le hN1)) (div_pos hc hN0).le
      _ = _ := by ring
  have hdist := (abs_sub_le_of_abs_log_le hj0 hT0 hlog).trans
    (mul_le_mul_of_nonneg_left he hT0.le)
  have hdist' := (abs_sub_le_of_abs_log_le hT0 hj0
    (by simpa only [abs_sub_comm] using hlog)).trans
    (mul_le_mul_of_nonneg_left he hj0.le)
  have hgap := one_le_abs_nat_gap hne
  have hgap' : (1 : ℝ) ≤ |(T : ℝ) - j| := by simpa only [abs_sub_comm] using hgap
  constructor
  · have h := hgap.trans hdist
    rw [← mul_div_assoc, le_div_iff₀ hN0] at h
    simpa only [one_mul, mul_one, mul_comm] using h
  · have h := hgap'.trans hdist'
    rw [← mul_div_assoc, le_div_iff₀ hN0] at h
    simpa only [one_mul, mul_one, mul_comm] using h

/-- Both the actual and reciprocal offset kernels vanish outside the macroscopic range;
inside it their difference is uniformly `O(1/N)`. -/
theorem exists_logPrimeKernel_linearization_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T j : ℕ,
      1 ≤ T → 1 ≤ j → T ≠ j → |(j : ℝ) - T| ≤ B →
      |Real.sqrt T / Real.sqrt j *
          shellAutocorr φ ((N : ℝ) / c * (Real.log j - Real.log T)) -
        shellAutocorr φ ((N : ℝ) / c * (((j : ℝ) - T) / T))| ≤ C / N := by
  obtain ⟨K, hK⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  let A := c * Real.exp c + 2 * c + 1
  let C := 4 * (K : ℝ) * A ^ 2 * (B : ℝ) ^ 2 / c + A * B * (∫ u, φ u ^ 2)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hca : c * Real.exp c ≤ A := by dsimp only [A]; linarith only [hc]
  have h2ca : 2 * c ≤ A := by
    have hce := mul_pos hc (Real.exp_pos c)
    dsimp only [A]
    linarith only [hce]
  have hcA : c ≤ A := (by linarith only [hc] : c ≤ 2 * c).trans h2ca
  have hM0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, max 1 ⌈2 * A * B⌉₊, ?_⟩
  intro N hN T j hT hj hne hgap
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlarge : 2 * A * (B : ℝ) ≤ N := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hN)
  have hlargec : 2 * c * (B : ℝ) ≤ N :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcA (by norm_num))
      (Nat.cast_nonneg B)).trans hlarge
  by_cases hact : shellAutocorr φ ((N : ℝ) / c * (Real.log j - Real.log T)) = 0
  · by_cases hlin : shellAutocorr φ ((N : ℝ) / c * (((j : ℝ) - T) / T)) = 0
    · rw [hact, hlin, mul_zero, sub_self, abs_zero]
      exact div_nonneg hC hN0.le
    · have hsmall : |(N : ℝ) / c * (((j : ℝ) - T) / T)| < 1 := by
        by_contra h
        exact hlin (shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (le_of_not_gt h))
      rw [abs_mul, abs_of_pos (div_pos hN0 hc), abs_div, abs_of_pos hT0] at hsmall
      have hsep := one_le_abs_nat_gap hne
      have hfrac : (N : ℝ) / c * (1 / T) < 1 :=
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsep hT0.le)
          (div_pos hN0 hc).le).trans_lt hsmall
      have hNT : (N : ℝ) ≤ c * T := by
        have h := (div_lt_one (mul_pos hc hT0)).mp
          (show (N : ℝ) / (c * T) < 1 by convert hfrac using 1; ring)
        exact h.le
      have hTj : (T : ℝ) ≤ j + B := by linarith only [(abs_le.mp hgap).1]
      have hNj : (N : ℝ) ≤ 2 * c * j := by
        have hmul := mul_le_mul_of_nonneg_left hTj hc.le
        linarith only [hNT, hmul, hlargec]
      exact abs_sqrt_log_kernel_sub_linear_le hK
        (fun t => abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) t)
        hc hN0 hA (Nat.cast_nonneg B) hT0 hj0 hgap
        (hNT.trans (mul_le_mul_of_nonneg_right hcA hT0.le))
        (hNj.trans (mul_le_mul_of_nonneg_right h2ca hj0.le)) hlarge
  · have hsmall : |(N : ℝ) / c * (Real.log j - Real.log T)| < 1 := by
      by_contra h
      exact hact (shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (le_of_not_gt h))
    have hlog : |Real.log j - Real.log T| ≤ c / N := by
      rw [abs_mul, abs_of_pos (div_pos hN0 hc)] at hsmall
      have h := (lt_div_iff₀ (div_pos hN0 hc)).mpr
        (show |Real.log j - Real.log T| * ((N : ℝ) / c) < 1 by simpa only [mul_comm] using hsmall)
      have heq : 1 / ((N : ℝ) / c) = c / N := by field_simp
      rw [heq] at h
      exact h.le
    obtain ⟨hNT, hNj⟩ := logWindow_integer_separation hc hN1 hT hj hne hlog
    exact abs_sqrt_log_kernel_sub_linear_le hK
      (fun t => abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) t)
      hc hN0 hA (Nat.cast_nonneg B) hT0 hj0 hgap
      (hNT.trans (mul_le_mul_of_nonneg_right hca hT0.le))
      (hNj.trans (mul_le_mul_of_nonneg_right hca hj0.le)) hlarge

/-- An upward product touching a horizon atom lies in a fixed integer offset strip. -/
theorem upward_product_distance_le {c : ℝ} (hc : 0 < c) {N T j : ℕ}
    (hT : 1 ≤ T) (hj : j ∈ Icc 1 N)
    (hlog : |Real.log T - Real.log j| ≤ c / N) :
    |(T : ℝ) - j| ≤ exteriorPrimeStrip c := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hj).1.trans (mem_Icc.mp hj).2
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  calc
    _ ≤ (j : ℝ) * (Real.exp (c / N) - 1) := abs_sub_le_of_abs_log_le hT0 hj0 hlog
    _ ≤ (j : ℝ) * (c / N * Real.exp (c / N)) :=
      mul_le_mul_of_nonneg_left exp_sub_one_le_mul_exp hj0.le
    _ ≤ (N : ℝ) * (c / N * Real.exp (c / N)) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (mem_Icc.mp hj).2) (by positivity)
    _ = c * Real.exp (c / N) := by field_simp
    _ ≤ c * Real.exp c := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (div_le_self hc.le hN1)) hc.le
    _ ≤ _ := Nat.le_ceil _

/-- The positive offset contribution, with its actual horizon cutoff. -/
def positiveUpwardOffset (g : ℝ → ℝ) (N m n k h : ℕ) : ℝ :=
  if k * n + h ≤ N then ramanujanLagCoefficient m (k * n + h) / Real.sqrt (k * n + h : ℕ) *
    bumpCorr g (Real.log (k * n : ℕ) - Real.log (k * n + h : ℕ)) else 0

/-- The negative offset contribution, with both positivity and horizon cutoffs. -/
def negativeUpwardOffset (g : ℝ → ℝ) (N m n k h : ℕ) : ℝ :=
  if h < k * n ∧ k * n - h ≤ N then
    ramanujanLagCoefficient m (k * n - h) / Real.sqrt (k * n - h : ℕ) *
      bumpCorr g (Real.log (k * n : ℕ) - Real.log (k * n - h : ℕ)) else 0

/-- Exact offset reindexing of the literal infinite upward prime-power action. -/
theorem upwardRamanujanRow_eq_offsets {g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N n : ℕ} (hn : n ∈ Icc 1 N)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0) (m : ℕ) :
    upwardPrimeRow g N (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n =
      ∑ k ∈ Icc 1 (N + exteriorPrimeStrip c), _root_.RHTower.vonMangoldtAtom k *
        ∑ h ∈ Icc 1 (exteriorPrimeStrip c),
          (positiveUpwardOffset g N m n k h + negativeUpwardOffset g N m n k h) := by
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  let B := exteriorPrimeStrip c
  have hinner (k : ℕ) (hk : 1 ≤ k) :
      (∑ j ∈ Icc 1 N, ramanujanLagCoefficient m j / Real.sqrt j *
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) =
      ∑ h ∈ Icc 1 B, (positiveUpwardOffset g N m n k h + negativeUpwardOffset g N m n k h) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hT : 1 ≤ k * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hlog (j : ℕ) : Real.log k - (Real.log j - Real.log n) =
        Real.log (k * n : ℕ) - Real.log j := by
      rw [Nat.cast_mul, Real.log_mul hk0.ne' hn0.ne']
      ring
    let F : ℕ → ℝ := fun j => ramanujanLagCoefficient m j / Real.sqrt j *
      bumpCorr g (Real.log (k * n : ℕ) - Real.log j)
    have hband : ∀ j ∈ Icc 1 N, k * n + B < j ∨ j + B < k * n → F j = 0 := by
      intro j hj hout
      have hgap : c / N < |Real.log (k * n : ℕ) - Real.log j| := by
        by_contra h
        have hd := upward_product_distance_le hc hT hj (le_of_not_gt h)
        have hlow := (abs_le.mp hd).1
        have hhigh := (abs_le.mp hd).2
        have h1 : j ≤ k * n + B := by
          have : (j : ℝ) ≤ (k * n : ℕ) + B := by linarith only [hlow]
          exact_mod_cast this
        have h2 : k * n ≤ j + B := by
          have : ((k * n : ℕ) : ℝ) ≤ j + B := by linarith only [hhigh]
          exact_mod_cast this
        omega
      dsimp only [F]
      rw [bumpCorr_eq_zero hgsupp hgap, mul_zero]
    calc
      _ = ∑ j ∈ Icc 1 N, if j = k * n then 0 else F j := by
        apply sum_congr rfl
        intro j _
        rw [hlog]
        split_ifs <;> simp only [mul_zero, F]
      _ = _ := by
        rw [sum_offDiagonal_eq_offset_sums F N (k * n) B hT hband, ← sum_add_distrib]
        exact sum_congr rfl fun h _ => rfl
  rw [upwardPrimeRow]
  have hrew : (∑' k : ℕ, _root_.RHTower.vonMangoldtAtom k * ∑ j ∈ Icc 1 N,
      ramanujanLagCoefficient m j / Real.sqrt j *
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) =
      ∑' k : ℕ, _root_.RHTower.vonMangoldtAtom k * ∑ h ∈ Icc 1 B,
        (positiveUpwardOffset g N m n k h + negativeUpwardOffset g N m n k h) := by
    apply tsum_congr
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [vonMangoldtAtom_eq_zero_of_lt_two (by norm_num : (0 : ℕ) < 2), zero_mul]
    · rw [hinner k hk]
  rw [hrew]
  apply tsum_eq_sum
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [vonMangoldtAtom_eq_zero_of_lt_two (by norm_num : (0 : ℕ) < 2), zero_mul]
  · have hbig : N + B < k := by
      by_contra h
      exact hk (mem_Icc.mpr ⟨hk0, by omega⟩)
    have hkn : k ≤ k * n := by simpa only [mul_one] using Nat.mul_le_mul_left k hn1
    have hzero : (∑ h ∈ Icc 1 B,
        (positiveUpwardOffset g N m n k h + negativeUpwardOffset g N m n k h)) = 0 := by
      apply sum_eq_zero
      intro h hh
      have hhB := (mem_Icc.mp hh).2
      have hpos : ¬ k * n + h ≤ N := by omega
      have hneg : ¬ (h < k * n ∧ k * n - h ≤ N) := by omega
      simp only [positiveUpwardOffset, negativeUpwardOffset, if_neg hpos, if_neg hneg, add_zero]
    rw [hzero, mul_zero]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.upwardRamanujanRow_eq_offsets

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_logPrimeKernel_linearization_bound

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_sqrt_mul_upwardRamanujanRow_le

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_primeIndexBoundaryMass

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_prime_product_strip_sq_le
