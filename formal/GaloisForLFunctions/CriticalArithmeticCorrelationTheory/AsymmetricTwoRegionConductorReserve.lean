import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteWeilSplitCrossBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheSeparatedPrefixRetainsItsDefect
import GaloisForLFunctions.CompletedArithmeticForms.ConductorPrefixLeakage

/-!
# Asymmetric prefix/terminal reserve and `O(c^{11})` conductor confinement

Splitting the atomic test at the linear cutoff `linearDefectCutoff c = ⌈max 3 (256 e² c)⌉₊`
keeps the separated prefix inside the non-overlapping regime while eliminating non-ratio prime
lags whose upper endpoint lies in the prefix:

1. **Pole source vanishing on `(conductorSubspace 1 N)ᗮ`.** Orthogonality to the constant
   Ramanujan mode annihilates `poleFunctional`, so the rank-2 pole moment product vanishes
   identically on `(conductorSubspace 1 N)ᗮ`.
2. **Split-source logarithmic tail localization.** Outgoing prime-power edges crossing `M = N / L`
   pay the `O((1 + u) log L)` Mertens cost strictly on the prefix mass `P`, while edges whose
   lower endpoint already exceeds `M` have step `< L` and cost at most `(log 4 + 4) L` on the
   terminal mass `S` without spending prime defect.
3. **Split-row non-ratio lag bound.** Because `|k m - n| ≥ 1` and `|log(k m) - log n| ≤ c / N`
   force `n ≥ N / (e c) > N / linearDefectCutoff c`, `upInd` vanishes for `n ≤ M`; prefix-to-tail
   pairs cost `O(c^9) P + (δ / 8)(log N + 1) S` and tail-to-tail pairs cost `O(c^2) S`.
4. **Asymmetric two-region reserve, `α < 1 / 9` polynomial-conductor complement coercivity, and
   `O(c^{11})` sublevel confinement.** On `(conductorSubspace R N)ᗮ`, `K c^9 ≤ log R / D - 1`
   suffices for coercivity, lifting `(conductorSubspace ⌊N^θ⌋₊ N)ᗮ` coercivity to `0 < α < 1 / 9`
   for every `θ > 0`, lowering cross-term absorption to `K c^{11} ≤ log R / D - 1`, and confining
   bounded-energy unit vectors orthogonal to `conductorSubspace Q₁ N` to
   `log R' ≤ C_R c^{11} + log Q₁` whenever `c^{16} / log N` is small.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23 ArithmeticFunction
open scoped Classical BigOperators RealInnerProductSpace ArithmeticFunction Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics ArithmeticEffectivityTheory

/-! ## Section 1: Linear Defect Cutoff and Pole Vanishing on `(conductorSubspace 1 N)ᗮ` -/

/-- Linear horizon-ratio cutoff `⌈max 3 (256 e² c)⌉₊` separating the prefix from overlap lags. -/
def linearDefectCutoff (c : ℝ) : ℕ :=
  ⌈max 3 (256 * Real.exp 2 * c)⌉₊

/-- Explicit two-sided linear bounds for `linearDefectCutoff c` across `1 ≤ c`. -/
theorem linearDefectCutoff_bounds {c : ℝ} (hc : 1 ≤ c) :
    3 ≤ linearDefectCutoff c ∧
      4 * c ≤ (linearDefectCutoff c : ℝ) ∧
      256 * Real.exp 2 * c ≤ (linearDefectCutoff c : ℝ) ∧
      (linearDefectCutoff c : ℝ) ≤ (256 * Real.exp 2 + 4) * c := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have he2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hceil : max 3 (256 * Real.exp 2 * c) ≤ (linearDefectCutoff c : ℝ) :=
    Nat.le_ceil _
  have h3R : (3 : ℝ) ≤ linearDefectCutoff c := (le_max_left _ _).trans hceil
  have h256 : 256 * Real.exp 2 * c ≤ (linearDefectCutoff c : ℝ) :=
    (le_max_right _ _).trans hceil
  have h4c : 4 * c ≤ (linearDefectCutoff c : ℝ) := by
    nlinarith only [h256, he2, hc0]
  have hup0 : (linearDefectCutoff c : ℝ) < max 3 (256 * Real.exp 2 * c) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hmax : max 3 (256 * Real.exp 2 * c) ≤ (256 * Real.exp 2 + 3) * c :=
    max_le (by nlinarith only [hc, he2]) (by nlinarith only [hc0])
  exact ⟨by exact_mod_cast h3R, h4c, h256, by linarith only [hup0, hmax, hc]⟩

/-- Orthogonality to `conductorSubspace 1 N` annihilates `poleFunctional` on `[1, N]`. -/
theorem poleFunctional_eq_zero_of_mem_conductorSubspace_one_orthogonal {N : ℕ} (hN : 2 ≤ N)
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ (conductorSubspace 1 N)ᗮ) :
    ArithmeticLorentzianGeometry.poleFunctional N (primeHorizonExtension z) = 0 := by
  have hv : normalizedRamanujanHorizonVector 1 N ∈ conductorSubspace 1 N :=
    mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  have horth : ⟪z, normalizedRamanujanHorizonVector 1 N⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hv hz
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpack : normalizedRamanujanHorizonVector 1 N =
      (Real.sqrt (Real.log N))⁻¹ • horizonProfileVector (fun n => 1 / Real.sqrt n) N := by
    have hp := normalizedRamanujanPacketVector_eq_smul_profile (Icc 1 1) (fun _ => (1 : ℝ)) N
    simp only [normalizedRamanujanPacketVector, Icc_self, sum_singleton, one_smul] at hp
    rw [hp]
    congr 1
    ext n
    simp only [horizonProfileVector, ramanujanPacketProfile, sum_singleton, one_mul,
      ramanujanPoleProfile, normalizedRamanujanMode_one]
  rw [← horizonProfileVector_extension z, hpack, real_inner_smul_right] at horth
  have dinner : ⟪horizonProfileVector (primeHorizonExtension z) N,
      horizonProfileVector (fun n => 1 / Real.sqrt n) N⟫ =
        ArithmeticLorentzianGeometry.poleFunctional N (primeHorizonExtension z) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ n : PrimeHorizonIndex N, (1 / Real.sqrt n.1) * primeHorizonExtension z n.1) = _
    rw [sum_coe_sort (Icc 1 N) (fun n => (1 / Real.sqrt n) * primeHorizonExtension z n)]
    unfold ArithmeticLorentzianGeometry.poleFunctional
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    exact sum_congr rfl fun n _ => by ring
  rw [dinner] at horth
  exact (mul_eq_zero.mp horth).resolve_left (inv_ne_zero (Real.sqrt_pos.mpr hLN).ne')

private theorem Ioc_eq_Icc_sdiff_Icc (M N : ℕ) :
    (Ioc M N : Finset ℕ) = Icc 1 N \ Icc 1 M := by
  ext n
  rw [mem_Ioc, Finset.mem_sdiff, mem_Icc, mem_Icc]
  omega

private theorem sum_atomicTailCoefficients_sq_eq_Ioc {M N : ℕ} (hMN : M ≤ N) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, atomicTailCoefficients M x n ^ 2) = ∑ n ∈ Ioc M N, x n ^ 2 := by
  have h1 := sum_sq_prefix_add_tail hMN x
  have h2 : (∑ n ∈ Icc 1 M, x n ^ 2) + (∑ n ∈ Ioc M N, x n ^ 2) = ∑ n ∈ Icc 1 N, x n ^ 2 := by
    rw [Ioc_eq_Icc_sdiff_Icc M N, add_comm]
    exact sum_sdiff (Icc_subset_Icc le_rfl hMN)
  linarith only [h1, h2]

/-! ## Section 2: Split-Source Logarithmic Tail Localization -/

private theorem logarithmicTailMass_le_split_defect_increment {L N : ℕ}
    (hL1 : 1 ≤ L) (hLN : L ≤ N) (x : ℕ → ℝ) {u : ℝ} (hu : 0 < u) :
    logarithmicTailMass (N / L) N x ≤
      (1 + 1 / u) * (poleDefect N x - poleDefect (N / L) x) +
        (1 + u) * cutoffPrimeCost (N / L) N * (∑ n ∈ Icc 1 (N / L), x n ^ 2) +
        (Real.log 4 + 4) * (L : ℝ) *
          (∑ n ∈ Icc 1 N, atomicTailCoefficients (N / L) x n ^ 2) := by
  let M := N / L
  have hM : 1 ≤ M := Nat.div_pos hLN hL1
  have hMN : M ≤ N := Nat.div_le_self N L
  let x₀ : ℕ → ℝ := fun n => if n ≤ M then x n else 0
  have hsplit_edge : logarithmicTailMass M N x =
      (∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
        if m ≤ M ∧ M < m * t then Λ t * x (m * t) ^ 2 else 0) +
      (∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
        if M < m ∧ M < m * t then Λ t * x (m * t) ^ 2 else 0) := by
    rw [logarithmicTailMass_eq_edges, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    by_cases hmM : m ≤ M
    · have hnot : ¬ M < m := not_lt.mpr hmM
      by_cases hmt : M < m * t <;> simp [hmM, hnot, hmt]
    · have hgt : M < m := lt_of_not_ge hmM
      by_cases hmt : M < m * t <;> simp [hmM, hgt, hmt]
  -- Cross-cutoff edges (`m ≤ M`, `m * t > M`) spend defect increment plus prefix mass only.
  have hcross_pt : ∀ m ∈ Icc 1 N, ∀ t ∈ Icc 1 (N / m),
      (if m ≤ M ∧ M < m * t then Λ t * x (m * t) ^ 2 else 0) ≤
        (1 + 1 / u) * (if M < m * t then Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 else 0) +
        (1 + u) * (if M < m * t then Λ t * (x₀ m / Real.sqrt t) ^ 2 else 0) := by
    intro m _ t _
    by_cases h : m ≤ M ∧ M < m * t
    · rw [if_pos h, if_pos h.2, if_pos h.2]
      have hx₀ : x₀ m = x m := if_pos h.1
      rw [hx₀]
      have hy : x (m * t) ^ 2 ≤
          (1 + 1 / u) * (x (m * t) - x m / Real.sqrt t) ^ 2 +
            (1 + u) * (x m / Real.sqrt t) ^ 2 := by
        calc
          _ ≤ x (m * t) ^ 2 +
              ((x (m * t) - x m / Real.sqrt t) - u * (x m / Real.sqrt t)) ^ 2 / u :=
            le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hu.le)
          _ = _ := by field_simp [hu.ne']; ring
      exact (mul_le_mul_of_nonneg_left hy (vonMangoldt_nonneg (n := t))).trans_eq (by ring)
    · rw [if_neg h]
      refine add_nonneg (mul_nonneg (by positivity) ?_) (mul_nonneg (by positivity) ?_) <;>
        (split_ifs <;> [exact mul_nonneg vonMangoldt_nonneg (sq_nonneg _); exact le_rfl])
  have hcross_sum := sum_le_sum fun m hm => sum_le_sum fun t ht => hcross_pt m hm t ht
  simp only [sum_add_distrib, ← mul_sum] at hcross_sum
  have hedge_def : (∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
      if M < m * t then Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 else 0) =
        poleDefect N x - poleDefect M x := by
    linarith only [poleDefect_eq_cutoff_add_tail hMN x]
  have hx₀_mass : (∑ m ∈ Icc 1 N, x₀ m ^ 2) = ∑ n ∈ Icc 1 M, x n ^ 2 := by
    have hfilt : (Icc 1 N).filter (fun n => n ≤ M) = Icc 1 M := by
      ext n; simp only [mem_filter, mem_Icc]; omega
    calc
      (∑ m ∈ Icc 1 N, x₀ m ^ 2) = ∑ m ∈ Icc 1 N, if m ≤ M then x m ^ 2 else 0 := by
        refine sum_congr rfl fun m _ => ?_
        dsimp only [x₀]
        split_ifs <;> simp
      _ = ∑ n ∈ Icc 1 M, x n ^ 2 := by rw [← sum_filter, hfilt]
  have hout := mul_le_mul_of_nonneg_left (outgoing_cutoff_edges_le hM hMN x₀)
    (show 0 ≤ 1 + u by positivity)
  rw [hx₀_mass] at hout
  rw [hedge_def] at hcross_sum
  -- Purely terminal edges (`m > M`, `m * t ≤ N`) have `t < L` and cost at most `O(L) * S`.
  have hNML : N < (M + 1) * L := by
    simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < L by omega)
  have htail_div : (∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
      if M < m ∧ M < m * t then Λ t * x (m * t) ^ 2 else 0) =
      ∑ n ∈ Icc 1 N, ∑ t ∈ n.divisors,
        if M < n / t ∧ M < n then Λ t * x n ^ 2 else 0 := by
    calc
      _ = ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
          if M < m * t / t ∧ M < m * t then Λ t * x (m * t) ^ 2 else 0 := by
        refine sum_congr rfl fun m _ => sum_congr rfl fun t ht => ?_
        rw [Nat.mul_div_cancel m (mem_Icc.mp ht).1]
      _ = _ := sum_edges_eq_sum_divisors N
          (fun n t => if M < n / t ∧ M < n then Λ t * x n ^ 2 else 0)
  have htail_pt : ∀ n ∈ Icc 1 N,
      (∑ t ∈ n.divisors, if M < n / t ∧ M < n then Λ t * x n ^ 2 else 0) ≤
        ((Real.log 4 + 4) * (L : ℝ)) * atomicTailCoefficients M x n ^ 2 := by
    intro n hn
    rw [atomicTailCoefficients_sq]
    by_cases hnM : M < n
    · rw [if_pos hnM]
      have hrew : (∑ t ∈ n.divisors, if M < n / t ∧ M < n then Λ t * x n ^ 2 else 0) =
          (∑ t ∈ n.divisors.filter (fun t => M < n / t), Λ t) * x n ^ 2 := by
        rw [sum_filter, sum_mul]
        refine sum_congr rfl fun t _ => ?_
        by_cases htM : M < n / t <;> simp [htM, hnM]
      rw [hrew]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hsub : n.divisors.filter (fun t => M < n / t) ⊆ Icc 1 L := by
        intro t ht
        obtain ⟨htd, htM⟩ := mem_filter.mp ht
        have ht1 : 1 ≤ t := Nat.pos_of_mem_divisors htd
        have hdvd : (n / t) * t = n := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors htd)
        have hltL : t < L := by
          have h1 : (M + 1) * t ≤ n := by
            calc
              (M + 1) * t ≤ (n / t) * t := Nat.mul_le_mul_right t htM
              _ = n := hdvd
          have h2 : (M + 1) * t < (M + 1) * L :=
            lt_of_le_of_lt (h1.trans (mem_Icc.mp hn).2) hNML
          exact lt_of_mul_lt_mul_left h2 (Nat.zero_le _)
        exact mem_Icc.mpr ⟨ht1, hltL.le⟩
      exact (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => vonMangoldt_nonneg).trans
        (SpacingScaleHarmonicAnalysis.sum_vonMangoldt_Icc_le L)
    · simp [hnM]
  have htail_sum := sum_le_sum htail_pt
  rw [← mul_sum] at htail_sum
  rw [htail_div] at hsplit_edge
  linarith only [hsplit_edge, hcross_sum, hout, htail_sum]

/-- Split-source tail logarithmic localization: the `(1 + u)` Mertens factor multiplies only the
prefix mass `P`, while the terminal mass `S` pays only `O(L)` without defect loss. -/
theorem log_mul_tail_mass_le_split_defect_increment {L N : ℕ}
    (hL1 : 1 ≤ L) (hLN : L ≤ N) (x : ℕ → ℝ) {u : ℝ} (hu : 0 < u) :
    Real.log N * (∑ n ∈ Icc 1 N, atomicTailCoefficients (N / L) x n ^ 2) ≤
      (1 + 1 / u) * (poleDefect N x - poleDefect (N / L) x) +
        (1 + u) * cutoffPrimeCost (N / L) N * (∑ n ∈ Icc 1 (N / L), x n ^ 2) +
        (Real.log (2 * (L : ℝ)) + (Real.log 4 + 4) * (L : ℝ)) *
          (∑ n ∈ Icc 1 N, atomicTailCoefficients (N / L) x n ^ 2) := by
  let M := N / L
  have hM : 1 ≤ M := Nat.div_pos hLN hL1
  have hMN : M ≤ N := Nat.div_le_self N L
  have hNR : (0 : ℝ) < N := by exact_mod_cast hL1.trans hLN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNML : (N : ℝ) < (M + 1) * L := by
    have ht : N < (M + 1) * L := by
      simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < L by omega)
    exact_mod_cast ht
  have hratio : Real.log N - Real.log M ≤ Real.log (2 * (L : ℝ)) := by
    rw [← Real.log_div hNR.ne' hMR.ne']
    apply Real.log_le_log (div_pos hNR hMR)
    apply (div_le_iff₀ hMR).mpr
    nlinarith only [hNML, mul_nonneg (sub_nonneg.mpr hM1R) hLR.le]
  have hpoint : ∀ n ∈ Icc 1 N,
      Real.log N * atomicTailCoefficients M x n ^ 2 ≤
        (if M < n then Real.log n * x n ^ 2 else 0) +
          (Real.log N - Real.log M) * atomicTailCoefficients M x n ^ 2 := by
    intro n _
    rw [atomicTailCoefficients_sq]
    by_cases hn : M < n
    · simp only [if_pos hn]
      have hl : Real.log M ≤ Real.log n :=
        Real.log_le_log hMR (by exact_mod_cast hn.le)
      nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg (x n))]
    · simp [hn]
  have hsum := sum_le_sum hpoint
  simp only [sum_add_distrib, ← mul_sum] at hsum
  change Real.log N * _ ≤ logarithmicTailMass M N x + _ at hsum
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, atomicTailCoefficients M x n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hratS := mul_le_mul_of_nonneg_right hratio hS0
  have htail := logarithmicTailMass_le_split_defect_increment hL1 hLN x hu
  dsimp only [M] at hsum hratS hS0
  nlinarith only [hsum, hratS, htail]

/-! ## Section 3: Split-Row Bound on `nonRatioForm` -/

private theorem exp_sub_one_le_mul_exp_one {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Real.exp w - 1 ≤ w * Real.exp 1 := by
  have h1 := Real.add_one_le_exp (-w)
  have hprod : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
  have hsub : Real.exp w - 1 ≤ w * Real.exp w := by
    nlinarith only [h1, hprod, Real.exp_pos w]
  exact hsub.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hw0)

private theorem directed_young_pair (x y : ℝ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    2 * (|x| * |y|) ≤ x ^ 2 * (a / t) + y ^ 2 * (t / a) := by
  have hsq := sq_nonneg (|x| * a - t * |y|)
  have hmul : 2 * (|x| * |y|) * (a * t) ≤
      (x ^ 2 * (a / t) + y ^ 2 * (t / a)) * (a * t) := by
    field_simp [ha.ne', ht.ne']
    nlinarith only [hsq, sq_abs x, sq_abs y]
  exact le_of_mul_le_mul_right hmul (mul_pos ha ht)

private theorem directed_row_bounds_unit {w c : ℝ} {N m : ℕ}
    (hN : 1 ≤ N) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hwc : w = c / N) (hc0 : 0 ≤ c)
    (hm : 1 ≤ m) (hmN : m ≤ N) :
    2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N ≤
        nonRatioUpConstant * c ∧
      2 * Real.exp (w / 2) * m * (Real.exp w - 1) * (Real.log m + w) ≤
        nonRatioDownConstant * c * (Real.log N + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hew : Real.exp w - 1 ≤ (c / N) * Real.exp 1 := by
    rw [← hwc]
    exact exp_sub_one_le_mul_exp_one hw0 hw1
  have hup : (Real.exp w - 1) * N ≤ c * Real.exp 1 := by
    calc
      _ ≤ ((c / N) * Real.exp 1) * N := mul_le_mul_of_nonneg_right hew hN0.le
      _ = _ := by field_simp [hN0.ne']
  have e1 : Real.exp (3 * w / 2) * Real.exp 1 ≤ Real.exp (5 / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hw1])
  have e2 : Real.exp (w / 2) * Real.exp 1 ≤ Real.exp (3 / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hw1])
  have hlog4 : 0 ≤ Real.log 4 + 4 := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith only [hlog]
  constructor
  · calc
      _ = 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * ((Real.exp w - 1) * N) := by ring
      _ ≤ 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (c * Real.exp 1) :=
        mul_le_mul_of_nonneg_left hup (by positivity)
      _ = 2 * (Real.log 4 + 4) * c * (Real.exp (3 * w / 2) * Real.exp 1) := by ring
      _ ≤ 2 * (Real.log 4 + 4) * c * Real.exp (5 / 2) :=
        mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = _ := by unfold nonRatioUpConstant; ring
  · have hmNR : (m : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast hmN)
    have hlogmN : Real.log m ≤ Real.log N := Real.log_le_log hm0 (by exact_mod_cast hmN)
    have hdown' : (Real.exp w - 1) * m ≤ c * Real.exp 1 := by
      have hdown : (Real.exp w - 1) * m ≤ c * Real.exp 1 * ((m : ℝ) / N) := by
        calc
          _ ≤ ((c / N) * Real.exp 1) * m := mul_le_mul_of_nonneg_right hew hm0.le
          _ = _ := by ring
      have h1 := mul_le_mul_of_nonneg_left hmNR (mul_nonneg hc0 (Real.exp_pos 1).le)
      linarith only [hdown, h1]
    have hlm : 0 ≤ Real.log m + w := add_nonneg (Real.log_natCast_nonneg m) hw0
    calc
      _ = 2 * Real.exp (w / 2) * ((Real.exp w - 1) * m) * (Real.log m + w) := by ring
      _ ≤ 2 * Real.exp (w / 2) * (c * Real.exp 1) * (Real.log N + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdown' (by positivity))
          (by linarith only [hlogmN, hw1]) hlm (by positivity)
      _ = 2 * c * (Real.log N + 1) * (Real.exp (w / 2) * Real.exp 1) := by ring
      _ ≤ 2 * c * (Real.log N + 1) * Real.exp (3 / 2) :=
        mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by unfold nonRatioDownConstant; ring

private theorem upInd_eq_zero_of_le_linearPrefix {c : ℝ} (hc : 1 ≤ c) {N k m n : ℕ}
    (hLN : linearDefectCutoff c ≤ N) (hk : 1 ≤ k) (hm : m ∈ Icc 1 N)
    (hn : n ∈ Icc 1 (N / linearDefectCutoff c)) :
    upInd (c / N) k m n = 0 := by
  unfold upInd upWin
  split_ifs with h
  · exfalso
    let L := linearDefectCutoff c
    let M := N / L
    let w := c / (N : ℝ)
    obtain ⟨hL3, h4c, h256, -⟩ := linearDefectCutoff_bounds hc
    have hc0 : 0 < c := zero_lt_one.trans_le hc
    have hN1 : 1 ≤ N := by omega
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
    have hLR : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have hcN : c ≤ (N : ℝ) := by
      have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
      linarith only [h4c, hLNR, hc0]
    have hw0 : 0 ≤ w := div_nonneg hc0.le hNR.le
    have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast (mem_Icc.mp hn).2
    have hkm_log : Real.log ((k * m : ℕ) : ℝ) = Real.log k + Real.log m := by
      push_cast; exact Real.log_mul hk0.ne' hm0.ne'
    have hlog : |Real.log ((k * m : ℕ) : ℝ) - Real.log n| ≤ w := by
      rw [hkm_log]
      convert h.2 using 2
      ring
    have habs_le : |((k * m : ℕ) : ℝ) - n| ≤ (n : ℝ) * (Real.exp w - 1) :=
      abs_sub_le_of_abs_log_le (by exact_mod_cast Nat.mul_pos hk (mem_Icc.mp hm).1) hn0 hlog
    have habs_ge : (1 : ℝ) ≤ |((k * m : ℕ) : ℝ) - n| := by
      rcases lt_or_gt_of_ne h.1 with hlt | hgt
      · have h1 : (n : ℝ) + 1 ≤ (k * m : ℕ) := by exact_mod_cast hlt
        exact (by linarith only [h1] : (1 : ℝ) ≤ (k * m : ℕ) - n).trans (le_abs_self _)
      · have h1 : ((k * m : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hgt
        exact (by linarith only [h1] : (1 : ℝ) ≤ -(((k * m : ℕ) : ℝ) - n)).trans (neg_le_abs _)
    have hew : Real.exp w - 1 ≤ w * Real.exp 1 := exp_sub_one_le_mul_exp_one hw0 hw1
    have hew0 : 0 ≤ Real.exp w - 1 := sub_nonneg.mpr (Real.one_le_exp hw0)
    have hstep1 : (1 : ℝ) ≤ (M : ℝ) * (w * Real.exp 1) := by
      calc
        (1 : ℝ) ≤ (n : ℝ) * (Real.exp w - 1) := habs_ge.trans habs_le
        _ ≤ (M : ℝ) * (w * Real.exp 1) :=
          mul_le_mul hnM hew hew0 (Nat.cast_nonneg M)
    have hNM : (N : ℝ) ≤ (M : ℝ) * c * Real.exp 1 := by
      have hm1 := mul_le_mul_of_nonneg_left hstep1 hNR.le
      dsimp only [w] at hm1
      have heq : (N : ℝ) * ((M : ℝ) * (c / (N : ℝ) * Real.exp 1)) =
          (M : ℝ) * c * Real.exp 1 := by field_simp [hNR.ne']
      linarith only [hm1, heq]
    have hML : (M : ℝ) * L ≤ N := by exact_mod_cast Nat.div_mul_le_self N L
    have hNL : (N : ℝ) * L ≤ (N : ℝ) * (c * Real.exp 1) := by
      calc
        (N : ℝ) * L ≤ ((M : ℝ) * c * Real.exp 1) * L :=
          mul_le_mul_of_nonneg_right hNM hLR.le
        _ = ((M : ℝ) * L) * (c * Real.exp 1) := by ring
        _ ≤ (N : ℝ) * (c * Real.exp 1) :=
          mul_le_mul_of_nonneg_right hML (by positivity)
    have hL_le : (L : ℝ) ≤ c * Real.exp 1 := le_of_mul_le_mul_left hNL hNR
    have he12 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    nlinarith only [hL_le, h256, he12, Real.exp_pos 2, hc0]
  · rfl

private def tailNonRatioConstant : ℝ :=
  nonRatioUpConstant + 2 * (Real.log 4 + 4) * (256 * Real.exp 2 + 4) * Real.exp (5 / 2)

private theorem tailNonRatioConstant_pos : 0 < tailNonRatioConstant := by
  have h1 := nonRatioUpConstant_pos
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  unfold tailNonRatioConstant
  positivity

private theorem tail_incoming_nonRatio_row_le {c : ℝ} (hc : 1 ≤ c) {N : ℕ}
    (hLN : linearDefectCutoff c ≤ N) (K_up : ℕ) {n : ℕ}
    (hn : n ∈ Ioc (N / linearDefectCutoff c) N) :
    (∑ k ∈ range K_up, vonMangoldtAtom k *
      ∑ m ∈ Ioc (N / linearDefectCutoff c) N, Real.sqrt ((n : ℝ) / m) * upInd (c / N) k m n) ≤
        2 * (Real.log 4 + 4) * (256 * Real.exp 2 + 4) * Real.exp (5 / 2) * c ^ 2 := by
  let L := linearDefectCutoff c
  let M := N / L
  let w := c / (N : ℝ)
  let K₁ := ⌊(L : ℝ) * Real.exp 1⌋₊
  obtain ⟨hL3, h4c, -, hLup⟩ := linearDefectCutoff_bounds hc
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  have hw0 : 0 ≤ w := div_nonneg hc0.le hNR.le
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  have hew0 : 0 ≤ Real.exp w - 1 := sub_nonneg.mpr (Real.one_le_exp hw0)
  have hn1 : 1 ≤ n := Nat.zero_lt_of_lt (mem_Ioc.mp hn).1
  have hnN : n ≤ N := (mem_Ioc.mp hn).2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hNML : (N : ℝ) < (M + 1) * L := by
    have ht : N < (M + 1) * L := by
      simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < L by omega)
    exact_mod_cast ht
  have hk_bound : ∀ k ∈ range K_up,
      vonMangoldtAtom k *
        (∑ m ∈ Ioc M N, Real.sqrt ((n : ℝ) / m) * upInd w k m n) ≤
          (if k ∈ Icc 1 K₁ then Λ k else 0) * (2 * Real.exp (3 / 2) * c) := by
    intro k _
    rcases lt_or_ge k 2 with hk2 | hk2
    · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
      split_ifs <;> [exact mul_nonneg vonMangoldt_nonneg (by positivity); simp]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    by_cases hkK : k ∈ Icc 1 K₁
    · rw [if_pos hkK, vonMangoldtAtom_eq hk2]
      let S_m := (Ioc M N).filter (fun m => upWin w k m n)
      have hinner : (∑ m ∈ Ioc M N, Real.sqrt ((n : ℝ) / m) * upInd w k m n) ≤
          (S_m.card : ℝ) * (Real.sqrt k * Real.exp (1 / 2)) := by
        calc
          _ = ∑ m ∈ S_m, Real.sqrt ((n : ℝ) / m) * upInd w k m n := by
            rw [sum_filter]
            refine sum_congr rfl fun m _ => ?_
            unfold upInd
            split_ifs <;> simp
          _ ≤ ∑ _m ∈ S_m, Real.sqrt k * Real.exp (1 / 2) := by
            refine sum_le_sum fun m hm => ?_
            obtain ⟨hmI, hwin⟩ := mem_filter.mp hm
            have hm1 : 1 ≤ m := Nat.zero_lt_of_lt (mem_Ioc.mp hmI).1
            have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
            have h1 : upInd w k m n = 1 := if_pos hwin
            rw [h1, mul_one]
            have hlog_le : Real.log ((n : ℝ) / m) ≤ Real.log ((k : ℝ) * Real.exp 1) := by
              rw [Real.log_div hn0.ne' hm0.ne', Real.log_mul hk0.ne' (Real.exp_ne_zero 1),
                Real.log_exp]
              have hab := (abs_le.mp hwin.2).1
              linarith only [hab, hw1]
            have hdiv_le : (n : ℝ) / m ≤ k * Real.exp 1 := by
              have hex := Real.exp_le_exp.mpr hlog_le
              rwa [Real.exp_log (div_pos hn0 hm0), Real.exp_log (by positivity)] at hex
            calc
              Real.sqrt ((n : ℝ) / m) ≤ Real.sqrt ((k : ℝ) * Real.exp 1) :=
                Real.sqrt_le_sqrt hdiv_le
              _ = Real.sqrt k * Real.exp (1 / 2) := by
                rw [Real.sqrt_mul hk0.le, ← Real.exp_half]
          _ = _ := by rw [sum_const, nsmul_eq_mul]
      let Img := S_m.image (fun m => k * m)
      have hcard_eq : S_m.card = Img.card :=
        (Finset.card_image_of_injective S_m (mul_right_injective₀ (by omega : k ≠ 0))).symm
      have hImg_sub : Img = Img.filter (fun y => y ≠ n ∧ |(y : ℝ) - n| ≤ c * Real.exp 1) := by
        symm
        apply filter_true_of_mem
        intro y hy
        obtain ⟨m, hmS, rfl⟩ := mem_image.mp hy
        obtain ⟨hmI, hwin⟩ := mem_filter.mp hmS
        have hm1 : 1 ≤ m := Nat.zero_lt_of_lt (mem_Ioc.mp hmI).1
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
        refine ⟨Ne.symm hwin.1, ?_⟩
        have hkm_log : Real.log ((k * m : ℕ) : ℝ) = Real.log k + Real.log m := by
          push_cast; exact Real.log_mul hk0.ne' hm0.ne'
        have hlog : |Real.log ((k * m : ℕ) : ℝ) - Real.log n| ≤ w := by
          rw [hkm_log]; convert hwin.2 using 2; ring
        have habs := abs_sub_le_of_abs_log_le
          (by exact_mod_cast Nat.mul_pos (show 0 < k by omega) hm1) hn0 hlog
        have hew := exp_sub_one_le_mul_exp_one hw0 hw1
        calc
          |((k * m : ℕ) : ℝ) - n| ≤ (n : ℝ) * (Real.exp w - 1) := habs
          _ ≤ (N : ℝ) * (w * Real.exp 1) :=
            mul_le_mul hnNR hew hew0 hNR.le
          _ = c * Real.exp 1 := by dsimp only [w]; field_simp [hNR.ne']
      have hcard_le : (S_m.card : ℝ) ≤ 2 * (c * Real.exp 1) := by
        rw [hcard_eq, hImg_sub]
        exact card_near_le Img n (by positivity)
      have hprod := mul_le_mul_of_nonneg_left
        (hinner.trans (mul_le_mul_of_nonneg_right hcard_le (by positivity)))
        (div_nonneg (vonMangoldt_nonneg (n := k)) hsk.le)
      refine hprod.trans_eq ?_
      have he32 : Real.exp 1 * Real.exp (1 / 2) = Real.exp (3 / 2) := by
        rw [← Real.exp_add]; norm_num
      calc
        Λ k / Real.sqrt k * (2 * (c * Real.exp 1) * (Real.sqrt k * Real.exp (1 / 2))) =
            Λ k * (2 * (Real.exp 1 * Real.exp (1 / 2)) * c) * (Real.sqrt k / Real.sqrt k) := by
          ring
        _ = Λ k * (2 * Real.exp (3 / 2) * c) := by rw [div_self hsk.ne', mul_one, he32]
    · rw [if_neg hkK, zero_mul]
      have hk_gt : (L : ℝ) * Real.exp 1 < k := by
        have hlt : K₁ < k := by
          by_contra hle
          exact hkK (mem_Icc.mpr ⟨by omega, not_lt.mp hle⟩)
        exact Nat.lt_of_floor_lt hlt
      have hzero : (∑ m ∈ Ioc M N, Real.sqrt ((n : ℝ) / m) * upInd w k m n) = 0 := by
        refine sum_eq_zero fun m hm => ?_
        have hmM : M + 1 ≤ m := (mem_Ioc.mp hm).1
        have hm1 : 1 ≤ m := Nat.zero_lt_of_lt (mem_Ioc.mp hm).1
        unfold upInd
        split_ifs with hwin
        · exfalso
          have hlow := (upWin_bounds (by omega) hm1 hn1 hwin.2).2.2
          have hprod_exp : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
          have hkm_le : (k : ℝ) * m ≤ (n : ℝ) * Real.exp w := by
            have h := mul_le_mul_of_nonneg_right hlow (Real.exp_pos w).le
            rwa [mul_assoc, hprod_exp, mul_one] at h
          have hnw_le : (n : ℝ) * Real.exp w ≤ (N : ℝ) * Real.exp 1 :=
            mul_le_mul hnNR (Real.exp_le_exp.mpr hw1) (Real.exp_pos w).le hNR.le
          have hmR : ((M : ℝ) + 1) ≤ m := by exact_mod_cast hmM
          have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
          have h1 : ((M : ℝ) + 1) * ((L : ℝ) * Real.exp 1) < ((M : ℝ) + 1) * k :=
            mul_lt_mul_of_pos_left hk_gt hMpos
          have h2 : ((M : ℝ) + 1) * k ≤ (k : ℝ) * m := by nlinarith only [hmR, hk0]
          have h3 : (N : ℝ) * Real.exp 1 < (((M : ℝ) + 1) * L) * Real.exp 1 :=
            mul_lt_mul_of_pos_right hNML (Real.exp_pos 1)
          linarith only [h1, h2, hkm_le, hnw_le, h3]
        · simp
      rw [hzero, mul_zero]
  have hsum_k := sum_le_sum hk_bound
  rw [← sum_mul] at hsum_k
  have hsub_sum : (∑ k ∈ range K_up, if k ∈ Icc 1 K₁ then Λ k else 0) ≤
      ∑ k ∈ Icc 1 K₁, Λ k := by
    rw [← sum_filter]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldt_nonneg
    intro k hk
    exact (mem_filter.mp hk).2
  have hcheb := hsub_sum.trans (SpacingScaleHarmonicAnalysis.sum_vonMangoldt_Icc_le K₁)
  have hK₁_le : (K₁ : ℝ) ≤ (256 * Real.exp 2 + 4) * c * Real.exp 1 := by
    exact (Nat.floor_le (by positivity)).trans
      (mul_le_mul_of_nonneg_right hLup (Real.exp_pos 1).le)
  have hlog4 : 0 ≤ Real.log 4 + 4 := by
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith only [hl]
  have he52 : Real.exp 1 * Real.exp (3 / 2) = Real.exp (5 / 2) := by
    rw [← Real.exp_add]; norm_num
  calc
    _ ≤ ((Real.log 4 + 4) * (K₁ : ℝ)) * (2 * Real.exp (3 / 2) * c) :=
      hsum_k.trans (mul_le_mul_of_nonneg_right hcheb (by positivity))
    _ ≤ ((Real.log 4 + 4) * ((256 * Real.exp 2 + 4) * c * Real.exp 1)) *
          (2 * Real.exp (3 / 2) * c) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK₁_le hlog4) (by positivity)
    _ = 2 * (Real.log 4 + 4) * (256 * Real.exp 2 + 4) *
          (Real.exp 1 * Real.exp (3 / 2)) * c ^ 2 := by ring
    _ = 2 * (Real.log 4 + 4) * (256 * Real.exp 2 + 4) * Real.exp (5 / 2) * c ^ 2 := by
      rw [he52]

private theorem abs_nonRatioForm_le_asymmetric_split {g : ℝ → ℝ} {c t₀ : ℝ} {N : ℕ}
    (hc : 1 ≤ c) (hLN : linearDefectCutoff c ≤ N) (ht₀ : 0 < t₀)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0) (x : ℕ → ℝ) :
    |nonRatioForm g N x| ≤ (∫ u, g u ^ 2) *
      ((nonRatioUpConstant * c / t₀) * (∑ m ∈ Icc 1 (N / linearDefectCutoff c), x m ^ 2) +
        t₀ * nonRatioDownConstant * c * (Real.log N + 1) *
          (∑ n ∈ Ioc (N / linearDefectCutoff c) N, x n ^ 2) +
        tailNonRatioConstant * c ^ 2 *
          (∑ n ∈ Ioc (N / linearDefectCutoff c) N, x n ^ 2)) := by
  let L := linearDefectCutoff c
  let M := N / L
  let w := c / (N : ℝ)
  let K_up := ⌈(N : ℝ) * Real.exp w⌉₊ + 1
  let G := ∫ u, g u ^ 2
  obtain ⟨hL3, h4c, -, -⟩ := linearDefectCutoff_bounds hc
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hMN : M ≤ N := Nat.div_le_self N L
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  have hw0 : 0 ≤ w := div_nonneg hc0.le hNR.le
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hfin : nonRatioForm g N x =
      ∑ k ∈ range K_up, vonMangoldtAtom k * nonRatioLag g N k x := by
    unfold nonRatioForm
    refine tsum_eq_sum fun k hk => ?_
    have hkL : K_up ≤ k := by simpa only [mem_range, not_lt] using hk
    have hbig : (N : ℝ) * Real.exp w < k := by
      have hceil := Nat.le_ceil ((N : ℝ) * Real.exp w)
      have hkR : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hkL
      push_cast at hkR
      linarith only [hceil, hkR]
    have hlog : Real.log N + w < Real.log k := by
      rw [← Real.log_exp w, ← Real.log_mul hNR.ne' (Real.exp_pos w).ne']
      exact Real.log_lt_log (by positivity) hbig
    rw [nonRatioLag_eq_zero_of_log_lt hsupp hw0 hlog, mul_zero]
  let V : ℕ → ℕ → ℝ := fun m n =>
    ∑ k ∈ range K_up, vonMangoldtAtom k * upInd w k m n
  have hV : ∀ m n, 0 ≤ V m n := fun m n =>
    sum_nonneg fun k _ => mul_nonneg (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
      (upInd_nonneg _ _ _ _)
  have hV_zero_prefix : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 M, V m n = 0 := by
    intro m hm n hn
    refine sum_eq_zero fun k _ => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [vonMangoldtAtom_eq_zero_of_lt_two (by norm_num), zero_mul]
    · rw [upInd_eq_zero_of_le_linearPrefix hc hLN hk1 hm hn, mul_zero]
  have hsource : |nonRatioForm g N x| ≤
      G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, 2 * (|x m| * |x n|) * V m n := by
    rw [hfin]
    have h1 : |∑ k ∈ range K_up, vonMangoldtAtom k * nonRatioLag g N k x| ≤
        G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * (V m n + V n m) := by
      calc
        _ ≤ ∑ k ∈ range K_up, vonMangoldtAtom k *
            (G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
              |x m| * |x n| * (upInd w k m n + upInd w k n m)) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
          rw [abs_mul, abs_of_nonneg (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)]
          exact mul_le_mul_of_nonneg_left (abs_nonRatioLag_le hg hgc hsupp N k x)
            (SpacingScaleHarmonicAnalysis.vonMangoldtAtom_nonneg' k)
        _ = _ := by
          simp only [V, ← sum_add_distrib, mul_sum, ← mul_add]
          rw [sum_comm]
          exact sum_congr rfl fun m _ => by
            rw [sum_comm]
            exact sum_congr rfl fun n _ => sum_congr rfl fun k _ => by ring
    have hswap : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * V n m) =
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * V m n := by
      rw [sum_comm]
      exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
    have hsym : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * (V m n + V n m)) =
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, 2 * (|x m| * |x n|) * V m n := by
      simp only [mul_add, sum_add_distrib]
      rw [hswap, ← two_mul]
      simp only [mul_sum]
      exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
    rw [hsym] at h1
    exact h1
  have hIoc_sub : Ioc M N ⊆ Icc 1 N := fun n hn =>
    mem_Icc.mpr ⟨Nat.zero_lt_of_lt (mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2⟩
  have hpartition : ∀ f : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, f n) = (∑ n ∈ Icc 1 M, f n) + ∑ n ∈ Ioc M N, f n := by
    intro f
    rw [Ioc_eq_Icc_sdiff_Icc M N, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
  have hdrop_n : ∀ m ∈ Icc 1 N,
      (∑ n ∈ Icc 1 N, 2 * (|x m| * |x n|) * V m n) =
        ∑ n ∈ Ioc M N, 2 * (|x m| * |x n|) * V m n := by
    intro m hm
    rw [hpartition]
    have hz : (∑ n ∈ Icc 1 M, 2 * (|x m| * |x n|) * V m n) = 0 :=
      sum_eq_zero fun n hn => by rw [hV_zero_prefix m hm n hn, mul_zero]
    rw [hz, zero_add]
  have hsplit_m : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, 2 * (|x m| * |x n|) * V m n) =
      (∑ m ∈ Icc 1 M, ∑ n ∈ Ioc M N, 2 * (|x m| * |x n|) * V m n) +
      (∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, 2 * (|x m| * |x n|) * V m n) := by
    rw [sum_congr rfl hdrop_n, hpartition]
  -- Outgoing row bound valid for every `m ∈ Icc 1 N`.
  have hout_row : ∀ m ∈ Icc 1 N,
      (∑ n ∈ Ioc M N, Real.sqrt ((m : ℝ) / n) * V m n) ≤ nonRatioUpConstant * c := by
    intro m hm
    have hsub := sum_le_sum_of_subset_of_nonneg
      (f := fun n : ℕ => Real.sqrt ((m : ℝ) / (n : ℝ)) * V m n) hIoc_sub fun n _ _ =>
      mul_nonneg (Real.sqrt_nonneg _) (hV m n)
    have hup : (∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n) =
        ∑ k ∈ range K_up, vonMangoldtAtom k *
          ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k m n := by
      simp only [V, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun n _ => by ring
    exact hsub.trans ((hup.trans_le (up_row_le hw0 (mem_Icc.mp hm).1 K_up)).trans
      (directed_row_bounds_unit hN1 hw0 hw1 rfl hc0.le (mem_Icc.mp hm).1 (mem_Icc.mp hm).2).1)
  -- Region A: prefix `m ∈ Icc 1 M` to tail `n ∈ Ioc M N`.
  have hregA : (∑ m ∈ Icc 1 M, ∑ n ∈ Ioc M N, 2 * (|x m| * |x n|) * V m n) ≤
      (nonRatioUpConstant * c / t₀) * (∑ m ∈ Icc 1 M, x m ^ 2) +
        t₀ * nonRatioDownConstant * c * (Real.log N + 1) * (∑ n ∈ Ioc M N, x n ^ 2) := by
    have hpair : ∀ m ∈ Icc 1 M, ∀ n ∈ Ioc M N,
        2 * (|x m| * |x n|) * V m n ≤
          x m ^ 2 * (Real.sqrt ((m : ℝ) / n) * V m n) / t₀ +
            t₀ * (x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V m n)) := by
      intro m hm n hn
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (hIoc_sub hn)).1
      have ha : 0 < Real.sqrt ((m : ℝ) / n) := Real.sqrt_pos.mpr (div_pos hm0 hn0)
      have hinv : Real.sqrt ((n : ℝ) / m) = (Real.sqrt ((m : ℝ) / n))⁻¹ := by
        rw [← Real.sqrt_inv, inv_div]
      have hy := mul_le_mul_of_nonneg_right (directed_young_pair (x m) (x n) ha ht₀) (hV m n)
      rw [hinv]
      exact hy.trans_eq (by ring)
    have hsum := sum_le_sum fun m hm => sum_le_sum fun n hn => hpair m hm n hn
    simp only [sum_add_distrib] at hsum
    rw [sum_comm (s := Icc 1 M) (t := Ioc M N)
      (f := fun m n => t₀ * (x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V m n)))] at hsum
    have hA1 : (∑ m ∈ Icc 1 M, ∑ n ∈ Ioc M N,
        x m ^ 2 * (Real.sqrt ((m : ℝ) / n) * V m n) / t₀) ≤
          (nonRatioUpConstant * c / t₀) * ∑ m ∈ Icc 1 M, x m ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun m hm => ?_
      have hmN : m ∈ Icc 1 N := Icc_subset_Icc le_rfl hMN hm
      calc
        _ = x m ^ 2 * ((∑ n ∈ Ioc M N, Real.sqrt ((m : ℝ) / n) * V m n) / t₀) := by
          simp only [← sum_div, ← mul_sum]; ring
        _ ≤ x m ^ 2 * (nonRatioUpConstant * c / t₀) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (hout_row m hmN) ht₀.le) (sq_nonneg _)
        _ = _ := by ring
    have hA2 : (∑ n ∈ Ioc M N, ∑ m ∈ Icc 1 M,
        t₀ * (x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V m n))) ≤
          t₀ * nonRatioDownConstant * c * (Real.log N + 1) * ∑ n ∈ Ioc M N, x n ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun n hn => ?_
      have hnI := hIoc_sub hn
      have hsubM : (∑ m ∈ Icc 1 M, Real.sqrt ((n : ℝ) / m) * V m n) ≤
          ∑ m ∈ Icc 1 N, Real.sqrt ((n : ℝ) / m) * V m n :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN) fun m _ _ =>
          mul_nonneg (Real.sqrt_nonneg _) (hV m n)
      have hdown : (∑ m ∈ Icc 1 N, Real.sqrt ((n : ℝ) / m) * V m n) =
          ∑ k ∈ range K_up, vonMangoldtAtom k *
            ∑ m ∈ Icc 1 N, Real.sqrt ((n : ℝ) / m) * upInd w k m n := by
        simp only [V, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
      have hin := hsubM.trans ((hdown.trans_le (down_row_le hw0 (mem_Icc.mp hnI).1 K_up)).trans
        (directed_row_bounds_unit hN1 hw0 hw1 rfl hc0.le (mem_Icc.mp hnI).1 (mem_Icc.mp hnI).2).2)
      calc
        _ = t₀ * x n ^ 2 * ∑ m ∈ Icc 1 M, Real.sqrt ((n : ℝ) / m) * V m n := by
          simp only [← mul_sum, mul_assoc]
        _ ≤ t₀ * x n ^ 2 * (nonRatioDownConstant * c * (Real.log N + 1)) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
        _ = _ := by ring
    linarith only [hsum, hA1, hA2]
  -- Region B: tail `m ∈ Ioc M N` to tail `n ∈ Ioc M N`.
  have hregB : (∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, 2 * (|x m| * |x n|) * V m n) ≤
      tailNonRatioConstant * c ^ 2 * ∑ n ∈ Ioc M N, x n ^ 2 := by
    have hpair : ∀ m ∈ Ioc M N, ∀ n ∈ Ioc M N,
        2 * (|x m| * |x n|) * V m n ≤
          x m ^ 2 * (Real.sqrt ((m : ℝ) / n) * V m n) +
            x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V m n) := by
      intro m hm n hn
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp (hIoc_sub hm)).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp (hIoc_sub hn)).1
      have ha : 0 < Real.sqrt ((m : ℝ) / n) := Real.sqrt_pos.mpr (div_pos hm0 hn0)
      have hinv : Real.sqrt ((n : ℝ) / m) = (Real.sqrt ((m : ℝ) / n))⁻¹ := by
        rw [← Real.sqrt_inv, inv_div]
      have hy := mul_le_mul_of_nonneg_right (directed_young_pair (x m) (x n) ha zero_lt_one) (hV m n)
      rw [div_one, one_div, ← hinv] at hy
      exact hy.trans_eq (by ring)
    have hsum := sum_le_sum fun m hm => sum_le_sum fun n hn => hpair m hm n hn
    simp only [sum_add_distrib] at hsum
    rw [sum_comm (s := Ioc M N) (t := Ioc M N)
      (f := fun m n => x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V m n))] at hsum
    have hB1 : (∑ m ∈ Ioc M N, ∑ n ∈ Ioc M N, x m ^ 2 * (Real.sqrt ((m : ℝ) / n) * V m n)) ≤
        nonRatioUpConstant * c ^ 2 * ∑ m ∈ Ioc M N, x m ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun m hm => ?_
      have hc12 : c ≤ c ^ 2 := by nlinarith only [hc]
      have hu := (hout_row m (hIoc_sub hm)).trans
        (mul_le_mul_of_nonneg_left hc12 nonRatioUpConstant_pos.le)
      calc
        _ = x m ^ 2 * ∑ n ∈ Ioc M N, Real.sqrt ((m : ℝ) / n) * V m n := by rw [← mul_sum]
        _ ≤ x m ^ 2 * (nonRatioUpConstant * c ^ 2) :=
          mul_le_mul_of_nonneg_left hu (sq_nonneg _)
        _ = _ := by ring
    have hB2 : (∑ n ∈ Ioc M N, ∑ m ∈ Ioc M N, x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V m n)) ≤
        (2 * (Real.log 4 + 4) * (256 * Real.exp 2 + 4) * Real.exp (5 / 2)) * c ^ 2 *
          ∑ n ∈ Ioc M N, x n ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun n hn => ?_
      have hrew : (∑ m ∈ Ioc M N, Real.sqrt ((n : ℝ) / m) * V m n) =
          ∑ k ∈ range K_up, vonMangoldtAtom k *
            ∑ m ∈ Ioc M N, Real.sqrt ((n : ℝ) / m) * upInd w k m n := by
        simp only [V, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
      have hin := hrew.trans_le (tail_incoming_nonRatio_row_le hc hLN K_up hn)
      calc
        _ = x n ^ 2 * ∑ m ∈ Ioc M N, Real.sqrt ((n : ℝ) / m) * V m n := by rw [← mul_sum]
        _ ≤ x n ^ 2 *
            (2 * (Real.log 4 + 4) * (256 * Real.exp 2 + 4) * Real.exp (5 / 2) * c ^ 2) :=
          mul_le_mul_of_nonneg_left hin (sq_nonneg _)
        _ = _ := by ring
    unfold tailNonRatioConstant
    linarith only [hsum, hB1, hB2]
  refine hsource.trans (mul_le_mul_of_nonneg_left ?_ hG)
  rw [hsplit_m]
  linarith only [hregA, hregB]

/-! ## Section 4: Asymmetric `(conductorSubspace 1 N)ᗮ` Reserve and Two-Region `(V_R)ᗮ` Coercivity -/

/-- **Asymmetric prefix/terminal reserve on `(conductorSubspace 1 N)ᗮ`.**
With `M = N / linearDefectCutoff c`, the `O(c^9)` overlap penalty multiplies strictly the
separated prefix mass `P`, while the terminal mass `S` incurs only `O(c^2)` cost and retains
both `+ (a / c^7) poleDefect N` and `+ (a / c^7) (log N) S`. -/
theorem exists_completeWeilEnergy_asymmetric_prefix_terminal_reserve :
    ∃ a C₀ C₁ : ℝ, 0 < a ∧ a ≤ 1 / 8 ∧ 0 < C₀ ∧ 0 < C₁ ∧
      ∀ {c : ℝ} {N : ℕ}, 1 ≤ c → linearDefectCutoff c ≤ N →
        ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
          (1 / 2 : ℝ) * poleDefect (N / linearDefectCutoff c) (primeHorizonExtension z) +
            (a / c ^ 7) * poleDefect N (primeHorizonExtension z) +
            (a / c ^ 7) * Real.log N *
              (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2) -
            C₀ * c ^ 9 *
              (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) -
            C₁ * c ^ 2 *
              (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2) ≤
            completeWeilEnergy tiltedUnitSpline c N z := by
  let d := min growingMassConstant (1 / 2)
  have hd : 0 < d := lt_min growingMassConstant_pos (by norm_num)
  have hd_le_half : d ≤ 1 / 2 := min_le_right _ _
  let a := d / 8
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha8 : a ≤ 1 / 8 := by dsimp only [a]; linarith only [hd_le_half]
  let J := (Real.log 4 + 4) + (Real.log 8 + 4)
  let L_const := 256 * Real.exp 2 + 4
  let C_arch0 := 1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost +
    2 * Real.pi * (1 + 2 * Real.exp 1) + (Real.log 4 + 4)
  let C_tp := (1 + 4 / d) * (Real.log (2 * L_const) + 1 + J)
  let C_nr0 := 8 * nonRatioUpConstant * nonRatioDownConstant / d
  let C₀ := C_arch0 + C_tp + C_nr0 + 1
  let C_ts := Real.log (2 * L_const) + 1 + (Real.log 4 + 4) * L_const
  let C₁ := growingReserveCost + 2 * Real.pi * (1 + 2 * Real.exp 1) + (Real.log 4 + 4) +
    C_ts + 1 + tailNonRatioConstant + 1
  have hAsep : 0 ≤ separatedCrossMassCost := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    unfold separatedCrossMassCost; positivity
  have hJ : 0 ≤ J := by
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    have h8 := Real.log_nonneg (show (1 : ℝ) ≤ 8 by norm_num)
    dsimp only [J]; linarith only [h4, h8]
  have hL_const1 : 1 ≤ L_const := by
    have he2 := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp only [L_const]; linarith only [he2]
  have hlog2L : 0 ≤ Real.log (2 * L_const) := Real.log_nonneg (by linarith only [hL_const1])
  have hC₀ : 0 < C₀ := by
    have := nonRatioUpConstant_pos
    have := nonRatioDownConstant_pos
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    dsimp only [C₀, C_arch0, C_tp, C_nr0]; positivity
  have hC₁ : 0 < C₁ := by
    have := growingReserveCost_nonneg
    have := tailNonRatioConstant_pos
    have h4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    dsimp only [C₁, C_ts]; positivity
  refine ⟨a, C₀, C₁, ha, ha8, hC₀, hC₁, ?_⟩
  intro c N hc1 hLN z hz
  obtain ⟨hL3, h4c, h256, hLup⟩ := linearDefectCutoff_bounds hc1
  let L := linearDefectCutoff c
  let M := N / L
  let x := primeHorizonExtension z
  let y := atomicTailCoefficients M x
  let P := ∑ n ∈ Icc 1 M, x n ^ 2
  let S := ∑ n ∈ Ioc M N, x n ^ 2
  let δ := d / c ^ 7
  let w := c / (N : ℝ)
  let g := atomDilate tiltedUnitSpline w
  let G := w * ∫ u, tiltedUnitSpline u ^ 2
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL1 : 1 ≤ L := by omega
  have hN3 : 3 ≤ N := hL3.trans hLN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hM : 1 ≤ M := Nat.div_pos hLN hL1
  have hMN : M ≤ N := Nat.div_le_self N L
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hcN : c ≤ (N : ℝ) := by
    have hLNR : (L : ℝ) ≤ N := by exact_mod_cast hLN
    linarith only [h4c, hLNR, hc0]
  have hw : 0 < w := div_pos hc0 hNR
  have hw1 : w ≤ 1 := (div_le_one hNR).mpr hcN
  have hwN : w * N = c := by dsimp only [w]; field_simp [hNR.ne']
  have hML : (M : ℝ) * L ≤ N := by exact_mod_cast Nat.div_mul_le_self N L
  have hwM : w * M ≤ c / L := by
    apply (le_div_iff₀ hLR).mpr
    calc
      w * M * L = w * ((M : ℝ) * L) := by ring
      _ ≤ w * N := mul_le_mul_of_nonneg_left hML hw.le
      _ = c := hwN
  have hwMc : w * M ≤ c := (mul_le_mul_of_nonneg_left (by exact_mod_cast hMN) hw.le).trans_eq hwN
  have hsep : w ≤ atomSpacing M / 2 := by
    have hfour : 4 * w * M ≤ 1 := by
      have hl : 4 * (c / (L : ℝ)) ≤ 1 := by
        rw [← mul_div_assoc, div_le_one hLR]; exact h4c
      nlinarith only [hwM, hl]
    have hbound : w ≤ (1 / ((M : ℝ) + 1)) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).mpr
      nlinarith only [hfour, mul_nonneg hw.le (sub_nonneg.mpr hM1R)]
    exact hbound.trans (div_le_div_of_nonneg_right (atomSpacing_bounds hM).1 (by norm_num))
  have hsmall_pre : 32 * Real.exp 2 * w * M ≤ 1 / 8 := by
    have hcost : 32 * Real.exp 2 * (c / (L : ℝ)) ≤ 1 / 8 := by
      rw [← mul_div_assoc, div_le_iff₀ hLR]
      linarith only [h256]
    calc
      32 * Real.exp 2 * w * M = (32 * Real.exp 2) * (w * M) := by ring
      _ ≤ (32 * Real.exp 2) * (c / (L : ℝ)) := mul_le_mul_of_nonneg_left hwM (by positivity)
      _ ≤ 1 / 8 := hcost
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ_half : δ ≤ 1 / 2 :=
    (div_le_self hd.le (one_le_pow₀ hc1)).trans hd_le_half
  have hδ_grow : δ ≤ growingMassConstant / c ^ 7 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (pow_nonneg hc0.le 7)
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hy_eq : (∑ n ∈ Icc 1 N, y n ^ 2) = S := sum_atomicTailCoefficients_sq_eq_Ioc hMN x
  have hPS_eq : P + S = ∑ n ∈ Icc 1 N, x n ^ 2 := by
    rw [← hy_eq]
    exact sum_sq_prefix_add_tail hMN x
  have hG : 0 < G := mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hg : ContDiff ℝ 2 g := contDiff_tiltedUnitSpline.comp (contDiff_id.div_const _)
  have hgc : HasCompactSupport g :=
    hasCompactSupport_atomDilate hw.ne' hasCompactSupport_tiltedUnitSpline
  have hsupp := tiltedUnitSpline_atom_support hw
  have hmass : (∫ u, g u ^ 2) = G := integral_atomDilate_sq hw
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hlogc_le : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  -- 1. Prefix archimedean bound (`- (1/8) D_M` and `O(c) P`).
  have hlo : Real.log N * P -
      (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost) * P -
      (1 / 8 : ℝ) * poleDefect M x ≤ archForm (atomicTest M x g) / G := by
    have hraw := archForm_atomicTest_ge_separated_defect hg hgc hsupp hM hw hw1 hsep x
    rw [hmass] at hraw
    have hlogw : Real.log (1 / w) = Real.log N - Real.log c := by
      dsimp only [w]; rw [one_div_div, Real.log_div hNR.ne' hc0.ne']
    have hcoef : Real.log N - (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost) ≤
        2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - 2 * w * M * separatedCrossMassCost := by
      have habs : Real.log c - 2 * gammaHardyPhaseRate 0 ≤ c + 2 * |gammaHardyPhaseRate 0| := by
        linarith only [hlogc_le, neg_le_abs (gammaHardyPhaseRate 0)]
      have hcost := mul_le_mul_of_nonneg_right hwMc
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hAsep)
      rw [hlogw]
      linarith only [habs, hcost]
    have hpay := mul_le_mul_of_nonneg_right hsmall_pre (poleDefect_nonneg M x)
    have hleft := mul_le_mul_of_nonneg_right hcoef hP
    have hl_inner : Real.log N * P -
        (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost) * P -
        (1 / 8 : ℝ) * poleDefect M x ≤
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - 2 * w * M * separatedCrossMassCost) * P -
          32 * Real.exp 2 * w * M * poleDefect M x := by
      linarith only [hleft, hpay]
    apply (le_div_iff₀ hG).mpr
    exact (mul_le_mul_of_nonneg_right hl_inner hG.le).trans (by rw [mul_comm]; exact hraw)
  -- 2. Terminal archimedean Fourier reserve (`δ * log N * S - b * c * S`).
  have hhi : δ * Real.log N * S - growingReserveCost * c * S ≤ archForm (atomicTest N y g) / G := by
    have hh0 := archForm_atomicTest_ge_growing hc1 hcN y
    rw [hy_eq] at hh0
    have hh : ((growingMassConstant / c ^ 7) * Real.log N - growingReserveCost * c) * S ≤
        archForm (atomicTest N y g) / G := by
      apply (le_div_iff₀ hG).mpr
      calc
        _ = ((growingMassConstant / c ^ 7 * Real.log N - growingReserveCost * c) * G) * S := by ring
        _ ≤ _ := hh0
    have ha' := mul_le_mul_of_nonneg_right hδ_grow (mul_nonneg hlogN0 hS)
    linarith only [hh, ha']
  -- 3. Ordered archimedean cross bound.
  have hordered := atomicTest_prefix_tail_ordered hsupp hM
    (by have hp := atomSpacing_pos hM; linarith only [hsep, hp]) N x
  obtain ⟨boundary, hleft, hright⟩ := hordered
  have hcross := archForm_add_ge_of_ordered
    (contDiff_atomicTest hg M x) (hasCompactSupport_atomicTest hsupp M x)
    (contDiff_atomicTest hg N y) (hasCompactSupport_atomicTest hsupp N y) hleft hright
  rw [← atomicTest_eq_prefix_add_tail hMN x g] at hcross
  have hloMass : (∫ u, atomicTest M x g u ^ 2) = P * G := by
    rw [integral_atomicTest_sq hg hgc hsupp
      (by have hp := atomSpacing_pos hM; linarith only [hsep, hp]), hmass]
  have hhiMass : (∫ u, atomicTest N y g u ^ 2) ≤ G * (1 + 2 * c * Real.exp 1) * S := by
    have h := integral_atomicTest_sq_le_of_le_horizon hg.continuous hgc hc0 hcN hsupp y
    rw [hmass, hy_eq] at h
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hB1 : (1 : ℝ) ≤ 1 + 2 * c * Real.exp 1 := by
    have : 0 ≤ 2 * c * Real.exp 1 := by positivity
    linarith only [this]
  have hphysical : (∫ u, atomicTest M x g u ^ 2) + (∫ u, atomicTest N y g u ^ 2) ≤
      G * (1 + 2 * c * Real.exp 1) * (P + S) := by
    have hlow := mul_le_mul_of_nonneg_right hB1 (mul_nonneg hG.le hP)
    rw [hloMass]
    nlinarith only [hhiMass, hlow]
  have harch : archForm (atomicTest M x g) / G + archForm (atomicTest N y g) / G -
      2 * Real.pi * (1 + 2 * c * Real.exp 1) * (P + S) ≤ archForm (atomicTest N x g) / G := by
    apply (le_div_iff₀ hG).mpr
    have he : (archForm (atomicTest M x g) / G + archForm (atomicTest N y g) / G -
        2 * Real.pi * (1 + 2 * c * Real.exp 1) * (P + S)) * G =
          archForm (atomicTest M x g) + archForm (atomicTest N y g) -
            2 * Real.pi * (G * (1 + 2 * c * Real.exp 1) * (P + S)) := by field_simp [hG.ne']
    rw [he]
    have hpaid := mul_le_mul_of_nonneg_left hphysical (by positivity : 0 ≤ 2 * Real.pi)
    linarith only [hcross, hpaid]
  -- 4. Ratio prime source, split non-ratio bound, and exact pole vanishing on `(V_1)ᗮ`.
  have hprime := atomicWeilForm_add_full_poleDefect_le N x
  rw [← hPS_eq] at hprime
  let t₀ := δ / (8 * nonRatioDownConstant * c)
  have ht₀ : 0 < t₀ := by have := nonRatioDownConstant_pos; dsimp only [t₀]; positivity
  have hnr0 := abs_nonRatioForm_le_asymmetric_split hc1 hLN ht₀ hg.continuous hgc hsupp x
  rw [hmass] at hnr0
  have hnr : nonRatioForm g N x / G ≤
      C_nr0 * c ^ 9 * P + (δ / 8) * Real.log N * S +
        (δ / 8 + tailNonRatioConstant * c ^ 2) * S := by
    apply (div_le_iff₀ hG).mpr
    have h1 := (le_abs_self _).trans hnr0
    have he1 : nonRatioUpConstant * c / t₀ = C_nr0 * c ^ 9 := by
      have := nonRatioDownConstant_pos
      dsimp only [t₀, δ, C_nr0]
      field_simp [hd.ne', hc0.ne', this.ne']
    have he2 : t₀ * nonRatioDownConstant * c = δ / 8 := by
      have := nonRatioDownConstant_pos
      dsimp only [t₀]
      field_simp [hc0.ne', this.ne']
    rw [he1, he2] at h1
    calc
      nonRatioForm g N x ≤ G * (C_nr0 * c ^ 9 * P + δ / 8 * (Real.log N + 1) * S +
          tailNonRatioConstant * c ^ 2 * S) := h1
      _ = (C_nr0 * c ^ 9 * P + δ / 8 * Real.log N * S +
          (δ / 8 + tailNonRatioConstant * c ^ 2) * S) * G := by ring
  have hpole_zero :
      (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
        (∫ u, atomicTest N x g u * Real.exp (u / 2)) = 0 := by
    rw [integral_atomicTest_mul_exp_neg_half hg.continuous hsupp N x,
      poleFunctional_eq_zero_of_mem_conductorSubspace_one_orthogonal hN2 hz, mul_zero, zero_mul]
  -- 5. Split-source tail logarithm payment on `(1 - 5 * δ / 8) * log N * S`.
  have hlog2Lc : Real.log (2 * (L : ℝ)) ≤ Real.log (2 * L_const) + c := by
    have h1 := Real.log_le_log (by positivity : 0 < 2 * (L : ℝ))
      (mul_le_mul_of_nonneg_left hLup zero_le_two)
    rw [show 2 * (L_const * c) = (2 * L_const) * c by ring,
      Real.log_mul (by linarith only [hL_const1]) hc0.ne'] at h1
    linarith only [h1, hlogc_le]
  have hNML : (N : ℝ) < (M + 1) * L := by
    have ht : N < (M + 1) * L := by
      simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < L by omega)
    exact_mod_cast ht
  have hratio : Real.log N - Real.log M ≤ Real.log (2 * (L : ℝ)) := by
    rw [← Real.log_div hNR.ne' hMR.ne']
    apply Real.log_le_log (div_pos hNR hMR)
    apply (div_le_iff₀ hMR).mpr
    nlinarith only [hNML, mul_nonneg (sub_nonneg.mpr hM1R) hLR.le]
  have hcutP : (1 + 4 / δ) * cutoffPrimeCost M N ≤ C_tp * c ^ 8 := by
    have h1 : cutoffPrimeCost M N ≤ (Real.log (2 * L_const) + 1 + J) * c := by
      unfold cutoffPrimeCost
      have hpos : 0 ≤ Real.log (2 * L_const) + J := add_nonneg hlog2L hJ
      nlinarith only [hratio, hlog2Lc, hc1, hpos]
    have h2 : 1 + 4 / δ ≤ (1 + 4 / d) * c ^ 7 := by
      have heq : 4 / δ = (4 / d) * c ^ 7 := by
        dsimp only [δ]; field_simp [hd.ne', hc0.ne']
      have hc7 : 1 ≤ c ^ 7 := one_le_pow₀ hc1
      rw [heq]
      linarith only [hc7]
    have hcut0 : 0 ≤ cutoffPrimeCost M N := by
      have hMN_log : Real.log M ≤ Real.log N := Real.log_le_log hMR (by exact_mod_cast hMN)
      unfold cutoffPrimeCost
      linarith only [hMN_log, hJ]
    calc
      (1 + 4 / δ) * cutoffPrimeCost M N ≤
          ((1 + 4 / d) * c ^ 7) * ((Real.log (2 * L_const) + 1 + J) * c) :=
        mul_le_mul h2 h1 hcut0 (by positivity)
      _ = C_tp * c ^ 8 := by dsimp only [C_tp]; ring
  have hcutS : Real.log (2 * (L : ℝ)) + (Real.log 4 + 4) * (L : ℝ) ≤ C_ts * c := by
    have hlog4 : 0 ≤ Real.log 4 + 4 := by
      have hl := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith only [hl]
    have h1 := mul_le_mul_of_nonneg_left hLup hlog4
    dsimp only [C_ts]
    nlinarith only [hlog2Lc, h1, hc1, hlog2L]
  have htail := log_mul_tail_mass_le_split_defect_increment hL1 hLN x (show 0 < 4 / δ by positivity)
  rw [show 1 / (4 / δ) = δ / 4 by field_simp [hδ.ne'], hy_eq] at htail
  have htail' : Real.log N * S ≤
      (1 + δ / 4) * (poleDefect N x - poleDefect M x) + C_tp * c ^ 9 * P + C_ts * c ^ 2 * S := by
    have hc89 : c ^ 8 ≤ c ^ 9 := pow_le_pow_right₀ hc1 (by norm_num)
    have hc12 : c ≤ c ^ 2 := by nlinarith only [hc1]
    have hp1 : (1 + 4 / δ) * cutoffPrimeCost M N * P ≤ C_tp * c ^ 9 * P :=
      mul_le_mul_of_nonneg_right
        (hcutP.trans (mul_le_mul_of_nonneg_left hc89 (by dsimp only [C_tp]; positivity))) hP
    have hs1 : (Real.log (2 * (L : ℝ)) + (Real.log 4 + 4) * (L : ℝ)) * S ≤ C_ts * c ^ 2 * S :=
      mul_le_mul_of_nonneg_right
        (hcutS.trans (mul_le_mul_of_nonneg_left hc12 (by dsimp only [C_ts]; positivity))) hS
    linarith only [htail, hp1, hs1]
  have hcoef58 : 0 ≤ 1 - 5 * δ / 8 := by linarith only [hδ_half]
  have hcoef58_le1 : 1 - 5 * δ / 8 ≤ 1 := by linarith only [hδ]
  have htpay := mul_le_mul_of_nonneg_left htail' hcoef58
  have htpay_P : (1 - 5 * δ / 8) * (C_tp * c ^ 9 * P) ≤ C_tp * c ^ 9 * P :=
    mul_le_of_le_one_left (by dsimp only [C_tp]; positivity) hcoef58_le1
  have htpay_S : (1 - 5 * δ / 8) * (C_ts * c ^ 2 * S) ≤ C_ts * c ^ 2 * S :=
    mul_le_of_le_one_left (by dsimp only [C_ts]; positivity) hcoef58_le1
  have htpay_exp : (1 - 5 * δ / 8) * (Real.log N * S) ≤
      (1 - 5 * δ / 8) * (1 + δ / 4) * poleDefect N x -
        (1 - 5 * δ / 8) * (1 + δ / 4) * poleDefect M x +
        C_tp * c ^ 9 * P + C_ts * c ^ 2 * S := by
    have hexp1 : (1 - 5 * δ / 8) *
        ((1 + δ / 4) * (poleDefect N x - poleDefect M x) + C_tp * c ^ 9 * P + C_ts * c ^ 2 * S) =
      (1 - 5 * δ / 8) * (1 + δ / 4) * poleDefect N x -
        (1 - 5 * δ / 8) * (1 + δ / 4) * poleDefect M x +
        (1 - 5 * δ / 8) * (C_tp * c ^ 9 * P) + (1 - 5 * δ / 8) * (C_ts * c ^ 2 * S) := by ring
    rw [hexp1, ← mul_assoc] at htpay
    linarith only [htpay, htpay_P, htpay_S]
  have harch_exp : archForm (atomicTest M x g) / G + archForm (atomicTest N y g) / G -
      2 * Real.pi * (1 + 2 * c * Real.exp 1) * P -
      2 * Real.pi * (1 + 2 * c * Real.exp 1) * S ≤ archForm (atomicTest N x g) / G := by
    have hid : 2 * Real.pi * (1 + 2 * c * Real.exp 1) * (P + S) =
      2 * Real.pi * (1 + 2 * c * Real.exp 1) * P + 2 * Real.pi * (1 + 2 * c * Real.exp 1) * S := by
      ring
    linarith only [harch, hid]
  have hprime_exp : atomicWeilForm N x + poleDefect N x ≤
      Real.log N * P + Real.log N * S + (Real.log 4 + 4) * P + (Real.log 4 + 4) * S := by
    have hid : (Real.log N + (Real.log 4 + 4)) * (P + S) =
      Real.log N * P + Real.log N * S + (Real.log 4 + 4) * P + (Real.log 4 + 4) * S := by ring
    linarith only [hprime, hid]
  have hDN_keep : (a / c ^ 7) * poleDefect N x ≤
      poleDefect N x - (1 - 5 * δ / 8) * (1 + δ / 4) * poleDefect N x := by
    have h1 : (a / c ^ 7) * poleDefect N x ≤
        (1 - (1 - 5 * δ / 8) * (1 + δ / 4)) * poleDefect N x := by
      refine mul_le_mul_of_nonneg_right ?_ (poleDefect_nonneg N x)
      have heq : a / c ^ 7 = δ / 8 := by dsimp only [a, δ]; ring
      rw [heq]
      nlinarith only [hδ, sq_nonneg δ]
    linarith only [h1, (by ring : (1 - (1 - 5 * δ / 8) * (1 + δ / 4)) * poleDefect N x =
      poleDefect N x - (1 - 5 * δ / 8) * (1 + δ / 4) * poleDefect N x)]
  have hDM_keep : (1 / 2 : ℝ) * poleDefect M x ≤
      (1 - 5 * δ / 8) * (1 + δ / 4) * poleDefect M x - (1 / 8 : ℝ) * poleDefect M x := by
    have h1 : (1 / 2 : ℝ) * poleDefect M x ≤
        ((1 - 5 * δ / 8) * (1 + δ / 4) - 1 / 8) * poleDefect M x := by
      refine mul_le_mul_of_nonneg_right ?_ (poleDefect_nonneg M x)
      nlinarith only [hδ, hδ_half]
    linarith only [h1, (by ring : ((1 - 5 * δ / 8) * (1 + δ / 4) - 1 / 8) * poleDefect M x =
      (1 - 5 * δ / 8) * (1 + δ / 4) * poleDefect M x - (1 / 8 : ℝ) * poleDefect M x)]
  have hlogS_keep : (a / c ^ 7) * Real.log N * S ≤ (δ / 4) * (Real.log N * S) := by
    have heq : a / c ^ 7 = δ / 8 := by dsimp only [a, δ]; ring
    rw [heq]
    have hh : (δ / 8) * Real.log N * S ≤ (δ / 4) * Real.log N * S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hδ]) hlogN0) hS
    linarith only [hh, (by ring : (δ / 4) * Real.log N * S = (δ / 4) * (Real.log N * S))]
  -- 6. Collect prefix and terminal mass coefficients cleanly.
  have hP_cost : (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost) * P +
      2 * Real.pi * (1 + 2 * c * Real.exp 1) * P + (Real.log 4 + 4) * P +
      C_tp * c ^ 9 * P + C_nr0 * c ^ 9 * P ≤ C₀ * c ^ 9 * P := by
    have hsumP : (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
        2 * Real.pi * (1 + 2 * c * Real.exp 1) + (Real.log 4 + 4) +
        C_tp * c ^ 9 + C_nr0 * c ^ 9) * P ≤ (C₀ * c ^ 9) * P := by
      refine mul_le_mul_of_nonneg_right ?_ hP
      have hc19 : c ≤ c ^ 9 := by
        simpa only [pow_one] using pow_le_pow_right₀ hc1 (by norm_num : 1 ≤ 9)
      have h19 : (1 : ℝ) ≤ c ^ 9 := one_le_pow₀ hc1
      have h4 : 0 ≤ Real.log 4 + 4 := by
        have hl := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith only [hl]
      have harchP : c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
          2 * Real.pi * (1 + 2 * c * Real.exp 1) + (Real.log 4 + 4) ≤ C_arch0 * c ^ 9 := by
        have ht1 : 2 * |gammaHardyPhaseRate 0| ≤ 2 * |gammaHardyPhaseRate 0| * c ^ 9 :=
          le_mul_of_one_le_right (by positivity) h19
        have ht2 : 2 * c * separatedCrossMassCost ≤ 2 * separatedCrossMassCost * c ^ 9 := by
          have := mul_le_mul_of_nonneg_left hc19 (mul_nonneg zero_le_two hAsep)
          linarith only [this, (by ring : 2 * separatedCrossMassCost * c = 2 * c * separatedCrossMassCost)]
        have ht3 : 2 * Real.pi * (1 + 2 * c * Real.exp 1) ≤
            2 * Real.pi * (1 + 2 * Real.exp 1) * c ^ 9 := by
          have hpi1 : 2 * Real.pi ≤ 2 * Real.pi * c ^ 9 :=
            le_mul_of_one_le_right (by positivity) h19
          have hpi2 : 4 * Real.pi * Real.exp 1 * c ≤ 4 * Real.pi * Real.exp 1 * c ^ 9 :=
            mul_le_mul_of_nonneg_left hc19 (by positivity)
          linarith only [hpi1, hpi2,
            (by ring : 2 * Real.pi * (1 + 2 * c * Real.exp 1) =
              2 * Real.pi + 4 * Real.pi * Real.exp 1 * c),
            (by ring : 2 * Real.pi * (1 + 2 * Real.exp 1) * c ^ 9 =
              2 * Real.pi * c ^ 9 + 4 * Real.pi * Real.exp 1 * c ^ 9)]
        have ht4 : Real.log 4 + 4 ≤ (Real.log 4 + 4) * c ^ 9 :=
          le_mul_of_one_le_right h4 h19
        dsimp only [C_arch0]
        linarith only [hc19, ht1, ht2, ht3, ht4,
          (by ring : (1 + 2 * |gammaHardyPhaseRate 0| + 2 * separatedCrossMassCost +
            2 * Real.pi * (1 + 2 * Real.exp 1) + (Real.log 4 + 4)) * c ^ 9 =
            c ^ 9 + 2 * |gammaHardyPhaseRate 0| * c ^ 9 + 2 * separatedCrossMassCost * c ^ 9 +
              2 * Real.pi * (1 + 2 * Real.exp 1) * c ^ 9 + (Real.log 4 + 4) * c ^ 9)]
      dsimp only [C₀]
      linarith only [harchP, h19]
    linarith only [hsumP, (by ring : (c + 2 * |gammaHardyPhaseRate 0| +
      2 * c * separatedCrossMassCost) * P + 2 * Real.pi * (1 + 2 * c * Real.exp 1) * P +
      (Real.log 4 + 4) * P + C_tp * c ^ 9 * P + C_nr0 * c ^ 9 * P =
      (c + 2 * |gammaHardyPhaseRate 0| + 2 * c * separatedCrossMassCost +
        2 * Real.pi * (1 + 2 * c * Real.exp 1) + (Real.log 4 + 4) +
        C_tp * c ^ 9 + C_nr0 * c ^ 9) * P)]
  have hS_cost : growingReserveCost * c * S + 2 * Real.pi * (1 + 2 * c * Real.exp 1) * S +
      (Real.log 4 + 4) * S + (δ / 8 + tailNonRatioConstant * c ^ 2) * S + C_ts * c ^ 2 * S ≤
        C₁ * c ^ 2 * S := by
    have hsumS : (growingReserveCost * c + 2 * Real.pi * (1 + 2 * c * Real.exp 1) +
        (Real.log 4 + 4) + (δ / 8 + tailNonRatioConstant * c ^ 2) + C_ts * c ^ 2) * S ≤
          (C₁ * c ^ 2) * S := by
      refine mul_le_mul_of_nonneg_right ?_ hS
      have hc12 : c ≤ c ^ 2 := by nlinarith only [hc1]
      have h12 : (1 : ℝ) ≤ c ^ 2 := one_le_pow₀ hc1
      have h4 : 0 ≤ Real.log 4 + 4 := by
        have hl := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith only [hl]
      have hδ8 : δ / 8 ≤ 1 := by linarith only [hδ_half]
      have hg0 := growingReserveCost_nonneg
      have hs1 : growingReserveCost * c ≤ growingReserveCost * c ^ 2 :=
        mul_le_mul_of_nonneg_left hc12 hg0
      have hs2 : 2 * Real.pi * (1 + 2 * c * Real.exp 1) ≤
          2 * Real.pi * (1 + 2 * Real.exp 1) * c ^ 2 := by
        have hpi1 : 2 * Real.pi ≤ 2 * Real.pi * c ^ 2 :=
          le_mul_of_one_le_right (by positivity) h12
        have hpi2 : 4 * Real.pi * Real.exp 1 * c ≤ 4 * Real.pi * Real.exp 1 * c ^ 2 :=
          mul_le_mul_of_nonneg_left hc12 (by positivity)
        linarith only [hpi1, hpi2,
          (by ring : 2 * Real.pi * (1 + 2 * c * Real.exp 1) =
            2 * Real.pi + 4 * Real.pi * Real.exp 1 * c),
          (by ring : 2 * Real.pi * (1 + 2 * Real.exp 1) * c ^ 2 =
            2 * Real.pi * c ^ 2 + 4 * Real.pi * Real.exp 1 * c ^ 2)]
      have hs3 : Real.log 4 + 4 ≤ (Real.log 4 + 4) * c ^ 2 :=
        le_mul_of_one_le_right h4 h12
      dsimp only [C₁]
      linarith only [h12, hδ8, hs1, hs2, hs3,
        (by ring : (growingReserveCost + 2 * Real.pi * (1 + 2 * Real.exp 1) + (Real.log 4 + 4) +
          C_ts + 1 + tailNonRatioConstant + 1) * c ^ 2 =
          growingReserveCost * c ^ 2 + 2 * Real.pi * (1 + 2 * Real.exp 1) * c ^ 2 +
            (Real.log 4 + 4) * c ^ 2 + C_ts * c ^ 2 + tailNonRatioConstant * c ^ 2 + 2 * c ^ 2)]
    linarith only [hsumS, (by ring : growingReserveCost * c * S +
      2 * Real.pi * (1 + 2 * c * Real.exp 1) * S + (Real.log 4 + 4) * S +
      (δ / 8 + tailNonRatioConstant * c ^ 2) * S + C_ts * c ^ 2 * S =
      (growingReserveCost * c + 2 * Real.pi * (1 + 2 * c * Real.exp 1) +
        (Real.log 4 + 4) + (δ / 8 + tailNonRatioConstant * c ^ 2) + C_ts * c ^ 2) * S)]
  -- 7. Exact identity to `completeWeilEnergy tiltedUnitSpline c N z`.
  have henergy : completeWeilEnergy tiltedUnitSpline c N z =
      archForm (atomicTest N x g) / G - atomicWeilForm N x - nonRatioForm g N x / G := by
    rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero hc0 hN1]
    have hdiv : G = ∫ u, g u ^ 2 := hmass.symm
    rw [← hdiv]
    have he := weilQuad_atomicTest_div_eq_arithmetic_add_gamma hg hsupp N x
    rw [hmass] at he
    have hpr : primeSum (atomicTest N x g) / G =
        atomicWeilForm N x + nonRatioForm g N x / G := by
      rw [primeSum_atomicTest_eq_ratio_add hg.continuous hgc hsupp hw.le, hmass]
      field_simp [hG.ne']
    rw [he]
    unfold overlapArithmeticEnergy overlapPrimeEnergy
    rw [hmass, hpr, hpole_zero]
    ring
  rw [henergy]
  have hlogS_id : δ * Real.log N * S - Real.log N * S - (δ / 8) * Real.log N * S =
      (δ / 4) * (Real.log N * S) - (1 - 5 * δ / 8) * (Real.log N * S) := by ring
  change (1 / 2 : ℝ) * poleDefect M x + (a / c ^ 7) * poleDefect N x +
    (a / c ^ 7) * Real.log N * S - C₀ * c ^ 9 * P - C₁ * c ^ 2 * S ≤ _
  linarith only [hlo, hhi, harch_exp, hprime_exp, hnr, htpay_exp,
    hDN_keep, hDM_keep, hlogS_keep, hP_cost, hS_cost, hlogS_id]

/-- **Asymmetric two-region reserve on `(conductorSubspace R N)ᗮ`.**
Because the `c^9` mass penalty is confined to the prefix `P` where an order-`1` defect reserve
`(1 / 2) D_M` is available, `K * c^9 ≤ log R / D - 1` (instead of `K * c^{16}`) suffices to
retain both `(k / 4) P` and `(a k / (2 c^7)) S`. -/
theorem exists_completeWeilEnergy_asymmetric_two_region_reserve :
    ∃ a K : ℝ, 0 < a ∧ a ≤ 1 / 8 ∧ 0 < K ∧
      ∀ {c : ℝ} {R N : ℕ}, 1 ≤ c → 2 ≤ R → linearDefectCutoff c ≤ N →
        R * R ≤ N / linearDefectCutoff c →
        18 * (1 + Real.log R) ≤ Real.log (N / linearDefectCutoff c : ℕ) →
        K * c ^ 9 ≤ Real.log R / explicitConductorCutoffConstant - 1 →
        terminalPacketCost R (N / linearDefectCutoff c) N /
          Real.log (N / linearDefectCutoff c : ℕ) ≤ a / (4 * c ^ 7) →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
        (Real.log R / explicitConductorCutoffConstant - 1) / 4 *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        a * (Real.log R / explicitConductorCutoffConstant - 1) / (2 * c ^ 7) *
          (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N w := by
  obtain ⟨a, C₀, C₁, ha, ha8, hC₀, hC₁, hreserve⟩ :=
    exists_completeWeilEnergy_asymmetric_prefix_terminal_reserve
  let K := 8 * C₀ + 4 * C₁ / a
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨a, K, ha, ha8, hK, ?_⟩
  intro c R N hc hR hLN hRM hlog hcut hleak w hw
  let M := N / linearDefectCutoff c
  let x := primeHorizonExtension w
  let P := ∑ n ∈ Icc 1 M, x n ^ 2
  let S := ∑ n ∈ Ioc M N, x n ^ 2
  let k := Real.log R / explicitConductorCutoffConstant - 1
  let B := terminalPacketCost R M N / Real.log M
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hM : 2 ≤ M := by have hh := Nat.mul_le_mul hR hR; omega
  have hMN : M ≤ N := Nat.div_le_self N (linearDefectCutoff c)
  have hN2 : 2 ≤ N := hM.trans hMN
  have hk : 0 < k := (mul_pos hK (pow_pos hc0 9)).trans_le hcut
  have hscale : explicitConductorCutoffConstant ≤ Real.log R := by
    have hh : 1 ≤ Real.log R / explicitConductorCutoffConstant := by
      dsimp only [k] at hk; linarith only [hk]
    simpa only [one_mul] using (le_div_iff₀ explicitConductorCutoffConstant_pos).mp hh
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hsplit : ‖w‖ ^ 2 = P + S := by
    rw [← sum_primeHorizonExtension_sq]
    dsimp only [P, S, x]
    rw [Ioc_eq_Icc_sdiff_Icc M N, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
  have hw1 : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw v (conductorSubspace_mono (by omega : 1 ≤ R) N hv)
  have hraw := hreserve hc hLN hw1
  have hpre := poleDefect_prefix_ge_of_conductor_orthogonal hR hM hMN hRM hlog hscale hw
  have hwhole := poleDefect_ge_explicit_on_conductor_orthogonal hR hN2 hw
  have htwoB : 2 * terminalPacketCost R M N / Real.log M = 2 * B := by dsimp only [B]; ring
  rw [htwoB] at hpre
  change k * ((15 / 16 : ℝ) * P - 2 * B * S) ≤ poleDefect M x at hpre
  rw [hsplit] at hwhole
  change k * (P + S) ≤ poleDefect N x at hwhole
  have h8C₀_le : 8 * C₀ ≤ K := by
    have hz : 0 ≤ 4 * C₁ / a := by positivity
    dsimp only [K]; linarith only [hz]
  have h4C₁_le : 4 * C₁ / a ≤ K := by
    dsimp only [K]; linarith only [hC₀]
  have hC₀_le : C₀ * c ^ 9 ≤ k / 8 := by
    have h1 : 8 * C₀ * c ^ 9 ≤ K * c ^ 9 :=
      mul_le_mul_of_nonneg_right h8C₀_le (pow_nonneg hc0.le 9)
    linarith only [h1, hcut]
  have hC₁_le : C₁ * c ^ 2 ≤ a * k / (4 * c ^ 7) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * c ^ 7)).mpr
    have h1 : (4 * C₁ / a) * c ^ 9 ≤ k :=
      (mul_le_mul_of_nonneg_right h4C₁_le (pow_nonneg hc0.le 9)).trans hcut
    have h2 := mul_le_mul_of_nonneg_left h1 ha.le
    have he : a * ((4 * C₁ / a) * c ^ 9) = 4 * C₁ * c ^ 9 := by field_simp [ha.ne']
    rw [he] at h2
    exact (by ring : C₁ * c ^ 2 * (4 * c ^ 7) = 4 * C₁ * c ^ 9).trans_le (by linarith only [h2])
  have hpre' := mul_le_mul_of_nonneg_left hpre (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hwhole' := mul_le_mul_of_nonneg_left hwhole (div_nonneg ha.le (pow_nonneg hc0.le 7))
  have hcostP := mul_le_mul_of_nonneg_right hC₀_le hP
  have hcostS := mul_le_mul_of_nonneg_right hC₁_le hS
  have hleakS := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleak hk.le) hS
  have hlogNS_nonneg : 0 ≤ (a / c ^ 7) * Real.log N * S := by
    have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    positivity
  have hpextra : 0 ≤ (a / c ^ 7) * k * P := by positivity
  have hkP : 0 ≤ k * P := mul_nonneg hk.le hP
  have hidP : (1 / 2 : ℝ) * (k * ((15 / 16 : ℝ) * P - 2 * B * S)) +
      (a / c ^ 7) * (k * (P + S)) - (k / 8) * P - (a * k / (4 * c ^ 7)) * S =
        (11 / 32 : ℝ) * (k * P) + (a / c ^ 7) * k * P +
          (3 * a * k / (4 * c ^ 7)) * S - (k * B) * S := by
    field_simp [hc0.ne']
    ring
  have hidS : (3 * a * k / (4 * c ^ 7)) * S - (k * (a / (4 * c ^ 7))) * S =
      (a * k / (2 * c ^ 7)) * S := by
    field_simp [hc0.ne']
    ring
  change (k / 4) * P + (a * k / (2 * c ^ 7)) * S ≤ completeWeilEnergy tiltedUnitSpline c N w
  linarith only [hraw, hpre', hwhole', hcostP, hcostS, hleakS, hlogNS_nonneg,
    hpextra, hkP, hidP, hidS]

/-! ## Section 5: Polynomial-Conductor Complement Coercivity Below `1 / 9` -/

private theorem eventually_log_nat_le_rpow_36_asymmetric :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).bound zero_lt_one)
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
    simpa only [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
  exact (le_abs_self _).trans habs

/-- **Polynomial-conductor complement coercivity up to `α < 1 / 9`.**
For every `θ > 0` and every `0 < α < 1 / 9`, eventually in `N` and uniformly across
`1 ≤ c ≤ (log N)^α`, every vector `z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ` satisfies
`(c_orth * Real.log N / c ^ 7) * ‖z‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N z`. -/
theorem eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal_below_one_ninth
    {θ α : ℝ} (hθ : 0 < θ) (_hα : 0 < α) (hα_lt : α < 1 / 9) :
    ∃ c_orth : ℝ, 0 < c_orth ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
        ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
          z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ →
          (c_orth * Real.log (N : ℝ) / c ^ 7) * ‖z‖ ^ 2 ≤
            completeWeilEnergy tiltedUnitSpline c N z := by
  obtain ⟨a, K, ha, ha8, hK, hres⟩ := exists_completeWeilEnergy_asymmetric_two_region_reserve
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  let θ₀ := min θ (1 / 36)
  have hθ₀ : 0 < θ₀ := lt_min hθ (by norm_num)
  have hθ₀_le : θ₀ ≤ θ := min_le_left _ _
  have hθ₀_36 : θ₀ ≤ 1 / 36 := min_le_right _ _
  let c_orth := a * θ₀ / (8 * D)
  have hc_orth : 0 < c_orth := by dsimp only [c_orth]; positivity
  refine ⟨c_orth, hc_orth, ?_⟩
  let μ := 1 - 9 * α
  have hμ : 0 < μ := by dsimp only [μ]; linarith only [hα_lt]
  let H_lin := 256 * Real.exp 2 + 4
  have hH_lin : 1 ≤ H_lin := by
    have he2 := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp only [H_lin]; linarith only [he2]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hNθlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ₀) atTop atTop :=
    (tendsto_rpow_atTop hθ₀).comp tendsto_natCast_atTop_atTop
  let M_L := max 2000 (max H_lin (max (2 / θ₀) (4 * D / θ₀)))
  let B_leak := 8 * (4 + Real.log (2 * H_lin) + 1) / a
  filter_upwards [hNθlim.eventually_ge_atTop 4,
    hLlim.eventually_ge_atTop M_L,
    ((tendsto_rpow_atTop hμ).comp hLlim).eventually_ge_atTop
      (max (4 * D * K / θ₀ + 1) (B_leak + 1)),
    eventually_log_nat_le_rpow_36_asymmetric,
    eventually_ge_atTop 3] with N hNθ4 hLM hLμ hLX hN3 c hc1 hcup z hz_orth
  dsimp only [Function.comp_def] at hLμ
  let L := Real.log (N : ℝ)
  let R := ⌊(N : ℝ) ^ θ₀⌋₊
  let T := linearDefectCutoff c
  let M := N / T
  have hL2000 : 2000 ≤ L := (le_max_left _ _).trans hLM
  have hHL : H_lin ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hLM
  have hL_2θ : 2 / θ₀ ≤ L :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLM
  have hL_4Dθ : 4 * D / θ₀ ≤ L :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLM
  have hL1 : 1 ≤ L := by linarith only [hL2000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1R
  have hcL : c ≤ L :=
    hcup.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα_lt] : α ≤ 1))
  obtain ⟨hT3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
  have hT1 : 1 ≤ T := by omega
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  let X := (N : ℝ) ^ (1 / 36 : ℝ)
  have hX1 : 1 ≤ X := hL1.trans hLX
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
    dsimp only [X]; rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hR2 : 2 ≤ R :=
    Nat.le_floor (by exact_mod_cast (show (2 : ℝ) ≤ (N : ℝ) ^ θ₀ by linarith only [hNθ4]))
  have hRX : (R : ℝ) ≤ X :=
    (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hN1R hθ₀_36)
  have hTX : (T : ℝ) ≤ X ^ 2 := by
    calc
      (T : ℝ) ≤ H_lin * c := hTup
      _ ≤ X * X := mul_le_mul (hHL.trans hLX) (hcL.trans hLX) hc0.le hX0.le
      _ = X ^ 2 := by ring
  have hRRT : R * R * T ≤ N := by
    have hh : (R : ℝ) ^ 2 * T ≤ (N : ℝ) := by
      calc
        (R : ℝ) ^ 2 * T ≤ X ^ 2 * X ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg R) hRX 2) hTX hT0.le (by positivity)
        _ = X ^ 4 := by ring
        _ ≤ (N : ℝ) := (pow_le_pow_right₀ hX1 (by norm_num : 4 ≤ 36)).trans_eq hX36
    have hhNat : R ^ 2 * T ≤ N := by exact_mod_cast hh
    simpa only [pow_two] using hhNat
  have hRM : R * R ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < T)).mpr hRRT
  have hTN : T ≤ N := by
    have hR1 : 1 ≤ R * R := Nat.mul_pos (by omega) (by omega)
    exact (by simpa only [one_mul] using Nat.mul_le_mul_right T hR1 : T ≤ R * R * T).trans hRRT
  have hM2 : 2 ≤ M := (by norm_num : 2 ≤ 2 * 2).trans ((Nat.mul_le_mul hR2 hR2).trans hRM)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hfloor : (N : ℝ) < ((M : ℝ) + 1) * T := by
    have hh : N < (M + 1) * T := by
      simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < T by omega)
    exact_mod_cast hh
  have hratio : Real.log N - Real.log M ≤ Real.log (2 * (T : ℝ)) := by
    rw [← Real.log_div hN0.ne' hM0.ne']
    apply Real.log_le_log (div_pos hN0 hM0)
    apply (div_le_iff₀ hM0).mpr
    nlinarith only [hfloor, mul_nonneg (sub_nonneg.mpr hM1) hT0.le]
  have hlog2T : Real.log (2 * (T : ℝ)) ≤ L / 4 + 1 := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * (T : ℝ))
      (mul_le_mul_of_nonneg_left hTX zero_le_two)
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hX0.ne'), Real.log_pow,
      show Real.log X = (1 / 36 : ℝ) * L from Real.log_rpow hN0 _] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hh, h2, hL0]
  have hhalf_M : L / 2 ≤ Real.log M := by linarith only [hratio, hlog2T, hL2000]
  have hlogR_le : Real.log R ≤ (1 / 36 : ℝ) * L := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < R by omega)) hRX
    rwa [show Real.log X = (1 / 36 : ℝ) * L from Real.log_rpow hN0 _] at hh
  have hlogM_cond : 18 * (1 + Real.log R) ≤ Real.log M := by
    linarith only [hlogR_le, hratio, hlog2T, hL2000]
  -- Gap lower bound on `k = log R / D - 1`.
  have hR_half : (1 / 2 : ℝ) * (N : ℝ) ^ θ₀ ≤ (R : ℝ) := by
    have hgt : (N : ℝ) ^ θ₀ - 1 < (R : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    linarith only [hNθ4, hgt]
  have hlogR_lb : (θ₀ / 2) * L ≤ Real.log R := by
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hpos : 0 < (N : ℝ) ^ θ₀ := by linarith only [hNθ4]
    have h1 := Real.log_le_log (by positivity) hR_half
    rw [Real.log_mul (by norm_num) hpos.ne', one_div, Real.log_inv, Real.log_rpow hN0] at h1
    have h2 : 2 ≤ θ₀ * L := by
      have h := (div_le_iff₀ hθ₀).mp hL_2θ; linarith only [h]
    linarith only [h1, hlog2, h2]
  have hgap_L : (θ₀ / (4 * D)) * L ≤ Real.log R / D - 1 := by
    have hdiv := div_le_div_of_nonneg_right hlogR_lb hD.le
    have h1 : (θ₀ / 2) * L / D = 2 * ((θ₀ / (4 * D)) * L) := by field_simp [hD.ne']; ring
    have h4D : 4 * D ≤ θ₀ * L := by
      have h := (div_le_iff₀ hθ₀).mp hL_4Dθ; linarith only [h]
    have h2 : 1 ≤ (θ₀ / (4 * D)) * L := by
      rw [div_mul_eq_mul_div, one_le_div (by positivity)]
      linarith only [h4D]
    linarith only [hdiv, h1, h2]
  have hc9_rpow : c ^ 9 ≤ L ^ (9 * α) := by
    have hp := pow_le_pow_left₀ hc0.le hcup 9
    have he : (L ^ α) ^ (9 : ℕ) = L ^ (9 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  have hL_split : L ^ μ * L ^ (9 * α) = L := by
    rw [← Real.rpow_add hL0]
    have hexp : μ + 9 * α = 1 := by dsimp only [μ]; ring
    rw [hexp, Real.rpow_one]
  have hKc9 : K * c ^ 9 ≤ Real.log R / D - 1 := by
    have h1 : 4 * D * K / θ₀ ≤ L ^ μ := by
      have hm := (le_max_left _ _).trans hLμ; linarith only [hm]
    have hK_le : K ≤ (θ₀ / (4 * D)) * L ^ μ := by
      have hh := (div_le_iff₀ hθ₀).mp h1
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith only [hh]
    calc
      K * c ^ 9 ≤ ((θ₀ / (4 * D)) * L ^ μ) * L ^ (9 * α) :=
        mul_le_mul hK_le hc9_rpow (by positivity) (by positivity)
      _ = (θ₀ / (4 * D)) * (L ^ μ * L ^ (9 * α)) := by ring
      _ = (θ₀ / (4 * D)) * L := by rw [hL_split]
      _ ≤ Real.log R / D - 1 := hgap_L
  -- Terminal leakage bound `terminalPacketCost R M N / Real.log M ≤ a / (4 * c ^ 7)`.
  have hlogM_pos : 0 < Real.log M := by linarith only [hhalf_M, hL0]
  have hleak : terminalPacketCost R M N / Real.log M ≤ a / (4 * c ^ 7) := by
    have hterm1 : terminalPacketCost R M N ≤ (4 + Real.log (2 * H_lin) + 1) * c := by
      have hh := terminalPacketCost_nat_div_le hT1 hTN hRM
      have ht := Real.log_le_log (by positivity : 0 < 2 * (T : ℝ))
        (mul_le_mul_of_nonneg_left hTup zero_le_two)
      rw [show 2 * (H_lin * c) = (2 * H_lin) * c by ring,
        Real.log_mul (by linarith only [hH_lin]) hc0.ne'] at ht
      have hlogc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
      have hpos : 0 ≤ 4 + Real.log (2 * H_lin) :=
        add_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hH_lin]))
      nlinarith only [hh, ht, hlogc, hc1, hpos]
    have hdivM : terminalPacketCost R M N / Real.log M ≤
        2 * (4 + Real.log (2 * H_lin) + 1) * c / L := by
      rw [div_le_div_iff₀ hlogM_pos hL0]
      have hpos : 0 ≤ 4 + Real.log (2 * H_lin) + 1 :=
        add_nonneg (add_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hH_lin])))
          zero_le_one
      have h1 := mul_le_mul_of_nonneg_right hterm1 hL0.le
      have h2 := mul_le_mul_of_nonneg_left hhalf_M (mul_nonneg (mul_nonneg zero_le_two hpos) hc0.le)
      nlinarith only [h1, h2]
    have hBleak_L : B_leak ≤ L ^ μ := by
      have hm := (le_max_right _ _).trans hLμ; linarith only [hm]
    have hc89 : c ^ 8 ≤ c ^ 9 := pow_le_pow_right₀ hc1 (by norm_num)
    have hBleak_mul : 8 * (4 + Real.log (2 * H_lin) + 1) * c ^ 8 ≤ a * L := by
      have h1 : 8 * (4 + Real.log (2 * H_lin) + 1) ≤ a * L ^ μ := by
        have hh := (div_le_iff₀ ha).mp (by dsimp only [B_leak] at hBleak_L; exact hBleak_L)
        linarith only [hh]
      have hpos : 0 ≤ 8 * (4 + Real.log (2 * H_lin) + 1) := by
        have hl := Real.log_nonneg (by linarith only [hH_lin] : (1 : ℝ) ≤ 2 * H_lin)
        linarith only [hl]
      calc
        8 * (4 + Real.log (2 * H_lin) + 1) * c ^ 8 ≤
            (a * L ^ μ) * L ^ (9 * α) :=
          mul_le_mul h1 (hc89.trans hc9_rpow) (by positivity) (by positivity)
        _ = a * (L ^ μ * L ^ (9 * α)) := by ring
        _ = a * L := by rw [hL_split]
    have hstep : 2 * (4 + Real.log (2 * H_lin) + 1) * c / L ≤ a / (4 * c ^ 7) := by
      rw [div_le_div_iff₀ hL0 (by positivity : 0 < 4 * c ^ 7)]
      calc
        2 * (4 + Real.log (2 * H_lin) + 1) * c * (4 * c ^ 7) =
            8 * (4 + Real.log (2 * H_lin) + 1) * c ^ 8 := by ring
        _ ≤ a * L := hBleak_mul
    exact hdivM.trans hstep
  -- Monotonicity from `⌊N ^ θ⌋₊` down to `R = ⌊N ^ θ₀⌋₊`.
  have hR_le_Q : R ≤ ⌊(N : ℝ) ^ θ⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hN1R hθ₀_le)
  have hz_R : z ∈ (conductorSubspace R N)ᗮ := fun v hv =>
    hz_orth v (conductorSubspace_mono hR_le_Q N hv)
  have hcoerc := hres hc1 hR2 hTN hRM hlogM_cond hKc9 hleak hz_R
  let P := ∑ n ∈ Icc 1 M, primeHorizonExtension z n ^ 2
  let S := ∑ n ∈ Ioc M N, primeHorizonExtension z n ^ 2
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hMN : M ≤ N := Nat.div_le_self N T
  have hnorm_split : ‖z‖ ^ 2 = P + S := by
    rw [← sum_primeHorizonExtension_sq]
    dsimp only [P, S]
    rw [Ioc_eq_Icc_sdiff_Icc M N, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
  let k := Real.log R / D - 1
  have hk0 : 0 < k := (mul_pos (div_pos hθ₀ (by positivity)) hL0).trans_le hgap_L
  have hcoefP : c_orth * L / c ^ 7 ≤ k / 4 := by
    have ha_le : a / (2 * c ^ 7) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * c ^ 7) (by norm_num)]
      have hc7 : (1 : ℝ) ≤ c ^ 7 := one_le_pow₀ hc1
      nlinarith only [ha8, hc7]
    calc
      c_orth * L / c ^ 7 = (a / (2 * c ^ 7)) * ((θ₀ / (4 * D)) * L) := by
        dsimp only [c_orth]; field_simp [hD.ne', hc0.ne']; ring
      _ ≤ (1 / 4 : ℝ) * k :=
        mul_le_mul ha_le hgap_L (by positivity) (by norm_num)
      _ = k / 4 := by ring
  have hcoefS : c_orth * L / c ^ 7 ≤ a * k / (2 * c ^ 7) := by
    calc
      c_orth * L / c ^ 7 = (a / (2 * c ^ 7)) * ((θ₀ / (4 * D)) * L) := by
        dsimp only [c_orth]; field_simp [hD.ne', hc0.ne']; ring
      _ ≤ (a / (2 * c ^ 7)) * k :=
        mul_le_mul_of_nonneg_left hgap_L (by positivity)
      _ = a * k / (2 * c ^ 7) := by ring
  have hp_term := mul_le_mul_of_nonneg_right hcoefP hP0
  have hs_term := mul_le_mul_of_nonneg_right hcoefS hS0
  rw [hnorm_split, mul_add]
  change (c_orth * L / c ^ 7) * P + (c_orth * L / c ^ 7) * S ≤ _
  change (k / 4) * P + (a * k / (2 * c ^ 7)) * S ≤ _ at hcoerc
  linarith only [hcoerc, hp_term, hs_term]

/-- **Global polynomial-conductor ceiling on nonpositive subspaces up to `α < 1 / 9`.**
For every `θ > 0` and `0 < α < 1 / 9`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
every subspace `U` on which `completeWeilEnergy` is nonpositive on nonzero vectors satisfies
`Module.finrank ℝ U ≤ ⌊(N : ℝ) ^ θ⌋₊`. -/
theorem eventually_completeWeil_global_negIndex_le_polynomialConductor_below_one_ninth
    {θ α : ℝ} (hθ : 0 < θ) (hα : 0 < α) (hα_lt : α < 1 / 9) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ U : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)),
        (∀ z ∈ U, z ≠ 0 → completeWeilEnergy tiltedUnitSpline c N z ≤ 0) →
        Module.finrank ℝ U ≤ ⌊(N : ℝ) ^ θ⌋₊ := by
  let θ₀ := min θ (1 / 4)
  have hθ₀ : 0 < θ₀ := lt_min hθ (by norm_num)
  have hθ₀_le : θ₀ ≤ θ := min_le_left _ _
  have hθ₀_4 : θ₀ ≤ 1 / 4 := min_le_right _ _
  obtain ⟨c_orth, hc_orth, horth⟩ :=
    eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal_below_one_ninth hθ₀ hα hα_lt
  have hNθlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ₀) atTop atTop :=
    (tendsto_rpow_atTop hθ₀).comp tendsto_natCast_atTop_atTop
  filter_upwards [horth, hNθlim.eventually_ge_atTop 2, eventually_ge_atTop 3] with
    N horthN hNθ2 hN3 c hc1 hcup U hU
  have hN2 : 2 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1R
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  let Q₀ := ⌊(N : ℝ) ^ θ₀⌋₊
  have hQ₀_mono : Q₀ ≤ ⌊(N : ℝ) ^ θ⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hN1R hθ₀_le)
  have hQ₀_pos : 0 < Q₀ :=
    Nat.le_floor (by exact_mod_cast (show (1 : ℝ) ≤ (N : ℝ) ^ θ₀ by linarith only [hNθ2]))
  have hQ₀_le : (Q₀ : ℝ) ≤ (N : ℝ) ^ θ₀ := Nat.floor_le (by positivity)
  have h2log : 2 * Real.log (Q₀ : ℝ) < Real.log (N : ℝ) := by
    have hlog_le : Real.log (Q₀ : ℝ) ≤ θ₀ * Real.log (N : ℝ) :=
      (Real.log_le_log (by exact_mod_cast hQ₀_pos) hQ₀_le).trans_eq (Real.log_rpow hN0 θ₀)
    have hhalf : 2 * (θ₀ * Real.log (N : ℝ)) ≤ (1 / 2) * Real.log (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hθ₀_4 hL0.le; linarith only [h]
    linarith only [hlog_le, hhalf, hL0]
  have hinf_bot : U ⊓ (conductorSubspace Q₀ N)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    by_contra hzne
    have hz_le := hU z hz.1 hzne
    have hz_ge := horthN c hc1 hcup hz.2
    have hpos : 0 < (c_orth * Real.log (N : ℝ) / c ^ 7) * ‖z‖ ^ 2 :=
      mul_pos (div_pos (mul_pos hc_orth hL0) (pow_pos hc0 7))
        (sq_pos_of_pos (norm_pos_iff.mpr hzne))
    linarith only [hz_le, hz_ge, hpos]
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq U ((conductorSubspace Q₀ N)ᗮ)
  rw [Submodule.finrank_eq_zero.mpr hinf_bot, add_zero] at hgrass
  have hsup_le : Module.finrank ℝ ↥(U ⊔ (conductorSubspace Q₀ N)ᗮ) ≤
      Module.finrank ℝ (conductorSubspace Q₀ N) +
        Module.finrank ℝ ↥((conductorSubspace Q₀ N)ᗮ) := by
    calc
      Module.finrank ℝ ↥(U ⊔ (conductorSubspace Q₀ N)ᗮ) ≤
          Module.finrank ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)) :=
        Submodule.finrank_le _
      _ = Module.finrank ℝ (conductorSubspace Q₀ N) +
            Module.finrank ℝ ↥((conductorSubspace Q₀ N)ᗮ) :=
        (Submodule.finrank_add_finrank_orthogonal (conductorSubspace Q₀ N)).symm
  have hfin_eq := finrank_conductorSubspace_eq hN2 h2log
  rw [hgrass, hfin_eq] at hsup_le
  exact (Nat.le_of_add_le_add_right hsup_le).trans hQ₀_mono

/-! ## Section 6: Asymmetric Cross-Term Absorption (`K c^{11}`) and `O(c^{11})` Confinement -/

private theorem asymmetric_payment_coefficients_small
    {L H B c k J Cp Cn a K r : ℝ}
    (hL : 0 < L) (hH : 0 ≤ H) (hB : 0 ≤ B) (hc : 1 ≤ c)
    (hk : 0 < k) (hJ : 0 < J) (hCp : 0 < Cp) (hCn : 0 < Cn) (ha : 0 < a)
    (hr : 0 ≤ r) (hHk : H ≤ J * k) (hcut : K * c ^ 11 ≤ k)
    (hK : 128 * Cn / a ≤ K)
    (hsmall :
      64 * ((8 * Cp * J + 8 * Cp * J / a) + 16 * Cn * J / a + 1) *
        (H / L + c ^ 7 * (1 + B) / L + c ^ 11 * (1 + Real.log c) / L + c ^ 11 * r) ≤ 1) :
    Cp * H / (L * (k / 8)) + Cp * H / (L * (a * k / (8 * c ^ 7))) ≤ 1 / 64 ∧
    Cp * H ^ 2 / (L * (k / 8)) + Cp * H * B / (L * (a * k / (8 * c ^ 7))) ≤ 1 / 64 ∧
    Cn * (c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L + r)) /
      (a * k / (8 * c ^ 7)) ≤ 1 / 64 ∧
    Cn * (c ^ 4 + c ^ 2 * (1 + Real.log c)) / (a * k / (8 * c ^ 7)) ≤ 1 / 8 := by
  let e := H / L + c ^ 7 * (1 + B) / L + c ^ 11 * (1 + Real.log c) / L + c ^ 11 * r
  let A0 := 8 * Cp * J
  let A1 := 8 * Cp * J / a
  let A2 := 16 * Cn * J / a
  have hc0 := zero_lt_one.trans_le hc
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have he0 : 0 ≤ e := by dsimp only [e]; positivity
  have hA0 : 0 ≤ A0 := by dsimp only [A0]; positivity
  have hA1 : 0 ≤ A1 := by dsimp only [A1]; positivity
  have hA2 : 0 ≤ A2 := by dsimp only [A2]; positivity
  have heH : H / L ≤ e := by
    have hh : 0 ≤ c ^ 7 * (1 + B) / L + c ^ 11 * (1 + Real.log c) / L + c ^ 11 * r := by positivity
    dsimp only [e]; linarith only [hh]
  have heB : c ^ 7 * (1 + B) / L ≤ e := by
    have hh : 0 ≤ H / L + c ^ 11 * (1 + Real.log c) / L + c ^ 11 * r := by positivity
    dsimp only [e]; linarith only [hh]
  have heC : c ^ 11 * (1 + Real.log c) / L ≤ e := by
    have hh : 0 ≤ H / L + c ^ 7 * (1 + B) / L + c ^ 11 * r := by positivity
    dsimp only [e]; linarith only [hh]
  have heCr : c ^ 11 * ((1 + Real.log c) / L + r) ≤ e := by
    have hh : 0 ≤ H / L + c ^ 7 * (1 + B) / L := by positivity
    dsimp only [e]
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith only [hh]
  have hAe : (A0 + A1) * e ≤ 1 / 64 := by
    have hh : 0 ≤ (A2 + 1) * e := by positivity
    change 64 * ((A0 + A1) + A2 + 1) * e ≤ 1 at hsmall
    nlinarith only [hsmall, hh]
  have hA2e : A2 * e ≤ 1 / 64 := by
    have hh : 0 ≤ (A0 + A1 + 1) * e := by positivity
    change 64 * ((A0 + A1) + A2 + 1) * e ≤ 1 at hsmall
    nlinarith only [hsmall, hh]
  have hratio : H / k ≤ J := (div_le_iff₀ hk).mpr hHk
  have hc7 : 1 ≤ c ^ 7 := one_le_pow₀ hc
  have hone : 1 / L ≤ c ^ 7 * (1 + B) / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith only [hc7, mul_nonneg (pow_nonneg hc0.le 7) hB]
  have hcB : c ^ 7 / L ≤ c ^ 7 * (1 + B) / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith only [mul_nonneg (pow_nonneg hc0.le 7) hB]
  have hcb : c ^ 7 * B / L ≤ c ^ 7 * (1 + B) / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith only [pow_nonneg hc0.le 7]
  have hmass : Cp * H / (L * (k / 8)) + Cp * H / (L * (a * k / (8 * c ^ 7))) ≤
      (A0 + A1) * e := by
    have h0 := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 8 * Cp / L by positivity)
    have h1 := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 8 * Cp / a * c ^ 7 / L by positivity)
    have he0' := mul_le_mul_of_nonneg_left (hone.trans heB) hA0
    have he1' := mul_le_mul_of_nonneg_left (hcB.trans heB) hA1
    have hid : Cp * H / (L * (k / 8)) + Cp * H / (L * (a * k / (8 * c ^ 7))) =
        (H / k) * (8 * Cp / L) + (H / k) * (8 * Cp / a * c ^ 7 / L) := by
      field_simp [hL.ne', hk.ne', ha.ne', hc0.ne']
    rw [hid]
    dsimp only [A0, A1] at he0' he1' ⊢
    simp only [div_eq_mul_inv] at h0 h1 he0' he1' ⊢
    nlinarith only [h0, h1, he0', he1']
  have henergy : Cp * H ^ 2 / (L * (k / 8)) + Cp * H * B / (L * (a * k / (8 * c ^ 7))) ≤
      (A0 + A1) * e := by
    have h0 := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 8 * Cp * H / L by positivity)
    have h1 := mul_le_mul_of_nonneg_right hratio (show 0 ≤ 8 * Cp / a * c ^ 7 * B / L by positivity)
    have he0' := mul_le_mul_of_nonneg_left heH hA0
    have he1' := mul_le_mul_of_nonneg_left (hcb.trans heB) hA1
    have hid : Cp * H ^ 2 / (L * (k / 8)) + Cp * H * B / (L * (a * k / (8 * c ^ 7))) =
        (H / k) * (8 * Cp * H / L) + (H / k) * (8 * Cp / a * c ^ 7 * B / L) := by
      field_simp [hL.ne', hk.ne', ha.ne', hc0.ne']
    rw [hid]
    dsimp only [A0, A1] at he0' he1' ⊢
    simp only [div_eq_mul_inv] at h0 h1 he0' he1' ⊢
    nlinarith only [h0, h1, he0', he1']
  have hweighted : Cn * (c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L + r)) /
      (a * k / (8 * c ^ 7)) ≤ A2 * e := by
    have hc9 : c ^ 9 / L ≤ c ^ 11 * (1 + Real.log c) / L := by
      apply div_le_div_of_nonneg_right _ hL.le
      have hh : c ^ 9 ≤ c ^ 11 := pow_le_pow_right₀ hc (by norm_num)
      nlinarith only [hh, mul_nonneg (pow_nonneg hc0.le 11) hlc]
    have hsum : c ^ 9 / L + c ^ 11 * ((1 + Real.log c) / L + r) ≤ 2 * e := by
      linarith only [hc9.trans heC, heCr]
    have h0 := mul_le_mul_of_nonneg_right hratio
      (show 0 ≤ 8 * Cn / a * (c ^ 9 / L + c ^ 11 * ((1 + Real.log c) / L + r)) by positivity)
    have h1 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 8 * Cn * J / a by positivity)
    have hid : Cn * (c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L + r)) /
        (a * k / (8 * c ^ 7)) =
        (H / k) * (8 * Cn / a * (c ^ 9 / L + c ^ 11 * ((1 + Real.log c) / L + r))) := by
      field_simp [hL.ne', hk.ne', ha.ne', hc0.ne']
    rw [hid]
    dsimp only [A2]
    simp only [div_eq_mul_inv] at h0 h1 ⊢
    nlinarith only [h0, h1]
  have hplain : Cn * (c ^ 4 + c ^ 2 * (1 + Real.log c)) / (a * k / (8 * c ^ 7)) ≤ 1 / 8 := by
    have hl : 1 + Real.log c ≤ c := by linarith only [Real.log_le_sub_one_of_pos hc0]
    have hc34 : c ^ 3 ≤ c ^ 4 := pow_le_pow_right₀ hc (by norm_num)
    have hcoef : c ^ 4 + c ^ 2 * (1 + Real.log c) ≤ 2 * c ^ 4 := by
      have hh := mul_le_mul_of_nonneg_left hl (sq_nonneg c)
      nlinarith only [hh, hc34]
    have hK' : 128 * Cn ≤ K * a := (div_le_iff₀ ha).mp hK
    have h1 := mul_le_mul_of_nonneg_right hK' (pow_nonneg hc0.le 11)
    have h2 := mul_le_mul_of_nonneg_left hcut ha.le
    have hpay : 128 * Cn * c ^ 11 ≤ a * k := by nlinarith only [h1, h2]
    calc
      _ ≤ Cn * (2 * c ^ 4) / (a * k / (8 * c ^ 7)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hCn.le) (by positivity)
      _ = 16 * Cn * c ^ 11 / (a * k) := by
        field_simp [ha.ne', hk.ne', hc0.ne']; ring
      _ ≤ 1 / 8 := (div_le_iff₀ (mul_pos ha hk)).mpr (by linarith only [hpay])
  exact ⟨hmass.trans hAe, henergy.trans hAe, hweighted.trans hA2e, hplain⟩

/-- **Asymmetric cross-term absorption at `K c^{11} ≤ log R / D - 1`.**
Using `linearDefectCutoff c` lowers the conductor-gap requirement from `c^{16}` to `c^{11}`. -/
theorem exists_completeWeil_asymmetric_conductor_cross_absorbed :
    ∃ b K C : ℝ, 0 < b ∧ b ≤ 1 / 8 ∧ 0 < K ∧ 0 < C ∧
      ∀ {R N : ℕ} {c : ℝ}, 1 ≤ c → 2 ≤ R → R ^ 6 ≤ N →
        linearDefectCutoff c ≤ N → c / N ≤ 1 / 3 →
        R * R ≤ N / linearDefectCutoff c →
        18 * (1 + Real.log R) ≤ Real.log (N / linearDefectCutoff c : ℕ) →
        K * c ^ 11 ≤ Real.log R / explicitConductorCutoffConstant - 1 →
        terminalPacketCost R (N / linearDefectCutoff c) N /
          Real.log (N / linearDefectCutoff c : ℕ) ≤ b / (4 * c ^ 7) →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        C * ((1 + Real.log R) / Real.log N +
          c ^ 7 * (1 + terminalPacketCost R (N / linearDefectCutoff c) N) / Real.log N +
          c ^ 11 * (1 + Real.log c) / Real.log N +
          c ^ 11 * (R : ℝ) ^ 2 * (Real.log N / N)) ≤ 1 →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| -
          completeWeilEnergy tiltedUnitSpline c N w ≤
        (1 / 8 : ℝ) * primeAdjunctionMass R a +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  obtain ⟨b, K0, hb, hb8, hK0, hreserve⟩ := exists_completeWeilEnergy_asymmetric_two_region_reserve
  obtain ⟨Cp, Cn, hCp, hCn, hcross⟩ := exists_completeWeil_cross_le_split_mass_reserves
  let D := explicitConductorCutoffConstant
  let J := 1 + 2 * D
  let K := 1 + K0 + 128 * Cn / b
  let C := 64 * ((8 * Cp * J + 8 * Cp * J / b) + 16 * Cn * J / b + 1)
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hK1 : 1 ≤ K := by
    have hh : 0 ≤ 128 * Cn / b := by positivity
    dsimp only [K]; linarith only [hK0, hh]
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨b, K, C, hb, hb8, hK, hC, ?_⟩
  intro R N c hc hR hR6 hLN hwidth hRM hlogM hcut hleak hsize hsize_up hsmall a hu1 w hw
  let M := N / linearDefectCutoff c
  let L := Real.log N
  let H := 1 + Real.log R
  let B := terminalPacketCost R M N
  let k := Real.log R / D - 1
  let s := k / 8
  let t := b * k / (8 * c ^ 7)
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let A := ∑ m ∈ Icc 1 R, a m ^ 2
  let E := primeAdjunctionMass R a
  let G := ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2
  let U := ‖u‖ ^ 2
  let P := ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2
  let S := ∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2
  let pa := Cp * H / (L * s) + Cp * H / (L * t)
  let pe := Cp * H ^ 2 / (L * s) + Cp * H * B / (L * t)
  let ng := Cn * (c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L +
    (R : ℝ) ^ 2 * (L / N))) / t
  let nu := Cn * (c ^ 4 + c ^ 2 * (1 + Real.log c)) / t
  have hc0 := zero_lt_one.trans_le hc
  have hM2 : 2 ≤ M := by have hh := Nat.mul_le_mul hR hR; omega
  have hMN : M ≤ N := Nat.div_le_self N (linearDefectCutoff c)
  have hlogN : 18 * (1 + Real.log R) ≤ Real.log N := hlogM.trans
    (Real.log_le_log (by exact_mod_cast (show 0 < M by omega)) (by exact_mod_cast hMN))
  have hL : 0 < L := by dsimp only [L]; linarith only [hlogN, Real.log_natCast_nonneg R]
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hB : 0 ≤ B := terminalPacketCost_nonneg R hMN
  have hk1 : 1 ≤ k := by
    have hh : 1 ≤ K * c ^ 11 := by
      simpa only [one_mul] using mul_le_mul hK1 (one_le_pow₀ hc (n := 11)) zero_le_one hK.le
    exact hh.trans hcut
  have hk : 0 < k := zero_lt_one.trans_le hk1
  have hs : 0 < s := by dsimp only [s]; positivity
  have ht : 0 < t := by dsimp only [t]; positivity
  have hHk : H ≤ J * k := by
    have hid : Real.log R = D * (k + 1) := by
      dsimp only [k]; field_simp [hD.ne']; ring
    have hh := mul_le_mul_of_nonneg_left hk1 hD.le
    dsimp only [H, J]
    rw [hid]
    nlinarith only [hh, hk1]
  have hKplain : 128 * Cn / b ≤ K := by dsimp only [K]; linarith only [hK0]
  have hsmall' :
      64 * ((8 * Cp * J + 8 * Cp * J / b) + 16 * Cn * J / b + 1) *
        (H / L + c ^ 7 * (1 + B) / L + c ^ 11 * (1 + Real.log c) / L +
          c ^ 11 * ((R : ℝ) ^ 2 * (L / N))) ≤ 1 := by
    simpa only [C, H, L, B, M, mul_assoc] using hsmall
  obtain ⟨hpa, hpe, hng, hnu⟩ := asymmetric_payment_coefficients_small hL hH hB hc hk hJ hCp hCn hb
    (by positivity : 0 ≤ (R : ℝ) ^ 2 * (L / N)) hHk hcut hKplain hsmall'
  change pa ≤ 1 / 64 at hpa
  change pe ≤ 1 / 64 at hpe
  change ng ≤ 1 / 64 at hng
  change nu ≤ 1 / 8 at hnu
  have hcut0 : K0 * c ^ 9 ≤ k := by
    have hh : K0 ≤ K := by
      have hz : 0 ≤ 128 * Cn / b := by positivity
      dsimp only [K]; linarith only [hz]
    have hc911 : c ^ 9 ≤ c ^ 11 := pow_le_pow_right₀ hc (by norm_num)
    exact (mul_le_mul hh hc911 (pow_nonneg hc0.le 9) hK.le).trans hcut
  have hres := hreserve hc hR hLN hRM hlogM hcut0 hleak hw
  change k / 4 * P + b * k / (2 * c ^ 7) * S ≤ completeWeilEnergy tiltedUnitSpline c N w at hres
  have hsplit : ‖w‖ ^ 2 = P + S := by
    rw [← sum_primeHorizonExtension_sq]
    dsimp only [P, S]
    rw [Ioc_eq_Icc_sdiff_Icc M N, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hA : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hE : 0 ≤ E := primeAdjunctionMass_nonneg R a
  have hG0 : 0 ≤ G := sum_nonneg fun m _ => by have := Real.log_natCast_nonneg m; positivity
  have hU : 0 ≤ U := sq_nonneg ‖u‖
  have hAU : A ≤ 2 * U := by
    have hRR : R * R ≤ N := hRM.trans hMN
    have hh := (half_and_three_halves_riesz_of_log_le hR hRR hlogN a).1
    change (1 / 2 : ℝ) * A ≤ U at hh
    linarith only [hh]
  have hG : G ≤ A + E := by
    dsimp only [G, A, E, primeAdjunctionMass]
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro m _
    have hh := mul_nonneg (tameDifferent_nonneg m) (sq_nonneg (a m))
    nlinarith only [hh]
  have ht_s : t ≤ k / 8 := by
    have hb1 : b ≤ 1 := hb8.trans (by norm_num)
    have hbc : b ≤ c ^ 7 := hb1.trans (one_le_pow₀ hc)
    have hh := mul_le_mul_of_nonneg_right hbc hk.le
    dsimp only [t]
    apply (div_le_iff₀ (by positivity : 0 < 8 * c ^ 7)).mpr
    nlinarith only [hh]
  have hraw := hcross hR hR6 hMN hlogN hc hwidth hsize hsize_up a hu1 hw s t t hs ht ht
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
    Cp * (H * A + H ^ 2 * E) / (L * s) + Cp * (H * A + H * B * E) / (L * t) +
    Cn * ((c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L + (R : ℝ) ^ 2 * (L / N))) * G +
      (c ^ 4 + c ^ 2 * (1 + Real.log c)) * U) / t + s * P + t * S + t * ‖w‖ ^ 2 at hraw
  rw [hsplit] at hraw
  have hid : Cp * (H * A + H ^ 2 * E) / (L * s) + Cp * (H * A + H * B * E) / (L * t) +
      Cn * ((c ^ 2 * H / L + c ^ 4 * H * ((1 + Real.log c) / L + (R : ℝ) ^ 2 * (L / N))) * G +
        (c ^ 4 + c ^ 2 * (1 + Real.log c)) * U) / t + s * P + t * S + t * (P + S) =
      pa * A + pe * E + ng * G + nu * U + s * P + t * S + t * (P + S) := by
    dsimp only [pa, pe, ng, nu]
    ring
  have hc_factored :
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
        pa * A + pe * E + ng * G + nu * U + s * P + t * S + t * (P + S) := by
    rwa [hid] at hraw
  have hp_pay : (s + t) * P ≤ (k / 4) * P :=
    mul_le_mul_of_nonneg_right (by dsimp only [s]; linarith only [ht_s]) hP
  have hq_pay : (t + t) * S ≤ (b * k / (2 * c ^ 7)) * S := by
    refine mul_le_mul_of_nonneg_right ?_ hS
    have he : b * k / (2 * c ^ 7) = 4 * t := by
      dsimp only [t]
      field_simp [hc0.ne']
      ring
    rw [he]
    linarith only [ht]
  have h1 := mul_le_mul_of_nonneg_right hpa hA
  have h2 := mul_le_mul_of_nonneg_right hpe hE
  have h3 := mul_le_mul_of_nonneg_right hng hG0
  have h4 := mul_le_mul_of_nonneg_right hnu hU
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| -
    completeWeilEnergy tiltedUnitSpline c N w ≤ (1 / 8 : ℝ) * E + (1 / 4 : ℝ) * U
  linarith only [h1, h2, h3, h4, hp_pay, hq_pay, hres, hc_factored, hAU, hG, hE, hU]

private theorem hermitian_inner_add_eq_asymmetric {N : ℕ}
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin A (x + y), x + y⟫ =
      ⟪Matrix.toEuclideanLin A x, x⟫ + 2 * ⟪Matrix.toEuclideanLin A x, y⟫ +
        ⟪Matrix.toEuclideanLin A y, y⟫ := by
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) y x
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym,
    real_inner_comm y (Matrix.toEuclideanLin A x)]
  ring

private theorem sub_starProjection_mem_orthogonal_asymmetric {N : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    x - K.starProjection x ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [real_inner_comm]
  exact K.starProjection_inner_eq_zero x v hv

private theorem poleDefect_restrict_profile_asymmetric (M : ℕ) (x : ℕ → ℝ) :
    poleDefect M (primeHorizonExtension (horizonProfileVector x M)) = poleDefect M x := by
  have he (n : ℕ) (hn : n ∈ Icc 1 M) :
      primeHorizonExtension (horizonProfileVector x M) n = x n := by
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]; rfl
  unfold poleDefect
  refine sum_congr rfl fun m hm => sum_congr rfl fun t ht => ?_
  have hmt : m * t ∈ Icc 1 M := by
    refine mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hm).1 (mem_Icc.mp ht).1, ?_⟩
    have hh := (Nat.mul_le_mul_right m (mem_Icc.mp ht).2).trans (Nat.div_mul_le_self M m)
    simpa only [Nat.mul_comm] using hh
  rw [he (m * t) hmt, he m hm]

/-- **Prefix-localized `O(c^{11})` sublevel confinement with adjunction debit.**
For any unit vector `zHat ∈ (conductorSubspace Q₁ N)ᗮ` with `completeWeilEnergy ≤ E0`, the
asymmetric `(V_1)ᗮ` reserve simultaneously bounds `poleDefect (N / linearDefectCutoff c)` by
`O(c^9)` and the terminal squared mass `S` by `O(c^{16} / log N)`. Lifting the `O(c^9)` prefix
conductor approximation from `[1, M]` to `[1, N]` and enlarging the cutoff to `O(c^{11})`
produces `R'` with `log R' ≤ C_R c^{11} + log Q₁` and `3 / 4 ≤ ‖P_{R'} zHat‖ ^ 2`. -/
theorem exists_asymmetric_conductor_projection_with_adjunction_debit {E0 : ℝ} (hE0 : 0 < E0) :
    ∃ C_R K_S C_abs b : ℝ, 0 < C_R ∧ 0 < K_S ∧ 0 < C_abs ∧ 0 < b ∧
      ∀ {Q₁ N : ℕ} {c : ℝ},
        2 ≤ Q₁ → 1 ≤ c → linearDefectCutoff c ≤ N → c / N ≤ 1 / 3 →
        K_S * c ^ 16 / Real.log N ≤ 1 →
        (∀ {R' : ℕ}, Q₁ ≤ R' → Real.log R' ≤ C_R * c ^ 11 + Real.log Q₁ →
          R' ^ 6 ≤ N ∧ R' * R' ≤ N / linearDefectCutoff c ∧
          18 * (1 + Real.log R') ≤ Real.log (N / linearDefectCutoff c : ℕ) ∧
          terminalPacketCost R' (N / linearDefectCutoff c) N /
            Real.log (N / linearDefectCutoff c : ℕ) ≤ b / (4 * c ^ 7) ∧
          ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
          ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N ∧
          C_abs * ((1 + Real.log R') / Real.log N +
            c ^ 7 * (1 + terminalPacketCost R' (N / linearDefectCutoff c) N) / Real.log N +
            c ^ 11 * (1 + Real.log c) / Real.log N +
            c ^ 11 * (R' : ℝ) ^ 2 * (Real.log N / N)) ≤ 1) →
      ∀ {zHat : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        zHat ∈ (conductorSubspace Q₁ N)ᗮ → ‖zHat‖ = 1 →
        completeWeilEnergy tiltedUnitSpline c N zHat ≤ E0 →
      ∃ R' : ℕ, Q₁ ≤ R' ∧ Real.log R' ≤ C_R * c ^ 11 + Real.log Q₁ ∧
        ∃ a : ℕ → ℝ,
          (∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace Q₁ N)ᗮ ∧
          3 / 4 ≤ ‖∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ∧
          ‖∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N‖ ≤ 1 ∧
          completeWeilEnergy tiltedUnitSpline c N
            (∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N) -
              (1 / 8 : ℝ) * primeAdjunctionMass R' a ≤ E0 + 1 := by
  obtain ⟨a₀, C₀, C₁, ha₀, -, hC₀, hC₁, hprefix⟩ :=
    exists_completeWeilEnergy_asymmetric_prefix_terminal_reserve
  obtain ⟨b, K, C_abs, hb, hb8, hK, hC_abs, habsorb⟩ :=
    exists_completeWeil_asymmetric_conductor_cross_absorbed
  let K_pre := 2 * (C₀ + C₁ + E0)
  let K_S := 32 * (C₀ + C₁ + E0) / a₀
  have hK_pre : 0 < K_pre := by dsimp only [K_pre]; positivity
  have hK_S : 0 < K_S := by dsimp only [K_S]; positivity
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  let C_gap := D * (1 + K)
  have hC_gap : 0 < C_gap := by dsimp only [C_gap]; positivity
  let C_app := 256 * quadraticConfinementConstant * (K_pre + 1)
  have hC_app : 0 < C_app := by
    have := quadraticConfinementConstant_pos; dsimp only [C_app]; positivity
  let C_R := C_app + C_gap + 1
  have hC_R : 0 < C_R := by dsimp only [C_R]; positivity
  refine ⟨C_R, K_S, C_abs, b, hC_R, hK_S, hC_abs, hb, ?_⟩
  intro Q₁ N c hQ₁ hc1 hLN hw1 hKS_le hR'_conds zHat hz_orth hz_norm hz_energy
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc9 : 1 ≤ c ^ 9 := one_le_pow₀ hc1
  have hc11 : 1 ≤ c ^ 11 := one_le_pow₀ hc1
  have hc9_11 : c ^ 9 ≤ c ^ 11 := pow_le_pow_right₀ hc1 (by norm_num)
  let M := N / linearDefectCutoff c
  let x := primeHorizonExtension zHat
  let P := ∑ n ∈ Icc 1 M, x n ^ 2
  let S := ∑ n ∈ Ioc M N, x n ^ 2
  have hMN : M ≤ N := Nat.div_le_self N (linearDefectCutoff c)
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hPS1 : P + S = 1 := by
    have hsplit : ‖zHat‖ ^ 2 = P + S := by
      rw [← sum_primeHorizonExtension_sq]
      dsimp only [P, S, x]
      rw [Ioc_eq_Icc_sdiff_Icc M N, add_comm]
      exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
    rw [hz_norm, one_pow] at hsplit
    exact hsplit.symm
  have hP_le1 : P ≤ 1 := by linarith only [hPS1, hS0]
  have hS_le1 : S ≤ 1 := by linarith only [hPS1, hP0]
  have hz_orth1 : zHat ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hz_orth v (conductorSubspace_mono (by omega : 1 ≤ Q₁) N hv)
  have hraw := hprefix hc1 hLN hz_orth1
  have hrhs_c9 : C₀ * c ^ 9 * P + C₁ * c ^ 2 * S + E0 ≤ (C₀ + C₁ + E0) * c ^ 9 := by
    have hc29 : c ^ 2 ≤ c ^ 9 := pow_le_pow_right₀ hc1 (by norm_num)
    have h1 : C₀ * c ^ 9 * P ≤ C₀ * c ^ 9 :=
      mul_le_of_le_one_right (by positivity) hP_le1
    have h2 : C₁ * c ^ 2 * S ≤ C₁ * c ^ 9 :=
      (mul_le_of_le_one_right (by positivity) hS_le1).trans
        (mul_le_mul_of_nonneg_left hc29 hC₁.le)
    have h3 : E0 ≤ E0 * c ^ 9 := by nlinarith only [hE0, hc9]
    linarith only [h1, h2, h3]
  have hDN0 : 0 ≤ (a₀ / c ^ 7) * poleDefect N x :=
    mul_nonneg (by positivity) (poleDefect_nonneg N x)
  have hDM0 : 0 ≤ (1 / 2 : ℝ) * poleDefect M x :=
    mul_nonneg (by norm_num) (poleDefect_nonneg M x)
  have hN3 : 3 ≤ N := (linearDefectCutoff_bounds hc1).1.trans hLN
  have hLN_pos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogNS0 : 0 ≤ (a₀ / c ^ 7) * Real.log N * S := by positivity
  have hdefM_le : poleDefect M x ≤ K_pre * c ^ 9 := by
    have h1 : (1 / 2 : ℝ) * poleDefect M x ≤ (C₀ + C₁ + E0) * c ^ 9 := by
      linarith only [hraw, hz_energy, hrhs_c9, hDN0, hlogNS0]
    dsimp only [K_pre]
    linarith only [h1]
  have hS_small : S ≤ 1 / 32 := by
    have h1 : (a₀ / c ^ 7) * Real.log N * S ≤ (C₀ + C₁ + E0) * c ^ 9 := by
      linarith only [hraw, hz_energy, hrhs_c9, hDN0, hDM0]
    have h2 : S ≤ (1 / 32 : ℝ) * (K_S * c ^ 16 / Real.log N) := by
      rw [show (1 / 32 : ℝ) * (K_S * c ^ 16 / Real.log N) =
        ((C₀ + C₁ + E0) * c ^ 16) / (a₀ * Real.log N) by
          dsimp only [K_S]; field_simp [ha₀.ne', hLN_pos.ne']]
      rw [le_div_iff₀ (mul_pos ha₀ hLN_pos)]
      have hm := mul_le_mul_of_nonneg_right h1 (pow_nonneg hc0.le 7)
      have hlhs : (a₀ / c ^ 7) * Real.log N * S * c ^ 7 = S * (a₀ * Real.log N) := by
        field_simp [hc0.ne']
      have hrhs : (C₀ + C₁ + E0) * c ^ 9 * c ^ 7 = (C₀ + C₁ + E0) * c ^ 16 := by ring
      linarith only [hm, hlhs, hrhs]
    nlinarith only [h2, hKS_le]
  -- Prefix quadratic conductor confinement at tolerance `1 / 16`.
  obtain ⟨R₀, hR₀1, hR₀log, happ⟩ := exists_explicit_quadratic_conductor_projection
    (1 / 16) (by norm_num) (by norm_num) (K_pre * c ^ 9) (by positivity)
  have hR₀2 : 2 ≤ R₀ := by omega
  have hR₀bound : Real.log R₀ ≤ C_app * c ^ 11 := by
    have hK1 : K_pre * c ^ 9 + 1 ≤ (K_pre + 1) * c ^ 9 := by linarith only [hc9]
    calc
      Real.log R₀ ≤ quadraticConfinementConstant / (1 / 16 : ℝ) ^ 2 * (K_pre * c ^ 9 + 1) := hR₀log
      _ ≤ quadraticConfinementConstant / (1 / 16 : ℝ) ^ 2 * ((K_pre + 1) * c ^ 9) :=
        mul_le_mul_of_nonneg_left hK1 (by have := quadraticConfinementConstant_pos; positivity)
      _ = C_app * c ^ 9 := by dsimp only [C_app]; ring
      _ ≤ C_app * c ^ 11 := mul_le_mul_of_nonneg_left hc9_11 hC_app.le
  let G : ℕ := ⌈Real.exp (C_gap * c ^ 11)⌉₊
  have hXpos : 0 < C_gap * c ^ 11 := mul_pos hC_gap (pow_pos hc0 11)
  have hexp1 : 1 < Real.exp (C_gap * c ^ 11) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hXpos
  have hceil : Real.exp (C_gap * c ^ 11) ≤ (G : ℝ) := Nat.le_ceil _
  have hGpos : (0 : ℝ) < G := (zero_lt_one.trans hexp1).trans_le hceil
  have hGlow : C_gap * c ^ 11 ≤ Real.log G := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hceil
  have hGup : Real.log G ≤ C_gap * c ^ 11 + 1 := by
    have hceilUp : (G : ℝ) < Real.exp (C_gap * c ^ 11) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have hdouble : (G : ℝ) ≤ 2 * Real.exp (C_gap * c ^ 11) := by linarith only [hceilUp, hexp1]
    have hlog := Real.log_le_log hGpos hdouble
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hlog
    linarith only [hlog, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  let R := max R₀ G
  let R' := max R Q₁
  have hQR' : Q₁ ≤ R' := le_max_right _ _
  have hR₀R' : R₀ ≤ R' := (le_max_left R₀ G).trans (le_max_left R Q₁)
  have hGR' : G ≤ R' := (le_max_right R₀ G).trans (le_max_left R Q₁)
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have hRbound : Real.log R ≤ C_R * c ^ 11 := by
    rcases le_total R₀ G with hRG | hGR
    · rw [show R = G from max_eq_right hRG]
      dsimp only [C_R]; nlinarith only [hGup, hc11, hC_app, pow_nonneg hc0.le 11]
    · rw [show R = R₀ from max_eq_left hGR]
      dsimp only [C_R]; nlinarith only [hR₀bound, hC_gap, pow_nonneg hc0.le 11]
  have hR'_log : Real.log R' ≤ C_R * c ^ 11 + Real.log Q₁ := by
    have hQlog := Real.log_natCast_nonneg Q₁
    have hCr : 0 ≤ C_R * c ^ 11 := by positivity
    rcases le_total R Q₁ with hRQ | hQR
    · rw [show R' = Q₁ from max_eq_right hRQ]; linarith only [hCr]
    · rw [show R' = R from max_eq_left hQR]; linarith only [hRbound, hQlog]
  have hgapLog : C_gap * c ^ 11 ≤ Real.log R' :=
    hGlow.trans (Real.log_le_log hGpos (by exact_mod_cast hGR'))
  obtain ⟨hR6N, hRM, hlogM, hleak, hRNT_lin, hRNT_up, hsmall⟩ :=
    hR'_conds hQR' hR'_log
  have hM2 : 2 ≤ M := (by norm_num : 2 ≤ 2 * 2).trans ((Nat.mul_le_mul hR'2 hR'2).trans hRM)
  have hLM_pos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  -- Lift the prefix conductor projection `p₀ ∈ V_{R₀}(M)` to `p_N ∈ V_{R₀}(N) ≤ V_{R'}(N)`.
  let y_M := horizonProfileVector x M
  have hyM_sq : ‖y_M‖ ^ 2 = P := horizonProfileVector_norm_sq x M
  have hyM_le1 : ‖y_M‖ ≤ 1 := by
    have hh : ‖y_M‖ ^ 2 ≤ 1 := hyM_sq.trans_le hP_le1
    nlinarith only [hh, norm_nonneg y_M]
  have hdef_yM : poleDefect M (primeHorizonExtension y_M) ≤ K_pre * c ^ 9 := by
    rw [poleDefect_restrict_profile_asymmetric]
    exact hdefM_le
  let p₀ := (conductorSubspace R₀ M).starProjection y_M
  have hp₀_err : ‖y_M - p₀‖ ^ 2 ≤ 1 / 16 := happ M hM2 y_M hyM_le1 hdef_yM
  have hp₀_sq_le1 : ‖p₀‖ ^ 2 ≤ 1 := by
    have hpy := norm_starProjection_sq_add_sub_sq (conductorSubspace R₀ M) y_M
    change ‖p₀‖ ^ 2 + ‖y_M - p₀‖ ^ 2 = ‖y_M‖ ^ 2 at hpy
    linarith only [hpy, sq_nonneg ‖y_M - p₀‖, hyM_sq, hP_le1]
  obtain ⟨b₀, -, hb₀_eq⟩ := (mem_conductorSubspace_iff (M := R₀) (N := M) (x := p₀)).mp
    ((conductorSubspace R₀ M).starProjection_apply_mem y_M)
  have hR₀M : R₀ * R₀ ≤ M := (Nat.mul_le_mul hR₀R' hR₀R').trans hRM
  have hlogR₀M : 18 * (1 + Real.log R₀) ≤ Real.log M := by
    have hlog_mono : Real.log R₀ ≤ Real.log R' :=
      Real.log_le_log (by exact_mod_cast (show 0 < R₀ by omega)) (by exact_mod_cast hR₀R')
    linarith only [hlog_mono, hlogM]
  have hb₀_sum : (∑ m ∈ Icc 1 R₀, b₀ m ^ 2) ≤ 2 := by
    have hr := (half_and_three_halves_riesz_of_log_le hR₀2 hR₀M hlogR₀M b₀).1
    rw [← hb₀_eq] at hr
    linarith only [hr, hp₀_sq_le1]
  let b_N : ℕ → ℝ := fun m => Real.sqrt (Real.log N / Real.log M) * b₀ m
  let p_N := ∑ m ∈ Icc 1 R₀, b_N m • normalizedRamanujanHorizonVector m N
  have hpN_mem : p_N ∈ conductorSubspace R' N :=
    conductorSubspace_mono hR₀R' N (sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R₀ N b_N)
  have hpN_coord : ∀ n : PrimeHorizonIndex N,
      p_N n = (Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n.1 := by
    intro n
    have hp := congrArg (fun v : EuclideanSpace ℝ (PrimeHorizonIndex N) => v n)
      (normalizedRamanujanPacketVector_eq_smul_profile (Icc 1 R₀) b_N N)
    dsimp only [normalizedRamanujanPacketVector, p_N] at hp ⊢
    rw [hp]
    change (Real.sqrt (Real.log N))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b_N n.1 = _
    have hprof : ramanujanPacketProfile (Icc 1 R₀) b_N n.1 =
        Real.sqrt (Real.log N / Real.log M) * ramanujanPacketProfile (Icc 1 R₀) b₀ n.1 := by
      unfold ramanujanPacketProfile
      dsimp only [b_N]
      rw [mul_sum]
      exact sum_congr rfl fun m _ => by ring
    rw [hprof, Real.sqrt_div hLN_pos.le]
    have hsN : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hLN_pos).ne'
    have hsM : Real.sqrt (Real.log M) ≠ 0 := (Real.sqrt_pos.mpr hLM_pos).ne'
    field_simp [hsN, hsM]
  have hp₀_coord : ∀ n : PrimeHorizonIndex M,
      p₀ n = (Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n.1 := by
    intro n
    rw [hb₀_eq]
    have hp := congrArg (fun v : EuclideanSpace ℝ (PrimeHorizonIndex M) => v n)
      (normalizedRamanujanPacketVector_eq_smul_profile (Icc 1 R₀) b₀ M)
    dsimp only [normalizedRamanujanPacketVector] at hp
    exact hp
  have hz_sub_pN_sq : ‖zHat - p_N‖ ^ 2 ≤ 1 / 4 := by
    rw [← sum_primeHorizonExtension_sq (zHat - p_N)]
    have hrew : (∑ n ∈ Icc 1 N, primeHorizonExtension (zHat - p_N) n ^ 2) =
        ∑ n ∈ Icc 1 N,
          (x n - (Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n) ^ 2 := by
      refine sum_congr rfl fun n hn => ?_
      congr 1
      rw [primeHorizonExtension_coe (zHat - p_N) ⟨n, hn⟩,
        show (zHat - p_N) ⟨n, hn⟩ = zHat ⟨n, hn⟩ - p_N ⟨n, hn⟩ from rfl,
        ← primeHorizonExtension_coe zHat ⟨n, hn⟩, hpN_coord ⟨n, hn⟩]
    rw [hrew]
    have hpart : (∑ n ∈ Icc 1 N,
        (x n - (Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n) ^ 2) =
        (∑ n ∈ Icc 1 M,
          (x n - (Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n) ^ 2) +
        (∑ n ∈ Ioc M N,
          (x n - (Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n) ^ 2) := by
      rw [Ioc_eq_Icc_sdiff_Icc M N, add_comm]
      exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm
    rw [hpart]
    have hpre_eq : (∑ n ∈ Icc 1 M,
        (x n - (Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n) ^ 2) =
        ‖y_M - p₀‖ ^ 2 := by
      rw [← sum_primeHorizonExtension_sq (y_M - p₀)]
      refine sum_congr rfl fun n hn => ?_
      congr 1
      rw [primeHorizonExtension_coe (y_M - p₀) ⟨n, hn⟩,
        show (y_M - p₀) ⟨n, hn⟩ = y_M ⟨n, hn⟩ - p₀ ⟨n, hn⟩ from rfl,
        hp₀_coord ⟨n, hn⟩]
      rfl
    have htail_pt : ∀ n ∈ Ioc M N,
        (x n - (Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n) ^ 2 ≤
          2 * x n ^ 2 + 2 * (Real.log M)⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n ^ 2 := by
      intro n _
      have hu : (x n - (Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n) ^ 2 ≤
          2 * x n ^ 2 +
            2 * ((Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n) ^ 2 := by
        nlinarith only [sq_nonneg
          (x n + (Real.sqrt (Real.log M))⁻¹ * ramanujanPacketProfile (Icc 1 R₀) b₀ n)]
      refine hu.trans_eq ?_
      rw [mul_pow, inv_pow, Real.sq_sqrt hLM_pos.le]
      ring
    have htail_sum := sum_le_sum htail_pt
    simp only [sum_add_distrib, ← mul_sum] at htail_sum
    have hprof_sq : ∀ n : ℕ, ramanujanPacketProfile (Icc 1 R₀) b₀ n ^ 2 =
        normalizedConductorPacket R₀ b₀ n ^ 2 / (n : ℝ) := by
      intro n
      have he : ramanujanPacketProfile (Icc 1 R₀) b₀ n =
          normalizedConductorPacket R₀ b₀ n / Real.sqrt n := by
        dsimp only [ramanujanPacketProfile, normalizedConductorPacket, ramanujanPoleProfile]
        rw [sum_div]
        exact sum_congr rfl fun m _ => by ring
      rw [he, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    have hgram_term : (∑ n ∈ Ioc M N, ramanujanPacketProfile (Icc 1 R₀) b₀ n ^ 2) ≤
        terminalPacketCost R' M N * 2 := by
      simp_rw [hprof_sq]
      have h1 := harmonicConductorPacket_terminal_le hR₀2 hMN b₀
      have hmono : terminalPacketCost R₀ M N ≤ terminalPacketCost R' M N := by
        unfold terminalPacketCost
        have hsq : (R₀ : ℝ) ^ 2 ≤ (R' : ℝ) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg R₀) (by exact_mod_cast hR₀R') 2
        have hdiv : 2 * (R₀ : ℝ) ^ 2 / ((M : ℝ) + 1) ≤ 2 * (R' : ℝ) ^ 2 / ((M : ℝ) + 1) :=
          div_le_div_of_nonneg_right (by linarith only [hsq]) (by positivity)
        linarith only [hdiv]
      calc
        _ ≤ terminalPacketCost R₀ M N * ∑ m ∈ Icc 1 R₀, b₀ m ^ 2 := h1
        _ ≤ terminalPacketCost R' M N * 2 :=
          mul_le_mul hmono hb₀_sum (sum_nonneg fun _ _ => sq_nonneg _)
            (terminalPacketCost_nonneg R' hMN)
    have hterm_le_eighth : 2 * (Real.log M)⁻¹ *
        (∑ n ∈ Ioc M N, ramanujanPacketProfile (Icc 1 R₀) b₀ n ^ 2) ≤ 1 / 8 := by
      have h1 := mul_le_mul_of_nonneg_left hgram_term (show 0 ≤ 2 * (Real.log M)⁻¹ by positivity)
      have heq : 2 * (Real.log M)⁻¹ * (terminalPacketCost R' M N * 2) =
          4 * (terminalPacketCost R' M N / Real.log M) := by ring
      rw [heq] at h1
      have hc7 : (1 : ℝ) ≤ c ^ 7 := one_le_pow₀ hc1
      have hb_le : 4 * (b / (4 * c ^ 7)) ≤ 1 / 8 := by
        have hdiv : b / c ^ 7 ≤ b := div_le_self hb.le hc7
        have he : 4 * (b / (4 * c ^ 7)) = b / c ^ 7 := by field_simp [hc0.ne']
        linarith only [he, hdiv, hb8]
      exact h1.trans ((mul_le_mul_of_nonneg_left hleak (by norm_num)).trans hb_le)
    rw [hpre_eq]
    change ‖y_M - p₀‖ ^ 2 + _ ≤ 1 / 4
    change _ ≤ 2 * S + _ at htail_sum
    linarith only [hp₀_err, htail_sum, hS_small, hterm_le_eighth]
  -- Complete cross-term absorption on `u = P_{R'} zHat` and `w = zHat - u`.
  let u := (conductorSubspace R' N).starProjection zHat
  let w := zHat - u
  have hu_mem : u ∈ conductorSubspace R' N :=
    (conductorSubspace R' N).starProjection_apply_mem zHat
  have hu_orthQ : u ∈ (conductorSubspace Q₁ N)ᗮ :=
    starProjection_mem_orthogonal_of_le (conductorSubspace_mono hQR' N) hz_orth
  have hu_orth1 : u ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu_orthQ v (conductorSubspace_mono (by omega : 1 ≤ Q₁) N hv)
  have hw_orth : w ∈ (conductorSubspace R' N)ᗮ :=
    sub_starProjection_mem_orthogonal_asymmetric _ zHat
  have hw_sq : ‖w‖ ^ 2 ≤ 1 / 4 :=
    (norm_sub_starProjection_sq_le (conductorSubspace R' N) zHat p_N hpN_mem).trans hz_sub_pN_sq
  have hpyth := norm_starProjection_sq_add_sub_sq (conductorSubspace R' N) zHat
  change ‖u‖ ^ 2 + ‖w‖ ^ 2 = ‖zHat‖ ^ 2 at hpyth
  rw [hz_norm, one_pow] at hpyth
  have hu_sq_ge : 3 / 4 ≤ ‖u‖ ^ 2 := by linarith only [hpyth, hw_sq]
  have hu_le1 : ‖u‖ ≤ 1 := by nlinarith only [hpyth, sq_nonneg ‖w‖, norm_nonneg u]
  have hgap : K * c ^ 11 ≤ Real.log R' / D - 1 := by
    have hh : (1 + K) * c ^ 11 ≤ Real.log R' / D := by
      apply (le_div_iff₀ hD).mpr
      exact (show ((1 + K) * c ^ 11) * D = C_gap * c ^ 11 by
        dsimp only [C_gap]; ring).trans_le hgapLog
    linarith only [hh, hc11]
  obtain ⟨a, -, ha⟩ := (mem_conductorSubspace_iff (x := u)).mp hu_mem
  have hpay := habsorb hc1 hR'2 hR6N hLN hw1 hRM hlogM hgap hleak hRNT_lin hRNT_up hsmall
    a (ha ▸ hu_orth1) hw_orth
  rw [← ha] at hpay
  have hu_sq_le1 : ‖u‖ ^ 2 ≤ 1 := by nlinarith only [hu_le1, norm_nonneg u]
  have htail : 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| -
      completeWeilEnergy tiltedUnitSpline c N w ≤
        (1 / 8 : ℝ) * primeAdjunctionMass R' a + 1 / 4 := by
    linarith only [hpay, hu_sq_le1]
  have hu_energy : completeWeilEnergy tiltedUnitSpline c N u -
      (1 / 8 : ℝ) * primeAdjunctionMass R' a ≤ E0 + 1 := by
    have hz_split : zHat = u + w := by dsimp only [w]; abel
    have hexp := hermitian_inner_add_eq_asymmetric
      (completeWeilMatrix_isHermitian tiltedUnitSpline c N) u w
    change completeWeilEnergy tiltedUnitSpline c N (u + w) =
      completeWeilEnergy tiltedUnitSpline c N u +
        2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫ +
        completeWeilEnergy tiltedUnitSpline c N w at hexp
    rw [← hz_split] at hexp
    linarith only [hexp, hz_energy, htail,
      neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫]
  refine ⟨R', hQR', hR'_log, a, ?_⟩
  rw [← ha]
  exact ⟨hu_orthQ, hu_sq_ge, hu_le1, hu_energy⟩

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeilEnergy_asymmetric_prefix_terminal_reserve
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeilEnergy_asymmetric_two_region_reserve
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal_below_one_ninth
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeil_global_negIndex_le_polynomialConductor_below_one_ninth
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_asymmetric_conductor_cross_absorbed
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_asymmetric_conductor_projection_with_adjunction_debit



