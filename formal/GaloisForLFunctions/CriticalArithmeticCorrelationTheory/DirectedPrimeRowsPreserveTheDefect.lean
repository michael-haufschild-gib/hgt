import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheArchimedeanCrossEnergyIsOneSided
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeDefectHasFiniteRamanujanApproximation

/-!
# Directed prime rows preserve the defect at bounded overlap

The upward non-ratio rows have bounded mass, while the downward rows carry a
logarithmic weight paid by the prime-edge defect. Keeping these directions
separate in Young's inequality makes the actual non-ratio prime form
infinitesimally bounded relative to that defect at every bounded overlap.
All prime powers and both orientations remain in the source.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Finset Filter Topology RHTower

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics ArithmeticEffectivityTheory

private theorem directed_young (x y : ℝ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    2 * (|x| * |y|) ≤ x ^ 2 * (a / t) + y ^ 2 * (t / a) := by
  have hsq := sq_nonneg (|x| * a - t * |y|)
  have hmul : 2 * (|x| * |y|) * (a * t) ≤
      (x ^ 2 * (a / t) + y ^ 2 * (t / a)) * (a * t) := by
    field_simp [ha.ne', ht.ne']
    nlinarith only [hsq, sq_abs x, sq_abs y]
  exact le_of_mul_le_mul_right hmul (mul_pos ha ht)

/-- A directed Schur estimate assigns independent costs to incoming and outgoing rows. -/
theorem sum_abs_mul_directed_schur (N : ℕ) (x : ℕ → ℝ) (V : ℕ → ℕ → ℝ)
    (hV : ∀ m n, 0 ≤ V m n) {t : ℝ} (ht : 0 < t) :
    (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      |x m| * |x n| * (V m n + V n m)) ≤
      (∑ m ∈ Icc 1 N, x m ^ 2 *
        ((∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n) / t +
          t * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V n m)) := by
  have hpair : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
      2 * (|x m| * |x n|) * V m n ≤
        x m ^ 2 * (Real.sqrt ((m : ℝ) / n) * V m n) / t +
          t * (x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V m n)) := by
    intro m hm n hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have ha : 0 < Real.sqrt ((m : ℝ) / n) := Real.sqrt_pos.mpr (div_pos hm0 hn0)
    have hinv : Real.sqrt ((n : ℝ) / m) = (Real.sqrt ((m : ℝ) / n))⁻¹ := by
      rw [← Real.sqrt_inv, inv_div]
    have h := mul_le_mul_of_nonneg_right (directed_young (x m) (x n) ha ht) (hV m n)
    rw [hinv]
    convert h using 1 <;> ring
  have hswap : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * V n m) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * V m n := by
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
  calc
    _ = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, 2 * (|x m| * |x n|) * V m n := by
      simp only [mul_add, sum_add_distrib]
      rw [hswap, ← two_mul]
      simp only [mul_sum]
      exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
    _ ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (x m ^ 2 * (Real.sqrt ((m : ℝ) / n) * V m n) / t +
          t * (x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V m n))) :=
      sum_le_sum fun m hm => sum_le_sum fun n hn => hpair m hm n hn
    _ = _ := by
      simp only [sum_add_distrib]
      rw [sum_comm (f := fun m n : ℕ =>
        t * (x n ^ 2 * (Real.sqrt ((n : ℝ) / m) * V m n)))]
      simp only [← sum_add_distrib, mul_sum, sum_div]
      exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring

/-- The literal source, with an independent Young parameter on its two directed rows. -/
theorem abs_nonRatioForm_le_directed_rows {g : ℝ → ℝ} {w t : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (ht : 0 < t)
    (N : ℕ) (x : ℕ → ℝ) :
    |nonRatioForm g N x| ≤ (∫ u, g u ^ 2) *
      ∑ m ∈ Icc 1 N, x m ^ 2 *
        (2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N / t +
          t * (2 * Real.exp (w / 2) * m * (Real.exp w - 1) * (Real.log m + w))) := by
  let L := ⌈(N : ℝ) * Real.exp w⌉₊ + 1
  let G := ∫ u, g u ^ 2
  have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hfin : nonRatioForm g N x =
      ∑ k ∈ range L, vonMangoldtAtom k * nonRatioLag g N k x := by
    unfold nonRatioForm
    refine tsum_eq_sum fun k hk => ?_
    have hkL : L ≤ k := by simpa only [mem_range, not_lt] using hk
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [nonRatioLag]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hbig : (N : ℝ) * Real.exp w < k := by
      have hceil := Nat.le_ceil ((N : ℝ) * Real.exp w)
      have hkR : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by
        exact_mod_cast hkL
      push_cast at hkR
      linarith only [hceil, hkR]
    have hlog : Real.log N + w < Real.log k := by
      rw [← Real.log_exp w, ← Real.log_mul hN0.ne' (Real.exp_pos w).ne']
      exact Real.log_lt_log (by positivity) hbig
    rw [nonRatioLag_eq_zero_of_log_lt hsupp hw hlog, mul_zero]
  let V : ℕ → ℕ → ℝ := fun m n =>
    ∑ k ∈ range L, vonMangoldtAtom k * upInd w k m n
  have hV : ∀ m n, 0 ≤ V m n := fun m n =>
    sum_nonneg fun k _ => mul_nonneg (vonMangoldtAtom_nonneg' k) (upInd_nonneg _ _ _ _)
  have hsource : |nonRatioForm g N x| ≤
      G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * (V m n + V n m) := by
    rw [hfin]
    calc
      _ ≤ ∑ k ∈ range L, vonMangoldtAtom k *
          (G * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
            |x m| * |x n| * (upInd w k m n + upInd w k n m)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
        rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' k)]
        exact mul_le_mul_of_nonneg_left (abs_nonRatioLag_le hg hgc hsupp N k x)
          (vonMangoldtAtom_nonneg' k)
      _ = _ := by
        simp only [V, ← sum_add_distrib, mul_sum, ← mul_add]
        rw [sum_comm]
        exact sum_congr rfl fun m _ => by
          rw [sum_comm]
          exact sum_congr rfl fun n _ => sum_congr rfl fun k _ => by ring
  have hrow : ∀ m ∈ Icc 1 N,
      (∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n) / t +
        t * (∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V n m) ≤
      2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N / t +
        t * (2 * Real.exp (w / 2) * m * (Real.exp w - 1) * (Real.log m + w)) := by
    intro m hm
    have hup : (∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n) =
        ∑ k ∈ range L, vonMangoldtAtom k *
          ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k m n := by
      simp only [V, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun n _ => by ring
    have hdown : (∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V n m) =
        ∑ k ∈ range L, vonMangoldtAtom k *
          ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k n m := by
      simp only [V, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun k _ => sum_congr rfl fun n _ => by ring
    rw [hup, hdown]
    exact add_le_add
      (div_le_div_of_nonneg_right (up_row_le hw (mem_Icc.mp hm).1 L) ht.le)
      (mul_le_mul_of_nonneg_left (down_row_le hw (mem_Icc.mp hm).1 L) ht.le)
  exact hsource.trans ((mul_le_mul_of_nonneg_left
    (sum_abs_mul_directed_schur N x V hV ht) hG).trans
      (mul_le_mul_of_nonneg_left (sum_le_sum fun m hm =>
        mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _)) hG))

/-- Chebyshev's cost for the outgoing non-ratio rows at unit overlap. -/
def nonRatioUpConstant : ℝ := 2 * (Real.log 4 + 4) * Real.exp (5 / 2)

/-- The divisor-identity cost for incoming non-ratio rows at unit overlap. -/
def nonRatioDownConstant : ℝ := 2 * Real.exp (3 / 2)

theorem nonRatioUpConstant_pos : 0 < nonRatioUpConstant := by
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  unfold nonRatioUpConstant
  positivity

theorem nonRatioDownConstant_pos : 0 < nonRatioDownConstant := by
  unfold nonRatioDownConstant
  positivity

private theorem directed_row_bounds {w K : ℝ} {N m : ℕ}
    (hN : 1 ≤ N) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hwK : w ≤ K / N) (hm : 1 ≤ m) :
    2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N ≤
        nonRatioUpConstant * K ∧
      2 * Real.exp (w / 2) * m * (Real.exp w - 1) * (Real.log m + w) ≤
        nonRatioDownConstant * K * ((m : ℝ) / N) * (Real.log m + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hK : 0 ≤ K := by
    have h := (le_div_iff₀ hN0).mp hwK
    exact (mul_nonneg hw0 hN0.le).trans h
  have hew : Real.exp w - 1 ≤ K / N * Real.exp w :=
    (exp_sub_one_le_mul_exp (w := w)).trans
      (mul_le_mul_of_nonneg_right hwK (Real.exp_pos _).le)
  have hup : (Real.exp w - 1) * N ≤ K * Real.exp w := by
    calc
      _ ≤ (K / N * Real.exp w) * N :=
        mul_le_mul_of_nonneg_right hew hN0.le
      _ = _ := by field_simp
  have hdown : (Real.exp w - 1) * m ≤ K * Real.exp w * ((m : ℝ) / N) := by
    calc
      _ ≤ (K / N * Real.exp w) * m :=
        mul_le_mul_of_nonneg_right hew hm0.le
      _ = _ := by ring
  have e1 : Real.exp (3 * w / 2) * Real.exp w ≤ Real.exp (5 / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hw1])
  have e2 : Real.exp (w / 2) * Real.exp w ≤ Real.exp (3 / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hw1])
  have hlog4 : 0 ≤ Real.log 4 + 4 := by
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith only [hlog]
  constructor
  · calc
      _ = 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) *
          ((Real.exp w - 1) * N) := by ring
      _ ≤ 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (K * Real.exp w) :=
        mul_le_mul_of_nonneg_left hup (by positivity)
      _ = 2 * (Real.log 4 + 4) * K * (Real.exp (3 * w / 2) * Real.exp w) := by ring
      _ ≤ 2 * (Real.log 4 + 4) * K * Real.exp (5 / 2) :=
        mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = _ := by unfold nonRatioUpConstant; ring
  · have hlm : 0 ≤ Real.log m + w := add_nonneg (Real.log_natCast_nonneg m) hw0
    calc
      _ = 2 * Real.exp (w / 2) * ((Real.exp w - 1) * m) * (Real.log m + w) := by ring
      _ ≤ 2 * Real.exp (w / 2) * (K * Real.exp w * ((m : ℝ) / N)) * (Real.log m + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hdown (by positivity))
          (by linarith only [hw1]) hlm (by positivity)
      _ = 2 * K * ((m : ℝ) / N) * (Real.log m + 1) *
          (Real.exp (w / 2) * Real.exp w) := by ring
      _ ≤ 2 * K * ((m : ℝ) / N) * (Real.log m + 1) * Real.exp (3 / 2) :=
        mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by unfold nonRatioDownConstant; ring

/-- At arbitrary bounded overlap, incoming rows cost defect and outgoing rows cost mass. -/
theorem abs_nonRatioForm_le_defect_young {g : ℝ → ℝ} {w K t : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ht : 0 < t)
    {N : ℕ} (hN : 1 ≤ N) (hwK : w ≤ K / N) (x : ℕ → ℝ) :
    |nonRatioForm g N x| ≤ (∫ u, g u ^ 2) *
      (2 * t * nonRatioDownConstant * K * poleDefect N x +
        (nonRatioUpConstant * K / t +
          t * nonRatioDownConstant * K * (2 * psiConstant + 1)) *
            ∑ m ∈ Icc 1 N, x m ^ 2) := by
  let S := ∑ m ∈ Icc 1 N, x m ^ 2
  let T := ∑ m ∈ Icc 1 N, (m : ℝ) / N * Real.log m * x m ^ 2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 ≤ K := by
    have h := (le_div_iff₀ hN0).mp hwK
    exact (mul_nonneg hw0 hN0.le).trans h
  have hB : 0 ≤ nonRatioDownConstant * K :=
    mul_nonneg nonRatioDownConstant_pos.le hK
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hrows : (∑ m ∈ Icc 1 N, x m ^ 2 *
      (2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N / t +
        t * (2 * Real.exp (w / 2) * m * (Real.exp w - 1) * (Real.log m + w)))) ≤
      (nonRatioUpConstant * K / t) * S + t * nonRatioDownConstant * K * (T + S) := by
    calc
      _ ≤ ∑ m ∈ Icc 1 N, x m ^ 2 *
          (nonRatioUpConstant * K / t +
            t * (nonRatioDownConstant * K * (((m : ℝ) / N) * Real.log m + 1))) := by
        refine sum_le_sum fun m hm => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        obtain ⟨hu, hd⟩ := directed_row_bounds hN hw0 hw1 hwK (mem_Icc.mp hm).1
        have hmN : (m : ℝ) / N ≤ 1 :=
          (div_le_one hN0).mpr (by exact_mod_cast (mem_Icc.mp hm).2)
        refine add_le_add (div_le_div_of_nonneg_right hu ht.le)
          (mul_le_mul_of_nonneg_left (hd.trans ?_) ht.le)
        nlinarith only [mul_le_mul_of_nonneg_left hmN hB]
      _ = _ := by
        simp only [S, T, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun m _ => by ring
  have htop : T ≤ 2 * poleDefect N x + 2 * psiConstant * S := by
    simpa only [T, S, one_div_one, one_add_one_eq_two] using
      sum_top_le_poleDefect_param N x (show (0 : ℝ) < 1 by norm_num)
  have hcost : (nonRatioUpConstant * K / t) * S +
      t * nonRatioDownConstant * K * (T + S) ≤
      2 * t * nonRatioDownConstant * K * poleDefect N x +
        (nonRatioUpConstant * K / t + t * nonRatioDownConstant * K * (2 * psiConstant + 1)) * S := by
    have h := mul_le_mul_of_nonneg_left htop (mul_nonneg ht.le hB)
    nlinarith only [h]
  exact (abs_nonRatioForm_le_directed_rows hg hgc hsupp hw0 ht N x).trans
    (mul_le_mul_of_nonneg_left (hrows.trans hcost) hG)

/-- The mass price of an arbitrary positive relative-defect allowance.
The first term is `8(log 4+4)exp(4)K²/ε`. -/
def nonRatioRelativeCost (K ε : ℝ) : ℝ :=
  2 * nonRatioUpConstant * nonRatioDownConstant * K ^ 2 / ε +
    ε / 2 * (2 * psiConstant + 1)

/-- Every bounded-overlap non-ratio source is infinitesimally bounded by the actual prime defect. -/
theorem abs_nonRatioForm_le_relative_defect {g : ℝ → ℝ} {w K ε : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hK : 0 < K) (hε : 0 < ε)
    {N : ℕ} (hN : 1 ≤ N) (hwK : w ≤ K / N) (x : ℕ → ℝ) :
    |nonRatioForm g N x| ≤ (∫ u, g u ^ 2) *
      (ε * poleDefect N x + nonRatioRelativeCost K ε * ∑ m ∈ Icc 1 N, x m ^ 2) := by
  let t := ε / (2 * nonRatioDownConstant * K)
  have hB := nonRatioDownConstant_pos
  have ht : 0 < t := div_pos hε (by positivity)
  have h := abs_nonRatioForm_le_defect_young hg hgc hsupp hw0 hw1 ht hN hwK x
  have heq : 2 * t * nonRatioDownConstant * K = ε := by
    dsimp only [t]
    field_simp [nonRatioDownConstant_pos.ne', hK.ne']
  have hcost : nonRatioUpConstant * K / t +
      t * nonRatioDownConstant * K * (2 * psiConstant + 1) = nonRatioRelativeCost K ε := by
    dsimp only [t, nonRatioRelativeCost]
    field_simp [nonRatioDownConstant_pos.ne', hK.ne', hε.ne']
    ring
  rwa [heq, hcost] at h

/-- The actual overlapping prime form, normalized by atom mass and with its logarithmic
coefficient divergence removed. -/
def overlapPrimeEnergy (g : ℝ → ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  Real.log N * (∑ n ∈ Icc 1 N, x n ^ 2) -
    primeSum (atomicTest N x g) / (∫ u, g u ^ 2)

/-- At every bounded overlap, the actual prime source retains half the prime-edge reserve.
The horizon is uniform over widths, profiles, and signed coefficient vectors. -/
theorem eventually_overlapPrimeEnergy_ge_defect {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, ∀ w : ℝ, 0 ≤ w → w ≤ 1 → w ≤ K / N →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      (∀ u, u ∉ Set.Icc 0 w → g u = 0) → 0 < ∫ u, g u ^ 2 →
      ∀ x : ℕ → ℝ,
        poleDefect N x / 2 +
          (Real.eulerMascheroniConstant - 1 / 4 - nonRatioRelativeCost K (1 / 4)) *
            (∑ n ∈ Icc 1 N, x n ^ 2) ≤ overlapPrimeEnergy g N x := by
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_add_poleDefect_le
    (show (0 : ℝ) < 1 / 4 by norm_num)
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 1]
    with N hN₀' hN w hw0 hw1 hwK g hg hgc hsupp hG x
  have hr := hN₀ N hN₀' x
  have hn := (div_le_iff₀ hG).mpr (by
    simpa only [mul_comm (∫ u, g u ^ 2)] using
      abs_nonRatioForm_le_relative_defect hg hgc hsupp hw0 hw1 hK
        (show (0 : ℝ) < 1 / 4 by norm_num) hN hwK x)
  have hnr := (div_le_div_of_nonneg_right (le_abs_self (nonRatioForm g N x)) hG.le).trans hn
  have heq : primeSum (atomicTest N x g) / (∫ u, g u ^ 2) =
      atomicWeilForm N x + nonRatioForm g N x / (∫ u, g u ^ 2) := by
    rw [primeSum_atomicTest_eq_ratio_add hg hgc hsupp hw0]
    field_simp [hG.ne']
  unfold overlapPrimeEnergy
  rw [heq]
  linarith only [hr, hnr]

/-- Bounded actual prime energy at bounded overlap has uniformly finite arithmetic coordinates. -/
theorem exists_ramanujan_approximation_of_overlapPrimeEnergy_le {K : ℝ} (hK : 0 < K)
    (T : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ w : ℝ, 0 ≤ w → w ≤ 1 → w ≤ K / N →
        ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
        (∀ u, u ∉ Set.Icc 0 w → g u = 0) → 0 < ∫ u, g u ^ 2 →
        ∀ x : ℕ → ℝ, (∑ n ∈ Icc 1 N, x n ^ 2) = 1 → overlapPrimeEnergy g N x ≤ T →
          ∃ a : ℕ → ℝ,
            (∑ n ∈ Icc 1 N,
              (x n - ∑ m ∈ S, a m * ramanujanPoleProfile m n) ^ 2) ≤ η := by
  let B := 2 * (T - Real.eulerMascheroniConstant + 1 / 4 + nonRatioRelativeCost K (1 / 4))
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le B hη
  refine ⟨S, hS, ?_⟩
  filter_upwards [eventually_overlapPrimeEnergy_ge_defect hK] with N hN
  intro w hw0 hw1 hwK g hg hgc hsupp hG x hx henergy
  have h := hN w hw0 hw1 hwK g hg hgc hsupp hG x
  rw [hx, mul_one] at h
  apply happ N x hx.le
  dsimp only [B]
  linarith only [h, henergy]

#print axioms abs_nonRatioForm_le_relative_defect
#print axioms eventually_overlapPrimeEnergy_ge_defect
#print axioms exists_ramanujan_approximation_of_overlapPrimeEnergy_le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
