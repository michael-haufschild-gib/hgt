import GaloisForLFunctions.BezoutValuationIncidence.UniformTruncatedMobiusReceiversHaveZeroTrivialDensity
import GaloisForLFunctions.RHTower.MobiusTwoJetLinearDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform logarithmic pronic energy from prefix cancellation

A square-root split separates the finite head from a uniform logarithmic
prefix estimate. Every logarithmic saving survives in the pronic norm,
with constants independent of the family index.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A common linear bound pays the finite head of an eventual common smooth-power bound. -/
theorem exists_uniform_rpow_bound_of_eventually {ι : Type*} {f : ι → ℕ → ℝ}
    {ε A B : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlinear : ∀ i n, 1 ≤ n → |f i n| ≤ A * n)
    (hevent : ∀ᶠ n : ℕ in atTop, ∀ i, |f i n| ≤ B * (n : ℝ) ^ (1 - ε)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i n, 1 ≤ n → |f i n| ≤ K * (n : ℝ) ^ (1 - ε) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨B + A * (N₀ : ℝ) ^ ε, by positivity, fun i n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hN : N₀ ≤ n
  · exact (hN₀ n hN i).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
        (Real.rpow_nonneg hn0.le _))
  · have hpow : (n : ℝ) ^ ε ≤ (N₀ : ℝ) ^ ε :=
      Real.rpow_le_rpow hn0.le (by exact_mod_cast (lt_of_not_ge hN).le) hε
    have heq : (n : ℝ) = (n : ℝ) ^ ε * (n : ℝ) ^ (1 - ε) := by
      rw [← Real.rpow_add hn0, show ε + (1 - ε) = 1 by ring, Real.rpow_one]
    calc
      _ ≤ A * n := hlinear i n hn
      _ = A * ((n : ℝ) ^ ε * (n : ℝ) ^ (1 - ε)) := congrArg (fun x : ℝ => A * x) heq
      _ = (A * (n : ℝ) ^ ε) * (n : ℝ) ^ (1 - ε) := by ring
      _ ≤ (A * (N₀ : ℝ) ^ ε) * (n : ℝ) ^ (1 - ε) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hA)
          (Real.rpow_nonneg hn0.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB)
        (Real.rpow_nonneg hn0.le _)

/-- Splitting a common prefix estimate separates its finite-head and tail energy constants. -/
theorem sum_pronicCell_le_of_split_rpow {f : ℕ → ℝ} {ε K L : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (D T : ℕ)
    (hglobal : ∀ n, 1 ≤ n → |f n| ≤ K * (n : ℝ) ^ (1 - ε))
    (hlate : ∀ n, 1 ≤ n → D ≤ n → |f n| ≤ L * (n : ℝ) ^ (1 - ε)) :
    (∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      K ^ 2 * (1 + (D : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) +
        L ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
  have hcell (n : ℕ) (hn : n ∈ Icc 1 T) :
      f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        (if n < D then K ^ 2 * (n : ℝ) ^ (-(2 * ε)) else 0) +
          L ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by
    have hn1 := (mem_Icc.mp hn).1
    split_ifs with h
    · exact (cell_le_of_abs_le_rpow hn1 (hglobal n hn1)).trans
        (le_add_of_nonneg_right (by positivity))
    · rw [zero_add]
      exact cell_le_of_abs_le_rpow hn1 (hlate n hn1 (not_lt.mp h))
  calc
    _ ≤ ∑ n ∈ Icc 1 T,
        ((if n < D then K ^ 2 * (n : ℝ) ^ (-(2 * ε)) else 0) +
          L ^ 2 * (n : ℝ) ^ (-(2 * ε))) := sum_le_sum hcell
    _ = (∑ n ∈ Icc 1 T with n < D, K ^ 2 * (n : ℝ) ^ (-(2 * ε))) +
        L ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * ε)) := by
      rw [sum_add_distrib, mul_sum, sum_filter]
    _ ≤ (∑ n ∈ Icc 1 D, K ^ 2 * (n : ℝ) ^ (-(2 * ε))) +
        L ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * ε)) := by
      refine add_le_add ?_ le_rfl
      exact sum_le_sum_of_subset_of_nonneg (fun n hn => by
        simp only [mem_filter, mem_Icc] at hn ⊢
        omega) (fun n _ _ => by positivity)
    _ ≤ _ := by
      rw [← mul_sum]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_two_mul_le_of_pos hε hε2 D) (sq_nonneg K))
        (mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_two_mul_le_of_pos hε hε2 T) (sq_nonneg L))

private theorem eventually_log_pow_le_positive_rpow (q : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ q ≤ (n : ℝ) ^ a := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ q / (n : ℝ) ^ a) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast] using
      ((isLittleO_log_rpow_rpow_atTop (q : ℝ) ha).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop)
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  exact ((div_lt_one (Real.rpow_pos_of_pos hn0 a)).mp hn).le

/-- A square-root energy split preserves all uniform logarithmic prefix savings. -/
theorem exists_uniform_pronicEnergy_log_rate_of_prefix_log_rate
    {ι : Type*} {f : ι → ℕ → ℝ} {ε K : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (_hK : 0 ≤ K) (hglobal : ∀ i n, 1 ≤ n → |f i n| ≤ K * (n : ℝ) ^ (1 - ε))
    (hlog : ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ i,
      |f i n| ≤ B * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ i,
      (∑ n ∈ Icc 1 T, f i n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
        C * (T : ℝ) ^ (1 - 2 * ε) / (Real.log (T : ℝ) ^ q) ^ 2 := by
  let β := 1 - 2 * ε
  have hβ : 0 < β := by dsimp only [β]; linarith only [hε2]
  obtain ⟨B, hB, hBbound⟩ := hlog q
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hBbound
  let D : ℕ → ℕ := fun T => ⌊(T : ℝ) ^ (1 / 2 : ℝ)⌋₊
  have hDlim : Tendsto D atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop)
  have hloglim : Tendsto (fun T : ℕ => Real.log (T : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨(K ^ 2 + (4 ^ q * B) ^ 2) * (1 + 1 / β), by positivity, ?_⟩
  filter_upwards [hDlim.eventually_ge_atTop (max N₀ 1), hloglim.eventually_ge_atTop 1,
    hloglim.eventually_ge_atTop (4 * Real.log 2),
    eventually_log_pow_le_positive_rpow (2 * q) (by positivity : 0 < β / 2),
    eventually_ge_atTop 1] with T hDstart hlog1 hlog4 hsmall hT i
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hl : 0 < Real.log (T : ℝ) := zero_lt_one.trans_le hlog1
  have hD1 : 1 ≤ D T := (le_max_right N₀ 1).trans hDstart
  have hD0 : (0 : ℝ) < D T := by exact_mod_cast hD1
  have hlogD : Real.log (T : ℝ) / 4 ≤ Real.log (D T : ℝ) := by
    have h := CubicGamma.log_floor_rpow_ge hT1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    change 1 / 2 * Real.log (T : ℝ) - Real.log 2 ≤ Real.log (D T : ℝ) at h
    linarith only [h, hlog4]
  have hlate (n : ℕ) (_hn : 1 ≤ n) (hDn : D T ≤ n) :
      |f i n| ≤ (4 ^ q * B / Real.log (T : ℝ) ^ q) * (n : ℝ) ^ (1 - ε) := by
    have hlogn : Real.log (T : ℝ) / 4 ≤ Real.log (n : ℝ) :=
      hlogD.trans (Real.log_le_log hD0 (by exact_mod_cast hDn))
    calc
      _ ≤ B * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q :=
        hN₀ n (((le_max_left N₀ 1).trans hDstart).trans hDn) i
      _ ≤ B * (n : ℝ) ^ (1 - ε) / (Real.log (T : ℝ) / 4) ^ q :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) hlogn q)
      _ = _ := by
        rw [div_pow]
        field_simp [hl.ne']
  have hfinite := sum_pronicCell_le_of_split_rpow hε hε2 (D T) T (hglobal i) hlate
  have hDpow : (D T : ℝ) ^ β ≤ (T : ℝ) ^ (β / 2) := by
    calc
      _ ≤ ((T : ℝ) ^ (1 / 2 : ℝ)) ^ β :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg hT0.le _)) hβ.le
      _ = _ := by rw [← Real.rpow_mul hT0.le]; congr 1; ring
  have hhalf1 : 1 ≤ (T : ℝ) ^ (β / 2) := Real.one_le_rpow hT1 (by positivity)
  have hfull1 : 1 ≤ (T : ℝ) ^ β := Real.one_le_rpow hT1 hβ.le
  rw [Nat.mul_comm 2 q, pow_mul] at hsmall
  have hhalf : (T : ℝ) ^ (β / 2) ≤ (T : ℝ) ^ β / (Real.log (T : ℝ) ^ q) ^ 2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hT0.le (β / 2))
    rw [← Real.rpow_add hT0, show β / 2 + β / 2 = β by ring] at h
    exact h
  have hhead : K ^ 2 * (1 + (D T : ℝ) ^ β / β) ≤
      (K ^ 2 * (1 + 1 / β)) * (T : ℝ) ^ β / (Real.log (T : ℝ) ^ q) ^ 2 := by
    have hdiv := div_le_div_of_nonneg_right hDpow hβ.le
    calc
      _ ≤ (K ^ 2 * (1 + 1 / β)) * (T : ℝ) ^ (β / 2) := by
        have h := mul_le_mul_of_nonneg_left (add_le_add hhalf1 hdiv) (sq_nonneg K)
        exact h.trans_eq (by ring)
      _ ≤ (K ^ 2 * (1 + 1 / β)) *
          ((T : ℝ) ^ β / (Real.log (T : ℝ) ^ q) ^ 2) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = _ := by ring
  have htail : (4 ^ q * B / Real.log (T : ℝ) ^ q) ^ 2 * (1 + (T : ℝ) ^ β / β) ≤
      ((4 ^ q * B) ^ 2 * (1 + 1 / β)) * (T : ℝ) ^ β / (Real.log (T : ℝ) ^ q) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left
      (add_le_add hfull1 (le_refl ((T : ℝ) ^ β / β)))
      (sq_nonneg (4 ^ q * B / Real.log (T : ℝ) ^ q))
    exact h.trans_eq (by rw [div_pow]; ring)
  exact hfinite.trans ((add_le_add hhead htail).trans_eq (by ring))

/-- The same uniform logarithmic energy bounds give the corresponding pronic norm bounds. -/
theorem exists_uniform_pronicNorm_log_rate_of_prefix_log_rate
    {ι : Type*} {f : ι → ℕ → ℝ} {ε K : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hK : 0 ≤ K) (hglobal : ∀ i n, 1 ≤ n → |f i n| ≤ K * (n : ℝ) ^ (1 - ε))
    (hlog : ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∀ i,
      |f i n| ≤ B * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q) (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℕ in atTop, ∀ i,
      pronicNorm (f i) T ≤
        B * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q := by
  obtain ⟨C, hC, hE⟩ := exists_uniform_pronicEnergy_log_rate_of_prefix_log_rate
    hε hε2 hK hglobal hlog q
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [hE, eventually_ge_atTop 1] with T hT hT1 i
  have hl : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT1)
  have h := Real.sqrt_le_sqrt (hT i)
  change pronicNorm (f i) T ≤ _ at h
  rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_mul hC,
    Real.sqrt_sq (pow_nonneg hl q)] at h
  exact h

/-- Every fixed logarithmic power is eventually below any positive pronic norm power scale. -/
theorem eventually_log_pow_le_sqrt_rpow (q : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ T : ℕ in atTop, Real.log (T : ℝ) ^ q ≤ Real.sqrt ((T : ℝ) ^ β) := by
  filter_upwards [eventually_log_pow_le_positive_rpow q (half_pos hβ)] with T hT
  simpa only [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg T), mul_one_div] using hT

/-- A uniformly bounded family has every logarithmic saving relative to a positive norm power scale. -/
theorem eventually_pronicNorm_log_rate_of_uniform_bound {ι : Type*} {f : ι → ℕ → ℝ}
    {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C)
    (hbound : ∀ i T, pronicNorm (f i) T ≤ C) (q : ℕ) :
    ∀ᶠ T : ℕ in atTop, ∀ i, pronicNorm (f i) T ≤
      C * Real.sqrt ((T : ℝ) ^ β) / Real.log (T : ℝ) ^ q := by
  have hloglim : Tendsto (fun T : ℕ => Real.log (T : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_log_pow_le_sqrt_rpow q hβ,
    hloglim.eventually_ge_atTop 1] with T hT hlog i
  have hl : 0 < Real.log (T : ℝ) := zero_lt_one.trans_le hlog
  refine (hbound i T).trans ?_
  exact (le_div_iff₀ (pow_pos hl q)).mpr (mul_le_mul_of_nonneg_left hT hC)

end GaloisForLFunctions.BezoutValuationIncidence
