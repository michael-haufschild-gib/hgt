import GaloisForLFunctions.RHTower.WeilLagFunctionInteger
import Mathlib.Analysis.Convex.Mul

/-!
# Quadratic upper interpolation for the integer Weil lag

The prime part of the unnormalized lag is a sum of nonnegative convex ramps.
The logarithmic chord defect has a quadratic upper bound, and the trivial-zero
series is convex. These facts control interior lag values
from two endpoint values without a zero-location assumption.
-/

open Real Set
open scoped Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-- The finite arithmetic ramp sum at a real position. -/
def lagArithmeticRamp (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, vonMangoldt j * max (x / (j : ℝ) - 1) 0

/-- At integer positions, the ramps give the complete prime-side lag term. -/
theorem lagArithmeticRamp_nat {n N : ℕ} (hnN : n ≤ N) :
    lagArithmeticRamp N n = (n : ℝ) * mertensSum n - Chebyshev.psi n := by
  classical
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 N := by
    intro j hj
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
      (Finset.mem_Icc.mp hj).2.trans hnN⟩
  have htrim :
      (∑ j ∈ Finset.Icc 1 n, vonMangoldt j * max ((n : ℝ) / j - 1) 0) =
      ∑ j ∈ Finset.Icc 1 N, vonMangoldt j * max ((n : ℝ) / j - 1) 0 := by
    apply Finset.sum_subset hsub
    intro j hj hjn
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hnj : n < j := by
      by_contra h
      exact hjn (Finset.mem_Icc.mpr ⟨hj1, by omega⟩)
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hle : (n : ℝ) / j - 1 ≤ 0 := by
      have := (div_le_one hj0).mpr (show (n : ℝ) ≤ j by exact_mod_cast hnj.le)
      linarith
    rw [max_eq_right hle, mul_zero]
  unfold lagArithmeticRamp
  have hIcc : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [← htrim, mertensSum, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, hIcc,
    Finset.sum_insert (by simp)]
  simp only [ArithmeticFunction.map_zero, zero_add]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hjn := (Finset.mem_Icc.mp hj).2
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hle : 0 ≤ (n : ℝ) / j - 1 := by
    have := (one_le_div hj0).mpr (show (j : ℝ) ≤ n by exact_mod_cast hjn)
    linarith
  rw [max_eq_left hle]
  ring

/-- Every finite arithmetic ramp sum lies below its endpoint chord. -/
theorem lagArithmeticRamp_chord (N : ℕ) {a b u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    lagArithmeticRamp N (u * a + v * b) ≤
      u * lagArithmeticRamp N a + v * lagArithmeticRamp N b := by
  unfold lagArithmeticRamp
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have hlinear : (u * a + v * b) / (j : ℝ) - 1 =
      u * (a / j - 1) + v * (b / j - 1) := by
    calc _ = (u * a + v * b) / (j : ℝ) - (u + v) := by rw [huv]
      _ = _ := by ring
  have hmax : max ((u * a + v * b) / (j : ℝ) - 1) 0 ≤
      u * max (a / j - 1) 0 + v * max (b / j - 1) 0 := by
    apply max_le
    · rw [hlinear]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hv)
    · positivity
  calc vonMangoldt j * max ((u * a + v * b) / (j : ℝ) - 1) 0 ≤
      vonMangoldt j * (u * max (a / j - 1) 0 + v * max (b / j - 1) 0) :=
        mul_le_mul_of_nonneg_left hmax ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by ring

/-- The entropy chord defect is at most the endpoint variance divided by its mean. -/
theorem mul_log_chord_defect_le {a b x u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : x = u * a + v * b) :
    u * a * Real.log a + v * b * Real.log b - x * Real.log x ≤
      u * v * (b - a) ^ 2 / x := by
  have hla : Real.log a - Real.log x ≤ a / x - 1 := by
    rw [← Real.log_div ha.ne' hx.ne']
    exact Real.log_le_sub_one_of_pos (div_pos ha hx)
  have hlb : Real.log b - Real.log x ≤ b / x - 1 := by
    rw [← Real.log_div hb.ne' hx.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hb hx)
  have he : u * a * (a / x - 1) + v * b * (b / x - 1) =
      u * v * (b - a) ^ 2 / x := by
    have hv' : v = 1 - u := by linarith
    field_simp
    rw [hmean, hv']
    ring
  calc u * a * Real.log a + v * b * Real.log b - x * Real.log x =
      u * a * (Real.log a - Real.log x) +
        v * b * (Real.log b - Real.log x) := by rw [hmean]; ring
    _ ≤ u * a * (a / x - 1) + v * b * (b / x - 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hla (mul_nonneg hu ha.le))
        (mul_le_mul_of_nonneg_left hlb (mul_nonneg hv hb.le))
    _ = _ := he

/-- The complete trivial-zero correction lies below its endpoint chord. -/
theorem trivialZeroSeriesReal_chord {a b u v : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    trivialZeroSeriesReal (u * a + v * b) ≤
      u * trivialZeroSeriesReal a + v * trivialZeroSeriesReal b := by
  have hx : 1 ≤ u * a + v * b := by
    calc 1 = u * 1 + v * 1 := by rw [mul_one, mul_one, huv]
      _ ≤ u * a + v * b := by gcongr
  let f : ℝ → ℕ → ℝ := fun x j =>
    (x ^ (2 * (j + 1)))⁻¹ / (2 * ((j : ℝ) + 1) * (2 * (j : ℝ) + 3))
  have hterm : ∀ j, f (u * a + v * b) j ≤ u * f a j + v * f b j := by
    intro j
    have h := (convexOn_zpow (𝕜 := ℝ) (-(2 * (j + 1) : ℕ) : ℤ)).2
      (show 0 < a by linarith) (show 0 < b by linarith) hu hv huv
    have hp : ((u * a + v * b) ^ (2 * (j + 1)))⁻¹ ≤
        u * (a ^ (2 * (j + 1)))⁻¹ + v * (b ^ (2 * (j + 1)))⁻¹ := by
      simpa only [smul_eq_mul, zpow_neg, zpow_natCast] using h
    dsimp [f]
    calc _ ≤ (u * (a ^ (2 * (j + 1)))⁻¹ + v * (b ^ (2 * (j + 1)))⁻¹) /
        (2 * ((j : ℝ) + 1) * (2 * (j : ℝ) + 3)) :=
          div_le_div_of_nonneg_right hp (by positivity)
      _ = _ := by ring
  have haS : Summable (f a) := summable_trivialZeroSeriesReal_term ha
  have hbS : Summable (f b) := summable_trivialZeroSeriesReal_term hb
  have hxS : Summable (f (u * a + v * b)) := summable_trivialZeroSeriesReal_term hx
  have h := hxS.tsum_le_tsum hterm ((haS.mul_left u).add (hbS.mul_left v))
  rw [(haS.mul_left u).tsum_add (hbS.mul_left v), tsum_mul_left, tsum_mul_left] at h
  exact h

private theorem sqrt_mul_integerLag_eq_ramp {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    Real.sqrt n * integerLag n =
      (n : ℝ) * (1 + eulerMascheroniConstant) - n * Real.log n - Real.log (2 * π) +
        trivialZeroSeriesReal n + lagArithmeticRamp N n := by
  rw [integerLag_eq hn, lagArithmeticRamp_nat hnN]
  have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp
  ring

/-- Upper interpolation for the actual integer Weil lag, including every prime atom. -/
theorem sqrt_integerLag_chord_le {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m) :
    Real.sqrt k * integerLag k ≤
      u * (Real.sqrt n * integerLag n) + v * (Real.sqrt m * integerLag m) +
        u * v * ((m : ℝ) - n) ^ 2 / k := by
  have hk : 2 ≤ k := hn.trans hnk
  have hm : 2 ≤ m := hk.trans hkm
  have hr := lagArithmeticRamp_chord m hu hv huv (a := (n : ℝ)) (b := (m : ℝ))
  rw [← hmean] at hr
  have hl := mul_log_chord_defect_le
    (by positivity : (0 : ℝ) < n) (by positivity : (0 : ℝ) < m)
    (by positivity : (0 : ℝ) < k) hu hv huv hmean
  have hS := trivialZeroSeriesReal_chord
    (show (1 : ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n))
    (show (1 : ℝ) ≤ m by exact_mod_cast (by omega : 1 ≤ m)) hu hv huv
  rw [← hmean] at hS
  rw [sqrt_mul_integerLag_eq_ramp hk hkm, sqrt_mul_integerLag_eq_ramp hn (hnk.trans hkm),
    sqrt_mul_integerLag_eq_ramp hm le_rfl]
  have hconst : (k : ℝ) * (1 + eulerMascheroniConstant) - Real.log (2 * π) =
      u * ((n : ℝ) * (1 + eulerMascheroniConstant) - Real.log (2 * π)) +
        v * ((m : ℝ) * (1 + eulerMascheroniConstant) - Real.log (2 * π)) := by
    calc _ = (u * n + v * m) * (1 + eulerMascheroniConstant) -
        (u + v) * Real.log (2 * π) := by rw [hmean, huv]; ring
      _ = _ := by ring
  linarith only [hconst, hr, hl, hS]

/-- A nonnegative endpoint ceiling propagates through the normalized upper chord. -/
theorem integerLag_chord_ceiling {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v M : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m)
    (hM : 0 ≤ M) (hnM : integerLag n ≤ M) (hmM : integerLag m ≤ M) :
    integerLag k ≤ M + (u * v * ((m : ℝ) - n) ^ 2 / k) / Real.sqrt k := by
  have hcore := sqrt_integerLag_chord_le hn hnk hkm hu hv huv hmean
  have hk : 2 ≤ k := hn.trans hnk
  have hk0 : (0 : ℝ) < k := by positivity
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hsn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsm : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have hvar : (u * Real.sqrt n + v * Real.sqrt m) ^ 2 +
      u * v * (Real.sqrt n - Real.sqrt m) ^ 2 = (k : ℝ) := by
    calc _ = u * (u + v) * (Real.sqrt n) ^ 2 +
        v * (u + v) * (Real.sqrt m) ^ 2 := by ring
      _ = u * (n : ℝ) + v * m := by
        rw [huv, mul_one, mul_one, Real.sq_sqrt (Nat.cast_nonneg n),
          Real.sq_sqrt (Nat.cast_nonneg m)]
      _ = k := hmean.symm
  have ht0 : 0 ≤ u * Real.sqrt n + v * Real.sqrt m := by positivity
  have ht2 : (u * Real.sqrt n + v * Real.sqrt m) ^ 2 ≤ (k : ℝ) := by
    rw [← hvar]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hu hv) (sq_nonneg _))
  have ht : u * Real.sqrt n + v * Real.sqrt m ≤ Real.sqrt k := by
    nlinarith only [ht0, ht2, hsk, Real.sq_sqrt hk0.le]
  have hend : u * (Real.sqrt n * integerLag n) + v * (Real.sqrt m * integerLag m) ≤
      Real.sqrt k * M := by
    calc _ ≤ u * (Real.sqrt n * M) + v * (Real.sqrt m * M) := by gcongr
      _ = (u * Real.sqrt n + v * Real.sqrt m) * M := by ring
      _ ≤ Real.sqrt k * M := mul_le_mul_of_nonneg_right ht hM
  have hfinal : Real.sqrt k * integerLag k ≤ Real.sqrt k * M +
      (u * v * ((m : ℝ) - n) ^ 2 / k) := by linarith only [hcore, hend]
  calc integerLag k = (Real.sqrt k * integerLag k) / Real.sqrt k := by field_simp
    _ ≤ (Real.sqrt k * M + (u * v * ((m : ℝ) - n) ^ 2 / k)) / Real.sqrt k :=
      div_le_div_of_nonneg_right hfinal hsk.le
    _ = _ := by field_simp

/-- A whole integer interval inherits its endpoint ceiling with quadratic gap loss. -/
theorem integerLag_le_endpoint_ceiling_add_quadratic {n k m : ℕ}
    (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {M : ℝ} (hM : 0 ≤ M) (hnM : integerLag n ≤ M) (hmM : integerLag m ≤ M) :
    integerLag k ≤ M + (((m : ℝ) - n) ^ 2 / (4 * k)) / Real.sqrt k := by
  by_cases hnm : n = m
  · have hkn : k = n := by omega
    subst m
    subst k
    have herror : 0 ≤ (((n : ℝ) - n) ^ 2 / (4 * n)) / Real.sqrt n := by positivity
    exact hnM.trans (le_add_of_nonneg_right herror)
  have hnm' : n < m := by omega
  have hg : 0 < (m : ℝ) - n := sub_pos.mpr (by exact_mod_cast hnm')
  let u : ℝ := ((m : ℝ) - k) / ((m : ℝ) - n)
  let v : ℝ := ((k : ℝ) - n) / ((m : ℝ) - n)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hkm)) hg.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hnk)) hg.le
  have huv : u + v = 1 := by dsimp [u, v]; field_simp; ring
  have hmean : (k : ℝ) = u * n + v * m := by dsimp [u, v]; field_simp; ring
  have hq : u * v ≤ 1 / 4 := by
    have hs : (u + v) ^ 2 = 1 := by rw [huv]; ring
    nlinarith only [hs, sq_nonneg (u - v)]
  have hcore := integerLag_chord_ceiling hn hnk hkm hu hv huv hmean hM hnM hmM
  refine hcore.trans (add_le_add le_rfl ?_)
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc u * v * ((m : ℝ) - n) ^ 2 / k ≤
      (1 / 4) * ((m : ℝ) - n) ^ 2 / k := by gcongr
    _ = ((m : ℝ) - n) ^ 2 / (4 * k) := by ring

/-- Unconditional upper interpolation of every actual lag by its two endpoint lags. -/
theorem integerLag_quadratic_upper_interpolation :
    ∀ n k m : ℕ, 2 ≤ n → n ≤ k → k ≤ m →
      integerLag k ≤ max 0 (max (integerLag n) (integerLag m)) +
        (((m : ℝ) - n) ^ 2 / (4 * k)) / Real.sqrt k := by
  intro n k m hn hnk hkm
  apply integerLag_le_endpoint_ceiling_add_quadratic hn hnk hkm (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- A set brackets the integers with gaps whose squares are at most the natural `n^(3/2)` scale. -/
def QuadraticLagMesh (S : Set ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 2 ≤ k →
    ∃ n ∈ S, ∃ m ∈ S, 2 ≤ n ∧ n ≤ k ∧ k ≤ m ∧
      ((m : ℝ) - n) ^ 2 ≤ C * ((n : ℝ) * Real.sqrt n)

/-- An upper bound on a quadratic lag mesh bounds all integer lags. -/
theorem integerLag_bddAbove_of_quadraticMesh {S : Set ℕ}
    (hS : QuadraticLagMesh S) {M : ℝ} (hM : ∀ n ∈ S, integerLag n ≤ M) :
    ∃ B : ℝ, ∀ k : ℕ, 2 ≤ k → integerLag k ≤ B := by
  obtain ⟨C, hC, hmesh⟩ := hS
  refine ⟨max M 0 + C / 4, ?_⟩
  intro k hk
  obtain ⟨n, hnS, m, hmS, hn, hnk, hkm, hgap⟩ := hmesh k hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hn0 : (0 : ℝ) < n := by positivity
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hsn : Real.sqrt (n : ℝ) ≤ Real.sqrt k := Real.sqrt_le_sqrt (by exact_mod_cast hnk)
  have hns : (n : ℝ) * Real.sqrt n ≤ (k : ℝ) * Real.sqrt k := by gcongr
  have hgap' : ((m : ℝ) - n) ^ 2 ≤ C * ((k : ℝ) * Real.sqrt k) :=
    hgap.trans (mul_le_mul_of_nonneg_left hns hC)
  have hquad : (((m : ℝ) - n) ^ 2 / (4 * k)) / Real.sqrt k ≤ C / 4 := by
    rw [div_le_iff₀ hsk, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * k)]
    nlinarith only [hgap']
  have hcore := integerLag_le_endpoint_ceiling_add_quadratic hn hnk hkm
    (le_max_right M 0) ((hM n hnS).trans (le_max_left M 0))
    ((hM m hmS).trans (le_max_left M 0))
  linarith only [hcore, hquad]

/-- For every quadratic mesh, its bounded upper lag law is exactly RH. -/
theorem quadraticLagMesh_characterization :
    ∀ S : Set ℕ,
      (QuadraticLagMesh S ∧ ∃ M : ℝ, ∀ n ∈ S, integerLag n ≤ M) ↔
        (QuadraticLagMesh S ∧ RiemannHypothesis) := by
  intro S
  constructor
  · rintro ⟨hS, M, hM⟩
    exact ⟨hS, riemannHypothesis_iff_integerLag_bddAbove.mpr
      (integerLag_bddAbove_of_quadraticMesh hS hM)⟩
  · rintro ⟨hS, hRH⟩
    refine ⟨hS, poleSharpConstant, fun n _ => ?_⟩
    exact (le_abs_self (integerLag n)).trans (abs_integerLag_le_of_riemannHypothesis hRH n)

end

end RHTower
