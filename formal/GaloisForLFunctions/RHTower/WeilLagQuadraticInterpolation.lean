import GaloisForLFunctions.RHTower.WeilLagFunctionInteger
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Prime-compensated upper interpolation for the integer Weil lag

The prime part of the unnormalized lag is a sum of nonnegative convex ramps.
The logarithmic chord defect has a quadratic upper bound, and the trivial-zero
series is convex. Their exact chord balance retains a triangular prime charge.
These facts control interior lag values from two endpoint values without a
zero-location assumption, and give both geometric and prime-compensated mesh receivers.
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

private theorem lag_max_chord_gap {A B u v : ℝ} (hAB : A ≤ B)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u * max A 0 + v * max B 0 - max (u * A + v * B) 0 =
      min (u * max (-A) 0) (v * max B 0) := by
  by_cases hA : 0 ≤ A
  · have hB : 0 ≤ B := hA.trans hAB
    rw [max_eq_left hA, max_eq_left hB, max_eq_right (by linarith : -A ≤ 0),
      max_eq_left (by positivity : 0 ≤ u * A + v * B), mul_zero,
      min_eq_left (by positivity : (0 : ℝ) ≤ v * B)]
    ring
  have hA' : A ≤ 0 := le_of_not_ge hA
  by_cases hB : B ≤ 0
  · have hX : u * A + v * B ≤ 0 := add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hu hA') (mul_nonpos_of_nonneg_of_nonpos hv hB)
    rw [max_eq_right hA', max_eq_right hB, max_eq_right hX,
      max_eq_left (by linarith : 0 ≤ -A), mul_zero, mul_zero,
      min_eq_right (mul_nonneg hu (neg_nonneg.mpr hA'))]
    ring
  have hB' : 0 ≤ B := le_of_not_ge hB
  rw [max_eq_right hA', max_eq_left hB', max_eq_left (by linarith : 0 ≤ -A), mul_zero]
  by_cases hX : 0 ≤ u * A + v * B
  · rw [max_eq_left hX, min_eq_left (by nlinarith : u * (-A) ≤ v * B)]
    ring
  · rw [max_eq_right (le_of_not_ge hX), min_eq_right (by nlinarith : v * B ≤ u * (-A))]
    ring

/-- Nonnegative prime mass in the triangular kernel between two arithmetic endpoints. -/
def lagPrimeChordCharge (N : ℕ) (a b u v : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, vonMangoldt j *
    min (u * max (1 - a / (j : ℝ)) 0) (v * max (b / (j : ℝ) - 1) 0)

/-- Every actual prime atom contributes nonnegative chord charge. -/
theorem lagPrimeChordCharge_nonneg (N : ℕ) (a b : ℝ) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ lagPrimeChordCharge N a b u v := by
  unfold lagPrimeChordCharge
  exact Finset.sum_nonneg fun j _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (le_min (by positivity) (by positivity))

/-- The arithmetic ramp chord deficit is exactly the triangular prime charge. -/
theorem lagArithmeticRamp_chord_eq_charge (N : ℕ) {a b u v : ℝ}
    (hab : a ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    u * lagArithmeticRamp N a + v * lagArithmeticRamp N b -
      lagArithmeticRamp N (u * a + v * b) = lagPrimeChordCharge N a b u v := by
  unfold lagArithmeticRamp lagPrimeChordCharge
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hlinear : (u * a + v * b) / (j : ℝ) - 1 =
      u * (a / j - 1) + v * (b / j - 1) := by
    calc _ = (u * a + v * b) / (j : ℝ) - (u + v) := by rw [huv]
      _ = _ := by ring
  have h := lag_max_chord_gap (sub_le_sub_right (div_le_div_of_nonneg_right hab hj0.le) 1) hu hv
  rw [← hlinear] at h
  have hneg : -(a / (j : ℝ) - 1) = 1 - a / j := by ring
  rw [hneg] at h
  calc _ = vonMangoldt j * (u * max (a / j - 1) 0 + v * max (b / j - 1) 0 -
      max ((u * a + v * b) / j - 1) 0) := by ring
    _ = _ := by rw [h]

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

private theorem convexOn_lagLogQuadratic {r : ℝ} (hr : 0 < r) :
    ConvexOn ℝ (Ici r) (fun x : ℝ => x ^ 2 / (2 * r) - x * Real.log x) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x => x / r - Real.log x - 1)
    (f'' := fun x => 1 / r - x⁻¹) (convex_Ici r)
  · exact ((continuous_id.pow 2).div_const (2 * r)).sub continuous_id.mul_log |>.continuousOn
  · intro x hx
    have hxr : r ≤ x := interior_subset hx
    have hx0 : 0 < x := hr.trans_le hxr
    have h := (((hasDerivAt_id' x).pow 2).div_const (2 * r)).sub
      (Real.hasDerivAt_mul_log hx0.ne')
    convert! h.hasDerivWithinAt using 1
    field_simp
    ring
  · intro x hx
    have hxr : r ≤ x := interior_subset hx
    have hx0 : 0 < x := hr.trans_le hxr
    simpa only [one_div, Pi.sub_apply] using!
      (((hasDerivAt_id' x).div_const r).sub (Real.hasDerivAt_log hx0.ne')).sub_const 1 |>.hasDerivWithinAt
  · intro x hx
    have hxr : r ≤ x := interior_subset hx
    have h := one_div_le_one_div_of_le hr hxr
    simpa only [one_div, sub_nonneg] using h

/-- The entropy chord defect is at most half the variance divided by a positive lower endpoint. -/
theorem mul_log_chord_defect_le_of_lower_bound {r a b x u v : ℝ} (hr : 0 < r)
    (ha : r ≤ a) (hb : r ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : x = u * a + v * b) :
    u * a * Real.log a + v * b * Real.log b - x * Real.log x ≤
      u * v * (b - a) ^ 2 / (2 * r) := by
  have h := (convexOn_lagLogQuadratic hr).2 ha hb hu hv huv
  simp only [smul_eq_mul] at h
  rw [← hmean] at h
  have he : u * a ^ 2 + v * b ^ 2 - x ^ 2 = u * v * (b - a) ^ 2 := by
    have hv' : v = 1 - u := by linarith
    rw [hmean, hv']
    ring
  calc _ ≤ (u * a ^ 2 + v * b ^ 2 - x ^ 2) / (2 * r) := by linear_combination h
    _ = _ := by rw [he]

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

/-- Exact lag chord balance: logarithmic defect minus prime charge and trivial-zero deficit. -/
theorem sqrt_integerLag_chord_exact {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m) :
    Real.sqrt k * integerLag k -
        u * (Real.sqrt n * integerLag n) - v * (Real.sqrt m * integerLag m) =
      (u * n * Real.log n + v * m * Real.log m - k * Real.log k) -
        lagPrimeChordCharge m n m u v -
        (u * trivialZeroSeriesReal n + v * trivialZeroSeriesReal m - trivialZeroSeriesReal k) := by
  have hk : 2 ≤ k := hn.trans hnk
  have hm : 2 ≤ m := hk.trans hkm
  have hr := lagArithmeticRamp_chord_eq_charge m
    (show (n : ℝ) ≤ m by exact_mod_cast (hnk.trans hkm)) hu hv huv
  rw [← hmean] at hr
  rw [sqrt_mul_integerLag_eq_ramp hk hkm, sqrt_mul_integerLag_eq_ramp hn (hnk.trans hkm),
    sqrt_mul_integerLag_eq_ramp hm le_rfl]
  have hconst : (k : ℝ) * (1 + eulerMascheroniConstant) - Real.log (2 * π) =
      u * ((n : ℝ) * (1 + eulerMascheroniConstant) - Real.log (2 * π)) +
        v * ((m : ℝ) * (1 + eulerMascheroniConstant) - Real.log (2 * π)) := by
    calc _ = (u * n + v * m) * (1 + eulerMascheroniConstant) -
        (u + v) * Real.log (2 * π) := by rw [hmean, huv]; ring
      _ = _ := by ring
  linarith only [hconst, hr]

/-- Prime chord charge subtracts from the logarithmic upper-interpolation loss. -/
theorem sqrt_integerLag_chord_le_prime {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m) :
    Real.sqrt k * integerLag k ≤
      u * (Real.sqrt n * integerLag n) + v * (Real.sqrt m * integerLag m) +
        ((u * n * Real.log n + v * m * Real.log m - k * Real.log k) -
          lagPrimeChordCharge m n m u v) := by
  have h := sqrt_integerLag_chord_exact hn hnk hkm hu hv huv hmean
  have hS := trivialZeroSeriesReal_chord
    (show (1 : ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n))
    (show (1 : ℝ) ≤ m by exact_mod_cast (by omega : 1 ≤ m)) hu hv huv
  rw [← hmean] at hS
  linarith only [h, hS]

/-- Upper interpolation for the actual integer Weil lag, including every prime atom. -/
theorem sqrt_integerLag_chord_le_log {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m) :
    Real.sqrt k * integerLag k ≤
      u * (Real.sqrt n * integerLag n) + v * (Real.sqrt m * integerLag m) +
        (u * n * Real.log n + v * m * Real.log m - k * Real.log k) := by
  have h := sqrt_integerLag_chord_le_prime hn hnk hkm hu hv huv hmean
  have hQ := lagPrimeChordCharge_nonneg m (n : ℝ) (m : ℝ) hu hv
  linarith only [h, hQ]

/-- Quadratic upper interpolation for the unnormalized lag at a barycentric integer. -/
theorem sqrt_integerLag_chord_le {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m) :
    Real.sqrt k * integerLag k ≤
      u * (Real.sqrt n * integerLag n) + v * (Real.sqrt m * integerLag m) +
        u * v * ((m : ℝ) - n) ^ 2 / k := by
  have hk : 2 ≤ k := hn.trans hnk
  have hm : 2 ≤ m := hk.trans hkm
  exact (sqrt_integerLag_chord_le_log hn hnk hkm hu hv huv hmean).trans
    (add_le_add le_rfl (mul_log_chord_defect_le
      (by positivity : (0 : ℝ) < n) (by positivity : (0 : ℝ) < m)
      (by positivity : (0 : ℝ) < k) hu hv huv hmean))

private theorem integerLag_ceiling_of_scaled_chord {n k m : ℕ} (hk : 0 < k)
    {u v M E : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m)
    (hM : 0 ≤ M) (hnM : integerLag n ≤ M) (hmM : integerLag m ≤ M)
    (hcore : Real.sqrt k * integerLag k ≤
      u * (Real.sqrt n * integerLag n) + v * (Real.sqrt m * integerLag m) + E) :
    integerLag k ≤ M + E / Real.sqrt k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
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
  have hfinal : Real.sqrt k * integerLag k ≤ Real.sqrt k * M + E := by
    linarith only [hcore, hend]
  calc integerLag k = (Real.sqrt k * integerLag k) / Real.sqrt k := by field_simp
    _ ≤ (Real.sqrt k * M + E) / Real.sqrt k :=
      div_le_div_of_nonneg_right hfinal hsk.le
    _ = _ := by field_simp

/-- Prime compensation strengthens the normalized endpoint ceiling. -/
theorem integerLag_chord_prime_ceiling {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v M : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m)
    (hM : 0 ≤ M) (hnM : integerLag n ≤ M) (hmM : integerLag m ≤ M) :
    integerLag k ≤ M +
      ((u * n * Real.log n + v * m * Real.log m - k * Real.log k) -
        lagPrimeChordCharge m n m u v) / Real.sqrt k := by
  exact integerLag_ceiling_of_scaled_chord (by omega) hu hv huv hmean hM hnM hmM
    (sqrt_integerLag_chord_le_prime hn hnk hkm hu hv huv hmean)

/-- A nonnegative endpoint ceiling propagates through the normalized upper chord. -/
theorem integerLag_chord_log_ceiling {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v M : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m)
    (hM : 0 ≤ M) (hnM : integerLag n ≤ M) (hmM : integerLag m ≤ M) :
    integerLag k ≤ M +
      (u * n * Real.log n + v * m * Real.log m - k * Real.log k) / Real.sqrt k := by
  exact integerLag_ceiling_of_scaled_chord (by omega) hu hv huv hmean hM hnM hmM
    (sqrt_integerLag_chord_le_log hn hnk hkm hu hv huv hmean)

/-- A quadratic endpoint ceiling bound at a barycentric integer. -/
theorem integerLag_chord_ceiling {n k m : ℕ} (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {u v M : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hmean : (k : ℝ) = u * n + v * m)
    (hM : 0 ≤ M) (hnM : integerLag n ≤ M) (hmM : integerLag m ≤ M) :
    integerLag k ≤ M + (u * v * ((m : ℝ) - n) ^ 2 / k) / Real.sqrt k := by
  have hk : 2 ≤ k := hn.trans hnk
  have hm : 2 ≤ m := hk.trans hkm
  refine (integerLag_chord_log_ceiling hn hnk hkm hu hv huv hmean hM hnM hmM).trans
    (add_le_add le_rfl (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)))
  exact mul_log_chord_defect_le (by positivity : (0 : ℝ) < n)
    (by positivity : (0 : ℝ) < m) (by positivity : (0 : ℝ) < k) hu hv huv hmean

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

/-- The curvature ceiling uses the local coefficient `1/8` at the lower endpoint. -/
theorem integerLag_le_endpoint_ceiling_add_curvature {n k m : ℕ}
    (hn : 2 ≤ n) (hnk : n ≤ k) (hkm : k ≤ m)
    {M : ℝ} (hM : 0 ≤ M) (hnM : integerLag n ≤ M) (hmM : integerLag m ≤ M) :
    integerLag k ≤ M + (((m : ℝ) - n) ^ 2 / (8 * n)) / Real.sqrt k := by
  by_cases hnm : n = m
  · have hkn : k = n := by omega
    subst m
    subst k
    simpa using hnM
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
  refine (integerLag_chord_log_ceiling hn hnk hkm hu hv huv hmean hM hnM hmM).trans
    (add_le_add le_rfl (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)))
  calc _ ≤ u * v * ((m : ℝ) - n) ^ 2 / (2 * n) :=
      mul_log_chord_defect_le_of_lower_bound (by positivity : (0 : ℝ) < n)
        le_rfl (by exact_mod_cast (hnk.trans hkm)) hu hv huv hmean
    _ ≤ (1 / 4) * ((m : ℝ) - n) ^ 2 / (2 * n) := by gcongr
    _ = ((m : ℝ) - n) ^ 2 / (8 * n) := by ring

/-- Unconditional interpolation with the local archimedean curvature coefficient. -/
theorem integerLag_curvature_upper_interpolation :
    ∀ n k m : ℕ, 2 ≤ n → n ≤ k → k ≤ m →
      integerLag k ≤ max 0 (max (integerLag n) (integerLag m)) +
        (((m : ℝ) - n) ^ 2 / (8 * n)) / Real.sqrt k := by
  intro n k m hn hnk hkm
  apply integerLag_le_endpoint_ceiling_add_curvature hn hnk hkm (le_max_left _ _)
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
  refine ⟨max M 0 + C / 8, ?_⟩
  intro k hk
  obtain ⟨n, hnS, m, hmS, hn, hnk, hkm, hgap⟩ := hmesh k hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hn0 : (0 : ℝ) < n := by positivity
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hsn : Real.sqrt (n : ℝ) ≤ Real.sqrt k := Real.sqrt_le_sqrt (by exact_mod_cast hnk)
  have hns : (n : ℝ) * Real.sqrt n ≤ (n : ℝ) * Real.sqrt k := by gcongr
  have hgap' : ((m : ℝ) - n) ^ 2 ≤ C * ((n : ℝ) * Real.sqrt k) :=
    hgap.trans (mul_le_mul_of_nonneg_left hns hC)
  have hquad : (((m : ℝ) - n) ^ 2 / (8 * n)) / Real.sqrt k ≤ C / 8 := by
    rw [div_le_iff₀ hsk, div_le_iff₀ (by positivity : (0 : ℝ) < 8 * n)]
    nlinarith only [hgap']
  have hcore := integerLag_le_endpoint_ceiling_add_curvature hn hnk hkm
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

/-- A sampling mesh whose logarithmic loss is paid by its explicit triangular prime mass. -/
def PrimeCompensatedLagMesh (S : Set ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 2 ≤ k →
    ∃ n ∈ S, ∃ m ∈ S, ∃ u v : ℝ,
      2 ≤ n ∧ n ≤ k ∧ k ≤ m ∧ 0 ≤ u ∧ 0 ≤ v ∧ u + v = 1 ∧
      (k : ℝ) = u * n + v * m ∧
      (u * n * Real.log n + v * m * Real.log m - k * Real.log k) -
        lagPrimeChordCharge m n m u v ≤ C * Real.sqrt k

/-- The geometric mesh receiver is contained in the explicit prime-compensated receiver. -/
theorem quadraticLagMesh_implies_primeCompensated :
    ∀ S : Set ℕ, QuadraticLagMesh S → PrimeCompensatedLagMesh S := by
  intro S hS
  obtain ⟨C, hC, hmesh⟩ := hS
  refine ⟨C / 8, by positivity, ?_⟩
  intro k hk
  obtain ⟨n, hnS, m, hmS, hn, hnk, hkm, hgap⟩ := hmesh k hk
  by_cases hnm : n = m
  · have hkn : k = n := by omega
    subst m
    subst k
    refine ⟨n, hnS, n, hmS, 1, 0, hn, le_rfl, le_rfl,
      by positivity, le_rfl, by ring, by ring, ?_⟩
    have hQ := lagPrimeChordCharge_nonneg n (n : ℝ) (n : ℝ)
      (by positivity : (0 : ℝ) ≤ 1) le_rfl
    simp only [one_mul, zero_mul, add_zero, sub_self, zero_sub]
    exact (neg_nonpos.mpr hQ).trans
      (show (0 : ℝ) ≤ C / 8 * Real.sqrt n by positivity)
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
  refine ⟨n, hnS, m, hmS, u, v, hn, hnk, hkm, hu, hv, huv, hmean, ?_⟩
  have hsn : Real.sqrt (n : ℝ) ≤ Real.sqrt k := Real.sqrt_le_sqrt (by exact_mod_cast hnk)
  have hgap' : ((m : ℝ) - n) ^ 2 ≤ C * ((n : ℝ) * Real.sqrt k) :=
    hgap.trans (mul_le_mul_of_nonneg_left (by gcongr) hC)
  have hQ := lagPrimeChordCharge_nonneg m (n : ℝ) (m : ℝ) hu hv
  calc _ ≤ u * n * Real.log n + v * m * Real.log m - k * Real.log k :=
      sub_le_self _ hQ
    _ ≤ u * v * ((m : ℝ) - n) ^ 2 / (2 * n) :=
      mul_log_chord_defect_le_of_lower_bound (by positivity : (0 : ℝ) < n)
        le_rfl (by exact_mod_cast (hnk.trans hkm)) hu hv huv hmean
    _ ≤ (1 / 4) * ((m : ℝ) - n) ^ 2 / (2 * n) := by gcongr
    _ = ((m : ℝ) - n) ^ 2 / (8 * n) := by ring
    _ ≤ C / 8 * Real.sqrt k := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * n)]
      nlinarith only [hgap']

/-- A bound on the prime-compensated mesh gives an explicit bound at every integer. -/
theorem integerLag_bddAbove_of_primeCompensatedMesh {S : Set ℕ}
    (hS : PrimeCompensatedLagMesh S) {M : ℝ} (hM : ∀ n ∈ S, integerLag n ≤ M) :
    ∃ B : ℝ, ∀ k : ℕ, 2 ≤ k → integerLag k ≤ B := by
  obtain ⟨C, _, hmesh⟩ := hS
  refine ⟨max M 0 + C, ?_⟩
  intro k hk
  obtain ⟨n, hnS, m, hmS, u, v, hn, hnk, hkm, hu, hv, huv, hmean, hdef⟩ := hmesh k hk
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have herror : ((u * n * Real.log n + v * m * Real.log m - k * Real.log k) -
      lagPrimeChordCharge m n m u v) / Real.sqrt k ≤ C := (div_le_iff₀ hsk).mpr hdef
  exact (integerLag_chord_prime_ceiling hn hnk hkm hu hv huv hmean
    (le_max_right M 0) ((hM n hnS).trans (le_max_left M 0))
    ((hM m hmS).trans (le_max_left M 0))).trans (add_le_add le_rfl herror)

/-- Every explicit prime-compensated mesh carries precisely the bounded-upper-lag RH law. -/
theorem primeCompensatedLagMesh_characterization :
    ∀ S : Set ℕ,
      (PrimeCompensatedLagMesh S ∧ ∃ M : ℝ, ∀ n ∈ S, integerLag n ≤ M) ↔
        (PrimeCompensatedLagMesh S ∧ RiemannHypothesis) := by
  intro S
  constructor
  · rintro ⟨hS, M, hM⟩
    exact ⟨hS, riemannHypothesis_iff_integerLag_bddAbove.mpr
      (integerLag_bddAbove_of_primeCompensatedMesh hS hM)⟩
  · rintro ⟨hS, hRH⟩
    refine ⟨hS, poleSharpConstant, fun n _ => ?_⟩
    exact (le_abs_self (integerLag n)).trans (abs_integerLag_le_of_riemannHypothesis hRH n)

end

end RHTower
