import GaloisForLFunctions.ArithmeticOrientationTheory.TheEvenFlipCreatesAnObstructionAtThePole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MultiplicativeWeightsPretendingToOneArePaidOnlyByAVanishingLocalFactor

/-!
# An orientation-faithful norm over the smooth power and over multiplicative weights

Over the odd squarefree weight `o(d) = 1_{d odd squarefree} d^{−ε}`, `o` vanishes on even integers,
so for any four-free kernel `k = k_o + δ₂ ⋆ k_e` the even flip acts directly on the kernel by
`evenFlip (k ⋆ o) = flipKernelOf k ⋆ o` with `flipKernelOf k = k_o + k_e − δ₂ ⋆ k_e`
(`AnOrientationFaithfulNormOverTheOddSquarefreeWeight`).

Over the smooth power `u(d) = d^{−ε}` (`dampedSignWeight unitSign ε`) and over multiplicative
weights `f(d) d^{−ε}`, the naive kernel flip `flipKernelOf` does **not** commute with convolution:
already at `k = δ₁`, `flipKernelOf δ₁ = δ₁` while `evenFlip (δ₁ ⋆ u)(1) = 1 + 2^{−ε} ≠ 1`, and for
a multiplicative weight `f` with `f(2) ≠ 0`, `evenFlip (f d^{−ε})(1) = 1 + f(2) 2^{−ε} ≠ 1` leaves
the multiplicative class.

This module resolves Open Problem 4 of Arithmetic Orientation Theory by constructing the exact
orientation-faithful norm, kernel involution, and orientation coordinates over the smooth power
`u(d) = d^{−ε}` and over multiplicative weights `f(d) d^{−ε}`:

1. **The orientation-faithful norm and paid hyperplane over the smooth power `u(d) = d^{−ε}` (§1):**
   - For any finite kernel `k` on `[1, J]` with `poleValue k J ε = 0`, every receiver energy of
     `k ⋆ u` is bounded by `smoothPowerReceiverConst ε * (∑_{j=1}^J |k(j)| j^ε)²`
     (`weightPronicEnergy_dirichletConv_unit_le_finite`), where
     `smoothPowerReceiverConst ε = 36 ∑_{n ≥ 1} n^{2/(2+ε) − 2}`.
   - Via hyperplane truncations `oddSqfTrunc ε k J`, for every admissible kernel `k`
     (`OrientAdmissible ε k`, `orientNorm ε k = ∑_j |k(j)| j^ε < ∞`) with `polePairing ε k = 0`,
     `E_T(k ⋆ u) ≤ 4 · smoothPowerReceiverConst ε · orientNorm ε k ^ 2` at every cutoff `T`
     (`weightPronicEnergy_dirichletConv_unit_le`), and payment over `u` is the closed hyperplane
     `polePairing ε k = 0` (`receiverBounded_dirichletConv_unit_iff_admissible`).

2. **Exact smooth-power flip involution on all kernels and continuity in `orientNorm ε` (§2):**
   - Because `u(2m) = 2^{−ε} u_odd(m)` on odd `m`, for **every** kernel `k : ℕ → ℝ` (with no
     four-free restriction) the even part of `k ⋆ u` is
     `evenPartWeight (k ⋆ u) = smoothEvenTrace ε k ⋆ u_odd = smoothEvenKernel ε k ⋆ u`
     (`evenPartWeight_dirichletConv_unit_eq_oddAF`, `evenPartWeight_dirichletConv_unit_eq`), where
     `smoothEvenTrace ε k = 2^{−ε} k_o + k_e` and
     `smoothEvenKernel ε k = (δ₁ − 2^{−ε} δ₂) ⋆ smoothEvenTrace ε k`.
   - Consequently, for **every** kernel `k : ℕ → ℝ`,
     `evenFlip (k ⋆ u) = smoothFlipKernel ε k ⋆ u` (`evenFlip_dirichletConv_unit`), where
     `smoothFlipKernel ε k = k + (δ₁ − 2 δ₂) ⋆ smoothEvenKernel ε k`.
   - Unlike `flipKernelOf` (which is an involution only on four-free kernels), `smoothFlipKernel ε`
     negates `smoothEvenTrace ε` and `smoothEvenKernel ε` on **all** kernels
     (`smoothEvenTrace_smoothFlipKernel`, `smoothEvenKernel_smoothFlipKernel`) and is therefore an
     exact involution `smoothFlipKernel ε (smoothFlipKernel ε k) = k` on **all** `k : ℕ → ℝ`
     (`smoothFlipKernel_smoothFlipKernel`), bounded in `orientNorm ε` by
     `orientNorm ε (smoothFlipKernel ε k) ≤ 21 · orientNorm ε k` (`orientNorm_smoothFlipKernel_le`).

3. **Orientation coordinates over the smooth power `u(d) = d^{−ε}` (§3):**
   - With `smoothEvenPolePairing ε k := polePairing ε (smoothEvenKernel ε k) =
     (1 / 2) * (2^{−ε} polePairing ε k_o + polePairing ε k_e)` (`smoothEvenPolePairing_eq`), the
     smooth flip acts on `(P, P_{smooth,e})` by
     `(P, P_{smooth,e}) ↦ (P + (1 − 2^ε) P_{smooth,e}, −P_{smooth,e})`
     (`polePairing_smoothFlipKernel`, `smoothEvenPolePairing_smoothFlipKernel`).
   - Both `k ⋆ u` and `evenFlip (k ⋆ u)` are paid iff `polePairing ε k = 0 ∧ smoothEvenPolePairing ε k = 0`
     (`receiverBounded_and_evenFlip_dirichletConv_unit_iff`), with both receiver energies bounded by
     `1764 · smoothPowerReceiverConst ε · orientNorm ε k ^ 2`
     (`weightPronicEnergy_evenFlip_dirichletConv_unit_le`). On four-free kernels with `P(k) = 0`,
     `smoothEvenPolePairing ε k = (1 / 4) polePairing ε k_e`
     (`smoothEvenPolePairing_of_fourFree_of_polePairing_eq_zero`).

4. **Multiplicative weights `f(d) d^{−ε}` and the 2-local orientation coordinate (§4):**
   - For any multiplicative `f : ArithmeticFunction ℝ`, `evenFlip (f d^{−ε})(1) = 1 + f(2) 2^{−ε}`
     and `evenFlip (f d^{−ε})(2) = −f(2) 2^{−ε}`, so `evenFlip (f d^{−ε})` stays normalized at `1`
     iff `f(2) = 0` (`evenFlip_dampedSignWeight_multiplicative_one_eq_one_iff`).
   - Writing `f(d) d^{−ε} = k_f ⋆ u` via the Möbius kernel `k_f = dampedSignWeight ⇑(f * μR) ε`
     (`dampedSignWeight_eq_dirichletConv_moebiusKernel_unit`), multiplicativity forces
     `(f * μR)(2m) = (f(2) − 1)(f * μR)(m)` on odd `m`, so the `2^{−ε} k_{f,o}` term cancels
     identically in `smoothEvenTrace ε k_f`:
     `smoothEvenTrace ε k_f = f(2) 2^{−ε} • oddPartKernel k_f`
     (`smoothEvenTrace_moebiusKernel_multiplicative`).
   - Hence the second orientation coordinate of a multiplicative weight is read directly by `f(2)`
     and the odd Euler factor `polePairing ε (oddPartKernel k_f)`:
     `smoothEvenPolePairing ε k_f = (1 / 2) * f(2) * 2^{−ε} * polePairing ε (oddPartKernel k_f)`
     (`smoothEvenPolePairing_moebiusKernel_multiplicative`), and when
     `polePairing ε (oddPartKernel k_f) ≠ 0`, both `f d^{−ε}` and `evenFlip (f d^{−ε})` are paid
     iff `polePairing ε k_f = 0 ∧ f(2) = 0` (`receiverBounded_and_evenFlip_multiplicative_iff`).
   - In particular, for any admissible multiplicative weight with `f(2) = 1` (such as a weight
     pretending to `1` on the primes) and `polePairing ε (oddPartKernel k_f) ≠ 0`, `f d^{−ε}` and
     its companion `evenFlip (f d^{−ε})` can **never** both be paid
     (`not_receiverBounded_and_evenFlip_of_apply_two_ne_zero`).
-/

open Finset Filter Topology
open scoped BigOperators
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

local notation "μR" => ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)

/-! ### 1. The receiver constant and paid hyperplane over the smooth power `u(d) = d^{−ε}` -/

/-- The receiver constant `36 ∑_{n ≥ 1} n^{2/(2+ε) − 2}` over the smooth power `u(d) = d^{−ε}`. -/
def smoothPowerReceiverConst (ε : ℝ) : ℝ :=
  36 * ∑' n : ℕ, (n : ℝ) ^ (2 * (1 / (2 + ε)) - 2)

theorem smoothPowerReceiverConst_nonneg (ε : ℝ) : 0 ≤ smoothPowerReceiverConst ε :=
  mul_nonneg (by norm_num) (tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- **The quantitative pole law over the smooth power `u(d) = d^{−ε}` for finite kernels:**
a kernel on `[1, J]` with vanishing pole value has every receiver energy of `k ⋆ d^{−ε}` at most
`smoothPowerReceiverConst ε * (∑_{j=1}^J |k(j)| j^ε)²`. -/
theorem weightPronicEnergy_dirichletConv_unit_le_finite {ε : ℝ} (hε : 0 < ε) {k : ℕ → ℝ}
    {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) (hK : poleValue k J ε = 0) (T : ℕ) :
    weightPronicEnergy (RHTower.dirichletConv k (dampedSignWeight unitSign ε))
        (∑' d : ℕ, RHTower.dirichletConv k (dampedSignWeight unitSign ε) d / d) T ≤
      smoothPowerReceiverConst ε * (∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε) ^ 2 := by
  set L := ∑ j ∈ Icc 1 J, |undampedKernel k ε j|
  have hLeq : L = ∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε := sum_congr rfl fun j _ => by
    rw [undampedKernel, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) ε)]
  have hL : 0 ≤ L := sum_nonneg fun j _ => abs_nonneg _
  have hw_eq : RHTower.dirichletConv k (dampedSignWeight unitSign ε) =
      dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) unitSign) ε :=
    funext (dirichletConv_damped_eq k unitSign ε)
  have hE := weightPronicEnergy_dampedSign_le hL hε (abs_sum_range_dirichletConv_unit_le hkJ hK) T
  rw [hw_eq, ← hLeq]
  calc weightPronicEnergy
        (dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) unitSign) ε)
        (∑' d : ℕ, dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) unitSign) ε d / d) T
      ≤ 36 * L ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (1 / (2 + ε)) - 2) := hE
    _ = smoothPowerReceiverConst ε * L ^ 2 := by unfold smoothPowerReceiverConst; ring

/-- The mean of `h ⋆ d^{−ε}` is the product of the means. -/
theorem tsum_dirichletConv_unit_div {ε : ℝ} (hε : 0 < ε) {h : ℕ → ℝ}
    (hh : Summable fun j : ℕ => |h j / j|) :
    ∑' d : ℕ, RHTower.dirichletConv h (dampedSignWeight unitSign ε) d / d =
      (∑' j : ℕ, h j / j) * ∑' d : ℕ, dampedSignWeight unitSign ε d / d :=
  (hasSum_dirichletConv_div hh.of_abs.hasSum (summable_abs_smoothPower_div hε).of_abs.hasSum hh
    (summable_abs_smoothPower_div hε)).tsum_eq

theorem dirichletConv_unit_oddSqfTrunc (ε : ℝ) (k : ℕ → ℝ) {J d : ℕ} (hd : 1 ≤ d) (hdJ : d ≤ J) :
    RHTower.dirichletConv (oddSqfTrunc ε k J) (dampedSignWeight unitSign ε) d =
      RHTower.dirichletConv k (dampedSignWeight unitSign ε) d -
        poleValue k J ε * dampedSignWeight unitSign ε d := by
  unfold RHTower.dirichletConv oddSqfTrunc
  have h : ∀ e ∈ d.divisors, ((if e ∈ Icc 1 J then k e else 0) -
      (if e = 1 then poleValue k J ε else 0)) * dampedSignWeight unitSign ε (d / e) =
      k e * dampedSignWeight unitSign ε (d / e) -
        if e = 1 then poleValue k J ε * dampedSignWeight unitSign ε (d / e) else 0 :=
    fun e he => by
      have h1 := Nat.pos_of_mem_divisors he
      have h2 := Nat.divisor_le he
      rw [if_pos (mem_Icc.2 ⟨h1, h2.trans hdJ⟩), sub_mul]
      split_ifs <;> simp
  rw [sum_congr rfl h, sum_sub_distrib, sum_ite_eq' d.divisors 1,
    if_pos (Nat.one_mem_divisors.2 (by omega)), Nat.div_one]

theorem tendsto_mean_unitTrunc {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) (hP : polePairing ε k = 0) :
    Tendsto (fun J => (∑ j ∈ Icc 1 J, k j / j - poleValue k J ε) *
        ∑' d : ℕ, dampedSignWeight unitSign ε d / d) atTop
      (𝓝 (∑' d : ℕ, RHTower.dirichletConv k (dampedSignWeight unitSign ε) d / d)) := by
  rw [tsum_dirichletConv_unit_div hε (hk.summable_abs_div hε)]
  refine Tendsto.mul_const _ ?_
  have h := (tendsto_sum_Icc (hk.summable_abs_div hε).of_abs (by simp)).sub
    (tendsto_poleValue hε hε2 hk)
  rwa [hP, sub_zero] at h

theorem truncEnergy_unitTrunc_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) {T J : ℕ} (hJ1 : 1 ≤ J) (hJT : T ≤ J) :
    truncEnergy (RHTower.dirichletConv k (dampedSignWeight unitSign ε))
        (dampedSignWeight unitSign ε) T (poleValue k J ε)
        ((∑ j ∈ Icc 1 J, k j / j - poleValue k J ε) *
          ∑' d : ℕ, dampedSignWeight unitSign ε d / d) ≤
      4 * smoothPowerReceiverConst ε * orientNorm ε k ^ 2 := by
  have hfin := weightPronicEnergy_dirichletConv_unit_le_finite hε (oddSqfTrunc_support hJ1)
    (poleValue_oddSqfTrunc ε k hJ1) T
  have hsum : Summable fun j : ℕ => |oddSqfTrunc ε k J j / j| := by
    refine summable_of_ne_finset_zero (s := Icc 1 J) fun j hj => ?_
    unfold oddSqfTrunc
    rw [if_neg hj]
    by_cases h1 : j = 1
    · exact absurd (by simp [h1, hJ1]) hj
    · rw [if_neg h1]; simp
  have hmeanJ := tsum_dirichletConv_unit_div hε hsum
  rw [tsum_oddSqfTrunc_div] at hmeanJ
  have hE := weightPronicEnergy_eq_truncEnergy
    (c := RHTower.dirichletConv k (dampedSignWeight unitSign ε))
    (o := dampedSignWeight unitSign ε)
    (h := RHTower.dirichletConv (oddSqfTrunc ε k J) (dampedSignWeight unitSign ε))
    (T := T) (a := poleValue k J ε)
    (fun d hd hdT => dirichletConv_unit_oddSqfTrunc ε k hd (hdT.trans hJT))
    ((∑ j ∈ Icc 1 J, k j / j - poleValue k J ε) * ∑' d : ℕ, dampedSignWeight unitSign ε d / d)
  rw [← hE, ← hmeanJ]
  refine hfin.trans ?_
  have h2 := sum_abs_oddSqfTrunc_le hε hε2 hk hJ1
  have h0 : 0 ≤ ∑ j ∈ Icc 1 J, |oddSqfTrunc ε k J j| * (j : ℝ) ^ ε :=
    sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  calc smoothPowerReceiverConst ε * (∑ j ∈ Icc 1 J, |oddSqfTrunc ε k J j| * (j : ℝ) ^ ε) ^ 2
      ≤ smoothPowerReceiverConst ε * (2 * orientNorm ε k) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h2 2) (smoothPowerReceiverConst_nonneg ε)
    _ = 4 * smoothPowerReceiverConst ε * orientNorm ε k ^ 2 := by ring

/-- **The receiver is bounded on the paid hyperplane over the smooth power `u(d) = d^{−ε}`:**
for every admissible kernel `k` (`OrientAdmissible ε k`) with `polePairing ε k = 0`, every receiver
energy of `k ⋆ d^{−ε}` is at most `4 * smoothPowerReceiverConst ε * orientNorm ε k ^ 2`. -/
theorem weightPronicEnergy_dirichletConv_unit_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk : OrientAdmissible ε k) (hP : polePairing ε k = 0) (T : ℕ) :
    weightPronicEnergy (RHTower.dirichletConv k (dampedSignWeight unitSign ε))
        (∑' d : ℕ, RHTower.dirichletConv k (dampedSignWeight unitSign ε) d / d) T ≤
      4 * smoothPowerReceiverConst ε * orientNorm ε k ^ 2 := by
  have hP0 : Tendsto (fun J => poleValue k J ε) atTop (𝓝 0) := hP ▸ tendsto_poleValue hε hε2 hk
  have hlim := ((continuous_truncEnergy
    (RHTower.dirichletConv k (dampedSignWeight unitSign ε))
    (dampedSignWeight unitSign ε) T).tendsto _).comp
    (hP0.prodMk_nhds (tendsto_mean_unitTrunc hε hε2 hk hP))
  rw [weightPronicEnergy_eq_truncEnergy
    (c := RHTower.dirichletConv k (dampedSignWeight unitSign ε))
    (o := dampedSignWeight unitSign ε) (a := 0) (fun d _ _ => by ring)]
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨max T 1, fun J hJ =>
    truncEnergy_unitTrunc_le hε hε2 hk ((le_max_right _ _).trans hJ) ((le_max_left _ _).trans hJ)⟩)

/-- **Payment over the smooth power `d^{−ε}` is the closed hyperplane `polePairing ε k = 0`**,
for every admissible kernel `k`. -/
theorem receiverBounded_dirichletConv_unit_iff_admissible {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) ↔
      polePairing ε k = 0 := by
  constructor
  · intro hB
    by_contra hK
    exact not_receiverBounded_dirichletConv_of_drift_critical hε hε2
      (q := dampedSignWeight unitSign ε)
      (fun d => by simp [dampedSignWeight, unitSign, Real.rpow_nonneg])
      (K := 1) (fun d => by simp [dampedSignWeight, unitSign, abs_of_nonneg, Real.rpow_nonneg])
      (κ := (2 : ℝ) ^ (-(1 + ε))) (by positivity)
      (by filter_upwards [eventually_ge_atTop 1] with n hn using unit_drift hε.le hn)
      (hk.criticalWiener hε) hK hB
  · intro hP
    exact ⟨_, weightPronicEnergy_dirichletConv_unit_le hε hε2 hk hP⟩

/-! ### 2. Exact smooth-power flip involution on all kernels and continuity in `orientNorm ε` -/

/-- Over the smooth power `u(d) = d^{−ε}`, the `o`-kernel flip `flipKernelOf` does **not** commute
with `evenFlip`: at `k = δ₁` (`unitKernel`), `flipKernelOf δ₁ = δ₁` has `(flipKernelOf δ₁ ⋆ u)(1) = 1`,
whereas `evenFlip (δ₁ ⋆ u)(1) = 1 + 2^{−ε} ≠ 1`. -/
theorem evenFlip_dirichletConv_unit_unitKernel_ne (ε : ℝ) :
    flipKernelOf unitKernel = unitKernel ∧
    evenFlip (RHTower.dirichletConv unitKernel (dampedSignWeight unitSign ε)) 1 =
      1 + (2 : ℝ) ^ (-ε) ∧
    RHTower.dirichletConv (flipKernelOf unitKernel) (dampedSignWeight unitSign ε) 1 = 1 ∧
    evenFlip (RHTower.dirichletConv unitKernel (dampedSignWeight unitSign ε)) 1 ≠
      RHTower.dirichletConv (flipKernelOf unitKernel) (dampedSignWeight unitSign ε) 1 := by
  have hflip_unit : flipKernelOf unitKernel = unitKernel := by
    funext j
    unfold flipKernelOf oddPartKernel evenPartWeight shiftTwo unitKernel
    have h2 : ∀ m : ℕ, 2 * m ≠ 1 := fun m => by omega
    by_cases hj1 : j = 1
    · subst hj1; norm_num
    · simp [hj1, h2]
  have hconv1 : RHTower.dirichletConv unitKernel (dampedSignWeight unitSign ε) 1 = 1 := by
    rw [dirichletConv_unitKernel _ (by decide)]
    simp [dampedSignWeight, unitSign]
  have hconv2 : RHTower.dirichletConv unitKernel (dampedSignWeight unitSign ε) 2 =
      (2 : ℝ) ^ (-ε) := by
    rw [dirichletConv_unitKernel _ (by decide)]
    simp [dampedSignWeight, unitSign]
  have hev1 : evenFlip (RHTower.dirichletConv unitKernel (dampedSignWeight unitSign ε)) 1 =
      1 + (2 : ℝ) ^ (-ε) := by
    rw [evenFlip_apply, if_pos rfl, hconv1, Nat.mul_one, hconv2]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by norm_num) (-ε)
  refine ⟨hflip_unit, hev1, by rw [hflip_unit, hconv1], ?_⟩
  rw [hev1, hflip_unit, hconv1]
  linarith

/-- The **smooth even-part trace** `2^{−ε} k_o + k_e` of a kernel `k` over `d^{−ε}`:
because `d^{−ε}` is nonzero on even integers (`(2m)^{−ε} = 2^{−ε} m^{−ε}`), both the odd part `k_o`
and the even part `k_e` of `k` feed into the even values `(k ⋆ d^{−ε})(2m)` at odd `m`. -/
def smoothEvenTrace (ε : ℝ) (k : ℕ → ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ (-ε) * oddPartKernel k j + evenPartWeight k j

/-- The **smooth even-part kernel** `(δ₁ − 2^{−ε} δ₂) ⋆ (2^{−ε} k_o + k_e)` whose convolution with
`d^{−ε}` equals `evenPartWeight (k ⋆ d^{−ε})`. -/
def smoothEvenKernel (ε : ℝ) (k : ℕ → ℝ) (j : ℕ) : ℝ :=
  smoothEvenTrace ε k j - (2 : ℝ) ^ (-ε) * shiftTwo (smoothEvenTrace ε k) j

/-- The **smooth-power flip kernel** `k + (δ₁ − 2 δ₂) ⋆ smoothEvenKernel ε k`, which represents the
even flip `evenFlip (k ⋆ d^{−ε}) = smoothFlipKernel ε k ⋆ d^{−ε}` for **every** kernel `k : ℕ → ℝ`. -/
def smoothFlipKernel (ε : ℝ) (k : ℕ → ℝ) (j : ℕ) : ℝ :=
  k j + smoothEvenKernel ε k j - 2 * shiftTwo (smoothEvenKernel ε k) j

theorem smoothEvenTrace_of_even (ε : ℝ) (k : ℕ → ℝ) {j : ℕ} (hj : 2 ∣ j) :
    smoothEvenTrace ε k j = 0 := by
  unfold smoothEvenTrace
  rw [oddPartKernel_of_even k hj, evenPartWeight_of_even k hj, mul_zero, add_zero]

theorem smoothEvenTrace_zero (ε : ℝ) (k : ℕ → ℝ) : smoothEvenTrace ε k 0 = 0 :=
  smoothEvenTrace_of_even ε k (dvd_zero 2)

theorem smoothEvenKernel_zero (ε : ℝ) (k : ℕ → ℝ) : smoothEvenKernel ε k 0 = 0 := by
  unfold smoothEvenKernel shiftTwo
  simp [smoothEvenTrace_zero]

/-- On any integer `n` not divisible by `4`, `f n = oddPartKernel f n + shiftTwo (evenPartWeight f) n`. -/
theorem eq_oddPart_add_shiftTwo_of_not_four_dvd (f : ℕ → ℝ) {n : ℕ} (hn4 : ¬ 4 ∣ n) :
    f n = oddPartKernel f n + shiftTwo (evenPartWeight f) n := by
  unfold oddPartKernel shiftTwo evenPartWeight
  by_cases h : n % 2 = 1
  · rw [if_pos h, if_neg (by omega), add_zero]
  · have h2 : 2 ∣ n := by omega
    have hodd : (n / 2) % 2 = 1 := by omega
    rw [if_neg h, if_pos h2, if_pos hodd, zero_add, Nat.mul_div_cancel' h2]

/-- The Dirichlet convolution of two odd-supported functions vanishes on all even integers. -/
theorem dirichletConv_of_even_of_oddSupported {a b : ℕ → ℝ}
    (ha : ∀ j, 2 ∣ j → a j = 0) (hb : ∀ j, 2 ∣ j → b j = 0) {n : ℕ} (hn : 2 ∣ n) :
    RHTower.dirichletConv a b n = 0 := by
  unfold RHTower.dirichletConv
  refine sum_eq_zero fun j hj => ?_
  by_cases h2 : 2 ∣ j
  · rw [ha j h2, zero_mul]
  · have hdiv : 2 ∣ n / j := by
      obtain ⟨m, hm⟩ := Nat.dvd_of_mem_divisors hj
      have hj0 := Nat.pos_of_mem_divisors hj
      rw [hm, Nat.mul_div_cancel_left m hj0]
      rw [hm] at hn
      exact (Nat.Prime.dvd_mul Nat.prime_two).mp hn |>.resolve_left h2
    rw [hb (n / j) hdiv, mul_zero]

/-- The Dirichlet convolution of two `shiftTwo`-dilated functions vanishes on all integers not
divisible by `4`. -/
theorem dirichletConv_shiftTwo_shiftTwo_of_not_four_dvd (a b : ℕ → ℝ) {n : ℕ} (hn4 : ¬ 4 ∣ n) :
    RHTower.dirichletConv (shiftTwo a) (shiftTwo b) n = 0 := by
  unfold RHTower.dirichletConv
  refine sum_eq_zero fun j hj => ?_
  by_cases h2 : 2 ∣ j
  · have hnot2 : ¬ 2 ∣ (n / j) := by
      intro hdiv
      obtain ⟨u, rfl⟩ := h2
      obtain ⟨v, hv⟩ := hdiv
      have hmul : 2 * u * (n / (2 * u)) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hj)
      rw [hv] at hmul
      exact hn4 ⟨u * v, by linarith⟩
    rw [shiftTwo_of_not_dvd b hnot2, mul_zero]
  · rw [shiftTwo_of_not_dvd a h2, zero_mul]

theorem oddPartKernel_dampedUnit (ε : ℝ) :
    oddPartKernel (dampedSignWeight unitSign ε) = dampedSignWeight ⇑oddAF ε := by
  funext j
  unfold oddPartKernel dampedSignWeight unitSign
  rw [oddAF_apply]
  by_cases h : j % 2 = 1
  · have h2 : ¬ 2 ∣ j := by omega
    simp [h, h2]
  · have h2 : 2 ∣ j := by omega
    simp [h, h2]

theorem evenPartWeight_dampedUnit (ε : ℝ) :
    evenPartWeight (dampedSignWeight unitSign ε) =
      fun j => (2 : ℝ) ^ (-ε) * dampedSignWeight ⇑oddAF ε j := by
  funext j
  unfold evenPartWeight dampedSignWeight unitSign
  rw [oddAF_apply]
  by_cases h : j % 2 = 1
  · have h2 : ¬ 2 ∣ j := by omega
    rw [if_pos h, if_pos h2, one_mul, one_mul, Nat.cast_mul, Nat.cast_two,
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg j)]
  · have h2 : 2 ∣ j := by omega
    simp [h, h2]

theorem dampedOddAF_of_even (ε : ℝ) {j : ℕ} (hj : 2 ∣ j) :
    dampedSignWeight ⇑oddAF ε j = 0 := by
  unfold dampedSignWeight
  rw [oddAF_apply]
  simp [hj]

/-- **Exact formula for the even part of `k ⋆ d^{−ε}` over `1_{odd} d^{−ε}`:**
for **every** kernel `k : ℕ → ℝ` (without any four-free hypothesis),
`evenPartWeight (k ⋆ d^{−ε}) = smoothEvenTrace ε k ⋆ (1_{odd} d^{−ε})`. -/
theorem evenPartWeight_dirichletConv_unit_eq_oddAF (ε : ℝ) (k : ℕ → ℝ) :
    evenPartWeight (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) =
      RHTower.dirichletConv (smoothEvenTrace ε k) (dampedSignWeight ⇑oddAF ε) := by
  set u := dampedSignWeight unitSign ε
  set uo := dampedSignWeight ⇑oddAF ε
  funext m
  by_cases hm : m % 2 = 1
  · have hm0 : m ≠ 0 := by omega
    have h2m0 : 2 * m ≠ 0 := by omega
    have hnot4 : ¬ 4 ∣ 2 * m := by omega
    have h_eq : RHTower.dirichletConv k u (2 * m) =
        RHTower.dirichletConv (fun j => oddPartKernel k j + shiftTwo (evenPartWeight k) j)
          (fun j => oddPartKernel u j + shiftTwo (evenPartWeight u) j) (2 * m) := by
      unfold RHTower.dirichletConv
      refine sum_congr rfl fun j hj => ?_
      have hj_dvd : j ∣ 2 * m := Nat.dvd_of_mem_divisors hj
      have hq_dvd : (2 * m) / j ∣ 2 * m := Nat.div_dvd_of_dvd hj_dvd
      have hj4 : ¬ 4 ∣ j := fun h4 => hnot4 (dvd_trans h4 hj_dvd)
      have hq4 : ¬ 4 ∣ (2 * m) / j := fun h4 => hnot4 (dvd_trans h4 hq_dvd)
      dsimp only
      rw [← eq_oddPart_add_shiftTwo_of_not_four_dvd k hj4,
        ← eq_oddPart_add_shiftTwo_of_not_four_dvd u hq4]
    have h1 : RHTower.dirichletConv (oddPartKernel k) (oddPartKernel u) (2 * m) = 0 := by
      rw [oddPartKernel_dampedUnit]
      exact dirichletConv_of_even_of_oddSupported (fun j hj => oddPartKernel_of_even k hj)
        (fun j hj => dampedOddAF_of_even ε hj) (dvd_mul_right 2 m)
    have h2 : RHTower.dirichletConv (oddPartKernel k) (shiftTwo (evenPartWeight u)) (2 * m) =
        (2 : ℝ) ^ (-ε) * RHTower.dirichletConv (oddPartKernel k) uo m := by
      rw [dirichletConv_comm, dirichletConv_shiftTwo _ _ h2m0, if_pos (dvd_mul_right 2 m),
        Nat.mul_div_cancel_left m two_pos, evenPartWeight_dampedUnit, dirichletConv_comm]
      unfold RHTower.dirichletConv
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    have h3 : RHTower.dirichletConv (shiftTwo (evenPartWeight k)) (oddPartKernel u) (2 * m) =
        RHTower.dirichletConv (evenPartWeight k) uo m := by
      rw [oddPartKernel_dampedUnit, dirichletConv_shiftTwo _ _ h2m0,
        if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m two_pos]
    have h4 : RHTower.dirichletConv (shiftTwo (evenPartWeight k))
        (shiftTwo (evenPartWeight u)) (2 * m) = 0 :=
      dirichletConv_shiftTwo_shiftTwo_of_not_four_dvd _ _ hnot4
    unfold evenPartWeight
    rw [if_pos hm, h_eq, dirichletConv_add_left]
    have h_add_right : ∀ a : ℕ → ℝ,
        RHTower.dirichletConv a (fun j => oddPartKernel u j + shiftTwo (evenPartWeight u) j) (2 * m) =
          RHTower.dirichletConv a (oddPartKernel u) (2 * m) +
            RHTower.dirichletConv a (shiftTwo (evenPartWeight u)) (2 * m) := fun a => by
      rw [dirichletConv_comm, dirichletConv_add_left,
        dirichletConv_comm (oddPartKernel u), dirichletConv_comm (shiftTwo (evenPartWeight u))]
    rw [h_add_right, h_add_right, h1, h2, h3, h4, zero_add, add_zero]
    unfold smoothEvenTrace RHTower.dirichletConv
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  · have hm2 : 2 ∣ m := by omega
    have hlhs : evenPartWeight (RHTower.dirichletConv k u) m = 0 := by
      unfold evenPartWeight; rw [if_neg hm]
    have hrhs : RHTower.dirichletConv (smoothEvenTrace ε k) uo m = 0 :=
      dirichletConv_of_even_of_oddSupported (fun j hj => smoothEvenTrace_of_even ε k hj)
        (fun j hj => dampedOddAF_of_even ε hj) hm2
    rw [hlhs, hrhs]

/-- `smoothEvenKernel ε k` equals `localFactorKernel 2 (2^{−ε}) ⋆ smoothEvenTrace ε k`. -/
theorem smoothEvenKernel_eq_dirichletConv_localFactor (ε : ℝ) (k : ℕ → ℝ) :
    smoothEvenKernel ε k =
      RHTower.dirichletConv (localFactorKernel 2 ((2 : ℝ) ^ (-ε))) (smoothEvenTrace ε k) := by
  funext j
  rcases eq_or_ne j 0 with rfl | hj
  · simp [smoothEvenKernel_zero, RHTower.dirichletConv]
  · rw [dirichletConv_localFactorKernel Nat.prime_two _ _ hj]
    unfold smoothEvenKernel shiftTwo
    ring

/-- **Exact kernel representation of `evenPartWeight (k ⋆ d^{−ε})` over the smooth power `d^{−ε}`:**
for **every** kernel `k : ℕ → ℝ`,
`evenPartWeight (k ⋆ d^{−ε}) = smoothEvenKernel ε k ⋆ d^{−ε}`. -/
theorem evenPartWeight_dirichletConv_unit_eq (ε : ℝ) (k : ℕ → ℝ) :
    evenPartWeight (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) =
      RHTower.dirichletConv (smoothEvenKernel ε k) (dampedSignWeight unitSign ε) := by
  rw [evenPartWeight_dirichletConv_unit_eq_oddAF, oddDamped_eq_localFactor_conv,
    ← dirichletConv_assoc, ← dirichletConv_comm (localFactorKernel 2 ((2 : ℝ) ^ (-ε))),
    ← smoothEvenKernel_eq_dirichletConv_localFactor]

/-- **Exact kernel representation of `evenFlip (k ⋆ d^{−ε})` over the smooth power `d^{−ε}`:**
for **every** kernel `k : ℕ → ℝ` (with no four-free hypothesis),
`evenFlip (k ⋆ d^{−ε}) = smoothFlipKernel ε k ⋆ d^{−ε}`. -/
theorem evenFlip_dirichletConv_unit (ε : ℝ) (k : ℕ → ℝ) :
    evenFlip (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) =
      RHTower.dirichletConv (smoothFlipKernel ε k) (dampedSignWeight unitSign ε) := by
  set u := dampedSignWeight unitSign ε
  set ek := smoothEvenKernel ε k
  funext d
  change RHTower.dirichletConv k u d +
      localFactorWeight (evenPartWeight (RHTower.dirichletConv k u)) 2 2 d =
    RHTower.dirichletConv (smoothFlipKernel ε k) u d
  rw [evenPartWeight_dirichletConv_unit_eq]
  have hshift : (if 2 ∣ d then RHTower.dirichletConv ek u (d / 2) else 0) =
      RHTower.dirichletConv (shiftTwo ek) u d := by
    rcases eq_or_ne d 0 with rfl | hd
    · simp [RHTower.dirichletConv]
    · exact (dirichletConv_shiftTwo ek u hd).symm
  have h2shift : RHTower.dirichletConv (fun j => 2 * shiftTwo ek j) u d =
      2 * RHTower.dirichletConv (shiftTwo ek) u d := by
    unfold RHTower.dirichletConv
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  unfold localFactorWeight smoothFlipKernel
  rw [dirichletConv_add_sub_left, h2shift, ← hshift]
  ring

/-- **Pointwise negation of `smoothEvenTrace` under `smoothFlipKernel`:**
for **every** `ε : ℝ` and **every** kernel `k : ℕ → ℝ` (without any four-free hypothesis),
`smoothEvenTrace ε (smoothFlipKernel ε k) = -smoothEvenTrace ε k`. -/
theorem smoothEvenTrace_smoothFlipKernel (ε : ℝ) (k : ℕ → ℝ) :
    smoothEvenTrace ε (smoothFlipKernel ε k) = fun j => -smoothEvenTrace ε k j := by
  funext j
  by_cases hj : j % 2 = 1
  · have hj2 : ¬ 2 ∣ j := by omega
    have hshift_odd : shiftTwo (smoothEvenKernel ε k) j = 0 :=
      shiftTwo_of_not_dvd (smoothEvenKernel ε k) hj2
    have hek_odd : smoothEvenKernel ε k j = smoothEvenTrace ε k j := by
      unfold smoothEvenKernel
      rw [shiftTwo_of_not_dvd (smoothEvenTrace ε k) hj2, mul_zero, sub_zero]
    have hodd_flip : oddPartKernel (smoothFlipKernel ε k) j =
        oddPartKernel k j + smoothEvenTrace ε k j := by
      unfold oddPartKernel smoothFlipKernel
      rw [if_pos hj, if_pos hj, hek_odd, hshift_odd, mul_zero, sub_zero]
    have ht_2j : smoothEvenTrace ε k (2 * j) = 0 :=
      smoothEvenTrace_of_even ε k (dvd_mul_right 2 j)
    have hek_2j : smoothEvenKernel ε k (2 * j) = -(2 : ℝ) ^ (-ε) * smoothEvenTrace ε k j := by
      unfold smoothEvenKernel
      rw [ht_2j, shiftTwo_two_mul, zero_sub]
      ring
    have heven_flip : evenPartWeight (smoothFlipKernel ε k) j =
        evenPartWeight k j - ((2 : ℝ) ^ (-ε) + 2) * smoothEvenTrace ε k j := by
      unfold evenPartWeight smoothFlipKernel
      rw [if_pos hj, if_pos hj, hek_2j, shiftTwo_two_mul, hek_odd]
      ring
    unfold smoothEvenTrace
    rw [hodd_flip, heven_flip]
    unfold smoothEvenTrace
    ring
  · have hj2 : 2 ∣ j := by omega
    rw [smoothEvenTrace_of_even ε (smoothFlipKernel ε k) hj2,
      smoothEvenTrace_of_even ε k hj2, neg_zero]

/-- **Pointwise negation of `smoothEvenKernel` under `smoothFlipKernel`:**
for **every** `ε : ℝ` and **every** kernel `k : ℕ → ℝ`,
`smoothEvenKernel ε (smoothFlipKernel ε k) = -smoothEvenKernel ε k`. -/
theorem smoothEvenKernel_smoothFlipKernel (ε : ℝ) (k : ℕ → ℝ) :
    smoothEvenKernel ε (smoothFlipKernel ε k) = fun j => -smoothEvenKernel ε k j := by
  funext j
  unfold smoothEvenKernel
  rw [smoothEvenTrace_smoothFlipKernel]
  unfold shiftTwo
  split_ifs <;> ring

/-- **`smoothFlipKernel ε` is an exact involution on ALL kernels `k : ℕ → ℝ`:**
unlike `flipKernelOf` over `o` (which requires `4 ∣ m → k m = 0`), over the smooth power `d^{−ε}`
the kernel flip `smoothFlipKernel ε` satisfies
`smoothFlipKernel ε (smoothFlipKernel ε k) = k` for **every** `k : ℕ → ℝ`. -/
theorem smoothFlipKernel_smoothFlipKernel (ε : ℝ) (k : ℕ → ℝ) :
    smoothFlipKernel ε (smoothFlipKernel ε k) = k := by
  funext j
  change smoothFlipKernel ε k j + smoothEvenKernel ε (smoothFlipKernel ε k) j -
      2 * shiftTwo (smoothEvenKernel ε (smoothFlipKernel ε k)) j = k j
  rw [smoothEvenKernel_smoothFlipKernel]
  unfold smoothFlipKernel shiftTwo
  split_ifs <;> ring

/-- For any `b : ℕ → ℝ` with `b 0 = 0` and `OrientAdmissible ε b`, `shiftTwo b` is admissible
and `orientNorm ε (shiftTwo b) = 2^ε * orientNorm ε b`. -/
theorem orientNorm_shiftTwo {ε : ℝ} {b : ℕ → ℝ} (hb0 : b 0 = 0) (hb : OrientAdmissible ε b) :
    OrientAdmissible ε (shiftTwo b) ∧
    orientNorm ε (shiftTwo b) = (2 : ℝ) ^ ε * orientNorm ε b := by
  have hzero : ∀ j, ¬ 2 ∣ j → |shiftTwo b j| * (j : ℝ) ^ ε = 0 := fun j hj => by
    rw [shiftTwo_of_not_dvd b hj, abs_zero, zero_mul]
  have hterm : ∀ m : ℕ, |shiftTwo b (2 * m)| * ((2 * m : ℕ) : ℝ) ^ ε =
      (2 : ℝ) ^ ε * (|b m| * (m : ℝ) ^ ε) := fun m => by
    rcases eq_or_ne m 0 with rfl | hm
    · simp [shiftTwo, hb0]
    · rw [shiftTwo_two_mul, Nat.cast_mul, Nat.cast_two,
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]
      ring
  have hsum : OrientAdmissible ε (shiftTwo b) := by
    unfold OrientAdmissible
    rw [summable_iff_two_mul hzero]
    exact (hb.mul_left ((2 : ℝ) ^ ε)).congr fun m => (hterm m).symm
  refine ⟨hsum, ?_⟩
  unfold orientNorm
  rw [tsum_eq_tsum_two_mul hzero, tsum_congr hterm, tsum_mul_left]

theorem orientNorm_smoothEvenTrace_le {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) :
    OrientAdmissible ε (smoothEvenTrace ε k) ∧
    orientNorm ε (smoothEvenTrace ε k) ≤ 2 * orientNorm ε k := by
  have h2le : (2 : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2nn : 0 ≤ (2 : ℝ) ^ (-ε) := Real.rpow_nonneg (by norm_num) (-ε)
  have hbound : ∀ j : ℕ, |smoothEvenTrace ε k j| * (j : ℝ) ^ ε ≤
      |oddPartKernel k j| * (j : ℝ) ^ ε + |evenPartWeight k j| * (j : ℝ) ^ ε := fun j => by
    have hj0 : 0 ≤ (j : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg j) ε
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ hj0
    unfold smoothEvenTrace
    calc |(2 : ℝ) ^ (-ε) * oddPartKernel k j + evenPartWeight k j|
        ≤ |(2 : ℝ) ^ (-ε) * oddPartKernel k j| + |evenPartWeight k j| := abs_add_le _ _
      _ = (2 : ℝ) ^ (-ε) * |oddPartKernel k j| + |evenPartWeight k j| := by
          rw [abs_mul, abs_of_nonneg h2nn]
      _ ≤ 1 * |oddPartKernel k j| + |evenPartWeight k j| :=
          add_le_add_left (mul_le_mul_of_nonneg_right h2le (abs_nonneg _)) _
      _ = |oddPartKernel k j| + |evenPartWeight k j| := by ring
  have hadm : OrientAdmissible ε (smoothEvenTrace ε k) :=
    (hk.oddPart.add (hk.evenPart hε)).of_nonneg_of_le
      (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)) hbound
  have h1 : orientNorm ε (oddPartKernel k) ≤ orientNorm ε k :=
    Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right (abs_oddPartKernel_le k j)
      (Real.rpow_nonneg (Nat.cast_nonneg j) _)) hk.oddPart hk
  have h2 : orientNorm ε (evenPartWeight k) ≤ orientNorm ε k :=
    (Summable.tsum_le_tsum (evenPart_le hε k) (hk.evenPart hε) (summable_two_mul hk)).trans
      (tsum_two_mul_le hk)
  refine ⟨hadm, ?_⟩
  calc orientNorm ε (smoothEvenTrace ε k)
      ≤ orientNorm ε (oddPartKernel k) + orientNorm ε (evenPartWeight k) := by
        unfold orientNorm
        rw [← hk.oddPart.tsum_add (hk.evenPart hε)]
        exact Summable.tsum_le_tsum hbound hadm (hk.oddPart.add (hk.evenPart hε))
    _ ≤ 2 * orientNorm ε k := by linarith

theorem orientNorm_smoothEvenKernel_le {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) :
    OrientAdmissible ε (smoothEvenKernel ε k) ∧
    orientNorm ε (smoothEvenKernel ε k) ≤ 4 * orientNorm ε k := by
  obtain ⟨ht_adm, ht_norm⟩ := orientNorm_smoothEvenTrace_le hε hk
  obtain ⟨hs_adm, hs_norm⟩ := orientNorm_shiftTwo (smoothEvenTrace_zero ε k) ht_adm
  have h2nn : 0 ≤ (2 : ℝ) ^ (-ε) := Real.rpow_nonneg (by norm_num) (-ε)
  have hprod : (2 : ℝ) ^ (-ε) * (2 : ℝ) ^ ε = 1 := by
    rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
  have hbound : ∀ j : ℕ, |smoothEvenKernel ε k j| * (j : ℝ) ^ ε ≤
      |smoothEvenTrace ε k j| * (j : ℝ) ^ ε +
        (2 : ℝ) ^ (-ε) * (|shiftTwo (smoothEvenTrace ε k) j| * (j : ℝ) ^ ε) := fun j => by
    have hj0 : 0 ≤ (j : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg j) ε
    unfold smoothEvenKernel
    calc |smoothEvenTrace ε k j - (2 : ℝ) ^ (-ε) * shiftTwo (smoothEvenTrace ε k) j| * (j : ℝ) ^ ε
        ≤ (|smoothEvenTrace ε k j| + |(2 : ℝ) ^ (-ε) * shiftTwo (smoothEvenTrace ε k) j|) *
            (j : ℝ) ^ ε := mul_le_mul_of_nonneg_right (abs_sub _ _) hj0
      _ = |smoothEvenTrace ε k j| * (j : ℝ) ^ ε +
            (2 : ℝ) ^ (-ε) * (|shiftTwo (smoothEvenTrace ε k) j| * (j : ℝ) ^ ε) := by
          rw [abs_mul, abs_of_nonneg h2nn]; ring
  have hadm : OrientAdmissible ε (smoothEvenKernel ε k) :=
    (ht_adm.add (hs_adm.mul_left ((2 : ℝ) ^ (-ε)))).of_nonneg_of_le
      (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)) hbound
  refine ⟨hadm, ?_⟩
  have htsum : orientNorm ε (smoothEvenKernel ε k) ≤
      orientNorm ε (smoothEvenTrace ε k) +
        (2 : ℝ) ^ (-ε) * orientNorm ε (shiftTwo (smoothEvenTrace ε k)) := by
    unfold orientNorm
    rw [← tsum_mul_left, ← ht_adm.tsum_add (hs_adm.mul_left ((2 : ℝ) ^ (-ε)))]
    exact Summable.tsum_le_tsum hbound hadm (ht_adm.add (hs_adm.mul_left ((2 : ℝ) ^ (-ε))))
  rw [hs_norm, ← mul_assoc, hprod, one_mul] at htsum
  linarith

/-- **The companion class over the smooth power `d^{−ε}` is continuous in `orientNorm ε`:**
for `0 ≤ ε ≤ 1/2` and `OrientAdmissible ε k`, `smoothFlipKernel ε k` is admissible with
`orientNorm ε (smoothFlipKernel ε k) ≤ 21 * orientNorm ε k`. -/
theorem orientNorm_smoothFlipKernel_le {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) :
    OrientAdmissible ε (smoothFlipKernel ε k) ∧
    orientNorm ε (smoothFlipKernel ε k) ≤ 21 * orientNorm ε k := by
  obtain ⟨hek_adm, hek_norm⟩ := orientNorm_smoothEvenKernel_le hε hk
  obtain ⟨hs_adm, hs_norm⟩ := orientNorm_shiftTwo (smoothEvenKernel_zero ε k) hek_adm
  have h2pow : (2 : ℝ) ^ ε ≤ 2 := by
    calc (2 : ℝ) ^ ε ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hbound : ∀ j : ℕ, |smoothFlipKernel ε k j| * (j : ℝ) ^ ε ≤
      |k j| * (j : ℝ) ^ ε + |smoothEvenKernel ε k j| * (j : ℝ) ^ ε +
        2 * (|shiftTwo (smoothEvenKernel ε k) j| * (j : ℝ) ^ ε) := fun j => by
    have hj0 : 0 ≤ (j : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg j) ε
    unfold smoothFlipKernel
    have habs : |k j + smoothEvenKernel ε k j - 2 * shiftTwo (smoothEvenKernel ε k) j| ≤
        |k j| + |smoothEvenKernel ε k j| + |2 * shiftTwo (smoothEvenKernel ε k) j| :=
      (abs_sub _ _).trans (by linarith [abs_add_le (k j) (smoothEvenKernel ε k j)])
    calc |k j + smoothEvenKernel ε k j - 2 * shiftTwo (smoothEvenKernel ε k) j| * (j : ℝ) ^ ε
        ≤ (|k j| + |smoothEvenKernel ε k j| + |2 * shiftTwo (smoothEvenKernel ε k) j|) *
            (j : ℝ) ^ ε := mul_le_mul_of_nonneg_right habs hj0
      _ = |k j| * (j : ℝ) ^ ε + |smoothEvenKernel ε k j| * (j : ℝ) ^ ε +
            2 * (|shiftTwo (smoothEvenKernel ε k) j| * (j : ℝ) ^ ε) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; ring
  have hadm : OrientAdmissible ε (smoothFlipKernel ε k) :=
    ((hk.add hek_adm).add (hs_adm.mul_left 2)).of_nonneg_of_le
      (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)) hbound
  refine ⟨hadm, ?_⟩
  have htsum : orientNorm ε (smoothFlipKernel ε k) ≤
      orientNorm ε k + orientNorm ε (smoothEvenKernel ε k) +
        2 * orientNorm ε (shiftTwo (smoothEvenKernel ε k)) := by
    unfold orientNorm
    rw [← tsum_mul_left, ← hk.tsum_add hek_adm, ← (hk.add hek_adm).tsum_add (hs_adm.mul_left 2)]
    exact Summable.tsum_le_tsum hbound hadm ((hk.add hek_adm).add (hs_adm.mul_left 2))
  have h0 : 0 ≤ orientNorm ε (smoothEvenKernel ε k) := orientNorm_nonneg ε _
  have hs_le : orientNorm ε (shiftTwo (smoothEvenKernel ε k)) ≤ 2 * orientNorm ε (smoothEvenKernel ε k) := by
    rw [hs_norm]
    exact mul_le_mul_of_nonneg_right h2pow h0
  linarith

/-! ### 3. Orientation coordinates over the smooth power `u(d) = d^{−ε}` -/

/-- The **smooth even-part pole pairing** `P_{smooth,e}(ε, k) = polePairing ε (smoothEvenKernel ε k)`. -/
def smoothEvenPolePairing (ε : ℝ) (k : ℕ → ℝ) : ℝ :=
  polePairing ε (smoothEvenKernel ε k)

/-- For any `b : ℕ → ℝ` with `b 0 = 0`, `polePairing ε (shiftTwo b) = 2^{ε − 1} * polePairing ε b`. -/
theorem polePairing_shiftTwo (ε : ℝ) (b : ℕ → ℝ) (hb0 : b 0 = 0) :
    polePairing ε (shiftTwo b) = (2 : ℝ) ^ (ε - 1) * polePairing ε b := by
  unfold polePairing
  rw [tsum_eq_tsum_two_mul fun j hj => by rw [shiftTwo_of_not_dvd b hj, zero_mul], ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp [shiftTwo, hb0]
  · rw [shiftTwo_two_mul, Nat.cast_mul, Nat.cast_two,
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg m), show -(1 - ε) = ε - 1 by ring]
    ring

/-- **Explicit formula for the smooth even-part pole pairing:**
for `0 < ε ≤ 1/2` and `OrientAdmissible ε k`,
`smoothEvenPolePairing ε k = (1 / 2) * (2^{−ε} * polePairing ε (oddPartKernel k) + polePairing ε (evenPartWeight k))`. -/
theorem smoothEvenPolePairing_eq {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) :
    smoothEvenPolePairing ε k =
      (1 / 2 : ℝ) * ((2 : ℝ) ^ (-ε) * polePairing ε (oddPartKernel k) +
        polePairing ε (evenPartWeight k)) := by
  have ht_adm := (orientNorm_smoothEvenTrace_le hε.le hk).1
  have hs_adm := (orientNorm_shiftTwo (smoothEvenTrace_zero ε k) ht_adm).1
  have st := ht_adm.summable_pole hε hε2
  have ss := hs_adm.summable_pole hε hε2
  have so := hk.oddPart.summable_pole hε hε2
  have se := (hk.evenPart hε.le).summable_pole hε hε2
  have h1 : smoothEvenPolePairing ε k =
      polePairing ε (smoothEvenTrace ε k) -
        (2 : ℝ) ^ (-ε) * polePairing ε (shiftTwo (smoothEvenTrace ε k)) := by
    unfold smoothEvenPolePairing polePairing smoothEvenKernel
    have hterm : (fun j : ℕ => (smoothEvenTrace ε k j - (2 : ℝ) ^ (-ε) * shiftTwo (smoothEvenTrace ε k) j) *
        (j : ℝ) ^ (-(1 - ε))) =
      fun j : ℕ => smoothEvenTrace ε k j * (j : ℝ) ^ (-(1 - ε)) -
        (2 : ℝ) ^ (-ε) * (shiftTwo (smoothEvenTrace ε k) j * (j : ℝ) ^ (-(1 - ε))) := by
      funext j; ring
    rw [hterm, st.tsum_sub (ss.mul_left ((2 : ℝ) ^ (-ε))), tsum_mul_left]
  have h2 : polePairing ε (smoothEvenTrace ε k) =
      (2 : ℝ) ^ (-ε) * polePairing ε (oddPartKernel k) + polePairing ε (evenPartWeight k) := by
    unfold polePairing smoothEvenTrace
    have hterm : (fun j : ℕ => ((2 : ℝ) ^ (-ε) * oddPartKernel k j + evenPartWeight k j) *
        (j : ℝ) ^ (-(1 - ε))) =
      fun j : ℕ => (2 : ℝ) ^ (-ε) * (oddPartKernel k j * (j : ℝ) ^ (-(1 - ε))) +
        evenPartWeight k j * (j : ℝ) ^ (-(1 - ε)) := by
      funext j; ring
    rw [hterm, (so.mul_left ((2 : ℝ) ^ (-ε))).tsum_add se, tsum_mul_left]
  have hprod : (2 : ℝ) ^ (-ε) * (2 : ℝ) ^ (ε - 1) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num), show -ε + (ε - 1) = -1 by ring, Real.rpow_neg_one]
    norm_num
  rw [h1, polePairing_shiftTwo ε (smoothEvenTrace ε k) (smoothEvenTrace_zero ε k),
    ← mul_assoc, hprod, h2]
  ring

/-- **The smooth flip negates the second orientation coordinate `smoothEvenPolePairing`:**
for every `ε : ℝ` and every kernel `k : ℕ → ℝ`,
`smoothEvenPolePairing ε (smoothFlipKernel ε k) = -smoothEvenPolePairing ε k`. -/
theorem smoothEvenPolePairing_smoothFlipKernel (ε : ℝ) (k : ℕ → ℝ) :
    smoothEvenPolePairing ε (smoothFlipKernel ε k) = -smoothEvenPolePairing ε k := by
  unfold smoothEvenPolePairing polePairing
  rw [smoothEvenKernel_smoothFlipKernel, ← tsum_neg]
  exact tsum_congr fun j => by ring

/-- **The smooth flip shifts the pole pairing by `(1 − 2^ε) * smoothEvenPolePairing ε k`:**
for `0 < ε ≤ 1/2` and `OrientAdmissible ε k` (with no four-free requirement),
`polePairing ε (smoothFlipKernel ε k) = polePairing ε k + (1 - 2^ε) * smoothEvenPolePairing ε k`. -/
theorem polePairing_smoothFlipKernel {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) :
    polePairing ε (smoothFlipKernel ε k) =
      polePairing ε k + (1 - (2 : ℝ) ^ ε) * smoothEvenPolePairing ε k := by
  have hek_adm := (orientNorm_smoothEvenKernel_le hε.le hk).1
  have hs_adm := (orientNorm_shiftTwo (smoothEvenKernel_zero ε k) hek_adm).1
  have sk := hk.summable_pole hε hε2
  have sek := hek_adm.summable_pole hε hε2
  have ss := hs_adm.summable_pole hε hε2
  have h1 : polePairing ε (smoothFlipKernel ε k) =
      polePairing ε k + polePairing ε (smoothEvenKernel ε k) -
        2 * polePairing ε (shiftTwo (smoothEvenKernel ε k)) := by
    unfold polePairing smoothFlipKernel
    have hterm : (fun j : ℕ => (k j + smoothEvenKernel ε k j - 2 * shiftTwo (smoothEvenKernel ε k) j) *
        (j : ℝ) ^ (-(1 - ε))) =
      fun j : ℕ => (k j * (j : ℝ) ^ (-(1 - ε)) + smoothEvenKernel ε k j * (j : ℝ) ^ (-(1 - ε))) -
        2 * (shiftTwo (smoothEvenKernel ε k) j * (j : ℝ) ^ (-(1 - ε))) := by
      funext j; ring
    rw [hterm, (sk.add sek).tsum_sub (ss.mul_left 2), sk.tsum_add sek, tsum_mul_left]
  have h2 : (2 : ℝ) * (2 : ℝ) ^ (ε - 1) = (2 : ℝ) ^ ε := by
    rw [show ε = 1 + (ε - 1) by ring, Real.rpow_add two_pos, Real.rpow_one]
    ring
  rw [h1, polePairing_shiftTwo ε (smoothEvenKernel ε k) (smoothEvenKernel_zero ε k),
    ← mul_assoc, h2]
  unfold smoothEvenPolePairing
  ring

/-- **Payment of the companion `(k ⋆ d^{−ε})^♭` over the smooth power:**
for `0 < ε ≤ 1/2` and `OrientAdmissible ε k` (with no four-free requirement),
`ReceiverBounded (evenFlip (k ⋆ d^{−ε})) ↔ polePairing ε k + (1 - 2^ε) * smoothEvenPolePairing ε k = 0`. -/
theorem receiverBounded_evenFlip_dirichletConv_unit_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    ReceiverBounded (evenFlip (RHTower.dirichletConv k (dampedSignWeight unitSign ε))) ↔
      polePairing ε k + (1 - (2 : ℝ) ^ ε) * smoothEvenPolePairing ε k = 0 := by
  rw [evenFlip_dirichletConv_unit,
    receiverBounded_dirichletConv_unit_iff_admissible hε hε2
      (orientNorm_smoothFlipKernel_le hε.le hε2 hk).1,
    polePairing_smoothFlipKernel hε hε2 hk]

/-- **Both members of a flip pair over the smooth power `d^{−ε}` are paid iff both orientation
coordinates vanish (`polePairing ε k = 0 ∧ smoothEvenPolePairing ε k = 0`).** -/
theorem receiverBounded_and_evenFlip_dirichletConv_unit_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    (ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) ∧
        ReceiverBounded (evenFlip (RHTower.dirichletConv k (dampedSignWeight unitSign ε)))) ↔
      (polePairing ε k = 0 ∧ smoothEvenPolePairing ε k = 0) := by
  rw [receiverBounded_dirichletConv_unit_iff_admissible hε hε2 hk,
    receiverBounded_evenFlip_dirichletConv_unit_iff hε hε2 hk]
  have h2 : (1 : ℝ) - (2 : ℝ) ^ ε ≠ 0 := by
    have : (1 : ℝ) < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
    linarith
  constructor
  · rintro ⟨h1, h3⟩
    rw [h1, zero_add] at h3
    exact ⟨h1, (mul_eq_zero.1 h3).resolve_left h2⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, by rw [h1, h3]; ring⟩

/-- **On the doubly paid subspace over the smooth power `d^{−ε}`, both receivers are bounded by
`orientNorm ε k ^ 2`:** if `polePairing ε k = 0` and `smoothEvenPolePairing ε k = 0`, then at every
cutoff `T`,
`E_T(evenFlip (k ⋆ d^{−ε})) ≤ 1764 * smoothPowerReceiverConst ε * orientNorm ε k ^ 2`. -/
theorem weightPronicEnergy_evenFlip_dirichletConv_unit_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk : OrientAdmissible ε k) (hP : polePairing ε k = 0)
    (hPe : smoothEvenPolePairing ε k = 0) (T : ℕ) :
    weightPronicEnergy (evenFlip (RHTower.dirichletConv k (dampedSignWeight unitSign ε)))
        (∑' d : ℕ, evenFlip (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) d / d) T ≤
      1764 * smoothPowerReceiverConst ε * orientNorm ε k ^ 2 := by
  rw [evenFlip_dirichletConv_unit]
  obtain ⟨hflip_adm, hflip_norm⟩ := orientNorm_smoothFlipKernel_le hε.le hε2 hk
  have hP' : polePairing ε (smoothFlipKernel ε k) = 0 := by
    rw [polePairing_smoothFlipKernel hε hε2 hk, hP, hPe]; ring
  refine (weightPronicEnergy_dirichletConv_unit_le hε hε2 hflip_adm hP' T).trans ?_
  have h0 := orientNorm_nonneg ε (smoothFlipKernel ε k)
  have hC : 0 ≤ 4 * smoothPowerReceiverConst ε :=
    mul_nonneg (by norm_num) (smoothPowerReceiverConst_nonneg ε)
  calc 4 * smoothPowerReceiverConst ε * orientNorm ε (smoothFlipKernel ε k) ^ 2
      ≤ 4 * smoothPowerReceiverConst ε * (21 * orientNorm ε k) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hflip_norm 2) hC
    _ = 1764 * smoothPowerReceiverConst ε * orientNorm ε k ^ 2 := by ring

/-- **Relation between `smoothEvenPolePairing` and `polePairing ε (evenPartWeight k)` on four-free
kernels:** if `k` is four-free (`∀ m, 4 ∣ m → k m = 0`), then
`smoothEvenPolePairing ε k = (1 / 2) * 2^{−ε} * polePairing ε k + (1 / 4) * polePairing ε (evenPartWeight k)`,
so on the paid hyperplane `polePairing ε k = 0`, `smoothEvenPolePairing ε k = (1 / 4) * polePairing ε (evenPartWeight k)`. -/
theorem smoothEvenPolePairing_of_fourFree_of_polePairing_eq_zero {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) (hk : OrientAdmissible ε k) :
    smoothEvenPolePairing ε k =
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-ε) * polePairing ε k +
        (1 / 4 : ℝ) * polePairing ε (evenPartWeight k) ∧
    (polePairing ε k = 0 →
      smoothEvenPolePairing ε k = (1 / 4 : ℝ) * polePairing ε (evenPartWeight k)) := by
  have so := hk.oddPart.summable_pole hε hε2
  have ss := hk.shiftEven.summable_pole hε hε2
  have hk_split : polePairing ε k =
      polePairing ε (oddPartKernel k) + (2 : ℝ) ^ (ε - 1) * polePairing ε (evenPartWeight k) := by
    rw [← polePairing_shiftTwo ε (evenPartWeight k) (evenPartWeight_of_even k (dvd_zero 2))]
    unfold polePairing
    rw [← so.tsum_add ss]
    exact tsum_congr fun j => by rw [kernel_eq_odd_add_shift hk4 j]; ring
  have hprod : (2 : ℝ) ^ (-ε) * (2 : ℝ) ^ (ε - 1) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num), show -ε + (ε - 1) = -1 by ring, Real.rpow_neg_one]
    norm_num
  have hid : smoothEvenPolePairing ε k =
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-ε) * polePairing ε k +
        (1 / 4 : ℝ) * polePairing ε (evenPartWeight k) := by
    rw [smoothEvenPolePairing_eq hε hε2 hk]
    calc (1 / 2 : ℝ) * ((2 : ℝ) ^ (-ε) * polePairing ε (oddPartKernel k) +
          polePairing ε (evenPartWeight k))
        = (1 / 2 : ℝ) * (2 : ℝ) ^ (-ε) *
            (polePairing ε (oddPartKernel k) + (2 : ℝ) ^ (ε - 1) * polePairing ε (evenPartWeight k)) +
          ((1 / 2 : ℝ) - (1 / 2 : ℝ) * ((2 : ℝ) ^ (-ε) * (2 : ℝ) ^ (ε - 1))) *
            polePairing ε (evenPartWeight k) := by ring
      _ = (1 / 2 : ℝ) * (2 : ℝ) ^ (-ε) * polePairing ε k +
          (1 / 4 : ℝ) * polePairing ε (evenPartWeight k) := by
        rw [← hk_split, hprod]; ring
  exact ⟨hid, fun h0 => by rw [hid, h0, mul_zero, zero_add]⟩

/-! ### 4. Multiplicative weights `f(d) d^{−ε}` and the 2-local orientation coordinate -/

/-- The **Möbius kernel** `k_f(j) = (f ⋆ μ)(j) j^{−ε}` representing any damped weight `f(d) d^{−ε}`
as `k_f ⋆ d^{−ε}` over the smooth power. -/
def moebiusKernelOf (f : ArithmeticFunction ℝ) (ε : ℝ) : ℕ → ℝ :=
  dampedSignWeight ⇑(f * μR) ε

/-- **Every damped arithmetic function `f(d) d^{−ε}` is `moebiusKernelOf f ε ⋆ d^{−ε}`** for `ε ≠ 0`. -/
theorem dampedSignWeight_eq_dirichletConv_moebiusKernel_unit (f : ArithmeticFunction ℝ) {ε : ℝ}
    (hε : ε ≠ 0) :
    dampedSignWeight ⇑f ε =
      RHTower.dirichletConv (moebiusKernelOf f ε) (dampedSignWeight unitSign ε) := by
  have hfg : f = (f * μR) * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) := by
    rw [mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  funext n
  unfold moebiusKernelOf
  rw [← dampedSignWeight_zeta hε, ← dampedSignWeight_dirichletConv]
  conv_lhs => rw [hfg]
  simp only [dampedSignWeight, mul_apply_eq_dirichletConv]

/-- For a multiplicative function `f` and odd `m` (`m % 2 = 1`), `f(2m) = f(2) * f(m)`. -/
theorem multiplicative_apply_two_mul_of_odd {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    {m : ℕ} (hm : m % 2 = 1) :
    f (2 * m) = f 2 * f m := by
  have hcop : Nat.Coprime 2 m :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  exact hf.map_mul_of_coprime hcop

/-- **How `evenFlip` acts on a damped multiplicative weight `f(d) d^{−ε}`:**
for any multiplicative `f : ArithmeticFunction ℝ`:
1. At `d = 1`: `evenFlip (f d^{−ε})(1) = 1 + f(2) 2^{−ε}`.
2. At `d = 2`: `evenFlip (f d^{−ε})(2) = -f(2) 2^{−ε}`.
3. On every odd `m`: `evenFlip (f d^{−ε})(m) = (1 + f(2) 2^{−ε}) * f(m) m^{−ε}`.
4. `evenFlip (f d^{−ε})(1) = 1 ↔ f(2) = 0`: the even flip breaks multiplicative normalization at `1`
   whenever `f(2) ≠ 0`. -/
theorem evenFlip_dampedSignWeight_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (ε : ℝ) :
    evenFlip (dampedSignWeight ⇑f ε) 1 = 1 + f 2 * (2 : ℝ) ^ (-ε) ∧
    evenFlip (dampedSignWeight ⇑f ε) 2 = -f 2 * (2 : ℝ) ^ (-ε) ∧
    (∀ m : ℕ, m % 2 = 1 →
      evenFlip (dampedSignWeight ⇑f ε) m =
        (1 + f 2 * (2 : ℝ) ^ (-ε)) * dampedSignWeight ⇑f ε m) ∧
    (evenFlip (dampedSignWeight ⇑f ε) 1 = 1 ↔ f 2 = 0) := by
  have h1 : evenFlip (dampedSignWeight ⇑f ε) 1 = 1 + f 2 * (2 : ℝ) ^ (-ε) := by
    rw [evenFlip_apply, if_pos rfl]
    simp [dampedSignWeight, hf.map_one]
  have h2 : evenFlip (dampedSignWeight ⇑f ε) 2 = -f 2 * (2 : ℝ) ^ (-ε) := by
    rw [evenFlip_apply, if_neg (by decide), if_pos (by decide)]
    simp [dampedSignWeight]
  have hodd : ∀ m : ℕ, m % 2 = 1 →
      evenFlip (dampedSignWeight ⇑f ε) m =
        (1 + f 2 * (2 : ℝ) ^ (-ε)) * dampedSignWeight ⇑f ε m := fun m hm => by
    rw [evenFlip_apply, if_pos hm]
    unfold dampedSignWeight
    rw [multiplicative_apply_two_mul_of_odd hf hm, Nat.cast_mul, Nat.cast_two,
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by norm_num) (-ε)
  refine ⟨h1, h2, hodd, ?_⟩
  rw [h1]
  constructor
  · intro heq
    have hmul : f 2 * (2 : ℝ) ^ (-ε) = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hpos)
  · intro hf2
    rw [hf2, zero_mul, add_zero]

/-- **Exact cancellation in `smoothEvenTrace` for multiplicative weights:**
for any multiplicative `f : ArithmeticFunction ℝ`, `(f ⋆ μ)(2) = f(2) − 1`, so on every `j : ℕ`,
`smoothEvenTrace ε (moebiusKernelOf f ε) j = f(2) * 2^{−ε} * oddPartKernel (moebiusKernelOf f ε) j`. -/
theorem smoothEvenTrace_moebiusKernel_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (ε : ℝ) (j : ℕ) :
    smoothEvenTrace ε (moebiusKernelOf f ε) j =
      f 2 * (2 : ℝ) ^ (-ε) * oddPartKernel (moebiusKernelOf f ε) j := by
  have hg : (f * μR).IsMultiplicative := hf.mul ArithmeticFunction.isMultiplicative_moebius.intCast
  have hg2 : (f * μR) 2 = f 2 - 1 := by
    have h := mul_moebius_apply_prime_pow f Nat.prime_two 0
    rwa [zero_add, pow_one, pow_zero, hf.map_one] at h
  by_cases hj : j % 2 = 1
  · unfold smoothEvenTrace oddPartKernel evenPartWeight moebiusKernelOf dampedSignWeight
    simp only [hj, ↓reduceIte]
    rw [multiplicative_apply_two_mul_of_odd hg hj, hg2,
      Nat.cast_mul, Nat.cast_two, Real.mul_rpow (by norm_num) (Nat.cast_nonneg j)]
    ring
  · have hj2 : 2 ∣ j := by omega
    rw [smoothEvenTrace_of_even ε (moebiusKernelOf f ε) hj2,
      oddPartKernel_of_even (moebiusKernelOf f ε) hj2, mul_zero]

/-- **The second orientation coordinate of a multiplicative weight `f(d) d^{−ε}`:**
for any multiplicative `f : ArithmeticFunction ℝ` with `OrientAdmissible ε (moebiusKernelOf f ε)`
(`0 < ε ≤ 1/2`),
`smoothEvenPolePairing ε (moebiusKernelOf f ε) = (1 / 2) * f(2) * 2^{−ε} * polePairing ε (oddPartKernel (moebiusKernelOf f ε))`,
and the pole pairing of `evenFlip (f d^{−ε})` is
`polePairing ε (moebiusKernelOf f ε) + (1 / 2) * (2^{−ε} - 1) * f(2) * polePairing ε (oddPartKernel (moebiusKernelOf f ε))`. -/
theorem smoothEvenPolePairing_moebiusKernel_multiplicative {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hk : OrientAdmissible ε (moebiusKernelOf f ε)) :
    smoothEvenPolePairing ε (moebiusKernelOf f ε) =
      (1 / 2 : ℝ) * f 2 * (2 : ℝ) ^ (-ε) *
        polePairing ε (oddPartKernel (moebiusKernelOf f ε)) ∧
    polePairing ε (smoothFlipKernel ε (moebiusKernelOf f ε)) =
      polePairing ε (moebiusKernelOf f ε) +
        (1 / 2 : ℝ) * ((2 : ℝ) ^ (-ε) - 1) * f 2 *
          polePairing ε (oddPartKernel (moebiusKernelOf f ε)) := by
  set k := moebiusKernelOf f ε
  have htrace : smoothEvenTrace ε k =
      fun j => f 2 * (2 : ℝ) ^ (-ε) * oddPartKernel k j :=
    funext (smoothEvenTrace_moebiusKernel_multiplicative hf ε)
  have hpe_even : polePairing ε (evenPartWeight k) =
      (f 2 - 1) * (2 : ℝ) ^ (-ε) * polePairing ε (oddPartKernel k) := by
    have hpt : ∀ j : ℕ, evenPartWeight k j =
        (f 2 - 1) * (2 : ℝ) ^ (-ε) * oddPartKernel k j := fun j => by
      have ht := smoothEvenTrace_moebiusKernel_multiplicative hf ε j
      unfold smoothEvenTrace at ht
      linarith
    unfold polePairing
    have hterm : (fun j : ℕ => evenPartWeight k j * (j : ℝ) ^ (-(1 - ε))) =
        fun j : ℕ => ((f 2 - 1) * (2 : ℝ) ^ (-ε)) *
          (oddPartKernel k j * (j : ℝ) ^ (-(1 - ε))) := by
      funext j; rw [hpt j]; ring
    rw [hterm, tsum_mul_left]
  have h1 : smoothEvenPolePairing ε k =
      (1 / 2 : ℝ) * f 2 * (2 : ℝ) ^ (-ε) * polePairing ε (oddPartKernel k) := by
    rw [smoothEvenPolePairing_eq hε hε2 hk, hpe_even]
    ring
  have hprod : (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε) = 1 := by
    rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
  have h2 : polePairing ε (smoothFlipKernel ε k) =
      polePairing ε k +
        (1 / 2 : ℝ) * ((2 : ℝ) ^ (-ε) - 1) * f 2 * polePairing ε (oddPartKernel k) := by
    rw [polePairing_smoothFlipKernel hε hε2 hk, h1]
    calc polePairing ε k + (1 - (2 : ℝ) ^ ε) *
          ((1 / 2 : ℝ) * f 2 * (2 : ℝ) ^ (-ε) * polePairing ε (oddPartKernel k))
        = polePairing ε k +
          (1 / 2 : ℝ) * ((2 : ℝ) ^ (-ε) - (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε)) *
            f 2 * polePairing ε (oddPartKernel k) := by ring
      _ = polePairing ε k +
          (1 / 2 : ℝ) * ((2 : ℝ) ^ (-ε) - 1) * f 2 * polePairing ε (oddPartKernel k) := by
        rw [hprod]
  exact ⟨h1, h2⟩

/-- **Simultaneous payment criterion for a multiplicative weight `f(d) d^{−ε}` and its even flip:**
for any multiplicative `f : ArithmeticFunction ℝ` with `OrientAdmissible ε (moebiusKernelOf f ε)`
(`0 < ε ≤ 1/2`) whose odd Möbius Euler factor is nonzero
(`polePairing ε (oddPartKernel (moebiusKernelOf f ε)) ≠ 0`), both `f(d) d^{−ε}` and
`evenFlip (f(d) d^{−ε})` are paid if and only if `polePairing ε (moebiusKernelOf f ε) = 0 ∧ f 2 = 0`. -/
theorem receiverBounded_and_evenFlip_multiplicative_iff {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hk : OrientAdmissible ε (moebiusKernelOf f ε))
    (hodd_ne : polePairing ε (oddPartKernel (moebiusKernelOf f ε)) ≠ 0) :
    (ReceiverBounded (dampedSignWeight ⇑f ε) ∧
        ReceiverBounded (evenFlip (dampedSignWeight ⇑f ε))) ↔
      (polePairing ε (moebiusKernelOf f ε) = 0 ∧ f 2 = 0) := by
  rw [dampedSignWeight_eq_dirichletConv_moebiusKernel_unit f hε.ne',
    receiverBounded_and_evenFlip_dirichletConv_unit_iff hε hε2 hk,
    (smoothEvenPolePairing_moebiusKernel_multiplicative hf hε hε2 hk).1]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by norm_num) (-ε)
  constructor
  · rintro ⟨hP, hPe⟩
    have hmul : f 2 * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-ε) *
        polePairing ε (oddPartKernel (moebiusKernelOf f ε))) = 0 := by linarith
    have hnz : (1 / 2 : ℝ) * (2 : ℝ) ^ (-ε) *
        polePairing ε (oddPartKernel (moebiusKernelOf f ε)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt h2pos)) hodd_ne
    exact ⟨hP, (mul_eq_zero.mp hmul).resolve_right hnz⟩
  · rintro ⟨hP, hf2⟩
    exact ⟨hP, by rw [hf2]; ring⟩

/-- **At most one of `f(d) d^{−ε}` and `evenFlip (f(d) d^{−ε})` is paid when `f(2) ≠ 0`:**
for any multiplicative `f : ArithmeticFunction ℝ` with `OrientAdmissible ε (moebiusKernelOf f ε)`
(`0 < ε ≤ 1/2`), `f 2 ≠ 0` (in particular whenever `f 2 = 1`), and
`polePairing ε (oddPartKernel (moebiusKernelOf f ε)) ≠ 0`, `f(d) d^{−ε}` and its even flip can
never both be paid. -/
theorem not_receiverBounded_and_evenFlip_of_apply_two_ne_zero {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hk : OrientAdmissible ε (moebiusKernelOf f ε))
    (hodd_ne : polePairing ε (oddPartKernel (moebiusKernelOf f ε)) ≠ 0) (hf2 : f 2 ≠ 0) :
    ¬ (ReceiverBounded (dampedSignWeight ⇑f ε) ∧
        ReceiverBounded (evenFlip (dampedSignWeight ⇑f ε))) := by
  rw [receiverBounded_and_evenFlip_multiplicative_iff hf hε hε2 hk hodd_ne]
  exact fun ⟨_, h⟩ => hf2 h

/-- **Master Synthesis for Open Problem 4 (`orientationFaithfulNorm_smooth_and_multiplicative_synthesis`):**
1. *Paid hyperplane and norm bound over `d^{−ε}`:* for `0 < ε ≤ 1/2` and `OrientAdmissible ε k`,
   `ReceiverBounded (k ⋆ d^{−ε}) ↔ polePairing ε k = 0`, with
   `E_T(k ⋆ d^{−ε}) ≤ 4 * smoothPowerReceiverConst ε * orientNorm ε k ^ 2` when `polePairing ε k = 0`.
2. *Exact kernel involution and continuity over `d^{−ε}`:* for **every** `k : ℕ → ℝ` (without any
   four-free requirement), `evenFlip (k ⋆ d^{−ε}) = smoothFlipKernel ε k ⋆ d^{−ε}`,
   `smoothFlipKernel ε (smoothFlipKernel ε k) = k`, and
   `orientNorm ε (smoothFlipKernel ε k) ≤ 21 * orientNorm ε k`.
3. *Orientation coordinates over `d^{−ε}`:* `smoothFlipKernel ε` acts on
   `(polePairing ε k, smoothEvenPolePairing ε k)` by
   `(P, P_{smooth,e}) ↦ (P + (1 - 2^ε) P_{smooth,e}, -P_{smooth,e})`, so both `k ⋆ d^{−ε}` and
   `evenFlip (k ⋆ d^{−ε})` are paid iff `polePairing ε k = 0 ∧ smoothEvenPolePairing ε k = 0`.
4. *Multiplicative weights `f(d) d^{−ε}`:* for any multiplicative `f : ArithmeticFunction ℝ`,
   `evenFlip (f d^{−ε})(1) = 1 + f(2) 2^{−ε}`, `smoothEvenTrace ε (moebiusKernelOf f ε) =
   f(2) 2^{−ε} • oddPartKernel (moebiusKernelOf f ε)`, and when `OrientAdmissible ε (moebiusKernelOf f ε)`
   and `polePairing ε (oddPartKernel (moebiusKernelOf f ε)) ≠ 0`, both `f d^{−ε}` and
   `evenFlip (f d^{−ε})` are paid iff `polePairing ε (moebiusKernelOf f ε) = 0 ∧ f 2 = 0`. -/
theorem orientationFaithfulNorm_smooth_and_multiplicative_synthesis {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ {k : ℕ → ℝ}, OrientAdmissible ε k →
      (ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) ↔
        polePairing ε k = 0) ∧
      (polePairing ε k = 0 → ∀ T : ℕ,
        weightPronicEnergy (RHTower.dirichletConv k (dampedSignWeight unitSign ε))
            (∑' d : ℕ, RHTower.dirichletConv k (dampedSignWeight unitSign ε) d / d) T ≤
          4 * smoothPowerReceiverConst ε * orientNorm ε k ^ 2)) ∧
    (∀ k : ℕ → ℝ,
      evenFlip (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) =
        RHTower.dirichletConv (smoothFlipKernel ε k) (dampedSignWeight unitSign ε) ∧
      smoothFlipKernel ε (smoothFlipKernel ε k) = k ∧
      smoothEvenPolePairing ε (smoothFlipKernel ε k) = -smoothEvenPolePairing ε k) ∧
    (∀ {k : ℕ → ℝ}, OrientAdmissible ε k →
      orientNorm ε (smoothFlipKernel ε k) ≤ 21 * orientNorm ε k ∧
      polePairing ε (smoothFlipKernel ε k) =
        polePairing ε k + (1 - (2 : ℝ) ^ ε) * smoothEvenPolePairing ε k ∧
      ((ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) ∧
          ReceiverBounded (evenFlip (RHTower.dirichletConv k (dampedSignWeight unitSign ε)))) ↔
        (polePairing ε k = 0 ∧ smoothEvenPolePairing ε k = 0))) ∧
    (∀ {f : ArithmeticFunction ℝ}, f.IsMultiplicative →
      OrientAdmissible ε (moebiusKernelOf f ε) →
      polePairing ε (oddPartKernel (moebiusKernelOf f ε)) ≠ 0 →
      evenFlip (dampedSignWeight ⇑f ε) 1 = 1 + f 2 * (2 : ℝ) ^ (-ε) ∧
      ((ReceiverBounded (dampedSignWeight ⇑f ε) ∧
          ReceiverBounded (evenFlip (dampedSignWeight ⇑f ε))) ↔
        (polePairing ε (moebiusKernelOf f ε) = 0 ∧ f 2 = 0))) :=
  ⟨fun hk => ⟨receiverBounded_dirichletConv_unit_iff_admissible hε hε2 hk,
      fun hP T => weightPronicEnergy_dirichletConv_unit_le hε hε2 hk hP T⟩,
   fun k => ⟨evenFlip_dirichletConv_unit ε k,
      smoothFlipKernel_smoothFlipKernel ε k,
      smoothEvenPolePairing_smoothFlipKernel ε k⟩,
   fun hk => ⟨(orientNorm_smoothFlipKernel_le hε.le hε2 hk).2,
      polePairing_smoothFlipKernel hε hε2 hk,
      receiverBounded_and_evenFlip_dirichletConv_unit_iff hε hε2 hk⟩,
   fun hf hk hodd => ⟨(evenFlip_dampedSignWeight_multiplicative hf ε).1,
      receiverBounded_and_evenFlip_multiplicative_iff hf hε hε2 hk hodd⟩⟩

end

end GaloisForLFunctions.ArithmeticOrientationTheory
