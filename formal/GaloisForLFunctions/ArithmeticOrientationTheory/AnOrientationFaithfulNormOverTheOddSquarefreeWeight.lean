import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheEvenFlipShiftsThePoleValueByTheEvenPartOfTheKernel
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerKernelsRepairAPositiveDriftOnlyAtItsPole
import GaloisForLFunctions.ArithmeticOrientationTheory.TheEvenFlipIsReadAtThePrimeTwo

/-!
# An orientation-faithful norm over the odd squarefree weight

Fix `0 < ε ≤ ½` and the odd squarefree weight `o(d) = 1_{d odd squarefree} d^{−ε}`.  Every kernel
`k` with `N(k) = Σ_j |k(j)| j^ε < ∞` (`OrientAdmissible`, `orientNorm`) gives the damped weight
`k ⋆ o`, and for kernels vanishing on multiples of four the even flip of `k ⋆ o` is `k^♭ ⋆ o`
(Trans-Horizon Incidence Mechanics).  The norm `N` is the orientation-faithful norm:

* **The receiver is bounded on the paid hyperplane** (`weightPronicEnergy_dirichletConv_oddSqf_le`):
  if the pole pairing `P(k) = Σ_j k(j) j^{−(1−ε)}` vanishes, then every receiver energy of `k ⋆ o`
  is at most `4 C_ε N(k)²`, with `C_ε` explicit (`oddSqfReceiverConst`).  For finite kernels the
  constant comes from the bounded partial sums of `k̃ ⋆ 1_odd` and the critical Wiener factor of
  `o` (`weightPronicEnergy_dirichletConv_oddSqf_le_finite`); in general from the truncations
  `k|_{[1,J]} − P_J δ₁`, which stay on the hyperplane and converge at every fixed cutoff.
* **Payment is the closed hyperplane `P = 0`** (`receiverBounded_dirichletConv_oddSqf_iff_admissible`)
  for every admissible kernel, not only for finite ones.
* **The companion class is continuous** (`orientNorm_flipKernelOf_le`, `flipKernelOf_flipKernelOf`):
  the flip `k ↦ k^♭` is an involution of the admissible four-free kernels with `N(k^♭) ≤ 3 N(k)`.
* **The orientation coordinates** (`polePairing_flipKernelOf`, `evenPartWeight_flipKernelOf`): with
  `P_e(k) = P(k_e)` the pole pairing of the even part, the flip acts on `(P, P_e)` by
  `(P, P_e) ↦ (P + (1 − 2^ε) P_e, −P_e)`.  So `c = k ⋆ o` and its companion are both paid iff
  `P(k) = P_e(k) = 0` (`receiverBounded_and_evenFlip_iff`), and then both receivers are bounded by
  `36 C_ε N(k)²` (`weightPronicEnergy_evenFlip_le`).

The orientation of `k ⋆ o` is therefore one continuous coordinate, the even-part pole pairing
`P_e`: the flip fixes payment exactly on its kernel and is otherwise the reflection that makes at
most one member of the pair paid.
-/

open Finset Filter Topology
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### The receiver constant and finite kernels -/

/-- The critical Wiener norm of the damped odd square-root Möbius kernel `g`, `o = g ⋆ 1_{odd} d^{−ε}`. -/
def oddSqfKernelNorm (ε : ℝ) : ℝ :=
  ∑' q : ℕ, |dampedSignWeight ⇑oddSqrtMoebius ε q| * (q : ℝ) ^ (-(1 / 2 : ℝ))

/-- The receiver constant `C_ε = (G_ε (6 √S_ε + (√2 + 1) Z_ε))²` over `o`. -/
def oddSqfReceiverConst (ε : ℝ) : ℝ :=
  (oddSqfKernelNorm ε * (6 * Real.sqrt (∑' n : ℕ, (n : ℝ) ^ (2 * (1 / (2 + ε)) - 2)) +
    (Real.sqrt 2 + 1) * ∑' d : ℕ, (d : ℝ) ^ (-(1 + ε)))) ^ 2

theorem oddSqfReceiverConst_nonneg (ε : ℝ) : 0 ≤ oddSqfReceiverConst ε := sq_nonneg _

/-- `k ⋆ o = g ⋆ w` with `w = (k̃ ⋆ 1_{odd}) d^{−ε}`. -/
theorem dirichletConv_oddSqf_eq (k : ℕ → ℝ) (ε : ℝ) :
    RHTower.dirichletConv k (oddSqfWeight ε) =
      RHTower.dirichletConv (dampedSignWeight ⇑oddSqrtMoebius ε)
        (dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) ⇑oddAF) ε) := by
  funext n
  have hk : RHTower.dirichletConv k (oddSqfWeight ε) n = RHTower.dirichletConv k
      (RHTower.dirichletConv (dampedSignWeight ⇑oddSqrtMoebius ε)
        (dampedSignWeight ⇑oddAF ε)) n := by
    unfold RHTower.dirichletConv
    exact sum_congr rfl fun d _ => by rw [oddSqfWeight_eq]; rfl
  rw [hk, dirichletConv_left_comm]
  congr 1
  funext m
  exact dirichletConv_damped_eq k _ ε m

/-- **The quantitative pole law over `o` for finite kernels**: a kernel on `[1, J]` with vanishing
pole value has every receiver energy of `k ⋆ o` at most `C_ε (Σ_j |k(j)| j^ε)²`. -/
theorem weightPronicEnergy_dirichletConv_oddSqf_le_finite {ε : ℝ} (hε : 0 < ε) {k : ℕ → ℝ}
    {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) (hK : poleValue k J ε = 0) (T : ℕ) :
    weightPronicEnergy (RHTower.dirichletConv k (oddSqfWeight ε))
        (∑' d : ℕ, RHTower.dirichletConv k (oddSqfWeight ε) d / d) T ≤
      oddSqfReceiverConst ε * (∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε) ^ 2 := by
  set g := dampedSignWeight ⇑oddSqrtMoebius ε
  set s := RHTower.dirichletConv (undampedKernel k ε) ⇑oddAF
  set w := dampedSignWeight s ε
  set L := ∑ j ∈ Icc 1 J, |undampedKernel k ε j|
  have hLeq : L = ∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε := sum_congr rfl fun j _ => by
    rw [undampedKernel, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) ε)]
  have hL : 0 ≤ L := sum_nonneg fun j _ => abs_nonneg _
  -- the sign sequence `k̃ ⋆ 1_{odd}` is bounded by `L`
  have hsign : ∀ d, |s d| ≤ L := fun d => by
    unfold s RHTower.dirichletConv
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ d.divisors, |undampedKernel k ε j * oddAF (d / j)| ≤
          ∑ j ∈ d.divisors.filter (· ≤ J), |undampedKernel k ε j| := by
          rw [sum_filter]
          refine sum_le_sum fun j _ => ?_
          split_ifs with hj
          · rw [abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (by
              rw [oddAF_apply]; split_ifs <;> norm_num)
          · rw [undampedKernel_support hkJ ε j (by omega), zero_mul, abs_zero]
      _ ≤ L := sum_le_sum_of_subset_of_nonneg (fun j hj => by
            obtain ⟨hjd, hjJ⟩ := mem_filter.mp hj
            exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hjd, hjJ⟩) fun _ _ _ => abs_nonneg _
  have hZ : Summable (fun d : ℕ => (d : ℝ) ^ (-(1 + ε))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hwd : ∀ d, |w d / d| ≤ L * (d : ℝ) ^ (-(1 + ε)) := fun d => by
    rw [dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hsign d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hs : Summable (fun d : ℕ => |w d / d|) :=
    (hZ.mul_left L).of_nonneg_of_le (fun _ => abs_nonneg _) hwd
  have hg := criticalWiener_dampedOddSqrtMoebius hε
  set mw := ∑' d : ℕ, w d / d
  have hmw : |mw| ≤ L * ∑' d : ℕ, (d : ℝ) ^ (-(1 + ε)) := by
    rw [← tsum_mul_left]
    calc |mw| ≤ ∑' d : ℕ, |w d / d| := by
          rw [← Real.norm_eq_abs]
          exact (norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using hs)).trans
            (le_of_eq (tsum_congr fun d => Real.norm_eq_abs _))
      _ ≤ ∑' d : ℕ, L * (d : ℝ) ^ (-(1 + ε)) := Summable.tsum_le_tsum hwd hs (hZ.mul_left L)
  have hmean : ∑' n : ℕ, RHTower.dirichletConv g w n / n = (∑' q : ℕ, g q / q) * mw :=
    (hasSum_dirichletConv_div hg.summable_abs_div.of_abs.hasSum hs.of_abs.hasSum
      hg.summable_abs_div hs).tsum_eq
  have hE := weightPronicEnergy_dampedSign_le hL hε (abs_sum_range_dirichletConv_oddAF_le hkJ hK) T
  set S := ∑' n : ℕ, (n : ℝ) ^ (2 * (1 / (2 + ε)) - 2)
  have hS : 0 ≤ S := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hw : pronicNorm (weightCenteredPrefix w mw) T ≤ 6 * L * Real.sqrt S := by
    rw [← Real.sqrt_sq (pronicNorm_nonneg _ T), ← weightPronicEnergy_eq_sq_pronicNorm]
    calc Real.sqrt (weightPronicEnergy w mw T) ≤ Real.sqrt (36 * L ^ 2 * S) := Real.sqrt_le_sqrt hE
      _ = 6 * L * Real.sqrt S := by
          rw [show 36 * L ^ 2 * S = (6 * L) ^ 2 * S by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity)]
  set G := oddSqfKernelNorm ε
  have hG : 0 ≤ G := tsum_nonneg fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have h1 := pronicNorm_dirichletConv_le (c := w) hg mw T
  have h3 : pronicNorm (weightCenteredPrefix (RHTower.dirichletConv g w)
      ((∑' q : ℕ, g q / q) * mw)) T ≤
      L * (G * (6 * Real.sqrt S + (Real.sqrt 2 + 1) * ∑' d : ℕ, (d : ℝ) ^ (-(1 + ε)))) := by
    calc _ ≤ G * pronicNorm (weightCenteredPrefix w mw) T + |mw| * ((Real.sqrt 2 + 1) * G) := h1
      _ ≤ G * (6 * L * Real.sqrt S) +
            (L * ∑' d : ℕ, (d : ℝ) ^ (-(1 + ε))) * ((Real.sqrt 2 + 1) * G) :=
          add_le_add (mul_le_mul_of_nonneg_left hw hG)
            (mul_le_mul_of_nonneg_right hmw (by positivity))
      _ = _ := by ring
  rw [dirichletConv_oddSqf_eq, hmean, weightPronicEnergy_eq_sq_pronicNorm, ← hLeq]
  calc _ ≤ (L * (G * (6 * Real.sqrt S + (Real.sqrt 2 + 1) * ∑' d : ℕ, (d : ℝ) ^ (-(1 + ε))))) ^ 2 :=
        pow_le_pow_left₀ (pronicNorm_nonneg _ _) h3 2
    _ = oddSqfReceiverConst ε * L ^ 2 := by unfold oddSqfReceiverConst; ring

/-! ### Admissible kernels -/

/-- The orientation-faithful norm `N(k) = Σ_j |k(j)| j^ε`. -/
def orientNorm (ε : ℝ) (k : ℕ → ℝ) : ℝ := ∑' j : ℕ, |k j| * (j : ℝ) ^ ε

/-- Admissible kernels: `N(k) < ∞`. -/
def OrientAdmissible (ε : ℝ) (k : ℕ → ℝ) : Prop := Summable fun j : ℕ => |k j| * (j : ℝ) ^ ε

/-- The pole pairing `P(k) = Σ_j k(j) j^{−(1−ε)}`: the value of the Dirichlet series at `1 − ε`. -/
def polePairing (ε : ℝ) (k : ℕ → ℝ) : ℝ := ∑' j : ℕ, k j * (j : ℝ) ^ (-(1 - ε))

theorem orientNorm_nonneg (ε : ℝ) (k : ℕ → ℝ) : 0 ≤ orientNorm ε k :=
  tsum_nonneg fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)

/-- `j^e ≤ j^ε` for every natural `j` and nonzero exponent `e ≤ ε`, `ε > 0`. -/
theorem natCast_rpow_le_rpow {ε e : ℝ} (hε : 0 < ε) (he : e ≤ ε) (he0 : e ≠ 0) (j : ℕ) :
    (j : ℝ) ^ e ≤ (j : ℝ) ^ ε := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [Real.zero_rpow he0, Real.zero_rpow hε.ne']
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) he

theorem OrientAdmissible.summable_rpow {ε e : ℝ} {k : ℕ → ℝ} (hk : OrientAdmissible ε k)
    (hε : 0 < ε) (he : e ≤ ε) (he0 : e ≠ 0) : Summable fun j : ℕ => |k j| * (j : ℝ) ^ e :=
  hk.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _))
    fun j => mul_le_mul_of_nonneg_left (natCast_rpow_le_rpow hε he he0 j) (abs_nonneg _)

theorem OrientAdmissible.criticalWiener {ε : ℝ} {k : ℕ → ℝ} (hk : OrientAdmissible ε k)
    (hε : 0 < ε) : CriticalWiener k :=
  hk.summable_rpow hε (by linarith) (by norm_num)

theorem OrientAdmissible.summable_abs_div {ε : ℝ} {k : ℕ → ℝ} (hk : OrientAdmissible ε k)
    (hε : 0 < ε) : Summable fun j : ℕ => |k j / j| :=
  (hk.summable_rpow hε (by linarith : (-1 : ℝ) ≤ ε) (by norm_num)).congr fun j => by
    rw [abs_div, Nat.abs_cast, Real.rpow_neg_one, div_eq_mul_inv]

theorem OrientAdmissible.summable_pole {ε : ℝ} {k : ℕ → ℝ} (hk : OrientAdmissible ε k)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) : Summable fun j : ℕ => k j * (j : ℝ) ^ (-(1 - ε)) :=
  Summable.of_abs ((hk.summable_rpow (e := -(1 - ε)) hε (by linarith) (by linarith)).congr
    fun j => by rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)])

theorem abs_oddSqfWeight_div_le {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    |oddSqfWeight ε d / d| ≤ (d : ℝ) ^ (-(1 + ε)) := by
  rw [oddSqfWeight, dampedSignWeight_div hε, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg d) _) (by
    rw [oddSqfAF_apply]; split_ifs <;> norm_num)

theorem summable_abs_oddSqfWeight_div {ε : ℝ} (hε : 0 < ε) :
    Summable fun d : ℕ => |oddSqfWeight ε d / d| :=
  (Real.summable_nat_rpow.mpr (by linarith : -(1 + ε) < -1)).of_nonneg_of_le
    (fun _ => abs_nonneg _) (abs_oddSqfWeight_div_le hε)

/-- The mean of `h ⋆ o` is the product of the means. -/
theorem tsum_dirichletConv_oddSqf_div {ε : ℝ} (hε : 0 < ε) {h : ℕ → ℝ}
    (hh : Summable fun j : ℕ => |h j / j|) :
    ∑' d : ℕ, RHTower.dirichletConv h (oddSqfWeight ε) d / d =
      (∑' j : ℕ, h j / j) * ∑' d : ℕ, oddSqfWeight ε d / d :=
  (hasSum_dirichletConv_div hh.of_abs.hasSum (summable_abs_oddSqfWeight_div hε).of_abs.hasSum hh
    (summable_abs_oddSqfWeight_div hε)).tsum_eq

theorem sum_Icc_eq_sum_range {g : ℕ → ℝ} (h0 : g 0 = 0) (n : ℕ) :
    ∑ j ∈ Icc 1 n, g j = ∑ j ∈ range (n + 1), g j := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega)]

/-- Partial sums over `[1, J]` of a summable series vanishing at `0` converge to its sum. -/
theorem tendsto_sum_Icc {g : ℕ → ℝ} (hg : Summable g) (h0 : g 0 = 0) :
    Tendsto (fun J => ∑ j ∈ Icc 1 J, g j) atTop (𝓝 (∑' j, g j)) := by
  simp_rw [sum_Icc_eq_sum_range h0]
  exact (hg.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

/-! ### Truncations on the paid hyperplane -/

/-- The truncation `k|_{[1,J]} − P_J δ₁`, which keeps the pole value zero. -/
def oddSqfTrunc (ε : ℝ) (k : ℕ → ℝ) (J j : ℕ) : ℝ :=
  (if j ∈ Icc 1 J then k j else 0) - (if j = 1 then poleValue k J ε else 0)

theorem oddSqfTrunc_support {ε : ℝ} {k : ℕ → ℝ} {J : ℕ} (hJ : 1 ≤ J) :
    ∀ j, J < j → oddSqfTrunc ε k J j = 0 := fun j hj => by
  unfold oddSqfTrunc
  rw [if_neg (by simp only [mem_Icc]; omega), if_neg (by omega), sub_zero]

theorem poleValue_oddSqfTrunc (ε : ℝ) (k : ℕ → ℝ) {J : ℕ} (hJ : 1 ≤ J) :
    poleValue (oddSqfTrunc ε k J) J ε = 0 := by
  unfold poleValue oddSqfTrunc
  have h : ∀ j ∈ Icc 1 J, ((if j ∈ Icc 1 J then k j else 0) - (if j = 1 then poleValue k J ε else 0)) *
      (j : ℝ) ^ (-(1 - ε)) = k j * (j : ℝ) ^ (-(1 - ε)) -
        (if j = 1 then poleValue k J ε * (j : ℝ) ^ (-(1 - ε)) else 0) := fun j hj => by
    rw [if_pos hj, sub_mul]; split_ifs <;> simp
  rw [sum_congr rfl h, sum_sub_distrib, sum_ite_eq' (Icc 1 J) 1, if_pos (by simp [hJ])]
  simp [poleValue]

theorem sum_abs_oddSqfTrunc_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) {J : ℕ} (hJ : 1 ≤ J) :
    ∑ j ∈ Icc 1 J, |oddSqfTrunc ε k J j| * (j : ℝ) ^ ε ≤ 2 * orientNorm ε k := by
  have hN : ∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε ≤ orientNorm ε k :=
    hk.sum_le_tsum _ fun j _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  have hP : |poleValue k J ε| ≤ orientNorm ε k := by
    refine (abs_sum_le_sum_abs _ _).trans (le_trans (sum_le_sum fun j _ => ?_) hN)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)]
    exact mul_le_mul_of_nonneg_left (natCast_rpow_le_rpow hε (by linarith) (by linarith) j)
      (abs_nonneg _)
  calc ∑ j ∈ Icc 1 J, |oddSqfTrunc ε k J j| * (j : ℝ) ^ ε
      ≤ ∑ j ∈ Icc 1 J, (|k j| * (j : ℝ) ^ ε + if j = 1 then |poleValue k J ε| else 0) := by
        refine sum_le_sum fun j hj => ?_
        unfold oddSqfTrunc
        rw [if_pos hj]
        by_cases h1 : j = 1
        · subst h1
          simp only [if_true, Nat.cast_one, Real.one_rpow, mul_one]
          exact abs_sub _ _
        · simp [h1]
    _ = ∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε + |poleValue k J ε| := by
        rw [sum_add_distrib, sum_ite_eq' (Icc 1 J) 1, if_pos (by simp [hJ])]
    _ ≤ 2 * orientNorm ε k := by linarith

theorem dirichletConv_oddSqfTrunc (ε : ℝ) (k : ℕ → ℝ) {J d : ℕ} (hd : 1 ≤ d) (hdJ : d ≤ J) :
    RHTower.dirichletConv (oddSqfTrunc ε k J) (oddSqfWeight ε) d =
      RHTower.dirichletConv k (oddSqfWeight ε) d - poleValue k J ε * oddSqfWeight ε d := by
  unfold RHTower.dirichletConv oddSqfTrunc
  have h : ∀ e ∈ d.divisors, ((if e ∈ Icc 1 J then k e else 0) -
      (if e = 1 then poleValue k J ε else 0)) * oddSqfWeight ε (d / e) =
      k e * oddSqfWeight ε (d / e) - if e = 1 then poleValue k J ε * oddSqfWeight ε (d / e) else 0 :=
    fun e he => by
      have h1 := Nat.pos_of_mem_divisors he
      have h2 := Nat.divisor_le he
      rw [if_pos (mem_Icc.2 ⟨h1, h2.trans hdJ⟩), sub_mul]
      split_ifs <;> simp
  rw [sum_congr rfl h, sum_sub_distrib, sum_ite_eq' d.divisors 1,
    if_pos (Nat.one_mem_divisors.2 (by omega)), Nat.div_one]

theorem tsum_oddSqfTrunc_div (ε : ℝ) (k : ℕ → ℝ) (J : ℕ) :
    ∑' j : ℕ, oddSqfTrunc ε k J j / j = ∑ j ∈ Icc 1 J, k j / j - poleValue k J ε := by
  rw [tsum_eq_sum (s := Icc 1 J) fun j hj => by
    unfold oddSqfTrunc
    rw [if_neg hj]
    by_cases h1 : j = 1
    · subst h1
      have hJ : J = 0 := by simp only [mem_Icc, le_refl, true_and, not_le] at hj; omega
      subst hJ
      simp [poleValue]
    · rw [if_neg h1]; simp]
  unfold oddSqfTrunc
  have h : ∀ j ∈ Icc 1 J, ((if j ∈ Icc 1 J then k j else 0) - (if j = 1 then poleValue k J ε else 0)) /
      (j : ℝ) = k j / j - if j = 1 then poleValue k J ε else 0 := fun j hj => by
    rw [if_pos hj]; split_ifs with h1 <;> simp [h1]
  rw [sum_congr rfl h, sum_sub_distrib, sum_ite_eq' (Icc 1 J) 1]
  split_ifs with h1
  · rfl
  · rw [mem_Icc] at h1
    have hJ : J = 0 := by omega
    subst hJ
    simp [poleValue]

/-- The receiver energy at cutoff `T` of `c − a o` with centring `b`. -/
def truncEnergy (c o : ℕ → ℝ) (T : ℕ) (a b : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 T, ((∑ j ∈ Icc 1 n, ∑ d ∈ j.divisors, (c d - a * o d)) - b * n) ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))

theorem continuous_truncEnergy (c o : ℕ → ℝ) (T : ℕ) :
    Continuous fun p : ℝ × ℝ => truncEnergy c o T p.1 p.2 := by
  unfold truncEnergy
  fun_prop

theorem weightPronicEnergy_eq_truncEnergy {c o h : ℕ → ℝ} {T : ℕ} {a : ℝ}
    (hh : ∀ d, 1 ≤ d → d ≤ T → h d = c d - a * o d) (b : ℝ) :
    weightPronicEnergy h b T = truncEnergy c o T a b := by
  unfold weightPronicEnergy weightCenteredPrefix truncEnergy
  refine sum_congr rfl fun n hn => ?_
  congr 3
  refine sum_congr rfl fun j hj => sum_congr rfl fun d hd => ?_
  have hn' := (mem_Icc.1 hn).2
  have hj' := (mem_Icc.1 hj).2
  exact hh d (Nat.pos_of_mem_divisors hd) ((Nat.divisor_le hd).trans (hj'.trans hn'))

/-- The pole values of an admissible kernel converge to its pole pairing. -/
theorem tendsto_poleValue {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) :
    Tendsto (fun J => poleValue k J ε) atTop (𝓝 (polePairing ε k)) :=
  tendsto_sum_Icc (hk.summable_pole hε hε2) (by
    rw [Nat.cast_zero, Real.zero_rpow (show -(1 - ε) ≠ 0 by linarith), mul_zero])

/-- The means of the truncations converge to the mean of `k ⋆ o` on the paid hyperplane. -/
theorem tendsto_mean_oddSqfTrunc {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) (hP : polePairing ε k = 0) :
    Tendsto (fun J => (∑ j ∈ Icc 1 J, k j / j - poleValue k J ε) *
        ∑' d : ℕ, oddSqfWeight ε d / d) atTop
      (𝓝 (∑' d : ℕ, RHTower.dirichletConv k (oddSqfWeight ε) d / d)) := by
  rw [tsum_dirichletConv_oddSqf_div hε (hk.summable_abs_div hε)]
  refine Tendsto.mul_const _ ?_
  have h := (tendsto_sum_Icc (hk.summable_abs_div hε).of_abs (by simp)).sub
    (tendsto_poleValue hε hε2 hk)
  rwa [hP, sub_zero] at h

/-- The truncation energies are bounded by `4 C_ε N(k)²` beyond the cutoff. -/
theorem truncEnergy_oddSqfTrunc_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk : OrientAdmissible ε k) {T J : ℕ} (hJ1 : 1 ≤ J) (hJT : T ≤ J) :
    truncEnergy (RHTower.dirichletConv k (oddSqfWeight ε)) (oddSqfWeight ε) T (poleValue k J ε)
        ((∑ j ∈ Icc 1 J, k j / j - poleValue k J ε) * ∑' d : ℕ, oddSqfWeight ε d / d) ≤
      4 * oddSqfReceiverConst ε * orientNorm ε k ^ 2 := by
  have hfin := weightPronicEnergy_dirichletConv_oddSqf_le_finite hε (oddSqfTrunc_support hJ1)
    (poleValue_oddSqfTrunc ε k hJ1) T
  have hsum : Summable fun j : ℕ => |oddSqfTrunc ε k J j / j| := by
    refine summable_of_ne_finset_zero (s := Icc 1 J) fun j hj => ?_
    unfold oddSqfTrunc
    rw [if_neg hj]
    by_cases h1 : j = 1
    · exact absurd (by simp [h1, hJ1]) hj
    · rw [if_neg h1]; simp
  have hmeanJ := tsum_dirichletConv_oddSqf_div hε hsum
  rw [tsum_oddSqfTrunc_div] at hmeanJ
  have hE := weightPronicEnergy_eq_truncEnergy (c := RHTower.dirichletConv k (oddSqfWeight ε))
    (o := oddSqfWeight ε) (h := RHTower.dirichletConv (oddSqfTrunc ε k J) (oddSqfWeight ε))
    (T := T) (a := poleValue k J ε)
    (fun d hd hdT => dirichletConv_oddSqfTrunc ε k hd (hdT.trans hJT))
    ((∑ j ∈ Icc 1 J, k j / j - poleValue k J ε) * ∑' d : ℕ, oddSqfWeight ε d / d)
  rw [← hE, ← hmeanJ]
  refine hfin.trans ?_
  have h2 := sum_abs_oddSqfTrunc_le hε hε2 hk hJ1
  have h0 : 0 ≤ ∑ j ∈ Icc 1 J, |oddSqfTrunc ε k J j| * (j : ℝ) ^ ε :=
    sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  calc oddSqfReceiverConst ε * (∑ j ∈ Icc 1 J, |oddSqfTrunc ε k J j| * (j : ℝ) ^ ε) ^ 2
      ≤ oddSqfReceiverConst ε * (2 * orientNorm ε k) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h2 2) (oddSqfReceiverConst_nonneg ε)
    _ = 4 * oddSqfReceiverConst ε * orientNorm ε k ^ 2 := by ring

/-- **The receiver is bounded on the paid hyperplane**: for an admissible kernel with vanishing
pole pairing, every receiver energy of `k ⋆ o` is at most `4 C_ε N(k)²`. -/
theorem weightPronicEnergy_dirichletConv_oddSqf_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk : OrientAdmissible ε k) (hP : polePairing ε k = 0) (T : ℕ) :
    weightPronicEnergy (RHTower.dirichletConv k (oddSqfWeight ε))
        (∑' d : ℕ, RHTower.dirichletConv k (oddSqfWeight ε) d / d) T ≤
      4 * oddSqfReceiverConst ε * orientNorm ε k ^ 2 := by
  have hP0 : Tendsto (fun J => poleValue k J ε) atTop (𝓝 0) := hP ▸ tendsto_poleValue hε hε2 hk
  have hlim := ((continuous_truncEnergy (RHTower.dirichletConv k (oddSqfWeight ε))
    (oddSqfWeight ε) T).tendsto _).comp (hP0.prodMk_nhds (tendsto_mean_oddSqfTrunc hε hε2 hk hP))
  rw [weightPronicEnergy_eq_truncEnergy (c := RHTower.dirichletConv k (oddSqfWeight ε))
    (o := oddSqfWeight ε) (a := 0) (fun d _ _ => by ring)]
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨max T 1, fun J hJ =>
    truncEnergy_oddSqfTrunc_le hε hε2 hk ((le_max_right _ _).trans hJ) ((le_max_left _ _).trans hJ)⟩)

/-- **Payment over `o` is the closed hyperplane `P = 0`**, for every admissible kernel. -/
theorem receiverBounded_dirichletConv_oddSqf_iff_admissible {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ↔ polePairing ε k = 0 := by
  constructor
  · intro hB
    by_contra hK
    have hD : 0 < RHTower.Sieve.squarefreeDensity := by
      rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
    exact not_receiverBounded_dirichletConv_of_drift_critical hε hε2 (oddSqfWeight_nonneg ε)
      (oddSqfWeight_mem_dampedClass ε) (by positivity) (eventually_oddSqfWeight_drift hε)
      (hk.criticalWiener hε) hK hB
  · intro hP
    exact ⟨_, weightPronicEnergy_dirichletConv_oddSqf_le hε hε2 hk hP⟩

/-! ### The flip is a bounded involution -/

theorem injective_two_mul : Function.Injective fun m : ℕ => 2 * m := fun a b h => by
  simp only at h; omega

/-- A series supported on the even integers is its series over `2m`. -/
theorem tsum_eq_tsum_two_mul {F : ℕ → ℝ} (hF : ∀ j, ¬ 2 ∣ j → F j = 0) :
    ∑' j : ℕ, F j = ∑' m : ℕ, F (2 * m) := by
  refine (injective_two_mul.tsum_eq fun j hj => ?_).symm
  by_contra h
  exact hj (hF j fun ⟨m, hm⟩ => h ⟨m, hm.symm⟩)

theorem summable_iff_two_mul {F : ℕ → ℝ} (hF : ∀ j, ¬ 2 ∣ j → F j = 0) :
    Summable F ↔ Summable fun m : ℕ => F (2 * m) :=
  (injective_two_mul.summable_iff fun j hj => hF j fun ⟨m, hm⟩ => hj ⟨m, hm.symm⟩).symm

theorem abs_evenPartWeight_le (k : ℕ → ℝ) (j : ℕ) : |evenPartWeight k j| ≤ |k (2 * j)| := by
  unfold evenPartWeight; split_ifs <;> simp

theorem summable_two_mul {ε : ℝ} {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    Summable fun m : ℕ => |k (2 * m)| * ((2 * m : ℕ) : ℝ) ^ ε :=
  hk.comp_injective injective_two_mul

theorem tsum_two_mul_le {ε : ℝ} {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    ∑' m : ℕ, |k (2 * m)| * ((2 * m : ℕ) : ℝ) ^ ε ≤ orientNorm ε k :=
  tsum_comp_le_tsum_of_inj hk
    (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)) injective_two_mul

/-- The even part is dominated by the even values: `|k_e(m)| m^ε ≤ |k(2m)| (2m)^ε`. -/
theorem evenPart_le {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ → ℝ) (m : ℕ) :
    |evenPartWeight k m| * (m : ℝ) ^ ε ≤ |k (2 * m)| * ((2 * m : ℕ) : ℝ) ^ ε :=
  mul_le_mul (abs_evenPartWeight_le k m) (Real.rpow_le_rpow (Nat.cast_nonneg m)
    (by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) hε)
    (Real.rpow_nonneg (Nat.cast_nonneg m) _) (abs_nonneg _)

theorem shiftTwo_two_mul (b : ℕ → ℝ) (m : ℕ) : shiftTwo b (2 * m) = b m := by
  unfold shiftTwo; rw [if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m two_pos]

theorem shiftTwo_of_not_dvd (b : ℕ → ℝ) {j : ℕ} (hj : ¬ 2 ∣ j) : shiftTwo b j = 0 := if_neg hj

theorem OrientAdmissible.evenPart {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    OrientAdmissible ε (evenPartWeight k) :=
  (summable_two_mul hk).of_nonneg_of_le
    (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)) (evenPart_le hε k)

theorem OrientAdmissible.shiftEven {ε : ℝ} {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    OrientAdmissible ε (shiftTwo (evenPartWeight k)) := by
  unfold OrientAdmissible
  rw [summable_iff_two_mul fun j hj => by rw [shiftTwo_of_not_dvd _ hj, abs_zero, zero_mul]]
  refine (summable_two_mul hk).of_nonneg_of_le
    (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) fun m => ?_
  rw [shiftTwo_two_mul]
  exact mul_le_mul_of_nonneg_right (abs_evenPartWeight_le k m) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem abs_oddPartKernel_le (k : ℕ → ℝ) (j : ℕ) : |oddPartKernel k j| ≤ |k j| := by
  unfold oddPartKernel; split_ifs <;> simp

theorem OrientAdmissible.oddPart {ε : ℝ} {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    OrientAdmissible ε (oddPartKernel k) :=
  hk.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _))
    fun j => mul_le_mul_of_nonneg_right (abs_oddPartKernel_le k j)
      (Real.rpow_nonneg (Nat.cast_nonneg j) _)

theorem abs_flipKernelOf_le (k : ℕ → ℝ) (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    |flipKernelOf k j| * x ≤ |oddPartKernel k j| * x + |evenPartWeight k j| * x +
      |shiftTwo (evenPartWeight k) j| * x := by
  rw [← add_mul, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ hx
  unfold flipKernelOf
  exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)

/-- The flip keeps admissibility. -/
theorem OrientAdmissible.flip {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    OrientAdmissible ε (flipKernelOf k) :=
  ((hk.oddPart.add (hk.evenPart hε)).add (hk.shiftEven)).of_nonneg_of_le
    (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _))
    fun j => abs_flipKernelOf_le k j _ (Real.rpow_nonneg (Nat.cast_nonneg j) _)

/-- **The companion class is continuous**: `N(k^♭) ≤ 3 N(k)`. -/
theorem orientNorm_flipKernelOf_le {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ → ℝ} (hk : OrientAdmissible ε k) :
    orientNorm ε (flipKernelOf k) ≤ 3 * orientNorm ε k := by
  have h1 : orientNorm ε (oddPartKernel k) ≤ orientNorm ε k :=
    Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right (abs_oddPartKernel_le k j)
      (Real.rpow_nonneg (Nat.cast_nonneg j) _)) hk.oddPart hk
  have h2 : orientNorm ε (evenPartWeight k) ≤ orientNorm ε k :=
    (Summable.tsum_le_tsum (evenPart_le hε k) (hk.evenPart hε) (summable_two_mul hk)).trans
      (tsum_two_mul_le hk)
  have h3 : orientNorm ε (shiftTwo (evenPartWeight k)) ≤ orientNorm ε k := by
    unfold orientNorm
    rw [tsum_eq_tsum_two_mul fun j hj => by rw [shiftTwo_of_not_dvd _ hj, abs_zero, zero_mul]]
    refine (Summable.tsum_le_tsum (fun m => ?_) ?_ (summable_two_mul hk)).trans (tsum_two_mul_le hk)
    · rw [shiftTwo_two_mul]
      exact mul_le_mul_of_nonneg_right (abs_evenPartWeight_le k m)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exact (summable_iff_two_mul fun j hj => by
        rw [shiftTwo_of_not_dvd _ hj, abs_zero, zero_mul]).1 (hk.shiftEven)
  calc orientNorm ε (flipKernelOf k)
      ≤ orientNorm ε (oddPartKernel k) + orientNorm ε (evenPartWeight k) +
          orientNorm ε (shiftTwo (evenPartWeight k)) := by
        unfold orientNorm
        calc ∑' j : ℕ, |flipKernelOf k j| * (j : ℝ) ^ ε
            ≤ ∑' j : ℕ, (|oddPartKernel k j| * (j : ℝ) ^ ε + |evenPartWeight k j| * (j : ℝ) ^ ε +
                |shiftTwo (evenPartWeight k) j| * (j : ℝ) ^ ε) :=
              Summable.tsum_le_tsum (fun j => abs_flipKernelOf_le k j _
                (Real.rpow_nonneg (Nat.cast_nonneg j) _)) (hk.flip hε)
                ((hk.oddPart.add (hk.evenPart hε)).add (hk.shiftEven))
          _ = _ := by
              rw [(hk.oddPart.add (hk.evenPart hε)).tsum_add (hk.shiftEven),
                hk.oddPart.tsum_add (hk.evenPart hε)]
    _ ≤ 3 * orientNorm ε k := by linarith

/-- For kernels vanishing on multiples of four the kernel flip is the even flip. -/
theorem flipKernelOf_eq_evenFlip {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) :
    flipKernelOf k = evenFlip k := by
  funext j
  rw [evenFlip_apply]
  unfold flipKernelOf oddPartKernel evenPartWeight shiftTwo
  by_cases h1 : j % 2 = 1
  · have h2 : ¬ 2 ∣ j := by omega
    simp [h1, h2]
  · have h2 : 2 ∣ j := by omega
    by_cases h4 : (j / 2) % 2 = 1
    · have h5 : 2 * (j / 2) = j := Nat.mul_div_cancel' h2
      simp [h1, h2, h4, h5]
    · have h5 : 4 ∣ j := by omega
      simp [h1, h2, h4, hk4 j h5]

/-- **The flip is an involution** of the four-free kernels. -/
theorem flipKernelOf_flipKernelOf {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) :
    flipKernelOf (flipKernelOf k) = k := by
  rw [flipKernelOf_eq_evenFlip hk4, flipKernelOf_eq_evenFlip (evenFlip_fourFree hk4),
    evenFlip_evenFlip]

/-- The even flip of `k ⋆ o` is `k^♭ ⋆ o`. -/
theorem evenFlip_dirichletConv_oddSqf {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) (ε : ℝ) :
    evenFlip (RHTower.dirichletConv k (oddSqfWeight ε)) =
      RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε) := by
  rw [dirichletConv_flipKernelOf hk4 ε]
  rfl

/-! ### The orientation coordinates -/

/-- The flip negates the even part. -/
theorem evenPartWeight_flipKernelOf (k : ℕ → ℝ) :
    evenPartWeight (flipKernelOf k) = fun j => -evenPartWeight k j := by
  funext j
  by_cases h : j % 2 = 1
  · have h2 : (2 * j) % 2 ≠ 1 := by omega
    have e0 : oddPartKernel k (2 * j) = 0 := by unfold oddPartKernel; rw [if_neg h2]
    have e1 : evenPartWeight k (2 * j) = 0 := by unfold evenPartWeight; rw [if_neg h2]
    have e2 : evenPartWeight (flipKernelOf k) j = flipKernelOf k (2 * j) := by
      unfold evenPartWeight; rw [if_pos h]
    have e3 : evenPartWeight k j = k (2 * j) := by unfold evenPartWeight; rw [if_pos h]
    rw [e2, e3]
    unfold flipKernelOf
    rw [e0, e1, shiftTwo_two_mul, e3]
    ring
  · have e2 : evenPartWeight (flipKernelOf k) j = 0 := by unfold evenPartWeight; rw [if_neg h]
    have e3 : evenPartWeight k j = 0 := by unfold evenPartWeight; rw [if_neg h]
    rw [e2, e3, neg_zero]

theorem OrientAdmissible.summable_pole_abs {ε : ℝ} {k : ℕ → ℝ} (hk : OrientAdmissible ε k)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) : Summable fun j : ℕ => |k j * (j : ℝ) ^ (-(1 - ε))| :=
  (hk.summable_rpow (e := -(1 - ε)) hε (by linarith) (by linarith)).congr fun j => by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)]

/-- **The flip moves the pole pairing by the even part**: `P(k^♭) = P(k) + (1 − 2^ε) P(k_e)`. -/
theorem polePairing_flipKernelOf {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k m = 0) (hk : OrientAdmissible ε k) :
    polePairing ε (flipKernelOf k) =
      polePairing ε k + (1 - (2 : ℝ) ^ ε) * polePairing ε (evenPartWeight k) := by
  set e := evenPartWeight k
  have so := (hk.oddPart.summable_pole hε hε2)
  have se := ((hk.evenPart hε.le).summable_pole hε hε2)
  have ss := ((hk.shiftEven).summable_pole hε hε2)
  -- the dilated part pairs to `2^{ε−1}` times the even part
  have hshift : polePairing ε (shiftTwo e) = (2 : ℝ) ^ (ε - 1) * polePairing ε e := by
    unfold polePairing
    rw [tsum_eq_tsum_two_mul fun j hj => by rw [shiftTwo_of_not_dvd _ hj, zero_mul], ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [shiftTwo_two_mul, Nat.cast_mul, Nat.cast_two,
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg m), show -(1 - ε) = ε - 1 by ring]
    ring
  have hk' : polePairing ε k = polePairing ε (oddPartKernel k) + polePairing ε (shiftTwo e) := by
    unfold polePairing
    rw [← so.tsum_add ss]
    exact tsum_congr fun j => by rw [kernel_eq_odd_add_shift hk4 j]; ring
  have hflip : polePairing ε (flipKernelOf k) =
      polePairing ε (oddPartKernel k) + polePairing ε e - polePairing ε (shiftTwo e) := by
    unfold polePairing
    rw [← so.tsum_add se, ← (so.add se).tsum_sub ss]
    exact tsum_congr fun j => by unfold flipKernelOf; ring
  have h2 : (2 : ℝ) * (2 : ℝ) ^ (ε - 1) = (2 : ℝ) ^ ε := by
    rw [show ε = 1 + (ε - 1) by ring, Real.rpow_add two_pos, Real.rpow_one]; ring_nf
  rw [hflip, hk', hshift]
  linear_combination (-(polePairing ε e)) * h2

/-- The flip negates the even-part pole pairing. -/
theorem polePairing_evenPart_flipKernelOf (ε : ℝ) (k : ℕ → ℝ) :
    polePairing ε (evenPartWeight (flipKernelOf k)) = -polePairing ε (evenPartWeight k) := by
  unfold polePairing
  rw [evenPartWeight_flipKernelOf, ← tsum_neg]
  exact tsum_congr fun j => by ring

/-! ### Both members of a flip pair -/

/-- **Payment of the companion**: `(k ⋆ o)^♭` is paid iff `P(k) + (1 − 2^ε) P(k_e) = 0`. -/
theorem receiverBounded_evenFlip_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k m = 0) (hk : OrientAdmissible ε k) :
    ReceiverBounded (evenFlip (RHTower.dirichletConv k (oddSqfWeight ε))) ↔
      polePairing ε k + (1 - (2 : ℝ) ^ ε) * polePairing ε (evenPartWeight k) = 0 := by
  rw [evenFlip_dirichletConv_oddSqf hk4, receiverBounded_dirichletConv_oddSqf_iff_admissible hε hε2
    (hk.flip hε.le), polePairing_flipKernelOf hε hε2 hk4 hk]

/-- **Both members of a flip pair are paid iff both orientation coordinates vanish.** -/
theorem receiverBounded_and_evenFlip_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k m = 0) (hk : OrientAdmissible ε k) :
    (ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ∧
        ReceiverBounded (evenFlip (RHTower.dirichletConv k (oddSqfWeight ε)))) ↔
      (polePairing ε k = 0 ∧ polePairing ε (evenPartWeight k) = 0) := by
  rw [receiverBounded_dirichletConv_oddSqf_iff_admissible hε hε2 hk,
    receiverBounded_evenFlip_iff hε hε2 hk4 hk]
  have h2 : (1 : ℝ) - (2 : ℝ) ^ ε ≠ 0 := by
    have : (1 : ℝ) < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
    linarith
  constructor
  · rintro ⟨h1, h3⟩
    rw [h1, zero_add] at h3
    exact ⟨h1, (mul_eq_zero.1 h3).resolve_left h2⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, by rw [h1, h3]; ring⟩

/-- **On the doubly paid subspace both receivers are bounded by the norm**: if `P(k) = P(k_e) = 0`
then `E_T(k ⋆ o) ≤ 4 C_ε N(k)²` and `E_T((k ⋆ o)^♭) ≤ 36 C_ε N(k)²` at every cutoff. -/
theorem weightPronicEnergy_evenFlip_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k m = 0) (hk : OrientAdmissible ε k) (hP : polePairing ε k = 0)
    (hPe : polePairing ε (evenPartWeight k) = 0) (T : ℕ) :
    weightPronicEnergy (evenFlip (RHTower.dirichletConv k (oddSqfWeight ε)))
        (∑' d : ℕ, evenFlip (RHTower.dirichletConv k (oddSqfWeight ε)) d / d) T ≤
      36 * oddSqfReceiverConst ε * orientNorm ε k ^ 2 := by
  rw [evenFlip_dirichletConv_oddSqf hk4]
  have hP' : polePairing ε (flipKernelOf k) = 0 := by
    rw [polePairing_flipKernelOf hε hε2 hk4 hk, hP, hPe]; ring
  refine (weightPronicEnergy_dirichletConv_oddSqf_le hε hε2 (hk.flip hε.le) hP' T).trans ?_
  have hN := orientNorm_flipKernelOf_le hε.le hk
  have h0 := orientNorm_nonneg ε (flipKernelOf k)
  have hC := oddSqfReceiverConst_nonneg ε
  calc 4 * oddSqfReceiverConst ε * orientNorm ε (flipKernelOf k) ^ 2
      ≤ 4 * oddSqfReceiverConst ε * (3 * orientNorm ε k) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hN 2) (by positivity)
    _ = 36 * oddSqfReceiverConst ε * orientNorm ε k ^ 2 := by ring

end

end GaloisForLFunctions.ArithmeticOrientationTheory
