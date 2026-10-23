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
  Summable.of_abs ((hk.summable_rpow hε (by linarith) (by linarith)).congr fun j => by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)])

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
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < n + 1), h0, zero_add,
    Nat.Ico_succ_right]

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
    · exact absurd (by simp [h1]) hj
    · rw [if_neg h1]; simp]
  unfold oddSqfTrunc
  have h : ∀ j ∈ Icc 1 J, ((if j ∈ Icc 1 J then k j else 0) - (if j = 1 then poleValue k J ε else 0)) /
      (j : ℝ) = k j / j - if j = 1 then poleValue k J ε else 0 := fun j hj => by
    rw [if_pos hj]; split_ifs with h1 <;> simp [h1, sub_div]
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

/-- **The receiver is bounded on the paid hyperplane**: for an admissible kernel with vanishing
pole pairing, every receiver energy of `k ⋆ o` is at most `4 C_ε N(k)²`. -/
theorem weightPronicEnergy_dirichletConv_oddSqf_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} (hk : OrientAdmissible ε k) (hP : polePairing ε k = 0) (T : ℕ) :
    weightPronicEnergy (RHTower.dirichletConv k (oddSqfWeight ε))
        (∑' d : ℕ, RHTower.dirichletConv k (oddSqfWeight ε) d / d) T ≤
      4 * oddSqfReceiverConst ε * orientNorm ε k ^ 2 := by
  set c := RHTower.dirichletConv k (oddSqfWeight ε)
  set o := oddSqfWeight ε
  set O := ∑' d : ℕ, o d / d
  have hmean : ∑' d : ℕ, c d / d = (∑' j : ℕ, k j / j) * O :=
    tsum_dirichletConv_oddSqf_div hε (hk.summable_abs_div hε)
  -- the pole values and the means of the truncations converge
  have hPJ : Tendsto (fun J => poleValue k J ε) atTop (𝓝 0) := by
    rw [← hP]
    exact tendsto_sum_Icc (hk.summable_pole hε hε2) (by
      simp [Real.zero_rpow (by linarith : -(1 - ε) ≠ 0)])
  have hmJ : Tendsto (fun J => (∑ j ∈ Icc 1 J, k j / j - poleValue k J ε) * O) atTop
      (𝓝 (∑' d : ℕ, c d / d)) := by
    rw [hmean]
    refine Tendsto.mul_const O ?_
    have := (tendsto_sum_Icc (hk.summable_abs_div hε).of_abs (by simp)).sub hPJ
    rwa [sub_zero] at this
  have hlim : Tendsto (fun J => truncEnergy c o T (poleValue k J ε)
      ((∑ j ∈ Icc 1 J, k j / j - poleValue k J ε) * O)) atTop
      (𝓝 (truncEnergy c o T 0 (∑' d : ℕ, c d / d))) :=
    ((continuous_truncEnergy c o T).tendsto _).comp (hPJ.prodMk_nhds hmJ)
  have hT : weightPronicEnergy c (∑' d : ℕ, c d / d) T =
      truncEnergy c o T 0 (∑' d : ℕ, c d / d) :=
    weightPronicEnergy_eq_truncEnergy (fun d _ _ => by ring) _
  rw [hT]
  refine le_of_tendsto hlim (eventually_atTop.2 ⟨max T 1, fun J hJ => ?_⟩)
  have hJ1 : 1 ≤ J := (le_max_right _ _).trans hJ
  have hJT : T ≤ J := (le_max_left _ _).trans hJ
  have hfin := weightPronicEnergy_dirichletConv_oddSqf_le_finite hε (oddSqfTrunc_support hJ1)
    (poleValue_oddSqfTrunc ε k hJ1) T
  have hmeanJ : ∑' d : ℕ, RHTower.dirichletConv (oddSqfTrunc ε k J) o d / d =
      (∑ j ∈ Icc 1 J, k j / j - poleValue k J ε) * O := by
    rw [tsum_dirichletConv_oddSqf_div hε, tsum_oddSqfTrunc_div]
    refine summable_of_ne_finset_zero (s := Icc 1 J) fun j hj => ?_
    unfold oddSqfTrunc
    rw [if_neg hj]
    by_cases h1 : j = 1
    · exact absurd (by simp [h1, hJ1]) hj
    · rw [if_neg h1]; simp
  rw [hmeanJ, weightPronicEnergy_eq_truncEnergy (c := c) (o := o)
    (fun d hd hdT => dirichletConv_oddSqfTrunc ε k hd (hdT.trans hJT))] at hfin
  refine hfin.trans ?_
  have h2 := sum_abs_oddSqfTrunc_le hε hε2 hk hJ1
  have h0 : 0 ≤ ∑ j ∈ Icc 1 J, |oddSqfTrunc ε k J j| * (j : ℝ) ^ ε :=
    sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  have hC := oddSqfReceiverConst_nonneg ε
  calc oddSqfReceiverConst ε * (∑ j ∈ Icc 1 J, |oddSqfTrunc ε k J j| * (j : ℝ) ^ ε) ^ 2
      ≤ oddSqfReceiverConst ε * (2 * orientNorm ε k) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h2 2) hC
    _ = 4 * oddSqfReceiverConst ε * orientNorm ε k ^ 2 := by ring

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

end

end GaloisForLFunctions.ArithmeticOrientationTheory
