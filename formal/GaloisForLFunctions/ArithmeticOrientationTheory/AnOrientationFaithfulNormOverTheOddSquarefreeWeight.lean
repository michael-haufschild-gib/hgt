import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheEvenFlipShiftsThePoleValueByTheEvenPartOfTheKernel
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerKernelsRepairAPositiveDriftOnlyAtItsPole

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

end

end GaloisForLFunctions.ArithmeticOrientationTheory
