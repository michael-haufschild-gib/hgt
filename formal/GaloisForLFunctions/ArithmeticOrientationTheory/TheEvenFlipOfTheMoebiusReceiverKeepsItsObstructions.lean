import GaloisForLFunctions.ArithmeticOrientationTheory.TheCalculusOfTheObstructionHull
import GaloisForLFunctions.ArithmeticOrientationTheory.TheOffLineZerosObstructTheMoebiusReceiver
import GaloisForLFunctions.ArithmeticOrientationTheory.TheEvenFlipIsReadAtThePrimeTwo
import GaloisForLFunctions.ArithmeticOrientationTheory.AKernelBoundedBelowOnTheHalfPlaneIsAUnit

/-!
# The even flip of the Möbius receiver keeps its obstructions

On a four-free weight that is multiplicative at `2`, `c = (δ₁ + x δ₂) ⋆ o` with `o` supported on odd
integers, the even flip is a convolution:

  `c♭ = ((1 + x) δ₁ − x δ₂) ⋆ o`  (`evenFlip_dirichletConv_twoPoint`).

So the flip acts on the obstruction hull through the 2-local kernel `n_x = (1 + x)δ₁ − xδ₂`: when
`δ₁ + xδ₂` is a unit (`|x| < √2`), `hull(c♭) ⊆ hull(c)`, and a point leaves only where
`n̂_x(ω) = (1 + x) − x ω(2)/√2` vanishes (`obstructionHull_evenFlip_subset`,
`mem_obstructionHull_evenFlip`); when `n_x` is a unit too the flip does not move the repairing ideal
at all (`paidIdeal_evenFlip_eq`).

For the damped Möbius weight `x = −2^{−ε}` (`pmPowerDampedRealWeight_eq_dirichletConv`):

* payment survives the flip (`receiverBounded_evenFlip_moebius`);
* every off-line zero `ρ` with `½ + ε < Re ρ < 1` and `ζ(ρ − ε) ≠ 0` still obstructs the flipped
  weight at `ρ − ε`, unless `2^{−ρ} = 2^{−ε} − 1` (`mem_obstructionHull_evenFlip_moebius_of_zero`);
* yet the flip is not invertible on the receiver for `ε ≤ ½` (`not_isWienerUnit_flipKernel_moebius`):
  `n̂` vanishes at `ω(2) = −√2(2^ε − 1)` inside the disk.

Contrast with the Fermi weight, whose flip creates a pole obstruction: on the Möbius receiver the
orientation of the prime `2` neither creates nor (off one curve) removes obstructions.
-/

open Finset ArithmeticFunction LSeries Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### Kernels supported on `{1, 2}` -/

/-- The kernel `a δ₁ + b δ₂`. -/
def twoPoint (a b : ℝ) : ℕ → ℝ := fun n => if n = 1 then a else if n = 2 then b else 0

theorem dirichletConv_twoPoint (a b : ℝ) (g : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    RHTower.dirichletConv (twoPoint a b) g n = a * g n + b * (if 2 ∣ n then g (n / 2) else 0) := by
  unfold RHTower.dirichletConv
  have hterm : ∀ d ∈ n.divisors, twoPoint a b d * g (n / d) =
      (if d = 1 then a * g n else 0) + (if d = 2 then b * g (n / 2) else 0) := by
    intro d _
    unfold twoPoint
    by_cases h1 : d = 1
    · subst h1; simp
    · by_cases h2 : d = 2
      · subst h2; simp
      · simp [h1, h2]
  rw [sum_congr rfl hterm, sum_add_distrib, sum_ite_eq', sum_ite_eq',
    if_pos (Nat.one_mem_divisors.2 hn)]
  by_cases h2n : 2 ∣ n
  · rw [if_pos (Nat.mem_divisors.2 ⟨h2n, hn⟩), if_pos h2n]
  · rw [if_neg (fun h => h2n (Nat.mem_divisors.1 h).1), if_neg h2n]; ring

theorem dirichletConv_twoPoint_zero (a b : ℝ) (g : ℕ → ℝ) :
    RHTower.dirichletConv (twoPoint a b) g 0 = 0 := by
  simp [RHTower.dirichletConv]

theorem criticalWiener_twoPoint (a b : ℝ) : CriticalWiener (twoPoint a b) := by
  unfold CriticalWiener
  refine summable_of_ne_finset_zero (s := {1, 2}) fun n hn => ?_
  simp only [mem_insert, mem_singleton, not_or] at hn
  simp [twoPoint, hn.1, hn.2]

theorem twoPoint_one_eq (x : ℝ) : twoPoint 1 x = localFactorKernel 2 (-x) := by
  funext n; simp [twoPoint, localFactorKernel]

/-- `δ₁ + x δ₂` is a unit iff `|x| < √2`. -/
theorem isWienerUnit_twoPoint_one_iff (x : ℝ) : IsWienerUnit (twoPoint 1 x) ↔ |x| < Real.sqrt 2 := by
  rw [twoPoint_one_eq, isWienerUnit_localFactor_iff Nat.prime_two, abs_neg, Nat.cast_ofNat]

theorem dirichletConv_smul_left (t : ℝ) (k g : ℕ → ℝ) (n : ℕ) :
    RHTower.dirichletConv (fun m => t * k m) g n = t * RHTower.dirichletConv k g n := by
  unfold RHTower.dirichletConv; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

theorem IsWienerUnit.smul {k : ℕ → ℝ} (hk : IsWienerUnit k) {t : ℝ} (ht : t ≠ 0) :
    IsWienerUnit fun m => t * k m := by
  obtain ⟨hk1, g, hg, hinv⟩ := hk
  refine ⟨(hk1.mul_left |t|).congr fun n => by rw [abs_mul, mul_assoc], fun m => t⁻¹ * g m,
    (hg.mul_left |t⁻¹|).congr fun n => by rw [abs_mul, mul_assoc], fun n hn => ?_⟩
  rw [dirichletConv_smul_left, dirichletConv_comm, dirichletConv_smul_left, dirichletConv_comm,
    hinv n hn, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]

/-- The flip kernel `(1 + x)δ₁ − xδ₂` is a unit when `1 + x ≠ 0` and `|x/(1 + x)| < √2`. -/
theorem isWienerUnit_flipKernel {x : ℝ} (hx : 1 + x ≠ 0) (h : |x / (1 + x)| < Real.sqrt 2) :
    IsWienerUnit (twoPoint (1 + x) (-x)) := by
  have e : twoPoint (1 + x) (-x) = fun m => (1 + x) * localFactorKernel 2 (x / (1 + x)) m := by
    funext n
    simp only [twoPoint, localFactorKernel]
    split_ifs <;> field_simp <;> ring
  rw [e]
  exact ((isWienerUnit_localFactor_iff Nat.prime_two _).2 (by rwa [Nat.cast_ofNat])).smul hx

/-! ### The flip of a weight multiplicative at `2` -/

/-- Supported on the odd integers. -/
def OddSupported (o : ℕ → ℝ) : Prop := ∀ d, d % 2 = 0 → o d = 0

/-- **The flip is a convolution**: `((δ₁ + xδ₂) ⋆ o)♭ = ((1 + x)δ₁ − xδ₂) ⋆ o` for odd `o`. -/
theorem evenFlip_dirichletConv_twoPoint {o : ℕ → ℝ} (ho : OddSupported o) (x : ℝ) :
    evenFlip (RHTower.dirichletConv (twoPoint 1 x) o) =
      RHTower.dirichletConv (twoPoint (1 + x) (-x)) o := by
  funext d
  rw [evenFlip_apply]
  rcases eq_or_ne d 0 with rfl | hd
  · simp [dirichletConv_twoPoint_zero]
  rw [dirichletConv_twoPoint _ _ _ hd]
  by_cases hodd : d % 2 = 1
  · have h2 : ¬ 2 ∣ d := by omega
    have h2d : 2 ∣ 2 * d := dvd_mul_right 2 d
    rw [if_pos hodd, dirichletConv_twoPoint _ _ _ hd, dirichletConv_twoPoint _ _ _ (by omega),
      if_neg h2, if_pos h2d, Nat.mul_div_cancel_left d two_pos, ho (2 * d) (by omega)]
    ring
  · have h2 : 2 ∣ d := by omega
    rw [if_neg hodd, if_pos h2, ho d (by omega)]
    by_cases hhalf : d / 2 % 2 = 1
    · rw [if_pos hhalf, dirichletConv_twoPoint _ _ _ hd, if_pos h2, ho d (by omega)]
      ring
    · rw [if_neg hhalf, dirichletConv_twoPoint _ _ _ hd, if_pos h2, ho d (by omega),
        ho (d / 2) (by omega)]
      ring

theorem obstructionHull_congr {c c' : ℕ → ℝ} (h : c = c') (hc : Summable fun d : ℕ => |c d / d|)
    (hc' : Summable fun d : ℕ => |c' d / d|) : obstructionHull c hc = obstructionHull c' hc' := by
  subst h; rfl

theorem paidIdeal_congr {c c' : ℕ → ℝ} (h : c = c') (hc : Summable fun d : ℕ => |c d / d|)
    (hc' : Summable fun d : ℕ => |c' d / d|) : paidIdeal c hc = paidIdeal c' hc' := by
  subst h; rfl

theorem summable_abs_evenFlip_div {o : ℕ → ℝ} (ho : OddSupported o)
    (hs : Summable fun d : ℕ => |o d / d|) (x : ℝ) :
    Summable fun d : ℕ => |evenFlip (RHTower.dirichletConv (twoPoint 1 x) o) d / d| := by
  rw [evenFlip_dirichletConv_twoPoint ho]
  exact summable_abs_dirichletConv_div (criticalWiener_twoPoint _ _) hs

/-- **The flip only removes obstructions**: `hull(c♭) ⊆ hull(c)` when `|x| < √2`. -/
theorem obstructionHull_evenFlip_subset {o : ℕ → ℝ} (ho : OddSupported o)
    (hs : Summable fun d : ℕ => |o d / d|) {x : ℝ} (hx : |x| < Real.sqrt 2) :
    obstructionHull (evenFlip (RHTower.dirichletConv (twoPoint 1 x) o))
        (summable_abs_evenFlip_div ho hs x) ⊆
      obstructionHull (RHTower.dirichletConv (twoPoint 1 x) o)
        (summable_abs_dirichletConv_div (criticalWiener_twoPoint 1 x) hs) := by
  have hu := (isWienerUnit_twoPoint_one_iff x).2 hx
  rw [obstructionHull_congr (evenFlip_dirichletConv_twoPoint ho x) _
      (summable_abs_dirichletConv_div (criticalWiener_twoPoint _ _) hs), obstructionHull_unit o hs hu]
  exact obstructionHull_conv_subset o hs (criticalWiener_twoPoint _ _)

/-- **… and only where the flip kernel vanishes.** -/
theorem mem_obstructionHull_evenFlip {o : ℕ → ℝ} (ho : OddSupported o)
    (hs : Summable fun d : ℕ => |o d / d|) {x : ℝ} (hx : |x| < Real.sqrt 2) {ω : BohrPoint}
    (hω : ω ∈ obstructionHull (RHTower.dirichletConv (twoPoint 1 x) o)
      (summable_abs_dirichletConv_div (criticalWiener_twoPoint 1 x) hs))
    (hne : bohrEval (1 / 2) (toWiener _ (criticalWiener_twoPoint (1 + x) (-x))).toFn ω ≠ 0) :
    ω ∈ obstructionHull (evenFlip (RHTower.dirichletConv (twoPoint 1 x) o))
      (summable_abs_evenFlip_div ho hs x) := by
  have hu := (isWienerUnit_twoPoint_one_iff x).2 hx
  rw [obstructionHull_unit o hs hu] at hω
  rw [obstructionHull_congr (evenFlip_dirichletConv_twoPoint ho x) _
    (summable_abs_dirichletConv_div (criticalWiener_twoPoint _ _) hs)]
  exact mem_obstructionHull_conv o hs (criticalWiener_twoPoint _ _) hω hne

/-- **The region of invisibility**: if both `δ₁ + xδ₂` and `(1 + x)δ₁ − xδ₂` are units the flip does
not move the repairing ideal. -/
theorem paidIdeal_evenFlip_eq {o : ℕ → ℝ} (ho : OddSupported o)
    (hs : Summable fun d : ℕ => |o d / d|) {x : ℝ} (hx : |x| < Real.sqrt 2) (hx1 : 1 + x ≠ 0)
    (hx2 : |x / (1 + x)| < Real.sqrt 2) :
    paidIdeal (evenFlip (RHTower.dirichletConv (twoPoint 1 x) o)) (summable_abs_evenFlip_div ho hs x) =
      paidIdeal (RHTower.dirichletConv (twoPoint 1 x) o)
        (summable_abs_dirichletConv_div (criticalWiener_twoPoint 1 x) hs) := by
  rw [paidIdeal_congr (evenFlip_dirichletConv_twoPoint ho x) _
      (summable_abs_dirichletConv_div (isWienerUnit_flipKernel hx1 hx2).1 hs),
    paidIdeal_unit o hs (isWienerUnit_flipKernel hx1 hx2),
    paidIdeal_unit o hs ((isWienerUnit_twoPoint_one_iff x).2 hx)]

/-- The Bohr transform of `a δ₁ + b δ₂`. -/
theorem bohrEval_toWiener_twoPoint (a b : ℝ) (ω : BohrPoint) :
    bohrEval (1 / 2) (toWiener _ (criticalWiener_twoPoint a b)).toFn ω =
      a + b * ω.ω 2 / (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
  unfold bohrEval LSeries
  rw [tsum_eq_sum (s := {1, 2}) fun m hm => ?_, sum_pair (by norm_num)]
  · simp [toWiener, toFn_mk, realFn, twoPoint, term_of_ne_zero, ω.map_one]
  · simp only [mem_insert, mem_singleton, not_or] at hm
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    simp [toWiener, toFn_mk, realFn, twoPoint, hm.1, hm.2, hm0]

/-! ### The Möbius receiver -/

/-- The odd part of the damped Möbius weight. -/
def moebiusOddPart (ε : ℝ) (d : ℕ) : ℝ := if d % 2 = 1 then pmPowerDampedRealWeight ε d else 0

theorem oddSupported_moebiusOddPart (ε : ℝ) : OddSupported (moebiusOddPart ε) := fun d hd => by
  simp [moebiusOddPart, hd]

theorem summable_abs_moebiusOddPart_div {ε : ℝ} (hε : 0 < ε) :
    Summable fun d : ℕ => |moebiusOddPart ε d / d| :=
  (summable_abs_moebius_div hε).of_nonneg_of_le (fun _ => abs_nonneg _) fun d => by
    unfold moebiusOddPart; split_ifs <;> simp

/-- `μ(d)d^{−ε} = (δ₁ − 2^{−ε}δ₂) ⋆ (odd part)`. -/
theorem pmPowerDampedRealWeight_eq_dirichletConv (ε : ℝ) :
    pmPowerDampedRealWeight ε =
      RHTower.dirichletConv (twoPoint 1 (-(2 : ℝ) ^ (-ε))) (moebiusOddPart ε) := by
  funext d
  rcases eq_or_ne d 0 with rfl | hd
  · simp [dirichletConv_twoPoint_zero, pmPowerDampedRealWeight, moebiusReal]
  rw [dirichletConv_twoPoint _ _ _ hd]
  by_cases hodd : d % 2 = 1
  · have h2 : ¬ 2 ∣ d := by omega
    simp [moebiusOddPart, hodd, h2]
  · have h2 : 2 ∣ d := by omega
    obtain ⟨m, rfl⟩ := h2
    have hm0 : m ≠ 0 := by rintro rfl; simp at hd
    rw [if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m two_pos]
    simp only [moebiusOddPart, show ¬ (2 * m) % 2 = 1 by omega, if_false, mul_zero,
      zero_add]
    unfold pmPowerDampedRealWeight moebiusReal
    by_cases hm : m % 2 = 1
    · have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.2 (Nat.odd_iff.2 hm)
      rw [if_pos hm, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two, Nat.cast_mul,
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
      push_cast
      ring
    · rw [if_neg hm]
      have h4 : ¬ Squarefree (2 * m) := by
        intro hsq
        obtain ⟨k, rfl⟩ : 2 ∣ m := by omega
        exact absurd (hsq 2 ⟨k, by ring⟩) (by norm_num)
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h4]
      simp

/-- `(μd^{−ε})♭ = ((1 − 2^{−ε})δ₁ + 2^{−ε}δ₂) ⋆ (odd part)`. -/
theorem evenFlip_moebius (ε : ℝ) :
    evenFlip (pmPowerDampedRealWeight ε) =
      RHTower.dirichletConv (twoPoint (1 - (2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ (-ε))) (moebiusOddPart ε) := by
  rw [pmPowerDampedRealWeight_eq_dirichletConv,
    evenFlip_dirichletConv_twoPoint (oddSupported_moebiusOddPart ε), neg_neg, ← sub_eq_add_neg]

theorem abs_two_rpow_neg_lt_sqrt_two {ε : ℝ} (hε : 0 < ε) :
    |-(2 : ℝ) ^ (-ε)| < Real.sqrt 2 := by
  rw [abs_neg, abs_of_pos (Real.rpow_pos_of_pos two_pos _)]
  have h1 : (2 : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one one_lt_two
  linarith

/-- **Payment survives the flip**: if `μ(d)d^{−ε}` is paid, so is its even flip. -/
theorem receiverBounded_evenFlip_moebius {ε : ℝ} (hε : 0 < ε)
    (h : ReceiverBounded (pmPowerDampedRealWeight ε)) :
    ReceiverBounded (evenFlip (pmPowerDampedRealWeight ε)) := by
  have hs := summable_abs_moebiusOddPart_div hε
  have hu := (isWienerUnit_twoPoint_one_iff _).2 (abs_two_rpow_neg_lt_sqrt_two hε)
  rw [pmPowerDampedRealWeight_eq_dirichletConv,
    receiverBounded_dirichletConv_iff_of_isWienerUnit hu hs] at h
  rw [evenFlip_moebius]
  exact receiverBounded_dirichletConv (criticalWiener_twoPoint _ _) hs h

theorem summable_abs_evenFlip_moebius_div {ε : ℝ} (hε : 0 < ε) :
    Summable fun d : ℕ => |evenFlip (pmPowerDampedRealWeight ε) d / d| := by
  rw [evenFlip_moebius]
  exact summable_abs_dirichletConv_div (criticalWiener_twoPoint _ _)
    (summable_abs_moebiusOddPart_div hε)

/-- **The flipped Möbius weight keeps the off-line zeros**: a zero `ρ` with `½ + ε < Re ρ < 1`,
`ζ(ρ − ε) ≠ 0` and `1 − 2^{−ε} + 2^{−ρ} ≠ 0` obstructs `(μd^{−ε})♭` at `ρ − ε`. -/
theorem mem_obstructionHull_evenFlip_moebius_of_zero {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0)
    (hz' : riemannZeta (ρ - ε) ≠ 0)
    (h2 : (((1 - (2 : ℝ) ^ (-ε) : ℝ)) : ℂ) + (2 : ℂ) ^ (-ρ) ≠ 0) :
    halfPlanePoint (1 / 2) (ρ - ε) (by simp; linarith) ∈
      obstructionHull (evenFlip (pmPowerDampedRealWeight ε)) (summable_abs_evenFlip_moebius_div hε) := by
  have hs := summable_abs_moebiusOddPart_div hε
  have hx := abs_two_rpow_neg_lt_sqrt_two hε
  have hmem := mem_obstructionHull_moebius_of_zero hε hε2 hρ hρ1 hz hz'
  rw [obstructionHull_congr (pmPowerDampedRealWeight_eq_dirichletConv ε) _
    (summable_abs_dirichletConv_div (criticalWiener_twoPoint 1 _) hs)] at hmem
  rw [obstructionHull_congr (congrArg evenFlip (pmPowerDampedRealWeight_eq_dirichletConv ε)) _
    (summable_abs_evenFlip_div (oddSupported_moebiusOddPart ε) hs _)]
  refine mem_obstructionHull_evenFlip (oddSupported_moebiusOddPart ε) hs hx hmem ?_
  rw [bohrEval_toWiener_twoPoint]
  -- `1 + x − x ω(2)/√2` with `x = −2^{−ε}` and `ω(2) = 2^{½ − ρ + ε}` is `1 − 2^{−ε} + 2^{−ρ}`.
  have hω2 : (halfPlanePoint (1 / 2) (ρ - ε) (by simp; linarith)).ω 2 =
      (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) * ((2 : ℂ) ^ (ε : ℂ) * (2 : ℂ) ^ (-ρ)) := by
    simp only [halfPlanePoint, two_ne_zero, if_false, Nat.cast_ofNat]
    rw [← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero]
    congr 1; push_cast; ring
  have hc : (((2 : ℝ) ^ (-ε) : ℝ) : ℂ) * (2 : ℂ) ^ (ε : ℂ) = 1 := by
    rw [ofReal_cpow two_pos.le, ofReal_ofNat, ← cpow_add _ _ two_ne_zero]
    push_cast; simp
  have hsq : (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) ≠ 0 := by rw [Ne, cpow_eq_zero_iff]; norm_num
  rw [hω2]
  convert h2 using 1
  field_simp
  push_cast
  linear_combination (2 : ℂ) ^ (-ρ) * hc

/-- **Unpaid after the flip**: such a zero leaves the flipped Möbius weight unpaid. -/
theorem not_receiverBounded_evenFlip_moebius_of_zero {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0)
    (hz' : riemannZeta (ρ - ε) ≠ 0)
    (h2 : (((1 - (2 : ℝ) ^ (-ε) : ℝ)) : ℂ) + (2 : ℂ) ^ (-ρ) ≠ 0) :
    ¬ ReceiverBounded (evenFlip (pmPowerDampedRealWeight ε)) :=
  (obstructionHull_nonempty_iff _ _).1
    ⟨_, mem_obstructionHull_evenFlip_moebius_of_zero hε hε2 hρ hρ1 hz hz' h2⟩

/-- **The flip is not invertible on the Möbius receiver** for `0 < ε ≤ ½`: its kernel
`(1 − 2^{−ε})δ₁ + 2^{−ε}δ₂` vanishes at `ω(2) = −√2(2^ε − 1)`. -/
theorem not_isWienerUnit_flipKernel_moebius {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ¬ IsWienerUnit (twoPoint (1 - (2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ (-ε))) := by
  intro hu
  rw [isWienerUnit_iff_forall_bohrEval_ne_zero _ (criticalWiener_twoPoint _ _)] at hu
  set z : ℂ := -((Real.sqrt 2 * ((2 : ℝ) ^ ε - 1) : ℝ) : ℂ)
  have h2e : (2 : ℝ) ^ ε ≤ Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le one_le_two hε2
  have h1e : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow one_lt_two hε
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hz : ‖z‖ ≤ 1 := by
    rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs0 (by linarith))]
    nlinarith
  have hz1 : ∀ p, p.Prime → ‖(fun q => if q = 2 then z else 1) p‖ ≤ 1 := fun p _ => by
    dsimp only
    split_ifs
    · exact hz
    · simp
  have h := hu (BohrPoint.ofPrimes _ hz1)
  rw [show realFn (twoPoint (1 - (2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ (-ε))) =
      (toWiener _ (criticalWiener_twoPoint (1 - (2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ (-ε)))).toFn from rfl,
    bohrEval_toWiener_twoPoint, BohrPoint.ofPrimes_apply_prime _ Nat.prime_two, if_pos rfl] at h
  apply h
  have hsq : (2 : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow zero_le_two]; norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ε := Real.rpow_pos_of_pos two_pos _
  have hinv : (2 : ℝ) ^ (-ε) * (2 : ℝ) ^ ε = 1 := by
    rw [← Real.rpow_add two_pos]; simp
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hr : (1 - (2 : ℝ) ^ (-ε)) + (2 : ℝ) ^ (-ε) * (-(Real.sqrt 2 * ((2 : ℝ) ^ ε - 1))) /
      Real.sqrt 2 = 0 := by
    have e : (2 : ℝ) ^ (-ε) * (-(Real.sqrt 2 * ((2 : ℝ) ^ ε - 1))) / Real.sqrt 2 =
        -((2 : ℝ) ^ (-ε) * (2 : ℝ) ^ ε) + (2 : ℝ) ^ (-ε) := by
      field_simp; ring
    rw [e, hinv]; ring
  rw [hsq, show z = ((-(Real.sqrt 2 * ((2 : ℝ) ^ ε - 1)) : ℝ) : ℂ) by simp [z]]
  exact_mod_cast hr

end

end GaloisForLFunctions.ArithmeticOrientationTheory
