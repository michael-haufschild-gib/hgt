import GaloisForLFunctions.ArithmeticOrientationTheory.TheOffLineZerosObstructTheMoebiusReceiver
import GaloisForLFunctions.ArithmeticOrientationTheory.AnOrientationFaithfulNormOverTheOddSquarefreeWeight
import GaloisForLFunctions.ArithmeticOrientationTheory.LocalFactorsAreTheUnitsOfTheWienerMonoid

/-!
# The even flip creates an obstruction at the pole

Let `0 < ε < ½`, `u(d) = d^{−ε}` and `o(d) = 1_{d odd squarefree} d^{−ε}`.  Since
`1_{odd} d^{−ε} = (δ₁ − 2^{−ε} δ₂) ⋆ u` (`oddDamped_eq_localFactor_conv`) and `o` is a critical
Wiener multiple of it, every weight `k ⋆ o` is a critical Wiener multiple of the smooth power, and
the pole values multiply (`poleSum_dirichletConv`).  Hence:

* **The pole law over `o` for critical Wiener kernels** (`receiverBounded_dirichletConv_oddSqf_iff_critical`):
  `k ⋆ o` is paid iff `Σ k(j) j^{−(1−ε)} = 0`.
* **The hull of a weight over `o`** (`paidIdeal_oddSqf_eq`, `mem_obstructionHull_oddSqf_iff`): if
  `K₀(1 − ε) ≠ 0` the repairing ideal of `k₀ ⋆ o` is that of the smooth power, so its obstruction
  hull is the pole point `s = 1 − ε`; otherwise the weight is paid and the hull is empty.
* **The even flip moves the index** (`obstructionHull_evenFlip_nonempty_iff`,
  `mem_obstructionHull_evenFlip_iff`): for a four-free critical Wiener kernel with `k₀ ⋆ o` paid,
  the companion `(k₀ ⋆ o)^♭` is obstructed exactly when the even-part pole value
  `K₀,ₑ(1 − ε)` is nonzero, and then its obstruction is the pole point.  The pole value of the
  flipped kernel is `K₀(1 − ε) + (1 − 2^ε) K₀,ₑ(1 − ε)` (`poleSum_flipKernelOf`).

So orientation acts on the index: the flip of a paid weight acquires an obstruction, always at
the same point of the spectrum, and the amount of orientation is the even-part pole value.
-/

open Finset ArithmeticFunction LSeries Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics WienerAlgebraAt

noncomputable section
set_option autoImplicit false

/-! ### Pole sums -/

/-- The pole sum `Σ_j k(j) j^{−t}`. -/
def poleSum (t : ℝ) (k : ℕ → ℝ) : ℝ := ∑' j : ℕ, k j * (j : ℝ) ^ (-t)

/-- Pole sums multiply under convolution. -/
theorem poleSum_dirichletConv {t : ℝ} (ht : 0 < t) {a b : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a n| * (n : ℝ) ^ (-t))
    (hb : Summable fun n : ℕ => |b n| * (n : ℝ) ^ (-t)) :
    poleSum t (RHTower.dirichletConv a b) = poleSum t a * poleSum t b := by
  apply Complex.ofReal_injective
  unfold poleSum
  rw [Complex.ofReal_mul, ofReal_tsum_rpow _ ht, ofReal_tsum_rpow _ ht, ofReal_tsum_rpow _ ht,
    cplx_dirichletConv]
  exact LSeries_convolution' ((lSeriesSummable_cplx_iff ht).2 ha) ((lSeriesSummable_cplx_iff ht).2 hb)

theorem summable_rpow_of_criticalWiener {k : ℕ → ℝ} (hk : CriticalWiener k) {t : ℝ}
    (ht : 1 / 2 ≤ t) : Summable fun n : ℕ => |k n| * (n : ℝ) ^ (-t) :=
  hk.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [Real.zero_rpow (by linarith : -t ≠ 0)]
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hn) (by linarith)) (abs_nonneg _)

/-! ### `o` is a critical Wiener multiple of the smooth power -/

/-- `1_{odd}(d) d^{−ε} = ((δ₁ − 2^{−ε} δ₂) ⋆ d^{−ε})(d)`. -/
theorem oddDamped_eq_localFactor_conv (ε : ℝ) :
    dampedSignWeight ⇑oddAF ε =
      RHTower.dirichletConv (localFactorKernel 2 ((2 : ℝ) ^ (-ε))) (dampedSignWeight unitSign ε) := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dampedSignWeight, oddAF_apply, RHTower.dirichletConv]
  rw [dirichletConv_localFactorKernel Nat.prime_two _ _ hn]
  unfold dampedSignWeight unitSign
  rw [oddAF_apply]
  by_cases h2 : 2 ∣ n
  · obtain ⟨m, rfl⟩ := h2
    rw [if_neg (by simp), if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m two_pos, Nat.cast_mul,
      Nat.cast_two, Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]
    ring
  · rw [if_pos h2, if_neg h2]; ring

theorem criticalWiener_twoFactor (ε : ℝ) : CriticalWiener (localFactorKernel 2 ((2 : ℝ) ^ (-ε))) :=
  criticalWiener_localFactorKernel 2 _

/-- The kernel turning the smooth power into `o`. -/
def oddSqfKernel (ε : ℝ) : ℕ → ℝ :=
  RHTower.dirichletConv (dampedSignWeight ⇑oddSqrtMoebius ε) (localFactorKernel 2 ((2 : ℝ) ^ (-ε)))

theorem criticalWiener_oddSqfKernel {ε : ℝ} (hε : 0 < ε) : CriticalWiener (oddSqfKernel ε) :=
  criticalWiener_dirichletConv (criticalWiener_dampedOddSqrtMoebius hε) (criticalWiener_twoFactor ε)

/-- `k ⋆ o = (k ⋆ g) ⋆ d^{−ε}` with `g` critical Wiener. -/
theorem dirichletConv_oddSqf_eq_unit (k : ℕ → ℝ) (ε : ℝ) :
    RHTower.dirichletConv k (oddSqfWeight ε) =
      RHTower.dirichletConv (RHTower.dirichletConv k (oddSqfKernel ε)) (dampedSignWeight unitSign ε) := by
  have ho : oddSqfWeight ε = RHTower.dirichletConv (oddSqfKernel ε) (dampedSignWeight unitSign ε) := by
    rw [oddSqfKernel, dirichletConv_assoc, ← oddDamped_eq_localFactor_conv]
    exact funext (oddSqfWeight_eq ε)
  rw [ho, dirichletConv_assoc]

/-! ### The pole law over `o` for critical Wiener kernels -/

/-- **The pole law over `o`**: for `0 < ε < ½` and a critical Wiener kernel, `k ⋆ o` is paid iff
`Σ k(j) j^{−(1−ε)} = 0`. -/
theorem receiverBounded_dirichletConv_oddSqf_iff_critical {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {k : ℕ → ℝ} (hk : CriticalWiener k) :
    ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ↔ poleSum (1 - ε) k = 0 := by
  constructor
  · intro hB
    by_contra hK
    have hD : 0 < RHTower.Sieve.squarefreeDensity := by
      rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
    exact not_receiverBounded_dirichletConv_of_drift_critical hε hε2.le (oddSqfWeight_nonneg ε)
      (oddSqfWeight_mem_dampedClass ε) (by positivity) (eventually_oddSqfWeight_drift hε) hk hK hB
  · intro hP
    rw [dirichletConv_oddSqf_eq_unit, receiverBounded_dirichletConv_unit_iff_critical hε hε2
      (criticalWiener_dirichletConv hk (criticalWiener_oddSqfKernel hε))]
    change poleSum (1 - ε) (RHTower.dirichletConv k (oddSqfKernel ε)) = 0
    rw [poleSum_dirichletConv (by linarith) (summable_rpow_of_criticalWiener hk (by linarith))
      (summable_rpow_of_criticalWiener (criticalWiener_oddSqfKernel hε) (by linarith)), hP, zero_mul]

/-! ### The hull of a weight over `o` -/

theorem summable_abs_dirichletConv_oddSqf_div {ε : ℝ} (hε : 0 < ε) {k₀ : ℕ → ℝ}
    (hk₀ : CriticalWiener k₀) :
    Summable fun d : ℕ => |RHTower.dirichletConv k₀ (oddSqfWeight ε) d / d| :=
  summable_abs_dirichletConv_div hk₀ (summable_abs_oddSqfWeight_div hε)

/-- **If `K₀(1 − ε) ≠ 0`, `k₀ ⋆ o` has the repairing ideal of the smooth power.** -/
theorem paidIdeal_oddSqf_eq {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k₀ : ℕ → ℝ}
    (hk₀ : CriticalWiener k₀) (hP : poleSum (1 - ε) k₀ ≠ 0) :
    paidIdeal (RHTower.dirichletConv k₀ (oddSqfWeight ε)) (summable_abs_dirichletConv_oddSqf_div hε hk₀) =
      paidIdeal (dampedSignWeight unitSign ε) (summable_abs_smoothPower_div hε) := by
  ext k
  rw [mem_paidIdeal _ _, mem_paidIdeal _ _]
  have key : ∀ f : ℕ → ℝ, CriticalWiener f →
      (ReceiverBounded (RHTower.dirichletConv f (RHTower.dirichletConv k₀ (oddSqfWeight ε))) ↔
        ReceiverBounded (RHTower.dirichletConv f (dampedSignWeight unitSign ε))) := fun f hf => by
    rw [← dirichletConv_assoc, receiverBounded_dirichletConv_oddSqf_iff_critical hε hε2
      (criticalWiener_dirichletConv hf hk₀), receiverBounded_dirichletConv_unit_iff_critical hε hε2 hf,
      poleSum_dirichletConv (by linarith) (summable_rpow_of_criticalWiener hf (by linarith))
        (summable_rpow_of_criticalWiener hk₀ (by linarith))]
    exact ⟨fun h => (mul_eq_zero.1 h).resolve_right hP, fun h => by
      change poleSum (1 - ε) f = 0 at h; rw [h, zero_mul]⟩
  rw [key _ (criticalWiener_rePart k), key _ (criticalWiener_imPart k)]

/-- **The obstruction of a weight over `o` is the pole point** when its kernel does not vanish
there. -/
theorem mem_obstructionHull_oddSqf_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k₀ : ℕ → ℝ}
    (hk₀ : CriticalWiener k₀) (hP : poleSum (1 - ε) k₀ ≠ 0) (ω : BohrPoint) :
    ω ∈ obstructionHull (RHTower.dirichletConv k₀ (oddSqfWeight ε))
        (summable_abs_dirichletConv_oddSqf_div hε hk₀) ↔
      ∀ p : ℕ, p.Prime → ω.ω p = (polePoint ε hε2.le).ω p := by
  unfold obstructionHull
  rw [paidIdeal_oddSqf_eq hε hε2 hk₀ hP]
  exact mem_obstructionHull_smoothPower_iff hε hε2 ω

/-! ### The flip and the even-part pole value -/

/-- The pole sum of the flipped kernel: `K^♭ = K + (1 − 2^t)·K_e` at exponent `t`. -/
theorem poleSum_flipKernelOf {t : ℝ} (ht : 0 < t) {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0)
    (hk : Summable fun n : ℕ => |k n| * (n : ℝ) ^ (-t)) :
    poleSum t (flipKernelOf k) = poleSum t k + (1 - (2 : ℝ) ^ (1 - t)) * poleSum t (evenPartWeight k) := by
  set e := evenPartWeight k
  have h2t : ∀ m : ℕ, ((2 * m : ℕ) : ℝ) ^ (-t) = (2 : ℝ) ^ (-t) * (m : ℝ) ^ (-t) := fun m => by
    rw [Nat.cast_mul, Nat.cast_two, Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]
  have hk2 : Summable fun m : ℕ => |k (2 * m)| * ((2 * m : ℕ) : ℝ) ^ (-t) :=
    hk.comp_injective injective_two_mul
  have sk : Summable fun j : ℕ => k j * (j : ℝ) ^ (-t) := Summable.of_abs (hk.congr fun j => by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)])
  have so : Summable fun j : ℕ => oddPartKernel k j * (j : ℝ) ^ (-t) :=
    Summable.of_norm (hk.of_nonneg_of_le (fun _ => norm_nonneg _) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _)]
      exact mul_le_mul_of_nonneg_right (abs_oddPartKernel_le k j) (Real.rpow_nonneg (Nat.cast_nonneg j) _))
  have se : Summable fun j : ℕ => e j * (j : ℝ) ^ (-t) := by
    refine Summable.of_norm ((hk2.mul_left ((2 : ℝ) ^ t)).of_nonneg_of_le (fun _ => norm_nonneg _)
      fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j) _), h2t,
      show (2 : ℝ) ^ t * (|k (2 * j)| * ((2 : ℝ) ^ (-t) * (j : ℝ) ^ (-t))) =
        ((2 : ℝ) ^ t * (2 : ℝ) ^ (-t)) * (|k (2 * j)| * (j : ℝ) ^ (-t)) by ring,
      ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero, one_mul]
    exact mul_le_mul_of_nonneg_right (abs_evenPartWeight_le k j) (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  have ss : Summable fun j : ℕ => shiftTwo e j * (j : ℝ) ^ (-t) := by
    rw [summable_iff_two_mul fun j hj => by rw [shiftTwo_of_not_dvd _ hj, zero_mul]]
    refine Summable.of_norm (hk2.of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_)
    rw [shiftTwo_two_mul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right (abs_evenPartWeight_le k m) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hshift : poleSum t (shiftTwo e) = (2 : ℝ) ^ (-t) * poleSum t e := by
    unfold poleSum
    rw [tsum_eq_tsum_two_mul fun j hj => by rw [shiftTwo_of_not_dvd _ hj, zero_mul], ← tsum_mul_left]
    exact tsum_congr fun m => by rw [shiftTwo_two_mul, h2t]; ring
  have hk' : poleSum t k = poleSum t (oddPartKernel k) + poleSum t (shiftTwo e) := by
    unfold poleSum
    rw [← so.tsum_add ss]
    exact tsum_congr fun j => by rw [kernel_eq_odd_add_shift hk4 j]; ring
  have hflip : poleSum t (flipKernelOf k) =
      poleSum t (oddPartKernel k) + poleSum t e - poleSum t (shiftTwo e) := by
    unfold poleSum
    rw [← so.tsum_add se, ← (so.add se).tsum_sub ss]
    exact tsum_congr fun j => by unfold flipKernelOf; ring
  have h2 : (2 : ℝ) * (2 : ℝ) ^ (-t) = (2 : ℝ) ^ (1 - t) := by
    rw [show 1 - t = 1 + -t by ring, Real.rpow_add two_pos, Real.rpow_one]
  rw [hflip, hk', hshift]
  linear_combination (-(poleSum t e)) * h2

theorem criticalWiener_flipKernelOf {k : ℕ → ℝ} (hk : CriticalWiener k) :
    CriticalWiener (flipKernelOf k) := by
  have hk2 : Summable fun m : ℕ => |k (2 * m)| * ((2 * m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
    hk.comp_injective injective_two_mul
  have he : CriticalWiener (evenPartWeight k) := by
    refine (hk2.mul_left (Real.sqrt 2)).of_nonneg_of_le
      (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _)) fun j => ?_
    have h2t : ((2 * j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = (2 : ℝ) ^ (-(1 / 2 : ℝ)) * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_two, Real.mul_rpow (by norm_num) (Nat.cast_nonneg j)]
    have hs : Real.sqrt 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num)]; norm_num
    rw [h2t, show Real.sqrt 2 * (|k (2 * j)| * ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * (j : ℝ) ^ (-(1 / 2 : ℝ)))) =
      (Real.sqrt 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ))) * (|k (2 * j)| * (j : ℝ) ^ (-(1 / 2 : ℝ))) by ring,
      hs, one_mul]
    exact mul_le_mul_of_nonneg_right (abs_evenPartWeight_le k j) (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  have hs : CriticalWiener (shiftTwo (evenPartWeight k)) := by
    unfold CriticalWiener
    rw [summable_iff_two_mul fun j hj => by rw [shiftTwo_of_not_dvd _ hj, abs_zero, zero_mul]]
    refine hk2.of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      fun m => ?_
    rw [shiftTwo_two_mul]
    exact mul_le_mul_of_nonneg_right (abs_evenPartWeight_le k m) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have ho : CriticalWiener (oddPartKernel k) :=
    hk.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _))
      fun j => mul_le_mul_of_nonneg_right (abs_oddPartKernel_le k j) (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  exact ((ho.add he).add hs).of_nonneg_of_le
    (fun j => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg j) _))
    fun j => abs_flipKernelOf_le k j _ (Real.rpow_nonneg (Nat.cast_nonneg j) _)

/-- **The even flip moves the index**: for a four-free critical Wiener kernel with `k₀ ⋆ o` paid,
the companion is obstructed iff the even-part pole value is nonzero. -/
theorem obstructionHull_evenFlip_nonempty_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k₀ : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k₀ m = 0) (hk₀ : CriticalWiener k₀) (hpaid : poleSum (1 - ε) k₀ = 0) :
    (obstructionHull (RHTower.dirichletConv (flipKernelOf k₀) (oddSqfWeight ε))
        (summable_abs_dirichletConv_oddSqf_div hε (criticalWiener_flipKernelOf hk₀))).Nonempty ↔
      poleSum (1 - ε) (evenPartWeight k₀) ≠ 0 := by
  rw [obstructionHull_nonempty_iff, receiverBounded_dirichletConv_oddSqf_iff_critical hε hε2
    (criticalWiener_flipKernelOf hk₀), poleSum_flipKernelOf (by linarith) hk4
      (summable_rpow_of_criticalWiener hk₀ (by linarith)), hpaid, zero_add, sub_sub_cancel]
  have h2 : (1 : ℝ) - (2 : ℝ) ^ ε ≠ 0 := by
    have : (1 : ℝ) < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
    linarith
  exact ⟨fun h he => h (by rw [he, mul_zero]), fun h he => h ((mul_eq_zero.1 he).resolve_left h2)⟩

/-- **The obstruction of the companion is the pole point.** -/
theorem mem_obstructionHull_evenFlip_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {k₀ : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k₀ m = 0) (hk₀ : CriticalWiener k₀) (hpaid : poleSum (1 - ε) k₀ = 0)
    (he : poleSum (1 - ε) (evenPartWeight k₀) ≠ 0) (ω : BohrPoint) :
    ω ∈ obstructionHull (RHTower.dirichletConv (flipKernelOf k₀) (oddSqfWeight ε))
        (summable_abs_dirichletConv_oddSqf_div hε (criticalWiener_flipKernelOf hk₀)) ↔
      ∀ p : ℕ, p.Prime → ω.ω p = (polePoint ε hε2.le).ω p := by
  refine mem_obstructionHull_oddSqf_iff hε hε2 (criticalWiener_flipKernelOf hk₀) ?_ ω
  rw [poleSum_flipKernelOf (by linarith) hk4 (summable_rpow_of_criticalWiener hk₀ (by linarith)),
    hpaid, zero_add, sub_sub_cancel]
  have h2 : (1 : ℝ) - (2 : ℝ) ^ ε ≠ 0 := by
    have : (1 : ℝ) < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
    linarith
  exact mul_ne_zero h2 he

end

end GaloisForLFunctions.ArithmeticOrientationTheory
