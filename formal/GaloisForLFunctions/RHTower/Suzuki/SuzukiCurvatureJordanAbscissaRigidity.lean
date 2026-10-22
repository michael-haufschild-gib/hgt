import GaloisForLFunctions.RHTower.Suzuki.SuzukiCurvatureJordanGaugeEscape
import GaloisForLFunctions.HTGeometry.RealDirichletSeries

/-!
# Sharp polynomial-gauge abscissa of Suzuki curvature Jordan sectors

Both Jordan sectors of exact Suzuki checkpoint curvature have summability abscissa `1 / 2`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter
open GaloisForLFunctions.RHTower
open scoped Interval

/-- Polynomial damping on checkpoint cell `N`, normalized at endpoint `N + 1`. -/
def suzukiCheckpointCurvaturePowerDamping (α : ℝ) (N : ℕ) : ℝ :=
  (((N + 1 : ℕ) : ℝ) ^ (-α))

private theorem abscissa_sqrt_endpoint_data {k : ℕ} (hk : 4 ≤ k) :
    let a := Real.sqrt ((k - 1 : ℕ) : ℝ)
    let b := Real.sqrt (k : ℝ)
    0 < a ∧ 0 < b ∧ a ≤ b ∧
      (b - a) * (b + a) = 1 ∧ 23 * b ≤ 27 * a :=
  jordanEscape_sqrt_endpoint_data hk

private theorem abscissa_integral_checkpoint_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < ∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
      screwRegularKernel t :=
  integral_screwRegularKernel_checkpoint_pos hk

private theorem abscissa_integral_checkpoint_upper {k : ℕ} (hk : 3 ≤ k) :
    (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t) ≤
      2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) :=
  jordanEscape_integral_checkpoint_upper hk

private theorem abscissa_integral_checkpoint_lower {k : ℕ} (hk : 4 ≤ k) :
    (4 / 5 : ℝ) / Real.sqrt k ≤
      ∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t :=
  jordanEscape_integral_checkpoint_lower hk

private theorem abscissa_expHalf_checkpoint_scaled_le {k : ℕ} (hk : 4 ≤ k) :
    2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) * Real.sqrt k ≤ 27 / 25 :=
  jordanEscape_expHalf_checkpoint_scaled_le hk

private theorem abscissa_not_isPrimePow_six_mul_succ (m : ℕ) :
    ¬ IsPrimePow (6 * (m + 1)) := by
  have hn2 : 2 ≤ 6 * (m + 1) := by omega
  rw [Nat.not_isPrimePow_iff_nontrivial_of_two_le hn2]
  refine ⟨2, Nat.mem_primeFactors.mpr ⟨Nat.prime_two, ?_, by omega⟩,
    3, Nat.mem_primeFactors.mpr ⟨Nat.prime_three, ?_, by omega⟩, by norm_num⟩
  · exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 6) _
  · exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 6) _

private theorem abscissa_rpow_product (α : ℝ) {x : ℝ} (hx : 0 < x) :
    x ^ (-α) * x ^ (-(1 / 2 : ℝ)) = x ^ (-(α + 1 / 2)) := by
  rw [← Real.rpow_add hx]
  congr 1
  ring

/-- Smooth-cell positivity and the square-root mesh give the sharp positive-sector upper order. -/
theorem suzukiCheckpointSignedCurvaturePositiveMass_le_halfOrder
    {N : ℕ} (hN : 3 ≤ N) :
    suzukiCheckpointSignedCurvaturePositiveMass N ≤
      2 * (((N + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let k := N + 1
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hindex : N = k - 1 := by omega
  have hIpos := abscissa_integral_checkpoint_pos (k := k) (by omega : 3 ≤ k)
  have hIupper := abscissa_integral_checkpoint_upper (k := k) (by omega : 3 ≤ k)
  have hAtom0 : 0 ≤ criticalMellinAtomWeight k := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer k
  let a := Real.sqrt ((k - 1 : ℕ) : ℝ)
  let b := Real.sqrt (k : ℝ)
  obtain ⟨ha, hb, hab, hgap, _⟩ := abscissa_sqrt_endpoint_data hk
  have hgap0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hmesh : b - a ≤ 1 / b := by
    rw [le_div_iff₀ hb]
    have hm : (b - a) * b ≤ (b - a) * (b + a) :=
      mul_le_mul_of_nonneg_left (by linarith : b ≤ b + a) hgap0
    linarith
  have hmax : suzukiCheckpointSignedCurvaturePositiveMass (k - 1) ≤
      ∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t := by
    unfold suzukiCheckpointSignedCurvaturePositiveMass
    unfold suzukiCheckpointSignedCurvatureCell
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    exact max_le (by linarith) hIpos.le
  have hfinal : suzukiCheckpointSignedCurvaturePositiveMass (k - 1) ≤ 2 / b := by
    calc
      _ ≤ ∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
          screwRegularKernel t := hmax
      _ ≤ 2 * (b - a) := hIupper
      _ ≤ 2 * (1 / b) := mul_le_mul_of_nonneg_left hmesh (by norm_num)
      _ = 2 / b := by ring
  rw [hindex]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  change suzukiCheckpointSignedCurvaturePositiveMass (k - 1) ≤ _
  rw [Real.rpow_neg (Nat.cast_nonneg k), ← Real.sqrt_eq_rpow]
  simpa [b, one_div, div_eq_mul_inv] using hfinal

/-- The negative Jordan mass is bounded by the exact von-Mangoldt half-density atom. -/
theorem suzukiCheckpointSignedCurvatureNegativeMass_le_atom
    {N : ℕ} (hN : 2 ≤ N) :
    suzukiCheckpointSignedCurvatureNegativeMass N ≤
      criticalMellinAtomWeight (N + 1) := by
  let k := N + 1
  have hk : 3 ≤ k := by dsimp [k]; omega
  have hindex : N = k - 1 := by omega
  have hIpos := abscissa_integral_checkpoint_pos (k := k) hk
  have hAtom0 : 0 ≤ criticalMellinAtomWeight k := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer k
  rw [hindex]
  unfold suzukiCheckpointSignedCurvatureNegativeMass
  unfold suzukiCheckpointSignedCurvatureCell
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  exact max_le (by linarith) hAtom0

/-- On the multiple-of-six lattice, positive Jordan mass has exact half-order lower size. -/
theorem suzukiCheckpointSignedCurvaturePositiveMass_ge_latticeHalfOrder (m : ℕ) :
    (4 / 5 : ℝ) * (((6 * (m + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      suzukiCheckpointSignedCurvaturePositiveMass (6 * m + 5) := by
  let k := 6 * (m + 1)
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hnot := abscissa_not_isPrimePow_six_mul_succ m
  have hvm : ArithmeticFunction.vonMangoldt k = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot
  have hlower := abscissa_integral_checkpoint_lower hk
  have hindex : 6 * m + 5 = k - 1 := by dsimp [k]; omega
  rw [hindex, suzukiCheckpointSignedCurvaturePositiveMass]
  have hpos := suzukiCheckpointSignedCurvatureCell_pos_of_not_primePower
    (k := k) (by omega : 3 ≤ k) hnot
  rw [max_eq_left hpos.le]
  unfold suzukiCheckpointSignedCurvatureCell
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k), criticalMellinAtomWeight_eq_div_sqrt, hvm]
  simp only [zero_div, sub_zero]
  rw [Real.rpow_neg hkpos.le, ← Real.sqrt_eq_rpow]
  simpa [k, div_eq_mul_inv] using hlower

/-- On every prime endpoint at least `11`, negative Jordan mass has exact half-order lower size. -/
theorem suzukiCheckpointSignedCurvatureNegativeMass_ge_primeHalfOrder
    (p : Nat.Primes) (hp11 : 11 ≤ (p : ℕ)) :
    (18 / 25 : ℝ) * (((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      suzukiCheckpointSignedCurvatureNegativeMass ((p : ℕ) - 1) := by
  let k : ℕ := p
  have hk : 4 ≤ k := by dsimp [k]; omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
  have hupper := abscissa_integral_checkpoint_upper (k := k) (by omega : 3 ≤ k)
  have hscale := abscissa_expHalf_checkpoint_scaled_le hk
  have hintScaled :
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
          screwRegularKernel t) * Real.sqrt k ≤ 27 / 25 := by
    exact (mul_le_mul_of_nonneg_right hupper hsqrt.le).trans hscale
  have hlogNine : (9 / 5 : ℝ) < Real.log 9 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_three_gt_d9]
  have hlogMono : Real.log 9 ≤ Real.log (k : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact hkpos
    · exact_mod_cast (by omega : 9 ≤ k)
  have hlogLower : (9 / 5 : ℝ) < Real.log (k : ℝ) := hlogNine.trans_le hlogMono
  have hvm : ArithmeticFunction.vonMangoldt k = Real.log (k : ℝ) := by
    exact ArithmeticFunction.vonMangoldt_apply_prime p.property
  have hcell : suzukiCheckpointSignedCurvatureCell (k - 1) =
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t) - Real.log (k : ℝ) / Real.sqrt (k : ℝ) := by
    unfold suzukiCheckpointSignedCurvatureCell
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k), criticalMellinAtomWeight_eq_div_sqrt, hvm]
  have hnegLower : (18 / 25 : ℝ) / Real.sqrt (k : ℝ) ≤
      -suzukiCheckpointSignedCurvatureCell (k - 1) := by
    rw [hcell, div_le_iff₀ hsqrt]
    have hcancel : Real.log (k : ℝ) / Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) =
        Real.log (k : ℝ) := by field_simp
    nlinarith
  rw [suzukiCheckpointSignedCurvatureNegativeMass]
  have hnegNonneg : 0 ≤ -suzukiCheckpointSignedCurvatureCell (k - 1) := by
    have hconstPos : 0 < (18 / 25 : ℝ) / Real.sqrt (k : ℝ) := by positivity
    linarith
  rw [max_eq_left hnegNonneg]
  rw [Real.rpow_neg hkpos.le, ← Real.sqrt_eq_rpow]
  simpa [k, div_eq_mul_inv] using hnegLower

private theorem abscissa_not_summable_six_succ_rpow
    {r : ℝ} (hr : -1 ≤ r) :
    ¬ Summable (fun m : ℕ => (((6 * (m + 1) : ℕ) : ℝ) ^ r)) := by
  intro hsix
  have hscaled : Summable (fun m : ℕ =>
      (6 : ℝ) ^ r * (((m + 1 : ℕ) : ℝ) ^ r)) := by
    apply hsix.congr
    intro m
    rw [show (((6 * (m + 1) : ℕ) : ℝ)) =
      (6 : ℝ) * ((m + 1 : ℕ) : ℝ) by norm_num, Real.mul_rpow]
    · positivity
    · positivity
  have hshifted : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ r)) :=
    (summable_mul_left_iff (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) r).ne').mp hscaled
  have hfull : Summable (fun m : ℕ => ((m : ℝ) ^ r)) :=
    (summable_nat_add_iff 1).mp hshifted
  have hlt : r < -1 := Real.summable_nat_rpow.mp hfull
  exact (not_lt_of_ge hr) hlt

private theorem abscissa_not_summable_prime_rpow
    {r : ℝ} (hr : -1 ≤ r) :
    ¬ Summable (fun p : Nat.Primes => ((p : ℝ) ^ r)) := by
  rw [Nat.Primes.summable_rpow]
  exact not_lt_of_ge hr

private theorem abscissa_finite_primes_lt (B : ℕ) :
    {p : Nat.Primes | (p : ℕ) < B}.Finite := by
  have h := (Set.finite_lt_nat B).preimage
    (f := fun p : Nat.Primes => (p : ℕ)) (by
      intro p hp q hq hpq
      exact Subtype.ext hpq)
  simpa using h

/-- Above the half-order wall, positive Suzuki curvature Jordan mass is summable. -/
theorem summable_suzukiCheckpointSignedCurvaturePositiveMass_powerDamping_of_half_lt
    {α : ℝ} (hα : 1 / 2 < α) :
    Summable (fun N : ℕ => suzukiCheckpointCurvaturePowerDamping α N *
      suzukiCheckpointSignedCurvaturePositiveMass N) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (-(α + 1 / 2)))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hinj : Function.Injective (fun n : ℕ => n + 3 + 1) := by
    intro m n h
    dsimp at h
    omega
  have hmajorBase : Summable (fun n : ℕ =>
      (((n + 3 + 1 : ℕ) : ℝ) ^ (-(α + 1 / 2)))) :=
    hbase.comp_injective hinj
  have hmajor : Summable (fun n : ℕ =>
      2 * (((n + 3 + 1 : ℕ) : ℝ) ^ (-(α + 1 / 2)))) :=
    hmajorBase.mul_left 2
  have htail : Summable (fun n : ℕ =>
      suzukiCheckpointCurvaturePowerDamping α (n + 3) *
        suzukiCheckpointSignedCurvaturePositiveMass (n + 3)) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (le_max_right _ _)
    · intro n
      have hmass := suzukiCheckpointSignedCurvaturePositiveMass_le_halfOrder
        (N := n + 3) (by omega)
      have hweight : 0 ≤ (((n + 3 + 1 : ℕ) : ℝ) ^ (-α)) :=
        Real.rpow_nonneg (by positivity) _
      have hproduct := abscissa_rpow_product α
        (show (0 : ℝ) < ((n + 3 + 1 : ℕ) : ℝ) by positivity)
      change (((n + 3 + 1 : ℕ) : ℝ) ^ (-α)) *
          suzukiCheckpointSignedCurvaturePositiveMass (n + 3) ≤
        2 * (((n + 3 + 1 : ℕ) : ℝ) ^ (-(α + 1 / 2)))
      calc
        _ ≤ (((n + 3 + 1 : ℕ) : ℝ) ^ (-α)) *
              (2 * (((n + 3 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hmass hweight
        _ = 2 * ((((n + 3 + 1 : ℕ) : ℝ) ^ (-α)) *
              (((n + 3 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))) := by ring
        _ = 2 * (((n + 3 + 1 : ℕ) : ℝ) ^ (-(α + 1 / 2))) := by rw [hproduct]
    · exact hmajor
  exact (summable_nat_add_iff 3).mp htail

/-- Above the half-order wall, negative Suzuki curvature Jordan mass is summable. -/
theorem summable_suzukiCheckpointSignedCurvatureNegativeMass_powerDamping_of_half_lt
    {α : ℝ} (hα : 1 / 2 < α) :
    Summable (fun N : ℕ => suzukiCheckpointCurvaturePowerDamping α N *
      suzukiCheckpointSignedCurvatureNegativeMass N) := by
  have hbase : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n *
      (n : ℝ) ^ (-(α + 1 / 2))) :=
    GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow (by linarith)
  have hinj : Function.Injective (fun n : ℕ => n + 3 + 1) := by
    intro m n h
    dsimp at h
    omega
  have hmajor : Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt (n + 3 + 1) *
        (((n + 3 + 1 : ℕ) : ℝ) ^ (-(α + 1 / 2)))) :=
    hbase.comp_injective hinj
  have htail : Summable (fun n : ℕ =>
      suzukiCheckpointCurvaturePowerDamping α (n + 3) *
        suzukiCheckpointSignedCurvatureNegativeMass (n + 3)) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (le_max_right _ _)
    · intro n
      let k := n + 3 + 1
      have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
      have hmass := suzukiCheckpointSignedCurvatureNegativeMass_le_atom
        (N := n + 3) (by omega)
      have hatom : criticalMellinAtomWeight k =
          ArithmeticFunction.vonMangoldt k * ((k : ℝ) ^ (-(1 / 2 : ℝ))) := by
        rw [criticalMellinAtomWeight_eq_div_sqrt, Real.rpow_neg hkpos.le,
          ← Real.sqrt_eq_rpow]
        ring
      have hweight : 0 ≤ ((k : ℝ) ^ (-α)) := Real.rpow_nonneg hkpos.le _
      have hproduct := abscissa_rpow_product α hkpos
      change ((k : ℝ) ^ (-α)) *
          suzukiCheckpointSignedCurvatureNegativeMass (n + 3) ≤
        ArithmeticFunction.vonMangoldt k * ((k : ℝ) ^ (-(α + 1 / 2)))
      calc
        _ ≤ ((k : ℝ) ^ (-α)) * criticalMellinAtomWeight k :=
          mul_le_mul_of_nonneg_left hmass hweight
        _ = ((k : ℝ) ^ (-α)) *
            (ArithmeticFunction.vonMangoldt k * ((k : ℝ) ^ (-(1 / 2 : ℝ)))) := by
          rw [hatom]
        _ = ArithmeticFunction.vonMangoldt k *
            (((k : ℝ) ^ (-α)) * ((k : ℝ) ^ (-(1 / 2 : ℝ)))) := by ring
        _ = ArithmeticFunction.vonMangoldt k * ((k : ℝ) ^ (-(α + 1 / 2))) := by
          rw [hproduct]
    · exact hmajor
  exact (summable_nat_add_iff 3).mp htail

/-- At and below the half-order wall, the positive Jordan sector is nonsummable. -/
theorem not_summable_suzukiCheckpointSignedCurvaturePositiveMass_powerDamping_of_le_half
    {α : ℝ} (hα : α ≤ 1 / 2) :
    ¬ Summable (fun N : ℕ => suzukiCheckpointCurvaturePowerDamping α N *
      suzukiCheckpointSignedCurvaturePositiveMass N) := by
  intro hs
  let i : ℕ → ℕ := fun m => 6 * m + 5
  have hi : Function.Injective i := by
    intro m n h
    dsimp [i] at h
    omega
  have hsub : Summable (fun m : ℕ =>
      suzukiCheckpointCurvaturePowerDamping α (i m) *
        suzukiCheckpointSignedCurvaturePositiveMass (i m)) :=
    hs.comp_injective hi
  have hdom : ∀ m : ℕ,
      (4 / 5 : ℝ) * (((6 * (m + 1) : ℕ) : ℝ) ^ (-(α + 1 / 2))) ≤
        suzukiCheckpointCurvaturePowerDamping α (i m) *
          suzukiCheckpointSignedCurvaturePositiveMass (i m) := by
    intro m
    let k := 6 * (m + 1)
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have hmass := suzukiCheckpointSignedCurvaturePositiveMass_ge_latticeHalfOrder m
    have hweight : 0 ≤ ((k : ℝ) ^ (-α)) := Real.rpow_nonneg hkpos.le _
    have hproduct := abscissa_rpow_product α hkpos
    have hindex : i m + 1 = k := by dsimp [i, k]; omega
    rw [suzukiCheckpointCurvaturePowerDamping, hindex]
    change (4 / 5 : ℝ) * ((k : ℝ) ^ (-(α + 1 / 2))) ≤
      ((k : ℝ) ^ (-α)) * suzukiCheckpointSignedCurvaturePositiveMass (i m)
    calc
      _ = (4 / 5 : ℝ) *
          (((k : ℝ) ^ (-α)) * ((k : ℝ) ^ (-(1 / 2 : ℝ)))) := by
        rw [hproduct]
      _ = ((k : ℝ) ^ (-α)) *
          ((4 / 5 : ℝ) * ((k : ℝ) ^ (-(1 / 2 : ℝ)))) := by ring
      _ ≤ ((k : ℝ) ^ (-α)) * suzukiCheckpointSignedCurvaturePositiveMass (i m) :=
        mul_le_mul_of_nonneg_left (by simpa [i, k] using hmass) hweight
  have hscaled : Summable (fun m : ℕ =>
      (4 / 5 : ℝ) * (((6 * (m + 1) : ℕ) : ℝ) ^ (-(α + 1 / 2)))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hdom hsub
  have hlattice : Summable (fun m : ℕ =>
      (((6 * (m + 1) : ℕ) : ℝ) ^ (-(α + 1 / 2)))) :=
    (summable_mul_left_iff (by norm_num : (4 / 5 : ℝ) ≠ 0)).mp hscaled
  exact abscissa_not_summable_six_succ_rpow (by linarith) hlattice

/-- At and below the half-order wall, the prime-supported negative Jordan sector is nonsummable. -/
theorem not_summable_suzukiCheckpointSignedCurvatureNegativeMass_powerDamping_of_le_half
    {α : ℝ} (hα : α ≤ 1 / 2) :
    ¬ Summable (fun N : ℕ => suzukiCheckpointCurvaturePowerDamping α N *
      suzukiCheckpointSignedCurvatureNegativeMass N) := by
  intro hs
  let i : Nat.Primes → ℕ := fun p => (p : ℕ) - 1
  have hi : Function.Injective i := by
    intro p q h
    apply Subtype.ext
    have hp : 1 ≤ (p : ℕ) := p.property.pos
    have hq : 1 ≤ (q : ℕ) := q.property.pos
    dsimp [i] at h
    omega
  have hsub : Summable (fun p : Nat.Primes =>
      suzukiCheckpointCurvaturePowerDamping α (i p) *
        suzukiCheckpointSignedCurvatureNegativeMass (i p)) :=
    hs.comp_injective hi
  let g : Nat.Primes → ℝ := fun p =>
    if 11 ≤ (p : ℕ) then
      (18 / 25 : ℝ) * ((p : ℝ) ^ (-(α + 1 / 2)))
    else 0
  have hg_nonneg : ∀ p : Nat.Primes, 0 ≤ g p := by
    intro p
    dsimp [g]
    split_ifs <;> positivity
  have hdom : ∀ p : Nat.Primes, g p ≤
      suzukiCheckpointCurvaturePowerDamping α (i p) *
        suzukiCheckpointSignedCurvatureNegativeMass (i p) := by
    intro p
    by_cases hp11 : 11 ≤ (p : ℕ)
    · have hpcast : (0 : ℝ) < (p : ℝ) := by positivity
      have hmass := suzukiCheckpointSignedCurvatureNegativeMass_ge_primeHalfOrder p hp11
      have hweight : 0 ≤ ((p : ℝ) ^ (-α)) := Real.rpow_nonneg hpcast.le _
      have hproduct := abscissa_rpow_product α hpcast
      have hindex : i p + 1 = (p : ℕ) := by
        dsimp [i]
        omega
      change (if 11 ≤ (p : ℕ) then
          (18 / 25 : ℝ) * ((p : ℝ) ^ (-(α + 1 / 2))) else 0) ≤ _
      rw [if_pos hp11]
      rw [suzukiCheckpointCurvaturePowerDamping, hindex]
      calc
        _ = (18 / 25 : ℝ) *
            (((p : ℝ) ^ (-α)) * ((p : ℝ) ^ (-(1 / 2 : ℝ)))) := by
          rw [hproduct]
        _ = ((p : ℝ) ^ (-α)) *
            ((18 / 25 : ℝ) * ((p : ℝ) ^ (-(1 / 2 : ℝ)))) := by ring
        _ ≤ ((p : ℝ) ^ (-α)) * suzukiCheckpointSignedCurvatureNegativeMass (i p) :=
          mul_le_mul_of_nonneg_left (by simpa [i] using hmass) hweight
    · change (if 11 ≤ (p : ℕ) then
          (18 / 25 : ℝ) * ((p : ℝ) ^ (-(α + 1 / 2))) else 0) ≤ _
      rw [if_neg hp11]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_max_right _ _)
  have hg : Summable g := Summable.of_nonneg_of_le hg_nonneg hdom hsub
  have hcofinite : g =ᶠ[cofinite] fun p : Nat.Primes =>
      (18 / 25 : ℝ) * ((p : ℝ) ^ (-(α + 1 / 2))) := by
    apply Filter.eventually_cofinite.mpr
    apply (abscissa_finite_primes_lt 11).subset
    intro p hp
    change (p : ℕ) < 11
    by_contra hnot
    have hp11 : 11 ≤ (p : ℕ) := le_of_not_gt hnot
    exact hp (by simp [g, hp11])
  have hscaled : Summable (fun p : Nat.Primes =>
      (18 / 25 : ℝ) * ((p : ℝ) ^ (-(α + 1 / 2)))) :=
    hg.congr_cofinite hcofinite
  have hprime : Summable (fun p : Nat.Primes =>
      ((p : ℝ) ^ (-(α + 1 / 2)))) :=
    (summable_mul_left_iff (by norm_num : (18 / 25 : ℝ) ≠ 0)).mp hscaled
  exact abscissa_not_summable_prime_rpow (by linarith) hprime

/-- Exact positive-sector polynomial-gauge chamber. -/
theorem summable_suzukiCheckpointSignedCurvaturePositiveMass_powerDamping_iff
    (α : ℝ) :
    Summable (fun N : ℕ => suzukiCheckpointCurvaturePowerDamping α N *
      suzukiCheckpointSignedCurvaturePositiveMass N) ↔ 1 / 2 < α := by
  constructor
  · intro hs
    by_contra hnot
    exact not_summable_suzukiCheckpointSignedCurvaturePositiveMass_powerDamping_of_le_half
      (le_of_not_gt hnot) hs
  · exact summable_suzukiCheckpointSignedCurvaturePositiveMass_powerDamping_of_half_lt

/-- Exact negative-sector polynomial-gauge chamber. -/
theorem summable_suzukiCheckpointSignedCurvatureNegativeMass_powerDamping_iff
    (α : ℝ) :
    Summable (fun N : ℕ => suzukiCheckpointCurvaturePowerDamping α N *
      suzukiCheckpointSignedCurvatureNegativeMass N) ↔ 1 / 2 < α := by
  constructor
  · intro hs
    by_contra hnot
    exact not_summable_suzukiCheckpointSignedCurvatureNegativeMass_powerDamping_of_le_half
      (le_of_not_gt hnot) hs
  · exact summable_suzukiCheckpointSignedCurvatureNegativeMass_powerDamping_of_half_lt

/-- **Common Jordan abscissa rigidity.** Both exact curvature sectors cross into finite variation
at precisely the same half-order wall. -/
theorem summable_suzukiCheckpointSignedCurvatureJordan_powerDamping_iff
    (α : ℝ) :
    (Summable (fun N : ℕ => suzukiCheckpointCurvaturePowerDamping α N *
        suzukiCheckpointSignedCurvaturePositiveMass N) ∧
      Summable (fun N : ℕ => suzukiCheckpointCurvaturePowerDamping α N *
        suzukiCheckpointSignedCurvatureNegativeMass N)) ↔ 1 / 2 < α := by
  rw [summable_suzukiCheckpointSignedCurvaturePositiveMass_powerDamping_iff,
    summable_suzukiCheckpointSignedCurvatureNegativeMass_powerDamping_iff,
    and_self]

/-- Closed route-class obstruction: no half-order or subcritical polynomial gauge compactifies
even the positive Jordan sector, hence none compactifies the exact two-sided source. -/
theorem no_halfOrderPolynomialDamping_summable_suzukiCheckpointCurvatureJordan :
    ¬ ∃ α : ℝ, α ≤ 1 / 2 ∧
      Summable (fun N : ℕ => suzukiCheckpointCurvaturePowerDamping α N *
        suzukiCheckpointSignedCurvaturePositiveMass N) ∧
      Summable (fun N : ℕ => suzukiCheckpointCurvaturePowerDamping α N *
        suzukiCheckpointSignedCurvatureNegativeMass N) := by
  rintro ⟨α, hα, hpos, hneg⟩
  exact not_summable_suzukiCheckpointSignedCurvaturePositiveMass_powerDamping_of_le_half hα hpos

end RHTower
