import GaloisForLFunctions.HTGeometry.HardyGeometricResolvent

/-!
# Number-minus-KMS eigenmodes

The geometric reproducing kernel and shifted Blaschke monomials satisfy the
actual number-minus-geometric-kernel equations coefficient by coefficient.
-/

noncomputable section

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {q : ℝ}

/-- The squared resolvent counts the intermediate positions in its triangular
geometric convolution. -/
theorem geometricResolvent_sq_single_apply (hq : ‖(q : ℂ)‖ < 1) (m n : ℕ) :
    hardyGeometricResolvent hq (hardyGeometricResolvent hq (lp.single 2 m (1 : ℂ))) n =
      if m ≤ n then ((n - m + 1 : ℕ) : ℂ) * (q : ℂ) ^ (n - m) else 0 := by
  induction n with
  | zero =>
    rw [geometricResolvent_apply_zero, geometricResolvent_single_apply]
    by_cases hm : m = 0
    · subst m
      norm_num
    · simp only [Nat.le_zero, hm, ↓reduceIte]
  | succ n ih =>
    rw [geometricResolvent_apply_succ, ih, geometricResolvent_single_apply]
    by_cases hm : m ≤ n
    · simp only [if_pos hm, if_pos (show m ≤ n + 1 by omega)]
      rw [show n + 1 - m = (n - m) + 1 by omega, pow_succ]
      push_cast
      ring
    · by_cases heq : m = n + 1
      · subst m
        simp
      · simp only [if_neg hm, if_neg (show ¬ m ≤ n + 1 by omega), mul_zero, add_zero]

theorem geometricResolvent_single_zero (hq : ‖(q : ℂ)‖ < 1) :
    hardyGeometricResolvent hq (lp.single 2 0 (1 : ℂ)) = hardyKernel hq := by
  apply lp.ext
  funext n
  rw [geometricResolvent_single_apply, if_pos (Nat.zero_le _), Nat.sub_zero]
  change (q : ℂ) ^ n = (starRingEnd ℂ (q : ℂ)) ^ n
  rw [Complex.conj_ofReal]

theorem geometricResolvent_kernel_apply (hq : ‖(q : ℂ)‖ < 1) (n : ℕ) :
    hardyGeometricResolvent hq (hardyKernel hq) n =
      ((n + 1 : ℕ) : ℂ) * (q : ℂ) ^ n := by
  rw [← geometricResolvent_single_zero hq, geometricResolvent_sq_single_apply,
    if_pos (Nat.zero_le _), Nat.sub_zero]

/-- The reproducing kernel is an adjoint eigenvector of the analytic resolvent. -/
theorem geometricResolvent_adjoint_kernel (hq : ‖(q : ℂ)‖ < 1) :
    ContinuousLinearMap.adjoint (hardyGeometricResolvent hq) (hardyKernel hq) =
      ((1 : ℂ) - (q : ℂ) ^ 2)⁻¹ • hardyKernel hq := by
  apply ext_inner_right ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, inner_hardyKernel,
    hardyFun_geometricResolvent hq _ hq, inner_smul_left, inner_hardyKernel,
    map_inv₀, map_sub, map_one, map_pow, Complex.conj_ofReal]
  rw [pow_two, div_eq_inv_mul]

/-- The Blaschke multiplier is the shift difference followed by the resolvent. -/
theorem blaschkeMul_eq_shift_geometricResolvent (hq : ‖(q : ℂ)‖ < 1) (x : HardyDisk) :
    blaschkeMul hq x = hardyShift (hardyGeometricResolvent hq x) -
      (q : ℂ) • hardyGeometricResolvent hq x := by
  apply hardyDisk_ext fun z hz => ?_
  rw [blaschkeMul, hardyFun_hardyMul _ _ hz, sub_eq_add_neg, ← neg_smul,
    hardyFun_add _ _ hz, hardyFun_smul _ _ hz, hardyFun_hardyMul diskShift _ hz,
    hardyFun_geometricResolvent hq _ hz]
  change (singleBlaschke hq).fn z * hardyFun x z =
    z * (hardyFun x z / (1 - (q : ℂ) * z)) +
      (-(q : ℂ)) * (hardyFun x z / (1 - (q : ℂ) * z))
  rw [singleBlaschke_fn, blaschkeFactor, Complex.conj_ofReal]
  ring

theorem geometricResolvent_adjoint_blaschkeMul (hq : ‖(q : ℂ)‖ < 1) (x : HardyDisk) :
    ContinuousLinearMap.adjoint (hardyGeometricResolvent hq) (blaschkeMul hq x) =
      ((1 : ℂ) - (q : ℂ) ^ 2)⁻¹ • (blaschkeMul hq x + (q : ℂ) • x) := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, hardyGeometricResolvent_apply,
    inner_smul_right, inner_add_right, inner_smul_right, inner_blaschkeMul,
    inner_smul_left, inner_add_left, inner_smul_left,
    map_inv₀, map_sub, map_one, map_pow, Complex.conj_ofReal]

/-- The KMS image of a Blaschke multiple has a double resolvent and one shift. -/
theorem hardyGeometricKMS_blaschkeMul (hq : ‖(q : ℂ)‖ < 1) (x : HardyDisk) :
    hardyGeometricKMS hq (blaschkeMul hq x) =
      ((1 : ℂ) - (q : ℂ) ^ 2) •
        hardyShift (hardyGeometricResolvent hq (hardyGeometricResolvent hq x)) := by
  change hardyGeometricResolvent hq (blaschkeMul hq x) +
    ContinuousLinearMap.adjoint (hardyGeometricResolvent hq) (blaschkeMul hq x) -
      blaschkeMul hq x = _
  rw [geometricResolvent_adjoint_blaschkeMul]
  apply hardyDisk_ext fun z hz => ?_
  have hneg : hardyFun (-(blaschkeMul hq x)) z = -hardyFun (blaschkeMul hq x) z := by
    simpa only [neg_one_smul, neg_one_mul] using
      hardyFun_smul (-1 : ℂ) (blaschkeMul hq x) hz
  rw [sub_eq_add_neg]
  rw [hardyFun_add _ _ hz, hardyFun_add _ _ hz,
    hardyFun_smul _ _ hz, hardyFun_add _ _ hz, hardyFun_smul _ _ hz,
    hneg, hardyFun_smul _ _ hz,
    hardyFun_hardyMul diskShift _ hz, hardyFun_geometricResolvent hq _ hz,
    hardyFun_geometricResolvent hq _ hz, hardyFun_geometricResolvent hq _ hz]
  have hB : hardyFun (blaschkeMul hq x) z = blaschkeFactor (q : ℂ) z * hardyFun x z := by
    rw [blaschkeMul, hardyFun_hardyMul _ _ hz]
    change (singleBlaschke hq).fn z * hardyFun x z = _
    rw [singleBlaschke_fn]
  rw [hB, blaschkeFactor, Complex.conj_ofReal]
  change ((z - (q : ℂ)) / (1 - (q : ℂ) * z) * hardyFun x z) /
      (1 - (q : ℂ) * z) +
    (1 - (q : ℂ) ^ 2)⁻¹ *
      ((z - (q : ℂ)) / (1 - (q : ℂ) * z) * hardyFun x z + (q : ℂ) * hardyFun x z) -
    (z - (q : ℂ)) / (1 - (q : ℂ) * z) * hardyFun x z =
      (1 - (q : ℂ) ^ 2) * (z * (hardyFun x z / (1 - (q : ℂ) * z) /
        (1 - (q : ℂ) * z)))
  have hd := hardyRealBlaschkeDen_at_ne_zero hq hz
  have hd' : (1 : ℂ) - z * (q : ℂ) ≠ 0 := by simpa only [mul_comm] using hd
  field_simp [hardyRealBlaschkeDen_ne_zero hq, hd, hd']
  ring

/-- The shifted Blaschke monomial has one leading coefficient and a geometric tail. -/
theorem blaschkeMul_single_apply (hq : ‖(q : ℂ)‖ < 1) (j n : ℕ) :
    blaschkeMul hq (lp.single 2 j (1 : ℂ)) n =
      if j < n then (1 - (q : ℂ) ^ 2) * (q : ℂ) ^ (n - (j + 1))
      else if n = j then -(q : ℂ) else 0 := by
  rw [blaschkeMul_eq_shift_geometricResolvent]
  change hardyShift (hardyGeometricResolvent hq (lp.single 2 j (1 : ℂ))) n -
    (q : ℂ) * hardyGeometricResolvent hq (lp.single 2 j (1 : ℂ)) n = _
  cases n with
  | zero =>
    rw [hardyShift_apply_zero, geometricResolvent_single_apply]
    by_cases hj : j = 0
    · subst j
      simp
    · simp [hj, Ne.symm hj]
  | succ n =>
    rw [hardyShift_apply_succ, geometricResolvent_single_apply,
      geometricResolvent_single_apply]
    by_cases hj : j ≤ n
    · rw [if_pos hj, if_pos (by omega : j ≤ n + 1), if_pos (by omega : j < n + 1),
        show n + 1 - (j + 1) = n - j by omega,
        show n + 1 - j = (n - j) + 1 by omega, pow_succ]
      ring
    · rw [if_neg hj, if_neg (by omega : ¬ j < n + 1)]
      by_cases heq : n + 1 = j
      · subst j
        simp
      · rw [if_neg (by omega : ¬ j ≤ n + 1), if_neg heq, mul_zero, sub_zero]

/-- The KMS action on every excited mode is an exact number-coordinate identity. -/
theorem hardyGeometricKMS_blaschke_single_apply (hq : ‖(q : ℂ)‖ < 1) (j n : ℕ) :
    hardyGeometricKMS hq (blaschkeMul hq (lp.single 2 j (1 : ℂ))) n =
      ((n : ℂ) - (j : ℂ)) * blaschkeMul hq (lp.single 2 j (1 : ℂ)) n := by
  rw [hardyGeometricKMS_blaschkeMul]
  change (1 - (q : ℂ) ^ 2) *
    hardyShift (hardyGeometricResolvent hq
      (hardyGeometricResolvent hq (lp.single 2 j (1 : ℂ)))) n = _
  cases n with
  | zero =>
    rw [hardyShift_apply_zero, blaschkeMul_single_apply]
    by_cases hj : j = 0
    · subst j
      simp
    · simp [Ne.symm hj]
  | succ n =>
    rw [hardyShift_apply_succ, geometricResolvent_sq_single_apply,
      blaschkeMul_single_apply]
    by_cases hj : j ≤ n
    · rw [if_pos hj, if_pos (by omega : j < n + 1),
        show n + 1 - (j + 1) = n - j by omega, Nat.cast_add, Nat.cast_sub hj,
        Nat.cast_one, Nat.cast_add, Nat.cast_one]
      ring
    · rw [if_neg hj, if_neg (by omega : ¬ j < n + 1)]
      by_cases heq : n + 1 = j
      · rw [if_pos heq, heq, sub_self, zero_mul, mul_zero]
      · rw [if_neg heq, mul_zero, mul_zero]

/-- The geometric ground vector has an exact affine number-coordinate KMS image. -/
theorem hardyGeometricKMS_kernel_apply (hq : ‖(q : ℂ)‖ < 1) (n : ℕ) :
    hardyGeometricKMS hq (hardyKernel hq) n =
      ((n : ℂ) + (1 - (q : ℂ) ^ 2)⁻¹) * (q : ℂ) ^ n := by
  change hardyGeometricResolvent hq (hardyKernel hq) n +
    ContinuousLinearMap.adjoint (hardyGeometricResolvent hq) (hardyKernel hq) n -
      hardyKernel hq n = _
  rw [geometricResolvent_kernel_apply, geometricResolvent_adjoint_kernel]
  change ((n + 1 : ℕ) : ℂ) * (q : ℂ) ^ n +
    (1 - (q : ℂ) ^ 2)⁻¹ * (starRingEnd ℂ (q : ℂ)) ^ n -
      (starRingEnd ℂ (q : ℂ)) ^ n = _
  rw [Complex.conj_ofReal]
  push_cast
  ring

/-- The kernel lies in the number domain because its weighted sequence is a
difference of two existing Hardy vectors. -/
theorem memlp_number_hardyKernel (hq : ‖(q : ℂ)‖ < 1) :
    Memℓp (fun n : ℕ => (n : ℂ) * hardyKernel hq n) 2 := by
  have hfun : (fun n : ℕ => (n : ℂ) * hardyKernel hq n) =
      fun n => (hardyGeometricResolvent hq (hardyKernel hq) - hardyKernel hq) n := by
    funext n
    change (n : ℂ) * hardyKernel hq n =
      hardyGeometricResolvent hq (hardyKernel hq) n - hardyKernel hq n
    rw [geometricResolvent_kernel_apply]
    change (n : ℂ) * (starRingEnd ℂ (q : ℂ)) ^ n =
      ((n + 1 : ℕ) : ℂ) * (q : ℂ) ^ n - (starRingEnd ℂ (q : ℂ)) ^ n
    rw [Complex.conj_ofReal]
    push_cast
    ring
  rw [hfun]
  exact lp.memℓp _

/-- Every excited mode lies in the number domain by its bounded KMS image. -/
theorem memlp_number_blaschke_single (hq : ‖(q : ℂ)‖ < 1) (j : ℕ) :
    Memℓp (fun n : ℕ => (n : ℂ) * blaschkeMul hq (lp.single 2 j (1 : ℂ)) n) 2 := by
  let u := blaschkeMul hq (lp.single 2 j (1 : ℂ))
  have hfun : (fun n : ℕ => (n : ℂ) * u n) =
      fun n => (hardyGeometricKMS hq u + (j : ℂ) • u) n := by
    funext n
    change (n : ℂ) * u n = hardyGeometricKMS hq u n + (j : ℂ) * u n
    rw [show hardyGeometricKMS hq u n = ((n : ℂ) - (j : ℂ)) * u n from
      hardyGeometricKMS_blaschke_single_apply hq j n]
    ring
  change Memℓp (fun n : ℕ => (n : ℂ) * u n) 2
  rw [hfun]
  exact lp.memℓp _

end GaloisForLFunctions.HTGeometry
