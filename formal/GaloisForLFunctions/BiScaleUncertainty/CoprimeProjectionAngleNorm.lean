import GaloisForLFunctions.BiScaleUncertainty.CoprimeProjectionAnglePolynomial

/-!
# Sharp arithmetic norms of products and commutators

The reduced product polynomial and the C*-identity determine the exact norms
on the full physical velocity space.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

theorem coprimeAngleSquare_nonneg (d e : ℕ) : 0 ≤ coprimeAngleSquare d e := by
  unfold coprimeAngleSquare
  split_ifs <;> norm_num

theorem coprimeAngleSquare_le_one (d e : ℕ) : coprimeAngleSquare d e ≤ 1 := by
  unfold coprimeAngleSquare
  split_ifs <;> norm_num

theorem coprimeProjector_mul_lcm (d e : ℕ) :
    coprimeProjector d * coprimeProjector (coprimeLcm d e) =
      coprimeProjector (coprimeLcm d e) :=
  coprimeProjector_comp_of_dvd d (coprimeLcm d e)
    (by simpa using Nat.dvd_lcm_left (d + 2) (e + 2))

theorem coprimeLcmProjector_mul (d e : ℕ) :
    coprimeProjector (coprimeLcm d e) * coprimeProjector d =
      coprimeProjector (coprimeLcm d e) :=
  coprimeProjector_comp_of_dvd_reverse d (coprimeLcm d e)
    (by simpa using Nat.dvd_lcm_left (d + 2) (e + 2))

theorem reducedCoprimeProduct_star_product (d e : ℕ) :
    reducedCoprimeProduct d e * reducedCoprimeProduct e d * reducedCoprimeProduct d e =
      reducedCoprimeProduct d e * reducedCoprimeProduct d e := by
  have hPP (x : Velocity) : coprimeProjector d (coprimeProjector d x) =
      coprimeProjector d x := coprimeProjection_idempotent d x
  have hQQ (x : Velocity) : coprimeProjector e (coprimeProjector e x) =
      coprimeProjector e x := coprimeProjection_idempotent e x
  have hRR (x : Velocity) :
      coprimeProjector (coprimeLcm d e) (coprimeProjector (coprimeLcm d e) x) =
        coprimeProjector (coprimeLcm d e) x := coprimeProjection_idempotent _ x
  have hPR (x : Velocity) : coprimeProjector d (coprimeProjector (coprimeLcm d e) x) =
      coprimeProjector (coprimeLcm d e) x :=
    congrArg (fun A : Velocity →L[ℝ] Velocity => A x) (coprimeProjector_mul_lcm d e)
  have hRP (x : Velocity) : coprimeProjector (coprimeLcm d e) (coprimeProjector d x) =
      coprimeProjector (coprimeLcm d e) x :=
    congrArg (fun A : Velocity →L[ℝ] Velocity => A x) (coprimeLcmProjector_mul d e)
  have hQR (x : Velocity) : coprimeProjector e (coprimeProjector (coprimeLcm d e) x) =
      coprimeProjector (coprimeLcm d e) x := by
    rw [coprimeLcm_comm d e]
    exact congrArg (fun A : Velocity →L[ℝ] Velocity => A x) (coprimeProjector_mul_lcm e d)
  have hRQ (x : Velocity) : coprimeProjector (coprimeLcm d e) (coprimeProjector e x) =
      coprimeProjector (coprimeLcm d e) x := by
    rw [coprimeLcm_comm d e]
    exact congrArg (fun A : Velocity →L[ℝ] Velocity => A x) (coprimeLcmProjector_mul e d)
  apply ContinuousLinearMap.ext
  intro q
  simp only [reducedCoprimeProduct, coprimeLcm_comm e d,
    sub_apply, mul_apply_eq_comp, map_sub,
    hPP, hQQ, hRR, hPR, hRP, hQR, hRQ]
  abel

private theorem norm_of_selfadjoint_quadratic (A : Velocity →L[ℝ] Velocity) (c : ℝ)
    (hc : 0 ≤ c) (hs : star A = A) (hq : A * A = c • A) (hn : A ≠ 0) :
    ‖A‖ = c := by
  have h := CStarRing.norm_star_mul_self (x := A)
  rw [hs, hq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at h
  have hp := norm_pos_iff.mpr hn
  nlinarith only [h, hp]

theorem reducedCoprimeProduct_ne_zero (d e : ℕ)
    (hg : ¬2 ≤ Nat.gcd (d + 2) (e + 2)) : reducedCoprimeProduct d e ≠ 0 := by
  intro h
  have hs := congrArg star h
  simp only [reducedCoprimeProduct_star, star_zero] at hs
  have hpq := sub_eq_zero.mp h
  have hqp := sub_eq_zero.mp hs
  change coprimeProjector d * coprimeProjector e = coprimeProjector (coprimeLcm d e) at hpq
  change coprimeProjector e * coprimeProjector d = coprimeProjector (coprimeLcm e d) at hqp
  rw [coprimeLcm_comm e d] at hqp
  exact hg ((coprimeProjector_commute_iff d e).mp (hpq.trans hqp.symm))

/-- Exact squared norm of the product after removing the common range. -/
theorem norm_sq_reducedCoprimeProduct (d e : ℕ) :
    ‖reducedCoprimeProduct d e‖ ^ 2 = coprimeAngleSquare d e := by
  by_cases hg : 2 ≤ Nat.gcd (d + 2) (e + 2)
  · simp [reducedCoprimeProduct_eq_zero_of_gcd d e hg, coprimeAngleSquare, hg]
  let T := reducedCoprimeProduct d e
  let U := reducedCoprimeProduct e d
  let A := T * U
  have hnorm : ‖A‖ = ‖T‖ * ‖T‖ := by
    simpa only [A, T, U, reducedCoprimeProduct_star] using
      CStarRing.norm_self_mul_star (x := reducedCoprimeProduct d e)
  have hstar : star A = A := by
    simp only [A, T, U, star_mul, reducedCoprimeProduct_star]
  have hquad : A * A = coprimeAngleSquare d e • A := by
    calc
      A * A = (T * U * T) * U := by simp only [A, mul_assoc]
      _ = (T * T) * U := by rw [reducedCoprimeProduct_star_product]
      _ = coprimeAngleSquare d e • A := by
        rw [reducedCoprimeProduct_square, smul_mul_assoc]
  have hne : A ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    have hp := norm_pos_iff.mpr (reducedCoprimeProduct_ne_zero d e hg)
    change 0 < ‖T‖ at hp
    nlinarith only [hnorm, hp]
  have hval := norm_of_selfadjoint_quadratic A _ (coprimeAngleSquare_nonneg d e)
    hstar hquad hne
  nlinarith only [hval, hnorm]

def coprimeCommutator (d e : ℕ) : Velocity →L[ℝ] Velocity :=
  reducedCoprimeProduct d e - reducedCoprimeProduct e d

theorem coprimeCommutator_eq (d e : ℕ) :
    coprimeCommutator d e =
      coprimeProjector d * coprimeProjector e - coprimeProjector e * coprimeProjector d := by
  simp only [coprimeCommutator, reducedCoprimeProduct, coprimeLcm_comm e d]
  abel

theorem coprimeCommutator_star (d e : ℕ) :
    star (coprimeCommutator d e) = -coprimeCommutator d e := by
  simp only [coprimeCommutator, star_sub, reducedCoprimeProduct_star, neg_sub]

private theorem commutator_cube_algebra (T U : Velocity →L[ℝ] Velocity) (c : ℝ)
    (hT : T * T = c • T) (hU : U * U = c • U)
    (hTU : T * U * T = T * T) (hUT : U * T * U = U * U) :
    (T - U) * (T - U) * (T - U) = (c * c - c) • (T - U) := by
  have hTTT : T * (T * T) = (c * c) • T := by
    rw [hT, mul_smul_comm, hT, smul_smul]
  have hTTU : T * (T * U) = c • (T * U) := by
    rw [← mul_assoc, hT, smul_mul_assoc]
  have hTUT : T * (U * T) = c • T := by rw [← mul_assoc, hTU, hT]
  have hTUU : T * (U * U) = c • (T * U) := by rw [hU, mul_smul_comm]
  have hUTT : U * (T * T) = c • (U * T) := by rw [hT, mul_smul_comm]
  have hUTU : U * (T * U) = c • U := by rw [← mul_assoc, hUT, hU]
  have hUUT : U * (U * T) = c • (U * T) := by rw [← mul_assoc, hU, smul_mul_assoc]
  have hUUU : U * (U * U) = (c * c) • U := by
    rw [hU, mul_smul_comm, hU, smul_smul]
  simp only [sub_mul, mul_sub, mul_assoc, hTTT, hTTU, hTUT, hTUU,
    hUTT, hUTU, hUUT, hUUU, smul_sub, sub_smul]
  abel

theorem coprimeCommutator_cube (d e : ℕ) :
    coprimeCommutator d e * coprimeCommutator d e * coprimeCommutator d e =
      -(coprimeAngleSquare d e * (1 - coprimeAngleSquare d e)) • coprimeCommutator d e := by
  have h := commutator_cube_algebra (reducedCoprimeProduct d e) (reducedCoprimeProduct e d)
    (coprimeAngleSquare d e) (reducedCoprimeProduct_square d e)
    (by simpa only [coprimeAngleSquare_comm e d] using reducedCoprimeProduct_square e d)
    (reducedCoprimeProduct_star_product d e) (reducedCoprimeProduct_star_product e d)
  have hc : coprimeAngleSquare d e * coprimeAngleSquare d e - coprimeAngleSquare d e =
      -(coprimeAngleSquare d e * (1 - coprimeAngleSquare d e)) := by ring
  rw [hc] at h
  exact h

theorem coprimeCommutator_ne_zero (d e : ℕ)
    (hg : ¬2 ≤ Nat.gcd (d + 2) (e + 2)) : coprimeCommutator d e ≠ 0 := by
  rw [coprimeCommutator_eq]
  intro h
  exact hg ((coprimeProjector_commute_iff d e).mp (sub_eq_zero.mp h))

private theorem commutator_star_quadratic (d e : ℕ) :
    (star (coprimeCommutator d e) * coprimeCommutator d e) *
        (star (coprimeCommutator d e) * coprimeCommutator d e) =
      (coprimeAngleSquare d e * (1 - coprimeAngleSquare d e)) •
        (star (coprimeCommutator d e) * coprimeCommutator d e) := by
  let K := coprimeCommutator d e
  let B := star K * K
  let c := coprimeAngleSquare d e * (1 - coprimeAngleSquare d e)
  change B * B = c • B
  calc
    B * B = (K * K * K) * K := by
      simp only [B, K, coprimeCommutator_star, neg_mul, mul_neg, neg_neg, mul_assoc]
    _ = (-c • K) * K := by rw [coprimeCommutator_cube]
    _ = c • B := by simp only [B, K, coprimeCommutator_star,
      neg_smul, smul_mul_assoc, neg_mul, smul_neg]

/-- Exact squared commutator norm, including the exceptional spacing-two stars. -/
theorem norm_sq_coprimeCommutator (d e : ℕ) :
    ‖coprimeCommutator d e‖ ^ 2 =
      coprimeAngleSquare d e * (1 - coprimeAngleSquare d e) := by
  by_cases hg : 2 ≤ Nat.gcd (d + 2) (e + 2)
  · have hs : 2 ≤ Nat.gcd (e + 2) (d + 2) := by simpa only [Nat.gcd_comm] using hg
    simp [coprimeCommutator, reducedCoprimeProduct_eq_zero_of_gcd d e hg,
      reducedCoprimeProduct_eq_zero_of_gcd e d hs, coprimeAngleSquare, hg]
  let K := coprimeCommutator d e
  let B := star K * K
  let c := coprimeAngleSquare d e * (1 - coprimeAngleSquare d e)
  have hnorm : ‖B‖ = ‖K‖ * ‖K‖ := CStarRing.norm_star_mul_self
  have hstar : star B = B := by simp [B, star_mul]
  have hquad : B * B = c • B := commutator_star_quadratic d e
  have hne : B ≠ 0 :=
    (CStarRing.star_mul_self_ne_zero_iff K).2 (coprimeCommutator_ne_zero d e hg)
  have hc : 0 ≤ c := mul_nonneg (coprimeAngleSquare_nonneg d e)
    (sub_nonneg.mpr (coprimeAngleSquare_le_one d e))
  have hval := norm_of_selfadjoint_quadratic B c hc hstar hquad hne
  nlinarith only [hval, hnorm]

theorem norm_reducedCoprimeProduct (d e : ℕ) :
    ‖reducedCoprimeProduct d e‖ = Real.sqrt (coprimeAngleSquare d e) := by
  rw [← norm_sq_reducedCoprimeProduct, Real.sqrt_sq (norm_nonneg _)]

theorem norm_coprimeCommutator (d e : ℕ) :
    ‖coprimeCommutator d e‖ =
      Real.sqrt (coprimeAngleSquare d e * (1 - coprimeAngleSquare d e)) := by
  rw [← norm_sq_coprimeCommutator, Real.sqrt_sq (norm_nonneg _)]

private theorem exists_quadratic_norm_attainer (T : Velocity →L[ℝ] Velocity) (c : ℝ)
    (hn : T ≠ 0) (hq : (star T * T) * (star T * T) = c • (star T * T)) :
    ∃ q : Velocity, q ≠ 0 ∧ ‖T q‖ ^ 2 = c * ‖q‖ ^ 2 := by
  let A := star T * T
  have hA : A ≠ 0 := (CStarRing.star_mul_self_ne_zero_iff T).2 hn
  have hex : ∃ x : Velocity, A x ≠ 0 := by
    by_contra h
    have hz : ∀ x : Velocity, A x = 0 := by simpa using h
    apply hA
    apply ContinuousLinearMap.ext
    exact hz
  obtain ⟨x, hx⟩ := hex
  refine ⟨A x, hx, ?_⟩
  have heig : A (A x) = c • A x :=
    congrArg (fun B : Velocity →L[ℝ] Velocity => B x) hq
  have he := T.apply_norm_sq_eq_inner_adjoint_left (A x)
  change ‖T (A x)‖ ^ 2 = ⟪A (A x), A x⟫ at he
  rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq] at he
  exact he

private theorem tent_zero_ne_zero (d : ℕ) : tentVelocity d 0 ≠ 0 := by
  intro h
  have hi := inner_tentVelocity d 0 0
  rw [h, inner_zero_left] at hi
  norm_num at hi

/-- The sharp reduced-product norm is attained by an actual nonzero velocity. -/
theorem exists_reducedCoprimeProduct_norm_attainer (d e : ℕ) :
    ∃ q : Velocity, q ≠ 0 ∧ ‖reducedCoprimeProduct d e q‖ ^ 2 =
      coprimeAngleSquare d e * ‖q‖ ^ 2 := by
  by_cases hg : 2 ≤ Nat.gcd (d + 2) (e + 2)
  · refine ⟨tentVelocity d 0, tent_zero_ne_zero d, ?_⟩
    simp [reducedCoprimeProduct_eq_zero_of_gcd d e hg, coprimeAngleSquare, hg]
  apply exists_quadratic_norm_attainer _ _ (reducedCoprimeProduct_ne_zero d e hg)
  rw [reducedCoprimeProduct_star]
  calc
    (reducedCoprimeProduct e d * reducedCoprimeProduct d e) *
        (reducedCoprimeProduct e d * reducedCoprimeProduct d e) =
      (reducedCoprimeProduct e d * reducedCoprimeProduct d e * reducedCoprimeProduct e d) *
        reducedCoprimeProduct d e := by simp only [mul_assoc]
    _ = (reducedCoprimeProduct e d * reducedCoprimeProduct e d) *
        reducedCoprimeProduct d e := by rw [reducedCoprimeProduct_star_product]
    _ = coprimeAngleSquare d e •
        (reducedCoprimeProduct e d * reducedCoprimeProduct d e) := by
      rw [reducedCoprimeProduct_square, coprimeAngleSquare_comm e d, smul_mul_assoc]

/-- The commutator norm is also attained, including the zero-commutator case. -/
theorem exists_coprimeCommutator_norm_attainer (d e : ℕ) :
    ∃ q : Velocity, q ≠ 0 ∧ ‖coprimeCommutator d e q‖ ^ 2 =
      (coprimeAngleSquare d e * (1 - coprimeAngleSquare d e)) * ‖q‖ ^ 2 := by
  by_cases hg : 2 ≤ Nat.gcd (d + 2) (e + 2)
  · have hz : coprimeCommutator d e = 0 := by
      rw [coprimeCommutator_eq]
      exact sub_eq_zero.mpr ((coprimeProjector_commute_iff d e).mpr hg)
    refine ⟨tentVelocity d 0, tent_zero_ne_zero d, ?_⟩
    simp [hz, coprimeAngleSquare, hg]
  exact exists_quadratic_norm_attainer _ _ (coprimeCommutator_ne_zero d e hg)
    (commutator_star_quadratic d e)

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
