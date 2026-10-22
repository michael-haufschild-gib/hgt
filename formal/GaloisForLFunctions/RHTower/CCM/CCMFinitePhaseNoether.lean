import GaloisForLFunctions.RHTower.CCM.CCMFinitePrimeCliques
import GaloisForLFunctions.RHTower.CCM.CCMWeilTriangleNoether

/-!
# Finite arithmetic phase actions and exact torque balance

Every finite family of actual Weil sources gives a two-channel phase potential.
Common phase translation is an exact continuous symmetry. Its interaction
torques cancel, and total angular momentum is conserved on Newton trajectories.
The kinetic masses below are a chosen mechanical realization of this potential.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

variable {ι : Type*} [Fintype ι]

def ccmWeilFinitePhaseEnergy (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta : ι → ℝ) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a (∑ i, (Real.cos (theta i) : ℂ) • u i) +
    ccmRestrictedWeilSourceQuadratic a (∑ i, (Real.sin (theta i) : ℂ) • u i)

theorem ccmWeilFinitePhaseEnergy_eq (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta : ι → ℝ) :
    ccmWeilFinitePhaseEnergy a u theta =
      ∑ i, ∑ j, ccmWeilRealPolar a (u i) (u j) * Real.cos (theta i - theta j) := by
  unfold ccmWeilFinitePhaseEnergy
  rw [ccmRestrictedWeilSourceQuadratic_real_sum, ccmRestrictedWeilSourceQuadratic_real_sum]
  simp only [finiteSignedQuadratic, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.cos_sub]
  ring

theorem ccmWeilFinitePhaseEnergy_common_shift (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta : ι → ℝ) (t : ℝ) :
    ccmWeilFinitePhaseEnergy a u (fun i => theta i + t) = ccmWeilFinitePhaseEnergy a u theta := by
  simp only [ccmWeilFinitePhaseEnergy_eq, add_sub_add_right_eq_sub]

def ccmWeilFinitePhaseTorque (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta : ι → ℝ) (i : ι) : ℝ :=
  2 * ∑ j, ccmWeilRealPolar a (u i) (u j) * Real.sin (theta i - theta j)

omit [Fintype ι] in
private theorem phase_interaction_skew (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta : ι → ℝ) (i j : ι) :
    ccmWeilRealPolar a (u j) (u i) * Real.sin (theta j - theta i) =
      -(ccmWeilRealPolar a (u i) (u j) * Real.sin (theta i - theta j)) := by
  rw [ccmWeilRealPolar_symm a (u j) (u i),
    show theta j - theta i = -(theta i - theta j) by ring, Real.sin_neg]
  ring

theorem ccmWeilFinitePhaseTorque_sum_zero (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta : ι → ℝ) :
    (∑ i, ccmWeilFinitePhaseTorque a u theta i) = 0 := by
  let A := fun i j => ccmWeilRealPolar a (u i) (u j) * Real.sin (theta i - theta j)
  have hs : (∑ i, ∑ j, A i j) = -(∑ i, ∑ j, A i j) := by
    calc
      _ = ∑ i, ∑ j, A j i := Finset.sum_comm
      _ = ∑ i, ∑ j, -(A i j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_congr rfl fun j _ => phase_interaction_skew a u theta i j
      _ = _ := by simp only [Finset.sum_neg_distrib]
  unfold ccmWeilFinitePhaseTorque
  rw [← Finset.mul_sum]
  change 2 * (∑ i, ∑ j, A i j) = 0
  linarith only [hs]

/-- The torque is the negative first variation of the actual phase potential. -/
theorem hasDerivAt_ccmWeilFinitePhaseEnergy_variation (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => ccmWeilFinitePhaseEnergy a u (fun i => theta i + t * v i))
      (-(∑ i, ccmWeilFinitePhaseTorque a u theta i * v i)) 0 := by
  let A := fun i j => ccmWeilRealPolar a (u i) (u j) * Real.sin (theta i - theta j)
  have hd (i j : ι) : HasDerivAt
      (fun t : ℝ => ccmWeilRealPolar a (u i) (u j) *
        Real.cos ((theta i + t * v i) - (theta j + t * v j)))
      (-(A i j * (v i - v j))) 0 := by
    have hi := ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (theta i)
    have hj := ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (theta j)
    convert! (hi.sub hj).cos.const_mul (ccmWeilRealPolar a (u i) (u j)) using 1
    simp only [A, Pi.sub_apply, id_eq, zero_mul, add_zero, one_mul]
    ring
  have hs : (∑ i, ∑ j, A i j * v j) = -(∑ i, ∑ j, A i j * v i) := by
    calc
      _ = ∑ i, ∑ j, A j i * v i := Finset.sum_comm
      _ = ∑ i, ∑ j, -(A i j * v i) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [show A j i = -A i j from phase_interaction_skew a u theta i j]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have he : (∑ i, ∑ j, -(A i j * (v i - v j))) =
      -(∑ i, ccmWeilFinitePhaseTorque a u theta i * v i) := by
    simp only [mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    rw [hs]
    unfold ccmWeilFinitePhaseTorque
    simp only [Finset.mul_sum, Finset.sum_mul]
    change _ = -(∑ i, ∑ j, 2 * A i j * v i)
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  simp_rw [ccmWeilFinitePhaseEnergy_eq]
  rw [← he]
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hd i j

def ccmWeilFinitePhaseLagrangian (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta v : ι → ℝ) : ℝ :=
  (∑ i, v i ^ 2) / 2 - ccmWeilFinitePhaseEnergy a u theta

theorem ccmWeilFinitePhaseLagrangian_common_shift (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta v : ι → ℝ) (t : ℝ) :
    ccmWeilFinitePhaseLagrangian a u (fun i => theta i + t) v =
      ccmWeilFinitePhaseLagrangian a u theta v := by
  simp only [ccmWeilFinitePhaseLagrangian, ccmWeilFinitePhaseEnergy_common_shift]

/-- The momentum paired with the common-phase generator is exactly the sum of velocities. -/
theorem hasDerivAt_ccmWeilFinitePhaseLagrangian_velocity_shift (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta v : ι → ℝ) :
    HasDerivAt (fun t : ℝ => ccmWeilFinitePhaseLagrangian a u theta (fun i => v i + t))
      (∑ i, v i) 0 := by
  have hi (i : ι) : HasDerivAt (fun t : ℝ => (v i + t) ^ 2) (2 * v i) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_add (v i)).pow 2 using 1
    simp
  have h := ((HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hi i).div_const 2).sub_const
    (ccmWeilFinitePhaseEnergy a u theta)
  convert! h using 1
  rw [← Finset.mul_sum]
  ring

theorem ccmWeilFinitePhase_total_momentum_conserved (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (q : ι → ℝ → ℝ)
    (hq : ∀ i t, HasDerivAt (deriv (q i)) (ccmWeilFinitePhaseTorque a u (fun j => q j t) i) t)
    (s t : ℝ) : (∑ i, deriv (q i) s) = ∑ i, deriv (q i) t := by
  have hd (t : ℝ) : HasDerivAt (fun s => ∑ i, deriv (q i) s) 0 t := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hq i t
    rwa [ccmWeilFinitePhaseTorque_sum_zero] at h
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s t

/-- A global common rotation satisfies all Newton equations as conclusions. -/
theorem ccmWeilFinitePhase_uniform_rotation_newton (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (c omega t : ℝ) (i : ι) :
    HasDerivAt (deriv (ccmWeilTriangleUniformPhase c omega))
      (ccmWeilFinitePhaseTorque a u (fun _ => ccmWeilTriangleUniformPhase c omega t) i) t := by
  have hv : deriv (ccmWeilTriangleUniformPhase c omega) = fun _ => omega :=
    funext fun s => (hasDerivAt_ccmWeilTriangleUniformPhase c omega s).deriv
  rw [hv]
  simp only [ccmWeilFinitePhaseTorque, sub_self, Real.sin_zero, mul_zero, Finset.sum_const_zero]
  exact hasDerivAt_const t omega

theorem ccmWeilFinitePhase_uniform_rotation_charges (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (c omega t : ℝ) :
    let q := ccmWeilTriangleUniformPhase c omega
    (∑ _i : ι, deriv q t) = Fintype.card ι * omega ∧
      (∑ _i : ι, deriv q t ^ 2) / 2 + ccmWeilFinitePhaseEnergy a u (fun _ => q t) =
        Fintype.card ι * omega ^ 2 / 2 + ccmWeilFinitePhaseEnergy a u (fun _ => c) := by
  dsimp only
  rw [(hasDerivAt_ccmWeilTriangleUniformPhase c omega t).deriv]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ccmWeilTriangleUniformPhase,
    ccmWeilFinitePhaseEnergy_common_shift, and_self]

theorem finiteSignedSeparateLower_cos_sin [DecidableEq ι] (M : ι → ι → ℝ) (theta : ι → ℝ) :
    finiteSignedSeparateLower M (fun i => Real.cos (theta i)) +
      finiteSignedSeparateLower M (fun i => Real.sin (theta i)) =
      finiteSignedSeparateLower M (fun _ => 1) := by
  unfold finiteSignedSeparateLower
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  linear_combination (M i i - ∑ j, |finiteSignedOffDiagonal M i j|) * Real.sin_sq_add_cos_sq (theta i)

def ccmWeilFinitePhaseFloor [DecidableEq ι] (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) : ℝ :=
  finiteSignedSeparateLower (fun i j => ccmWeilRealPolar a (u i) (u j)) (fun _ => 1)

/-- The group correction retains the squared magnitude of the total phase vector. -/
theorem ccmWeilFinitePhase_clique_lower [DecidableEq ι] (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (theta : ι → ℝ) :
    ccmWeilFinitePhaseFloor a u + finiteSignedCliqueGain (fun i j => ccmWeilRealPolar a (u i) (u j)) *
      ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 2) +
        (∑ i, Real.cos (theta i)) ^ 2 + (∑ i, Real.sin (theta i)) ^ 2) ≤
      ccmWeilFinitePhaseEnergy a u theta := by
  let M := fun i j => ccmWeilRealPolar a (u i) (u j)
  have hc := finiteSignedClique_lower M (fun i j => ccmWeilRealPolar_symm a (u i) (u j))
    (fun i => Real.cos (theta i))
  have hs := finiteSignedClique_lower M (fun i j => ccmWeilRealPolar_symm a (u i) (u j))
    (fun i => Real.sin (theta i))
  rw [← ccmRestrictedWeilSourceQuadratic_real_sum] at hc hs
  have hl := finiteSignedSeparateLower_cos_sin M theta
  have hmass : (∑ i, Real.cos (theta i) ^ 2) + (∑ i, Real.sin (theta i) ^ 2) = Fintype.card ι := by
    rw [← Finset.sum_add_distrib]
    have he (i : ι) : Real.cos (theta i) ^ 2 + Real.sin (theta i) ^ 2 = 1 := by
      linarith only [Real.sin_sq_add_cos_sq (theta i)]
    simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hm := congrArg (fun t : ℝ => finiteSignedCliqueGain M * ((Fintype.card ι : ℝ) - 2) * t) hmass
  unfold finiteSignedCliqueCorrection at hc hs
  unfold ccmWeilFinitePhaseFloor ccmWeilFinitePhaseEnergy
  change finiteSignedSeparateLower M (fun _ => 1) + finiteSignedCliqueGain M * _ ≤ _
  nlinarith only [hc, hs, hl, hm]

end RHTower
