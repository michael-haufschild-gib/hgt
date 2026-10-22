import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureIntrinsicBalance

open Real Set Filter Topology

namespace RHTower

noncomputable section

private theorem secondDeriv_nonneg_of_isLocalMin
    {f : ℝ → ℝ} {x : ℝ} (hmin : IsLocalMin f x)
    (hcont : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra h
  have hsecondNeg : deriv (deriv f) x < 0 := lt_of_not_ge h
  have hfirstZero : deriv f x = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax f x :=
    isLocalMax_of_deriv_deriv_neg hsecondNeg hfirstZero hcont
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmax, hmin] with y hyMax hyMin
    exact le_antisymm hyMax hyMin
  have hderivEq : deriv f =ᶠ[𝓝 x] deriv (fun _ => f x) := heq.deriv
  have hsecondZero :
      deriv (deriv f) x = deriv (deriv (fun _ => f x)) x :=
    hderivEq.deriv_eq
  have hsecondZero' : deriv (deriv f) x = 0 := by
    simpa using hsecondZero
  linarith

/-- First derivative of intrinsic C5 after cancellation of one positive drop factor. -/
def thetaCuspReflectedSourceFifthRootCurvatureIntrinsicVelocity
    (u t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop u t
  let D := thetaCuspReflectedSourceDecayFlux u t
  let N := thetaCuspReflectedSourceFifthRootCurvatureNumerator u t
  let V := thetaCuspReflectedSourceFifthRootCurvatureVelocity u t
  (V * A - 2 * N * D) / A ^ (3 : ℕ)

/-- Second derivative of intrinsic C5 at an intrinsic stationary point. -/
def thetaCuspReflectedSourceFifthRootCurvatureIntrinsicAcceleration
    (u t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop u t
  let D := thetaCuspReflectedSourceDecayFlux u t
  let J := thetaCuspReflectedSourceDecayFluxCurvature u t
  let N := thetaCuspReflectedSourceFifthRootCurvatureNumerator u t
  let Acc := thetaCuspReflectedSourceFifthRootCurvatureAcceleration u t
  (Acc * A ^ (2 : ℕ) - 2 * N * (D ^ (2 : ℕ) + A * J)) / A ^ (4 : ℕ)

/-- Division-free second-order numerator of intrinsic C5. -/
def thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderNumerator
    (u t : ℝ) : ℝ :=
  let A := thetaCuspReflectedSourceFirstDrop u t
  let D := thetaCuspReflectedSourceDecayFlux u t
  let J := thetaCuspReflectedSourceDecayFluxCurvature u t
  let N := thetaCuspReflectedSourceFifthRootCurvatureNumerator u t
  let Acc := thetaCuspReflectedSourceFifthRootCurvatureAcceleration u t
  Acc * A ^ (2 : ℕ) - 2 * N * (D ^ (2 : ℕ) + A * J)

theorem thetaCuspReflectedSourceFifthRootCurvatureIntrinsicAcceleration_eq_secondOrder_div
    (u t : ℝ) :
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicAcceleration u t =
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderNumerator u t /
        thetaCuspReflectedSourceFirstDrop u t ^ (4 : ℕ) := by
  rfl

theorem deriv_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_eq_velocity
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    deriv (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u) t =
      thetaCuspReflectedSourceFifthRootCurvatureIntrinsicVelocity u t := by
  rw [(hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u ht).deriv]
  unfold thetaCuspReflectedSourceFifthRootCurvatureIntrinsicVelocity
  have hA := (thetaCuspReflectedSourceFirstDrop_pos u ht).ne'
  field_simp [hA]

theorem hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicVelocity_of_stationary
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hstationary :
      thetaCuspReflectedSourceFifthRootCurvatureVelocity u t *
          thetaCuspReflectedSourceFirstDrop u t =
        2 * thetaCuspReflectedSourceFifthRootCurvatureNumerator u t *
          thetaCuspReflectedSourceDecayFlux u t) :
    HasDerivAt (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicVelocity u)
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicAcceleration u t) t := by
  let A : ℝ → ℝ := thetaCuspReflectedSourceFirstDrop u
  let D : ℝ → ℝ := thetaCuspReflectedSourceDecayFlux u
  let J : ℝ → ℝ := thetaCuspReflectedSourceDecayFluxCurvature u
  let N : ℝ → ℝ := thetaCuspReflectedSourceFifthRootCurvatureNumerator u
  let V : ℝ → ℝ := thetaCuspReflectedSourceFifthRootCurvatureVelocity u
  let Acc : ℝ → ℝ := thetaCuspReflectedSourceFifthRootCurvatureAcceleration u
  have hA : HasDerivAt A (D t) t := by
    simpa only [A, D] using hasDerivAt_thetaCuspReflectedSourceFirstDrop u t
  have hD : HasDerivAt D (J t) t := by
    simpa only [D, J] using hasDerivAt_thetaCuspReflectedSourceDecayFlux u t
  have hN : HasDerivAt N (V t) t := by
    simpa only [N, V] using
      hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureNumerator u t
  have hV : HasDerivAt V (Acc t) t := by
    simpa only [V, Acc] using
      hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureVelocity u t
  have hnum := (hV.mul hA).sub (((hN.mul hD).const_mul 2))
  have hden := hA.pow 3
  have hraw := hnum.div hden
    (pow_ne_zero 3 (thetaCuspReflectedSourceFirstDrop_pos u ht).ne')
  have hfun :
      (V * A - fun y => 2 * (N * D) y) / A ^ (3 : ℕ) =
        fun s => (V s * A s - 2 * N s * D s) / A s ^ (3 : ℕ) := by
    funext s
    simp only [Pi.div_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    ring
  rw [hfun] at hraw
  unfold thetaCuspReflectedSourceFifthRootCurvatureIntrinsicVelocity
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicAcceleration
  dsimp only [A, D, J, N, V, Acc] at hraw ⊢
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Nat.cast_ofNat,
    Nat.reduceSub] at hraw
  refine hraw.congr_deriv ?_
  have hAne := (thetaCuspReflectedSourceFirstDrop_pos u ht).ne'
  field_simp [hAne]
  linear_combination
    -4 * thetaCuspReflectedSourceDecayFlux u t * hstationary

theorem thetaCuspReflectedSourceFifthRootCurvatureIntrinsicAcceleration_nonneg_of_isLocalMin
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hmin : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u) t) :
    0 ≤ thetaCuspReflectedSourceFifthRootCurvatureIntrinsicAcceleration u t := by
  have hstationary :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_isLocalMin_velocity
      u ht hmin
  have hvelDeriv :=
    hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicVelocity_of_stationary
      u ht hstationary
  have hevent :
      deriv (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u) =ᶠ[𝓝 t]
        thetaCuspReflectedSourceFifthRootCurvatureIntrinsicVelocity u := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact deriv_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance_eq_velocity u hs
  have hsecond :
      0 ≤ deriv
        (deriv (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u)) t :=
    secondDeriv_nonneg_of_isLocalMin hmin
      (hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u ht).continuousAt
  rw [hevent.deriv_eq, hvelDeriv.deriv] at hsecond
  exact hsecond

theorem
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderNumerator_nonneg_of_isLocalMin
    (u : ℝ) {t : ℝ} (ht : 0 < t)
    (hmin : IsLocalMin
      (thetaCuspReflectedSourceFifthRootCurvatureIntrinsicBalance u) t) :
    0 ≤ thetaCuspReflectedSourceFifthRootCurvatureIntrinsicSecondOrderNumerator u t := by
  have hacc :=
    thetaCuspReflectedSourceFifthRootCurvatureIntrinsicAcceleration_nonneg_of_isLocalMin
      u ht hmin
  rw [thetaCuspReflectedSourceFifthRootCurvatureIntrinsicAcceleration_eq_secondOrder_div]
    at hacc
  rcases div_nonneg_iff.mp hacc with hgood | hbad
  · exact hgood.1
  · have hden := pow_pos (thetaCuspReflectedSourceFirstDrop_pos u ht) 4
    linarith

end

end RHTower
