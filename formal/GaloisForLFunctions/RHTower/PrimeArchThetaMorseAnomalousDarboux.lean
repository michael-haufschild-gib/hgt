import GaloisForLFunctions.RHTower.PrimeArchThetaMorseGroundState

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A polynomial test vector dressing the exact Morse zero mode. -/
def thetaCuspMorseDressedPolynomial
    (A : ℝ) (n : ℕ) (P : ℝ[X]) (x : ℝ) : ℝ :=
  P.eval x * thetaCuspMorseZeroMode A n x

/-- Pointwise lower Morse Hamiltonian action. -/
def thetaCuspMorseHamiltonianMinus
    (A : ℝ) (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv f) x + thetaCuspMorsePotentialMinus A n x * f x

theorem hasDerivAt_thetaCuspMorseDressedPolynomial
    (A : ℝ) (n : ℕ) (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (thetaCuspMorseDressedPolynomial A n P)
      (P.derivative.eval x * thetaCuspMorseZeroMode A n x -
        thetaCuspMorseSuperpotential A n x *
          thetaCuspMorseDressedPolynomial A n P x) x := by
  have hP := P.hasDerivAt x
  have hψ := hasDerivAt_thetaCuspMorseZeroMode A n x
  change HasDerivAt
    (fun y : ℝ => P.eval y * thetaCuspMorseZeroMode A n y)
    (P.derivative.eval x * thetaCuspMorseZeroMode A n x -
      thetaCuspMorseSuperpotential A n x *
        (P.eval x * thetaCuspMorseZeroMode A n x)) x
  exact (hP.mul hψ).congr_deriv
    (g' := P.derivative.eval x * thetaCuspMorseZeroMode A n x -
      thetaCuspMorseSuperpotential A n x *
        (P.eval x * thetaCuspMorseZeroMode A n x)) (by ring)

theorem thetaCuspMorse_supercharge_dressedPolynomial
    (A : ℝ) (n : ℕ) (P : ℝ[X]) (x : ℝ) :
    deriv (thetaCuspMorseDressedPolynomial A n P) x +
        thetaCuspMorseSuperpotential A n x *
          thetaCuspMorseDressedPolynomial A n P x =
      P.derivative.eval x * thetaCuspMorseZeroMode A n x := by
  rw [(hasDerivAt_thetaCuspMorseDressedPolynomial A n P x).deriv]
  ring

theorem thetaCuspMorse_robinDefect_dressedPolynomial
    (A : ℝ) (n : ℕ) (P : ℝ[X]) :
    deriv (thetaCuspMorseDressedPolynomial A n P) 0 +
        thetaCuspMorseSuperpotential A n 0 *
          thetaCuspMorseDressedPolynomial A n P 0 =
      P.derivative.eval 0 * thetaCuspMorseZeroMode A n 0 := by
  exact thetaCuspMorse_supercharge_dressedPolynomial A n P 0

theorem thetaCuspMorseZeroMode_pos
    (A : ℝ) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    0 < thetaCuspMorseZeroMode A n x := by
  unfold thetaCuspMorseZeroMode
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem thetaCuspMorse_robinDefect_eq_zero_iff
    (A : ℝ) {n : ℕ} (hn : 0 < n) (P : ℝ[X]) :
    deriv (thetaCuspMorseDressedPolynomial A n P) 0 +
          thetaCuspMorseSuperpotential A n 0 *
            thetaCuspMorseDressedPolynomial A n P 0 = 0 ↔
      P.derivative.eval 0 = 0 := by
  rw [thetaCuspMorse_robinDefect_dressedPolynomial]
  exact mul_eq_zero.trans (or_iff_left (thetaCuspMorseZeroMode_pos A hn 0).ne')

theorem thetaCuspMorseGroundState_robin (n : ℕ) :
    deriv (thetaCuspMorseGroundState n) 0 +
        thetaCuspMorseSuperpotential (5 / 4 : ℝ) n 0 *
          thetaCuspMorseGroundState n 0 = 0 := by
  rw [(hasDerivAt_thetaCuspMorseGroundState n 0).deriv]
  ring

theorem thetaCuspMorseGroundState_zero_sq (n : ℕ) :
    thetaCuspMorseGroundState n 0 ^ 2 =
      (n : ℝ) ^ 2 * Real.exp (-Real.pi * (n : ℝ) ^ 2) := by
  rw [thetaCuspMorseGroundState_sq, thetaCuspLiouvilleGibbsAtom_zero]

theorem hasDerivAt_deriv_thetaCuspMorseDressedPolynomial
    (A : ℝ) (n : ℕ) (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (deriv (thetaCuspMorseDressedPolynomial A n P))
      (P.derivative.derivative.eval x * thetaCuspMorseZeroMode A n x -
        2 * thetaCuspMorseSuperpotential A n x *
          P.derivative.eval x * thetaCuspMorseZeroMode A n x +
        thetaCuspMorsePotentialMinus A n x *
          thetaCuspMorseDressedPolynomial A n P x) x := by
  have hψ := hasDerivAt_thetaCuspMorseZeroMode A n x
  have hP' := P.derivative.hasDerivAt x
  have hW := hasDerivAt_thetaCuspMorseSuperpotential A n x
  have hdress := hasDerivAt_thetaCuspMorseDressedPolynomial A n P x
  have hfirst : HasDerivAt
      (fun y : ℝ => P.derivative.eval y * thetaCuspMorseZeroMode A n y)
      (P.derivative.derivative.eval x * thetaCuspMorseZeroMode A n x +
        P.derivative.eval x *
          (-thetaCuspMorseSuperpotential A n x *
            thetaCuspMorseZeroMode A n x)) x := hP'.mul hψ
  have hsecond : HasDerivAt
      (fun y : ℝ => thetaCuspMorseSuperpotential A n y *
        thetaCuspMorseDressedPolynomial A n P y)
      (2 * thetaCuspMorseScale n x *
          thetaCuspMorseDressedPolynomial A n P x +
        thetaCuspMorseSuperpotential A n x *
          (P.derivative.eval x * thetaCuspMorseZeroMode A n x -
            thetaCuspMorseSuperpotential A n x *
              thetaCuspMorseDressedPolynomial A n P x)) x := hW.mul hdress
  rw [show deriv (thetaCuspMorseDressedPolynomial A n P) =
      fun y : ℝ =>
        P.derivative.eval y * thetaCuspMorseZeroMode A n y -
          thetaCuspMorseSuperpotential A n y *
            thetaCuspMorseDressedPolynomial A n P y by
    funext y
    exact (hasDerivAt_thetaCuspMorseDressedPolynomial A n P y).deriv]
  exact (hfirst.sub hsecond).congr_deriv
    (g' := P.derivative.derivative.eval x * thetaCuspMorseZeroMode A n x -
      2 * thetaCuspMorseSuperpotential A n x *
        P.derivative.eval x * thetaCuspMorseZeroMode A n x +
      thetaCuspMorsePotentialMinus A n x *
        thetaCuspMorseDressedPolynomial A n P x) (by
      simp only [thetaCuspMorsePotentialMinus]
      ring)

theorem secondDeriv_thetaCuspMorseDressedPolynomial
    (A : ℝ) (n : ℕ) (P : ℝ[X]) (x : ℝ) :
    deriv (deriv (thetaCuspMorseDressedPolynomial A n P)) x =
      P.derivative.derivative.eval x * thetaCuspMorseZeroMode A n x -
        2 * thetaCuspMorseSuperpotential A n x *
          P.derivative.eval x * thetaCuspMorseZeroMode A n x +
        thetaCuspMorsePotentialMinus A n x *
          thetaCuspMorseDressedPolynomial A n P x := by
  exact (hasDerivAt_deriv_thetaCuspMorseDressedPolynomial A n P x).deriv

/-- Exact Darboux/Doob ground-state transform for every polynomial test vector. -/
theorem thetaCuspMorseHamiltonianMinus_dressedPolynomial
    (A : ℝ) (n : ℕ) (P : ℝ[X]) (x : ℝ) :
    thetaCuspMorseHamiltonianMinus A n
        (thetaCuspMorseDressedPolynomial A n P) x =
      (-P.derivative.derivative.eval x +
          2 * thetaCuspMorseSuperpotential A n x * P.derivative.eval x) *
        thetaCuspMorseZeroMode A n x := by
  rw [thetaCuspMorseHamiltonianMinus,
    secondDeriv_thetaCuspMorseDressedPolynomial]
  simp only [thetaCuspMorseDressedPolynomial]
  ring

/-- The theta source Ward identity as an exact Hamiltonian matrix-value law. -/
theorem derivative_eval_mul_thetaCuspSourceTerm_eq_morseHamiltonianWard
    (P : ℝ[X]) (n : ℕ) (x : ℝ) :
    P.derivative.eval x * thetaCuspSourceTerm x n =
      2 * Real.pi *
        (thetaCuspMorseGroundState n x *
            thetaCuspMorseHamiltonianMinus (5 / 4 : ℝ) n
              (thetaCuspMorseDressedPolynomial (5 / 4 : ℝ) n P) x +
          (P.derivative.derivative.eval x -
              (1 / 2 : ℝ) * P.derivative.eval x) *
            thetaCuspMorseGroundState n x ^ 2) := by
  rw [thetaCuspSourceTerm_eq_morseBornObservable,
    thetaCuspMorseHamiltonianMinus_dressedPolynomial]
  simp only [thetaCuspMorseGroundState]
  ring

/-- The normalized odd monomial whose derivative is the even moment test x^(2j). -/
def thetaCuspMorseMomentTestPolynomial (j : ℕ) : ℝ[X] :=
  C (((2 * j + 1 : ℕ) : ℝ)⁻¹) * X ^ (2 * j + 1)

theorem thetaCuspMorseMomentTestPolynomial_derivative_eval
    (j : ℕ) (x : ℝ) :
    (thetaCuspMorseMomentTestPolynomial j).derivative.eval x = x ^ (2 * j) := by
  simp only [thetaCuspMorseMomentTestPolynomial, derivative_mul, derivative_C,
    zero_mul, derivative_X_pow, zero_add, eval_mul, eval_C, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, eval_pow, eval_X]
  have hk : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
  norm_num only [Nat.cast_one]
  rw [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
  simp

theorem thetaCuspMorseMomentTestPolynomial_secondDerivative_eval
    (j : ℕ) (x : ℝ) :
    (thetaCuspMorseMomentTestPolynomial j).derivative.derivative.eval x =
      ((2 * j : ℕ) : ℝ) * x ^ (2 * j - 1) := by
  have hP := (thetaCuspMorseMomentTestPolynomial j).derivative.hasDerivAt x
  have hfun :
      (fun y : ℝ =>
        (thetaCuspMorseMomentTestPolynomial j).derivative.eval y) =
        fun y : ℝ => y ^ (2 * j) := by
    funext y
    exact thetaCuspMorseMomentTestPolynomial_derivative_eval j y
  rw [hfun] at hP
  have hpow := (hasDerivAt_id x).pow (2 * j)
  simpa only [id_eq, one_mul, mul_one] using hP.unique hpow

theorem thetaCuspMorseMomentTestPolynomial_robinDefect
    (j n : ℕ) :
    deriv (thetaCuspMorseDressedPolynomial (5 / 4 : ℝ) n
          (thetaCuspMorseMomentTestPolynomial j)) 0 +
        thetaCuspMorseSuperpotential (5 / 4 : ℝ) n 0 *
          thetaCuspMorseDressedPolynomial (5 / 4 : ℝ) n
            (thetaCuspMorseMomentTestPolynomial j) 0 =
      if j = 0 then thetaCuspMorseGroundState n 0 else 0 := by
  rw [thetaCuspMorse_robinDefect_dressedPolynomial,
    thetaCuspMorseMomentTestPolynomial_derivative_eval]
  cases j with
  | zero => simp [thetaCuspMorseGroundState]
  | succ j => simp

/-- The Darboux Hamiltonian density attached to the `2j`-th theta Born moment. -/
def thetaCuspMorseHamiltonianWardDensity (j n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspMorseGroundState n x *
      thetaCuspMorseHamiltonianMinus (5 / 4 : ℝ) n
        (thetaCuspMorseDressedPolynomial (5 / 4 : ℝ) n
          (thetaCuspMorseMomentTestPolynomial j)) x +
    (((2 * j : ℕ) : ℝ) * x ^ (2 * j - 1) -
        (1 / 2 : ℝ) * x ^ (2 * j)) *
      thetaCuspMorseGroundState n x ^ 2

/-- Every theta Born-moment integrand is an anomalous half-line Hamiltonian matrix value. -/
theorem pow_mul_thetaCuspSourceTerm_eq_morseHamiltonianWard
    (j n : ℕ) (x : ℝ) :
    x ^ (2 * j) * thetaCuspSourceTerm x n =
      2 * Real.pi * thetaCuspMorseHamiltonianWardDensity j n x := by
  simp only [thetaCuspMorseHamiltonianWardDensity]
  simpa only [thetaCuspMorseMomentTestPolynomial_derivative_eval,
    thetaCuspMorseMomentTestPolynomial_secondDerivative_eval] using
    derivative_eval_mul_thetaCuspSourceTerm_eq_morseHamiltonianWard
      (thetaCuspMorseMomentTestPolynomial j) n x

/-- Existing atom moments are exactly integrated anomalous Hamiltonian Ward densities. -/
theorem thetaCuspAtomRawEvenMoment_eq_morseHamiltonianWard
    (j n : ℕ) :
    thetaCuspAtomRawEvenMoment j n =
      4 * Real.pi *
        ∫ x : ℝ in Ioi 0, thetaCuspMorseHamiltonianWardDensity j n x := by
  rw [thetaCuspAtomRawEvenMoment]
  rw [show (fun x : ℝ => x ^ (2 * j) * thetaCuspSourceTerm x n) =
      fun x : ℝ => 2 * Real.pi * thetaCuspMorseHamiltonianWardDensity j n x by
    funext x
    exact pow_mul_thetaCuspSourceTerm_eq_morseHamiltonianWard j n x]
  rw [integral_const_mul]
  ring

/-- The full theta-cusp raw moment is the sum of its exact anomalous Hamiltonian Ward values. -/
theorem thetaCuspRawEvenMoment_eq_tsum_morseHamiltonianWard (j : ℕ) :
    thetaCuspRawEvenMoment j =
      ∑' n : ℕ,
        4 * Real.pi *
          ∫ x : ℝ in Ioi 0, thetaCuspMorseHamiltonianWardDensity j n x := by
  rw [thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment]
  apply tsum_congr
  intro n
  exact thetaCuspAtomRawEvenMoment_eq_morseHamiltonianWard j n

/-- Every existing Morse Born moment is the integrated anomalous Hamiltonian Ward density. -/
theorem thetaCuspMorseBornMoment_eq_morseHamiltonianWard
    (j n : ℕ) :
    thetaCuspMorseBornMoment j n =
      2 * ∫ x : ℝ in Ioi 0, thetaCuspMorseHamiltonianWardDensity j n x := by
  have hborn := thetaCuspAtomRawEvenMoment_eq_morseBornMoment j n
  have hward := thetaCuspAtomRawEvenMoment_eq_morseHamiltonianWard j n
  nlinarith [Real.pi_pos]

/-- Direct Hamiltonian-Ward replacement for the two remaining Born-moment
hypotheses in the linear prime-archimedean Hankel consumer. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_morseHamiltonianWard
    (hupper :
      14 * ((3005 / 2997 : ℝ) *
          (2 * ∫ x : ℝ in Ioi 0,
            thetaCuspMorseHamiltonianWardDensity 2 1 x)) ^ 2 ≤
        9 *
          (2 * ∫ x : ℝ in Ioi 0,
            thetaCuspMorseHamiltonianWardDensity 1 1 x) *
          (2 * ∫ x : ℝ in Ioi 0,
            thetaCuspMorseHamiltonianWardDensity 3 1 x))
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          (2 * ∫ x : ℝ in Ioi 0,
            thetaCuspMorseHamiltonianWardDensity 0 1 x)) *
          ((3005 / 2997 : ℝ) *
            (2 * ∫ x : ℝ in Ioi 0,
              thetaCuspMorseHamiltonianWardDensity 2 1 x)) ≤
        45 *
          (2 * ∫ x : ℝ in Ioi 0,
            thetaCuspMorseHamiltonianWardDensity 1 1 x) ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  apply forall_primeArchSourceTraceHankel_linear_nonneg_of_morseBorn
  · simpa only [thetaCuspMorseBornMoment_eq_morseHamiltonianWard] using hupper
  · simpa only [thetaCuspMorseBornMoment_eq_morseHamiltonianWard] using hrelaxed

end
end RHTower
