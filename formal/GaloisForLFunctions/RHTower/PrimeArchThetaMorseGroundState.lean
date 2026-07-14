import GaloisForLFunctions.RHTower.PrimeArchThetaLiouvilleWard

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exponential Morse coordinate carried by one theta-cusp atom. -/
def thetaCuspMorseScale (n : ℕ) (x : ℝ) : ℝ :=
  Real.pi * ((n : ℝ) * Real.exp x) ^ 2

/-- Morse superpotential with parameter `A`. -/
def thetaCuspMorseSuperpotential (A : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspMorseScale n x - A

/-- The `A`-dependent supersymmetric Morse zero mode. -/
def thetaCuspMorseZeroMode (A : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * Real.exp (A * x) *
    Real.exp (-thetaCuspMorseScale n x / 2)

/-- The exact `A = 5/4` zero mode underlying the theta atom. -/
def thetaCuspMorseGroundState (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspMorseZeroMode (5 / 4 : ℝ) n x

/-- The `A`-dependent lower supersymmetric Morse potential. -/
def thetaCuspMorsePotentialMinus (A : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspMorseSuperpotential A n x ^ 2 - 2 * thetaCuspMorseScale n x

/-- The `A`-dependent partner supersymmetric Morse potential. -/
def thetaCuspMorsePotentialPlus (A : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspMorseSuperpotential A n x ^ 2 + 2 * thetaCuspMorseScale n x

theorem hasDerivAt_thetaCuspMorseScale (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspMorseScale n) (2 * thetaCuspMorseScale n x) x := by
  have hu : HasDerivAt (fun y : ℝ => (n : ℝ) * Real.exp y)
      ((n : ℝ) * Real.exp x) x :=
    (Real.hasDerivAt_exp x).const_mul (n : ℝ)
  convert (hu.pow 2).const_mul Real.pi using 1
  all_goals simp only [thetaCuspMorseScale]
  all_goals ring

theorem hasDerivAt_thetaCuspMorseSuperpotential
    (A : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspMorseSuperpotential A n)
      (2 * thetaCuspMorseScale n x) x := by
  exact (hasDerivAt_thetaCuspMorseScale n x).sub_const A

theorem hasDerivAt_thetaCuspMorseZeroMode (A : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspMorseZeroMode A n)
      (-thetaCuspMorseSuperpotential A n x *
        thetaCuspMorseZeroMode A n x) x := by
  have hscale := hasDerivAt_thetaCuspMorseScale n x
  have hlin : HasDerivAt (fun y : ℝ => A * y) A x :=
    by simpa using (hasDerivAt_id x).const_mul A
  have hA : HasDerivAt (fun y : ℝ => Real.exp (A * y))
      (A * Real.exp (A * x)) x := by
    convert (Real.hasDerivAt_exp (A * x)).comp x hlin using 1
    all_goals ring
  have hneg : HasDerivAt (fun y : ℝ => -thetaCuspMorseScale n y / 2)
      (-thetaCuspMorseScale n x) x := by
    convert hscale.neg.div_const 2 using 1
    all_goals ring
  have hB : HasDerivAt
      (fun y : ℝ => Real.exp (-thetaCuspMorseScale n y / 2))
      (-thetaCuspMorseScale n x *
        Real.exp (-thetaCuspMorseScale n x / 2)) x := by
    convert (Real.hasDerivAt_exp (-thetaCuspMorseScale n x / 2)).comp x hneg using 1
    all_goals ring
  convert (hA.const_mul (n : ℝ)).mul hB using 1
  all_goals simp only [thetaCuspMorseZeroMode, thetaCuspMorseSuperpotential]
  all_goals ring

theorem hasDerivAt_thetaCuspMorseGroundState (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspMorseGroundState n)
      (-thetaCuspMorseSuperpotential (5 / 4 : ℝ) n x *
        thetaCuspMorseGroundState n x) x := by
  exact hasDerivAt_thetaCuspMorseZeroMode (5 / 4 : ℝ) n x

theorem thetaCuspMorseGroundState_sq (n : ℕ) (x : ℝ) :
    thetaCuspMorseGroundState n x ^ 2 =
      thetaCuspLiouvilleGibbsAtom n x := by
  have hA : Real.exp ((5 / 4 : ℝ) * x) ^ 2 =
      Real.exp ((5 / 2 : ℝ) * x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hB : Real.exp (-thetaCuspMorseScale n x / 2) ^ 2 =
      Real.exp (-thetaCuspMorseScale n x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hxexp : Real.exp (x / 2) * Real.exp x * Real.exp x =
      Real.exp ((5 / 2 : ℝ) * x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    thetaCuspMorseGroundState n x ^ 2 =
        (n : ℝ) ^ 2 * Real.exp ((5 / 4 : ℝ) * x) ^ 2 *
          Real.exp (-thetaCuspMorseScale n x / 2) ^ 2 := by
            simp only [thetaCuspMorseGroundState]
            simp only [thetaCuspMorseZeroMode]
            ring
    _ = (n : ℝ) ^ 2 * Real.exp ((5 / 2 : ℝ) * x) *
          Real.exp (-thetaCuspMorseScale n x) := by rw [hA, hB]
    _ = thetaCuspLiouvilleGibbsAtom n x := by
      rw [thetaCuspLiouvilleGibbsAtom_apply]
      simp only [thetaCuspMorseScale]
      rw [show Real.exp (x / 2) * ((n : ℝ) * Real.exp x) ^ 2 =
          (n : ℝ) ^ 2 * Real.exp ((5 / 2 : ℝ) * x) by
            calc
              Real.exp (x / 2) * ((n : ℝ) * Real.exp x) ^ 2 =
                  (n : ℝ) ^ 2 *
                    (Real.exp (x / 2) * Real.exp x * Real.exp x) := by ring
              _ = (n : ℝ) ^ 2 * Real.exp ((5 / 2 : ℝ) * x) := by rw [hxexp]]
      congr 1
      ring

theorem hasDerivAt_neg_morseSuperpotential_mul_zeroMode
    (A : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
      -thetaCuspMorseSuperpotential A n y * thetaCuspMorseZeroMode A n y)
      (thetaCuspMorsePotentialMinus A n x * thetaCuspMorseZeroMode A n x) x := by
  have hW := hasDerivAt_thetaCuspMorseSuperpotential A n x
  have hψ := hasDerivAt_thetaCuspMorseZeroMode A n x
  convert hW.neg.mul hψ using 1
  all_goals simp only [thetaCuspMorsePotentialMinus, Pi.neg_apply]
  all_goals ring

theorem secondDeriv_thetaCuspMorseZeroMode (A : ℝ) (n : ℕ) (x : ℝ) :
    deriv (deriv (thetaCuspMorseZeroMode A n)) x =
      thetaCuspMorsePotentialMinus A n x * thetaCuspMorseZeroMode A n x := by
  rw [show deriv (thetaCuspMorseZeroMode A n) = fun y : ℝ =>
      -thetaCuspMorseSuperpotential A n y * thetaCuspMorseZeroMode A n y by
    funext y
    exact (hasDerivAt_thetaCuspMorseZeroMode A n y).deriv]
  exact (hasDerivAt_neg_morseSuperpotential_mul_zeroMode A n x).deriv

theorem thetaCuspMorseZeroMode_schrodinger_zero
    (A : ℝ) (n : ℕ) (x : ℝ) :
    -deriv (deriv (thetaCuspMorseZeroMode A n)) x +
        thetaCuspMorsePotentialMinus A n x * thetaCuspMorseZeroMode A n x = 0 := by
  rw [secondDeriv_thetaCuspMorseZeroMode]
  ring

theorem thetaCuspMorseGroundState_schrodinger_zero (n : ℕ) (x : ℝ) :
    -deriv (deriv (thetaCuspMorseGroundState n)) x +
        thetaCuspMorsePotentialMinus (5 / 4 : ℝ) n x *
          thetaCuspMorseGroundState n x = 0 := by
  exact thetaCuspMorseZeroMode_schrodinger_zero (5 / 4 : ℝ) n x

theorem thetaCuspMorse_shapeInvariant (A : ℝ) (n : ℕ) (x : ℝ) :
    thetaCuspMorsePotentialPlus A n x =
      thetaCuspMorsePotentialMinus (A - 2) n x + 4 * (A - 1) := by
  simp only [thetaCuspMorsePotentialPlus, thetaCuspMorsePotentialMinus,
    thetaCuspMorseSuperpotential]
  ring

theorem thetaCuspMorseScale_pi_le
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    Real.pi ≤ thetaCuspMorseScale n x := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
  have hu : (1 : ℝ) ≤ (n : ℝ) * Real.exp x := by nlinarith
  have hu2 : (1 : ℝ) ≤ ((n : ℝ) * Real.exp x) ^ 2 := by nlinarith
  simpa only [thetaCuspMorseScale, mul_one] using
    (mul_le_mul_of_nonneg_left hu2 Real.pi_pos.le)

/-- A pointwise coercive floor for the partner Hamiltonian on the theta
half-line.  This is a potential bound, not yet a spectral-gap theorem. -/
theorem thetaCuspMorsePotentialPlus_floor
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    Real.pi ^ 2 - Real.pi / 2 + 25 / 16 ≤
      thetaCuspMorsePotentialPlus (5 / 4 : ℝ) n x := by
  have ht := thetaCuspMorseScale_pi_le hn hx
  have hfactor :
      0 ≤ (thetaCuspMorseScale n x - Real.pi) *
        (thetaCuspMorseScale n x + Real.pi - 1 / 2) := by
    apply mul_nonneg (sub_nonneg.mpr ht)
    nlinarith [Real.pi_gt_three]
  simp only [thetaCuspMorsePotentialPlus, thetaCuspMorseSuperpotential]
  nlinarith

theorem thetaCuspSourceTerm_eq_morseBornObservable (n : ℕ) (x : ℝ) :
    thetaCuspSourceTerm x n =
      4 * Real.pi *
        (thetaCuspMorseSuperpotential (5 / 4 : ℝ) n x - 1 / 4) *
          thetaCuspMorseGroundState n x ^ 2 := by
  rw [thetaCuspSourceTerm_eq_liouvilleWard]
  have hfun : thetaCuspLiouvilleGibbsAtom n = fun y : ℝ =>
      thetaCuspMorseGroundState n y ^ 2 := by
    funext y
    exact (thetaCuspMorseGroundState_sq n y).symm
  rw [hfun]
  have hsq : HasDerivAt (fun y : ℝ => thetaCuspMorseGroundState n y ^ 2)
      (2 * thetaCuspMorseGroundState n x *
        (-thetaCuspMorseSuperpotential (5 / 4 : ℝ) n x *
          thetaCuspMorseGroundState n x)) x := by
    convert (hasDerivAt_thetaCuspMorseGroundState n x).pow 2 using 1
    all_goals simp only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
  rw [hsq.deriv]
  simp only [thetaCuspMorseSuperpotential]
  ring

theorem thetaCuspMorseBornObservable_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspMorseSuperpotential (5 / 4 : ℝ) n x - 1 / 4 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
  have hu : (1 : ℝ) ≤ (n : ℝ) * Real.exp x := by nlinarith
  have hu2 : (1 : ℝ) ≤ ((n : ℝ) * Real.exp x) ^ 2 := by nlinarith
  simp only [thetaCuspMorseSuperpotential, thetaCuspMorseScale]
  nlinarith [Real.pi_gt_three, Real.pi_pos,
    mul_le_mul_of_nonneg_left hu2 Real.pi_pos.le]

/-- Born moments of the positive Morse observable selected by the theta source. -/
def thetaCuspMorseBornMoment (j n : ℕ) : ℝ :=
  4 * ∫ x : ℝ in Ioi 0,
    x ^ (2 * j) *
      (thetaCuspMorseSuperpotential (5 / 4 : ℝ) n x - 1 / 4) *
        thetaCuspMorseGroundState n x ^ 2

theorem thetaCuspMorseBornMoment_nonneg (j : ℕ) {n : ℕ} (hn : 0 < n) :
    0 ≤ thetaCuspMorseBornMoment j n := by
  rw [thetaCuspMorseBornMoment]
  apply mul_nonneg (by norm_num)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg
    (mul_nonneg (pow_nonneg hx.le _) (thetaCuspMorseBornObservable_pos hn hx.le).le)
    (sq_nonneg _)

theorem thetaCuspAtomRawEvenMoment_eq_morseBornMoment
    (j n : ℕ) :
    thetaCuspAtomRawEvenMoment j n =
      2 * Real.pi * thetaCuspMorseBornMoment j n := by
  rw [thetaCuspAtomRawEvenMoment, thetaCuspMorseBornMoment]
  rw [show (fun x : ℝ => x ^ (2 * j) * thetaCuspSourceTerm x n) =
      fun x => 4 * Real.pi *
        (x ^ (2 * j) *
          (thetaCuspMorseSuperpotential (5 / 4 : ℝ) n x - 1 / 4) *
            thetaCuspMorseGroundState n x ^ 2) by
    funext x
    rw [thetaCuspSourceTerm_eq_morseBornObservable]
    ring]
  rw [integral_const_mul]
  ring

theorem thetaCuspFirstAtomWardMoment_eq_morseBornMoment (j : ℕ) :
    thetaCuspFirstAtomWardMoment j = thetaCuspMorseBornMoment j 1 := by
  have hward := thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment j
  have hborn := thetaCuspAtomRawEvenMoment_eq_morseBornMoment j 1
  nlinarith [Real.pi_pos]

/-- The all-order first-atom enclosure, rewritten as a quantum Born-moment
bound so it can feed every existing raw-moment consumer. -/
theorem thetaCuspRawEvenMoment_between_morseBornMoment (j : ℕ) :
    2 * Real.pi * thetaCuspMorseBornMoment j 1 ≤ thetaCuspRawEvenMoment j ∧
      thetaCuspRawEvenMoment j ≤
        (3005 / 2997 : ℝ) *
          (2 * Real.pi * thetaCuspMorseBornMoment j 1) := by
  simpa only [thetaCuspFirstAtomWardMoment_eq_morseBornMoment] using
    thetaCuspRawEvenMoment_between_firstAtomWardMoment j

theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_morseBorn
    (hupper :
      14 * ((3005 / 2997 : ℝ) * thetaCuspMorseBornMoment 2 1) ^ 2 ≤
        9 * thetaCuspMorseBornMoment 1 1 * thetaCuspMorseBornMoment 3 1)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) * thetaCuspMorseBornMoment 0 1) *
          ((3005 / 2997 : ℝ) * thetaCuspMorseBornMoment 2 1) ≤
        45 * thetaCuspMorseBornMoment 1 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  apply forall_primeArchSourceTraceHankel_linear_nonneg_of_liouvilleWard
  · simpa only [thetaCuspFirstAtomWardMoment_eq_morseBornMoment] using hupper
  · simpa only [thetaCuspFirstAtomWardMoment_eq_morseBornMoment] using hrelaxed

end
end RHTower
