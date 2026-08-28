import GaloisForLFunctions.HilbertMetric.SecondLevelConcavityRiccatiFifthRootNoGo

/-!
# Six-jet atom--likelihood signs do not force fifth-root curvature

The completed-theta corpus decomposes its reflected action into a first-atom action plus a
negative likelihood-interference action.  It proves positive atom and likelihood Riccati
margins, a negative mixed channel, strict atom domination of that channel, and source likelihood
orientations through order six.

This module proves that even the corresponding six-jet reflected sign architecture does not
imply C5.  The sextic action from `SecondLevelConcavityRiccatiFifthRootNoGo` admits an exact split
`q = q_atom + q_likelihood` where likelihood jets one through six are strictly negative, both
component Riccati margins are positive, the mixed channel is negative, and the atom strictly
dominates it on the whole positive half-line.

The resulting profile still has strict radial second-level concavity, globally concave
correlation angle, and positive C5 near the cusp, but C5 is negative at `sqrt (1/2)`.
Consequently the surviving completed-theta proof must use genuinely nonlocal action--jet
information; adding finitely many isolated likelihood signs through the currently formalized
sixth level cannot close the route.
-/

open Set

namespace HilbertMetric

noncomputable section

/-- Positive atom-like action in the exact Riccati sign-architecture counterexample. -/
def riccatiNoGoAtomAction (t : ℝ) : ℝ :=
  201 / 100 * t ^ 2 + 21 / 100 * t ^ 4 + 101 / 100 * t ^ 6

def riccatiNoGoAtomJetOne (t : ℝ) : ℝ :=
  201 / 50 * t + 21 / 25 * t ^ 3 + 303 / 50 * t ^ 5

def riccatiNoGoAtomJetTwo (t : ℝ) : ℝ :=
  201 / 50 + 63 / 25 * t ^ 2 + 303 / 10 * t ^ 4

def riccatiNoGoAtomJetThree (t : ℝ) : ℝ :=
  126 / 25 * t + 606 / 5 * t ^ 3

/-- Negative likelihood-like action in the exact Riccati sign-architecture counterexample. -/
def riccatiNoGoLikelihoodAction (t : ℝ) : ℝ :=
  -(t ^ 2 + t ^ 4 + t ^ 6) / 100

def riccatiNoGoLikelihoodJetOne (t : ℝ) : ℝ :=
  -t / 50 - t ^ 3 / 25 - 3 / 50 * t ^ 5

def riccatiNoGoLikelihoodJetTwo (t : ℝ) : ℝ :=
  -1 / 50 - 3 / 25 * t ^ 2 - 3 / 10 * t ^ 4

def riccatiNoGoLikelihoodJetThree (t : ℝ) : ℝ :=
  -6 / 25 * t - 6 / 5 * t ^ 3

def riccatiNoGoLikelihoodJetFour (t : ℝ) : ℝ :=
  -6 / 25 - 18 / 5 * t ^ 2

def riccatiNoGoLikelihoodJetFive (t : ℝ) : ℝ :=
  -36 / 5 * t

def riccatiNoGoLikelihoodJetSix (_t : ℝ) : ℝ :=
  -36 / 5

def riccatiNoGoAtomRiccatiMargin (t : ℝ) : ℝ :=
  2 * riccatiNoGoAtomJetOne t * riccatiNoGoAtomJetTwo t -
    riccatiNoGoAtomJetThree t

def riccatiNoGoLikelihoodRiccatiMargin (t : ℝ) : ℝ :=
  2 * riccatiNoGoLikelihoodJetOne t * riccatiNoGoLikelihoodJetTwo t -
    riccatiNoGoLikelihoodJetThree t

def riccatiNoGoAtomLikelihoodCross (t : ℝ) : ℝ :=
  2 * (riccatiNoGoAtomJetOne t * riccatiNoGoLikelihoodJetTwo t +
    riccatiNoGoLikelihoodJetOne t * riccatiNoGoAtomJetTwo t)

def riccatiNoGoAtomProfile (t : ℝ) : ℝ := Real.exp (-riccatiNoGoAtomAction t)

def riccatiNoGoLikelihoodInterference (t : ℝ) : ℝ :=
  Real.exp (-riccatiNoGoLikelihoodAction t)

theorem riccatiNoGoAction_decomposition (t : ℝ) :
    sexticGaussianAction t =
      riccatiNoGoAtomAction t + riccatiNoGoLikelihoodAction t := by
  unfold sexticGaussianAction riccatiNoGoAtomAction riccatiNoGoLikelihoodAction
  ring

theorem riccatiNoGoJetOne_decomposition (t : ℝ) :
    sexticGaussianActionOne t =
      riccatiNoGoAtomJetOne t + riccatiNoGoLikelihoodJetOne t := by
  unfold sexticGaussianActionOne riccatiNoGoAtomJetOne riccatiNoGoLikelihoodJetOne
  ring

theorem riccatiNoGoJetTwo_decomposition (t : ℝ) :
    sexticGaussianActionTwo t =
      riccatiNoGoAtomJetTwo t + riccatiNoGoLikelihoodJetTwo t := by
  unfold sexticGaussianActionTwo riccatiNoGoAtomJetTwo riccatiNoGoLikelihoodJetTwo
  ring

theorem riccatiNoGoJetThree_decomposition (t : ℝ) :
    sexticGaussianActionThree t =
      riccatiNoGoAtomJetThree t + riccatiNoGoLikelihoodJetThree t := by
  unfold sexticGaussianActionThree riccatiNoGoAtomJetThree riccatiNoGoLikelihoodJetThree
  ring

theorem hasDerivAt_riccatiNoGoLikelihoodAction (t : ℝ) :
    HasDerivAt riccatiNoGoLikelihoodAction (riccatiNoGoLikelihoodJetOne t) t := by
  unfold riccatiNoGoLikelihoodAction riccatiNoGoLikelihoodJetOne
  have hraw := ((((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).pow 4)).add
    ((hasDerivAt_id t).pow 6)).neg.div_const 100
  rw [show (fun y : ℝ => -(y ^ 2 + y ^ 4 + y ^ 6) / 100) =
      (-((id ^ 2 + id ^ 4) + id ^ 6)) / fun _ : ℝ => 100 by
      funext y
      simp only [Pi.div_apply, Pi.neg_apply, Pi.add_apply, Pi.pow_apply, id_eq]]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_riccatiNoGoLikelihoodJetOne (t : ℝ) :
    HasDerivAt riccatiNoGoLikelihoodJetOne (riccatiNoGoLikelihoodJetTwo t) t := by
  unfold riccatiNoGoLikelihoodJetOne riccatiNoGoLikelihoodJetTwo
  have hraw := (((hasDerivAt_id t).div_const 50).neg.sub
    (((hasDerivAt_id t).pow 3).div_const 25)).sub
    (((hasDerivAt_id t).pow 5).const_mul (3 / 50 : ℝ))
  rw [show (fun y : ℝ => -y / 50 - y ^ 3 / 25 - 3 / 50 * y ^ 5) =
      (-(id / fun _ : ℝ => 50) - (id ^ 3) / fun _ : ℝ => 25) -
        fun y => (3 / 50 : ℝ) * (id ^ 5) y by
      funext y
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply, id_eq]
      ring]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_riccatiNoGoLikelihoodJetTwo (t : ℝ) :
    HasDerivAt riccatiNoGoLikelihoodJetTwo (riccatiNoGoLikelihoodJetThree t) t := by
  unfold riccatiNoGoLikelihoodJetTwo riccatiNoGoLikelihoodJetThree
  have hraw := ((hasDerivAt_const t (-1 / 50 : ℝ)).sub
    (((hasDerivAt_id t).pow 2).const_mul (3 / 25 : ℝ))).sub
    (((hasDerivAt_id t).pow 4).const_mul (3 / 10 : ℝ))
  rw [show (fun y : ℝ => -1 / 50 - 3 / 25 * y ^ 2 - 3 / 10 * y ^ 4) =
      ((fun _ : ℝ => -1 / 50) - fun y => (3 / 25 : ℝ) * (id ^ 2) y) -
        fun y => (3 / 10 : ℝ) * (id ^ 4) y by
      funext y
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_riccatiNoGoLikelihoodJetThree (t : ℝ) :
    HasDerivAt riccatiNoGoLikelihoodJetThree (riccatiNoGoLikelihoodJetFour t) t := by
  unfold riccatiNoGoLikelihoodJetThree riccatiNoGoLikelihoodJetFour
  have hraw := ((hasDerivAt_id t).const_mul (-6 / 25 : ℝ)).sub
    (((hasDerivAt_id t).pow 3).const_mul (6 / 5 : ℝ))
  rw [show (fun y : ℝ => -6 / 25 * y - 6 / 5 * y ^ 3) =
      (fun y => (-6 / 25 : ℝ) * id y) - fun y => (6 / 5 : ℝ) * (id ^ 3) y by
      funext y
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_riccatiNoGoLikelihoodJetFour (t : ℝ) :
    HasDerivAt riccatiNoGoLikelihoodJetFour (riccatiNoGoLikelihoodJetFive t) t := by
  unfold riccatiNoGoLikelihoodJetFour riccatiNoGoLikelihoodJetFive
  have hraw := (hasDerivAt_const t (-6 / 25 : ℝ)).sub
    (((hasDerivAt_id t).pow 2).const_mul (18 / 5 : ℝ))
  rw [show (fun y : ℝ => -6 / 25 - 18 / 5 * y ^ 2) =
      (fun _ : ℝ => -6 / 25) - fun y => (18 / 5 : ℝ) * (id ^ 2) y by
      funext y
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]]
  refine hraw.congr_deriv ?_
  norm_num [id_eq]
  ring

theorem hasDerivAt_riccatiNoGoLikelihoodJetFive (t : ℝ) :
    HasDerivAt riccatiNoGoLikelihoodJetFive (riccatiNoGoLikelihoodJetSix t) t := by
  unfold riccatiNoGoLikelihoodJetFive riccatiNoGoLikelihoodJetSix
  have hraw := (hasDerivAt_id t).const_mul (-36 / 5 : ℝ)
  rw [show (fun y : ℝ => -36 / 5 * y) = fun y => (-36 / 5 : ℝ) * id y by
    funext y
    rfl]
  refine hraw.congr_deriv ?_
  norm_num

theorem hasDerivAt_riccatiNoGoAtomAction (t : ℝ) :
    HasDerivAt riccatiNoGoAtomAction (riccatiNoGoAtomJetOne t) t := by
  have hraw := (hasDerivAt_sexticGaussianAction t).sub
    (hasDerivAt_riccatiNoGoLikelihoodAction t)
  rw [show riccatiNoGoAtomAction =
      sexticGaussianAction - riccatiNoGoLikelihoodAction by
      funext y
      simp only [Pi.sub_apply]
      rw [riccatiNoGoAction_decomposition]
      ring]
  refine hraw.congr_deriv ?_
  rw [riccatiNoGoJetOne_decomposition]
  ring

theorem hasDerivAt_riccatiNoGoAtomJetOne (t : ℝ) :
    HasDerivAt riccatiNoGoAtomJetOne (riccatiNoGoAtomJetTwo t) t := by
  have hraw := (hasDerivAt_sexticGaussianActionOne t).sub
    (hasDerivAt_riccatiNoGoLikelihoodJetOne t)
  rw [show riccatiNoGoAtomJetOne =
      sexticGaussianActionOne - riccatiNoGoLikelihoodJetOne by
      funext y
      simp only [Pi.sub_apply]
      rw [riccatiNoGoJetOne_decomposition]
      ring]
  refine hraw.congr_deriv ?_
  rw [riccatiNoGoJetTwo_decomposition]
  ring

theorem hasDerivAt_riccatiNoGoAtomJetTwo (t : ℝ) :
    HasDerivAt riccatiNoGoAtomJetTwo (riccatiNoGoAtomJetThree t) t := by
  have hraw := (hasDerivAt_sexticGaussianActionTwo t).sub
    (hasDerivAt_riccatiNoGoLikelihoodJetTwo t)
  rw [show riccatiNoGoAtomJetTwo =
      sexticGaussianActionTwo - riccatiNoGoLikelihoodJetTwo by
      funext y
      simp only [Pi.sub_apply]
      rw [riccatiNoGoJetTwo_decomposition]
      ring]
  refine hraw.congr_deriv ?_
  rw [riccatiNoGoJetThree_decomposition]
  ring

theorem riccatiNoGoProfile_factorization (t : ℝ) :
    sexticGaussianReflectedProfile t =
      riccatiNoGoAtomProfile t * riccatiNoGoLikelihoodInterference t := by
  unfold sexticGaussianReflectedProfile riccatiNoGoAtomProfile
    riccatiNoGoLikelihoodInterference
  rw [riccatiNoGoAction_decomposition, neg_add, Real.exp_add]

theorem riccatiNoGoAtomJetOne_pos {t : ℝ} (ht : 0 < t) :
    0 < riccatiNoGoAtomJetOne t := by
  unfold riccatiNoGoAtomJetOne
  positivity

theorem riccatiNoGoAtomJetTwo_pos (t : ℝ) :
    0 < riccatiNoGoAtomJetTwo t := by
  unfold riccatiNoGoAtomJetTwo
  positivity

theorem riccatiNoGoLikelihoodAction_neg {t : ℝ} (ht : 0 < t) :
    riccatiNoGoLikelihoodAction t < 0 := by
  unfold riccatiNoGoLikelihoodAction
  have : 0 < t ^ 2 := sq_pos_of_pos ht
  have hsum : 0 < t ^ 2 + t ^ 4 + t ^ 6 := by positivity
  have hneg : -(t ^ 2 + t ^ 4 + t ^ 6) < 0 := by linarith
  exact div_neg_of_neg_of_pos hneg (by norm_num)

theorem riccatiNoGoLikelihoodInterference_one_lt {t : ℝ} (ht : 0 < t) :
    1 < riccatiNoGoLikelihoodInterference t := by
  unfold riccatiNoGoLikelihoodInterference
  rw [Real.one_lt_exp_iff]
  exact neg_pos.mpr (riccatiNoGoLikelihoodAction_neg ht)

theorem riccatiNoGoLikelihoodJetOne_neg {t : ℝ} (ht : 0 < t) :
    riccatiNoGoLikelihoodJetOne t < 0 := by
  unfold riccatiNoGoLikelihoodJetOne
  have ht3 : 0 < t ^ 3 := by positivity
  have ht5 : 0 < t ^ 5 := by positivity
  nlinarith

theorem riccatiNoGoLikelihoodJetTwo_neg (t : ℝ) :
    riccatiNoGoLikelihoodJetTwo t < 0 := by
  unfold riccatiNoGoLikelihoodJetTwo
  nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]

theorem riccatiNoGoLikelihoodJetThree_neg {t : ℝ} (ht : 0 < t) :
    riccatiNoGoLikelihoodJetThree t < 0 := by
  unfold riccatiNoGoLikelihoodJetThree
  have ht3 : 0 < t ^ 3 := by positivity
  nlinarith

theorem riccatiNoGoLikelihoodJetFour_neg (t : ℝ) :
    riccatiNoGoLikelihoodJetFour t < 0 := by
  unfold riccatiNoGoLikelihoodJetFour
  nlinarith [sq_nonneg t]

theorem riccatiNoGoLikelihoodJetFive_neg {t : ℝ} (ht : 0 < t) :
    riccatiNoGoLikelihoodJetFive t < 0 := by
  unfold riccatiNoGoLikelihoodJetFive
  linarith

theorem riccatiNoGoLikelihoodJetSix_neg (t : ℝ) :
    riccatiNoGoLikelihoodJetSix t < 0 := by
  norm_num [riccatiNoGoLikelihoodJetSix]

theorem riccatiNoGoLikelihoodRiccatiMargin_eq (t : ℝ) :
    riccatiNoGoLikelihoodRiccatiMargin t =
      t / 1250 *
        (301 + 1508 * t ^ 2 + 30 * t ^ 4 + 48 * t ^ 6 + 45 * t ^ 8) := by
  unfold riccatiNoGoLikelihoodRiccatiMargin riccatiNoGoLikelihoodJetOne
    riccatiNoGoLikelihoodJetTwo riccatiNoGoLikelihoodJetThree
  ring

theorem riccatiNoGoLikelihoodRiccatiMargin_pos {t : ℝ} (ht : 0 < t) :
    0 < riccatiNoGoLikelihoodRiccatiMargin t := by
  rw [riccatiNoGoLikelihoodRiccatiMargin_eq]
  positivity

theorem riccatiNoGoAtomLikelihoodCross_neg {t : ℝ} (ht : 0 < t) :
    riccatiNoGoAtomLikelihoodCross t < 0 := by
  unfold riccatiNoGoAtomLikelihoodCross
  have ha1 := riccatiNoGoAtomJetOne_pos ht
  have ha2 := riccatiNoGoAtomJetTwo_pos t
  have hl1 := riccatiNoGoLikelihoodJetOne_neg ht
  have hl2 := riccatiNoGoLikelihoodJetTwo_neg t
  nlinarith [mul_neg_of_pos_of_neg ha1 hl2, mul_neg_of_neg_of_pos hl1 ha2]

theorem riccatiNoGoAtomMargin_add_cross_eq (t : ℝ) :
    riccatiNoGoAtomRiccatiMargin t + riccatiNoGoAtomLikelihoodCross t =
      t / 1250 *
        (33699 - 119508 * t ^ 2 + 364770 * t ^ 4 +
          95952 * t ^ 6 + 449955 * t ^ 8) := by
  unfold riccatiNoGoAtomRiccatiMargin riccatiNoGoAtomLikelihoodCross
    riccatiNoGoAtomJetOne riccatiNoGoAtomJetTwo riccatiNoGoAtomJetThree
    riccatiNoGoLikelihoodJetOne riccatiNoGoLikelihoodJetTwo
  ring

theorem riccatiNoGoAtomMargin_add_cross_pos {t : ℝ} (ht : 0 < t) :
    0 < riccatiNoGoAtomRiccatiMargin t + riccatiNoGoAtomLikelihoodCross t := by
  rw [riccatiNoGoAtomMargin_add_cross_eq]
  have hx : 0 ≤ t ^ 2 := sq_nonneg t
  have hquad : 0 < 33699 - 119508 * t ^ 2 + 364770 * (t ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (364770 * t ^ 2 - 59754)]
  have hbracket :
      0 < 33699 - 119508 * t ^ 2 + 364770 * t ^ 4 +
        95952 * t ^ 6 + 449955 * t ^ 8 := by
    nlinarith [sq_nonneg (t ^ 3), sq_nonneg (t ^ 4)]
  positivity

theorem neg_riccatiNoGoAtomLikelihoodCross_lt_atomMargin {t : ℝ} (ht : 0 < t) :
    -riccatiNoGoAtomLikelihoodCross t < riccatiNoGoAtomRiccatiMargin t := by
  linarith [riccatiNoGoAtomMargin_add_cross_pos ht]

theorem riccatiNoGoAtomRiccatiMargin_pos {t : ℝ} (ht : 0 < t) :
    0 < riccatiNoGoAtomRiccatiMargin t := by
  have hcross := riccatiNoGoAtomLikelihoodCross_neg ht
  have hdom := neg_riccatiNoGoAtomLikelihoodCross_lt_atomMargin ht
  linarith

theorem riccatiNoGoTotalRiccatiMargin_decomposition (t : ℝ) :
    2 * sexticGaussianActionOne t * sexticGaussianActionTwo t -
        sexticGaussianActionThree t =
      riccatiNoGoAtomRiccatiMargin t +
        riccatiNoGoLikelihoodRiccatiMargin t +
        riccatiNoGoAtomLikelihoodCross t := by
  unfold riccatiNoGoAtomRiccatiMargin riccatiNoGoLikelihoodRiccatiMargin
    riccatiNoGoAtomLikelihoodCross
  rw [riccatiNoGoJetOne_decomposition, riccatiNoGoJetTwo_decomposition,
    riccatiNoGoJetThree_decomposition]
  ring

theorem riccatiNoGoAtomAction_zero : riccatiNoGoAtomAction 0 = 0 := by
  norm_num [riccatiNoGoAtomAction]

theorem riccatiNoGoLikelihoodAction_zero : riccatiNoGoLikelihoodAction 0 = 0 := by
  norm_num [riccatiNoGoLikelihoodAction]

theorem riccatiNoGoAtomAction_even : Function.Even riccatiNoGoAtomAction := by
  intro t
  unfold riccatiNoGoAtomAction
  ring

theorem riccatiNoGoLikelihoodAction_even : Function.Even riccatiNoGoLikelihoodAction := by
  intro t
  unfold riccatiNoGoLikelihoodAction
  ring

theorem riccatiNoGoAtomProfile_pos (t : ℝ) : 0 < riccatiNoGoAtomProfile t := by
  unfold riccatiNoGoAtomProfile
  positivity

theorem riccatiNoGoLikelihoodInterference_pos (t : ℝ) :
    0 < riccatiNoGoLikelihoodInterference t := by
  unfold riccatiNoGoLikelihoodInterference
  positivity

/-- **No-go for the complete current atom--likelihood Riccati sign architecture.**
The full list of presently available component signs, including strict atom domination of the
negative cross channel, coexists with local C5 positivity and a later strict C5 failure. -/
theorem atomLikelihoodRiccatiSignArchitecture_with_localC5_does_not_force_globalC5 :
    (∀ t : ℝ,
      HasDerivAt riccatiNoGoAtomAction (riccatiNoGoAtomJetOne t) t ∧
      HasDerivAt riccatiNoGoAtomJetOne (riccatiNoGoAtomJetTwo t) t ∧
      HasDerivAt riccatiNoGoAtomJetTwo (riccatiNoGoAtomJetThree t) t ∧
      HasDerivAt riccatiNoGoLikelihoodAction (riccatiNoGoLikelihoodJetOne t) t ∧
      HasDerivAt riccatiNoGoLikelihoodJetOne (riccatiNoGoLikelihoodJetTwo t) t ∧
      HasDerivAt riccatiNoGoLikelihoodJetTwo (riccatiNoGoLikelihoodJetThree t) t ∧
      HasDerivAt riccatiNoGoLikelihoodJetThree (riccatiNoGoLikelihoodJetFour t) t ∧
      HasDerivAt riccatiNoGoLikelihoodJetFour (riccatiNoGoLikelihoodJetFive t) t ∧
      HasDerivAt riccatiNoGoLikelihoodJetFive (riccatiNoGoLikelihoodJetSix t) t) ∧
    (∀ t : ℝ, sexticGaussianAction t =
      riccatiNoGoAtomAction t + riccatiNoGoLikelihoodAction t) ∧
    (∀ t : ℝ, sexticGaussianReflectedProfile t =
      riccatiNoGoAtomProfile t * riccatiNoGoLikelihoodInterference t) ∧
    (∀ t : ℝ, 0 < t →
      0 < riccatiNoGoAtomJetOne t ∧
      0 < riccatiNoGoAtomJetTwo t ∧
      riccatiNoGoLikelihoodAction t < 0 ∧
      1 < riccatiNoGoLikelihoodInterference t ∧
      riccatiNoGoLikelihoodJetOne t < 0 ∧
      riccatiNoGoLikelihoodJetTwo t < 0 ∧
      riccatiNoGoLikelihoodJetThree t < 0 ∧
      riccatiNoGoLikelihoodJetFour t < 0 ∧
      riccatiNoGoLikelihoodJetFive t < 0 ∧
      riccatiNoGoLikelihoodJetSix t < 0 ∧
      0 < riccatiNoGoAtomRiccatiMargin t ∧
      0 < riccatiNoGoLikelihoodRiccatiMargin t ∧
      riccatiNoGoAtomLikelihoodCross t < 0 ∧
      -riccatiNoGoAtomLikelihoodCross t < riccatiNoGoAtomRiccatiMargin t) ∧
    (∀ T : ℝ, 0 ≤ T →
      ConcaveOn ℝ (Icc 0 T) (riccatiCorrelationAngle sexticGaussianAction)) ∧
    (∀ x : ℝ, 0 ≤ x →
      iteratedDeriv 2
        (fun y => Real.log (firstLaguerreExpression cubicGaussianRadialProfile y)) x < 0) ∧
    (∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < fifthRootDividedDropCurvatureNumerator sexticGaussianReflectedProfile t) ∧
    fifthRootDividedDropCurvatureNumerator sexticGaussianReflectedProfile
      (Real.sqrt (1 / 2)) < 0 := by
  refine ⟨?_, riccatiNoGoAction_decomposition, riccatiNoGoProfile_factorization,
    ?_, ?_, ?_, exists_sexticGaussianReflectedProfile_fifthRootCurvature_pos_right,
    sexticGaussianReflectedProfile_fifthRootCurvature_neg⟩
  · intro t
    exact ⟨hasDerivAt_riccatiNoGoAtomAction t,
      hasDerivAt_riccatiNoGoAtomJetOne t,
      hasDerivAt_riccatiNoGoAtomJetTwo t,
      hasDerivAt_riccatiNoGoLikelihoodAction t,
      hasDerivAt_riccatiNoGoLikelihoodJetOne t,
      hasDerivAt_riccatiNoGoLikelihoodJetTwo t,
      hasDerivAt_riccatiNoGoLikelihoodJetThree t,
      hasDerivAt_riccatiNoGoLikelihoodJetFour t,
      hasDerivAt_riccatiNoGoLikelihoodJetFive t⟩
  · intro t ht
    exact ⟨riccatiNoGoAtomJetOne_pos ht,
      riccatiNoGoAtomJetTwo_pos t,
      riccatiNoGoLikelihoodAction_neg ht,
      riccatiNoGoLikelihoodInterference_one_lt ht,
      riccatiNoGoLikelihoodJetOne_neg ht,
      riccatiNoGoLikelihoodJetTwo_neg t,
      riccatiNoGoLikelihoodJetThree_neg ht,
      riccatiNoGoLikelihoodJetFour_neg t,
      riccatiNoGoLikelihoodJetFive_neg ht,
      riccatiNoGoLikelihoodJetSix_neg t,
      riccatiNoGoAtomRiccatiMargin_pos ht,
      riccatiNoGoLikelihoodRiccatiMargin_pos ht,
      riccatiNoGoAtomLikelihoodCross_neg ht,
      neg_riccatiNoGoAtomLikelihoodCross_lt_atomMargin ht⟩
  · intro T hT
    exact sexticGaussianCorrelationAngle_concaveOn hT
  · intro x hx
    exact cubicGaussianRadialProfile_secondLevel_strict hx

end

end HilbertMetric
