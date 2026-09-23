import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSeventhEighthCumulant
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHighSourceJets

/-!
# Seventh and eighth source-coordinate theta likelihood jets

Pulls the seventh/eighth likelihood cumulants through the exponential theta source coordinate.
The coefficients are the order-seven and order-eight Stirling score rows.  The order-eight
ordinary score has a genuine low-support obstruction but becomes strictly positive at `z ≥ 14`;
this isolates the global rank-three correction to a compact low spectral chamber.
-/

namespace RHTower

noncomputable section

/-- Seventh source-coordinate jet of the logarithmic higher-likelihood partition. -/
def thetaCuspLikelihoodSourceLogPartitionJetSeven (x : ℝ) : ℝ :=
  -128 * thetaCuspSingleAtomReflectionScale 1 x ^ (7 : ℕ) *
      thetaCuspLikelihoodSeventhCumulant (thetaCuspLikelihoodCoordinate x) +
    2688 * thetaCuspSingleAtomReflectionScale 1 x ^ (6 : ℕ) *
      thetaCuspLikelihoodSixthCumulant (thetaCuspLikelihoodCoordinate x) -
    17920 * thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) *
      thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x) +
    44800 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
      thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x) -
    38528 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) *
      thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x) +
    8064 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
      thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) -
    128 * thetaCuspSingleAtomReflectionScale 1 x *
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)

/-- Eighth source-coordinate jet of the logarithmic higher-likelihood partition. -/
def thetaCuspLikelihoodSourceLogPartitionJetEight (x : ℝ) : ℝ :=
  256 * thetaCuspSingleAtomReflectionScale 1 x ^ (8 : ℕ) *
      thetaCuspLikelihoodEighthCumulant (thetaCuspLikelihoodCoordinate x) -
    7168 * thetaCuspSingleAtomReflectionScale 1 x ^ (7 : ℕ) *
      thetaCuspLikelihoodSeventhCumulant (thetaCuspLikelihoodCoordinate x) +
    68096 * thetaCuspSingleAtomReflectionScale 1 x ^ (6 : ℕ) *
      thetaCuspLikelihoodSixthCumulant (thetaCuspLikelihoodCoordinate x) -
    268800 * thetaCuspSingleAtomReflectionScale 1 x ^ (5 : ℕ) *
      thetaCuspLikelihoodFifthCumulant (thetaCuspLikelihoodCoordinate x) +
    435456 * thetaCuspSingleAtomReflectionScale 1 x ^ (4 : ℕ) *
      thetaCuspLikelihoodFourthCumulant (thetaCuspLikelihoodCoordinate x) -
    247296 * thetaCuspSingleAtomReflectionScale 1 x ^ (3 : ℕ) *
      thetaCuspLikelihoodThirdCumulant (thetaCuspLikelihoodCoordinate x) +
    32512 * thetaCuspSingleAtomReflectionScale 1 x ^ (2 : ℕ) *
      thetaCuspLikelihoodVariance (thetaCuspLikelihoodCoordinate x) -
    256 * thetaCuspSingleAtomReflectionScale 1 x *
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x)

/-- Differentiating the sixth source jet gives the literal seventh source jet. -/
theorem hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSix
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt thetaCuspLikelihoodSourceLogPartitionJetSix (thetaCuspLikelihoodSourceLogPartitionJetSeven x) x := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx
  have hA := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hcoord := hasDerivAt_thetaCuspLikelihoodCoordinate x
  have hm := (hasDerivAt_thetaCuspLikelihoodMean hB).comp x hcoord
  have hv := (hasDerivAt_thetaCuspLikelihoodVariance hB).comp x hcoord
  have hk3 := (hasDerivAt_thetaCuspLikelihoodThirdCumulant hB).comp x hcoord
  have hk4 := (hasDerivAt_thetaCuspLikelihoodFourthCumulant hB).comp x hcoord
  have hk5 := (hasDerivAt_thetaCuspLikelihoodFifthCumulant hB).comp x hcoord
  have hk6 := (hasDerivAt_thetaCuspLikelihoodSixthCumulant hB).comp x hcoord
  have h0 := ((hA.pow 6).mul hk6).const_mul 64
  have h1 := h0.sub (((hA.pow 5).mul hk5).const_mul 960)
  have h2 := h1.add (((hA.pow 4).mul hk4).const_mul 4160)
  have h3 := h2.sub (((hA.pow 3).mul hk3).const_mul 5760)
  have h4 := h3.add (((hA.pow 2).mul hv).const_mul 1984)
  have hraw := h4.sub ((hA.mul hm).const_mul 64)
  unfold thetaCuspLikelihoodSourceLogPartitionJetSix thetaCuspLikelihoodSourceLogPartitionJetSeven
  convert hraw using 1
  any_goals rfl
  · funext y
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring
  · simp only [Function.comp_apply, Pi.pow_apply]
    ring

/-- Differentiating the seventh source jet gives the literal eighth source jet. -/
theorem hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetSeven
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt thetaCuspLikelihoodSourceLogPartitionJetSeven
      (thetaCuspLikelihoodSourceLogPartitionJetEight x) x := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx
  have hA := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hcoord := hasDerivAt_thetaCuspLikelihoodCoordinate x
  have hm := (hasDerivAt_thetaCuspLikelihoodMean hB).comp x hcoord
  have hv := (hasDerivAt_thetaCuspLikelihoodVariance hB).comp x hcoord
  have hk3 := (hasDerivAt_thetaCuspLikelihoodThirdCumulant hB).comp x hcoord
  have hk4 := (hasDerivAt_thetaCuspLikelihoodFourthCumulant hB).comp x hcoord
  have hk5 := (hasDerivAt_thetaCuspLikelihoodFifthCumulant hB).comp x hcoord
  have hk6 := (hasDerivAt_thetaCuspLikelihoodSixthCumulant hB).comp x hcoord
  have hk7 := (hasDerivAt_thetaCuspLikelihoodSeventhCumulant hB).comp x hcoord
  have h0 := ((hA.pow 7).mul hk7).const_mul (-128)
  have h1 := h0.add (((hA.pow 6).mul hk6).const_mul 2688)
  have h2 := h1.sub (((hA.pow 5).mul hk5).const_mul 17920)
  have h3 := h2.add (((hA.pow 4).mul hk4).const_mul 44800)
  have h4 := h3.sub (((hA.pow 3).mul hk3).const_mul 38528)
  have h5 := h4.add (((hA.pow 2).mul hv).const_mul 8064)
  have hraw := h5.sub ((hA.mul hm).const_mul 128)
  unfold thetaCuspLikelihoodSourceLogPartitionJetSeven thetaCuspLikelihoodSourceLogPartitionJetEight
  convert hraw using 1
  any_goals rfl
  · funext y
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring
  · simp only [Function.comp_apply, Pi.pow_apply]
    ring

/-- Order-eight ordinary likelihood score in the scaled spectral coordinate `z = A t`. -/
def thetaCuspLikelihoodEighthSourceScore (z : ℝ) : ℝ :=
  z ^ (8 : ℕ) - 28 * z ^ (7 : ℕ) + 266 * z ^ (6 : ℕ) - 1050 * z ^ (5 : ℕ) +
    1701 * z ^ (4 : ℕ) - 966 * z ^ (3 : ℕ) + 127 * z ^ (2 : ℕ) - z

/-- The order-eight score is negative at the proved order-six support margin. -/
theorem thetaCuspLikelihoodEighthSourceScore_supportMargin_neg :
    thetaCuspLikelihoodEighthSourceScore (47 / 5) < 0 := by
  norm_num [thetaCuspLikelihoodEighthSourceScore]

/-- Above the exact rational barrier `14`, the order-eight score has positive coefficients. -/
theorem thetaCuspLikelihoodEighthSourceScore_pos_of_fourteen_le
    {z : ℝ} (hz : 14 ≤ z) :
    0 < thetaCuspLikelihoodEighthSourceScore z := by
  let y := z - 14
  have hy : 0 ≤ y := by
    dsimp only [y]
    linarith
  rw [show z = 14 + y by dsimp only [y]; ring]
  dsimp only [thetaCuspLikelihoodEighthSourceScore]
  ring_nf
  positivity

end

end RHTower
