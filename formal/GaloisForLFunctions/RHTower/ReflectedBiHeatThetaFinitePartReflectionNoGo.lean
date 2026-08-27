import GaloisForLFunctions.RHTower.ReflectedBiHeatThetaResidue

/-!
# Reflection no-go for the reflected bi-heat theta finite part

Complementary-order reflection swaps the two Dirichlet factors while lattice
transpose preserves their additive heat coefficient.  Therefore the regulated
pair sum, its canonical theta-pole finite part, and every reflection-even source
are unable to distinguish the two sides of the critical wall.

The positive survivor is exact: an arbitrary added scalar source splits into
reflection-even and reflection-odd projections, and the completed finite-part
defect is twice the odd projection.
-/

open Complex Filter Set Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Complementary-order reflection of a reflected bi-heat datum. -/
def ReflectedBiHeatDatum.reflect (P : ReflectedBiHeatDatum) : ReflectedBiHeatDatum where
  z := 1 - P.z
  x := P.x
  z_re_pos := by
    simp only [sub_re, one_re]
    linarith [P.z_re_lt_one]
  z_re_lt_one := by
    simp only [sub_re, one_re]
    linarith [P.z_re_pos]
  x_pos := P.x_pos

@[simp] theorem ReflectedBiHeatDatum.reflect_z (P : ReflectedBiHeatDatum) :
    P.reflect.z = 1 - P.z := rfl

@[simp] theorem ReflectedBiHeatDatum.reflect_x (P : ReflectedBiHeatDatum) :
    P.reflect.x = P.x := rfl

@[simp] theorem ReflectedBiHeatDatum.reflect_reflect (P : ReflectedBiHeatDatum) :
    P.reflect.reflect = P := by
  cases P
  simp [ReflectedBiHeatDatum.reflect]

@[simp] theorem ReflectedBiHeatDatum.reflect_leftOrder
    (P : ReflectedBiHeatDatum) (epsilon : ℂ) :
    P.reflect.leftOrder epsilon = P.rightOrder epsilon := by
  simp [ReflectedBiHeatDatum.reflect, ReflectedBiHeatDatum.leftOrder,
    ReflectedBiHeatDatum.rightOrder]

@[simp] theorem ReflectedBiHeatDatum.reflect_rightOrder
    (P : ReflectedBiHeatDatum) (epsilon : ℂ) :
    P.reflect.rightOrder epsilon = P.leftOrder epsilon := by
  simp [ReflectedBiHeatDatum.reflect, ReflectedBiHeatDatum.leftOrder,
    ReflectedBiHeatDatum.rightOrder]

/-- Factor swap equals lattice transpose for the additive-heat pair term. -/
theorem asymmetricHeatPairTerm_swap (a b : ℂ) (x : ℝ) (m n : ℕ) :
    asymmetricHeatPairTerm a b x (m, n) =
      asymmetricHeatPairTerm b a x (n, m) := by
  rw [asymmetricHeatPairTerm, asymmetricHeatPairTerm]
  have hdiff : (m : ℤ) - (n : ℤ) = -((n : ℤ) - (m : ℤ)) := by ring
  rw [hdiff, heatCoeff_neg]
  ring

/-- Regulated pair sum is exactly invariant under complementary-order reflection. -/
theorem reflectedBiHeatPairSum_reflect
    (P : ReflectedBiHeatDatum) (epsilon : ℂ) :
    reflectedBiHeatPairSum P.reflect epsilon =
      reflectedBiHeatPairSum P epsilon := by
  simp only [reflectedBiHeatPairSum, ReflectedBiHeatDatum.reflect_leftOrder,
    ReflectedBiHeatDatum.reflect_rightOrder, ReflectedBiHeatDatum.reflect_x]
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
  apply tsum_congr
  intro p
  rcases p with ⟨m, n⟩
  exact (asymmetricHeatPairTerm_swap _ _ _ _ _).symm

/-- Canonical theta-pole finite part is unchanged by complementary-order reflection. -/
theorem reflectedBiHeatFinitePart_reflect (P : ReflectedBiHeatDatum) :
    reflectedBiHeatFinitePart P.reflect = reflectedBiHeatFinitePart P := by
  have hreflect : Tendsto (fun epsilon : ℝ =>
      reflectedBiHeatPairSum P (epsilon : ℂ) -
        ((heatCoeffSum P.x : ℝ) : ℂ) / (epsilon : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (reflectedBiHeatFinitePart P.reflect)) := by
    simpa only [reflectedBiHeatPairSum_reflect, ReflectedBiHeatDatum.reflect_x] using
      tendsto_reflectedBiHeatPairSum_sub_thetaPole_finitePart P.reflect
  exact tendsto_nhds_unique hreflect
    (tendsto_reflectedBiHeatPairSum_sub_thetaPole_finitePart P)

/-- Off the critical wall, complementary-order reflection changes the datum. -/
theorem ReflectedBiHeatDatum.reflect_ne_of_re_ne_half
    (P : ReflectedBiHeatDatum) (hz : P.z.re ≠ 1 / 2) :
    P.reflect ≠ P := by
  intro h
  apply hz
  have hre := congrArg (fun Q : ReflectedBiHeatDatum => Q.z.re) h
  simp [ReflectedBiHeatDatum.reflect] at hre
  linarith

/-- Canonical finite part is pointwise noninjective at every off-wall datum. -/
theorem reflectedBiHeatFinitePart_noninjective_at_offWall
    (P : ReflectedBiHeatDatum) (hz : P.z.re ≠ 1 / 2) :
    ∃ Q : ReflectedBiHeatDatum,
      Q ≠ P ∧ reflectedBiHeatFinitePart Q = reflectedBiHeatFinitePart P := by
  exact ⟨P.reflect, P.reflect_ne_of_re_ne_half hz,
    reflectedBiHeatFinitePart_reflect P⟩

/-- Reflection-even projection of an arbitrary scalar source. -/
def reflectedBiHeatSourceEvenPart
    (A : ReflectedBiHeatDatum → ℂ) (P : ReflectedBiHeatDatum) : ℂ :=
  (A P + A P.reflect) / 2

/-- Reflection-odd projection of an arbitrary scalar source. -/
def reflectedBiHeatSourceOddPart
    (A : ReflectedBiHeatDatum → ℂ) (P : ReflectedBiHeatDatum) : ℂ :=
  (A P - A P.reflect) / 2

theorem reflectedBiHeatSource_eq_evenPart_add_oddPart
    (A : ReflectedBiHeatDatum → ℂ) (P : ReflectedBiHeatDatum) :
    A P = reflectedBiHeatSourceEvenPart A P + reflectedBiHeatSourceOddPart A P := by
  simp only [reflectedBiHeatSourceEvenPart, reflectedBiHeatSourceOddPart]
  ring

theorem reflectedBiHeatSourceEvenPart_reflect
    (A : ReflectedBiHeatDatum → ℂ) (P : ReflectedBiHeatDatum) :
    reflectedBiHeatSourceEvenPart A P.reflect = reflectedBiHeatSourceEvenPart A P := by
  simp [reflectedBiHeatSourceEvenPart]
  ring

theorem reflectedBiHeatSourceOddPart_reflect
    (A : ReflectedBiHeatDatum → ℂ) (P : ReflectedBiHeatDatum) :
    reflectedBiHeatSourceOddPart A P.reflect = -reflectedBiHeatSourceOddPart A P := by
  simp [reflectedBiHeatSourceOddPart]
  ring

/-- Canonical finite part with an arbitrary additional scalar source. -/
def reflectedBiHeatAugmentedFinitePart
    (A : ReflectedBiHeatDatum → ℂ) (P : ReflectedBiHeatDatum) : ℂ :=
  reflectedBiHeatFinitePart P + A P

/-- Every completed finite-part reflection defect is twice the odd source projection. -/
theorem reflectedBiHeatAugmentedFinitePart_sub_reflect
    (A : ReflectedBiHeatDatum → ℂ) (P : ReflectedBiHeatDatum) :
    reflectedBiHeatAugmentedFinitePart A P -
        reflectedBiHeatAugmentedFinitePart A P.reflect =
      2 * reflectedBiHeatSourceOddPart A P := by
  rw [reflectedBiHeatAugmentedFinitePart, reflectedBiHeatAugmentedFinitePart,
    reflectedBiHeatFinitePart_reflect]
  simp only [reflectedBiHeatSourceOddPart]
  ring

/-- Completed finite part is reflection-blind exactly when its odd source part vanishes. -/
theorem reflectedBiHeatAugmentedFinitePart_reflect_eq_iff_oddPart_eq_zero
    (A : ReflectedBiHeatDatum → ℂ) (P : ReflectedBiHeatDatum) :
    reflectedBiHeatAugmentedFinitePart A P =
        reflectedBiHeatAugmentedFinitePart A P.reflect ↔
      reflectedBiHeatSourceOddPart A P = 0 := by
  constructor
  · intro h
    have hsub : reflectedBiHeatAugmentedFinitePart A P -
        reflectedBiHeatAugmentedFinitePart A P.reflect = 0 := sub_eq_zero.mpr h
    rw [reflectedBiHeatAugmentedFinitePart_sub_reflect] at hsub
    exact (mul_eq_zero.mp hsub).resolve_left (by norm_num)
  · intro h
    apply sub_eq_zero.mp
    rw [reflectedBiHeatAugmentedFinitePart_sub_reflect, h, mul_zero]

end RHTower
