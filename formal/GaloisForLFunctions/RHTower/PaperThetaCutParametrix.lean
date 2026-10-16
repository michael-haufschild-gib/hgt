import GaloisForLFunctions.RHTower.PaperThetaBoundedVariation
import GaloisForLFunctions.RHTower.PaperThetaLocalRegularity

/-! # A two-ended theta parametrix with a movable interior charge

The upper and reflected lower branches are glued at a finite source cut.
Every complex parameter then has a genuine bounded-variation mode, with
trace `-1` at both ends. The connection coefficient is retained exactly as
the jump, rather than discarded by a divisor-dependent domain restriction.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry

/-- The branch decaying at the left source end. -/
def leftQuotient (z : ℂ) (x : ℝ) : ℂ := flatQuotient (-z) (-x)

/-- Both native tails, joined at an arbitrary finite source cut. -/
def cutQuotient (z : ℂ) (a x : ℝ) : ℂ :=
  if x < a then leftQuotient z x else flatQuotient z x

/-- The exact right-minus-left connection charge. -/
def cutCharge (z : ℂ) (a : ℝ) : ℂ :=
  flatQuotient z a - leftQuotient z a

theorem flatPrimitiveMode_connection_reflection (z : ℂ) (x : ℝ) :
    flatPrimitiveMode z x + flatPrimitiveMode (-z) (-x) =
      flatConnection z * Complex.exp (-(Complex.I*z)*(x : ℂ)) := by
  have hI : ∫ y in Iic x, flatCharDensity z y =
      ∫ y in Ioi (-x), flatCharDensity (-z) y := by
    rw [← integral_comp_neg_Iic x (flatCharDensity (-z))]
    apply integral_congr_ae
    filter_upwards [] with y
    exact (flatCharDensity_reflection z y).symm
  have he : Complex.exp (-(Complex.I*(-z))*((-x : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I*z)*(x : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [flatPrimitiveMode_eq_all, hI, flatPrimitiveMode, he]
  ring

/-- The charge is the full Xi connection coefficient, with a nonzero cut gauge. -/
theorem cutCharge_eq (z : ℂ) (a : ℝ) :
    cutCharge z a =
      -(Complex.I*z) * XiC z * Complex.exp (-(Complex.I*z)*(a : ℂ)) /
        (thetaSource.k a : ℂ) := by
  have hρ : (thetaSource.normalized a : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos a).ne'
  have hm : (thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast thetaSource.mass_ne_zero
  have hk : (thetaSource.k a : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.pos_k a).ne'
  have hp := flatPrimitiveMode_connection_reflection z a
  rw [flatConnection_eq_all] at hp
  unfold cutCharge leftQuotient flatQuotient flatMode
  rw [normalized_reflection]
  calc
    _ = -(Complex.I*z) *
        (flatPrimitiveMode z a + flatPrimitiveMode (-z) (-a)) /
          (thetaSource.normalized a : ℂ) := by field_simp; ring
    _ = _ := by
      rw [hp, PositiveDensitySource.normalized]
      push_cast
      field_simp

theorem continuous_leftQuotient (z : ℂ) : Continuous (leftQuotient z) :=
  (continuous_flatQuotient (-z)).comp continuous_neg

theorem cutQuotient_left (z : ℂ) {a x : ℝ} (hx : x < a) :
    cutQuotient z a x = leftQuotient z x := if_pos hx

theorem cutQuotient_right (z : ℂ) {a x : ℝ} (hx : a ≤ x) :
    cutQuotient z a x = flatQuotient z x := if_neg (not_lt.mpr hx)

theorem tendsto_cutQuotient_left (z : ℂ) (a : ℝ) :
    Tendsto (cutQuotient z a) (𝓝[<] a) (𝓝 (leftQuotient z a)) := by
  apply ((continuous_leftQuotient z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (cutQuotient_left z hx).symm

theorem tendsto_cutQuotient_atTop (z : ℂ) (a : ℝ) :
    Tendsto (cutQuotient z a) atTop (𝓝 (-1)) := by
  apply (tendsto_flatQuotient_atTop z).congr'
  filter_upwards [eventually_ge_atTop a] with x hx
  exact (cutQuotient_right z hx).symm

theorem tendsto_cutQuotient_atBot (z : ℂ) (a : ℝ) :
    Tendsto (cutQuotient z a) atBot (𝓝 (-1)) := by
  apply ((tendsto_flatQuotient_atTop (-z)).comp tendsto_neg_atBot_atTop).congr'
  filter_upwards [eventually_lt_atBot a] with x hx
  exact (cutQuotient_left z hx).symm

/-- The singular mode domain is replaced by a genuine BV family for every parameter. -/
theorem boundedVariationOn_cutQuotient (z : ℂ) (a : ℝ) :
    BoundedVariationOn (cutQuotient z a) univ := by
  have hleft : eVariationOn (cutQuotient z a) (Iio a) ≤
      eVariationOn (flatQuotient (-z)) (Ici (-a)) := by
    rw [eVariationOn.congr (s := Iio a)
      (fun x hx => cutQuotient_left z (a := a) (x := x) hx)]
    apply eVariationOn.comp_le_of_antitoneOn (flatQuotient (-z))
      (s := Ici (-a)) (fun x : ℝ => -x)
      (fun _ _ _ _ h => neg_le_neg h)
    intro x hx
    exact neg_le_neg (show x ≤ a from hx.le)
  have hleftFin : eVariationOn (cutQuotient z a) (Iio a) ≠ ⊤ :=
    ne_top_of_le_ne_top (boundedVariationOn_flatQuotient_Ici (-z) (-a)) hleft
  have hleftClosed : eVariationOn (cutQuotient z a) (Iic a) ≠ ⊤ := by
    have he := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
      (f := cutQuotient z a) (s := univ) (a := a)
      (l := leftQuotient z a) (by simpa using (inferInstance : (𝓝[<] a).NeBot))
      (mem_univ a) (by simpa using tendsto_cutQuotient_left z a)
    simp only [univ_inter] at he
    rw [he]
    exact ENNReal.add_ne_top.mpr ⟨hleftFin, edist_ne_top _ _⟩
  have hright : eVariationOn (cutQuotient z a) (Ici a) ≠ ⊤ := by
    rw [eVariationOn.congr (s := Ici a)
      (fun x hx => cutQuotient_right z (a := a) (x := x) hx)]
    exact boundedVariationOn_flatQuotient_Ici z a
  have hu : Iic a ∪ Ici a = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total x a
  change eVariationOn (cutQuotient z a) univ ≠ ⊤
  have he := eVariationOn.union (cutQuotient z a) (s := Iic a) (t := Ici a) (x := a)
    ⟨by simp, fun _ h => h⟩ ⟨by simp, fun _ h => h⟩
  rw [hu] at he
  rw [he]
  exact ENNReal.add_ne_top.mpr ⟨hleftClosed, hright⟩

/-- On the original divisor domain the construction is pointwise the original mode. -/
theorem cutQuotient_eq_native (z : {z : ℂ // z = 0 ∨ XiC z = 0}) (a x : ℝ) :
    cutQuotient z.val a x = flatQuotient z.val x := by
  by_cases hx : x < a
  · rw [cutQuotient_left z.val hx, leftQuotient]
    rcases z.property with hz | hz
    · simp [hz, flatQuotient_zero]
    · exact (flatQuotient_divisor_reflection ⟨z.val, hz⟩ x).symm
  · exact cutQuotient_right z.val (le_of_not_gt hx)

/-- Moving the cut does not change the normalized source charge. -/
theorem cutCharge_transport (z : ℂ) (a b : ℝ) :
    (thetaSource.k a : ℂ) * Complex.exp (Complex.I*z*(a : ℂ)) * cutCharge z a =
      (thetaSource.k b : ℂ) * Complex.exp (Complex.I*z*(b : ℂ)) * cutCharge z b := by
  have h (x : ℝ) : (thetaSource.k x : ℂ) *
      Complex.exp (Complex.I*z*(x : ℂ)) * cutCharge z x = -(Complex.I*z)*XiC z := by
    have hk : (thetaSource.k x : ℂ) ≠ 0 := by
      exact_mod_cast (thetaSource.pos_k x).ne'
    rw [cutCharge_eq]
    have he : Complex.exp (Complex.I*z*(x : ℂ)) *
        Complex.exp (-(Complex.I*z)*(x : ℂ)) = 1 := by
      rw [← Complex.exp_add,
        show Complex.I*z*(x : ℂ) + -(Complex.I*z)*(x : ℂ) = 0 by ring,
        Complex.exp_zero]
    calc
      _ = (-(Complex.I*z)*XiC z) *
          (Complex.exp (Complex.I*z*(x : ℂ)) *
            Complex.exp (-(Complex.I*z)*(x : ℂ))) := by field_simp
      _ = _ := by rw [he, mul_one]
  rw [h, h]

end RHTower.PaperThetaEndpoint
