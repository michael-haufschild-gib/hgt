import GaloisForLFunctions.HTGeometry.QDifferenceLaurentModel

/-!
# The rational base field of the two-variable Laurent model

The two-variable rational function field `k(z)(h)` embeds into `k((z))((h))` by expanding both
coordinates in Laurent series, and the dilation `z ↦ b z`, `h ↦ a⁻¹ h` of the base is the
restriction of the dilation of the ambient field.  Both statements are instances of the Laurent
intertwining of a twisted dilation.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Multiplicative

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-- The twisted dilation with trivial coefficient twist is the plain dilation. -/
theorem ratFuncTwist_id (q : k) (hq : q ≠ 0) (f : RatFunc k) :
    ratFuncTwist (RingHom.id k) Function.injective_id q hq f = ratFuncScale q hq f := by
  refine RatFunc.induction_on (P := fun f =>
    ratFuncTwist (RingHom.id k) Function.injective_id q hq f = ratFuncScale q hq f) f ?_
  intro p s _
  rw [ratFuncTwist_div, ratFuncScale_div, polyTwist_apply, polyTwist_apply,
    Polynomial.map_id, Polynomial.map_id]

/-- **The Laurent expansion intertwines the dilation of `k(z)` with the dilation of `k((z))`.** -/
theorem algebraMap_ratFuncScale (b : k) (hb : b ≠ 0) (f : RatFunc k) :
    algebraMap (RatFunc k) (LaurentSeries k) (ratFuncScale b hb f)
      = innerDilation b hb (algebraMap (RatFunc k) (LaurentSeries k) f) := by
  rw [← ratFuncTwist_id b hb f,
    algebraMap_ratFuncTwist (RingHom.id k) Function.injective_id b hb f]
  rfl

/-- The two-variable rational base field `k(z)(h)`. -/
abbrev QBase (k : Type*) [Field k] := RatFunc (RatFunc k)

theorem ratFuncScale_injective (b : k) (hb : b ≠ 0) :
    Function.Injective ((ratFuncScale b hb : RatFunc k →ₐ[k] RatFunc k) : RatFunc k →+* RatFunc k) :=
  RingHom.injective _

/-- The dilation `z ↦ b z`, `h ↦ a⁻¹ h` of `k(z)(h)`. -/
def qBaseDilation (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) : QBase k →+* QBase k :=
  ratFuncTwist ((ratFuncScale b hb : RatFunc k →ₐ[k] RatFunc k) : RatFunc k →+* RatFunc k)
    (ratFuncScale_injective b hb) (algebraMap k (RatFunc k) a⁻¹)
    (by simpa using inv_ne_zero ha)

/-- The Laurent expansion of the two-variable rational function field. -/
def qEmbed (k : Type*) [Field k] : QBase k →+* QLaurent k :=
  (hahnMapRingHom (algebraMap (RatFunc k) (LaurentSeries k))).comp
    (algebraMap (RatFunc (RatFunc k)) (LaurentSeries (RatFunc k)))

/-- **The base dilation is the restriction of the ambient dilation.** -/
theorem qEmbed_qBaseDilation (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) (x : QBase k) :
    qEmbed k (qBaseDilation a b ha hb x) = qDilation a b ha hb (qEmbed k x) := by
  have hχ : ∀ n : ℤ,
      algebraMap (RatFunc k) (LaurentSeries k)
          ((laurentChar (algebraMap k (RatFunc k) a⁻¹) (by simpa using inv_ne_zero ha))
            (ofAdd n) : RatFunc k)
        = ((laurentChar (HahnSeries.C a⁻¹ : LaurentSeries k)
            (C_ne_zero_of_ne_zero (inv_ne_zero ha))) (ofAdd n) : LaurentSeries k) := by
    intro n
    rw [laurentChar_apply, laurentChar_apply, map_zpow₀, algebraMap_const_laurentSeries,
      HahnSeries.C_apply]
  simp only [qEmbed, RingHom.coe_comp, Function.comp_apply, qBaseDilation, qDilation,
    hahnTwistHom_apply]
  rw [algebraMap_ratFuncTwist, hahnTwistHom_apply, hahnMapRingHom_hahnTwist
    (algebraMap (RatFunc k) (LaurentSeries k))
    ((ratFuncScale b hb : RatFunc k →ₐ[k] RatFunc k) : RatFunc k →+* RatFunc k)
    (innerDilation b hb) _ _ (fun x => algebraMap_ratFuncScale b hb x) hχ]

end

end GaloisForLFunctions.HTGeometry
