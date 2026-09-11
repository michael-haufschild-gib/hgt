import GaloisForLFunctions.HTGeometry.GomesNormalizedFormalUnits

/-!
# Formal logarithms give additive coordinates for the entire normalized unit group

The existing horizon logarithm multiplication law is a homomorphism on the
actual normalized formal-unit group. The full composition identities make it
bijective, with the substituted formal exponential as its inverse.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The full formal logarithm, as a homomorphism from multiplication to addition. -/
def gomesNormalizedFormalLogHom : gomesNormalizedFormalUnitGroup →* Multiplicative GomesBasedFormalSeries where
  toFun u := Multiplicative.ofAdd ⟨PowerSeries.logOf u.val.val, by
    change PowerSeries.constantCoeff (PowerSeries.logOf u.val.val) = 0
    exact PowerSeries.constantCoeff_logOf (gomesNormalizedFormalUnitGroup_constantCoeff u)⟩
  map_one' := by
    apply Subtype.ext
    change PowerSeries.logOf (1 : PowerSeries ℂ) = 0
    rw [PowerSeries.logOf_eq, sub_self]
    exact PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log
  map_mul' u v := by
    apply Subtype.ext
    change PowerSeries.logOf (u.val.val * v.val.val) =
      PowerSeries.logOf u.val.val + PowerSeries.logOf v.val.val
    exact logOf_mul (gomesNormalizedFormalUnitGroup_constantCoeff u)
      (gomesNormalizedFormalUnitGroup_constantCoeff v)

/-- The homomorphism retains the literal formal logarithm of the actual unit. -/
theorem gomesNormalizedFormalLogHom_val (u : gomesNormalizedFormalUnitGroup) :
    (Multiplicative.toAdd (gomesNormalizedFormalLogHom u)).val = PowerSeries.logOf u.val.val := rfl

/-- The logarithm of every based exponential is its complete formal coordinate. -/
theorem gomesNormalizedFormalLogHom_exponential (G : GomesBasedFormalSeries) :
    Multiplicative.toAdd (gomesNormalizedFormalLogHom (gomesBasedFormalExponentialUnit G)) = G := by
  apply Subtype.ext
  rw [gomesNormalizedFormalLogHom_val, gomesBasedFormalExponentialUnit_val]
  exact gomesFormalSeries_logOf_exp_subst G

/-- Exponentiating the logarithmic coordinate recovers every actual normalized unit. -/
theorem gomesNormalizedFormalExponential_log (u : gomesNormalizedFormalUnitGroup) :
    gomesBasedFormalExponentialUnit (Multiplicative.toAdd (gomesNormalizedFormalLogHom u)) = u := by
  apply Subtype.ext
  apply Units.ext
  rw [gomesBasedFormalExponentialUnit_val]
  change PowerSeries.subst (PowerSeries.logOf u.val.val) (PowerSeries.exp ℂ) = u.val.val
  have h := gomesFormalSeries_exp_subst_logOf_one_add (gomesNormalizedFormalUnitIncrement u)
  rw [gomesNormalizedFormalUnit_one_add_increment] at h
  exact h

/-- The full logarithmic coordinate distinguishes all normalized formal units. -/
theorem gomesNormalizedFormalLogHom_injective : Function.Injective gomesNormalizedFormalLogHom := by
  intro u v h
  have he := congrArg (fun G => gomesBasedFormalExponentialUnit (Multiplicative.toAdd G)) h
  simpa only [gomesNormalizedFormalExponential_log] using he

/-- Every based formal coordinate is realized by an actual normalized formal unit. -/
theorem gomesNormalizedFormalLogHom_surjective : Function.Surjective gomesNormalizedFormalLogHom := by
  intro G
  refine ⟨gomesBasedFormalExponentialUnit (Multiplicative.toAdd G), ?_⟩
  apply Multiplicative.toAdd.injective
  exact gomesNormalizedFormalLogHom_exponential _

/-- The entire normalized formal-unit group is equivalent to the additive group of based formal series. -/
def gomesNormalizedFormalLogEquiv :
    gomesNormalizedFormalUnitGroup ≃* Multiplicative GomesBasedFormalSeries :=
  MulEquiv.ofBijective gomesNormalizedFormalLogHom
    ⟨gomesNormalizedFormalLogHom_injective, gomesNormalizedFormalLogHom_surjective⟩

/-- The inverse logarithmic coordinate is the actual substituted formal exponential. -/
theorem gomesNormalizedFormalLogEquiv_symm (G : GomesBasedFormalSeries) :
    gomesNormalizedFormalLogEquiv.symm (Multiplicative.ofAdd G) = gomesBasedFormalExponentialUnit G := by
  apply gomesNormalizedFormalLogEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  exact (gomesNormalizedFormalLogHom_exponential G).symm

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
