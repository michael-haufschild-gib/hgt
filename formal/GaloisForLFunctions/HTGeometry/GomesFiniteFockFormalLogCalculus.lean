import GaloisForLFunctions.HTGeometry.GomesNormalizedFormalLogEquiv
import GaloisForLFunctions.HTGeometry.GomesFiniteFockTaylorLogarithm

/-!
# Full formal logarithm and exponential calculus under finite clock evaluation

The complete formal-unit logarithm laws descend through the existing finite
clock homomorphism. These identities hold in every matrix dimension, including
zero, and apply to all normalized formal units and all based coordinates.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Every based formal exponential becomes the literal finite exponential of its clock matrix. -/
theorem gomesFiniteFockBasedFormal_exponential (N : ℕ) (G : GomesBasedFormalSeries) :
    gomesFiniteFockFormalHom N (gomesBasedFormalExponential G) =
      Polynomial.aeval (gomesFiniteFockFormalHom N G.val) (PowerSeries.trunc N (PowerSeries.exp ℂ)) :=
  gomesFiniteFockFormalHom_subst N (PowerSeries.exp ℂ) G

/-- The logarithm of every normalized formal unit becomes the literal terminating matrix logarithm. -/
theorem gomesFiniteFockFormalUnit_logarithm (N : ℕ) (F : gomesNormalizedFormalUnitGroup) :
    gomesFiniteFockFormalHom N (PowerSeries.logOf F.val.val) =
      Polynomial.aeval (gomesFiniteFockFormalHom N F.val.val - 1)
        (gomesFiniteFockLogarithmPolynomial N) := by
  have h := gomesFiniteFockFormalHom_subst N (PowerSeries.log ℂ) (gomesNormalizedFormalUnitIncrement F)
  change gomesFiniteFockFormalHom N (PowerSeries.subst (F.val.val - 1) (PowerSeries.log ℂ)) =
    Polynomial.aeval (gomesFiniteFockFormalHom N (F.val.val - 1))
      (PowerSeries.trunc N (PowerSeries.log ℂ)) at h
  simpa only [PowerSeries.logOf_eq, gomesFiniteFockLogarithmPolynomial, map_sub, map_one] using h

/-- The finite logarithm changes multiplication into addition on every pair of evaluated formal units. -/
theorem gomesFiniteFockFormalUnits_logarithm_mul (N : ℕ) (F G : gomesNormalizedFormalUnitGroup) :
    Polynomial.aeval (gomesFiniteFockFormalHom N F.val.val * gomesFiniteFockFormalHom N G.val.val - 1)
        (gomesFiniteFockLogarithmPolynomial N) =
      Polynomial.aeval (gomesFiniteFockFormalHom N F.val.val - 1) (gomesFiniteFockLogarithmPolynomial N) +
      Polynomial.aeval (gomesFiniteFockFormalHom N G.val.val - 1) (gomesFiniteFockLogarithmPolynomial N) := by
  have h := gomesFiniteFockFormalUnit_logarithm N (F * G)
  change gomesFiniteFockFormalHom N (PowerSeries.logOf (F.val.val * G.val.val)) =
    Polynomial.aeval (gomesFiniteFockFormalHom N (F.val.val * G.val.val) - 1)
      (gomesFiniteFockLogarithmPolynomial N) at h
  rw [logOf_mul (gomesNormalizedFormalUnitGroup_constantCoeff F)
      (gomesNormalizedFormalUnitGroup_constantCoeff G), map_add, map_mul,
    gomesFiniteFockFormalUnit_logarithm, gomesFiniteFockFormalUnit_logarithm] at h
  exact h.symm

/-- The terminating logarithm inverts the terminating exponential on every evaluated based formal coordinate. -/
theorem gomesFiniteFockBasedFormal_logarithm_exponential (N : ℕ) (G : GomesBasedFormalSeries) :
    Polynomial.aeval
        (Polynomial.aeval (gomesFiniteFockFormalHom N G.val) (PowerSeries.trunc N (PowerSeries.exp ℂ)) - 1)
        (gomesFiniteFockLogarithmPolynomial N) = gomesFiniteFockFormalHom N G.val := by
  have h := gomesFiniteFockFormalUnit_logarithm N (gomesBasedFormalExponentialUnit G)
  rw [gomesBasedFormalExponentialUnit_val,
    show PowerSeries.logOf (gomesBasedFormalExponential G) = G.val from gomesFormalSeries_logOf_exp_subst G,
    gomesFiniteFockBasedFormal_exponential] at h
  exact h.symm

/-- The terminating exponential inverts the terminating logarithm on every evaluated normalized formal unit. -/
theorem gomesFiniteFockFormalUnit_exponential_logarithm (N : ℕ) (F : gomesNormalizedFormalUnitGroup) :
    Polynomial.aeval
        (Polynomial.aeval (gomesFiniteFockFormalHom N F.val.val - 1) (gomesFiniteFockLogarithmPolynomial N))
        (PowerSeries.trunc N (PowerSeries.exp ℂ)) = gomesFiniteFockFormalHom N F.val.val := by
  have hF := congrArg (fun u : gomesNormalizedFormalUnitGroup => u.val.val)
    (gomesNormalizedFormalExponential_log F)
  rw [gomesBasedFormalExponentialUnit_val] at hF
  have h := congrArg (gomesFiniteFockFormalHom N) hF
  rw [gomesFiniteFockBasedFormal_exponential] at h
  change Polynomial.aeval (gomesFiniteFockFormalHom N (PowerSeries.logOf F.val.val))
    (PowerSeries.trunc N (PowerSeries.exp ℂ)) = gomesFiniteFockFormalHom N F.val.val at h
  rw [gomesFiniteFockFormalUnit_logarithm] at h
  exact h

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
