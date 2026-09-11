import GaloisForLFunctions.HTGeometry.GomesTruncatedJetUnipotentLogEquiv
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeArcTransport

/-!
# Exact logarithm and exponential calculus inside the existing arc geometry

The established faithful arc embedding transports the terminating polynomial
logarithm and exponential. Thus the same intrinsic additive coordinates
control both actual matrix symmetries and their geometric arc units.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The literal finite exponential commutes with the existing geometric arc embedding. -/
theorem gomesTruncatedJetArcEmbedding_exponential (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    gomesTruncatedJetArcEmbedding n z (gomesTruncatedJetNilpotentExponential n z E) =
      Polynomial.aeval (gomesTruncatedJetArcEmbedding n z E.val)
        (PowerSeries.trunc (n + 1) (PowerSeries.exp ℂ)) :=
  (Polynomial.aeval_algHom_apply (gomesTruncatedJetArcEmbedding n z) E.val _).symm

/-- Exponentiating an actual nilpotent symmetry gives the literal polynomial exponential arc unit. -/
theorem gomesTruncatedJetGaugeArcHom_exponential (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    (gomesTruncatedJetGaugeArcHom n z (gomesTruncatedJetUnipotentExponential n z E).val).val =
      Polynomial.aeval (gomesTruncatedJetArcEmbedding n z E.val)
        (PowerSeries.trunc (n + 1) (PowerSeries.exp ℂ)) := by
  have h : ((gomesTruncatedJetInternalUnitsEquiv n z).symm
      (gomesTruncatedJetUnipotentExponential n z E).val).val =
      gomesTruncatedJetNilpotentExponential n z E := by
    apply Subtype.ext
    exact gomesTruncatedJetNilpotentExponentialGauge_val n z E
  change gomesTruncatedJetArcEmbedding n z
    (((gomesTruncatedJetInternalUnitsEquiv n z).symm
      (gomesTruncatedJetUnipotentExponential n z E).val).val) = _
  rw [h, gomesTruncatedJetArcEmbedding_exponential]

/-- The actual symmetry logarithm becomes the literal terminating logarithm of its arc unit. -/
theorem gomesTruncatedJetArcEmbedding_logarithm (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) :
    gomesTruncatedJetArcEmbedding n z (gomesTruncatedJetUnipotentLogarithm n z u).val =
      Polynomial.aeval ((gomesTruncatedJetGaugeArcHom n z u.val).val - 1)
        (gomesFiniteFockLogarithmPolynomial (n + 1)) := by
  change gomesTruncatedJetArcEmbedding n z
    (Polynomial.aeval (((gomesTruncatedJetInternalUnitsEquiv n z).symm u.val).val - 1)
      (gomesFiniteFockLogarithmPolynomial (n + 1))) = _
  rw [← Polynomial.aeval_algHom_apply, map_sub, map_one]
  rfl

/-- In geometric arc coordinates, the terminating logarithm recovers every actual nilpotent symmetry from its exponential. -/
theorem gomesTruncatedJetArc_logarithm_exponential (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    Polynomial.aeval
      (Polynomial.aeval (gomesTruncatedJetArcEmbedding n z E.val)
        (PowerSeries.trunc (n + 1) (PowerSeries.exp ℂ)) - 1)
      (gomesFiniteFockLogarithmPolynomial (n + 1)) = gomesTruncatedJetArcEmbedding n z E.val := by
  have h := congrArg (fun F : gomesTruncatedJetNilpotentSpace n z =>
    gomesTruncatedJetArcEmbedding n z F.val) (gomesTruncatedJetUnipotentLogarithm_exponential n z E)
  rw [gomesTruncatedJetArcEmbedding_logarithm, gomesTruncatedJetGaugeArcHom_exponential] at h
  exact h

/-- Exponentiating the terminating arc logarithm recovers every actual unipotent arc unit. -/
theorem gomesTruncatedJetArc_exponential_logarithm (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) :
    Polynomial.aeval
      (Polynomial.aeval ((gomesTruncatedJetGaugeArcHom n z u.val).val - 1)
        (gomesFiniteFockLogarithmPolynomial (n + 1)))
      (PowerSeries.trunc (n + 1) (PowerSeries.exp ℂ)) =
      (gomesTruncatedJetGaugeArcHom n z u.val).val := by
  have h := congrArg (fun v : gomesTruncatedJetUnipotentGroup n z =>
    (gomesTruncatedJetGaugeArcHom n z v.val).val) (gomesTruncatedJetUnipotentExponential_logarithm n z u)
  rw [gomesTruncatedJetGaugeArcHom_exponential, gomesTruncatedJetArcEmbedding_logarithm] at h
  exact h

/-- Multiplication of actual unipotent arc units becomes addition of their terminating logarithms. -/
theorem gomesTruncatedJetArc_logarithm_mul (n : ℕ) (z : ℂ)
    (u v : gomesTruncatedJetUnipotentGroup n z) :
    Polynomial.aeval
      ((gomesTruncatedJetGaugeArcHom n z u.val).val * (gomesTruncatedJetGaugeArcHom n z v.val).val - 1)
      (gomesFiniteFockLogarithmPolynomial (n + 1)) =
    Polynomial.aeval ((gomesTruncatedJetGaugeArcHom n z u.val).val - 1)
        (gomesFiniteFockLogarithmPolynomial (n + 1)) +
      Polynomial.aeval ((gomesTruncatedJetGaugeArcHom n z v.val).val - 1)
        (gomesFiniteFockLogarithmPolynomial (n + 1)) := by
  have h : gomesTruncatedJetUnipotentLogarithm n z (u * v) =
      gomesTruncatedJetUnipotentLogarithm n z u + gomesTruncatedJetUnipotentLogarithm n z v :=
    congrArg Multiplicative.toAdd (map_mul (gomesTruncatedJetUnipotentLogHom n z) u v)
  have ha := congrArg (fun E : gomesTruncatedJetNilpotentSpace n z =>
    gomesTruncatedJetArcEmbedding n z E.val) h
  change gomesTruncatedJetArcEmbedding n z (gomesTruncatedJetUnipotentLogarithm n z (u * v)).val =
    gomesTruncatedJetArcEmbedding n z
      ((gomesTruncatedJetUnipotentLogarithm n z u).val + (gomesTruncatedJetUnipotentLogarithm n z v).val) at ha
  rw [map_add, gomesTruncatedJetArcEmbedding_logarithm,
    gomesTruncatedJetArcEmbedding_logarithm, gomesTruncatedJetArcEmbedding_logarithm] at ha
  simpa only [Subgroup.coe_mul, map_mul, Units.val_mul] using ha

/-- The geometric arc logarithm loses no information about any actual unipotent symmetry. -/
theorem gomesTruncatedJetArc_logarithm_injective (n : ℕ) (z : ℂ) :
    Function.Injective (fun u : gomesTruncatedJetUnipotentGroup n z =>
      Polynomial.aeval ((gomesTruncatedJetGaugeArcHom n z u.val).val - 1)
        (gomesFiniteFockLogarithmPolynomial (n + 1))) := by
  intro u v h
  apply (gomesTruncatedJetUnipotentLogEquiv n z).injective
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply gomesTruncatedJetArcEmbedding_injective n z
  change gomesTruncatedJetArcEmbedding n z (gomesTruncatedJetUnipotentLogarithm n z u).val =
    gomesTruncatedJetArcEmbedding n z (gomesTruncatedJetUnipotentLogarithm n z v).val
  simpa only [gomesTruncatedJetArcEmbedding_logarithm] using h

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
