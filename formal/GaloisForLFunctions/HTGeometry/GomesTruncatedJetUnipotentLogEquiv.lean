import GaloisForLFunctions.HTGeometry.GomesTruncatedJetFormalLifts

/-!
# The entire actual unipotent gauge group has exact additive logarithmic coordinates

The formal calculus descends through proved lifts of every actual matrix.
Finite exponential and logarithm are inverse on the full groups, and the
logarithm turns matrix multiplication into addition in the nilpotent space.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The literal terminating logarithm recovers every actual nilpotent coordinate from its exponential. -/
theorem gomesTruncatedJetUnipotentLogarithm_exponential (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    gomesTruncatedJetUnipotentLogarithm n z (gomesTruncatedJetUnipotentExponential n z E) = E := by
  obtain ⟨G, hG⟩ := gomesTruncatedJetNilpotentSpace_formal_lift n z E
  apply Subtype.ext
  apply Subtype.ext
  rw [gomesTruncatedJetUnipotentLogarithm_val, gomesTruncatedJetUnipotentExponential_val, ← hG]
  exact gomesFiniteFockBasedFormal_logarithm_exponential (n + 1) G

/-- The literal terminating exponential recovers every actual unipotent symmetry from its logarithm. -/
theorem gomesTruncatedJetUnipotentExponential_logarithm (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) :
    gomesTruncatedJetUnipotentExponential n z (gomesTruncatedJetUnipotentLogarithm n z u) = u := by
  obtain ⟨F, hF⟩ := gomesTruncatedJetUnipotentGroup_formal_lift n z u
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [gomesTruncatedJetUnipotentExponential_val, gomesTruncatedJetUnipotentLogarithm_val, ← hF]
  exact gomesFiniteFockFormalUnit_exponential_logarithm (n + 1) F

/-- The full finite logarithm is a homomorphism from actual matrix multiplication to coordinate addition. -/
def gomesTruncatedJetUnipotentLogHom (n : ℕ) (z : ℂ) :
    gomesTruncatedJetUnipotentGroup n z →* Multiplicative (gomesTruncatedJetNilpotentSpace n z) where
  toFun u := Multiplicative.ofAdd (gomesTruncatedJetUnipotentLogarithm n z u)
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change (gomesTruncatedJetUnipotentLogarithm n z 1).val.val = 0
    rw [gomesTruncatedJetUnipotentLogarithm_val]
    change Polynomial.aeval ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - 1)
      (gomesFiniteFockLogarithmPolynomial (n + 1)) = 0
    rw [sub_self, ← Polynomial.coeff_zero_eq_aeval_zero', gomesFiniteFockLogarithmPolynomial,
      PowerSeries.coeff_trunc, if_pos (Nat.succ_pos n),
      PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_log, map_zero]
  map_mul' u v := by
    obtain ⟨F, hF⟩ := gomesTruncatedJetUnipotentGroup_formal_lift n z u
    obtain ⟨G, hG⟩ := gomesTruncatedJetUnipotentGroup_formal_lift n z v
    apply Subtype.ext
    apply Subtype.ext
    change (gomesTruncatedJetUnipotentLogarithm n z (u * v)).val.val =
      (gomesTruncatedJetUnipotentLogarithm n z u).val.val +
      (gomesTruncatedJetUnipotentLogarithm n z v).val.val
    rw [gomesTruncatedJetUnipotentLogarithm_val, gomesTruncatedJetUnipotentLogarithm_val,
      gomesTruncatedJetUnipotentLogarithm_val]
    change Polynomial.aeval (u.val.val.val * v.val.val.val - 1) (gomesFiniteFockLogarithmPolynomial (n + 1)) =
      Polynomial.aeval (u.val.val.val - 1) (gomesFiniteFockLogarithmPolynomial (n + 1)) +
      Polynomial.aeval (v.val.val.val - 1) (gomesFiniteFockLogarithmPolynomial (n + 1))
    rw [← hF, ← hG]
    exact gomesFiniteFockFormalUnits_logarithm_mul (n + 1) F G

/-- The logarithmic homomorphism uses precisely the already constructed terminating logarithm. -/
theorem gomesTruncatedJetUnipotentLogHom_apply (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) :
    Multiplicative.toAdd (gomesTruncatedJetUnipotentLogHom n z u) =
      gomesTruncatedJetUnipotentLogarithm n z u := rfl

/-- Exact logarithmic coordinates distinguish every actual unipotent gauge transformation. -/
theorem gomesTruncatedJetUnipotentLogHom_injective (n : ℕ) (z : ℂ) :
    Function.Injective (gomesTruncatedJetUnipotentLogHom n z) := by
  intro u v h
  have he := congrArg (fun E => gomesTruncatedJetUnipotentExponential n z (Multiplicative.toAdd E)) h
  simpa only [gomesTruncatedJetUnipotentLogHom_apply, gomesTruncatedJetUnipotentExponential_logarithm] using he

/-- Every actual nilpotent joint coordinate occurs as the logarithm of an actual unipotent symmetry. -/
theorem gomesTruncatedJetUnipotentLogHom_surjective (n : ℕ) (z : ℂ) :
    Function.Surjective (gomesTruncatedJetUnipotentLogHom n z) := by
  intro E
  refine ⟨gomesTruncatedJetUnipotentExponential n z (Multiplicative.toAdd E), ?_⟩
  apply Multiplicative.toAdd.injective
  exact gomesTruncatedJetUnipotentLogarithm_exponential n z _

/-- The full actual unipotent gauge group is exactly the additive group of its nilpotent joint matrix space. -/
def gomesTruncatedJetUnipotentLogEquiv (n : ℕ) (z : ℂ) :
    gomesTruncatedJetUnipotentGroup n z ≃* Multiplicative (gomesTruncatedJetNilpotentSpace n z) :=
  MulEquiv.ofBijective (gomesTruncatedJetUnipotentLogHom n z)
    ⟨gomesTruncatedJetUnipotentLogHom_injective n z, gomesTruncatedJetUnipotentLogHom_surjective n z⟩

/-- The inverse additive coordinate map is the literal terminating exponential. -/
theorem gomesTruncatedJetUnipotentLogEquiv_symm (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    (gomesTruncatedJetUnipotentLogEquiv n z).symm (Multiplicative.ofAdd E) =
      gomesTruncatedJetUnipotentExponential n z E := by
  apply (gomesTruncatedJetUnipotentLogEquiv n z).injective
  rw [MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  exact (gomesTruncatedJetUnipotentLogarithm_exponential n z E).symm

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
