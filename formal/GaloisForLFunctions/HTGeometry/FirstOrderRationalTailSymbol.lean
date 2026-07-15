import GaloisForLFunctions.HTGeometry.VerticalLaurentSymbol

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

/-- Polynomial-ring realization of a phase-coordinate base change followed by `v ↦ a*v`. -/
def verticalTransportPolynomialRingHom
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) (a : K₀) : K₁[X] →+* K₀[X] :=
  Polynomial.eval₂RingHom (Polynomial.C.comp σ) (Polynomial.C a * Polynomial.X)

@[simp]
theorem verticalTransportPolynomialRingHom_apply
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) (a : K₀) (p : K₁[X]) :
    verticalTransportPolynomialRingHom σ a p = verticalTransportPolynomial σ a p := by
  change Polynomial.eval₂ (Polynomial.C.comp σ) (Polynomial.C a * Polynomial.X) p =
    Polynomial.eval₂ Polynomial.C (Polynomial.C a * Polynomial.X) (p.map σ)
  exact (Polynomial.eval₂_map σ Polynomial.C (Polynomial.C a * Polynomial.X)).symm

theorem verticalTransportPolynomialRingHom_injective
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0) :
    Function.Injective (verticalTransportPolynomialRingHom σ a) := by
  intro p q hpq
  apply sub_eq_zero.mp
  by_contra hpq0
  apply verticalTransportPolynomial_ne_zero σ ha hpq0
  rw [← verticalTransportPolynomialRingHom_apply, map_sub, hpq, sub_self]

def verticalTransportNonZeroDivisors
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0) :
    nonZeroDivisors K₁[X] ≤
      (nonZeroDivisors K₀[X]).comap (verticalTransportPolynomialRingHom σ a) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (verticalTransportPolynomialRingHom_injective σ ha)

/-- A nonzero vertical Jacobian gives an injective homomorphism on rational functions in the
first-jet coordinate. -/
def verticalTransportRatFuncRingHom
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) (a : K₀) (ha : a ≠ 0) : RatFunc K₁ →+* RatFunc K₀ :=
  RatFunc.mapRingHom (verticalTransportPolynomialRingHom σ a)
    (verticalTransportNonZeroDivisors σ ha)

theorem verticalTransportRatFuncRingHom_injective
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0) :
    Function.Injective (verticalTransportRatFuncRingHom σ a ha) := by
  unfold verticalTransportRatFuncRingHom
  exact RatFunc.map_injective _ (verticalTransportNonZeroDivisors σ ha)
    (verticalTransportPolynomialRingHom_injective σ ha)

theorem verticalTransportRatFuncRingHom_apply
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0) (H : RatFunc K₁) :
    verticalTransportRatFuncRingHom σ a ha H =
      algebraMap K₀[X] (RatFunc K₀) (verticalTransportPolynomial σ a H.num) /
        algebraMap K₀[X] (RatFunc K₀) (verticalTransportPolynomial σ a H.denom) := by
  change RatFunc.map (verticalTransportPolynomialRingHom σ a)
    (verticalTransportNonZeroDivisors σ ha) H = _
  rw [RatFunc.map_apply]
  simp only [verticalTransportPolynomialRingHom_apply]

/-- Equality of transported rational first-order observables gives the cross-multiplied
polynomial identity needed for Laurent-symbol extraction. -/
theorem num_denom_cross_of_verticalTransport_eq
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0)
    {H₀ : RatFunc K₀} {H₁ : RatFunc K₁}
    (htransport : verticalTransportRatFuncRingHom σ a ha H₁ = H₀) :
    H₀.num * verticalTransportPolynomial σ a H₁.denom =
      verticalTransportPolynomial σ a H₁.num * H₀.denom := by
  have hfrac :
      algebraMap K₀[X] (RatFunc K₀) H₀.num /
          algebraMap K₀[X] (RatFunc K₀) H₀.denom =
        algebraMap K₀[X] (RatFunc K₀) (verticalTransportPolynomial σ a H₁.num) /
          algebraMap K₀[X] (RatFunc K₀) (verticalTransportPolynomial σ a H₁.denom) := by
    rw [RatFunc.num_div_denom]
    exact htransport.symm.trans (verticalTransportRatFuncRingHom_apply σ ha H₁)
  have hden₀ : algebraMap K₀[X] (RatFunc K₀) H₀.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero H₀.denom_ne_zero
  have hden₁ : algebraMap K₀[X] (RatFunc K₀)
      (verticalTransportPolynomial σ a H₁.denom) ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      (verticalTransportPolynomial_ne_zero σ ha H₁.denom_ne_zero)
  have hcross := (div_eq_div_iff hden₀ hden₁).mp hfrac
  apply RatFunc.algebraMap_injective
  simpa only [map_mul] using hcross

/-- Laurent weight of an arbitrary rational first-order observable. -/
def verticalRatFuncLaurentWeight {K : Type*} [Field K] (H : RatFunc K) : ℤ :=
  verticalLaurentWeight H.num H.denom

/-- Leading Laurent symbol of a nonzero rational first-order observable. -/
def verticalRatFuncLaurentCoefficient {K : Type*} [Field K] (H : RatFunc K) : K :=
  verticalLaurentCoefficient H.num H.denom

/-- **First-order Laurent-weight extraction.**  Transport of a nonzero rational first-order
observable preserves its integer vertical weight. -/
theorem verticalRatFuncLaurentWeight_eq_of_transport
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0)
    {H₀ : RatFunc K₀} {H₁ : RatFunc K₁}
    (hH₀ : H₀ ≠ 0) (hH₁ : H₁ ≠ 0)
    (htransport : verticalTransportRatFuncRingHom σ a ha H₁ = H₀) :
    verticalRatFuncLaurentWeight H₀ = verticalRatFuncLaurentWeight H₁ := by
  exact verticalLaurentWeight_eq_of_transport_fraction σ ha
    (RatFunc.num_ne_zero hH₀) H₀.denom_ne_zero
    (RatFunc.num_ne_zero hH₁) H₁.denom_ne_zero
    (num_denom_cross_of_verticalTransport_eq σ ha htransport)

/-- **First-order leading-symbol extraction.**  The leading coefficient of a transported
rational first-order observable obeys the tensor law with its extracted integer weight. -/
theorem verticalRatFuncLaurentCoefficient_eq_zpow_of_transport
    {K₀ K₁ : Type*} [Field K₀] [Field K₁]
    (σ : K₁ →+* K₀) {a : K₀} (ha : a ≠ 0)
    {H₀ : RatFunc K₀} {H₁ : RatFunc K₁}
    (hH₀ : H₀ ≠ 0) (hH₁ : H₁ ≠ 0)
    (htransport : verticalTransportRatFuncRingHom σ a ha H₁ = H₀) :
    verticalRatFuncLaurentCoefficient H₀ =
      σ (verticalRatFuncLaurentCoefficient H₁) *
        a ^ verticalRatFuncLaurentWeight H₁ := by
  exact verticalLaurentCoefficient_eq_zpow_of_transport_fraction σ ha
    (RatFunc.num_ne_zero hH₀) H₀.denom_ne_zero
    (RatFunc.num_ne_zero hH₁) H₁.denom_ne_zero
    (num_denom_cross_of_verticalTransport_eq σ ha htransport)

/-- A phasewise rational first-order chain has one common Laurent weight at every depth. -/
theorem verticalRatFuncLaurentWeight_eq_zeroPhase
    {K : Type*} [Field K]
    (σ : ℕ → K →+* K) (a : ℕ → K) (ha : ∀ i, a i ≠ 0)
    (H : ℕ → RatFunc K) (hH : ∀ i, H i ≠ 0)
    (htransport : ∀ i,
      verticalTransportRatFuncRingHom (σ i) (a i) (ha i) (H (i + 1)) = H i) :
    ∀ i, verticalRatFuncLaurentWeight (H i) =
      verticalRatFuncLaurentWeight (H 0) := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      exact (verticalRatFuncLaurentWeight_eq_of_transport (σ i) (ha i)
        (hH i) (hH (i + 1)) (htransport i)).symm.trans ih

/-- The leading coefficients extracted from a phasewise first-order rational chain form the
transported integer tensor chain claimed in Theorem A. -/
theorem verticalRatFuncLaurentCoefficient_phaseChain
    {K : Type*} [Field K]
    (σ : ℕ → K →+* K) (a : ℕ → K) (ha : ∀ i, a i ≠ 0)
    (H : ℕ → RatFunc K) (hH : ∀ i, H i ≠ 0)
    (htransport : ∀ i,
      verticalTransportRatFuncRingHom (σ i) (a i) (ha i) (H (i + 1)) = H i) :
    ∀ i,
      verticalRatFuncLaurentCoefficient (H i) =
        σ i (verticalRatFuncLaurentCoefficient (H (i + 1))) *
          a i ^ verticalRatFuncLaurentWeight (H 0) := by
  intro i
  rw [← verticalRatFuncLaurentWeight_eq_zeroPhase σ a ha H hH htransport (i + 1)]
  exact verticalRatFuncLaurentCoefficient_eq_zpow_of_transport (σ i) (ha i)
    (hH i) (hH (i + 1)) (htransport i)

end

end GaloisForLFunctions.HTGeometry
