import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.EpsteinLatticeDecomposition
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMass
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.SquareTorusDirichlet

/-!
# The scalar Narain Dirichlet series at arbitrary target moduli

Primitive scalar coordinates separate the two positive quadratic forms.
The zero-winding sector cancels the axis omitted by positive winding scale.
Absolute convergence justifies every infinite-sum reindexing.
-/

open Complex RHTower RHTower.HeckeFactorization

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

noncomputable section

/-- The nonvacuum scalar charge term for the actual Narain mass. -/
def narainDirichletTerm (ρ σ : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (q : NonzeroScalarCharge) : ℂ := (narainMassSq ρ σ q.val : ℂ) ^ (-s)

private def latticeReflect : {p : ℤ × ℤ // p ≠ (0, 0)} ≃
    {p : ℤ × ℤ // p ≠ (0, 0)} where
  toFun p := ⟨(p.val.1, -p.val.2), by
    intro h
    apply p.property
    exact Prod.ext (congrArg Prod.fst h) (by simpa using congrArg Prod.snd h)⟩
  invFun p := ⟨(p.val.1, -p.val.2), by
    intro h
    apply p.property
    exact Prod.ext (congrArg Prod.fst h) (by simpa using congrArg Prod.snd h)⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

private def scalarParameterOrder : (ℕ × ℤ) × D4BMPrimitiveIntegerPair ≃ ScalarCharge :=
  (show (ℕ × ℤ) × D4BMPrimitiveIntegerPair ≃ (ℕ × D4BMPrimitiveIntegerPair) × ℤ from
    { toFun := fun t => ((t.1.1, t.2), t.1.2)
      invFun := fun t => ((t.1.1, t.2), t.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans scalarChargeEquiv

private theorem mass_zeroWinding (ρ σ : D4BMUpperHalfPlaneCoordinate) (p : ℤ × ℤ) :
    narainMassSq ρ σ (p, (0, 0)) =
      (d4BMPoincareQuadratic σ (p.1, -p.2) / σ.y) / ρ.y := by
  have h : narainMassSq ρ σ (p, (0, 0)) =
      targetQuadratic σ ((p.1 : ℝ), (p.2 : ℝ)) / (ρ.y * σ.y) := by
    simp only [narainMassSq, Int.cast_zero, mul_zero, add_zero, sub_zero, neg_zero]
    simp only [targetQuadratic, mul_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]
  rw [h, targetQuadratic_poincare]
  ring

private theorem zeroWindingTerm (ρ σ : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : {p : ℤ × ℤ // p ≠ (0, 0)}) :
    narainDirichletTerm ρ σ s (windingSplit (Sum.inl p)) =
      (ρ.y : ℂ) ^ s * epsteinTerm σ s (latticeReflect p) := by
  change (narainMassSq ρ σ (p.val, (0, 0)) : ℂ) ^ (-s) = _
  rw [mass_zeroWinding, Sieve.ofReal_div_cpow_eq_mul_cpow_neg
    (div_pos (d4BMPoincareQuadratic_pos σ (latticeReflect p).val
      (latticeReflect p).property) σ.y_pos) ρ.y_pos, neg_neg]
  rw [epsteinTerm, epsteinWeight_eq_div_cpow σ s _ (latticeReflect p).property]
  exact mul_comm _ _

private theorem scalarTerm_parameters (ρ σ : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (t : (ℕ × ℤ) × D4BMPrimitiveIntegerPair) :
    (narainMassSq ρ σ (scalarParameterOrder t).val : ℂ) ^ (-s) =
      halfEpsteinTerm ρ s t.1 * d4BMPoincareSeed σ s
        (d4BMPrimitiveIntegerPairReflectEquiv t.2) := by
  have hp : ((t.1.1 : ℤ) + 1, t.1.2) ≠ (0, 0) := by
    intro h; have := congrArg Prod.fst h; dsimp at this; omega
  have ha := (d4BMPrimitiveIntegerPairReflectEquiv t.2).pair_ne_zero
  change (narainMassSq ρ σ (scalarParameters t.1.1 t.2 t.1.2) : ℂ) ^ (-s) = _
  rw [narainMassSq_scalarParameters, targetQuadratic_poincare,
    ← epsteinWeight_primitive]
  change ((d4BMPoincareQuadratic σ (d4BMPrimitiveIntegerPairReflectEquiv t.2).pair *
      d4BMPoincareQuadratic ρ ((t.1.1 : ℤ) + 1, t.1.2) / (ρ.y * σ.y) : ℝ) : ℂ) ^ (-s) = _
  have hfactor : d4BMPoincareQuadratic σ (d4BMPrimitiveIntegerPairReflectEquiv t.2).pair *
      d4BMPoincareQuadratic ρ ((t.1.1 : ℤ) + 1, t.1.2) / (ρ.y * σ.y) =
      (d4BMPoincareQuadratic ρ ((t.1.1 : ℤ) + 1, t.1.2) / ρ.y) *
        (d4BMPoincareQuadratic σ (d4BMPrimitiveIntegerPairReflectEquiv t.2).pair / σ.y) := by ring
  rw [hfactor, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
    (div_pos (d4BMPoincareQuadratic_pos ρ _ hp) ρ.y_pos).le
    (div_pos (d4BMPoincareQuadratic_pos σ _ ha) σ.y_pos).le]
  rw [halfEpsteinTerm, epsteinWeight_eq_div_cpow ρ s _ hp,
    epsteinWeight_eq_div_cpow σ s _ ha]

private theorem summable_scalarWindingTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun q : ScalarCharge => (narainMassSq ρ σ q.val : ℂ) ^ (-s)) := by
  apply scalarParameterOrder.summable_iff.mp
  simp only [Function.comp_def, scalarTerm_parameters]
  exact summable_mul_of_summable_norm (summable_halfEpsteinTerm ρ hs).norm
    ((summable_d4BMPoincareSeed σ ⟨s, hs⟩).comp_injective
      d4BMPrimitiveIntegerPairReflectEquiv.injective).norm

private theorem scalarWindingTerm_sum (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' q : ScalarCharge, (narainMassSq ρ σ q.val : ℂ) ^ (-s)) =
      (∑' t, halfEpsteinTerm ρ s t) * ∑' a, d4BMPoincareSeed σ s a := by
  rw [← scalarParameterOrder.tsum_eq
    (fun q : ScalarCharge => (narainMassSq ρ σ q.val : ℂ) ^ (-s))]
  simp only [scalarTerm_parameters]
  rw [← tsum_mul_tsum_of_summable_norm (summable_halfEpsteinTerm ρ hs).norm
    ((summable_d4BMPoincareSeed σ ⟨s, hs⟩).comp_injective
      d4BMPrimitiveIntegerPairReflectEquiv.injective).norm,
    d4BMPrimitiveIntegerPairReflectEquiv.tsum_eq (d4BMPoincareSeed σ s)]

private theorem summable_narainZeroWinding (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p => narainDirichletTerm ρ σ s (windingSplit (Sum.inl p))) := by
  have h := ((summable_epsteinTerm σ hs).comp_injective latticeReflect.injective).mul_left
    ((ρ.y : ℂ) ^ s)
  exact h.congr fun p => (zeroWindingTerm ρ σ s p).symm

/-- Absolute convergence of the scalar mass Dirichlet series at every target modulus. -/
theorem summable_narainDirichletTerm (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) : Summable (narainDirichletTerm ρ σ s) := by
  apply windingSplit.summable_iff.mp
  exact Summable.sum (narainDirichletTerm ρ σ s ∘ windingSplit)
    (summable_narainZeroWinding ρ σ hs) (summable_scalarWindingTerm ρ σ hs)

private theorem narainDirichlet_split (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' q, narainDirichletTerm ρ σ s q) =
      (ρ.y : ℂ) ^ s * (∑' p, epsteinTerm σ s p) +
        (∑' t, halfEpsteinTerm ρ s t) * ∑' a, d4BMPoincareSeed σ s a := by
  rw [← windingSplit.tsum_eq (narainDirichletTerm ρ σ s)]
  have hsum := Summable.tsum_sum (f := narainDirichletTerm ρ σ s ∘ windingSplit)
    (summable_narainZeroWinding ρ σ hs) (summable_scalarWindingTerm ρ σ hs)
  change (∑' q, (narainDirichletTerm ρ σ s ∘ windingSplit) q) = _
  rw [hsum]
  simp only [Function.comp_apply, zeroWindingTerm, tsum_mul_left]
  rw [latticeReflect.tsum_eq (epsteinTerm σ s)]
  exact congrArg ((ρ.y : ℂ) ^ s * (∑' p, epsteinTerm σ s p) + ·)
    (scalarWindingTerm_sum ρ σ hs)

/-- The actual scalar mass series equals the product of two primitive Eisenstein series. -/
theorem narainDirichlet_eq_eisenstein_product (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' q, narainDirichletTerm ρ σ s q) = 2 * riemannZeta (2 * s) *
      d4BMRawEisensteinPoincareSeries ρ ⟨s, hs⟩ *
        d4BMRawEisensteinPoincareSeries σ ⟨s, hs⟩ := by
  rw [narainDirichlet_split ρ σ hs, epstein_eq_eisenstein σ hs,
    halfEpstein_eq_eisenstein_sub ρ hs]
  simp only [d4BMRawEisensteinPoincareSeries]
  ring

end

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.summable_narainDirichletTerm
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainDirichlet_eq_eisenstein_product
