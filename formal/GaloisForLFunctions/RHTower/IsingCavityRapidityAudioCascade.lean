import GaloisForLFunctions.RHTower.PrimeIsingTreeCavity

/-!
# Ising cavity rapidity and audio-scattering cascade

The scalar Ising cavity map

`T_c(r) = (c+r)/(1+cr)`

is also the normalized collinear velocity-addition law of special relativity and the real
reflection-coefficient cascade used in passive wave-digital and lattice-filter descriptions.
Serial sections therefore form a Möbius semigroup: the effective coefficient is

`c ⊕ d = (c+d)/(1+cd)`.

This `[BRIDGE]` formalizes the cascade on the physical open disk.  It also evaluates every finite
prime Ising tree at the common zero-field point.  Since every centered prime field equals one at
`z=0`, the partition is exactly `2 * ∏_edges (1+c_e)`, a strictly nonzero source-independent
normalization.  The result supplies the active locally uniform tree route with a canonical central
normalization; it does not construct the cofinal source tree or its `XiC` comparison.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Serial/rapidity composition of normalized ferromagnetic couplings. -/
def FerromagneticCoupling.compose
    (c d : FerromagneticCoupling) : FerromagneticCoupling where
  coefficient := (c.coefficient + d.coefficient) /
    (1 + c.coefficient * d.coefficient)
  nonneg := by
    apply div_nonneg
    · exact add_nonneg c.nonneg d.nonneg
    · nlinarith [mul_nonneg c.nonneg d.nonneg]
  le_one := by
    apply (div_le_one (by nlinarith [mul_nonneg c.nonneg d.nonneg])).2
    nlinarith [mul_nonneg (sub_nonneg.mpr c.le_one) (sub_nonneg.mpr d.le_one)]

/-- Einstein/reflection-coefficient addition: serial cavity sections collapse to one section on
the physical open disk.  The disk condition excludes the totalized-field pole cases. -/
theorem cavityTransfer_compose
    (c d : FerromagneticCoupling) {r : ℂ} (hr : ‖r‖ < 1) :
    cavityTransfer c (cavityTransfer d r) =
      cavityTransfer (c.compose d) r := by
  have hd := cavityTransfer_den_ne_zero d hr
  have he := cavityTransfer_den_ne_zero (c.compose d) hr
  have hreal : (1 + c.coefficient * d.coefficient : ℝ) ≠ 0 := by
    nlinarith [mul_nonneg c.nonneg d.nonneg]
  have hrealC : (1 + (c.coefficient : ℂ) * d.coefficient) ≠ 0 := by
    exact_mod_cast hreal
  have heCoeff : ((c.compose d).coefficient : ℂ) =
      ((c.coefficient : ℂ) + d.coefficient) /
        (1 + (c.coefficient : ℂ) * d.coefficient) := by
    simp [FerromagneticCoupling.compose]
  have houter : 1 + (c.coefficient : ℂ) * cavityTransfer d r ≠ 0 := by
    rw [cavityTransfer]
    rw [show 1 + (c.coefficient : ℂ) *
        (((d.coefficient : ℂ) + r) / (1 + (d.coefficient : ℂ) * r)) =
      ((1 + (c.coefficient : ℂ) * d.coefficient) +
          ((c.coefficient : ℂ) + d.coefficient) * r) /
        (1 + (d.coefficient : ℂ) * r) by field_simp [hd]; ring]
    apply div_ne_zero
    · rw [show (1 + (c.coefficient : ℂ) * d.coefficient) +
          ((c.coefficient : ℂ) + d.coefficient) * r =
        (1 + (c.coefficient : ℂ) * d.coefficient) *
          (1 + (((c.compose d).coefficient : ℝ) : ℂ) * r) by
          simp [FerromagneticCoupling.compose]
          field_simp [hrealC]]
      exact mul_ne_zero hrealC he
    · exact hd
  have hcombined : (1 + (c.coefficient : ℂ) * d.coefficient) +
      ((c.coefficient : ℂ) + d.coefficient) * r ≠ 0 := by
    rw [show (1 + (c.coefficient : ℂ) * d.coefficient) +
          ((c.coefficient : ℂ) + d.coefficient) * r =
        (1 + (c.coefficient : ℂ) * d.coefficient) *
          (1 + (((c.compose d).coefficient : ℝ) : ℂ) * r) by
          simp [FerromagneticCoupling.compose]
          field_simp [hrealC]]
    exact mul_ne_zero hrealC he
  calc
    cavityTransfer c (cavityTransfer d r) =
        (((c.coefficient : ℂ) + d.coefficient) +
            (1 + (c.coefficient : ℂ) * d.coefficient) * r) /
          ((1 + (c.coefficient : ℂ) * d.coefficient) +
            ((c.coefficient : ℂ) + d.coefficient) * r) := by
      rw [cavityTransfer, cavityTransfer]
      field_simp [hd, houter, hcombined]
      ring
    _ = cavityTransfer (c.compose d) r := by
      rw [cavityTransfer, heCoeff]
      field_simp [hrealC, he, hcombined]

mutual
  /-- Product of the zero-field factors `(1+c_e)` over all tree edges. -/
  def treeEdgeFactorProduct : PrimeIsingTree → ℝ
    | .node _ branches => forestEdgeFactorProduct branches

  /-- Product of the zero-field factors over a forest. -/
  def forestEdgeFactorProduct : PrimeIsingForest → ℝ
    | .nil => 1
    | .cons c child tail =>
        (1 + c.coefficient) * treeEdgeFactorProduct child *
          forestEdgeFactorProduct tail
end

mutual
  theorem treeEdgeFactorProduct_pos (T : PrimeIsingTree) :
      0 < treeEdgeFactorProduct T := by
    cases T with
    | node _ branches => exact forestEdgeFactorProduct_pos branches

  theorem forestEdgeFactorProduct_pos (F : PrimeIsingForest) :
      0 < forestEdgeFactorProduct F := by
    cases F with
    | nil => simp [forestEdgeFactorProduct]
    | cons c child tail =>
        simp only [forestEdgeFactorProduct]
        exact mul_pos (mul_pos (by linarith [c.nonneg])
          (treeEdgeFactorProduct_pos child))
          (forestEdgeFactorProduct_pos tail)
end

mutual
  /-- At common field one, spin-flip symmetry makes the two conditional tree weights equal to the
  edge-factor product. -/
  theorem treeConditionalWeights_one (T : PrimeIsingTree) :
      treeConditionalWeights (fun _ => 1) T =
        ((treeEdgeFactorProduct T : ℂ), (treeEdgeFactorProduct T : ℂ)) := by
    cases T with
    | node _ branches =>
        rw [treeConditionalWeights, forestConditionalFactors_one branches]
        simp [treeEdgeFactorProduct]

  theorem forestConditionalFactors_one (F : PrimeIsingForest) :
      forestConditionalFactors (fun _ => 1) F =
        ((forestEdgeFactorProduct F : ℂ), (forestEdgeFactorProduct F : ℂ)) := by
    cases F with
    | nil => simp [forestConditionalFactors, forestEdgeFactorProduct]
    | cons c child tail =>
        rw [forestConditionalFactors, treeConditionalWeights_one child,
          forestConditionalFactors_one tail]
        simp only [forestEdgeFactorProduct]
        push_cast
        ext <;> ring
end

/-- Exact zero-field partition value of an arbitrary finite ferromagnetic tree. -/
theorem treePartition_one (T : PrimeIsingTree) :
    treePartition (fun _ => 1) T = 2 * (treeEdgeFactorProduct T : ℂ) := by
  rw [treePartition, treeConditionalWeights_one]
  ring

/-- Every centered prime field is one at the centered origin. -/
theorem centeredPrimeLeeYangField_zero (p : Nat.Primes) :
    _root_.RHTower.centeredPrimeLeeYangField p 0 = 1 := by
  rw [_root_.RHTower.centeredPrimeLeeYangField, _root_.RHTower.centeredPrimeMark]
  simp

/-- Exact central normalization of every finite prime Ising tree. -/
theorem primeIsingTreePartition_zero (T : PrimeIsingTree) :
    primeIsingTreePartition T 0 = 2 * (treeEdgeFactorProduct T : ℂ) := by
  rw [primeIsingTreePartition]
  have hfields : (fun p => _root_.RHTower.centeredPrimeLeeYangField p 0) =
      (fun _ => 1) := by
    funext p
    exact centeredPrimeLeeYangField_zero p
  rw [hfields, treePartition_one]

/-- The explicit central value is strictly nonzero. -/
theorem primeIsingTreePartition_zero_ne_zero (T : PrimeIsingTree) :
    primeIsingTreePartition T 0 ≠ 0 := by
  rw [primeIsingTreePartition_zero]
  exact mul_ne_zero (by norm_num)
    (ofReal_ne_zero.mpr (treeEdgeFactorProduct_pos T).ne')

/-- Canonical unit-central normalization for the locally uniform source-comparison problem. -/
def centralNormalizedPrimeIsingTreePartition (T : PrimeIsingTree) (z : ℂ) : ℂ :=
  (primeIsingTreePartition T 0)⁻¹ * primeIsingTreePartition T z

@[simp] theorem centralNormalizedPrimeIsingTreePartition_zero (T : PrimeIsingTree) :
    centralNormalizedPrimeIsingTreePartition T 0 = 1 := by
  rw [centralNormalizedPrimeIsingTreePartition,
    inv_mul_cancel₀ (primeIsingTreePartition_zero_ne_zero T)]

/-- Central normalization changes no zero. -/
theorem centralNormalizedPrimeIsingTreePartition_eq_zero_iff
    (T : PrimeIsingTree) (z : ℂ) :
    centralNormalizedPrimeIsingTreePartition T z = 0 ↔
      primeIsingTreePartition T z = 0 := by
  rw [centralNormalizedPrimeIsingTreePartition, mul_eq_zero]
  simp [primeIsingTreePartition_zero_ne_zero T]

/-- The canonically normalized tree partition remains entire. -/
theorem differentiable_centralNormalizedPrimeIsingTreePartition (T : PrimeIsingTree) :
    Differentiable ℂ (centralNormalizedPrimeIsingTreePartition T) := by
  exact (differentiable_const _).mul (differentiable_primeIsingTreePartition T)

/-- Direct normalized-tree capstone.  The central scaling contributes neither zeros nor analytic
hypotheses, so locally uniform convergence of the normalized trees to `XiC` proves RH. -/
theorem riemannHypothesis_of_centralNormalizedPrimeIsingTreePartition_tendstoLocallyUniformly
    (T : ℕ → PrimeIsingTree)
    (hconv : TendstoLocallyUniformly
      (fun n => centralNormalizedPrimeIsingTreePartition (T n))
      _root_.RHTower.XiC atTop) :
    RiemannHypothesis := by
  apply _root_.RHTower.riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hconv
  · exact Filter.Eventually.of_forall
      (fun n => differentiable_centralNormalizedPrimeIsingTreePartition (T n))
  · exact Filter.Eventually.of_forall (fun n z hz =>
      primeIsingTreePartition_zero_im (T n)
        ((centralNormalizedPrimeIsingTreePartition_eq_zero_iff (T n) z).mp hz))

end


end GaloisForLFunctions.RHTower
