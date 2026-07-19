import GaloisForLFunctions.RHTower.PoissonCoarseGrainingEnergy
import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureDyadicProjection
import GaloisForLFunctions.RHTower.XiSquaredEulerRayCubicAmplification

/-!
# Signature parity of aperture and Poisson response refinements

The true Möbius aperture gains a positive-semidefinite Hilbert innovation when its valuation-depth
mesh is refined.  The finite-resolution slab response has a different scale law.  Its Lorentzian
kernel increment vanishes on the diagonal and is strictly positive off it.  Consequently its
two-node matrix has an exact positive mirror-even channel and negative mirror-odd channel, and its
three-node determinant is strictly positive on distinct displacement nodes.

This gives an unconditional source-to-response classification.  A coarsening increment is not a
Hilbert Gram and its positive amplification eventually forces the three-node determinant positive.
But the actual fine-minus-coarse response refinement reverses the cubic: it has exactly one
negative channel and is an eventual negative amplifier against every fixed background.  The open
core is therefore the signature-converting map from the positive aperture innovation into this
indefinite response refinement, not the construction of the target negative cubic itself.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower.PoissonCoarseGrainingEnergy

/-- The change in the Lorentzian slab-response kernel between two resolutions. -/
def poissonScaleIncrement (a b x : ℝ) : ℝ :=
  lorentz b x - lorentz a x

/-- Exact spatial factorization of one Poisson scale increment. -/
theorem poissonScaleIncrement_eq
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    poissonScaleIncrement a b x =
      x ^ 2 * (b ^ 2 - a ^ 2) /
        ((b ^ 2 + x ^ 2) * (a ^ 2 + x ^ 2)) := by
  have hda := lorentz_denom_pos ha.ne' x
  have hdb := lorentz_denom_pos hb.ne' x
  unfold poissonScaleIncrement lorentz
  field_simp [hda.ne', hdb.ne']
  ring

/-- A scale increment vanishes on the diagonal. -/
theorem poissonScaleIncrement_zero
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    poissonScaleIncrement a b 0 = 0 := by
  rw [poissonScaleIncrement, lorentz_self hb, lorentz_self ha]
  ring

/-- Away from the diagonal, coarsening the resolution gives a strict positive spatial increment. -/
theorem poissonScaleIncrement_pos
    {a b x : ℝ} (ha : 0 < a) (hab : a < b) (hx : x ≠ 0) :
    0 < poissonScaleIncrement a b x := by
  have hb : 0 < b := ha.trans hab
  rw [poissonScaleIncrement_eq ha hb x]
  exact div_pos
    (mul_pos (sq_pos_of_ne_zero hx) (by nlinarith))
    (mul_pos (lorentz_denom_pos hb.ne' x) (lorentz_denom_pos ha.ne' x))

/-- The two-node signed quadratic carried by one Poisson scale increment. -/
def poissonScaleIncrementTwoPointQuadratic
    (a b x u v : ℝ) : ℝ :=
  poissonScaleIncrement a b 0 * u ^ 2 +
    2 * poissonScaleIncrement a b x * u * v +
    poissonScaleIncrement a b 0 * v ^ 2

/-- The mirror-even channel is the positive scale channel. -/
theorem poissonScaleIncrementTwoPointQuadratic_even
    {a b x m : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    poissonScaleIncrementTwoPointQuadratic a b x m m =
      2 * poissonScaleIncrement a b x * m ^ 2 := by
  rw [poissonScaleIncrementTwoPointQuadratic,
    poissonScaleIncrement_zero ha hb]
  ring

/-- The mirror-odd channel has exactly the opposite sign. -/
theorem poissonScaleIncrementTwoPointQuadratic_odd
    {a b x m : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    poissonScaleIncrementTwoPointQuadratic a b x m (-m) =
      -(2 * poissonScaleIncrement a b x * m ^ 2) := by
  rw [poissonScaleIncrementTwoPointQuadratic,
    poissonScaleIncrement_zero ha hb]
  ring

/-- Strict mirror-even positivity for a nontrivial pair and nonzero mass. -/
theorem poissonScaleIncrementTwoPointQuadratic_even_pos
    {a b x m : ℝ} (ha : 0 < a) (hab : a < b) (hx : x ≠ 0) (hm : m ≠ 0) :
    0 < poissonScaleIncrementTwoPointQuadratic a b x m m := by
  rw [poissonScaleIncrementTwoPointQuadratic_even ha.ne' (ha.trans hab).ne']
  exact mul_pos (mul_pos (by norm_num) (poissonScaleIncrement_pos ha hab hx))
    (sq_pos_of_ne_zero hm)

/-- Strict mirror-odd negativity for a nontrivial pair and nonzero mass. -/
theorem poissonScaleIncrementTwoPointQuadratic_odd_neg
    {a b x m : ℝ} (ha : 0 < a) (hab : a < b) (hx : x ≠ 0) (hm : m ≠ 0) :
    poissonScaleIncrementTwoPointQuadratic a b x m (-m) < 0 := by
  rw [poissonScaleIncrementTwoPointQuadratic_odd ha.ne' (ha.trans hab).ne']
  exact neg_neg_of_pos
    (mul_pos (mul_pos (by norm_num) (poissonScaleIncrement_pos ha hab hx))
      (sq_pos_of_ne_zero hm))

/-- The two-node determinant is the negative square of the off-diagonal scale increment. -/
theorem poissonScaleIncrement_twoPointDet
    {a b x : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    poissonScaleIncrement a b 0 * poissonScaleIncrement a b 0 -
        poissonScaleIncrement a b x ^ 2 =
      -(poissonScaleIncrement a b x) ^ 2 := by
  rw [poissonScaleIncrement_zero ha hb]
  ring

/-- A nontrivial Poisson scale increment cannot be a Hilbert Gram: its zero diagonal would force
both feature vectors to vanish, contradicting its positive off-diagonal. -/
theorem not_exists_inner_poissonScaleIncrement_twoPoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b x : ℝ} (ha : 0 < a) (hab : a < b) (hx : x ≠ 0) :
    ¬ ∃ u v : E,
      inner ℝ u u = poissonScaleIncrement a b 0 ∧
      inner ℝ v v = poissonScaleIncrement a b 0 ∧
      inner ℝ u v = poissonScaleIncrement a b x := by
  rintro ⟨u, v, hu, _, huv⟩
  have hu0 : inner ℝ u u = 0 := by
    rw [hu, poissonScaleIncrement_zero ha.ne' (ha.trans hab).ne']
  have hU : u = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hu0
  rw [hU, inner_zero_left] at huv
  exact (poissonScaleIncrement_pos ha hab hx).ne' huv.symm

/-- The signed quadratic in the actual resolution-refinement direction, fine minus coarse. -/
def poissonScaleRefinementTwoPointQuadratic
    (a b x u v : ℝ) : ℝ :=
  -poissonScaleIncrementTwoPointQuadratic a b x u v

/-- Refinement reverses the two parity channels: the physical mirror-even channel is negative. -/
theorem poissonScaleRefinementTwoPointQuadratic_even_neg
    {a b x m : ℝ} (ha : 0 < a) (hab : a < b) (hx : x ≠ 0) (hm : m ≠ 0) :
    poissonScaleRefinementTwoPointQuadratic a b x m m < 0 := by
  rw [poissonScaleRefinementTwoPointQuadratic,
    poissonScaleIncrementTwoPointQuadratic_even ha.ne' (ha.trans hab).ne']
  exact neg_neg_of_pos
    (mul_pos (mul_pos (by norm_num) (poissonScaleIncrement_pos ha hab hx))
      (sq_pos_of_ne_zero hm))

/-- The mirror-odd signed channel is positive in the fine-minus-coarse orientation. -/
theorem poissonScaleRefinementTwoPointQuadratic_odd_pos
    {a b x m : ℝ} (ha : 0 < a) (hab : a < b) (hx : x ≠ 0) (hm : m ≠ 0) :
    0 < poissonScaleRefinementTwoPointQuadratic a b x m (-m) := by
  rw [poissonScaleRefinementTwoPointQuadratic,
    poissonScaleIncrementTwoPointQuadratic_odd ha.ne' (ha.trans hab).ne']
  have hpos : 0 < 2 * poissonScaleIncrement a b x * m ^ 2 :=
    mul_pos (mul_pos (by norm_num) (poissonScaleIncrement_pos ha hab hx))
      (sq_pos_of_ne_zero hm)
  simpa only [neg_neg] using hpos

/-- The Poisson scale-increment kernel on displacement nodes. -/
def poissonScaleIncrementKernel (a b x y : ℝ) : ℝ :=
  poissonScaleIncrement a b (x - y)

/-- The slab response in the actual resolution-refinement direction, fine minus coarse. -/
def poissonScaleRefinementKernel (a b x y : ℝ) : ℝ :=
  -poissonScaleIncrementKernel a b x y

/-- The correctly oriented response refinement is still not a Hilbert Gram.  Its diagonal
vanishes while its off-diagonal is strictly negative at distinct nodes. -/
theorem not_exists_inner_poissonScaleRefinement_twoPoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b x : ℝ} (ha : 0 < a) (hab : a < b) (hx : x ≠ 0) :
    ¬ ∃ u v : E,
      inner ℝ u u = poissonScaleRefinementKernel a b 0 0 ∧
      inner ℝ v v = poissonScaleRefinementKernel a b x x ∧
      inner ℝ u v = poissonScaleRefinementKernel a b 0 x := by
  rintro ⟨u, v, hu, _, huv⟩
  have hu0 : inner ℝ u u = 0 := by
    rw [hu, poissonScaleRefinementKernel, poissonScaleIncrementKernel,
      sub_self, poissonScaleIncrement_zero ha.ne' (ha.trans hab).ne']
    ring
  have hU : u = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hu0
  rw [hU, inner_zero_left] at huv
  have hneg : poissonScaleRefinementKernel a b 0 x < 0 := by
    rw [poissonScaleRefinementKernel, poissonScaleIncrementKernel]
    exact neg_neg_of_pos
      (poissonScaleIncrement_pos ha hab (sub_ne_zero.mpr hx.symm))
  exact hneg.ne huv.symm

/-- Exact three-node determinant of a Poisson scale increment. -/
theorem symmetricThreePointDet_poissonScaleIncrementKernel
    {a b x y z : ℝ} (ha : 0 < a) (hb : 0 < b) :
    symmetricThreePointDet (poissonScaleIncrementKernel a b) x y z =
      2 * poissonScaleIncrement a b (x - y) *
        poissonScaleIncrement a b (x - z) *
        poissonScaleIncrement a b (y - z) := by
  unfold symmetricThreePointDet poissonScaleIncrementKernel
  have hzero : poissonScaleIncrement a b 0 = 0 :=
    poissonScaleIncrement_zero ha.ne' hb.ne'
  simp only [sub_self, hzero, zero_mul, zero_add]
  ring

/-- On three pairwise distinct displacements the scale-increment cubic is strictly positive. -/
theorem symmetricThreePointDet_poissonScaleIncrementKernel_pos
    {a b x y z : ℝ} (ha : 0 < a) (hab : a < b)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    0 < symmetricThreePointDet (poissonScaleIncrementKernel a b) x y z := by
  rw [symmetricThreePointDet_poissonScaleIncrementKernel ha (ha.trans hab)]
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num)
        (poissonScaleIncrement_pos ha hab (sub_ne_zero.mpr hxy)))
      (poissonScaleIncrement_pos ha hab (sub_ne_zero.mpr hxz)))
    (poissonScaleIncrement_pos ha hab (sub_ne_zero.mpr hyz))

/-- Reversing to the actual fine-minus-coarse orientation reverses the odd-dimensional cubic. -/
theorem symmetricThreePointDet_poissonScaleRefinementKernel_eq_neg
    (a b x y z : ℝ) :
    symmetricThreePointDet (poissonScaleRefinementKernel a b) x y z =
      -symmetricThreePointDet (poissonScaleIncrementKernel a b) x y z := by
  unfold symmetricThreePointDet poissonScaleRefinementKernel
  ring

/-- **Correct response signature.**  On three distinct displacement nodes, fine-minus-coarse
Poisson refinement has a strictly negative cubic, hence the same negative-index parity as one
off-line squared-Xi orbit. -/
theorem symmetricThreePointDet_poissonScaleRefinementKernel_neg
    {a b x y z : ℝ} (ha : 0 < a) (hab : a < b)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    symmetricThreePointDet (poissonScaleRefinementKernel a b) x y z < 0 := by
  rw [symmetricThreePointDet_poissonScaleRefinementKernel_eq_neg]
  exact neg_neg_of_pos
    (symmetricThreePointDet_poissonScaleIncrementKernel_pos
      ha hab hxy hxz hyz)

/-- Positive-cubic counterpart of the existing negative-amplification theorem: a kernel with
positive three-node self-determinant eventually forces every fixed background determinant positive. -/
theorem exists_symmetricThreePointDet_add_smul_pos
    (A B : ℝ → ℝ → ℝ) {x y z : ℝ}
    (hA : 0 < symmetricThreePointDet A x y z) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lambda : ℝ, L < lambda →
      0 < symmetricThreePointDet (fun u v => B u v + lambda * A u v) x y z := by
  have hnegA :
      symmetricThreePointDet (fun u v => -A u v) x y z < 0 := by
    have hflip : symmetricThreePointDet (fun u v => -A u v) x y z =
        -symmetricThreePointDet A x y z := by
      unfold symmetricThreePointDet
      ring
    rw [hflip]
    linarith
  obtain ⟨L, hL, hdet⟩ :=
    exists_symmetricThreePointDet_add_smul_neg
      (fun u v => -A u v) (fun u v => -B u v) hnegA
  refine ⟨L, hL, ?_⟩
  intro lambda hlambda
  have hneg := hdet lambda hlambda
  have hflip :
      symmetricThreePointDet
          (fun u v => -B u v + lambda * -A u v) x y z =
        -symmetricThreePointDet
          (fun u v => B u v + lambda * A u v) x y z := by
    unfold symmetricThreePointDet
    ring
  rw [hflip] at hneg
  linarith

/-- **Wrong-cubic-sign no-go.**  At any three distinct displacement nodes, positive amplification
of a Poisson scale increment eventually makes the determinant positive, whereas selecting an
off-line Xi orbit requires an eventually negative cubic. -/
theorem exists_poissonScaleIncrement_add_smul_threePointDet_pos
    (B : ℝ → ℝ → ℝ) {a b x y z : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lambda : ℝ, L < lambda →
      0 < symmetricThreePointDet
        (fun u v => B u v + lambda * poissonScaleIncrementKernel a b u v) x y z :=
  exists_symmetricThreePointDet_add_smul_pos
    (poissonScaleIncrementKernel a b) B
    (symmetricThreePointDet_poissonScaleIncrementKernel_pos
      ha hab hxy hxz hyz)

/-- **Positive survivor of the coarsening no-go.**  In the actual resolution-refinement
orientation, the Poisson response is an unbounded negative cubic amplifier against every fixed
background.  What remains open is a source-pure map from the positive aperture innovation to this
indefinite refinement kernel. -/
theorem exists_poissonScaleRefinement_add_smul_threePointDet_neg
    (B : ℝ → ℝ → ℝ) {a b x y z : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lambda : ℝ, L < lambda →
      symmetricThreePointDet
        (fun u v => B u v + lambda * poissonScaleRefinementKernel a b u v) x y z < 0 :=
  exists_symmetricThreePointDet_add_smul_neg
    (poissonScaleRefinementKernel a b) B
    (symmetricThreePointDet_poissonScaleRefinementKernel_neg
      ha hab hxy hxz hyz)

end

end RHTower
