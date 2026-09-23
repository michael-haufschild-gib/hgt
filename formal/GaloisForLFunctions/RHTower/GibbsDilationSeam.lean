import Mathlib
import GaloisForLFunctions.RHTower.GibbsClusterRepulsion

/-!
# The dilation seam of the squarefree Gibbs gas

The gas is an Euler operator-product over the dilation semigroup: with
`(dilate c f)(x) = f(cx)`,

  `P_S(z, x) = [∏_{p∈S} (1 + z·dilate p)] (e^{−·}) (x)`,

and the cutoff recursion T0 is the peeling of one factor.  The dilations commute
(`dilate p ∘ dilate q = dilate (pq)`), and on `L²` the dilation by `p` scales squared
mass by exactly `p⁻¹` — the square-root-of-`p` law that seats the spectral locus of the
commuting family `{dilate p}` on the Mellin critical line `Re s = 1/2`.  This file
records the exact finite layer:

* `dilate_dilate`, `dilate_comm` — the dilation semigroup;
* `gibbsDiag_insert_dilate` — T0 in operator form;
* `gibbsDiag_eq_sum_dilates` — the gas as the expanded operator product applied to the
  Gibbs state;
* `integral_dilate_sq` — the exact `p⁻¹` scaling of squared mass under dilation.
-/

namespace RHTower.GibbsGas

open Real MeasureTheory

/-- Dilation of a function by a scale factor. -/
noncomputable def dilate (c : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (c * x)

/-- Dilations form a (commutative) multiplicative semigroup. -/
theorem dilate_dilate (a b : ℝ) (f : ℝ → ℝ) :
    dilate a (dilate b f) = dilate (b * a) f := by
  funext x
  simp only [dilate, mul_assoc]

theorem dilate_comm (a b : ℝ) (f : ℝ → ℝ) :
    dilate a (dilate b f) = dilate b (dilate a f) := by
  rw [dilate_dilate, dilate_dilate, mul_comm]

/-- **T0 in operator form**: adjoining an element multiplies the gas operator by
`(1 + z·dilate p)`. -/
theorem gibbsDiag_insert_dilate (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x z : ℝ) :
    gibbsDiag (insert p S) x z
      = gibbsDiag S x z + z * dilate (p : ℝ) (fun y => gibbsDiag S y z) x := by
  rw [gibbsDiag_insert p S hp]
  rfl

/-- **The gas is the expanded Euler operator-product applied to the Gibbs state**:
`P_S(z,·) = ∑_{T⊆S} z^{|T|}·(∏_{p∈T} dilate p)(e^{−·})`, the fully expanded form of
`∏_{p∈S}(1 + z·dilate p)`. -/
theorem gibbsDiag_eq_sum_dilates (S : Finset ℕ) (x z : ℝ) :
    gibbsDiag S x z
      = ∑ T ∈ S.powerset, z ^ T.card
          * dilate (∏ p ∈ T, (p : ℝ)) (fun y => Real.exp (-y)) x := by
  rw [gibbsDiag]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [dilate]
  rw [mul_comm x (∏ p ∈ T, (p : ℝ))]

/-- **The square-root-of-`p` law**: dilation by `p > 0` scales squared mass by exactly
`p⁻¹`.  This is the spectral normalization that places the commuting dilation family on
the Mellin critical line. -/
theorem integral_dilate_sq (p : ℝ) (hp : 0 < p) (f : ℝ → ℝ) :
    ∫ x : ℝ, (dilate p f x) ^ (2 : ℕ) = p⁻¹ * ∫ x : ℝ, (f x) ^ (2 : ℕ) := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun y => (f y) ^ (2 : ℕ)) p
  simp only [dilate]
  rw [h, smul_eq_mul, abs_of_pos (inv_pos.mpr hp)]

end RHTower.GibbsGas
