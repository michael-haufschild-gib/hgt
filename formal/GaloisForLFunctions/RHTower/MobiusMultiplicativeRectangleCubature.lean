import GaloisForLFunctions.RHTower.MobiusBoundaryOppositeSignTransport

/-!
# Second-order multiplicative rectangle cubature for the Möbius boundary

Pairwise transport pays the spectator-amplified displacement of each edge.  A multiplicative
four-corner packet cancels both first-order edge defects and pays only the product of the two
token displacements.  This file proves the literal exponential-kernel estimate, its Möbius
parity instantiation, and finite packet aggregation.

No arithmetic rectangle covering theorem is assumed.  Such a theorem must construct the packets
from actual factor replacements and control the uncovered residual; the consumer here makes its
required second-order cost exact.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Sharp global mixed-difference estimate for the multiplicative exponential kernel.

The mixed derivative of `(a,b) ↦ exp (-x*a*b)` is
`x * (x*a*b - 1) * exp (-x*a*b)`, whose absolute value is at most `x` on the
nonnegative quadrant.  The proof below is purely algebraic: it factors the four-corner
difference into three nonnegative exponential increments and uses `1 - exp (-t) ≤ t`.
-/
theorem exp_mul_four_corner_le
    {x a₀ a₁ b₀ b₁ : ℝ}
    (hx : 0 ≤ x) (ha₀ : 0 ≤ a₀) (ha : a₀ ≤ a₁)
    (hb₀ : 0 ≤ b₀) (hb : b₀ ≤ b₁) :
    |Real.exp (-(x * (a₀ * b₀))) -
        Real.exp (-(x * (a₁ * b₀))) -
        Real.exp (-(x * (a₀ * b₁))) +
        Real.exp (-(x * (a₁ * b₁)))|
      ≤ x * (a₁ - a₀) * (b₁ - b₀) := by
  let da := a₁ - a₀
  let db := b₁ - b₀
  let Y := x * (a₀ * b₀)
  let U := x * (da * b₀)
  let V := x * (a₀ * db)
  let W := x * (da * db)
  have hda : 0 ≤ da := sub_nonneg.mpr ha
  have hdb : 0 ≤ db := sub_nonneg.mpr hb
  have hY : 0 ≤ Y := mul_nonneg hx (mul_nonneg ha₀ hb₀)
  have hU : 0 ≤ U := mul_nonneg hx (mul_nonneg hda hb₀)
  have hV : 0 ≤ V := mul_nonneg hx (mul_nonneg ha₀ hdb)
  have hW : 0 ≤ W := mul_nonneg hx (mul_nonneg hda hdb)
  have hU0 : 0 ≤ 1 - Real.exp (-U) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hU))
  have hU1 : 1 - Real.exp (-U) ≤ U := by
    linarith [Real.add_one_le_exp (-U)]
  have hV0 : 0 ≤ 1 - Real.exp (-V) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hV))
  have hV1 : 1 - Real.exp (-V) ≤ V := by
    linarith [Real.add_one_le_exp (-V)]
  have hW0 : 0 ≤ 1 - Real.exp (-W) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hW))
  have hW1 : 1 - Real.exp (-W) ≤ W := by
    linarith [Real.add_one_le_exp (-W)]
  have hYexp : (1 + Y) * Real.exp (-Y) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right
      (show 1 + Y ≤ Real.exp Y by simpa [add_comm] using Real.add_one_le_exp Y)
      (Real.exp_pos (-Y)).le
    rw [← Real.exp_add] at h
    simpa using h
  have hfactor :
      Real.exp (-(x * (a₀ * b₀))) -
          Real.exp (-(x * (a₁ * b₀))) -
          Real.exp (-(x * (a₀ * b₁))) +
          Real.exp (-(x * (a₁ * b₁))) =
        Real.exp (-Y) *
          ((1 - Real.exp (-U)) * (1 - Real.exp (-V)) -
            Real.exp (-(U + V)) * (1 - Real.exp (-W))) := by
    have ha₁ : a₁ = a₀ + da := by simp [da]
    have hb₁ : b₁ = b₀ + db := by simp [db]
    rw [ha₁, hb₁]
    rw [show -(x * ((a₀ + da) * b₀)) = -Y + -U by simp [Y, U]; ring]
    rw [show -(x * (a₀ * (b₀ + db))) = -Y + -V by simp [Y, V]; ring]
    rw [show -(x * ((a₀ + da) * (b₀ + db))) =
        -Y + (-(U + V) + -W) by simp [Y, U, V, W]; ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
    rw [show -(U + V) = -U + -V by ring, Real.exp_add]
    rw [show -(x * (a₀ * b₀)) = -Y by rfl]
    ring
  rw [hfactor, abs_mul, abs_of_nonneg (Real.exp_pos (-Y)).le]
  calc
    Real.exp (-Y) *
        |(1 - Real.exp (-U)) * (1 - Real.exp (-V)) -
          Real.exp (-(U + V)) * (1 - Real.exp (-W))| ≤
      Real.exp (-Y) *
        ((1 - Real.exp (-U)) * (1 - Real.exp (-V)) +
          Real.exp (-(U + V)) * (1 - Real.exp (-W))) := by
        gcongr
        have hA :
            0 ≤ (1 - Real.exp (-U)) * (1 - Real.exp (-V)) :=
          mul_nonneg hU0 hV0
        have hB :
            0 ≤ Real.exp (-(U + V)) * (1 - Real.exp (-W)) :=
          mul_nonneg (Real.exp_pos _).le hW0
        let A := (1 - Real.exp (-U)) * (1 - Real.exp (-V))
        let B := Real.exp (-(U + V)) * (1 - Real.exp (-W))
        have hA' : 0 ≤ A := hA
        have hB' : 0 ≤ B := hB
        have habs := abs_sub_le A (0 : ℝ) B
        simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hA',
          abs_of_nonneg hB'] using habs
    _ ≤ Real.exp (-Y) * (U * V + W) := by
      have hfirst :
          (1 - Real.exp (-U)) * (1 - Real.exp (-V)) ≤ U * V :=
        mul_le_mul hU1 hV1 hV0 hU
      have hsecond :
          Real.exp (-(U + V)) * (1 - Real.exp (-W)) ≤ W := by
        calc
          Real.exp (-(U + V)) * (1 - Real.exp (-W))
              ≤ 1 * (1 - Real.exp (-W)) := by
                gcongr
                exact Real.exp_le_one_iff.mpr
                  (neg_nonpos.mpr (add_nonneg hU hV))
          _ ≤ W := by simpa using hW1
      exact mul_le_mul_of_nonneg_left
        (add_le_add hfirst hsecond) (Real.exp_pos _).le
    _ = (x * da * db) * ((1 + Y) * Real.exp (-Y)) := by
      simp [Y, U, V, W]
      ring
    _ ≤ x * da * db := by
      have hxdadb : 0 ≤ x * da * db := by positivity
      nlinarith
    _ = x * (a₁ - a₀) * (b₁ - b₀) := by rfl

/-- Arithmetic admission condition for a literal multiplicative Möbius rectangle.

All four products are coprime factorizations, and changing either factor reverses its Möbius
coefficient.  Hence the four product coefficients have the checkerboard signs `+,-,-,+`,
up to one common Möbius factor.
-/
def MobiusParityRectangle (a₀ a₁ b₀ b₁ : ℕ) : Prop :=
  a₀.Coprime b₀ ∧ a₁.Coprime b₀ ∧ a₀.Coprime b₁ ∧ a₁.Coprime b₁ ∧
    mobiusComplexCoefficient a₁ = -mobiusComplexCoefficient a₀ ∧
    mobiusComplexCoefficient b₁ = -mobiusComplexCoefficient b₀

/-- Both token replacements reverse the two corresponding product signs; performing both
replacements restores the original sign. -/
theorem mobiusParityRectangle_cornerSigns
    {a₀ a₁ b₀ b₁ : ℕ} (h : MobiusParityRectangle a₀ a₁ b₀ b₁) :
    mobiusComplexCoefficient (a₁ * b₀) =
        -mobiusComplexCoefficient (a₀ * b₀) ∧
      mobiusComplexCoefficient (a₀ * b₁) =
        -mobiusComplexCoefficient (a₀ * b₀) ∧
      mobiusComplexCoefficient (a₁ * b₁) =
        mobiusComplexCoefficient (a₀ * b₀) := by
  rcases h with ⟨h00, h10, h01, h11, ha, hb⟩
  rw [mobiusComplexCoefficient_mul_of_coprime h00,
    mobiusComplexCoefficient_mul_of_coprime h10,
    mobiusComplexCoefficient_mul_of_coprime h01,
    mobiusComplexCoefficient_mul_of_coprime h11,
    ha, hb]
  constructor
  · ring
  · constructor <;> ring

/-- The four physical Möbius atoms factor exactly as one Möbius coefficient times the
checkerboard exponential difference. -/
theorem mobiusParityRectangle_laplace_eq
    {a₀ a₁ b₀ b₁ : ℕ} (h : MobiusParityRectangle a₀ a₁ b₀ b₁)
    (x : ℝ) :
    mobiusComplexCoefficient (a₀ * b₀) *
          Real.exp (-(x * ((a₀ * b₀ : ℕ) : ℝ))) +
        mobiusComplexCoefficient (a₁ * b₀) *
          Real.exp (-(x * ((a₁ * b₀ : ℕ) : ℝ))) +
        mobiusComplexCoefficient (a₀ * b₁) *
          Real.exp (-(x * ((a₀ * b₁ : ℕ) : ℝ))) +
        mobiusComplexCoefficient (a₁ * b₁) *
          Real.exp (-(x * ((a₁ * b₁ : ℕ) : ℝ))) =
      mobiusComplexCoefficient (a₀ * b₀) *
        ((Real.exp (-(x * ((a₀ * b₀ : ℕ) : ℝ))) : ℂ) -
          Real.exp (-(x * ((a₁ * b₀ : ℕ) : ℝ))) -
          Real.exp (-(x * ((a₀ * b₁ : ℕ) : ℝ))) +
          Real.exp (-(x * ((a₁ * b₁ : ℕ) : ℝ)))) := by
  obtain ⟨h10, h01, h11⟩ := mobiusParityRectangle_cornerSigns h
  rw [h10, h01, h11]
  push_cast
  ring

/-- A literal Möbius rectangle pays only the product of its two factor displacements.
The common Möbius coefficient costs at most one. -/
theorem norm_mobiusParityRectangle_laplace_le
    {a₀ a₁ b₀ b₁ : ℕ} (h : MobiusParityRectangle a₀ a₁ b₀ b₁)
    (ha : a₀ ≤ a₁) (hb : b₀ ≤ b₁) {x : ℝ} (hx : 0 ≤ x) :
    ‖mobiusComplexCoefficient (a₀ * b₀) *
          Real.exp (-(x * ((a₀ * b₀ : ℕ) : ℝ))) +
        mobiusComplexCoefficient (a₁ * b₀) *
          Real.exp (-(x * ((a₁ * b₀ : ℕ) : ℝ))) +
        mobiusComplexCoefficient (a₀ * b₁) *
          Real.exp (-(x * ((a₀ * b₁ : ℕ) : ℝ))) +
        mobiusComplexCoefficient (a₁ * b₁) *
          Real.exp (-(x * ((a₁ * b₁ : ℕ) : ℝ)))‖
      ≤ x * ((a₁ : ℝ) - a₀) * ((b₁ : ℝ) - b₀) := by
  rw [mobiusParityRectangle_laplace_eq h, norm_mul]
  have hk := exp_mul_four_corner_le
    (x := x) (a₀ := (a₀ : ℝ)) (a₁ := (a₁ : ℝ))
    (b₀ := (b₀ : ℝ)) (b₁ := (b₁ : ℝ))
    hx (Nat.cast_nonneg a₀) (by exact_mod_cast ha)
      (Nat.cast_nonneg b₀) (by exact_mod_cast hb)
  have hnorm :
      ‖((Real.exp (-(x * ((a₀ : ℝ) * b₀))) : ℂ) -
          Real.exp (-(x * ((a₁ : ℝ) * b₀))) -
          Real.exp (-(x * ((a₀ : ℝ) * b₁))) +
          Real.exp (-(x * ((a₁ : ℝ) * b₁))))‖ =
        |Real.exp (-(x * ((a₀ : ℝ) * b₀))) -
          Real.exp (-(x * ((a₁ : ℝ) * b₀))) -
          Real.exp (-(x * ((a₀ : ℝ) * b₁))) +
          Real.exp (-(x * ((a₁ : ℝ) * b₁)))| := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, ← Complex.ofReal_add,
      Complex.norm_real]
    rfl
  calc
    ‖mobiusComplexCoefficient (a₀ * b₀)‖ *
        ‖((Real.exp (-(x * ↑(a₀ * b₀))) : ℂ) -
          Real.exp (-(x * ↑(a₁ * b₀))) -
          Real.exp (-(x * ↑(a₀ * b₁))) +
          Real.exp (-(x * ↑(a₁ * b₁))))‖ ≤
      1 *
        |Real.exp (-(x * ((a₀ : ℝ) * b₀))) -
          Real.exp (-(x * ((a₁ : ℝ) * b₀))) -
          Real.exp (-(x * ((a₀ : ℝ) * b₁))) +
          Real.exp (-(x * ((a₁ : ℝ) * b₁)))| := by
            gcongr
            · exact norm_mobiusComplexCoefficient_le_one _
            · simpa only [Nat.cast_mul] using hnorm.le
    _ ≤ x * ((a₁ : ℝ) - a₀) * ((b₁ : ℝ) - b₀) := by
      simpa only [one_mul] using hk

/-- Physical four-corner packet attached to one admitted Möbius rectangle. -/
def mobiusParityRectangleLaplacePacket
    (a₀ a₁ b₀ b₁ : ℕ) (x : ℝ) : ℂ :=
  mobiusComplexCoefficient (a₀ * b₀) *
        Real.exp (-(x * ((a₀ * b₀ : ℕ) : ℝ))) +
    mobiusComplexCoefficient (a₁ * b₀) *
        Real.exp (-(x * ((a₁ * b₀ : ℕ) : ℝ))) +
    mobiusComplexCoefficient (a₀ * b₁) *
        Real.exp (-(x * ((a₀ * b₁ : ℕ) : ℝ))) +
    mobiusComplexCoefficient (a₁ * b₁) *
        Real.exp (-(x * ((a₁ * b₁ : ℕ) : ℝ)))

theorem norm_mobiusParityRectangleLaplacePacket_le
    {a₀ a₁ b₀ b₁ : ℕ} (h : MobiusParityRectangle a₀ a₁ b₀ b₁)
    (ha : a₀ ≤ a₁) (hb : b₀ ≤ b₁) {x : ℝ} (hx : 0 ≤ x) :
    ‖mobiusParityRectangleLaplacePacket a₀ a₁ b₀ b₁ x‖
      ≤ x * ((a₁ : ℝ) - a₀) * ((b₁ : ℝ) - b₀) := by
  exact norm_mobiusParityRectangle_laplace_le h ha hb hx

/-- Total second-order displacement budget of a finite admitted rectangle family. -/
def finiteMobiusRectangleSecondOrderCost
    {ι : Type*} (s : Finset ι)
    (a₀ a₁ b₀ b₁ : ι → ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ s,
    x * ((a₁ i : ℝ) - a₀ i) * ((b₁ i : ℝ) - b₀ i)

/-- Finite rectangle-cubature consumer.  Every admitted packet pays its mixed displacement
product; atoms not assigned to packets remain in the explicit residual `r`.

An arithmetic source theorem must identify `r` with the literal unused Route E capacity and
bound it.  This theorem supplies no existential decomposition.
-/
theorem norm_sum_mobiusParityRectangleLaplace_add_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a₀ a₁ b₀ b₁ : ι → ℕ)
    (hrect : ∀ i ∈ s, MobiusParityRectangle (a₀ i) (a₁ i) (b₀ i) (b₁ i))
    (ha : ∀ i ∈ s, a₀ i ≤ a₁ i) (hb : ∀ i ∈ s, b₀ i ≤ b₁ i)
    {x : ℝ} (hx : 0 ≤ x) (r : ℂ) :
    ‖(∑ i ∈ s,
        mobiusParityRectangleLaplacePacket
          (a₀ i) (a₁ i) (b₀ i) (b₁ i) x) + r‖
      ≤ finiteMobiusRectangleSecondOrderCost s a₀ a₁ b₀ b₁ x + ‖r‖ := by
  calc
    ‖(∑ i ∈ s,
        mobiusParityRectangleLaplacePacket
          (a₀ i) (a₁ i) (b₀ i) (b₁ i) x) + r‖ ≤
        ‖∑ i ∈ s,
          mobiusParityRectangleLaplacePacket
            (a₀ i) (a₁ i) (b₀ i) (b₁ i) x‖ + ‖r‖ :=
      norm_add_le _ _
    _ ≤ (∑ i ∈ s,
          ‖mobiusParityRectangleLaplacePacket
            (a₀ i) (a₁ i) (b₀ i) (b₁ i) x‖) + ‖r‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ finiteMobiusRectangleSecondOrderCost s a₀ a₁ b₀ b₁ x + ‖r‖ := by
      gcongr
      rw [finiteMobiusRectangleSecondOrderCost]
      exact Finset.sum_le_sum fun i hi =>
        norm_mobiusParityRectangleLaplacePacket_le
          (hrect i hi) (ha i hi) (hb i hi) hx

/-- Fractionally weighted second-order displacement budget.  This is the cost used by an
arithmetic rectangle hypergraph cover with vertex capacities. -/
def finiteWeightedMobiusRectangleSecondOrderCost
    {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (a₀ a₁ b₀ b₁ : ι → ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ s,
    c i * (x * ((a₁ i : ℝ) - a₀ i) * ((b₁ i : ℝ) - b₀ i))

/-- Fractional rectangle-cubature consumer.  Nonnegative packet weights may split one boundary
atom among many arithmetic rectangles.  The only analytic charge is the weighted product of the
two factor displacements; any uncovered capacity remains explicit in `r`. -/
theorem norm_sum_weightedMobiusParityRectangleLaplace_add_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ)
    (a₀ a₁ b₀ b₁ : ι → ℕ)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hrect : ∀ i ∈ s, MobiusParityRectangle (a₀ i) (a₁ i) (b₀ i) (b₁ i))
    (ha : ∀ i ∈ s, a₀ i ≤ a₁ i) (hb : ∀ i ∈ s, b₀ i ≤ b₁ i)
    {x : ℝ} (hx : 0 ≤ x) (r : ℂ) :
    ‖(∑ i ∈ s, (c i : ℂ) *
        mobiusParityRectangleLaplacePacket
          (a₀ i) (a₁ i) (b₀ i) (b₁ i) x) + r‖
      ≤ finiteWeightedMobiusRectangleSecondOrderCost
          s c a₀ a₁ b₀ b₁ x + ‖r‖ := by
  calc
    ‖(∑ i ∈ s, (c i : ℂ) *
        mobiusParityRectangleLaplacePacket
          (a₀ i) (a₁ i) (b₀ i) (b₁ i) x) + r‖ ≤
        ‖∑ i ∈ s, (c i : ℂ) *
          mobiusParityRectangleLaplacePacket
            (a₀ i) (a₁ i) (b₀ i) (b₁ i) x‖ + ‖r‖ :=
      norm_add_le _ _
    _ ≤ (∑ i ∈ s, ‖(c i : ℂ) *
          mobiusParityRectangleLaplacePacket
            (a₀ i) (a₁ i) (b₀ i) (b₁ i) x‖) + ‖r‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ finiteWeightedMobiusRectangleSecondOrderCost
          s c a₀ a₁ b₀ b₁ x + ‖r‖ := by
      gcongr
      rw [finiteWeightedMobiusRectangleSecondOrderCost]
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real]
      have hcnorm : ‖c i‖ = c i := by
        exact abs_of_nonneg (hc i hi)
      rw [hcnorm]
      exact mul_le_mul_of_nonneg_left
        (norm_mobiusParityRectangleLaplacePacket_le
          (hrect i hi) (ha i hi) (hb i hi) hx)
        (hc i hi)

/-- Total fractional corner load placed on the physical Möbius vertex `n`.
Repeated corners are charged with multiplicity, so no injectivity is hidden. -/
def finiteMobiusRectangleVertexLoad
    {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (a₀ a₁ b₀ b₁ : ι → ℕ) (n : ℕ) : ℝ :=
  ∑ i ∈ s,
    ((if n = a₀ i * b₀ i then c i else 0) +
      (if n = a₁ i * b₀ i then c i else 0) +
      (if n = a₀ i * b₁ i then c i else 0) +
      (if n = a₁ i * b₁ i then c i else 0))

/-- One literal finite Möbius--Laplace atom, written with a real exponential so that it
regroups definitionally into `mobiusParityRectangleLaplacePacket`. -/
def mobiusRectangleLaplaceAtom (n : ℕ) (x : ℝ) : ℂ :=
  mobiusComplexCoefficient n * Real.exp (-(x * (n : ℝ)))

private theorem sum_single_rectangleCornerLaplaceAtom
    (V : Finset ℕ) {v : ℕ} (hv : v ∈ V) (c : ℝ) (x : ℝ) :
    ∑ n ∈ V,
        ((if n = v then c else 0 : ℝ) : ℂ) *
          mobiusRectangleLaplaceAtom n x =
      (c : ℂ) * mobiusRectangleLaplaceAtom v x := by
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hbV hb
    simp [hb]
  · exact fun hvV => (hvV hv).elim

private theorem sum_rectangleCornerLaplaceAtom
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (V : Finset ℕ) (c : ι → ℝ) (v : ι → ℕ)
    (hv : ∀ i ∈ s, v i ∈ V) (x : ℝ) :
    ∑ n ∈ V,
        (∑ i ∈ s, ((if n = v i then c i else 0 : ℝ) : ℂ)) *
          mobiusRectangleLaplaceAtom n x =
      ∑ i ∈ s, (c i : ℂ) * mobiusRectangleLaplaceAtom (v i) x := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_single_rectangleCornerLaplaceAtom V (hv i hi) (c i) x

/-- Exact finite regrouping: the weighted sum of physical rectangle packets is the physical
atom sum multiplied by its literal corner load. -/
theorem sum_finiteMobiusRectangleVertexLoad_mul_atom_eq_weightedPackets
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (V : Finset ℕ) (c : ι → ℝ)
    (a₀ a₁ b₀ b₁ : ι → ℕ)
    (h00 : ∀ i ∈ s, a₀ i * b₀ i ∈ V)
    (h10 : ∀ i ∈ s, a₁ i * b₀ i ∈ V)
    (h01 : ∀ i ∈ s, a₀ i * b₁ i ∈ V)
    (h11 : ∀ i ∈ s, a₁ i * b₁ i ∈ V)
    (x : ℝ) :
    ∑ n ∈ V,
        (finiteMobiusRectangleVertexLoad s c a₀ a₁ b₀ b₁ n : ℂ) *
          mobiusRectangleLaplaceAtom n x =
      ∑ i ∈ s, (c i : ℂ) *
        mobiusParityRectangleLaplacePacket
          (a₀ i) (a₁ i) (b₀ i) (b₁ i) x := by
  simp only [finiteMobiusRectangleVertexLoad, Complex.ofReal_sum, Complex.ofReal_add,
    add_mul, Finset.sum_add_distrib]
  rw [sum_rectangleCornerLaplaceAtom s V c
      (fun i => a₀ i * b₀ i) h00 x,
    sum_rectangleCornerLaplaceAtom s V c
      (fun i => a₁ i * b₀ i) h10 x,
    sum_rectangleCornerLaplaceAtom s V c
      (fun i => a₀ i * b₁ i) h01 x,
    sum_rectangleCornerLaplaceAtom s V c
      (fun i => a₁ i * b₁ i) h11 x,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mobiusRectangleLaplaceAtom, mobiusParityRectangleLaplacePacket]
  ring

/-- Literal unused Gibbs vector after subtracting all rectangle corner loads from the target
finite vertex set. -/
def finiteMobiusRectangleUnusedLaplace
    {ι : Type*} (s : Finset ι) (V : Finset ℕ) (c : ι → ℝ)
    (a₀ a₁ b₀ b₁ : ι → ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ V,
    ((1 - finiteMobiusRectangleVertexLoad s c a₀ a₁ b₀ b₁ n : ℝ) : ℂ) *
      mobiusRectangleLaplaceAtom n x

/-- Exact target decomposition into weighted admitted packets and the literal unused capacity.
This removes the arbitrary residual from the final rectangle consumer. -/
theorem sum_mobiusRectangleLaplaceAtom_eq_weightedPackets_add_unused
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (V : Finset ℕ) (c : ι → ℝ)
    (a₀ a₁ b₀ b₁ : ι → ℕ)
    (h00 : ∀ i ∈ s, a₀ i * b₀ i ∈ V)
    (h10 : ∀ i ∈ s, a₁ i * b₀ i ∈ V)
    (h01 : ∀ i ∈ s, a₀ i * b₁ i ∈ V)
    (h11 : ∀ i ∈ s, a₁ i * b₁ i ∈ V)
    (x : ℝ) :
    ∑ n ∈ V, mobiusRectangleLaplaceAtom n x =
      (∑ i ∈ s, (c i : ℂ) *
        mobiusParityRectangleLaplacePacket
          (a₀ i) (a₁ i) (b₀ i) (b₁ i) x) +
        finiteMobiusRectangleUnusedLaplace s V c a₀ a₁ b₀ b₁ x := by
  rw [← sum_finiteMobiusRectangleVertexLoad_mul_atom_eq_weightedPackets
    s V c a₀ a₁ b₀ b₁ h00 h10 h01 h11 x]
  rw [finiteMobiusRectangleUnusedLaplace, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

theorem norm_mobiusRectangleLaplaceAtom_le (n : ℕ) (x : ℝ) :
    ‖mobiusRectangleLaplaceAtom n x‖ ≤ Real.exp (-(x * (n : ℝ))) := by
  rw [mobiusRectangleLaplaceAtom, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le
    (norm_mobiusComplexCoefficient_le_one n)

/-- The literal residual norm is bounded by the positive unused Gibbs capacity whenever no
physical vertex is overloaded. -/
theorem norm_finiteMobiusRectangleUnusedLaplace_le
    {ι : Type*} (s : Finset ι) (V : Finset ℕ) (c : ι → ℝ)
    (a₀ a₁ b₀ b₁ : ι → ℕ) (x : ℝ)
    (hload : ∀ n ∈ V,
      finiteMobiusRectangleVertexLoad s c a₀ a₁ b₀ b₁ n ≤ 1) :
    ‖finiteMobiusRectangleUnusedLaplace s V c a₀ a₁ b₀ b₁ x‖ ≤
      ∑ n ∈ V,
        (1 - finiteMobiusRectangleVertexLoad s c a₀ a₁ b₀ b₁ n) *
          Real.exp (-(x * (n : ℝ))) := by
  rw [finiteMobiusRectangleUnusedLaplace]
  calc
    ‖∑ n ∈ V,
        ((1 - finiteMobiusRectangleVertexLoad s c a₀ a₁ b₀ b₁ n : ℝ) : ℂ) *
          mobiusRectangleLaplaceAtom n x‖ ≤
      ∑ n ∈ V,
        ‖((1 - finiteMobiusRectangleVertexLoad s c a₀ a₁ b₀ b₁ n : ℝ) : ℂ) *
          mobiusRectangleLaplaceAtom n x‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ V,
        (1 - finiteMobiusRectangleVertexLoad s c a₀ a₁ b₀ b₁ n) *
          Real.exp (-(x * (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hload n hn))]
      exact mul_le_mul_of_nonneg_left
        (norm_mobiusRectangleLaplaceAtom_le n x)
        (sub_nonneg.mpr (hload n hn))

/-- Literal finite hypergraph form of the second-order rectangle consumer.

The conclusion contains only two nonnegative arithmetic obligations: mixed displacement cost and
unused vertex capacity.  No arbitrary complex residual remains in the theorem. -/
theorem norm_sum_mobiusRectangleLaplaceAtom_le_secondOrderCost_add_unusedCapacity
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (V : Finset ℕ) (c : ι → ℝ)
    (a₀ a₁ b₀ b₁ : ι → ℕ)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hrect : ∀ i ∈ s, MobiusParityRectangle (a₀ i) (a₁ i) (b₀ i) (b₁ i))
    (ha : ∀ i ∈ s, a₀ i ≤ a₁ i) (hb : ∀ i ∈ s, b₀ i ≤ b₁ i)
    (h00 : ∀ i ∈ s, a₀ i * b₀ i ∈ V)
    (h10 : ∀ i ∈ s, a₁ i * b₀ i ∈ V)
    (h01 : ∀ i ∈ s, a₀ i * b₁ i ∈ V)
    (h11 : ∀ i ∈ s, a₁ i * b₁ i ∈ V)
    {x : ℝ} (hx : 0 ≤ x)
    (hload : ∀ n ∈ V,
      finiteMobiusRectangleVertexLoad s c a₀ a₁ b₀ b₁ n ≤ 1) :
    ‖∑ n ∈ V, mobiusRectangleLaplaceAtom n x‖ ≤
      finiteWeightedMobiusRectangleSecondOrderCost s c a₀ a₁ b₀ b₁ x +
        ∑ n ∈ V,
          (1 - finiteMobiusRectangleVertexLoad s c a₀ a₁ b₀ b₁ n) *
            Real.exp (-(x * (n : ℝ))) := by
  rw [sum_mobiusRectangleLaplaceAtom_eq_weightedPackets_add_unused
    s V c a₀ a₁ b₀ b₁ h00 h10 h01 h11 x]
  exact le_trans
    (norm_sum_weightedMobiusParityRectangleLaplace_add_le
      s c a₀ a₁ b₀ b₁ hc hrect ha hb hx
      (finiteMobiusRectangleUnusedLaplace s V c a₀ a₁ b₀ b₁ x))
    (by
      gcongr
      exact norm_finiteMobiusRectangleUnusedLaplace_le
        s V c a₀ a₁ b₀ b₁ x hload)

/-- Large-prime breadth is additive across a coprime product.  This is the arithmetic
conservation law behind the zero/one-sector audit of a multiplicative rectangle. -/
theorem mobiusLargePrimeFactorCount_mul_of_coprime
    {z a b : ℕ} (h : a.Coprime b) :
    mobiusLargePrimeFactorCount z (a * b) =
      mobiusLargePrimeFactorCount z a +
        mobiusLargePrimeFactorCount z b := by
  simp only [mobiusLargePrimeFactorCount, mobiusLargePrimeFactors]
  rw [h.primeFactors_mul, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_filter_filter
    (p := fun q : ℕ => z < q) (q := fun q : ℕ => z < q)
    h.disjoint_primeFactors

/-- On the zero/one-large-prime boundary, the zero-sector indicator is the affine function
`1 - largePrimeCount`. -/
theorem mobiusZeroLargePrimeCoefficient_eq_mul_one_sub_count
    {z n : ℕ} (h : mobiusLargePrimeFactorCount z n ≤ 1) :
    mobiusZeroLargePrimeCoefficient z n =
      mobiusComplexCoefficient n *
        (1 - (mobiusLargePrimeFactorCount z n : ℂ)) := by
  rw [mobiusZeroLargePrimeCoefficient]
  by_cases hzero : mobiusLargePrimeFactorCount z n = 0
  · simp [hzero]
  · have hone : mobiusLargePrimeFactorCount z n = 1 := by omega
    simp [hone]

/-- On the zero/one-large-prime boundary, the one-sector indicator is the linear function
`largePrimeCount`. -/
theorem mobiusOneLargePrimeCoefficient_eq_mul_count
    {z n : ℕ} (h : mobiusLargePrimeFactorCount z n ≤ 1) :
    mobiusOneLargePrimeCoefficient z n =
      mobiusComplexCoefficient n *
        (mobiusLargePrimeFactorCount z n : ℂ) := by
  rw [mobiusOneLargePrimeCoefficient]
  by_cases hone : mobiusLargePrimeFactorCount z n = 1
  · simp [hone]
  · have hzero : mobiusLargePrimeFactorCount z n = 0 := by omega
    simp [hzero]

/-- A multiplicative Möbius rectangle wholly inside the zero/one-large-prime boundary has
zero signed coefficient mass in the zero-large-prime sector by itself.

Thus a rectangle crossing the seam does not transfer static coefficient imbalance between
sectors: its two zero-sector corners already have opposite signs. -/
theorem mobiusParityRectangle_zeroLargePrime_cornerSum_eq_zero
    {z a₀ a₁ b₀ b₁ : ℕ}
    (h : MobiusParityRectangle a₀ a₁ b₀ b₁)
    (h00 : mobiusLargePrimeFactorCount z (a₀ * b₀) ≤ 1)
    (h10 : mobiusLargePrimeFactorCount z (a₁ * b₀) ≤ 1)
    (h01 : mobiusLargePrimeFactorCount z (a₀ * b₁) ≤ 1)
    (h11 : mobiusLargePrimeFactorCount z (a₁ * b₁) ≤ 1) :
    mobiusZeroLargePrimeCoefficient z (a₀ * b₀) +
        mobiusZeroLargePrimeCoefficient z (a₁ * b₀) +
        mobiusZeroLargePrimeCoefficient z (a₀ * b₁) +
        mobiusZeroLargePrimeCoefficient z (a₁ * b₁) = 0 := by
  have hcount00 := mobiusLargePrimeFactorCount_mul_of_coprime (z := z) h.1
  have hcount10 := mobiusLargePrimeFactorCount_mul_of_coprime (z := z) h.2.1
  have hcount01 := mobiusLargePrimeFactorCount_mul_of_coprime (z := z) h.2.2.1
  have hcount11 := mobiusLargePrimeFactorCount_mul_of_coprime (z := z) h.2.2.2.1
  rw [mobiusZeroLargePrimeCoefficient_eq_mul_one_sub_count h00,
    mobiusZeroLargePrimeCoefficient_eq_mul_one_sub_count h10,
    mobiusZeroLargePrimeCoefficient_eq_mul_one_sub_count h01,
    mobiusZeroLargePrimeCoefficient_eq_mul_one_sub_count h11]
  obtain ⟨hs10, hs01, hs11⟩ := mobiusParityRectangle_cornerSigns h
  rw [hs10, hs01, hs11, hcount00, hcount10, hcount01, hcount11]
  push_cast
  ring

/-- The complementary one-large-prime sector also has zero signed coefficient mass on every
admitted boundary rectangle.  This is an independent sector-marginal conservation law, not
only cancellation after the two sectors are added. -/
theorem mobiusParityRectangle_oneLargePrime_cornerSum_eq_zero
    {z a₀ a₁ b₀ b₁ : ℕ}
    (h : MobiusParityRectangle a₀ a₁ b₀ b₁)
    (h00 : mobiusLargePrimeFactorCount z (a₀ * b₀) ≤ 1)
    (h10 : mobiusLargePrimeFactorCount z (a₁ * b₀) ≤ 1)
    (h01 : mobiusLargePrimeFactorCount z (a₀ * b₁) ≤ 1)
    (h11 : mobiusLargePrimeFactorCount z (a₁ * b₁) ≤ 1) :
    mobiusOneLargePrimeCoefficient z (a₀ * b₀) +
        mobiusOneLargePrimeCoefficient z (a₁ * b₀) +
        mobiusOneLargePrimeCoefficient z (a₀ * b₁) +
        mobiusOneLargePrimeCoefficient z (a₁ * b₁) = 0 := by
  have hcount00 := mobiusLargePrimeFactorCount_mul_of_coprime (z := z) h.1
  have hcount10 := mobiusLargePrimeFactorCount_mul_of_coprime (z := z) h.2.1
  have hcount01 := mobiusLargePrimeFactorCount_mul_of_coprime (z := z) h.2.2.1
  have hcount11 := mobiusLargePrimeFactorCount_mul_of_coprime (z := z) h.2.2.2.1
  rw [mobiusOneLargePrimeCoefficient_eq_mul_count h00,
    mobiusOneLargePrimeCoefficient_eq_mul_count h10,
    mobiusOneLargePrimeCoefficient_eq_mul_count h01,
    mobiusOneLargePrimeCoefficient_eq_mul_count h11]
  obtain ⟨hs10, hs01, hs11⟩ := mobiusParityRectangle_cornerSigns h
  rw [hs10, hs01, hs11, hcount00, hcount10, hcount01, hcount11]
  push_cast
  ring

end

end RHTower
