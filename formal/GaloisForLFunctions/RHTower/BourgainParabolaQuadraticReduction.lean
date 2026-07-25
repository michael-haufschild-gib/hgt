/-
# Parabola triple fibers as quadratic-form representations

For a triple `(a,b,c)` with first moment `s` and second moment `q`, put

`u = 3a - s`,  `v = b - c`.

Then

`u² + 3v² = 2(3q - s²)`.

This module proves the identity, injectivity on each fixed moment fiber, and
the resulting exact reduction to a finite box of representations of
`u² + 3v²`.  A subpolynomial bound for that representation set is the
remaining arithmetic input needed to sharpen the elementary `2H` loss to
`H^ε`.
-/
import GaloisForLFunctions.RHTower.BourgainParabolaFiberArithmetic

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every positive index represented by `Fin H` is at most `H`. -/
theorem bourgainIndex_le {H : ℕ} (h : Fin H) :
    bourgainIndex h ≤ H := by
  simp only [bourgainIndex]
  omega

/-- Integral coordinates associated to a parabola triple. -/
def bourgainParabolaQuadraticCode {H : ℕ}
    (h : Fin 3 → Fin H) : ℤ × ℤ :=
  (3 * (bourgainIndex (h 0) : ℤ) -
      (∑ j : Fin 3, bourgainIndex (h j) : ℕ),
    (bourgainIndex (h 1) : ℤ) - bourgainIndex (h 2))

/-- Discriminant attached to the pair `(Σn, Σn²)`. -/
def bourgainParabolaDiscriminant (y : ℕ × ℕ) : ℤ :=
  2 * (3 * (y.2 : ℤ) - (y.1 : ℤ) ^ (2 : ℕ))

/-- The quadratic-code norm is exactly the moment discriminant. -/
theorem bourgainParabolaQuadraticCode_norm
    {H : ℕ} (h : Fin 3 → Fin H) :
    (bourgainParabolaQuadraticCode h).1 ^ (2 : ℕ) +
        3 * (bourgainParabolaQuadraticCode h).2 ^ (2 : ℕ) =
      bourgainParabolaDiscriminant
        (bourgainParabolaTripleMoment h) := by
  simp only [bourgainParabolaQuadraticCode,
    bourgainParabolaDiscriminant, bourgainParabolaTripleMoment,
    Fin.sum_univ_three]
  push_cast
  ring

/-- Every moment discriminant arising from a triple is nonnegative. -/
theorem bourgainParabolaDiscriminant_nonneg
    {H : ℕ} (h : Fin 3 → Fin H) :
    0 ≤ bourgainParabolaDiscriminant
      (bourgainParabolaTripleMoment h) := by
  rw [← bourgainParabolaQuadraticCode_norm]
  positivity

/-- A triple from `[1,H]` has discriminant at most `18H²`. -/
theorem bourgainParabolaDiscriminant_le
    {H : ℕ} (h : Fin 3 → Fin H) :
    bourgainParabolaDiscriminant
        (bourgainParabolaTripleMoment h) ≤
      18 * (H : ℤ) ^ (2 : ℕ) := by
  have h0 := bourgainIndex_le (h 0)
  have h1 := bourgainIndex_le (h 1)
  have h2 := bourgainIndex_le (h 2)
  have h0z : (bourgainIndex (h 0) : ℤ) ≤ H := by exact_mod_cast h0
  have h1z : (bourgainIndex (h 1) : ℤ) ≤ H := by exact_mod_cast h1
  have h2z : (bourgainIndex (h 2) : ℤ) ≤ H := by exact_mod_cast h2
  have h0nonneg : (0 : ℤ) ≤ bourgainIndex (h 0) := by positivity
  have h1nonneg : (0 : ℤ) ≤ bourgainIndex (h 1) := by positivity
  have h2nonneg : (0 : ℤ) ≤ bourgainIndex (h 2) := by positivity
  simp only [bourgainParabolaDiscriminant,
    bourgainParabolaTripleMoment, Fin.sum_univ_three]
  push_cast
  nlinarith [sq_nonneg
    ((bourgainIndex (h 0) : ℤ) +
      bourgainIndex (h 1) + bourgainIndex (h 2))]

/-- On a fixed moment fiber, the quadratic code is injective. -/
theorem bourgainParabolaQuadraticCode_injective_on_fiber
    {H : ℕ} {h k : Fin 3 → Fin H}
    (hmoment :
      bourgainParabolaTripleMoment h =
        bourgainParabolaTripleMoment k)
    (hcode :
      bourgainParabolaQuadraticCode h =
        bourgainParabolaQuadraticCode k) :
    h = k := by
  have hsumNat := congrArg Prod.fst hmoment
  simp only [bourgainParabolaTripleMoment, Fin.sum_univ_three] at hsumNat
  have hsum :
      (bourgainIndex (h 0) : ℤ) +
          bourgainIndex (h 1) + bourgainIndex (h 2) =
        (bourgainIndex (k 0) : ℤ) +
          bourgainIndex (k 1) + bourgainIndex (k 2) := by
    exact_mod_cast hsumNat
  have hu := congrArg Prod.fst hcode
  have hv := congrArg Prod.snd hcode
  simp only [bourgainParabolaQuadraticCode, Fin.sum_univ_three] at hu hv
  push_cast at hu
  have hzeroIndex :
      bourgainIndex (h 0) = bourgainIndex (k 0) := by
    exact_mod_cast (show
      (bourgainIndex (h 0) : ℤ) =
        bourgainIndex (k 0) by nlinarith)
  have honeIndex :
      bourgainIndex (h 1) = bourgainIndex (k 1) := by
    exact_mod_cast (show
      (bourgainIndex (h 1) : ℤ) =
        bourgainIndex (k 1) by nlinarith)
  have htwoIndex :
      bourgainIndex (h 2) = bourgainIndex (k 2) := by
    exact_mod_cast (show
      (bourgainIndex (h 2) : ℤ) =
        bourgainIndex (k 2) by nlinarith)
  funext j
  fin_cases j
  · apply Fin.ext
    simpa [bourgainIndex] using hzeroIndex
  · apply Fin.ext
    simpa [bourgainIndex] using honeIndex
  · apply Fin.ext
    simpa [bourgainIndex] using htwoIndex

/-- Finite box of representations of the discriminant by `u² + 3v²`. -/
def bourgainParabolaRepresentationFinset
    (H : ℕ) (y : ℕ × ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(3 * (H : ℤ))) (3 * H)).product
      (Finset.Icc (-(3 * (H : ℤ))) (3 * H))).filter
    fun uv =>
      uv.1 ^ (2 : ℕ) + 3 * uv.2 ^ (2 : ℕ) =
        bourgainParabolaDiscriminant y

/-- A triple code lies in the `3H` box. -/
theorem bourgainParabolaQuadraticCode_mem_box
    {H : ℕ} (h : Fin 3 → Fin H) :
    bourgainParabolaQuadraticCode h ∈
      (Finset.Icc (-(3 * (H : ℤ))) (3 * H)).product
        (Finset.Icc (-(3 * (H : ℤ))) (3 * H)) := by
  have h0 := bourgainIndex_le (h 0)
  have h1 := bourgainIndex_le (h 1)
  have h2 := bourgainIndex_le (h 2)
  have h0z : (bourgainIndex (h 0) : ℤ) ≤ H := by exact_mod_cast h0
  have h1z : (bourgainIndex (h 1) : ℤ) ≤ H := by exact_mod_cast h1
  have h2z : (bourgainIndex (h 2) : ℤ) ≤ H := by exact_mod_cast h2
  have h0nonneg : (0 : ℤ) ≤ bourgainIndex (h 0) := by positivity
  have h1nonneg : (0 : ℤ) ≤ bourgainIndex (h 1) := by positivity
  have h2nonneg : (0 : ℤ) ≤ bourgainIndex (h 2) := by positivity
  rw [Finset.product_eq_sprod, Finset.mem_product]
  simp only [bourgainParabolaQuadraticCode, Fin.sum_univ_three,
    Finset.mem_Icc]
  push_cast
  constructor <;> constructor <;> omega

/-- Every triple in a fixed moment fiber maps to the corresponding
quadratic-form representation set. -/
theorem bourgainParabolaQuadraticCode_mem_representation
    {H : ℕ} {y : ℕ × ℕ} {h : Fin 3 → Fin H}
    (hmoment : bourgainParabolaTripleMoment h = y) :
    bourgainParabolaQuadraticCode h ∈
      bourgainParabolaRepresentationFinset H y := by
  rw [bourgainParabolaRepresentationFinset, Finset.mem_filter]
  refine ⟨bourgainParabolaQuadraticCode_mem_box h, ?_⟩
  rw [← hmoment]
  exact bourgainParabolaQuadraticCode_norm h

/-- Exact cardinality reduction from a moment fiber to bounded
representations of `u² + 3v²`. -/
theorem card_bourgainParabolaTripleMoment_fiber_le_representation
    (H : ℕ) (y : ℕ × ℕ) :
    ((Finset.univ : Finset (Fin 3 → Fin H)).filter
      fun h => bourgainParabolaTripleMoment h = y).card ≤
        (bourgainParabolaRepresentationFinset H y).card := by
  classical
  let fiber : Finset (Fin 3 → Fin H) :=
    (Finset.univ : Finset (Fin 3 → Fin H)).filter
      fun h => bourgainParabolaTripleMoment h = y
  apply Finset.card_le_card_of_injOn bourgainParabolaQuadraticCode
  · intro h hh
    exact bourgainParabolaQuadraticCode_mem_representation
      (Finset.mem_filter.mp hh).2
  · intro h hh k hk heq
    apply bourgainParabolaQuadraticCode_injective_on_fiber
    · exact (Finset.mem_filter.mp hh).2.trans
        (Finset.mem_filter.mp hk).2.symm
    · exact heq

end

end RHTower
