/-
# Exact torus `L⁶` estimate for the discrete parabola

For fixed `H`, the radix `3H+1` embeds every attained pair of triple moments
`(Σn, Σn²)` into one natural frequency.  Thus one-variable Fourier
orthogonality already separates the two moment coordinates on this finite
set.

We realize the resulting Fourier sum as a complex polynomial on the unit
circle.  Polynomial Parseval turns its sixth moment exactly into the grouped
triple-fiber `L²` mass.  The subpolynomial fiber theorem then supplies the
`H^ε` loss.
-/
import GaloisForLFunctions.RHTower.BourgainParabolaFiberSubpower
import Mathlib.Analysis.Polynomial.Fourier

open scoped BigOperators Polynomial

namespace RHTower

noncomputable section

/-- Radix separating the first moment of every parabola triple. -/
def bourgainParabolaMomentBase (H : ℕ) : ℕ :=
  3 * H + 1

/-- One-dimensional encoding of the first two triple moments. -/
def bourgainParabolaMomentCode (H : ℕ) (y : ℕ × ℕ) : ℕ :=
  y.1 + bourgainParabolaMomentBase H * y.2

/-- Frequency assigned to one point of the parabola. -/
def bourgainParabolaFrequency {H : ℕ} (n : Fin H) : ℕ :=
  bourgainIndex n +
    bourgainParabolaMomentBase H * bourgainIndex n ^ (2 : ℕ)

/-- The first moment of a triple lies strictly below the encoding radix. -/
theorem bourgainParabolaTripleMoment_fst_lt_base
    {H : ℕ} (h : Fin 3 → Fin H) :
    (bourgainParabolaTripleMoment h).1 <
      bourgainParabolaMomentBase H := by
  have h0 := bourgainIndex_le (h 0)
  have h1 := bourgainIndex_le (h 1)
  have h2 := bourgainIndex_le (h 2)
  simp only [bourgainParabolaTripleMoment, Fin.sum_univ_three,
    bourgainParabolaMomentBase]
  omega

/-- The radix encoding is injective on moment pairs attained by triples. -/
theorem bourgainParabolaMomentCode_injective_on_image
    {H : ℕ} {y z : ℕ × ℕ}
    (hy : y ∈ (Finset.univ : Finset (Fin 3 → Fin H)).image
      bourgainParabolaTripleMoment)
    (hz : z ∈ (Finset.univ : Finset (Fin 3 → Fin H)).image
      bourgainParabolaTripleMoment)
    (hcode :
      bourgainParabolaMomentCode H y =
        bourgainParabolaMomentCode H z) :
    y = z := by
  obtain ⟨h, -, hhy⟩ := Finset.mem_image.mp hy
  obtain ⟨k, -, hkz⟩ := Finset.mem_image.mp hz
  have hylt : y.1 < bourgainParabolaMomentBase H := by
    rw [← hhy]
    exact bourgainParabolaTripleMoment_fst_lt_base h
  have hzlt : z.1 < bourgainParabolaMomentBase H := by
    rw [← hkz]
    exact bourgainParabolaTripleMoment_fst_lt_base k
  have hfst : y.1 = z.1 := by
    have hmod := congrArg
      (fun n : ℕ => n % bourgainParabolaMomentBase H) hcode
    simpa [bourgainParabolaMomentCode,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hylt,
      Nat.mod_eq_of_lt hzlt] using hmod
  have hsndMul :
      bourgainParabolaMomentBase H * y.2 =
        bourgainParabolaMomentBase H * z.2 := by
    simpa [bourgainParabolaMomentCode, hfst] using hcode
  have hsnd : y.2 = z.2 :=
    Nat.mul_left_cancel (by
      simp [bourgainParabolaMomentBase]) hsndMul
  exact Prod.ext hfst hsnd

/-- Encoding a triple moment equals the sum of its three individual
frequencies. -/
theorem bourgainParabolaMomentCode_eq_sum_frequency
    {H : ℕ} (h : Fin 3 → Fin H) :
    bourgainParabolaMomentCode H
        (bourgainParabolaTripleMoment h) =
      ∑ j : Fin 3, bourgainParabolaFrequency (h j) := by
  simp only [bourgainParabolaMomentCode, bourgainParabolaTripleMoment,
    bourgainParabolaFrequency, Fin.sum_univ_three]
  ring

/-- Polynomial whose unit-circle values are the encoded parabola sum. -/
def bourgainParabolaPolynomial
    (H : ℕ) (a : Fin H → ℂ) : ℂ[X] :=
  ∑ n : Fin H, Polynomial.monomial
    (bourgainParabolaFrequency n) (a n)

/-- Cubic polynomial grouped by parabola triple moments. -/
def bourgainParabolaTriplePolynomial
    (H : ℕ) (a : Fin H → ℂ) : ℂ[X] :=
  ∑ h : Fin 3 → Fin H, Polynomial.monomial
    (bourgainParabolaMomentCode H
      (bourgainParabolaTripleMoment h))
    (bourgainTripleWeight a h)

/-- Cubing the original parabola polynomial produces the grouped triple
polynomial exactly. -/
theorem bourgainParabolaPolynomial_pow_three
    (H : ℕ) (a : Fin H → ℂ) :
    bourgainParabolaPolynomial H a ^ (3 : ℕ) =
      bourgainParabolaTriplePolynomial H a := by
  rw [bourgainParabolaPolynomial, Fintype.sum_pow]
  apply Fintype.sum_congr
  intro h
  simp only [Fin.prod_univ_three, bourgainTripleWeight,
    Polynomial.monomial_mul_monomial]
  rw [show
    bourgainParabolaFrequency (h 0) +
          bourgainParabolaFrequency (h 1) +
          bourgainParabolaFrequency (h 2) =
        bourgainParabolaMomentCode H (bourgainParabolaTripleMoment h) by
      simpa [Fin.sum_univ_three] using
        (bourgainParabolaMomentCode_eq_sum_frequency h).symm]

/-- Coefficients of the triple polynomial are sums over encoded fibers. -/
theorem coeff_bourgainParabolaTriplePolynomial
    (H : ℕ) (a : Fin H → ℂ) (m : ℕ) :
    (bourgainParabolaTriplePolynomial H a).coeff m =
      ∑ h ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter
          (fun h =>
            bourgainParabolaMomentCode H
              (bourgainParabolaTripleMoment h) = m),
        bourgainTripleWeight a h := by
  classical
  rw [bourgainParabolaTriplePolynomial]
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _
  rw [Polynomial.coeff_monomial]

/-- At an attained moment pair, the encoded coefficient is exactly its
triple-fiber amplitude. -/
theorem coeff_bourgainParabolaTriplePolynomial_code
    (H : ℕ) (a : Fin H → ℂ) (y : ℕ × ℕ)
    (hy : y ∈ (Finset.univ : Finset (Fin 3 → Fin H)).image
      bourgainParabolaTripleMoment) :
    (bourgainParabolaTriplePolynomial H a).coeff
        (bourgainParabolaMomentCode H y) =
      ∑ h ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter
          (fun h => bourgainParabolaTripleMoment h = y),
        bourgainTripleWeight a h := by
  rw [coeff_bourgainParabolaTriplePolynomial]
  congr 1
  ext h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hcode
    apply bourgainParabolaMomentCode_injective_on_image
    · exact Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩
    · exact hy
    · exact hcode
  · exact congrArg (bourgainParabolaMomentCode H)

/-- Every supported frequency of the triple polynomial comes from an
attained moment pair. -/
theorem support_bourgainParabolaTriplePolynomial_subset_image
    (H : ℕ) (a : Fin H → ℂ) :
    (bourgainParabolaTriplePolynomial H a).support ⊆
      ((Finset.univ : Finset (Fin 3 → Fin H)).image
        bourgainParabolaTripleMoment).image
          (bourgainParabolaMomentCode H) := by
  classical
  intro m hm
  rw [Polynomial.mem_support_iff] at hm
  by_contra hnot
  have hempty :
      (Finset.univ : Finset (Fin 3 → Fin H)).filter
          (fun h =>
            bourgainParabolaMomentCode H
              (bourgainParabolaTripleMoment h) = m) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro h hh
    apply hnot
    exact Finset.mem_image.mpr
      ⟨bourgainParabolaTripleMoment h,
        Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩,
        (Finset.mem_filter.mp hh).2⟩
  apply hm
  rw [coeff_bourgainParabolaTriplePolynomial, hempty]
  simp

/-- Exact polynomial Parseval, enlarged from support to all attained encoded
moment pairs. -/
theorem circleAverage_bourgainParabolaTriplePolynomial_le_fiberMass
    (H : ℕ) (a : Fin H → ℂ) :
    Real.circleAverage
        (fun z => ‖(bourgainParabolaTriplePolynomial H a).eval z‖ ^ (2 : ℕ))
        0 1 ≤
      ∑ y ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).image
            bourgainParabolaTripleMoment,
        ‖∑ h ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter
            (fun h => bourgainParabolaTripleMoment h = y),
          bourgainTripleWeight a h‖ ^ (2 : ℕ) := by
  classical
  let Q := bourgainParabolaTriplePolynomial H a
  let Y : Finset (ℕ × ℕ) :=
    (Finset.univ : Finset (Fin 3 → Fin H)).image
      bourgainParabolaTripleMoment
  have hparseval := Polynomial.sum_sq_norm_coeff_eq_circleAverage Q
  calc
    Real.circleAverage (fun z => ‖Q.eval z‖ ^ (2 : ℕ)) 0 1 =
        ∑ m ∈ Q.support, ‖Q.coeff m‖ ^ (2 : ℕ) := hparseval.symm
    _ ≤ ∑ m ∈ Y.image (bourgainParabolaMomentCode H),
        ‖Q.coeff m‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa [Q, Y] using
          support_bourgainParabolaTriplePolynomial_subset_image H a
      · intro m _ _
        exact sq_nonneg _
    _ = ∑ y ∈ Y,
        ‖∑ h ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter
            (fun h => bourgainParabolaTripleMoment h = y),
          bourgainTripleWeight a h‖ ^ (2 : ℕ) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro y hy
        rw [show Q = bourgainParabolaTriplePolynomial H a by rfl,
          coeff_bourgainParabolaTriplePolynomial_code H a y hy]
      · intro y hy z hz hcode
        exact bourgainParabolaMomentCode_injective_on_image hy hz hcode
    _ = ∑ y ∈
          (Finset.univ : Finset (Fin 3 → Fin H)).image
            bourgainParabolaTripleMoment,
        ‖∑ h ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter
            (fun h => bourgainParabolaTripleMoment h = y),
          bourgainTripleWeight a h‖ ^ (2 : ℕ) := by rfl

/-- **Discrete parabola `L⁶` estimate on the unit circle.**  The radix
encoding realizes the two moment coordinates without collisions, and the
sixth moment has only an `H^ε` loss. -/
theorem circleAverage_bourgainParabolaPolynomial_norm_pow_six_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ) (a : Fin H → ℂ),
        Real.circleAverage
            (fun z => ‖(bourgainParabolaPolynomial H a).eval z‖ ^ (6 : ℕ))
            0 1 ≤
          C * (H : ℝ) ^ ε *
            (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  obtain ⟨C, hC, hfiber⟩ := bourgainParabolaFiberL2_subpower hε
  refine ⟨C, hC, ?_⟩
  intro H a
  have hcubic :
      Real.circleAverage
          (fun z => ‖(bourgainParabolaPolynomial H a).eval z‖ ^ (6 : ℕ))
          0 1 =
        Real.circleAverage
          (fun z =>
            ‖(bourgainParabolaTriplePolynomial H a).eval z‖ ^ (2 : ℕ))
          0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z _
    rw [← bourgainParabolaPolynomial_pow_three H a]
    change
      ‖(bourgainParabolaPolynomial H a).eval z‖ ^ (6 : ℕ) =
        ‖(bourgainParabolaPolynomial H a ^ (3 : ℕ)).eval z‖ ^ (2 : ℕ)
    rw [Polynomial.eval_pow, norm_pow]
    ring
  rw [hcubic]
  exact (circleAverage_bourgainParabolaTriplePolynomial_le_fiberMass H a).trans
    (hfiber H a)

end

end RHTower
