/-
# Finite fiber `L²` inequality for decoupling moments

Moment expansions group tuples by the value of a finite moment map.  This
module proves the exact Cauchy--Schwarz estimate: if every fiber has at most
`R` elements, then the squared `L²` mass of the grouped amplitudes is at most
`R` times the original coefficient mass.

It then specializes the statement to triples on the parabola
`n ↦ (n,n²)`, the discrete planar `L⁶` input used repeatedly in Bourgain's
decoupling argument.
-/
import GaloisForLFunctions.RHTower.BourgainGaussianFourier
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Finite Cauchy--Schwarz grouped by fibers of a map. -/
theorem sum_norm_fiberSum_sq_le
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (φ : ι → κ) (w : ι → ℂ) {R : ℝ}
    (hfiber :
      ∀ y ∈ (Finset.univ : Finset ι).image φ,
        (((Finset.univ : Finset ι).filter fun i => φ i = y).card : ℝ) ≤ R) :
    ∑ y ∈ (Finset.univ : Finset ι).image φ,
        ‖∑ i ∈ (Finset.univ : Finset ι).filter (fun i => φ i = y),
          w i‖ ^ (2 : ℕ) ≤
      R * ∑ i : ι, ‖w i‖ ^ (2 : ℕ) := by
  classical
  let fiber : κ → Finset ι := fun y =>
    (Finset.univ : Finset ι).filter fun i => φ i = y
  have hone (y : κ) :
      ‖∑ i ∈ fiber y, w i‖ ^ (2 : ℕ) ≤
        (fiber y).card * ∑ i ∈ fiber y, ‖w i‖ ^ (2 : ℕ) := by
    have hnorm :
        ‖∑ i ∈ fiber y, w i‖ ≤ ∑ i ∈ fiber y, ‖w i‖ :=
      norm_sum_le _ _
    have hpow :
        ‖∑ i ∈ fiber y, w i‖ ^ (2 : ℕ) ≤
          (∑ i ∈ fiber y, ‖w i‖) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (fiber y) (fun _ => (1 : ℝ)) (fun i => ‖w i‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul,
      mul_one] at hcs
    exact hpow.trans hcs
  have honeR (y : κ)
      (hy : y ∈ (Finset.univ : Finset ι).image φ) :
      ‖∑ i ∈ fiber y, w i‖ ^ (2 : ℕ) ≤
        R * ∑ i ∈ fiber y, ‖w i‖ ^ (2 : ℕ) := by
    exact (hone y).trans
      (mul_le_mul_of_nonneg_right
        (by simpa [fiber] using hfiber y hy)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    ∑ y ∈ (Finset.univ : Finset ι).image φ,
        ‖∑ i ∈ (Finset.univ : Finset ι).filter (fun i => φ i = y),
          w i‖ ^ (2 : ℕ) ≤
      ∑ y ∈ (Finset.univ : Finset ι).image φ,
        R * ∑ i ∈ fiber y, ‖w i‖ ^ (2 : ℕ) := by
      exact Finset.sum_le_sum fun y hy => by
        simpa [fiber] using honeR y hy
    _ = R * ∑ y ∈ (Finset.univ : Finset ι).image φ,
        ∑ i ∈ fiber y, ‖w i‖ ^ (2 : ℕ) := by
      rw [Finset.mul_sum]
    _ = R * ∑ i : ι, ‖w i‖ ^ (2 : ℕ) := by
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset ι))
        (t := (Finset.univ : Finset ι).image φ)
        (g := φ)
        (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        (fun i => ‖w i‖ ^ (2 : ℕ))

/-- First two moments of a triple on the parabola. -/
def bourgainParabolaTripleMoment {H : ℕ}
    (h : Fin 3 → Fin H) : ℕ × ℕ :=
  (∑ j : Fin 3, bourgainIndex (h j),
    ∑ j : Fin 3, bourgainIndex (h j) ^ (2 : ℕ))

/-- Product coefficient attached to a triple. -/
def bourgainTripleWeight {H : ℕ}
    (a : Fin H → ℂ) (h : Fin 3 → Fin H) : ℂ :=
  ∏ j : Fin 3, a (h j)

/-- The squared coefficient mass of all triples factorizes exactly. -/
theorem sum_norm_bourgainTripleWeight_sq
    (H : ℕ) (a : Fin H → ℂ) :
    ∑ h : Fin 3 → Fin H,
        ‖bourgainTripleWeight a h‖ ^ (2 : ℕ) =
      (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  calc
    ∑ h : Fin 3 → Fin H,
        ‖bourgainTripleWeight a h‖ ^ (2 : ℕ) =
      ∑ h : Fin 3 → Fin H,
        ∏ j : Fin 3, ‖a (h j)‖ ^ (2 : ℕ) := by
      apply Fintype.sum_congr
      intro h
      simp [bourgainTripleWeight, norm_prod, Finset.prod_pow]
    _ = ∏ _j : Fin 3, ∑ n : Fin H, ‖a n‖ ^ (2 : ℕ) :=
      (Fintype.prod_sum fun (_j : Fin 3) n => ‖a n‖ ^ (2 : ℕ)).symm
    _ = (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
      simp

/-- Weighted discrete planar `L⁶` estimate reduced exactly to a uniform
fiber-cardinality bound for `(Σn,Σn²)`. -/
theorem bourgainParabolaFiberL2_le
    (H : ℕ) (a : Fin H → ℂ) {R : ℝ}
    (hfiber :
      ∀ y ∈
        (Finset.univ : Finset (Fin 3 → Fin H)).image
          bourgainParabolaTripleMoment,
        (((Finset.univ : Finset (Fin 3 → Fin H)).filter
          fun h => bourgainParabolaTripleMoment h = y).card : ℝ) ≤ R) :
    ∑ y ∈
        (Finset.univ : Finset (Fin 3 → Fin H)).image
          bourgainParabolaTripleMoment,
      ‖∑ h ∈ (Finset.univ : Finset (Fin 3 → Fin H)).filter
          (fun h => bourgainParabolaTripleMoment h = y),
        bourgainTripleWeight a h‖ ^ (2 : ℕ) ≤
      R * (∑ n : Fin H, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
  calc
    _ ≤ R * ∑ h : Fin 3 → Fin H,
        ‖bourgainTripleWeight a h‖ ^ (2 : ℕ) :=
      sum_norm_fiberSum_sq_le bourgainParabolaTripleMoment
        (bourgainTripleWeight a) hfiber
    _ = _ := by rw [sum_norm_bourgainTripleWeight_sq]

end

end RHTower
