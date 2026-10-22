import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Position operators under a finite-range lattice evolution

A finite Laurent polynomial in commuting lattice shifts commutes with each of its own commutators
with a coordinate, because those commutators are again finite Laurent polynomials in the same
shifts.  The Heisenberg flow of a coordinate therefore terminates at first order:

`e^{tA} X e^{-tA} = X + t C`,   `C = AX - XA`,   `AC = CA`,

so a coordinate passes through the evolution at the cost of an affine shift.  Iterating over a word
of coordinates gives the exact form of the iterated position commutator identity: a word in the
coordinates passes through the evolution and becomes the same word in the shifted coordinates.
Expanding that word in powers of the time yields operator coefficients independent of the time,
with degree bounded by the length of the word.
-/

open NormedSpace

noncomputable section

namespace RHTower

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-! ## The evolution group -/

theorem exp_smul_mul_exp_neg_smul (A : 𝔸) (t : ℝ) :
    exp (t • A) * exp ((-t) • A) = 1 := by
  rw [← exp_add_of_commute (((Commute.refl A).smul_left t).smul_right (-t)), ← add_smul]
  simp

theorem exp_neg_smul_mul_exp_smul (A : 𝔸) (t : ℝ) :
    exp ((-t) • A) * exp (t • A) = 1 := by
  have h := exp_smul_mul_exp_neg_smul A (-t)
  rwa [neg_neg] at h

omit [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] in
theorem commute_exp_smul (A C : 𝔸) (h : Commute A C) (t : ℝ) :
    Commute (exp (t • A)) C :=
  ((h.symm.smul_right t).exp_right).symm

/-! ## The Heisenberg flow of a coordinate -/

/-- **`(16)` terminates at first order.**  The conjugated coordinate has constant velocity. -/
theorem hasDerivAt_conj_position (A X C : 𝔸) (hC : A * X - X * A = C) (hAC : Commute A C)
    (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u • A) * X * exp ((-u) • A)) C t := by
  have h1 : HasDerivAt (fun u : ℝ => exp (u • A)) (exp (t • A) * A) t :=
    hasDerivAt_exp_smul_const A t
  have h2 : HasDerivAt (fun u : ℝ => exp ((-u) • A)) (-(exp ((-t) • A) * A)) t := by
    have h := (hasDerivAt_exp_smul_const A (-t)).scomp t (hasDerivAt_neg t)
    simpa [Function.comp_def] using h
  have h3 : HasDerivAt (fun u : ℝ => exp (u • A) * X * exp ((-u) • A))
      (exp (t • A) * A * X * exp ((-t) • A)
        + exp (t • A) * X * -(exp ((-t) • A) * A)) t := (h1.mul_const X).mul h2
  have hAE : Commute A (exp ((-t) • A)) := ((Commute.refl A).smul_right (-t)).exp_right
  have hCE : Commute (exp (t • A)) C := commute_exp_smul A C hAC t
  have hval : exp (t • A) * A * X * exp ((-t) • A)
      + exp (t • A) * X * -(exp ((-t) • A) * A) = C := by
    have hswap : exp (t • A) * X * -(exp ((-t) • A) * A)
        = -(exp (t • A) * X * A * exp ((-t) • A)) := by
      rw [← hAE.eq]
      noncomm_ring
    rw [hswap]
    have hfold : exp (t • A) * A * X * exp ((-t) • A)
        - exp (t • A) * X * A * exp ((-t) • A)
        = exp (t • A) * (A * X - X * A) * exp ((-t) • A) := by
      noncomm_ring
    rw [← sub_eq_add_neg, hfold, hC, hCE.eq, mul_assoc, exp_smul_mul_exp_neg_smul, mul_one]
  rwa [hval] at h3

/-- **The Heisenberg flow of a coordinate is affine in time.** -/
theorem conj_position_eq (A X C : 𝔸) (hC : A * X - X * A = C) (hAC : Commute A C) (t : ℝ) :
    exp (t • A) * X * exp ((-t) • A) = X + t • C := by
  have hderiv : ∀ u : ℝ,
      HasDerivAt (fun v : ℝ => exp (v • A) * X * exp ((-v) • A) - v • C) 0 u := by
    intro u
    have h1 := hasDerivAt_conj_position A X C hC hAC u
    have h2 : HasDerivAt (fun v : ℝ => v • C) C u := by
      simpa using (hasDerivAt_id u).smul_const C
    have hsub : HasDerivAt (fun v : ℝ => exp (v • A) * X * exp ((-v) • A) - v • C) (C - C) u :=
      h1.sub h2
    rwa [sub_self] at hsub
  have hdiff : Differentiable ℝ (fun v : ℝ => exp (v • A) * X * exp ((-v) • A) - v • C) :=
    fun u => (hderiv u).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun u => (hderiv u).deriv) t 0
  simp only [zero_smul, neg_zero, exp_zero, one_mul, mul_one, sub_zero] at hconst
  linear_combination (norm := noncomm_ring) hconst

/-- **`(15)` for a single coordinate.**  A coordinate passes through the evolution at the cost of
an affine shift. -/
theorem position_mul_exp (A X C : 𝔸) (hC : A * X - X * A = C) (hAC : Commute A C) (t : ℝ) :
    X * exp ((-t) • A) = exp ((-t) • A) * (X + t • C) := by
  have h := conj_position_eq A X C hC hAC t
  calc X * exp ((-t) • A)
      = exp ((-t) • A) * exp (t • A) * X * exp ((-t) • A) := by
        rw [exp_neg_smul_mul_exp_smul, one_mul]
    _ = exp ((-t) • A) * (exp (t • A) * X * exp ((-t) • A)) := by noncomm_ring
    _ = exp ((-t) • A) * (X + t • C) := by rw [h]

/-! ## The iterated identity -/

/-- **`(15)`: a word of coordinates passes through the evolution and becomes the same word in the
shifted coordinates.** -/
theorem listProd_mul_exp {ι : Type*} (A : 𝔸) (X C : ι → 𝔸)
    (hC : ∀ i, A * X i - X i * A = C i) (hAC : ∀ i, Commute A (C i)) (t : ℝ) (l : List ι) :
    (l.map X).prod * exp ((-t) • A)
      = exp ((-t) • A) * (l.map (fun i => X i + t • C i)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [mul_assoc, ih, ← mul_assoc, position_mul_exp A (X i) (C i) (hC i) (hAC i), mul_assoc]

end RHTower

namespace RHTower

section Algebraic

variable {R 𝔹 : Type*} [CommSemiring R] [Ring 𝔹] [Algebra R 𝔹]

/-- **The degree bound in `(15)`.**  The shifted word is a polynomial in the time of degree at most
the word length, with coefficients independent of the time. -/
theorem exists_time_polynomial {ι : Type*} (X C : ι → 𝔹) (l : List ι) :
    ∃ P : ℕ → 𝔹, (∀ k, l.length < k → P k = 0) ∧
      ∀ t : R, (l.map (fun i => X i + t • C i)).prod
        = ∑ k ∈ Finset.range (l.length + 1), t ^ k • P k := by
  induction l with
  | nil =>
      refine ⟨fun k => if k = 0 then 1 else 0, ?_, ?_⟩
      · intro k hk
        simp only [List.length_nil] at hk
        show (if k = 0 then (1 : 𝔹) else 0) = 0
        rw [if_neg (by omega : ¬ k = 0)]
      · intro t
        simp
  | cons i l ih =>
      obtain ⟨P, hP0, hP⟩ := ih
      refine ⟨fun k => X i * P k + C i * (match k with | 0 => 0 | (j + 1) => P j), ?_, ?_⟩
      · intro k hk
        simp only [List.length_cons] at hk
        cases k with
        | zero => omega
        | succ j =>
            have h1 : P (j + 1) = 0 := hP0 _ (by omega)
            have h2 : P j = 0 := hP0 _ (by omega)
            show X i * P (j + 1) + C i * P j = 0
            rw [h1, h2, mul_zero, mul_zero, add_zero]
      · intro t
        have hPn : P (l.length + 1) = 0 := hP0 _ (by omega)
        have hA : X i * ∑ k ∈ Finset.range (l.length + 1), t ^ k • P k
            = ∑ k ∈ Finset.range (l.length + 1), t ^ k • (X i * P k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => mul_smul_comm _ _ _
        have hB : (t • C i) * ∑ k ∈ Finset.range (l.length + 1), t ^ k • P k
            = ∑ k ∈ Finset.range (l.length + 1), t ^ (k + 1) • (C i * P k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [smul_mul_assoc, mul_smul_comm, smul_smul]
          congr 1
          ring
        have hshift : ∑ k ∈ Finset.range (l.length + 1 + 1),
              t ^ k • (X i * P k + C i * (match k with | 0 => 0 | (j + 1) => P j))
            = (∑ k ∈ Finset.range (l.length + 1),
                t ^ (k + 1) • (X i * P (k + 1) + C i * P k)) + X i * P 0 := by
          rw [Finset.sum_range_succ' (fun k => t ^ k •
            (X i * P k + C i * (match k with | 0 => 0 | (j + 1) => P j))) (l.length + 1)]
          norm_num
        have hxsum : ∑ k ∈ Finset.range (l.length + 1), t ^ k • (X i * P k)
            = (∑ k ∈ Finset.range (l.length + 1), t ^ (k + 1) • (X i * P (k + 1)))
              + X i * P 0 := by
          rw [Finset.sum_range_succ (fun k => t ^ (k + 1) • (X i * P (k + 1))) l.length, hPn,
            mul_zero, smul_zero, add_zero,
            Finset.sum_range_succ' (fun k => t ^ k • (X i * P k)) l.length]
          norm_num
        rw [List.map_cons, List.prod_cons, hP t, List.length_cons, add_mul, hA, hB, hshift,
          hxsum]
        have hsplit : ∑ k ∈ Finset.range (l.length + 1),
              t ^ (k + 1) • (X i * P (k + 1) + C i * P k)
            = (∑ k ∈ Finset.range (l.length + 1), t ^ (k + 1) • (X i * P (k + 1)))
              + ∑ k ∈ Finset.range (l.length + 1), t ^ (k + 1) • (C i * P k) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => smul_add _ _ _
        rw [hsplit]
        abel

end Algebraic

end RHTower
