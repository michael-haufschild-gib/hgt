/-
# Hurwitz all-N — row close from rational-tail independence

This file isolates the algebraic close used by
`hurwitz-quadratic-all-n-tail-independence.md` after the quadratic weight
filtration has supplied `A_w = 0`.

No analytic input is hidden here.  The only non-algebraic statement is the
explicit `RationalTailIndependent` interface: a polynomial-coefficient relation
among the finitely many tail sequences must have all coefficients zero.
-/
import GaloisForLFunctions.Hurwitz.AllNQuadFilt
import GaloisForLFunctions.Hurwitz.DescentAlgebra
import GaloisForLFunctions.Hurwitz.HurwitzZeta
import GaloisForLFunctions.Hurwitz.N2Survivor
import GaloisForLFunctions.Hurwitz.PolylogPoleTower

open Polynomial Filter

namespace HurwitzAllNTailIndependence

variable {N : ℕ}

/-- Rational-tail independence for a finite tail ladder `V`.

This is the Lean shape of Lemma 1 in
`hurwitz-quadratic-all-n-tail-independence.md`, after denominators have been
cleared: if a polynomial-coefficient combination of the tail sequences agrees
eventually with a polynomial, then every tail coefficient and the polynomial
right side vanish. -/
def RationalTailIndependent (V : Fin (N + 1) → ℕ → ℂ) : Prop :=
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n → (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * V i n)
      = P.eval (-(n : ℂ))) →
    (∀ i, coeff i = 0) ∧ P = 0

/-- Coefficients of the tail part in the row equation for column `j`. -/
noncomputable def rowTailCoeff (eta : Fin (N + 1) → ℂ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (j i : Fin (N + 1)) :
    Polynomial ℂ :=
  C (2 * eta i) * q i j

/-- Polynomial right side of the row equation after moving the constant tail
values and the linear coefficient to the other side. -/
noncomputable def rowTailRhs (zeta : Fin (N + 1) → ℂ)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (j : Fin (N + 1)) : Polynomial ℂ :=
  -(l j + ∑ i : Fin (N + 1), C (2 * zeta i) * q i j)

/-- One row closes from the rational-tail interface.

The hypothesis `hrow` is the coefficient equation extracted from the
`x^(-s-j)` term:
`l_j(-n) + 2 * sum_i q_ij(-n) * (zeta_i + eta_i * V_i(n)) = 0`.
The interface kills all `q_ij`, then the polynomial right side kills `l_j`. -/
theorem row_close_of_rationalTailIndependent
    (V : Fin (N + 1) → ℕ → ℂ) (hTail : RationalTailIndependent V)
    (eta zeta : Fin (N + 1) → ℂ) (heta : ∀ i, eta i ≠ 0)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (j : Fin (N + 1)) {M : ℕ}
    (hrow : ∀ n, M ≤ n →
      (l j).eval (-(n : ℂ)) +
        (∑ i : Fin (N + 1),
          (q i j).eval (-(n : ℂ)) * (2 * (zeta i + eta i * V i n))) = 0) :
    (∀ i, q i j = 0) ∧ l j = 0 := by
  have hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (rowTailCoeff eta q j i).eval (-(n : ℂ)) * V i n)
        = (rowTailRhs zeta q l j).eval (-(n : ℂ)) := by
    intro n hn
    have hr := hrow n hn
    have hr' : (l j).eval (-(n : ℂ)) +
        (∑ i : Fin (N + 1),
          (zeta i + V i n * eta i) * (2 * (q i j).eval (-(n : ℂ)))) = 0 := by
      simpa [mul_assoc, mul_left_comm, mul_comm, add_comm] using hr
    have hsum :
        (∑ i : Fin (N + 1),
          (zeta i + V i n * eta i) * (2 * (q i j).eval (-(n : ℂ)))) =
        (∑ i : Fin (N + 1), (2 * zeta i) * (q i j).eval (-(n : ℂ))) +
        (∑ i : Fin (N + 1), (2 * eta i) * (q i j).eval (-(n : ℂ)) * V i n) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have hzero : (l j).eval (-(n : ℂ)) +
        (∑ i : Fin (N + 1), (2 * zeta i) * (q i j).eval (-(n : ℂ))) +
        (∑ i : Fin (N + 1), (2 * eta i) * (q i j).eval (-(n : ℂ)) * V i n) = 0 := by
      rw [add_assoc, ← hsum]
      exact hr'
    simp only [rowTailCoeff, rowTailRhs, eval_neg, eval_add, eval_finsetSum, eval_mul, eval_C]
    linear_combination hzero
  obtain ⟨hcoeff, hP⟩ := hTail (rowTailCoeff eta q j) (rowTailRhs zeta q l j) hrel
  have hq : ∀ i, q i j = 0 := by
    intro i
    have hc : (C (2 * eta i) : Polynomial ℂ) ≠ 0 := by
      simpa using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (heta i)
    have hprod := hcoeff i
    simp only [rowTailCoeff] at hprod
    exact (mul_eq_zero.mp hprod).resolve_left hc
  have hl : l j = 0 := by
    have hsum : (∑ i : Fin (N + 1), C (2 * zeta i) * q i j) = 0 := by
      simp [hq]
    have hP' := hP
    simp only [rowTailRhs, hsum, add_zero, neg_eq_zero] at hP'
    exact hP'
  exact ⟨hq, hl⟩

/-- All rows and the residual constant close from rational-tail independence
and an eventual vanishing statement for the constant coefficient. -/
theorem rows_and_constant_close_of_rationalTailIndependent
    (V : Fin (N + 1) → ℕ → ℂ) (hTail : RationalTailIndependent V)
    (eta zeta : Fin (N + 1) → ℂ) (heta : ∀ i, eta i ≠ 0)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (hrow : ∀ j : Fin (N + 1), ∃ M : ℕ, ∀ n, M ≤ n →
      (l j).eval (-(n : ℂ)) +
        (∑ i : Fin (N + 1),
          (q i j).eval (-(n : ℂ)) * (2 * (zeta i + eta i * V i n))) = 0)
    (hcc : ∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) :
    (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0 := by
  have hrows : ∀ j : Fin (N + 1), (∀ i, q i j = 0) ∧ l j = 0 := by
    intro j
    obtain ⟨M, hM⟩ := hrow j
    exact row_close_of_rationalTailIndependent V hTail eta zeta heta q l j hM
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact (hrows j).1 i
  · intro j
    exact (hrows j).2
  · obtain ⟨M, hM⟩ := hcc
    exact HurwitzDescent.eq_zero_of_eventually_neg_nat_roots
      (p := cc) (N := M) (fun n hn => hM n hn)

/-! ## Proven base case for the rational-tail interface -/

/-- A single tail sequence with noninteger-power finite difference satisfies the
rational-tail interface.  This is the `N=0` case of Lemma 1, proved by the
existing N=2 survivor obstruction. -/
theorem rationalTailIndependent_single_of_diff {s η : ℂ}
    (hs : ∀ k : ℤ, s ≠ (k : ℂ)) (hη : η ≠ 0) {V : ℕ → ℂ}
    (hdiff : ∀ n : ℕ, 1 ≤ n → V n - V (n - 1) = η * (n : ℂ) ^ (-s)) :
    RationalTailIndependent (N := 0) (fun _ => V) := by
  intro coeff P M hrel
  have hsurvRel : ∀ᶠ n : ℕ in Filter.atTop,
      (coeff 0).eval (-(n : ℂ)) * V n + (-P).eval (-(n : ℂ)) = 0 := by
    filter_upwards [eventually_ge_atTop M] with n hn
    have hr := hrel n hn
    have hsum : (∑ i : Fin (0 + 1), (coeff i).eval (-(n : ℂ)) * V n)
        = (coeff 0).eval (-(n : ℂ)) * V n := by
      apply Finset.sum_eq_single 0
      · intro b _ hb
        fin_cases b
        exact (hb rfl).elim
      · intro hnot
        simp at hnot
    rw [hsum] at hr
    rw [eval_neg]
    linear_combination hr
  have hcoeff0 : coeff 0 = 0 :=
    HurwitzN2Survivor.survivor_q_eq_zero hs hη hdiff hsurvRel
  have hP : P = 0 := by
    apply HurwitzDescent.eq_zero_of_eventually_neg_nat_roots (p := P) (N := M)
    intro n hn
    have hr := hrel n hn
    have hsum : (∑ i : Fin (0 + 1), (coeff i).eval (-(n : ℂ)) * V n)
        = (coeff 0).eval (-(n : ℂ)) * V n := by
      apply Finset.sum_eq_single 0
      · intro b _ hb
        fin_cases b
        exact (hb rfl).elim
      · intro hnot
        simp at hnot
    rw [hsum, hcoeff0, eval_zero, zero_mul] at hr
    exact hr.symm
  exact ⟨fun i => by fin_cases i; exact hcoeff0, hP⟩

end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence

open HurwitzZetaShift

/-- The actual Hurwitz negative-integer tail sequence for any fixed shift is
rational-tail independent in the singleton sense. -/
theorem rationalTailIndependent_hzeta_shift_neg_nat_single {s : ℂ}
    (hs1 : 1 < s.re) (hsZ : ∀ k : ℤ, s ≠ (k : ℂ)) (j : ℕ) :
    RationalTailIndependent (N := 0)
      (fun _ n => hzeta (s + (j : ℂ)) (-(n : ℂ))) := by
  have hs1j : 1 < (s + (j : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hsZj : ∀ k : ℤ, s + (j : ℂ) ≠ (k : ℂ) := by
    intro k h
    apply hsZ (k - (j : ℤ))
    rw [Int.cast_sub, Int.cast_natCast]
    linear_combination h
  apply rationalTailIndependent_single_of_diff hsZj (Complex.exp_ne_zero _)
  intro n hn
  simpa using hzeta_neg_nat_diff (s := s + (j : ℂ)) hs1j hn

end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence

/-- Rational-tail independence is invariant under nonzero diagonal affine changes of the tail
sequences, because constants are absorbed into the polynomial right side. -/
theorem rationalTailIndependent_affine_of_rationalTailIndependent
    {V W : Fin (N + 1) → ℕ → ℂ} (hTail : RationalTailIndependent V)
    (eta zeta : Fin (N + 1) → ℂ) (heta : ∀ i, eta i ≠ 0)
    (hW : ∀ i n, W i n = zeta i + eta i * V i n) :
    RationalTailIndependent W := by
  intro coeff P M hrel
  let coeff' : Fin (N + 1) → Polynomial ℂ := fun i => C (eta i) * coeff i
  let P' : Polynomial ℂ := P - ∑ i : Fin (N + 1), C (zeta i) * coeff i
  have hrelV : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff' i).eval (-(n : ℂ)) * V i n) = P'.eval (-(n : ℂ)) := by
    intro n hn
    have hr := hrel n hn
    have hsplit :
        (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * W i n) =
          (∑ i : Fin (N + 1), zeta i * (coeff i).eval (-(n : ℂ))) +
          (∑ i : Fin (N + 1), (coeff' i).eval (-(n : ℂ)) * V i n) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hW i n]
      simp only [coeff', eval_mul, eval_C]
      ring
    rw [hsplit] at hr
    simp only [P', eval_sub, eval_finsetSum, eval_mul, eval_C]
    linear_combination hr
  obtain ⟨hcoeff', hP'⟩ := hTail coeff' P' hrelV
  have hcoeff : ∀ i, coeff i = 0 := by
    intro i
    have hprod := hcoeff' i
    simp only [coeff'] at hprod
    exact (mul_eq_zero.mp hprod).resolve_left (by simpa using heta i)
  have hP : P = 0 := by
    have hsum : (∑ i : Fin (N + 1), C (zeta i) * coeff i) = 0 := by
      simp [hcoeff]
    simpa [P', hsum] using hP'
  exact ⟨hcoeff, hP⟩

namespace HurwitzZetaTail

open HurwitzZetaShift

/-- The finite harmonic-sum part of the shifted negative-integer Hurwitz value. -/
noncomputable def harmonicTail (s : ℂ) (i : Fin (N + 1)) (n : ℕ) : ℂ :=
  ∑ l ∈ Finset.range n, ((l : ℂ) + 1) ^ (-(s + (i : ℂ)))

/-- Full shifted Hurwitz tail independence follows from independence of the harmonic-sum parts; the
constant `ζ(s+i)` and nonzero phase `exp(-πi(s+i))` are an invertible affine change. -/
theorem rationalTailIndependent_hzeta_shift_neg_nat_of_harmonic {s : ℂ} (hs1 : 1 < s.re)
    (hH : RationalTailIndependent (N := N) (harmonicTail (N := N) s)) :
    RationalTailIndependent (N := N)
      (fun i n => hzeta (s + (i : ℂ)) (-(n : ℂ))) := by
  apply rationalTailIndependent_affine_of_rationalTailIndependent (N := N) hH
    (eta := fun i => Complex.exp (-((Real.pi : ℂ) * Complex.I * (s + (i : ℂ)))))
    (zeta := fun i => hzeta (s + (i : ℂ)) 0)
  · intro i
    exact Complex.exp_ne_zero _
  · intro i n
    have hsi : 1 < (s + (i : ℂ)).re := by
      rw [Complex.add_re, Complex.natCast_re]
      have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg i.val
      linarith
    simp only [harmonicTail]
    exact hzeta_neg_nat hsi n

end HurwitzZetaTail

end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

/-- The singleton harmonic-sum tail has rational-tail independence; its finite difference is the
noninteger power `n^{-s}`. -/
theorem rationalTailIndependent_harmonic_single {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ)) :
    RationalTailIndependent (N := 0) (harmonicTail (N := 0) s) := by
  apply rationalTailIndependent_single_of_diff hsZ (by norm_num : (1 : ℂ) ≠ 0)
  intro n hn
  simp only [harmonicTail]
  have hsucc : Finset.range n = Finset.range ((n - 1) + 1) := by congr 1; omega
  rw [hsucc, Finset.sum_range_succ]
  have hcast : ((↑(n - 1) : ℂ) + 1) = (n : ℂ) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [hcast]
  ring_nf

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

open HurwitzZetaShift

/-- Actual shifted-Hurwitz row/constant close after reducing the rational-tail input to harmonic-tail
independence. This is the all-`N` row descent with the real tail values
`n ↦ ζ(s+i,-n)`, leaving only the harmonic-sum family independence as input. -/
theorem rows_and_constant_close_of_hzeta_shift_neg_nat_of_harmonic {N : ℕ} {s : ℂ}
    (hs1 : 1 < s.re)
    (hH : RationalTailIndependent (N := N) (harmonicTail (N := N) s))
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (hrow : ∀ j : Fin (N + 1), ∃ M : ℕ, ∀ n, M ≤ n →
      (l j).eval (-(n : ℂ)) +
        (∑ i : Fin (N + 1),
          (q i j).eval (-(n : ℂ)) *
            (2 * hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0)
    (hcc : ∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) :
    (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0 := by
  apply rows_and_constant_close_of_rationalTailIndependent
    (V := fun i n => hzeta (s + (i : ℂ)) (-(n : ℂ)))
    (hTail := rationalTailIndependent_hzeta_shift_neg_nat_of_harmonic (N := N) hs1 hH)
    (eta := fun _ => (1 : ℂ)) (zeta := fun _ => (0 : ℂ))
  · intro i
    norm_num
  · intro j
    obtain ⟨M, hM⟩ := hrow j
    refine ⟨M, ?_⟩
    intro n hn
    simpa using hM n hn
  · exact hcc

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

/-- The exact analytic bridge needed by the polylog proof of harmonic-tail independence: every eventual
polynomial-coefficient relation among the harmonic tails yields the Gamma pole-root identities for the
coefficient polynomials. The theorem below is the algebraic close after this bridge. -/
def HarmonicPoleRootInput (N : ℕ) (s : ℂ) : Prop :=
  ∀ (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) →
    ∀ (d n : ℕ),
      (∑ i : Fin (N + 1),
        (coeff i).coeff d * Complex.Gamma (1 - s - (i : ℂ)) *
          (HurwitzPolylogPoleTower.twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (i : ℕ)) = 0

/-- Harmonic-tail rational independence from the polylog pole-root bridge. This is the algebraic
endgame of Lemma 1 in the all-`N` Hurwitz card: once the fractional-polylog analysis supplies the
Gamma pole-root identities, the committed pole-tower injectivity kills every tail coefficient, and the
residual polynomial then vanishes on all sufficiently many negative integers. -/
theorem rationalTailIndependent_harmonic_of_poleRootInput {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ)) (hpole : HarmonicPoleRootInput N s) :
    RationalTailIndependent (N := N) (harmonicTail (N := N) s) := by
  intro coeff P M hrel
  have hcoeff : ∀ i, coeff i = 0 :=
    HurwitzPolylogPoleTower.polynomials_zero_of_gamma_pole_sum_roots hsZ (hpole coeff P hrel)
  have hP : P = 0 := by
    apply HurwitzDescent.eq_zero_of_eventually_neg_nat_roots (p := P) (N := M)
    intro n hn
    have hr := hrel n hn
    have hsum : (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * harmonicTail (N := N) s i n) = 0 := by
      simp [hcoeff]
    rw [hsum] at hr
    exact hr.symm
  exact ⟨hcoeff, hP⟩

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

open HurwitzZetaShift

/-- Actual shifted-Hurwitz row/constant close directly from the polylog pole-root bridge. This composes
`rationalTailIndependent_harmonic_of_poleRootInput` with the affine reduction from actual
`ζ(s+i,-n)` values to harmonic sums. -/
theorem rows_and_constant_close_of_hzeta_shift_neg_nat_of_poleRootInput {N : ℕ} {s : ℂ}
    (hs1 : 1 < s.re) (hsZ : ∀ k : ℤ, s ≠ (k : ℂ)) (hpole : HarmonicPoleRootInput N s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (hrow : ∀ j : Fin (N + 1), ∃ M : ℕ, ∀ n, M ≤ n →
      (l j).eval (-(n : ℂ)) +
        (∑ i : Fin (N + 1),
          (q i j).eval (-(n : ℂ)) *
            (2 * hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0)
    (hcc : ∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) :
    (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0 := by
  exact rows_and_constant_close_of_hzeta_shift_neg_nat_of_harmonic hs1
    (rationalTailIndependent_harmonic_of_poleRootInput hsZ hpole) q l cc hrow hcc

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

open HurwitzZetaShift

/-- Actual shifted-Hurwitz rational-tail independence directly from the polylog pole-root bridge. -/
theorem rationalTailIndependent_hzeta_shift_neg_nat_of_poleRootInput {N : ℕ} {s : ℂ}
    (hs1 : 1 < s.re) (hsZ : ∀ k : ℤ, s ≠ (k : ℂ)) (hpole : HarmonicPoleRootInput N s) :
    RationalTailIndependent (N := N)
      (fun i n => hzeta (s + (i : ℂ)) (-(n : ℂ))) :=
  rationalTailIndependent_hzeta_shift_neg_nat_of_harmonic hs1
    (rationalTailIndependent_harmonic_of_poleRootInput hsZ hpole)

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

/-- The pole-root bridge is automatic from harmonic-tail rational independence. This records the reverse
implication to `rationalTailIndependent_harmonic_of_poleRootInput`, making the remaining Hurwitz analytic
input exact rather than oversized. -/
theorem harmonicPoleRootInput_of_rationalTailIndependent {N : ℕ} {s : ℂ}
    (hTail : RationalTailIndependent (N := N) (harmonicTail (N := N) s)) :
    HarmonicPoleRootInput N s := by
  intro coeff P M hrel d n
  have hcoeff : ∀ i, coeff i = 0 := (hTail coeff P hrel).1
  simp [hcoeff]

/-- For nonintegral `s`, the polylog pole-root bridge is equivalent to the harmonic-tail rational
independence target. -/
theorem rationalTailIndependent_harmonic_iff_poleRootInput {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ)) :
    RationalTailIndependent (N := N) (harmonicTail (N := N) s) ↔ HarmonicPoleRootInput N s := by
  constructor
  · exact harmonicPoleRootInput_of_rationalTailIndependent
  · exact rationalTailIndependent_harmonic_of_poleRootInput hsZ

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

/-- The exact polylog pole-root bridge is unconditional for the singleton harmonic tail. This is the
`N = 0` base case of the all-`N` Hurwitz tail-independence provider: the existing finite-difference
nonrationality theorem already proves the singleton rational-tail interface, and the pole-root bridge
is its formal equivalent. -/
theorem harmonicPoleRootInput_zero {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ)) :
    HarmonicPoleRootInput 0 s := by
  exact harmonicPoleRootInput_of_rationalTailIndependent
    (N := 0) (s := s) (rationalTailIndependent_harmonic_single (s := s) hsZ)

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

open HurwitzZetaShift

/-- Unconditional singleton-ladder row/constant close for the actual shifted Hurwitz values. This is the
`N = 0` instance of `rows_and_constant_close_of_hzeta_shift_neg_nat_of_harmonic` with the singleton
harmonic-tail provider discharged by `rationalTailIndependent_harmonic_single`. -/
theorem rows_and_constant_close_of_hzeta_shift_neg_nat_N0 {s : ℂ}
    (hs1 : 1 < s.re) (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (q : Fin (0 + 1) → Fin (0 + 1) → Polynomial ℂ)
    (l : Fin (0 + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (hrow : ∀ j : Fin (0 + 1), ∃ M : ℕ, ∀ n, M ≤ n →
      (l j).eval (-(n : ℂ)) +
        (∑ i : Fin (0 + 1),
          (q i j).eval (-(n : ℂ)) *
            (2 * hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0)
    (hcc : ∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) :
    (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0 := by
  exact rows_and_constant_close_of_hzeta_shift_neg_nat_of_harmonic (N := 0) hs1
    (rationalTailIndependent_harmonic_single (s := s) hsZ) q l cc hrow hcc

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

open HurwitzZetaShift

/-- Scalar singleton-ladder row/constant close for the actual shifted Hurwitz values. This unpacks the
`N = 0` row-close theorem to ordinary coefficient polynomials. -/
theorem rows_and_constant_close_of_hzeta_shift_neg_nat_N0_scalar {s : ℂ}
    (hs1 : 1 < s.re) (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (q l cc : Polynomial ℂ)
    (hrow : ∃ M : ℕ, ∀ n, M ≤ n →
      l.eval (-(n : ℂ)) + q.eval (-(n : ℂ)) * (2 * hzeta s (-(n : ℂ))) = 0)
    (hcc : ∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) :
    q = 0 ∧ l = 0 ∧ cc = 0 := by
  let qF : Fin (0 + 1) → Fin (0 + 1) → Polynomial ℂ := fun _ _ => q
  let lF : Fin (0 + 1) → Polynomial ℂ := fun _ => l
  have hrowF : ∀ j : Fin (0 + 1), ∃ M : ℕ, ∀ n, M ≤ n →
      (lF j).eval (-(n : ℂ)) +
        (∑ i : Fin (0 + 1),
          (qF i j).eval (-(n : ℂ)) *
            (2 * hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0 := by
    intro j
    obtain ⟨M, hM⟩ := hrow
    refine ⟨M, ?_⟩
    intro n hn
    fin_cases j
    simpa [qF, lF] using hM n hn
  obtain ⟨hq, hl, hcc0⟩ := rows_and_constant_close_of_hzeta_shift_neg_nat_N0
    (s := s) hs1 hsZ qF lF cc hrowF hcc
  exact ⟨hq 0 0, hl 0, hcc0⟩

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

/-- Finite difference of the harmonic tail: `H_i(n)-H_i(n-1)=n^(-(s+i))`. -/
theorem harmonicTail_sub_prev {N : ℕ} (s : ℂ) (i : Fin (N + 1)) {n : ℕ} (hn : 1 ≤ n) :
    harmonicTail (N := N) s i n - harmonicTail (N := N) s i (n - 1) =
      (n : ℂ) ^ (-(s + (i : ℂ))) := by
  simp only [harmonicTail]
  have hsucc : Finset.range n = Finset.range ((n - 1) + 1) := by congr 1; omega
  rw [hsucc, Finset.sum_range_succ]
  have hcast : ((↑(n - 1) : ℂ) + 1) = (n : ℂ) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [hcast]
  ring_nf

/-- Constant-coefficient harmonic-tail relations are impossible for every finite ladder. This is the
first finite-difference subcase of the all-`N` rational-tail provider: differencing kills the constant
coefficients and leaves exactly the shifted-power obstruction. -/
theorem constant_coefficients_zero_of_harmonicTail_relation {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (c : Fin (N + 1) → ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) :
    (∀ i : Fin (N + 1), c i = 0) ∧ P = 0 := by
  let Q : Polynomial ℂ := P.comp (-X) - P.comp (1 - X)
  have hdiff : ∀ᶠ n : ℕ in atTop,
      (∑ i : Fin (N + 1), c i * (n : ℂ) ^ (-(s + (i : ℂ)))) = Q.eval (n : ℂ) := by
    filter_upwards [eventually_ge_atTop (M + 1)] with n hn
    have hn1 : 1 ≤ n := by omega
    have hMn : M ≤ n := by omega
    have hMprev : M ≤ n - 1 := by omega
    have hrel_n := hrel n hMn
    have hrel_prev := hrel (n - 1) hMprev
    have hsub0 := congrArg₂ (fun a b : ℂ => a - b) hrel_n hrel_prev
    have hsub :
        (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * harmonicTail (N := N) s i n) -
          (∑ i : Fin (N + 1), (C (c i)).eval (-((n - 1 : ℕ) : ℂ)) *
            harmonicTail (N := N) s i (n - 1)) =
        P.eval (-(n : ℂ)) - P.eval (-((n - 1 : ℕ) : ℂ)) := by
      simpa using hsub0
    have hleft :
        (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * harmonicTail (N := N) s i n) -
          (∑ i : Fin (N + 1), (C (c i)).eval (-((n - 1 : ℕ) : ℂ)) *
            harmonicTail (N := N) s i (n - 1)) =
        ∑ i : Fin (N + 1), c i * (n : ℂ) ^ (-(s + (i : ℂ))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [eval_C]
      rw [← mul_sub, harmonicTail_sub_prev (N := N) s i hn1]
    have hright : P.eval (-(n : ℂ)) - P.eval (-((n - 1 : ℕ) : ℂ)) = Q.eval (n : ℂ) := by
      simp only [Q, eval_sub, eval_comp, eval_neg, eval_X, eval_one]
      have hprev : -((n - 1 : ℕ) : ℂ) = (1 : ℂ) - (n : ℂ) := by
        rw [Nat.cast_sub hn1]
        push_cast
        ring
      rw [hprev]
    rw [hleft, hright] at hsub
    exact hsub
  obtain ⟨hc, _hQ⟩ := HurwitzNonRat.const_coefficients_eq_zero_of_eventually_cpow_sum_eq_poly
    (N := N) (s := s) hsZ c Q hdiff
  refine ⟨hc, ?_⟩
  apply HurwitzDescent.eq_zero_of_eventually_neg_nat_roots (p := P) (N := M)
  intro n hn
  have hr := hrel n hn
  have hsum : (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * harmonicTail (N := N) s i n) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hc i]
    simp
  rw [hsum] at hr
  exact hr.symm

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

/-- Constant-coefficient harmonic-tail relations satisfy the pole-root identities automatically. -/
theorem harmonicPoleRootInput_constant_coeff_relation {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (c : Fin (N + 1) → ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) :
    ∀ (d n : ℕ),
      (∑ i : Fin (N + 1),
        (C (c i)).coeff d * Complex.Gamma (1 - s - (i : ℂ)) *
          (HurwitzPolylogPoleTower.twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (i : ℕ)) = 0 := by
  obtain ⟨hc, _hP⟩ := constant_coefficients_zero_of_harmonicTail_relation
    (N := N) (s := s) hsZ c P hrel
  intro d n
  simp [hc]

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

open HurwitzZetaShift

/-- Constant-coefficient relations among the actual shifted negative-integer Hurwitz values are
impossible for every finite ladder. -/
theorem constant_coefficients_zero_of_hzeta_shift_neg_nat_relation {N : ℕ} {s : ℂ}
    (hs1 : 1 < s.re) (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (c : Fin (N + 1) → ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * hzeta (s + (i : ℂ)) (-(n : ℂ)))
        = P.eval (-(n : ℂ))) :
    (∀ i : Fin (N + 1), c i = 0) ∧ P = 0 := by
  let Q : Polynomial ℂ := P.comp (-X) - P.comp (1 - X)
  let cη : Fin (N + 1) → ℂ := fun i =>
    c i * Complex.exp (-((Real.pi : ℂ) * Complex.I * (s + (i : ℂ))))
  have hdiff : ∀ᶠ n : ℕ in atTop,
      (∑ i : Fin (N + 1), cη i * (n : ℂ) ^ (-(s + (i : ℂ)))) = Q.eval (n : ℂ) := by
    filter_upwards [eventually_ge_atTop (M + 1)] with n hn
    have hn1 : 1 ≤ n := by omega
    have hMn : M ≤ n := by omega
    have hMprev : M ≤ n - 1 := by omega
    have hrel_n := hrel n hMn
    have hrel_prev := hrel (n - 1) hMprev
    have hsub0 := congrArg₂ (fun a b : ℂ => a - b) hrel_n hrel_prev
    have hsub :
        (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * hzeta (s + (i : ℂ)) (-(n : ℂ))) -
          (∑ i : Fin (N + 1), (C (c i)).eval (-((n - 1 : ℕ) : ℂ)) *
            hzeta (s + (i : ℂ)) (-((n - 1 : ℕ) : ℂ))) =
        P.eval (-(n : ℂ)) - P.eval (-((n - 1 : ℕ) : ℂ)) := by
      simpa using hsub0
    have hleft :
        (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * hzeta (s + (i : ℂ)) (-(n : ℂ))) -
          (∑ i : Fin (N + 1), (C (c i)).eval (-((n - 1 : ℕ) : ℂ)) *
            hzeta (s + (i : ℂ)) (-((n - 1 : ℕ) : ℂ))) =
        ∑ i : Fin (N + 1), cη i * (n : ℂ) ^ (-(s + (i : ℂ))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hsi1 : 1 < (s + (i : ℂ)).re := by
        rw [Complex.add_re, Complex.natCast_re]
        have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg i.val
        linarith
      simp only [eval_C, cη]
      rw [← mul_sub, hzeta_neg_nat_diff (s := s + (i : ℂ)) hsi1 hn1]
      ring
    have hright : P.eval (-(n : ℂ)) - P.eval (-((n - 1 : ℕ) : ℂ)) = Q.eval (n : ℂ) := by
      simp only [Q, eval_sub, eval_comp, eval_neg, eval_X, eval_one]
      have hprev : -((n - 1 : ℕ) : ℂ) = (1 : ℂ) - (n : ℂ) := by
        rw [Nat.cast_sub hn1]
        push_cast
        ring
      rw [hprev]
    rw [hleft, hright] at hsub
    exact hsub
  obtain ⟨hcη, _hQ⟩ := HurwitzNonRat.const_coefficients_eq_zero_of_eventually_cpow_sum_eq_poly
    (N := N) (s := s) hsZ cη Q hdiff
  have hc : ∀ i : Fin (N + 1), c i = 0 := by
    intro i
    have h := hcη i
    simp only [cη] at h
    exact (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _)
  refine ⟨hc, ?_⟩
  apply HurwitzDescent.eq_zero_of_eventually_neg_nat_roots (p := P) (N := M)
  intro n hn
  have hr := hrel n hn
  have hsum : (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * hzeta (s + (i : ℂ)) (-(n : ℂ))) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hc i]
    simp
  rw [hsum] at hr
  exact hr.symm

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

/-- Finite-difference transform for a polynomial-coefficient harmonic-tail relation. It is the exact
induction brick for the all-`N` tail provider: differencing lowers the polynomial coefficient side and
creates an explicit shifted-power term. -/
theorem harmonicTail_relation_finite_difference {N : ℕ} {s : ℂ}
    (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) :
    ∀ n, M + 1 ≤ n →
      (∑ i : Fin (N + 1),
        ((coeff i).comp (-X) - (coeff i).comp (1 - X)).eval (n : ℂ) *
          harmonicTail (N := N) s i n) +
      (∑ i : Fin (N + 1),
        ((coeff i).comp (1 - X)).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) =
      (P.comp (-X) - P.comp (1 - X)).eval (n : ℂ) := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hMn : M ≤ n := by omega
  have hMprev : M ≤ n - 1 := by omega
  have hrel_n := hrel n hMn
  have hrel_prev := hrel (n - 1) hMprev
  have hsub0 := congrArg₂ (fun a b : ℂ => a - b) hrel_n hrel_prev
  have hsub :
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * harmonicTail (N := N) s i n) -
        (∑ i : Fin (N + 1), (coeff i).eval (-((n - 1 : ℕ) : ℂ)) *
          harmonicTail (N := N) s i (n - 1)) =
      P.eval (-(n : ℂ)) - P.eval (-((n - 1 : ℕ) : ℂ)) := by
    simpa using hsub0
  have hleft :
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * harmonicTail (N := N) s i n) -
        (∑ i : Fin (N + 1), (coeff i).eval (-((n - 1 : ℕ) : ℂ)) *
          harmonicTail (N := N) s i (n - 1)) =
      (∑ i : Fin (N + 1),
        ((coeff i).comp (-X) - (coeff i).comp (1 - X)).eval (n : ℂ) *
          harmonicTail (N := N) s i n) +
      (∑ i : Fin (N + 1),
        ((coeff i).comp (1 - X)).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hprev : -((n - 1 : ℕ) : ℂ) = (1 : ℂ) - (n : ℂ) := by
      rw [Nat.cast_sub hn1]
      push_cast
      ring
    have hdiff := harmonicTail_sub_prev (N := N) s i hn1
    simp only [eval_sub, eval_comp, eval_neg, eval_X, eval_one]
    rw [hprev]
    rw [← hdiff]
    ring
  have hright : P.eval (-(n : ℂ)) - P.eval (-((n - 1 : ℕ) : ℂ)) =
      (P.comp (-X) - P.comp (1 - X)).eval (n : ℂ) := by
    simp only [eval_sub, eval_comp, eval_neg, eval_X, eval_one]
    have hprev : -((n - 1 : ℕ) : ℂ) = (1 : ℂ) - (n : ℂ) := by
      rw [Nat.cast_sub hn1]
      push_cast
      ring
    rw [hprev]
  rw [hleft, hright] at hsub
  exact hsub

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

open HurwitzZetaShift

/-- Finite-difference transform for a polynomial-coefficient relation among actual shifted
negative-integer Hurwitz values. -/
theorem hzeta_shift_neg_nat_relation_finite_difference {N : ℕ} {s : ℂ} (hs1 : 1 < s.re)
    (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * hzeta (s + (i : ℂ)) (-(n : ℂ)))
        = P.eval (-(n : ℂ))) :
    ∀ n, M + 1 ≤ n →
      (∑ i : Fin (N + 1),
        ((coeff i).comp (-X) - (coeff i).comp (1 - X)).eval (n : ℂ) *
          hzeta (s + (i : ℂ)) (-(n : ℂ))) +
      (∑ i : Fin (N + 1),
        ((coeff i).comp (1 - X)).eval (n : ℂ) *
          (Complex.exp (-((Real.pi : ℂ) * Complex.I * (s + (i : ℂ)))) *
            (n : ℂ) ^ (-(s + (i : ℂ))))) =
      (P.comp (-X) - P.comp (1 - X)).eval (n : ℂ) := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hMn : M ≤ n := by omega
  have hMprev : M ≤ n - 1 := by omega
  have hrel_n := hrel n hMn
  have hrel_prev := hrel (n - 1) hMprev
  have hsub0 := congrArg₂ (fun a b : ℂ => a - b) hrel_n hrel_prev
  have hsub :
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * hzeta (s + (i : ℂ)) (-(n : ℂ))) -
        (∑ i : Fin (N + 1), (coeff i).eval (-((n - 1 : ℕ) : ℂ)) *
          hzeta (s + (i : ℂ)) (-((n - 1 : ℕ) : ℂ))) =
      P.eval (-(n : ℂ)) - P.eval (-((n - 1 : ℕ) : ℂ)) := by
    simpa using hsub0
  have hleft :
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * hzeta (s + (i : ℂ)) (-(n : ℂ))) -
        (∑ i : Fin (N + 1), (coeff i).eval (-((n - 1 : ℕ) : ℂ)) *
          hzeta (s + (i : ℂ)) (-((n - 1 : ℕ) : ℂ))) =
      (∑ i : Fin (N + 1),
        ((coeff i).comp (-X) - (coeff i).comp (1 - X)).eval (n : ℂ) *
          hzeta (s + (i : ℂ)) (-(n : ℂ))) +
      (∑ i : Fin (N + 1),
        ((coeff i).comp (1 - X)).eval (n : ℂ) *
          (Complex.exp (-((Real.pi : ℂ) * Complex.I * (s + (i : ℂ)))) *
            (n : ℂ) ^ (-(s + (i : ℂ))))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hprev : -((n - 1 : ℕ) : ℂ) = (1 : ℂ) - (n : ℂ) := by
      rw [Nat.cast_sub hn1]
      push_cast
      ring
    have hsi1 : 1 < (s + (i : ℂ)).re := by
      rw [Complex.add_re, Complex.natCast_re]
      have hi : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg i.val
      linarith
    have hdiff := hzeta_neg_nat_diff (s := s + (i : ℂ)) hsi1 hn1
    simp only [eval_sub, eval_comp, eval_neg, eval_X, eval_one]
    have hcoefprev :
        (coeff i).eval (-((n - 1 : ℕ) : ℂ)) = (coeff i).eval ((1 : ℂ) - (n : ℂ)) := by
      rw [hprev]
    rw [← hcoefprev]
    rw [← hdiff]
    ring
  have hright : P.eval (-(n : ℂ)) - P.eval (-((n - 1 : ℕ) : ℂ)) =
      (P.comp (-X) - P.comp (1 - X)).eval (n : ℂ) := by
    simp only [eval_sub, eval_comp, eval_neg, eval_X, eval_one]
    have hprev : -((n - 1 : ℕ) : ℂ) = (1 : ℂ) - (n : ℂ) := by
      rw [Nat.cast_sub hn1]
      push_cast
      ring
    rw [hprev]
  rw [hleft, hright] at hsub
  exact hsub

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence

/-- A complex polynomial whose `-n` finite difference is zero is constant. -/
theorem polynomial_eq_C_of_comp_neg_eq_comp_oneSub {p : Polynomial ℂ}
    (h : p.comp (-X) = p.comp (1 - X)) : p = C (p.eval 0) := by
  have hshift : p = p.comp (X + 1) := by
    have hc := congrArg (fun q : Polynomial ℂ => q.comp (-X)) h
    change (p.comp (-X)).comp (-X) = (p.comp (1 - X)).comp (-X) at hc
    rw [Polynomial.comp_assoc, Polynomial.comp_assoc] at hc
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hc
  have hstep : ∀ z : ℂ, p.eval z = p.eval (z + 1) := by
    intro z
    have hz := congrArg (fun q : Polynomial ℂ => q.eval z) hshift
    simpa [eval_comp, add_comm] using hz
  have hnat : ∀ n : ℕ, p.eval (n : ℂ) = p.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hstep (n : ℂ)
        have hcast : (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) := by norm_num
        rw [hcast] at hs
        exact hs.symm.trans ih
  have hzero : p - C (p.eval 0) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hUniv : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
    have hinj : Set.InjOn (fun n : ℕ => (n : ℂ)) Set.univ := by
      intro a _ b _ hcast
      exact Nat.cast_injective hcast
    have himg : ((fun n : ℕ => (n : ℂ)) '' (Set.univ : Set ℕ)).Infinite :=
      hUniv.image hinj
    refine Set.Infinite.mono ?_ himg
    rintro x ⟨n, _hn, rfl⟩
    change (p - C (p.eval 0)).IsRoot (n : ℂ)
    rw [Polynomial.IsRoot.def, eval_sub, eval_C, hnat n, sub_self]
  exact sub_eq_zero.mp hzero

namespace HurwitzZetaTail

/-- If every polynomial coefficient has zero `-n` finite difference, the harmonic-tail relation closes
without the full all-`N` provider. -/
theorem coefficients_zero_of_harmonicTail_relation_of_zero_finite_difference {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hdiff0 : ∀ i : Fin (N + 1), (coeff i).comp (-X) - (coeff i).comp (1 - X) = 0)
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) :
    (∀ i : Fin (N + 1), coeff i = 0) ∧ P = 0 := by
  let c : Fin (N + 1) → ℂ := fun i => (coeff i).eval 0
  have hconst : ∀ i : Fin (N + 1), coeff i = C (c i) := by
    intro i
    exact polynomial_eq_C_of_comp_neg_eq_comp_oneSub (sub_eq_zero.mp (hdiff0 i))
  have hrelC : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ)) := by
    intro n hn
    simpa [hconst] using hrel n hn
  obtain ⟨hc, hP⟩ := constant_coefficients_zero_of_harmonicTail_relation
    (N := N) (s := s) hsZ c P hrelC
  refine ⟨?_, hP⟩
  intro i
  rw [hconst i, hc i, map_zero]

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

open HurwitzZetaShift

/-- If every polynomial coefficient has zero `-n` finite difference, the actual shifted-Hurwitz relation
closes without the full all-`N` provider. -/
theorem coefficients_zero_of_hzeta_shift_relation_of_zero_finite_difference {N : ℕ} {s : ℂ}
    (hs1 : 1 < s.re) (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hdiff0 : ∀ i : Fin (N + 1), (coeff i).comp (-X) - (coeff i).comp (1 - X) = 0)
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * hzeta (s + (i : ℂ)) (-(n : ℂ)))
        = P.eval (-(n : ℂ))) :
    (∀ i : Fin (N + 1), coeff i = 0) ∧ P = 0 := by
  let c : Fin (N + 1) → ℂ := fun i => (coeff i).eval 0
  have hconst : ∀ i : Fin (N + 1), coeff i = C (c i) := by
    intro i
    exact polynomial_eq_C_of_comp_neg_eq_comp_oneSub (sub_eq_zero.mp (hdiff0 i))
  have hrelC : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (C (c i)).eval (-(n : ℂ)) * hzeta (s + (i : ℂ)) (-(n : ℂ)))
        = P.eval (-(n : ℂ)) := by
    intro n hn
    simpa [hconst] using hrel n hn
  obtain ⟨hc, hP⟩ := constant_coefficients_zero_of_hzeta_shift_neg_nat_relation
    (N := N) (s := s) hs1 hsZ c P hrelC
  refine ⟨?_, hP⟩
  intro i
  rw [hconst i, hc i, map_zero]

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

/-- Mixed harmonic-tail/shifted-power independence with coefficients evaluated on the positive
natural parameter. This is the exact relation type produced by finite differencing a negative-argument
harmonic-tail relation. -/
def MixedTailIndependent (N : ℕ) (s : ℂ) : Prop :=
  ∀ (hcoeff scoeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (hcoeff i).eval (n : ℂ) * harmonicTail (N := N) s i n) +
        (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
          (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ)) →
    (∀ i : Fin (N + 1), hcoeff i = 0) ∧
      HurwitzNonRat.shiftedPowerPolynomial N scoeff = 0 ∧ P = 0

/-- The shifted-power part of the mixed target closes unconditionally. -/
theorem shiftedPower_relation_close_of_eventually_ge {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (scoeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
        (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ)) :
    HurwitzNonRat.shiftedPowerPolynomial N scoeff = 0 ∧ P = 0 := by
  have hev : ∀ᶠ n : ℕ in atTop,
      (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
        (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ) := by
    filter_upwards [eventually_ge_atTop M] with n hn
    exact hrel n hn
  exact HurwitzNonRat.shiftedPowerPolynomial_eq_zero_and_rhs_eq_zero_of_eventually_cpow_sum_eq_poly
    hsZ scoeff P hev

/-- Mixed relations with zero harmonic coefficients close by the shifted-power obstruction. -/
theorem mixedTailIndependent_zero_harmonic_part {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hcoeff scoeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hh : ∀ i : Fin (N + 1), hcoeff i = 0)
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (hcoeff i).eval (n : ℂ) * harmonicTail (N := N) s i n) +
        (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
          (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ)) :
    (∀ i : Fin (N + 1), hcoeff i = 0) ∧
      HurwitzNonRat.shiftedPowerPolynomial N scoeff = 0 ∧ P = 0 := by
  have hshift : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
        (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ) := by
    intro n hn
    have hr := hrel n hn
    have hsum :
        (∑ i : Fin (N + 1), (hcoeff i).eval (n : ℂ) * harmonicTail (N := N) s i n) = 0 := by
      simp [hh]
    simpa [hsum] using hr
  obtain ⟨hD, hP⟩ := shiftedPower_relation_close_of_eventually_ge hsZ scoeff P hshift
  exact ⟨hh, hD, hP⟩

/-- Singleton mixed relations with zero harmonic coefficients close in coefficient form: for `N = 0`,
the compressed shifted-power polynomial is just the unique shifted coefficient. -/
theorem mixedTailIndependent_zero_harmonic_part_N0_coefficients {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hcoeff scoeff : Fin (0 + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hh : ∀ i : Fin (0 + 1), hcoeff i = 0)
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (0 + 1), (hcoeff i).eval (n : ℂ) * harmonicTail (N := 0) s i n) +
        (∑ i : Fin (0 + 1), (scoeff i).eval (n : ℂ) *
          (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ)) :
    (∀ i : Fin (0 + 1), hcoeff i = 0) ∧
      (∀ i : Fin (0 + 1), scoeff i = 0) ∧ P = 0 := by
  obtain ⟨hhcoeff, hD, hP⟩ :=
    mixedTailIndependent_zero_harmonic_part (N := 0) (s := s)
      hsZ hcoeff scoeff P hh hrel
  have hscoeff0 : scoeff 0 = 0 := by
    simpa [HurwitzNonRat.shiftedPowerPolynomial] using hD
  refine ⟨hhcoeff, ?_, hP⟩
  intro i
  fin_cases i
  exact hscoeff0

/-- Mixed relations with zero shifted-power coefficients close from the harmonic-tail rational
independence provider.  This is the complementary easy branch to
`mixedTailIndependent_zero_harmonic_part`: after composing the coefficient polynomials with `-X`, the
positive-parameter mixed relation becomes exactly the negative-parameter harmonic-tail interface. -/
theorem mixedTailIndependent_zero_shifted_part_of_rationalTailIndependent {N : ℕ} {s : ℂ}
    (hTail : RationalTailIndependent (N := N) (harmonicTail (N := N) s))
    (hcoeff scoeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hs : ∀ i : Fin (N + 1), scoeff i = 0)
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (hcoeff i).eval (n : ℂ) * harmonicTail (N := N) s i n) +
        (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
          (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ)) :
    (∀ i : Fin (N + 1), hcoeff i = 0) ∧
      HurwitzNonRat.shiftedPowerPolynomial N scoeff = 0 ∧ P = 0 := by
  let coeffNeg : Fin (N + 1) → Polynomial ℂ := fun i => (hcoeff i).comp (-X)
  let PNeg : Polynomial ℂ := P.comp (-X)
  have hrelNeg : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeffNeg i).eval (-(n : ℂ)) *
        harmonicTail (N := N) s i n) = PNeg.eval (-(n : ℂ)) := by
    intro n hn
    have hr := hrel n hn
    have hshift :
        (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
          (n : ℂ) ^ (-(s + (i : ℂ)))) = 0 := by
      simp [hs]
    rw [hshift, add_zero] at hr
    simpa [coeffNeg, PNeg, eval_comp] using hr
  obtain ⟨hcoeffNeg, hPNeg⟩ := hTail coeffNeg PNeg hrelNeg
  have hh : ∀ i : Fin (N + 1), hcoeff i = 0 := by
    intro i
    by_contra hi
    exact (HurwitzN2Survivor.comp_neg_ne_zero hi) (hcoeffNeg i)
  have hD : HurwitzNonRat.shiftedPowerPolynomial N scoeff = 0 := by
    simp [HurwitzNonRat.shiftedPowerPolynomial, hs]
  have hP : P = 0 := by
    by_contra hP0
    exact (HurwitzN2Survivor.comp_neg_ne_zero hP0) hPNeg
  exact ⟨hh, hD, hP⟩

/-- Unconditional singleton mixed-tail close in the zero shifted-power subcase. -/
theorem mixedTailIndependent_zero_shifted_part_N0 {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hcoeff scoeff : Fin (0 + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hs : ∀ i : Fin (0 + 1), scoeff i = 0)
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (0 + 1), (hcoeff i).eval (n : ℂ) *
        harmonicTail (N := 0) s i n) +
        (∑ i : Fin (0 + 1), (scoeff i).eval (n : ℂ) *
          (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ)) :
    (∀ i : Fin (0 + 1), hcoeff i = 0) ∧
      HurwitzNonRat.shiftedPowerPolynomial 0 scoeff = 0 ∧ P = 0 := by
  exact mixedTailIndependent_zero_shifted_part_of_rationalTailIndependent
    (N := 0) (s := s) (rationalTailIndependent_harmonic_single (s := s) hsZ)
    hcoeff scoeff P hs hrel

/-- The existing finite-difference transform lands exactly in the mixed relation type. -/
theorem harmonicTail_relation_finite_difference_mixed {N : ℕ} {s : ℂ}
    (coeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (coeff i).eval (-(n : ℂ)) * harmonicTail (N := N) s i n)
        = P.eval (-(n : ℂ))) :
    ∀ n, M + 1 ≤ n →
      (∑ i : Fin (N + 1),
        ((coeff i).comp (-X) - (coeff i).comp (1 - X)).eval (n : ℂ) *
          harmonicTail (N := N) s i n) +
      (∑ i : Fin (N + 1),
        ((coeff i).comp (1 - X)).eval (n : ℂ) * (n : ℂ) ^ (-(s + (i : ℂ)))) =
      (P.comp (-X) - P.comp (1 - X)).eval (n : ℂ) := by
  exact harmonicTail_relation_finite_difference (N := N) (s := s) coeff P hrel

/-- A proof of the mixed target is enough to close the original harmonic-tail rational independence
provider. The finite-difference landing gives a mixed relation; mixed independence kills the coefficient
finite differences, and the already-proved zero-finite-difference close finishes the original relation. -/
theorem rationalTailIndependent_harmonic_of_mixedTailIndependent {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hMixed : MixedTailIndependent N s) :
    RationalTailIndependent (N := N) (harmonicTail (N := N) s) := by
  intro coeff P M hrel
  let hcoeff : Fin (N + 1) → Polynomial ℂ := fun i => (coeff i).comp (-X) - (coeff i).comp (1 - X)
  let scoeff : Fin (N + 1) → Polynomial ℂ := fun i => (coeff i).comp (1 - X)
  let Q : Polynomial ℂ := P.comp (-X) - P.comp (1 - X)
  have hmixRel : ∀ n, M + 1 ≤ n →
      (∑ i : Fin (N + 1), (hcoeff i).eval (n : ℂ) * harmonicTail (N := N) s i n) +
        (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
          (n : ℂ) ^ (-(s + (i : ℂ)))) = Q.eval (n : ℂ) := by
    intro n hn
    simpa [hcoeff, scoeff, Q] using
      harmonicTail_relation_finite_difference_mixed (N := N) (s := s) coeff P hrel n hn
  obtain ⟨hdiff, _hD, _hQ⟩ := hMixed hcoeff scoeff Q hmixRel
  have hdiff0 : ∀ i : Fin (N + 1), (coeff i).comp (-X) - (coeff i).comp (1 - X) = 0 := by
    intro i
    exact hdiff i
  exact coefficients_zero_of_harmonicTail_relation_of_zero_finite_difference
    (N := N) (s := s) hsZ coeff P hdiff0 hrel

/-- Mixed independence also supplies the pole-root bridge expected by the polylog endgame. -/
theorem harmonicPoleRootInput_of_mixedTailIndependent {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hMixed : MixedTailIndependent N s) :
    HarmonicPoleRootInput N s := by
  exact harmonicPoleRootInput_of_rationalTailIndependent
    (N := N) (s := s) (rationalTailIndependent_harmonic_of_mixedTailIndependent hsZ hMixed)

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

/-- Mixed pole-root bridge for the full finite-difference target: every eventual mixed relation gives
Gamma pole-root identities for the harmonic-tail coefficient polynomials. The shifted-power summands are
regular at the pole tower and therefore do not enter the highest-pole equations. -/
def MixedPoleRootInput (N : ℕ) (s : ℂ) : Prop :=
  ∀ (hcoeff scoeff : Fin (N + 1) → Polynomial ℂ) (P : Polynomial ℂ) {M : ℕ},
    (∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (hcoeff i).eval (n : ℂ) * harmonicTail (N := N) s i n) +
        (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
          (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ)) →
    ∀ (d n : ℕ),
      (∑ i : Fin (N + 1),
        (hcoeff i).coeff d * Complex.Gamma (1 - s - (i : ℂ)) *
          (HurwitzPolylogPoleTower.twoPiI * ((n + 1 : ℕ) : ℂ)) ^ (i : ℕ)) = 0

/-- The mixed pole-root bridge closes the full mixed harmonic-tail/shifted-power provider. -/
theorem mixedTailIndependent_of_mixedPoleRootInput {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : MixedPoleRootInput N s) :
    MixedTailIndependent N s := by
  intro hcoeff scoeff P M hrel
  have hhcoeff : ∀ i : Fin (N + 1), hcoeff i = 0 :=
    HurwitzPolylogPoleTower.polynomials_zero_of_gamma_pole_sum_roots hsZ
      (hpole hcoeff scoeff P hrel)
  have hshift : ∀ n, M ≤ n →
      (∑ i : Fin (N + 1), (scoeff i).eval (n : ℂ) *
        (n : ℂ) ^ (-(s + (i : ℂ)))) = P.eval (n : ℂ) := by
    intro n hn
    have hr := hrel n hn
    have hsum :
        (∑ i : Fin (N + 1), (hcoeff i).eval (n : ℂ) * harmonicTail (N := N) s i n) = 0 := by
      simp [hhcoeff]
    simpa [hsum] using hr
  obtain ⟨hD, hP⟩ := shiftedPower_relation_close_of_eventually_ge hsZ scoeff P hshift
  exact ⟨hhcoeff, hD, hP⟩

/-- Mixed independence makes the mixed pole-root bridge automatic. -/
theorem mixedPoleRootInput_of_mixedTailIndependent {N : ℕ} {s : ℂ}
    (hMixed : MixedTailIndependent N s) :
    MixedPoleRootInput N s := by
  intro hcoeff scoeff P M hrel d n
  have hhcoeff : ∀ i : Fin (N + 1), hcoeff i = 0 := (hMixed hcoeff scoeff P hrel).1
  simp [hhcoeff]

/-- For nonintegral `s`, the mixed pole-root bridge is equivalent to the full mixed-tail provider. -/
theorem mixedTailIndependent_iff_mixedPoleRootInput {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ)) :
    MixedTailIndependent N s ↔ MixedPoleRootInput N s := by
  constructor
  · exact mixedPoleRootInput_of_mixedTailIndependent
  · exact mixedTailIndependent_of_mixedPoleRootInput hsZ

/-- Mixed pole-root input closes the original harmonic-tail rational independence provider. -/
theorem rationalTailIndependent_harmonic_of_mixedPoleRootInput {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : MixedPoleRootInput N s) :
    RationalTailIndependent (N := N) (harmonicTail (N := N) s) := by
  exact rationalTailIndependent_harmonic_of_mixedTailIndependent hsZ
    (mixedTailIndependent_of_mixedPoleRootInput hsZ hpole)

end HurwitzZetaTail
end HurwitzAllNTailIndependence

namespace HurwitzAllNTailIndependence
namespace HurwitzZetaTail

open HurwitzZetaShift

/-- Mixed pole-root input also supplies the older harmonic pole-root bridge. -/
theorem harmonicPoleRootInput_of_mixedPoleRootInput {N : ℕ} {s : ℂ}
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : MixedPoleRootInput N s) :
    HarmonicPoleRootInput N s := by
  exact harmonicPoleRootInput_of_rationalTailIndependent
    (N := N) (s := s) (rationalTailIndependent_harmonic_of_mixedPoleRootInput hsZ hpole)

/-- Actual shifted-Hurwitz rational-tail independence from the sharper mixed pole-root bridge. -/
theorem rationalTailIndependent_hzeta_shift_neg_nat_of_mixedPoleRootInput {N : ℕ} {s : ℂ}
    (hs1 : 1 < s.re) (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : MixedPoleRootInput N s) :
    RationalTailIndependent (N := N)
      (fun i n => hzeta (s + (i : ℂ)) (-(n : ℂ))) := by
  exact rationalTailIndependent_hzeta_shift_neg_nat_of_harmonic hs1
    (rationalTailIndependent_harmonic_of_mixedPoleRootInput hsZ hpole)

/-- Actual shifted-Hurwitz row/constant close from the sharper mixed pole-root bridge. -/
theorem rows_and_constant_close_of_hzeta_shift_neg_nat_of_mixedPoleRootInput {N : ℕ} {s : ℂ}
    (hs1 : 1 < s.re) (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : MixedPoleRootInput N s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (hrow : ∀ j : Fin (N + 1), ∃ M : ℕ, ∀ n, M ≤ n →
      (l j).eval (-(n : ℂ)) +
        (∑ i : Fin (N + 1),
          (q i j).eval (-(n : ℂ)) *
            (2 * hzeta (s + (i : ℂ)) (-(n : ℂ)))) = 0)
    (hcc : ∃ M : ℕ, ∀ n, M ≤ n → cc.eval (-(n : ℂ)) = 0) :
    (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0 := by
  exact rows_and_constant_close_of_hzeta_shift_neg_nat_of_harmonic hs1
    (rationalTailIndependent_harmonic_of_mixedPoleRootInput hsZ hpole) q l cc hrow hcc

end HurwitzZetaTail
end HurwitzAllNTailIndependence
