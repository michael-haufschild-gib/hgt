import GaloisForLFunctions.RHTower.XiGaussianHeatHankelIndex
import GaloisForLFunctions.HTGeometry.SymmetricPolynomialJets

/-!
# Root-flip symmetry of the heat Hankel form and real roots of simple ground states

For a polynomial `P` let `P^*` be the polynomial with conjugated coefficients, so that
`P^*(z) = \overline{P(\bar z)}`.  The heat Hankel form only sees the Hermitian square `P · P^*`:

`H_a(P, P) = Σ_q e^{-a w_q} (P · P^*)(w_q)` (`heatHankelTermAt_eq_eval_mul_conjPoly`).

If `r` is a root of `P`, the root flip `P̃ = (P / (X − r)) · (X − r̄)` has the same Hermitian square
(`rootFlip_mul_conjPoly`), so

**Theorem** (`heatHankel_rootFlip`).  `H_a(P̃, P̃) = H_a(P, P)` for every heat time `a` and every
root `r`, unconditionally.

A flip at a non-real root strictly raises the multiplicity at `r̄`, so a flip-closed family whose
members are all proportional to one polynomial forces that polynomial to have only real roots
(`im_eq_zero_of_rootFlip_unique`).  Applied to the Rayleigh quotient of `H_a` against any reference
functional of the Hermitian square (for instance `∫ |P|² dμ` for a positive measure `μ` on `ℝ`):

**Theorem** (`im_eq_zero_of_heatHankel_simple_minimizer`).  A minimiser of
`Re H_a(P, P) / g(P)` over nonzero polynomials of degree `< N` that is unique up to scalars has only
real roots.
-/

open Complex Polynomial
open GaloisForLFunctions.HTGeometry (conjPoly eval_conjPoly)

namespace RHTower

noncomputable section

/-! ## Conjugate polynomial and the Hermitian square -/

theorem conjPoly_mul (P R : ℂ[X]) : conjPoly (P * R) = conjPoly P * conjPoly R :=
  Polynomial.map_mul _

theorem conjPoly_X_sub_C (r : ℂ) : conjPoly (X - C r) = X - C ((starRingEnd ℂ) r) := by
  simp [conjPoly]

/-- The heat Hankel term only depends on the Hermitian square `P · P^*`. -/
theorem heatHankelTermAt_eq_eval_mul_conjPoly (a : ℝ) (P : ℂ[X]) (w : ℂ) :
    heatHankelTermAt a P P w = Complex.exp (-(a : ℂ) * w) * (P * conjPoly P).eval w := by
  rw [heatHankelTermAt, eval_mul, eval_conjPoly]
  ring

theorem heatHankel_eq_of_mul_conjPoly_eq {P R : ℂ[X]} (h : P * conjPoly P = R * conjPoly R)
    (a : ℝ) : heatHankel a P P = heatHankel a R R := by
  unfold heatHankel
  congr 1
  funext q
  rw [heatHankelTermAt_eq_eval_mul_conjPoly, heatHankelTermAt_eq_eval_mul_conjPoly, h]

/-! ## The root flip -/

/-- The root flip `(P / (X − r)) · (X − r̄)`. -/
def rootFlip (P : ℂ[X]) (r : ℂ) : ℂ[X] := (P /ₘ (X - C r)) * (X - C ((starRingEnd ℂ) r))

theorem eq_mul_divByMonic_of_isRoot {P : ℂ[X]} {r : ℂ} (hr : P.IsRoot r) :
    P = (P /ₘ (X - C r)) * (X - C r) := by
  rw [mul_comm]
  exact (mul_divByMonic_eq_iff_isRoot.2 hr).symm

/-- **The flip preserves the Hermitian square.** -/
theorem rootFlip_mul_conjPoly {P : ℂ[X]} {r : ℂ} (hr : P.IsRoot r) :
    rootFlip P r * conjPoly (rootFlip P r) = P * conjPoly P := by
  have hP := eq_mul_divByMonic_of_isRoot hr
  set Q := P /ₘ (X - C r)
  rw [rootFlip, conjPoly_mul, conjPoly_X_sub_C, Complex.conj_conj]
  conv_rhs => rw [hP, conjPoly_mul, conjPoly_X_sub_C]
  ring

/-- **Root-flip symmetry of the heat Hankel form.** -/
theorem heatHankel_rootFlip {P : ℂ[X]} {r : ℂ} (hr : P.IsRoot r) (a : ℝ) :
    heatHankel a (rootFlip P r) (rootFlip P r) = heatHankel a P P :=
  heatHankel_eq_of_mul_conjPoly_eq (rootFlip_mul_conjPoly hr) a

theorem divByMonic_ne_zero_of_isRoot {P : ℂ[X]} {r : ℂ} (hP : P ≠ 0) (hr : P.IsRoot r) :
    P /ₘ (X - C r) ≠ 0 := by
  intro h0
  apply hP
  rw [eq_mul_divByMonic_of_isRoot hr, h0, zero_mul]

theorem rootFlip_ne_zero {P : ℂ[X]} {r : ℂ} (hP : P ≠ 0) (hr : P.IsRoot r) : rootFlip P r ≠ 0 :=
  mul_ne_zero (divByMonic_ne_zero_of_isRoot hP hr) (X_sub_C_ne_zero _)

theorem natDegree_rootFlip {P : ℂ[X]} {r : ℂ} (hP : P ≠ 0) (hr : P.IsRoot r) :
    (rootFlip P r).natDegree = P.natDegree := by
  have hQ := divByMonic_ne_zero_of_isRoot hP hr
  have hP' := eq_mul_divByMonic_of_isRoot hr
  rw [rootFlip, natDegree_mul hQ (X_sub_C_ne_zero _), natDegree_X_sub_C]
  conv_rhs => rw [hP', natDegree_mul hQ (X_sub_C_ne_zero _), natDegree_X_sub_C]

/-- A flip at a non-real root raises the multiplicity at the conjugate root by one. -/
theorem rootMultiplicity_conj_rootFlip {P : ℂ[X]} {r : ℂ} (hP : P ≠ 0) (hr : P.IsRoot r)
    (him : r.im ≠ 0) :
    rootMultiplicity ((starRingEnd ℂ) r) (rootFlip P r) =
      rootMultiplicity ((starRingEnd ℂ) r) P + 1 := by
  classical
  have hQ := divByMonic_ne_zero_of_isRoot hP hr
  have hne : (starRingEnd ℂ) r ≠ r := fun h => him (Complex.conj_eq_iff_im.1 h)
  have hP' := eq_mul_divByMonic_of_isRoot hr
  rw [rootFlip, rootMultiplicity_mul (mul_ne_zero hQ (X_sub_C_ne_zero _)),
    rootMultiplicity_X_sub_C, if_pos rfl]
  conv_rhs => rw [hP', rootMultiplicity_mul (mul_ne_zero hQ (X_sub_C_ne_zero _)),
    rootMultiplicity_X_sub_C, if_neg hne]

/-- **Real roots from flip-uniqueness.**  If a flip-closed family of nonzero polynomials consists of
scalar multiples of `P₀ ∈ S`, then every root of `P₀` is real. -/
theorem im_eq_zero_of_rootFlip_unique {P₀ : ℂ[X]} (S : ℂ[X] → Prop) (hS₀ : S P₀)
    (hne : ∀ P, S P → P ≠ 0)
    (hflip : ∀ P r, S P → P.IsRoot r → S (rootFlip P r))
    (huniq : ∀ P, S P → ∃ c : ℂ, P = C c * P₀) {r : ℂ} (hr : P₀.IsRoot r) : r.im = 0 := by
  by_contra him
  have hP₀ := hne P₀ hS₀
  obtain ⟨c, hc⟩ := huniq _ (hflip P₀ r hS₀ hr)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact rootFlip_ne_zero hP₀ hr (by rw [hc, C_0, zero_mul])
  have h1 := rootMultiplicity_conj_rootFlip hP₀ hr him
  rw [hc, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.2 hc0) hP₀), rootMultiplicity_C,
    zero_add] at h1
  omega

/-! ## Simple heat Hankel ground states -/

/-- **Simple ground states have real roots.**  Let `g` be a functional of the Hermitian square (e.g.
`∫ |P|² dμ` for a positive measure `μ` on `ℝ`).  If every nonzero polynomial of degree `< N` with the
same Rayleigh value `Re H_a(P, P) / g(P)` as `P₀` is a scalar multiple of `P₀` (for instance `P₀` a
minimiser that is unique up to scalars), then every root of `P₀` is real. -/
theorem im_eq_zero_of_heatHankel_simple_minimizer {a : ℝ} {N : ℕ} (g : ℂ[X] → ℝ)
    (hg : ∀ P R : ℂ[X], P * conjPoly P = R * conjPoly R → g P = g R)
    {P₀ : ℂ[X]} (hP₀ : P₀ ≠ 0) (hdeg : P₀.natDegree < N)
    (huniq : ∀ P : ℂ[X], P ≠ 0 → P.natDegree < N →
      (heatHankel a P P).re * g P₀ = (heatHankel a P₀ P₀).re * g P → ∃ c : ℂ, P = C c * P₀)
    {r : ℂ} (hr : P₀.IsRoot r) : r.im = 0 := by
  refine im_eq_zero_of_rootFlip_unique
    (fun P => P ≠ 0 ∧ P.natDegree < N ∧
      (heatHankel a P P).re * g P₀ = (heatHankel a P₀ P₀).re * g P)
    ⟨hP₀, hdeg, rfl⟩ (fun P hP => hP.1) (fun P s hP hs => ?_)
    (fun P hP => huniq P hP.1 hP.2.1 hP.2.2) hr
  refine ⟨rootFlip_ne_zero hP.1 hs, (natDegree_rootFlip hP.1 hs).symm ▸ hP.2.1, ?_⟩
  rw [heatHankel_rootFlip hs, hg _ _ (rootFlip_mul_conjPoly hs)]
  exact hP.2.2

end

end RHTower
