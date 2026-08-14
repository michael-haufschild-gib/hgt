import GaloisForLFunctions.HTGeometry.PowerCanonicalProductLogDeriv
import GaloisForLFunctions.HTGeometry.ZetaMomentFunctionalEquation
import GaloisForLFunctions.RHTower.BarnesMellinGenusEulerDerivative

/-!
# The Barnes expansion of a power canonical product

Let `s > 0` with `1/s` not an integer, let `g = ⌊1/s⌋` and let

```text
W_s(z) = ∏_{n ≥ 1} E_g(-z/n^s) ,   H_s(x) = x W_s'(x)/W_s(x) .
```

The Mellin representation of `H_s` on the strip `-(g+1) < Re w < -g` and the rightward contour
shift give, for every truncation `K`,

```text
H_s(x) = (π/s) csc(π/s) x^{1/s}
       + ∑_{j = -g}^{K-1-g} (-1)^j ζ(-sj) x^{-j}
       + O(x^{-(K-1-g+1/2)}) .
```

The terms with `j < 0` are the ascending powers `(-1)^j ζ(s|j|) x^{|j|}`, the term `j = 0` is the
constant `ζ(0) = -1/2`, and the terms with `j > 0` are the descending Barnes tail with coefficients
`b_j = (-1)^j ζ(-sj)`.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {s : ℝ}

/-! ### The terms of the expansion in their classical shape -/

/-- The leading term `(π/s) csc(π/s) x^{1/s}` of the Barnes expansion. -/
def barnesLeadingTerm (s x : ℝ) : ℂ :=
  ((Real.pi : ℂ) / (s : ℂ)) / Complex.sin ((Real.pi : ℂ) / (s : ℂ))
    * ((x : ℝ) : ℂ) ^ (1 / (s : ℂ))

/-- The term of the Barnes expansion at the integer `j`: `(-1)^j ζ(-sj) x^{-j}`. -/
def barnesTerm (s x : ℝ) (j : ℤ) : ℂ :=
  ((-1 : ℂ) ^ j) * riemannZeta (-(s : ℂ) * (j : ℂ)) * ((x : ℝ) : ℂ) ^ (-(j : ℂ))

/-- The crossed zeta residue is the negative of the leading term. -/
theorem neg_barnesLeadingGenusResidue_eq (hs : 0 < s) (x : ℝ) :
    -barnesLeadingGenusResidue s x 0 = barnesLeadingTerm s x := by
  have hsne : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hsin : Complex.sin ((Real.pi : ℂ) * (-(1 / (s : ℂ))))
      = -Complex.sin ((Real.pi : ℂ) / (s : ℂ)) := by
    rw [show (Real.pi : ℂ) * (-(1 / (s : ℂ))) = -((Real.pi : ℂ) / (s : ℂ)) by ring,
      Complex.sin_neg]
  rw [barnesLeadingGenusResidue, barnesLeadingTerm, pow_zero, one_mul, hsin, neg_neg]
  rcases eq_or_ne (Complex.sin ((Real.pi : ℂ) / (s : ℂ))) 0 with h0 | h0
  · rw [h0]
    simp
  · field_simp

/-- The crossed kernel residue at an integer is the negative of the corresponding Barnes term. -/
theorem neg_barnesIntResidue_eq (s x : ℝ) (j : ℤ) :
    -barnesIntResidue s x 0 j = barnesTerm s x j := by
  rw [barnesIntResidue, barnesTerm, pow_zero, one_mul]
  ring

/-- **The descending part of the expansion carries the moment-Borel coefficients.**  At a
nonnegative index the Barnes term is `b_k x^{-k}` with `b_k = (-1)^k ζ(-sk)`, the coefficient the
moment-Borel transform is built from. -/
theorem barnesTerm_natCast (s x : ℝ) (k : ℕ) :
    barnesTerm s x (k : ℤ) = zetaMomentCoeff (s : ℂ) k * ((x : ℝ) : ℂ) ^ (-(k : ℂ)) := by
  rw [barnesTerm, zetaMomentCoeff, zpow_natCast, neg_mul]
  norm_cast

/-! ### The genus of a power canonical product -/

theorem powerGenus_lt (hs : 0 < s) (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) :
    ((HTGeometry.powerGenus s : ℕ) : ℝ) < 1 / s := by
  have hpos : (0 : ℝ) ≤ 1 / s := le_of_lt (div_pos one_pos hs)
  exact lt_of_le_of_ne (Nat.floor_le hpos) hne

theorem lt_powerGenus_add_one (s : ℝ) :
    1 / s < ((HTGeometry.powerGenus s : ℕ) : ℝ) + 1 :=
  Nat.lt_floor_add_one (1 / s)

/-! ### The expansion -/

/-- **The Barnes expansion of the logarithmic derivative of a power canonical product.**  For
`s > 0` with `1/s` not an integer and every truncation `K`, the Euler logarithmic derivative of
`W_s` differs from the leading term `(π/s) csc(π/s) x^{1/s}` plus the `K` terms
`(-1)^j ζ(-sj) x^{-j}`, `j = -g, …, K-1-g`, by `O(x^{-σ_{K+1}})`, where
`σ_{K+1} = K - 1 - g + 1/2` grows without bound. -/
theorem barnes_expansion_powerCanonicalProduct (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖((x : ℝ) : ℂ) * logDeriv (HTGeometry.powerCanonicalProduct s) ((x : ℝ) : ℂ)
          - barnesLeadingTerm s x
          - ∑ k ∈ Finset.range K,
              barnesTerm s x ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))‖
        ≤ C * x ^ (-(genusAbscissa s (HTGeometry.powerGenus s) (K + 1))) := by
  have hgl := powerGenus_lt hs hne
  have hgu := lt_powerGenus_add_one s
  obtain ⟨C, hC0, hC⟩ :=
    barnes_genus_poincare_expansion (s := s) (g := HTGeometry.powerGenus s) hs hgl hgu K
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hlead : barnesLeadingGenusResidue s x 0 = -barnesLeadingTerm s x := by
    rw [← neg_barnesLeadingGenusResidue_eq hs x]
    ring
  have hsumres : ∑ k ∈ Finset.range K,
        barnesIntResidue s x 0 ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))
      = -∑ k ∈ Finset.range K,
          barnesTerm s x ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← neg_barnesIntResidue_eq s x ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)), neg_neg]
  have heq : (∑' n : ℕ, ((-1) ^ (HTGeometry.powerGenus s) : ℂ)
          * barnesModel (HTGeometry.powerGenus s) (x / ((n : ℝ) + 1) ^ s))
        + barnesLeadingGenusResidue s x 0
        + ∑ k ∈ Finset.range K,
            barnesIntResidue s x 0 ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))
      = ((x : ℝ) : ℂ) * logDeriv (HTGeometry.powerCanonicalProduct s) ((x : ℝ) : ℂ)
        - barnesLeadingTerm s x
        - ∑ k ∈ Finset.range K,
            barnesTerm s x ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) := by
    rw [HTGeometry.ofReal_mul_logDeriv_powerCanonicalProduct hs hx, hlead, hsumres]
    ring
  rw [← heq]
  exact hC x hx

/-- The Euler logarithmic derivative of the canonical product, as a function on the positive
axis. -/
def powerCanonicalEulerSum (s : ℝ) : ℝ → ℂ :=
  fun x => ((x : ℝ) : ℂ) * logDeriv (HTGeometry.powerCanonicalProduct s) ((x : ℝ) : ℂ)

/-- On the positive axis the Euler logarithmic derivative is the genus Euler sum. -/
theorem powerCanonicalEulerSum_eqOn (hs : 0 < s) :
    Set.EqOn (powerCanonicalEulerSum s) (barnesGenusEulerSum s (HTGeometry.powerGenus s))
      (Set.Ioi (0 : ℝ)) := fun _ hx =>
  HTGeometry.ofReal_mul_logDeriv_powerCanonicalProduct hs hx

/-- **The Barnes expansion of a power canonical product is termwise differentiable.**  Every Euler
derivative `D^m` of `x W_s'(x)/W_s(x)` has the expansion obtained by weighting the `j`-th term of
the expansion of `x W_s'(x)/W_s(x)` by `j^m`, with the same uniform error order. -/
theorem barnes_expansion_powerCanonicalProduct_euler (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) (m K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(eulerDeriv^[m] (powerCanonicalEulerSum s)) x
          + barnesLeadingGenusResidue s x m
          + ∑ k ∈ Finset.range K,
              barnesIntResidue s x m ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))‖
        ≤ C * x ^ (-(genusAbscissa s (HTGeometry.powerGenus s) (K + 1))) := by
  have hgl := powerGenus_lt hs hne
  have hgu := lt_powerGenus_add_one s
  obtain ⟨C, hC0, hC⟩ :=
    barnes_genus_poincare_expansion_euler (s := s) (g := HTGeometry.powerGenus s) hs hgl hgu m K
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hxmem : x ∈ Set.Ioi (0 : ℝ) := hx
  have hcongr := eulerDeriv_iterate_congr isOpen_Ioi (powerCanonicalEulerSum_eqOn hs) m hxmem
  rw [hcongr]
  exact hC x hx

end

end RHTower
