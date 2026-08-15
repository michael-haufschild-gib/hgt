import GaloisForLFunctions.RHTower.BarnesEulerRemainderStep
import GaloisForLFunctions.HTGeometry.PowerCanonicalProductRightHalfPlane

/-!
# The Barnes remainder as an analytic function on the right half-plane

The zeros of `W_s` are negative reals and the branch of `z^{1/s}` is analytic off the negative axis,
so the whole Barnes decomposition

```text
R_s(z) = z W_s'(z)/W_s(z) − (π/s) csc(π/s) z^{1/s} − ∑_{j = −g}^{0} (−1)^j ζ(−sj) z^{−j}
```

is analytic on the right half-plane and restricts on the positive axis to the remainder whose Euler
jets carry the formal Barnes tail.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

variable {s : ℝ}

/-- The Barnes term at an integer, as a function on the plane. -/
def barnesTermC (s : ℝ) (j : ℤ) (z : ℂ) : ℂ :=
  ((-1 : ℂ) ^ j) * riemannZeta (-(s : ℂ) * (j : ℂ)) * z ^ (-(j : ℂ))

/-- The leading term of the Barnes expansion, as a function on the plane. -/
def barnesLeadingTermC (s : ℝ) (z : ℂ) : ℂ :=
  ((Real.pi : ℂ) / (s : ℂ)) / Complex.sin ((Real.pi : ℂ) / (s : ℂ)) * z ^ (1 / (s : ℂ))

/-- The Barnes remainder of a power canonical product, as a function on the plane. -/
def barnesRemainderC (s : ℝ) (z : ℂ) : ℂ :=
  z * logDeriv (HTGeometry.powerCanonicalProduct s) z
    - barnesLeadingTermC s z
    - ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
        barnesTermC s ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) z

theorem barnesTermC_ofReal (s : ℝ) (j : ℤ) (x : ℝ) :
    barnesTermC s j ((x : ℝ) : ℂ) = barnesTerm s x j := by
  rw [barnesTermC, barnesTerm]

theorem barnesLeadingTermC_ofReal (s : ℝ) (x : ℝ) :
    barnesLeadingTermC s ((x : ℝ) : ℂ) = barnesLeadingTerm s x := by
  rw [barnesLeadingTermC, barnesLeadingTerm]

/-- **On the positive axis the complex remainder is the remainder of the expansion.** -/
theorem barnesRemainderC_ofReal (hs : 0 < s) (x : ℝ) :
    barnesRemainderC s ((x : ℝ) : ℂ) = barnesEulerRemainder s 0 x := by
  have hlead : barnesLeadingGenusResidue s x 0 = -barnesLeadingTerm s x := by
    rw [← neg_barnesLeadingGenusResidue_eq hs x]
    ring
  have hsum : ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
        barnesIntResidue s x 0 ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))
      = -∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
          barnesTerm s x ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← neg_barnesIntResidue_eq s x ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)), neg_neg]
  have hEuler : (eulerDeriv^[0] (powerCanonicalEulerSum s)) x
      = ((x : ℝ) : ℂ) * logDeriv (HTGeometry.powerCanonicalProduct s) ((x : ℝ) : ℂ) := rfl
  rw [barnesRemainderC, barnesEulerRemainder, hEuler, hlead, hsum, barnesLeadingTermC_ofReal]
  have hterms : ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
      barnesTermC s ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) ((x : ℝ) : ℂ)
      = ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
          barnesTerm s x ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) :=
    Finset.sum_congr rfl fun k _ => barnesTermC_ofReal s _ x
  rw [hterms]
  ring

/-! ### Analyticity -/

theorem analyticOnNhd_cpow_const_rightHalfPlane (c : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => z ^ c) HTGeometry.rightHalfPlane := by
  refine DifferentiableOn.analyticOnNhd ?_ HTGeometry.isOpen_rightHalfPlane
  intro z hz
  have hslit : z ∈ Complex.slitPlane := HTGeometry.rightHalfPlane_subset_slitPlane hz
  exact ((Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt.differentiableAt).differentiableWithinAt

theorem analyticOnNhd_barnesTermC (s : ℝ) (j : ℤ) :
    AnalyticOnNhd ℂ (barnesTermC s j) HTGeometry.rightHalfPlane := by
  have hc : AnalyticOnNhd ℂ (fun _ : ℂ => ((-1 : ℂ) ^ j) * riemannZeta (-(s : ℂ) * (j : ℂ)))
      HTGeometry.rightHalfPlane := fun z _ => analyticAt_const
  exact hc.mul (analyticOnNhd_cpow_const_rightHalfPlane (-(j : ℂ)))

theorem analyticOnNhd_barnesLeadingTermC (s : ℝ) :
    AnalyticOnNhd ℂ (barnesLeadingTermC s) HTGeometry.rightHalfPlane := by
  have hc : AnalyticOnNhd ℂ
      (fun _ : ℂ => ((Real.pi : ℂ) / (s : ℂ)) / Complex.sin ((Real.pi : ℂ) / (s : ℂ)))
      HTGeometry.rightHalfPlane := fun z _ => analyticAt_const
  exact hc.mul (analyticOnNhd_cpow_const_rightHalfPlane (1 / (s : ℂ)))

theorem analyticOnNhd_powerCanonicalProduct_rightHalfPlane (hs : 0 < s) :
    AnalyticOnNhd ℂ (HTGeometry.powerCanonicalProduct s) HTGeometry.rightHalfPlane :=
  (HTGeometry.analyticOnNhd_powerCanonicalProduct hs).mono (Set.subset_univ _)

theorem analyticOnNhd_eulerLogDeriv_powerCanonicalProduct (hs : 0 < s) :
    AnalyticOnNhd ℂ (fun z : ℂ => z * logDeriv (HTGeometry.powerCanonicalProduct s) z)
      HTGeometry.rightHalfPlane := by
  have hW := analyticOnNhd_powerCanonicalProduct_rightHalfPlane hs
  have hne : ∀ z ∈ HTGeometry.rightHalfPlane, HTGeometry.powerCanonicalProduct s z ≠ 0 :=
    fun z hz => HTGeometry.powerCanonicalProduct_ne_zero_of_re_pos hs hz
  have hid : AnalyticOnNhd ℂ (fun z : ℂ => z) HTGeometry.rightHalfPlane := fun z _ => analyticAt_id
  exact hid.mul (hW.deriv.div hW hne)

/-- **The Barnes remainder is analytic on the right half-plane.** -/
theorem analyticOnNhd_barnesRemainderC (hs : 0 < s) :
    AnalyticOnNhd ℂ (barnesRemainderC s) HTGeometry.rightHalfPlane := by
  have h1 := analyticOnNhd_eulerLogDeriv_powerCanonicalProduct hs
  have h2 := analyticOnNhd_barnesLeadingTermC s
  have h3 : AnalyticOnNhd ℂ (fun z : ℂ => ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
      barnesTermC s ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) z)
      HTGeometry.rightHalfPlane :=
    Finset.analyticOnNhd_fun_sum _ fun k _ => analyticOnNhd_barnesTermC s _
  exact (h1.sub h2).sub h3

end

end RHTower
