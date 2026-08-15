import GaloisForLFunctions.RHTower.BarnesTailAsymptoticExpansion

/-!
# The Barnes remainder is an Euler jet of its own zeroth term

Each term removed from the Euler logarithmic derivative is a constant multiple of a power `x^{-p}`,
and the Euler operator multiplies such a term by `-p`.  That is exactly the weight `(-p)^m` carried
by the crossed residues, so the remainder at weight `m+1` is the Euler derivative of the remainder at
weight `m`, and the whole family is the Euler jet family of the single function

```text
R_s(x) = x W_s'(x)/W_s(x) − (π/s) csc(π/s) x^{1/s} − ∑_{j = −g}^{0} (−1)^j ζ(−sj) x^{−j} .
```
-/

open Complex Filter Set MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

variable {s : ℝ}

/-! ### Powers -/

theorem hasDerivAt_ofReal_cpow_all {x : ℝ} (hx : x ≠ 0) (r : ℂ) :
    HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ r) (r * ((x : ℝ) : ℂ) ^ (r - 1)) x := by
  rcases eq_or_ne r 0 with rfl | hr
  · simpa using (hasDerivAt_const x (1 : ℂ))
  · exact hasDerivAt_ofReal_cpow_const hx hr

theorem differentiableAt_const_mul_ofReal_cpow (c A : ℂ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : ℝ => c * ((y : ℝ) : ℂ) ^ A) x :=
  ((hasDerivAt_ofReal_cpow_all hx A).const_mul c).differentiableAt

/-- **The Euler operator multiplies a power by its exponent.** -/
theorem eulerDeriv_const_mul_ofReal_cpow (c A : ℂ) {x : ℝ} (hx : 0 < x) :
    eulerDeriv (fun y : ℝ => c * ((y : ℝ) : ℂ) ^ A) x = (A * c) * ((x : ℝ) : ℂ) ^ A := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hderiv := ((hasDerivAt_ofReal_cpow_all (ne_of_gt hx) A).const_mul c).deriv
  rw [eulerDeriv, hderiv]
  have hstep : ((x : ℝ) : ℂ) ^ (A - 1) * ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) ^ A := by
    conv_rhs => rw [show A = (A - 1) + 1 from by ring]
    rw [Complex.cpow_add _ _ hxne, Complex.cpow_one]
  calc ((x : ℝ) : ℂ) * (c * (A * ((x : ℝ) : ℂ) ^ (A - 1)))
      = (A * c) * (((x : ℝ) : ℂ) ^ (A - 1) * ((x : ℝ) : ℂ)) := by ring
    _ = (A * c) * ((x : ℝ) : ℂ) ^ A := by rw [hstep]

/-! ### The removed terms -/

theorem barnesIntResidue_eq_const_mul_cpow (s : ℝ) (m : ℕ) (j : ℤ) :
    (fun y : ℝ => barnesIntResidue s y m j)
      = fun y : ℝ =>
        ((-(j : ℂ)) ^ m * riemannZeta (-(s : ℂ) * (j : ℂ)) * (-(-1 : ℂ) ^ j))
          * ((y : ℝ) : ℂ) ^ (-(j : ℂ)) := by
  funext y
  rw [barnesIntResidue]
  ring

theorem eulerDeriv_barnesIntResidue (s : ℝ) (m : ℕ) (j : ℤ) {x : ℝ} (hx : 0 < x) :
    eulerDeriv (fun y : ℝ => barnesIntResidue s y m j) x = barnesIntResidue s x (m + 1) j := by
  rw [barnesIntResidue_eq_const_mul_cpow, eulerDeriv_const_mul_ofReal_cpow _ _ hx,
    barnesIntResidue]
  ring

theorem differentiableAt_barnesIntResidue (s : ℝ) (m : ℕ) (j : ℤ) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (fun y : ℝ => barnesIntResidue s y m j) x := by
  rw [barnesIntResidue_eq_const_mul_cpow]
  exact differentiableAt_const_mul_ofReal_cpow _ _ (ne_of_gt hx)

theorem barnesLeadingGenusResidue_eq_const_mul_cpow (s : ℝ) (m : ℕ) :
    (fun y : ℝ => barnesLeadingGenusResidue s y m)
      = fun y : ℝ =>
        ((1 / (s : ℂ)) ^ m * (-((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (-(1 / (s : ℂ))))))
            * (-(1 / (s : ℂ))))
          * ((y : ℝ) : ℂ) ^ (1 / (s : ℂ)) := by
  funext y
  rw [barnesLeadingGenusResidue]
  have h1 : (-(-(1 / ((s : ℝ) : ℂ)))) = 1 / ((s : ℝ) : ℂ) := by ring
  rw [h1]
  ring

theorem eulerDeriv_barnesLeadingGenusResidue (s : ℝ) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    eulerDeriv (fun y : ℝ => barnesLeadingGenusResidue s y m) x
      = barnesLeadingGenusResidue s x (m + 1) := by
  rw [barnesLeadingGenusResidue_eq_const_mul_cpow, eulerDeriv_const_mul_ofReal_cpow _ _ hx,
    barnesLeadingGenusResidue]
  have h1 : (-(-(1 / ((s : ℝ) : ℂ)))) = 1 / ((s : ℝ) : ℂ) := by ring
  rw [h1]
  ring

theorem differentiableAt_barnesLeadingGenusResidue (s : ℝ) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (fun y : ℝ => barnesLeadingGenusResidue s y m) x := by
  rw [barnesLeadingGenusResidue_eq_const_mul_cpow]
  exact differentiableAt_const_mul_ofReal_cpow _ _ (ne_of_gt hx)

/-! ### The Euler sum -/

theorem hasDerivAt_verticalIntegral'_barnesIntegrandPow {s σ : ℝ} (hs : 0 < s) (m : ℕ)
    (hζ : -(s : ℝ) * σ ≠ 1) (hsin : Real.sin (Real.pi * σ) ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y m) σ)
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
        (((x⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, barnesIntegrandPow s x (m + 1) ((σ : ℂ) + (t : ℂ) * I))) x := by
  have hbase := hasDerivAt_integral_barnesIntegrandPow hs m hζ hsin hx
  have hscaled := hbase.const_mul (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
  have hfun : (fun y : ℝ => (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
      * ∫ t : ℝ, barnesIntegrandPow s y m ((σ : ℂ) + (t : ℂ) * I))
      = fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y m) σ := by
    funext y
    rw [verticalIntegral'_eq_smul, Complex.real_smul]
  rwa [hfun] at hscaled

theorem differentiableAt_eulerIterate_powerCanonicalEulerSum (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (eulerDeriv^[m] (powerCanonicalEulerSum s)) x := by
  have hgl := powerGenus_lt hs hne
  have hgu := lt_powerGenus_add_one s
  have heqOn : Set.EqOn (eulerDeriv^[m] (powerCanonicalEulerSum s))
      (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y m)
        (genusAbscissa s (HTGeometry.powerGenus s) 0)) (Set.Ioi (0 : ℝ)) := by
    intro y hy
    have hcongr := eulerDeriv_iterate_congr isOpen_Ioi (powerCanonicalEulerSum_eqOn hs) m hy
    rw [hcongr]
    exact eulerIterate_barnesGenusEulerSum hs hgl hgu m hy
  have hev : (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y m)
      (genusAbscissa s (HTGeometry.powerGenus s) 0))
      =ᶠ[nhds x] eulerDeriv^[m] (powerCanonicalEulerSum s) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hx) fun y hy => (heqOn hy).symm
  have hder := hasDerivAt_verticalIntegral'_barnesIntegrandPow (s := s)
    (σ := genusAbscissa s (HTGeometry.powerGenus s) 0) hs m
    (genusStart_zeta hs hgl hgu) (sin_pi_genusAbscissa_zero_ne_zero hgl hgu) hx
  exact (hder.congr_of_eventuallyEq hev.symm).differentiableAt

/-! ### The step -/

theorem differentiableAt_barnesEulerRemainder (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (barnesEulerRemainder s m) x := by
  have h1 := differentiableAt_eulerIterate_powerCanonicalEulerSum hs hne m hx
  have h2 := differentiableAt_barnesLeadingGenusResidue s m hx
  have h3 : DifferentiableAt ℝ (fun y : ℝ => ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
      barnesIntResidue s y m ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))) x :=
    DifferentiableAt.fun_sum fun k _ => differentiableAt_barnesIntResidue s m _ hx
  exact ((h1.add h2).add h3)

/-- **The Barnes remainder at weight `m+1` is the Euler derivative of the one at weight `m`.** -/
theorem barnesEulerRemainder_succ (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    barnesEulerRemainder s (m + 1) x = eulerDeriv (barnesEulerRemainder s m) x := by
  have h1 := differentiableAt_eulerIterate_powerCanonicalEulerSum hs hne m hx
  have h2 := differentiableAt_barnesLeadingGenusResidue s m hx
  have h3 : DifferentiableAt ℝ (fun y : ℝ => ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
      barnesIntResidue s y m ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))) x :=
    DifferentiableAt.fun_sum fun k _ => differentiableAt_barnesIntResidue s m _ hx
  have hsplit : eulerDeriv (barnesEulerRemainder s m) x
      = eulerDeriv (eulerDeriv^[m] (powerCanonicalEulerSum s)) x
        + eulerDeriv (fun y : ℝ => barnesLeadingGenusResidue s y m) x
        + eulerDeriv (fun y : ℝ => ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
            barnesIntResidue s y m ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))) x := by
    have hfun : barnesEulerRemainder s m
        = fun y : ℝ => (eulerDeriv^[m] (powerCanonicalEulerSum s) y
            + barnesLeadingGenusResidue s y m)
          + ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
              barnesIntResidue s y m ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) := rfl
    rw [eulerDeriv, eulerDeriv, eulerDeriv, eulerDeriv, hfun,
      deriv_fun_add (h1.fun_add h2) h3, deriv_fun_add h1 h2]
    ring
  have hsum : eulerDeriv (fun y : ℝ => ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
      barnesIntResidue s y m ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))) x
      = ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
          barnesIntResidue s x (m + 1) ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) := by
    rw [eulerDeriv, deriv_fun_sum fun k _ => differentiableAt_barnesIntResidue s m _ hx,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := eulerDeriv_barnesIntResidue s m ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) hx
    rwa [eulerDeriv] at h
  have hit : eulerDeriv (eulerDeriv^[m] (powerCanonicalEulerSum s))
      = eulerDeriv^[m + 1] (powerCanonicalEulerSum s) :=
    (Function.iterate_succ_apply' eulerDeriv m (powerCanonicalEulerSum s)).symm
  rw [hsplit, hsum, eulerDeriv_barnesLeadingGenusResidue s m hx]
  rw [show eulerDeriv (eulerDeriv^[m] (powerCanonicalEulerSum s)) x
      = eulerDeriv^[m + 1] (powerCanonicalEulerSum s) x from congrFun hit x]
  rw [barnesEulerRemainder]

/-- **The Barnes remainders are the Euler jets of the remainder itself.** -/
theorem barnesEulerRemainder_eq_iterate (hs : 0 < s)
    (hne : ((HTGeometry.powerGenus s : ℕ) : ℝ) ≠ 1 / s) :
    ∀ (m : ℕ) {x : ℝ}, 0 < x →
      barnesEulerRemainder s m x = eulerDeriv^[m] (barnesEulerRemainder s 0) x
  | 0, x, _ => rfl
  | (m + 1), x, hx => by
    have hIH : Set.EqOn (barnesEulerRemainder s m)
        (eulerDeriv^[m] (barnesEulerRemainder s 0)) (Set.Ioi (0 : ℝ)) :=
      fun y hy => barnesEulerRemainder_eq_iterate hs hne m hy
    have hev : eulerDeriv^[m] (barnesEulerRemainder s 0) =ᶠ[nhds x] barnesEulerRemainder s m :=
      Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hx) fun y hy => (hIH hy).symm
    rw [Function.iterate_succ_apply', eulerDeriv, hev.deriv_eq,
      barnesEulerRemainder_succ hs hne m hx, eulerDeriv]

end

end RHTower
