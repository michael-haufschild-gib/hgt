import GaloisForLFunctions.HTGeometry.BohrTrigPolynomial

/-!
# The mixed means of a function against a trigonometric polynomial

Two computations, both instances of orthonormality of the characters for the Bohr mean: the mean of
`f · conj p` is the pairing of the coefficients of `p` with the Bohr coefficients of `f`, and the
mean of `|p|²` is the sum of the squared moduli of the coefficients.

Indexing the polynomial by a `Finset` of frequencies makes the frequencies distinct by construction,
so no injectivity hypothesis is needed.
-/

open MeasureTheory ComplexConjugate

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- The trigonometric polynomial with coefficient function `a` on a finite frequency set. -/
def trigPoly (S : Finset ℝ) (a : ℝ → ℂ) (t : ℝ) : ℂ := ∑ lam ∈ S, a lam * bohrExp lam t

theorem continuous_trigPoly (S : Finset ℝ) (a : ℝ → ℂ) : Continuous (trigPoly S a) :=
  continuous_finsetSum _ fun lam _ => continuous_const.mul (continuous_bohrExp lam)

theorem isBohrAlmostPeriodic_trigPoly (S : Finset ℝ) (a : ℝ → ℂ) :
    IsBohrAlmostPeriodic (trigPoly S a) :=
  isBohrAlmostPeriodic_sum _ (fun lam _ => continuous_const.mul (continuous_bohrExp lam))
    (fun lam _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_bohrExp lam))

/-- **The mean of a function against a trigonometric polynomial** pairs the coefficients with the
Bohr coefficients. -/
theorem bohrMean_mul_conj_trigPoly {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : IsBohrAlmostPeriodic f) (S : Finset ℝ) (a : ℝ → ℂ) :
    bohrMean (fun t => f t * conj (trigPoly S a t))
      = ∑ lam ∈ S, conj (a lam) * bohrCoefficient f lam := by
  classical
  have hsplit : (fun t : ℝ => f t * conj (trigPoly S a t))
      = fun t : ℝ => ∑ lam ∈ S, conj (a lam) * (f t * bohrChar lam t) := by
    funext t
    rw [trigPoly, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [map_mul, conj_bohrExp]
    ring
  rw [hsplit, bohrMean_sum (F := fun lam => fun t : ℝ => conj (a lam) * (f t * bohrChar lam t)) S
    (fun lam _ => continuous_const.mul (hfc.mul (continuous_bohrChar lam)))
    (fun lam _ => isBohrAlmostPeriodic_const_mul _
      (isBohrAlmostPeriodic_mul_bohrChar hfc hfa lam))]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [bohrMean_const_mul (f := fun t : ℝ => f t * bohrChar lam t) _
    (hfc.mul (continuous_bohrChar lam)) (isBohrAlmostPeriodic_mul_bohrChar hfc hfa lam)]
  rfl

/-- **The mean square of a trigonometric polynomial** is the sum of the squared moduli of its
coefficients. -/
theorem bohrMean_trigPoly_mul_conj_self (S : Finset ℝ) (a : ℝ → ℂ) :
    bohrMean (fun t => trigPoly S a t * conj (trigPoly S a t))
      = ∑ lam ∈ S, a lam * conj (a lam) := by
  classical
  have hsplit : (fun t : ℝ => trigPoly S a t * conj (trigPoly S a t))
      = fun t : ℝ => ∑ p ∈ S ×ˢ S, (a p.1 * conj (a p.2)) * bohrChar (p.2 - p.1) t := by
    funext t
    rw [trigPoly, map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, conj_bohrExp]
    rw [show a p.1 * bohrExp p.1 t * (conj (a p.2) * bohrChar p.2 t)
        = a p.1 * conj (a p.2) * (bohrExp p.1 t * bohrChar p.2 t) by ring,
      bohrExp_mul_bohrChar]
  rw [hsplit, bohrMean_sum (F := fun p : ℝ × ℝ => fun t : ℝ =>
      (a p.1 * conj (a p.2)) * bohrChar (p.2 - p.1) t) (S ×ˢ S)
    (fun p _ => continuous_const.mul (continuous_bohrChar _))
    (fun p _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_bohrChar _))]
  have hterm : ∀ p ∈ S ×ˢ S,
      bohrMean (fun t : ℝ => (a p.1 * conj (a p.2)) * bohrChar (p.2 - p.1) t)
        = if p.1 = p.2 then a p.1 * conj (a p.2) else 0 := by
    intro p _
    rw [bohrMean_const_mul (f := bohrChar (p.2 - p.1)) _ (continuous_bohrChar _)
      (isBohrAlmostPeriodic_bohrChar _), bohrMean_bohrChar]
    by_cases h : p.1 = p.2
    · rw [if_pos (by rw [h]; ring), if_pos h, mul_one]
    · rw [if_neg (fun hz => h (by linarith [sub_eq_zero.mp hz])), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_product]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  rw [Finset.sum_ite_eq S lam (fun mu => a lam * conj (a mu)), if_pos hlam]

/-- **The mean square of the approximation error**, expanded in the coefficients. -/
theorem bohrMean_sub_trigPoly_mul_conj {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : IsBohrAlmostPeriodic f) (S : Finset ℝ) (a : ℝ → ℂ) :
    bohrMean (fun t => (f t - trigPoly S a t) * conj (f t - trigPoly S a t))
      = bohrMean (fun t => f t * conj (f t))
        - ∑ lam ∈ S, (conj (a lam) * bohrCoefficient f lam
            + a lam * conj (bohrCoefficient f lam) - a lam * conj (a lam)) := by
  classical
  set p : ℝ → ℂ := trigPoly S a with hp
  have hpc : Continuous p := continuous_trigPoly S a
  have hpa : IsBohrAlmostPeriodic p := isBohrAlmostPeriodic_trigPoly S a
  have hcfc : Continuous fun t : ℝ => conj (f t) := Complex.continuous_conj.comp hfc
  have hcfa : IsBohrAlmostPeriodic fun t : ℝ => conj (f t) := isBohrAlmostPeriodic_conj hfa
  have hcpc : Continuous fun t : ℝ => conj (p t) := Complex.continuous_conj.comp hpc
  have hcpa : IsBohrAlmostPeriodic fun t : ℝ => conj (p t) := isBohrAlmostPeriodic_conj hpa
  -- the four mixed terms
  have hff : Continuous fun t : ℝ => f t * conj (f t) := hfc.mul hcfc
  have hffa : IsBohrAlmostPeriodic fun t : ℝ => f t * conj (f t) :=
    isBohrAlmostPeriodic_mul hfc hfa hcfc hcfa
  have hfp : Continuous fun t : ℝ => f t * conj (p t) := hfc.mul hcpc
  have hfpa : IsBohrAlmostPeriodic fun t : ℝ => f t * conj (p t) :=
    isBohrAlmostPeriodic_mul hfc hfa hcpc hcpa
  have hpf : Continuous fun t : ℝ => p t * conj (f t) := hpc.mul hcfc
  have hpfa : IsBohrAlmostPeriodic fun t : ℝ => p t * conj (f t) :=
    isBohrAlmostPeriodic_mul hpc hpa hcfc hcfa
  have hpp : Continuous fun t : ℝ => p t * conj (p t) := hpc.mul hcpc
  have hppa : IsBohrAlmostPeriodic fun t : ℝ => p t * conj (p t) :=
    isBohrAlmostPeriodic_mul hpc hpa hcpc hcpa
  have hexpand : (fun t : ℝ => (f t - p t) * conj (f t - p t))
      = fun t : ℝ => (f t * conj (f t) - f t * conj (p t))
        - (p t * conj (f t) - p t * conj (p t)) := by
    funext t
    rw [map_sub]
    ring
  rw [hexpand,
    bohrMean_sub (f := fun t : ℝ => f t * conj (f t) - f t * conj (p t))
      (g := fun t : ℝ => p t * conj (f t) - p t * conj (p t))
      (hff.sub hfp) (isBohrAlmostPeriodic_sub hff hffa hfp hfpa)
      (hpf.sub hpp) (isBohrAlmostPeriodic_sub hpf hpfa hpp hppa),
    bohrMean_sub (f := fun t : ℝ => f t * conj (f t)) (g := fun t : ℝ => f t * conj (p t))
      hff hffa hfp hfpa,
    bohrMean_sub (f := fun t : ℝ => p t * conj (f t)) (g := fun t : ℝ => p t * conj (p t))
      hpf hpfa hpp hppa]
  -- the three computed means
  have h1 : bohrMean (fun t : ℝ => f t * conj (p t))
      = ∑ lam ∈ S, conj (a lam) * bohrCoefficient f lam :=
    bohrMean_mul_conj_trigPoly hfc hfa S a
  have h2 : bohrMean (fun t : ℝ => p t * conj (f t))
      = ∑ lam ∈ S, a lam * conj (bohrCoefficient f lam) := by
    have hconjfun : (fun t : ℝ => conj (f t * conj (p t))) = fun t : ℝ => p t * conj (f t) := by
      funext t
      rw [map_mul, Complex.conj_conj]
      ring
    have := bohrMean_conj hfp hfpa
    rw [hconjfun] at this
    rw [this, h1, map_sum]
    exact Finset.sum_congr rfl fun lam _ => by rw [map_mul, Complex.conj_conj]
  have h3 : bohrMean (fun t : ℝ => p t * conj (p t)) = ∑ lam ∈ S, a lam * conj (a lam) :=
    bohrMean_trigPoly_mul_conj_self S a
  rw [h1, h2, h3]
  have hsum : ∑ lam ∈ S, (conj (a lam) * bohrCoefficient f lam
      + a lam * conj (bohrCoefficient f lam) - a lam * conj (a lam))
      = (∑ lam ∈ S, conj (a lam) * bohrCoefficient f lam)
        + (∑ lam ∈ S, a lam * conj (bohrCoefficient f lam))
        - ∑ lam ∈ S, a lam * conj (a lam) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [hsum]
  abel

end

end GaloisForLFunctions
