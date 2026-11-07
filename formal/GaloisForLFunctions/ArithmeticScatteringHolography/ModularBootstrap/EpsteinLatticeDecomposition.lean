import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.ScalarChargeCoordinates

/-!
# Full and half-plane Epstein sums at arbitrary moduli

Positive gcd separates the full lattice sum into a zeta factor and the
primitive Eisenstein series. Central reflection pairs the two half-planes;
the remaining axis is an explicit zeta term.
-/

open Complex RHTower RHTower.HeckeFactorization

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

noncomputable section

/-- The normalized Epstein weight, before removal of the origin. -/
def epsteinWeight (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (p : ℤ × ℤ) : ℂ :=
  (z.y : ℂ) ^ s * (d4BMPoincareQuadratic z p : ℂ) ^ (-s)

def epsteinTerm (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : {p : ℤ × ℤ // p ≠ (0, 0)}) : ℂ := epsteinWeight z s p.val

/-- Positive first coordinates represent one half of the non-axis lattice. -/
def halfEpsteinTerm (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (t : ℕ × ℤ) : ℂ :=
  epsteinWeight z s ((t.1 : ℤ) + 1, t.2)

theorem epsteinWeight_primitive (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (a : D4BMPrimitiveIntegerPair) :
    epsteinWeight z s a.pair = d4BMPoincareSeed z s a := by
  have hq := d4BMPoincareQuadratic_pos z a.pair a.pair_ne_zero
  rw [d4BMPoincareSeed]
  change _ = ((z.y / d4BMPoincareQuadratic z a.pair : ℝ) : ℂ) ^ s
  exact (Sieve.ofReal_div_cpow_eq_mul_cpow_neg z.y_pos hq s).symm

theorem epsteinWeight_eq_div_cpow (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : ℤ × ℤ) (hp : p ≠ (0, 0)) :
    epsteinWeight z s p = ((d4BMPoincareQuadratic z p / z.y : ℝ) : ℂ) ^ (-s) := by
  rw [Sieve.ofReal_div_cpow_eq_mul_cpow_neg
    (d4BMPoincareQuadratic_pos z p hp) z.y_pos, neg_neg]
  exact mul_comm _ _

/-- Absolute convergence follows from the positive-definite quadratic bound. -/
theorem summable_epsteinTerm (z : D4BMUpperHalfPlaneCoordinate) {s : ℂ}
    (hs : 1 < s.re) : Summable (epsteinTerm z s) := by
  have h : Summable (fun p : {p : ℤ × ℤ // p ≠ (0, 0)} =>
      (d4BMPoincareQuadratic z p.val : ℂ) ^ (-s)) := by
    refine Summable.of_norm_bounded (summable_d4BMPoincareQuadratic_cpow_norm z ⟨s, hs⟩)
      fun p => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (d4BMPoincareQuadratic_pos z p.val p.property)]
    simp
  exact h.mul_left ((z.y : ℂ) ^ s)

theorem summable_halfEpsteinTerm (z : D4BMUpperHalfPlaneCoordinate) {s : ℂ}
    (hs : 1 < s.re) : Summable (halfEpsteinTerm z s) := by
  let f : ℕ × ℤ → {p : ℤ × ℤ // p ≠ (0, 0)} := fun t =>
    ⟨((t.1 : ℤ) + 1, t.2), by intro h; have := congrArg Prod.fst h; dsimp at this; omega⟩
  exact (summable_epsteinTerm z hs).comp_injective (i := f) (by
    intro a b h
    have h₁ := congrArg (fun p => p.val.1) h
    have h₂ := congrArg (fun p => p.val.2) h
    exact Prod.ext (by dsimp [f] at h₁; omega) h₂)

private theorem quadratic_gcd (z : D4BMUpperHalfPlaneCoordinate) (k : ℕ)
    (a : D4BMPrimitiveIntegerPair) :
    d4BMPoincareQuadratic z (gcdEquiv (k, a)).val =
      (((k + 1) ^ 2 : ℕ) : ℝ) * d4BMPoincareQuadratic z a.pair := by
  change (((((k : ℤ) + 1) * a.pair.1 : ℤ) : ℝ) * z.y) ^ 2 +
    (((((k : ℤ) + 1) * a.pair.1 : ℤ) : ℝ) * z.x +
      ((((k : ℤ) + 1) * a.pair.2 : ℤ) : ℝ)) ^ 2 = _
  simp only [d4BMPoincareQuadratic]
  push_cast
  ring

private theorem epsteinTerm_gcd (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (k : ℕ) (a : D4BMPrimitiveIntegerPair) :
    epsteinTerm z s (gcdEquiv (k, a)) =
      (1 / ((k : ℂ) + 1) ^ (2 * s)) * d4BMPoincareSeed z s a := by
  rw [epsteinTerm, epsteinWeight, quadratic_gcd, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity)
      (d4BMPoincareQuadratic_pos z a.pair a.pair_ne_zero).le]
  simp only [ofReal_natCast]
  rw [natCast_sq_cpow_neg, ← epsteinWeight_primitive]
  dsimp only [epsteinWeight]
  ring

/-- Positive-gcd decomposition gives the exact primitive-series normalization. -/
theorem epstein_eq_zeta_primitive (z : D4BMUpperHalfPlaneCoordinate) {s : ℂ}
    (hs : 1 < s.re) :
    (∑' p, epsteinTerm z s p) =
      riemannZeta (2 * s) * ∑' a, d4BMPoincareSeed z s a := by
  have hsum : Summable (epsteinTerm z s ∘ gcdEquiv) :=
    gcdEquiv.summable_iff.mpr (summable_epsteinTerm z hs)
  calc
    _ = ∑' t, (epsteinTerm z s ∘ gcdEquiv) t := (gcdEquiv.tsum_eq _).symm
    _ = ∑' k, ∑' a, epsteinTerm z s (gcdEquiv (k, a)) := hsum.tsum_prod
    _ = _ := by
      simp_rw [epsteinTerm_gcd, tsum_mul_left]
      rw [tsum_mul_right, ← zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith only [hs])]

theorem epstein_eq_eisenstein (z : D4BMUpperHalfPlaneCoordinate) {s : ℂ}
    (hs : 1 < s.re) :
    (∑' p, epsteinTerm z s p) =
      2 * riemannZeta (2 * s) * d4BMRawEisensteinPoincareSeries z ⟨s, hs⟩ := by
  rw [epstein_eq_zeta_primitive z hs, d4BMRawEisensteinPoincareSeries]
  ring

private def puncturedEpstein (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) : ℤ × ℤ → ℂ :=
  {p | p ≠ (0, 0)}.indicator (epsteinWeight z s)

private theorem summable_puncturedEpstein (z : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) : Summable (puncturedEpstein z s) :=
  summable_subtype_iff_indicator.mp (summable_epsteinTerm z hs)

private theorem puncturedEpstein_neg (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (c d : ℤ) : puncturedEpstein z s (-c, d) = puncturedEpstein z s (c, -d) := by
  have hq : d4BMPoincareQuadratic z (-c, d) = d4BMPoincareQuadratic z (c, -d) := by
    dsimp only [d4BMPoincareQuadratic]
    push_cast
    ring
  simp only [puncturedEpstein, Set.indicator_apply, Set.mem_setOf_eq,
    ne_eq, Prod.mk.injEq, neg_eq_zero, epsteinWeight, hq]

private theorem puncturedEpstein_pos (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (k : ℕ) (d : ℤ) :
    puncturedEpstein z s ((k : ℤ) + 1, d) = halfEpsteinTerm z s (k, d) := by
  have h : ((k : ℤ) + 1, d) ≠ (0, 0) := by
    intro h; have := congrArg Prod.fst h; dsimp at this; omega
  simp only [puncturedEpstein, Set.indicator_apply, Set.mem_setOf_eq, if_pos h, halfEpsteinTerm]

private theorem puncturedEpstein_axis_pos (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (k : ℕ) : puncturedEpstein z s (0, (k : ℤ) + 1) =
      (z.y : ℂ) ^ s * (1 / ((k : ℂ) + 1) ^ (2 * s)) := by
  have h : ((0 : ℤ), (k : ℤ) + 1) ≠ (0, 0) := by
    intro h; have := congrArg Prod.snd h; dsimp at this; omega
  have hq : d4BMPoincareQuadratic z (0, (k : ℤ) + 1) = (((k + 1) ^ 2 : ℕ) : ℝ) := by
    simp only [d4BMPoincareQuadratic]
    push_cast
    ring
  simp only [puncturedEpstein, Set.indicator_apply, Set.mem_setOf_eq, if_pos h,
    epsteinWeight, hq, ofReal_natCast, natCast_sq_cpow_neg]

/-- The omitted zero-first-coordinate axis contributes `2 y^s ζ(2s)`. -/
theorem epstein_halfPlane_split (z : D4BMUpperHalfPlaneCoordinate) {s : ℂ}
    (hs : 1 < s.re) :
    (∑' p, epsteinTerm z s p) = 2 * (∑' t, halfEpsteinTerm z s t) +
      2 * (z.y : ℂ) ^ s * riemannZeta (2 * s) := by
  have h := summable_puncturedEpstein z hs
  have ha : Summable (fun d : ℤ => puncturedEpstein z s (0, d)) := h.prod_factor 0
  have hap : Summable (fun k : ℕ => puncturedEpstein z s (0, (k : ℤ) + 1)) :=
    ha.comp_injective (fun a b h => by omega)
  have han : Summable (fun k : ℕ => puncturedEpstein z s (0, -((k : ℤ) + 1))) :=
    ha.comp_injective (fun a b h => by omega)
  have haxis : (∑' d : ℤ, puncturedEpstein z s (0, d)) =
      2 * (z.y : ℂ) ^ s * riemannZeta (2 * s) := by
    rw [tsum_of_add_one_of_neg_add_one (f := fun d : ℤ => puncturedEpstein z s (0, d)) hap han]
    have hneg (d : ℤ) : puncturedEpstein z s (0, -d) = puncturedEpstein z s (0, d) := by
      simpa only [neg_zero] using (puncturedEpstein_neg z s 0 d).symm
    simp only [hneg, puncturedEpstein_axis_pos, tsum_mul_left]
    rw [← zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith only [hs])]
    simp [puncturedEpstein]
    ring
  have hr : Summable (fun c : ℤ => ∑' d : ℤ, puncturedEpstein z s (c, d)) := h.prod
  have hp : Summable (fun k : ℕ => ∑' d : ℤ, puncturedEpstein z s ((k : ℤ) + 1, d)) :=
    hr.comp_injective (fun a b h => by omega)
  have hn : Summable (fun k : ℕ => ∑' d : ℤ, puncturedEpstein z s (-((k : ℤ) + 1), d)) :=
    hr.comp_injective (fun a b h => by omega)
  have hrow (c : ℤ) : (∑' d : ℤ, puncturedEpstein z s (-c, d)) =
      ∑' d : ℤ, puncturedEpstein z s (c, d) := by
    simp only [puncturedEpstein_neg]
    exact (Equiv.neg ℤ).tsum_eq (fun d => puncturedEpstein z s (c, d))
  have ht : (∑' p, epsteinTerm z s p) = ∑' p, puncturedEpstein z s p :=
    tsum_subtype {p : ℤ × ℤ | p ≠ (0, 0)} (epsteinWeight z s)
  rw [ht, h.tsum_prod, tsum_of_add_one_of_neg_add_one
    (f := fun c : ℤ => ∑' d : ℤ, puncturedEpstein z s (c, d)) hp hn]
  simp only [hrow, puncturedEpstein_pos]
  rw [haxis, ← (summable_halfEpsteinTerm z hs).tsum_prod]
  ring

/-- The half-plane sum is the Eisenstein series with its leading cusp term removed. -/
theorem halfEpstein_eq_eisenstein_sub (z : D4BMUpperHalfPlaneCoordinate) {s : ℂ}
    (hs : 1 < s.re) :
    (∑' t, halfEpsteinTerm z s t) = riemannZeta (2 * s) *
      (d4BMRawEisensteinPoincareSeries z ⟨s, hs⟩ - (z.y : ℂ) ^ s) := by
  have h₁ := epstein_halfPlane_split z hs
  have h₂ := epstein_eq_eisenstein z hs
  linear_combination (h₂ - h₁) / 2

end

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.epstein_eq_eisenstein
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.halfEpstein_eq_eisenstein_sub
