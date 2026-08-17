import GaloisForLFunctions.HTGeometry.HermitianSOSExtremal

/-!
# A nonnegative real polynomial in one variable is a sum of two squares

The classical univariate Positivstellensatz, by induction on the degree.  A nonconstant nonnegative
polynomial has an irreducible factor of degree one or two.  A linear factor forces a double root —
a zero of a nonnegative function is a minimum, so the derivative vanishes there — and a quadratic
irreducible factor is already a sum of two squares, `(X + b/2)² + (c - b²/4)`, whose constant term is
positive because the factor has no real root.  In both cases the cofactor is nonnegative of smaller
degree, and `(u² + v²)(a² + b²) = (ua + vb)² + (ub - va)²` closes the induction.

The half-line form is the one used downstream: `p ≥ 0` on `[0, ∞)` gives `p(y²) = A(y)² + B(y)²`,
which turns a nonnegative signomial with commensurable exponents into a sum of squares of signomials.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

private theorem sq_add_sq_mul (u v a b : ℝ[X]) :
    (u ^ 2 + v ^ 2) * (a ^ 2 + b ^ 2) = (u * a + v * b) ^ 2 + (u * b - v * a) ^ 2 := by ring

private theorem monic_quadratic_sq_add_sq {h : ℝ[X]} (hmonic : h.Monic) (hdeg : h.natDegree = 2)
    (hroot : ∀ r : ℝ, h.eval r ≠ 0) :
    ∃ u v : ℝ[X], h = u ^ 2 + v ^ 2 ∧ ∀ x : ℝ, 0 < h.eval x := by
  set b : ℝ := h.coeff 1 with hb
  set c : ℝ := h.coeff 0 with hc
  have h2 : h.coeff 2 = 1 := by
    have := hmonic.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  have hform : ∀ x : ℝ, h.eval x = x ^ 2 + b * x + c := by
    intro x
    rw [eval_eq_sum_range, hdeg, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, h2, ← hb, ← hc]
    ring
  set d : ℝ := c - b ^ 2 / 4 with hd
  have hval : ∀ x : ℝ, h.eval x = (x + b / 2) ^ 2 + d := by
    intro x; rw [hform, hd]; ring
  have hdpos : 0 < d := by
    rcases lt_trichotomy d 0 with hneg | hzero | hpos
    · exact absurd (by
        rw [hval, show (-(b / 2) + Real.sqrt (-d) + b / 2) = Real.sqrt (-d) from by ring,
          Real.sq_sqrt (by linarith)]
        ring) (hroot (-(b / 2) + Real.sqrt (-d)))
    · exact absurd (by rw [hval, ← hzero]; ring) (hroot (-(b / 2)))
    · exact hpos
  refine ⟨X + C (b / 2), C (Real.sqrt d), ?_, fun x => ?_⟩
  · refine Polynomial.funext (fun r => ?_)
    simp only [eval_add, eval_pow, eval_X, eval_C]
    rw [hval r, Real.sq_sqrt hdpos.le]
  · rw [hval x]; positivity

private theorem cofactor_nonneg {p q g : ℝ[X]} (hpg : p = q * g)
    (hqpos : ∀ x : ℝ, 0 < q.eval x) (hnn : ∀ x : ℝ, 0 ≤ p.eval x) (x : ℝ) : 0 ≤ g.eval x := by
  have := hnn x
  rw [hpg, eval_mul] at this
  nlinarith [hqpos x]

/-- **The univariate Positivstellensatz.**  A real polynomial nonnegative on the whole line is a sum
of two squares. -/
theorem exists_sq_add_sq_of_nonneg :
    ∀ (n : ℕ) (p : ℝ[X]), p.natDegree ≤ n → (∀ x : ℝ, 0 ≤ p.eval x) →
      ∃ a b : ℝ[X], p = a ^ 2 + b ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hdeg hnn
    by_cases hp0 : p = 0
    · exact ⟨0, 0, by rw [hp0]; ring⟩
    by_cases hdeg0 : p.natDegree = 0
    · obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨p.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hdeg0⟩
      have hcnn : 0 ≤ c := by simpa using hnn 0
      exact ⟨C (Real.sqrt c), 0, by rw [← C_pow, Real.sq_sqrt hcnn]; ring⟩
    have hnu : ¬ IsUnit p := by
      intro hu
      obtain ⟨r, _, hr⟩ := Polynomial.isUnit_iff.mp hu
      exact hdeg0 (by rw [← hr]; simp)
    obtain ⟨f, hfirr, hfdvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hp0
    have hf0 : f ≠ 0 := hfirr.ne_zero
    have hlc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf0
    have hfle : f.natDegree ≤ 2 := hfirr.natDegree_le_two
    have hfne : f.natDegree ≠ 0 := by
      intro hcon
      refine hfirr.not_isUnit (Polynomial.isUnit_iff.mpr ⟨f.coeff 0, ?_, ?_⟩)
      · refine isUnit_iff_ne_zero.mpr (fun hz => hf0 ?_)
        rw [Polynomial.eq_C_of_natDegree_eq_zero hcon, hz, map_zero]
      · exact (Polynomial.eq_C_of_natDegree_eq_zero hcon).symm
    have hcase : f.natDegree = 1 ∨ f.natDegree = 2 := by omega
    rcases hcase with hfd | hfd
    · -- a linear factor gives a double root
      set r : ℝ := -(f.coeff 0) / f.coeff 1 with hr
      have hc1 : f.coeff 1 ≠ 0 := by rwa [Polynomial.leadingCoeff, hfd] at hlc
      have hfr : f.eval r = 0 := by
        rw [eval_eq_sum_range, hfd, Finset.sum_range_succ, Finset.sum_range_one, hr]
        field_simp
        ring
      obtain ⟨k, hk⟩ := hfdvd
      have hpr : p.eval r = 0 := by rw [hk, eval_mul, hfr, zero_mul]
      have hmin : IsLocalMin (fun x => p.eval x) r :=
        Filter.Eventually.of_forall (fun x => by
          show p.eval r ≤ p.eval x
          rw [hpr]
          exact hnn x)
      have hder : p.derivative.eval r = 0 := by
        have := hmin.deriv_eq_zero
        rwa [Polynomial.deriv] at this
      obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hpr
      have hqr : q.eval r = 0 := by
        have hd2 : p.derivative = q + (X - C r) * q.derivative := by
          rw [hq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
        rw [hd2, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
          add_zero] at hder
        exact hder
      obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hqr
      have hpg : p = (X - C r) ^ 2 * g := by rw [hq, hg]; ring
      have hgnn : ∀ x : ℝ, 0 ≤ g.eval x := by
        intro x
        by_contra hcon
        push Not at hcon
        have hcont : ContinuousAt (fun y => g.eval y) x := (Polynomial.continuous g).continuousAt
        have hev : ∀ᶠ y in nhds x, g.eval y < 0 := hcont.eventually (eventually_lt_nhds hcon)
        obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
        set y : ℝ := if x = r then x + ε / 2 else x with hy
        have hyclose : dist y x < ε := by
          rw [hy]
          by_cases hxr : x = r
          · rw [if_pos hxr, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
            linarith
          · rw [if_neg hxr, Real.dist_eq, sub_self, abs_zero]
            exact hε
        have hyne : y - r ≠ 0 := by
          rw [hy]
          by_cases hxr : x = r
          · rw [if_pos hxr, ← hxr]
            intro hcon2
            have : ε / 2 = 0 := by linarith [hcon2]
            linarith
          · rw [if_neg hxr]
            exact sub_ne_zero.mpr hxr
        have hgy : g.eval y < 0 := hball hyclose
        have hpy := hnn y
        rw [hpg, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hpy
        have hsq : (0 : ℝ) < (y - r) ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hyne))
        nlinarith
      have hg0 : g ≠ 0 := fun hcon => hp0 (by rw [hpg, hcon, mul_zero])
      have hxr0 : ((X : ℝ[X]) - C r) ^ 2 ≠ 0 := pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero r)
      have hdegg : g.natDegree + 2 = p.natDegree := by
        rw [hpg, natDegree_mul hxr0 hg0, natDegree_pow, Polynomial.natDegree_X_sub_C]
        ring
      obtain ⟨a, b, hab⟩ := ih g.natDegree (by omega) g (le_refl _) hgnn
      exact ⟨(X - C r) * a, (X - C r) * b, by rw [hpg, hab]; ring⟩
    · -- an irreducible quadratic factor is itself a sum of two squares
      set h : ℝ[X] := f * C (f.leadingCoeff)⁻¹ with hh
      have hmonic : h.Monic := monic_mul_leadingCoeff_inv hf0
      have hCne : (C (f.leadingCoeff)⁻¹ : ℝ[X]) ≠ 0 := by
        simpa using inv_ne_zero hlc
      have hhdeg : h.natDegree = 2 := by
        rw [hh, natDegree_mul hf0 hCne, Polynomial.natDegree_C, hfd]
      have hunit : IsUnit (C (f.leadingCoeff)⁻¹ : ℝ[X]) :=
        Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc))
      have hass : Associated f h := ⟨hunit.unit, by rw [hh]; rfl⟩
      have hhirr : Irreducible h := hass.irreducible hfirr
      have hhdvd : h ∣ p := hass.dvd_iff_dvd_left.mp hfdvd
      have hnoroot : ∀ r : ℝ, h.eval r ≠ 0 := by
        intro r hrz
        obtain ⟨k, hk⟩ := Polynomial.dvd_iff_isRoot.mpr hrz
        rcases hhirr.isUnit_or_isUnit hk with hu | hu
        · have := Polynomial.natDegree_eq_zero_of_isUnit hu
          rw [Polynomial.natDegree_X_sub_C] at this
          exact one_ne_zero this
        · have hk0 : k.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
          have hkne : k ≠ 0 := fun hc => by
            rw [hc, mul_zero] at hk; exact hmonic.ne_zero hk
          have := hhdeg
          rw [hk, natDegree_mul (Polynomial.X_sub_C_ne_zero r) hkne,
            Polynomial.natDegree_X_sub_C, hk0] at this
          omega
      obtain ⟨u, v, huv, hpos⟩ := monic_quadratic_sq_add_sq hmonic hhdeg hnoroot
      obtain ⟨g, hg⟩ := hhdvd
      have hgnn : ∀ x : ℝ, 0 ≤ g.eval x := cofactor_nonneg hg hpos hnn
      have hg0 : g ≠ 0 := fun hcon => hp0 (by rw [hg, hcon, mul_zero])
      have hdegg : g.natDegree + 2 = p.natDegree := by
        rw [hg, natDegree_mul hmonic.ne_zero hg0, hhdeg]
        ring
      obtain ⟨a, b, hab⟩ := ih g.natDegree (by omega) g (le_refl _) hgnn
      exact ⟨u * a + v * b, u * b - v * a, by rw [hg, huv, hab, ← sq_add_sq_mul]⟩

/-- **The half-line form.**  A real polynomial nonnegative on `[0, ∞)` becomes a sum of two squares
after the substitution `y ↦ y²`. -/
theorem exists_sq_add_sq_comp_sq (p : ℝ[X]) (h : ∀ y : ℝ, 0 ≤ y → 0 ≤ p.eval y) :
    ∃ A B : ℝ[X], ∀ y : ℝ, p.eval (y ^ 2) = (A.eval y) ^ 2 + (B.eval y) ^ 2 := by
  set q : ℝ[X] := p.comp (X ^ 2) with hq
  have hqeval : ∀ y : ℝ, q.eval y = p.eval (y ^ 2) := by
    intro y
    rw [hq, Polynomial.eval_comp, eval_pow, eval_X]
  obtain ⟨A, B, hAB⟩ := exists_sq_add_sq_of_nonneg q.natDegree q (le_refl _) (fun y => by
    rw [hqeval]
    exact h (y ^ 2) (sq_nonneg y))
  refine ⟨A, B, fun y => ?_⟩
  rw [← hqeval, hAB]
  simp

end GaloisForLFunctions.HTGeometry
