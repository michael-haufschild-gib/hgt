import GaloisForLFunctions.RHTower.XiCTaylorThetaTailDensityAtoms

/-!
# Arithmetic logarithmic translates of the canonical theta-tail density

Every positive-index differentiated Gaussian atom is an exact logarithmic translate of the
first atom, with the arithmetic weight `n^(-1/2)`.  Thus the full canonical density is not an
arbitrary positive mixture: all of its phase cancellation is carried by one fixed profile sampled
on the logarithmic integer lattice.  These identities retain the complete arithmetic
interference that is lost by first-atom domination estimates.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Exact logarithmic-translation law for every polynomial Gaussian theta atom. -/
theorem thetaCuspPolynomialAtom_eq_rpow_mul_translate
    (P : ℝ[X]) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    thetaCuspPolynomialAtom P n x =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspPolynomialAtom P 1 (x + Real.log n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale :
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp ((x + Real.log n) / 2) =
        Real.exp (x / 2) := by
    rw [show (x + Real.log n) / 2 = x / 2 + Real.log n / 2 by ring,
      Real.exp_add, Real.rpow_def_of_pos hnR]
    calc
      Real.exp (Real.log (n : ℝ) * (-(1 / 2 : ℝ))) *
          (Real.exp (x / 2) * Real.exp (Real.log n / 2)) =
          Real.exp (x / 2) *
            (Real.exp (Real.log n * (-(1 / 2 : ℝ))) *
              Real.exp (Real.log n / 2)) := by ring
      _ = Real.exp (x / 2) * Real.exp 0 := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = Real.exp (x / 2) := by rw [Real.exp_zero, mul_one]
  have harg : Real.exp (x + Real.log n) = (n : ℝ) * Real.exp x := by
    rw [Real.exp_add, Real.exp_log hnR]
    ring
  unfold thetaCuspPolynomialAtom
  simp only [Nat.cast_one, one_mul]
  rw [harg]
  rw [show (n : ℝ) ^ (-(1 / 2 : ℝ)) *
      (Real.exp ((x + Real.log n) / 2) *
        eval ((n : ℝ) * Real.exp x) P *
          Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2)) =
      ((n : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp ((x + Real.log n) / 2)) *
          eval ((n : ℝ) * Real.exp x) P *
            Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2) by ring,
    hscale]

/-- Every atom of `4 T''` is the corresponding arithmetic translate of the first atom. -/
theorem thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    thetaCuspTailSecondDensityAtom n x =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspTailSecondDensityAtom 1 (x + Real.log n) := by
  unfold thetaCuspTailSecondDensityAtom
  rw [thetaCuspPolynomialAtom_eq_rpow_mul_translate _ hn]
  ring

/-- The complete canonical density is one differentiated Gaussian profile sampled on the
logarithmic integer lattice with its exact critical weights. -/
theorem thetaCuspTailSecondDensity_eq_tsum_arithmetic_translates (x : ℝ) :
    thetaCuspTailSecondDensity x =
      ∑' n : ℕ,
        ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          thetaCuspTailSecondDensityAtom 1
            (x + Real.log (n + 1 : ℕ)) := by
  rw [thetaCuspTailSecondDensity_eq_tsum_atom]
  apply tsum_congr
  intro n
  exact thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate
    (Nat.succ_pos n) x

/-- Translation of a positive-half-line integral to the corresponding shifted half-line. -/
theorem integral_Ioi_comp_add_eq_integral_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (ell : ℝ) :
    (∫ x : ℝ in Ioi 0, f (x + ell)) =
      ∫ u : ℝ in Ioi ell, f u := by
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioi]
  let g : ℝ → E := (Ioi ell).indicator f
  calc
    (∫ x : ℝ, (Ioi 0).indicator (fun x => f (x + ell)) x) =
        ∫ x : ℝ, g (x + ell) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · have hxl : x + ell ∈ Ioi ell := by
          simpa using add_lt_add_right hx ell
        simp [g, hx, hxl]
      · have hxl : x + ell ∉ Ioi ell := by
          simp only [mem_Ioi, not_lt] at hx ⊢
          linarith
        simp [g, hx, hxl]
    _ = ∫ u : ℝ, g u := by
      exact (measurePreserving_add_right volume ell).integral_comp
        (Homeomorph.addRight ell).measurableEmbedding g
    _ = ∫ u : ℝ, (Ioi ell).indicator f u := rfl

/-- Pairing one density atom with an arbitrary complex test function exposes its exact
logarithmic shift and shifted lower endpoint. -/
theorem integral_densityAtom_mul_eq_rpow_mul_integral_translate
    (K : ℝ → ℂ) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensityAtom n x : ℂ) * K x) =
      ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
        ∫ u : ℝ in Ioi (Real.log n),
          (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
            K (u - Real.log n) := by
  let ell : ℝ := Real.log n
  let weight : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ))
  let f : ℝ → ℂ := fun u =>
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) * K (u - ell)
  have htranslate := integral_Ioi_comp_add_eq_integral_Ioi f ell
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom n x : ℂ) * K x) =
      fun x => (weight : ℂ) * f (x + ell) by
    funext x
    rw [thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate hn]
    dsimp [weight, f, ell]
    push_cast
    rw [add_sub_cancel_right]
    ring]
  rw [integral_const_mul, htranslate]

/-- Arithmetic-translate form of one finite core value contribution. -/
theorem integral_densityAtom_mul_coreAtom_eq_translate
    (d : ℕ) (z : ℂ) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensityAtom n x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) =
      ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
        ∫ u : ℝ in Ioi (Real.log n),
          (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
            thetaCuspTailSecondCoreAtom d z (u - Real.log n) := by
  exact integral_densityAtom_mul_eq_rpow_mul_integral_translate
    (fun x => thetaCuspTailSecondCoreAtom d z x) hn

end

end RHTower
