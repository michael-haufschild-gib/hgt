import GaloisForLFunctions.RHTower.PrimeArchThetaBeyondSecondLikelihoodOrder

/-!
# Quantitative likelihood separation of theta atoms

The Born--Witten score gap gives an exponential contraction of every later
atom's density ratio against an earlier atom. This retains the size of the
likelihood gap, beyond its previously proved order sign.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

/-- Every pairwise Born--Witten score gap is at least its Morse-scale gap. -/
theorem thetaCuspBornWitten_pairScoreGap_ge_scaleGap
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspMorseScale n x - thetaCuspMorseScale m x ≤
      thetaCuspBornWittenSuperpotential n x -
        thetaCuspBornWittenSuperpotential m x := by
  have hn : 0 < n := hm.trans_le hmn
  have hscale : 0 ≤ thetaCuspMorseScale n x - thetaCuspMorseScale m x :=
    sub_nonneg.mpr (thetaCuspMorseScale_mono_nat hmn x)
  have hwn := thetaCuspBornWittenWeight_pos hn hx
  have hwm := thetaCuspBornWittenWeight_pos hm hx
  have hbonus : 0 ≤ (3 / 2 : ℝ) /
      (thetaCuspBornWittenWeight n x * thetaCuspBornWittenWeight m x) := by
    positivity
  rw [thetaCuspBornWittenSuperpotential_sub_eq_scaleDifference_mul hm hn hx]
  nlinarith [mul_nonneg hscale hbonus]

/-- The Morse-scale gap increases away from the theta seam at zero. -/
theorem thetaCuspMorseScale_pairGap_ge_zeroGap
    {m n : ℕ} (hmn : m ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspMorseScale n 0 - thetaCuspMorseScale m 0 ≤
      thetaCuspMorseScale n x - thetaCuspMorseScale m x := by
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hsq : 0 ≤ (n : ℝ) ^ (2 : ℕ) - (m : ℝ) ^ (2 : ℕ) := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hexp : 1 ≤ Real.exp x ^ (2 : ℕ) := by
    have he : 1 ≤ Real.exp x := by
      simpa using Real.exp_le_exp.mpr hx
    nlinarith [Real.exp_pos x]
  have hprod := mul_nonneg
    (mul_nonneg Real.pi_pos.le hsq) (sub_nonneg.mpr hexp)
  simp only [thetaCuspMorseScale, Real.exp_zero, mul_one]
  nlinarith [hprod]

/-- The pairwise score gap has a uniform strictly positive seam value when `m<n`. -/
theorem thetaCuspBornWitten_pairScoreGap_ge_zeroScaleGap
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspMorseScale n 0 - thetaCuspMorseScale m 0 ≤
      thetaCuspBornWittenSuperpotential n x -
        thetaCuspBornWittenSuperpotential m x :=
  (thetaCuspMorseScale_pairGap_ge_zeroGap hmn hx).trans
    (thetaCuspBornWitten_pairScoreGap_ge_scaleGap hm hmn hx)

/-- The exponential tilt removes the constant part of the score gap. -/
theorem thetaCuspAtomPairLikelihoodRatio_expTilt_antitoneOn
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    let κ := 2 * (thetaCuspMorseScale n 0 - thetaCuspMorseScale m 0)
    AntitoneOn
      (fun x : ℝ => Real.exp (κ * x) * thetaCuspAtomPairLikelihoodRatio m n x)
      (Ioi 0) := by
  dsimp only
  let κ : ℝ := 2 * (thetaCuspMorseScale n 0 - thetaCuspMorseScale m 0)
  let F : ℝ → ℝ := fun x =>
    Real.exp (κ * x) * thetaCuspAtomPairLikelihoodRatio m n x
  have hn : 0 < n := hm.trans_le hmn
  have hderiv {x : ℝ} (hx : 0 < x) :
      HasDerivAt F
        (Real.exp (κ * x) * thetaCuspAtomPairLikelihoodRatio m n x *
          (κ - 2 * (thetaCuspBornWittenSuperpotential n x -
            thetaCuspBornWittenSuperpotential m x))) x := by
    have hlin : HasDerivAt (fun t : ℝ => κ * t) κ x := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul κ
    have hexp := (Real.hasDerivAt_exp (κ * x)).comp x hlin
    have hratio := hasDerivAt_thetaCuspAtomPairLikelihoodRatio hm hn hx
    have hmul := hexp.mul hratio
    have hmul' : HasDerivAt F
        (Real.exp (κ * x) * κ * thetaCuspAtomPairLikelihoodRatio m n x +
          Real.exp (κ * x) *
            (-2 * (thetaCuspBornWittenSuperpotential n x -
              thetaCuspBornWittenSuperpotential m x) *
                thetaCuspAtomPairLikelihoodRatio m n x)) x := by
      simpa only [F, Function.comp_apply, Pi.mul_apply] using! hmul
    have heq :
        Real.exp (κ * x) * thetaCuspAtomPairLikelihoodRatio m n x *
          (κ - 2 * (thetaCuspBornWittenSuperpotential n x -
            thetaCuspBornWittenSuperpotential m x)) =
          Real.exp (κ * x) * κ * thetaCuspAtomPairLikelihoodRatio m n x +
          Real.exp (κ * x) *
            (-2 * (thetaCuspBornWittenSuperpotential n x -
              thetaCuspBornWittenSuperpotential m x) *
                thetaCuspAtomPairLikelihoodRatio m n x) := by ring
    rw [heq]
    exact hmul'
  change AntitoneOn F (Ioi 0)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx
    exact (hderiv hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hderiv hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hgap := thetaCuspBornWitten_pairScoreGap_ge_zeroScaleGap hm hmn hx.le
    have hr : 0 ≤ thetaCuspAtomPairLikelihoodRatio m n x :=
      (div_pos
        (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hn)
        (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hm)).le
    rw [(hderiv hx).deriv]
    have hfactor : κ - 2 * (thetaCuspBornWittenSuperpotential n x -
        thetaCuspBornWittenSuperpotential m x) ≤ 0 := by
      dsimp only [κ]
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le hr) hfactor

/-- Later-to-earlier atom density ratios contract at least exponentially with
separation in logarithmic source position. -/
theorem thetaCuspAtomPairLikelihoodRatio_le_expGap_mul
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    let κ := 2 * (thetaCuspMorseScale n 0 - thetaCuspMorseScale m 0)
    thetaCuspAtomPairLikelihoodRatio m n y ≤
      Real.exp (-κ * (y - x)) * thetaCuspAtomPairLikelihoodRatio m n x := by
  dsimp only
  let κ : ℝ := 2 * (thetaCuspMorseScale n 0 - thetaCuspMorseScale m 0)
  have hy : 0 < y := hx.trans_le hxy
  have hmono := thetaCuspAtomPairLikelihoodRatio_expTilt_antitoneOn
    hm hmn hx hy hxy
  change Real.exp (κ * y) * thetaCuspAtomPairLikelihoodRatio m n y ≤
    Real.exp (κ * x) * thetaCuspAtomPairLikelihoodRatio m n x at hmono
  have hExp : 0 < Real.exp (κ * y) := Real.exp_pos _
  have hprod : thetaCuspAtomPairLikelihoodRatio m n y * Real.exp (κ * y) ≤
      Real.exp (κ * x) * thetaCuspAtomPairLikelihoodRatio m n x := by
    simpa only [mul_comm] using hmono
  have hdiv := (le_div_iff₀ hExp).2 hprod
  calc
    thetaCuspAtomPairLikelihoodRatio m n y ≤
        (Real.exp (κ * x) * thetaCuspAtomPairLikelihoodRatio m n x) /
          Real.exp (κ * y) := hdiv
    _ = (Real.exp (κ * x) / Real.exp (κ * y)) *
          thetaCuspAtomPairLikelihoodRatio m n x := by ring
    _ = Real.exp (-κ * (y - x)) *
          thetaCuspAtomPairLikelihoodRatio m n x := by
        rw [← Real.exp_sub]
        congr 1
        ring

/-- Using the full increasing Morse gap gives a stronger exponential tilt. -/
theorem thetaCuspAtomPairLikelihoodRatio_morseTilt_antitoneOn
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    AntitoneOn
      (fun x : ℝ => Real.exp
        (thetaCuspMorseScale n x - thetaCuspMorseScale m x) *
          thetaCuspAtomPairLikelihoodRatio m n x) (Ioi 0) := by
  let τ : ℝ → ℝ := fun x =>
    thetaCuspMorseScale n x - thetaCuspMorseScale m x
  let F : ℝ → ℝ := fun x =>
    Real.exp (τ x) * thetaCuspAtomPairLikelihoodRatio m n x
  have hn : 0 < n := hm.trans_le hmn
  have hderiv {x : ℝ} (hx : 0 < x) :
      HasDerivAt F
        (Real.exp (τ x) * thetaCuspAtomPairLikelihoodRatio m n x *
          (2 * τ x - 2 * (thetaCuspBornWittenSuperpotential n x -
            thetaCuspBornWittenSuperpotential m x))) x := by
    have hτ : HasDerivAt τ (2 * τ x) x := by
      have hdiff := (hasDerivAt_thetaCuspMorseScale n x).sub
        (hasDerivAt_thetaCuspMorseScale m x)
      simpa only [τ, mul_sub] using! hdiff
    have hexp := (Real.hasDerivAt_exp (τ x)).comp x hτ
    have hratio := hasDerivAt_thetaCuspAtomPairLikelihoodRatio hm hn hx
    have hmul := hexp.mul hratio
    have hmul' : HasDerivAt F
        (Real.exp (τ x) * (2 * τ x) * thetaCuspAtomPairLikelihoodRatio m n x +
          Real.exp (τ x) *
            (-2 * (thetaCuspBornWittenSuperpotential n x -
              thetaCuspBornWittenSuperpotential m x) *
                thetaCuspAtomPairLikelihoodRatio m n x)) x := by
      simpa only [F, Function.comp_apply, Pi.mul_apply] using! hmul
    have heq :
        Real.exp (τ x) * thetaCuspAtomPairLikelihoodRatio m n x *
          (2 * τ x - 2 * (thetaCuspBornWittenSuperpotential n x -
            thetaCuspBornWittenSuperpotential m x)) =
          Real.exp (τ x) * (2 * τ x) * thetaCuspAtomPairLikelihoodRatio m n x +
          Real.exp (τ x) *
            (-2 * (thetaCuspBornWittenSuperpotential n x -
              thetaCuspBornWittenSuperpotential m x) *
                thetaCuspAtomPairLikelihoodRatio m n x) := by ring
    rw [heq]
    exact hmul'
  change AntitoneOn F (Ioi 0)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx
    exact (hderiv hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hderiv hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hgap := thetaCuspBornWitten_pairScoreGap_ge_scaleGap hm hmn hx.le
    have hr : 0 ≤ thetaCuspAtomPairLikelihoodRatio m n x :=
      (div_pos
        (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hn)
        (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hm)).le
    rw [(hderiv hx).deriv]
    have hfactor : 2 * τ x - 2 *
        (thetaCuspBornWittenSuperpotential n x -
          thetaCuspBornWittenSuperpotential m x) ≤ 0 := by
      dsimp only [τ]
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le hr) hfactor

/-- Superexponential pair separation across a positive source interval. -/
theorem thetaCuspAtomPairLikelihoodRatio_le_expMorseGap_mul
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    let τ := fun z : ℝ => thetaCuspMorseScale n z - thetaCuspMorseScale m z
    thetaCuspAtomPairLikelihoodRatio m n y ≤
      Real.exp (-(τ y - τ x)) * thetaCuspAtomPairLikelihoodRatio m n x := by
  dsimp only
  let τ : ℝ → ℝ := fun z =>
    thetaCuspMorseScale n z - thetaCuspMorseScale m z
  have hy : 0 < y := hx.trans_le hxy
  have hmono := thetaCuspAtomPairLikelihoodRatio_morseTilt_antitoneOn
    hm hmn hx hy hxy
  change Real.exp (τ y) * thetaCuspAtomPairLikelihoodRatio m n y ≤
    Real.exp (τ x) * thetaCuspAtomPairLikelihoodRatio m n x at hmono
  have hExp : 0 < Real.exp (τ y) := Real.exp_pos _
  have hprod : thetaCuspAtomPairLikelihoodRatio m n y * Real.exp (τ y) ≤
      Real.exp (τ x) * thetaCuspAtomPairLikelihoodRatio m n x := by
    simpa only [mul_comm] using hmono
  have hdiv := (le_div_iff₀ hExp).2 hprod
  calc
    thetaCuspAtomPairLikelihoodRatio m n y ≤
        (Real.exp (τ x) * thetaCuspAtomPairLikelihoodRatio m n x) /
          Real.exp (τ y) := hdiv
    _ = (Real.exp (τ x) / Real.exp (τ y)) *
          thetaCuspAtomPairLikelihoodRatio m n x := by ring
    _ = Real.exp (-(τ y - τ x)) *
          thetaCuspAtomPairLikelihoodRatio m n x := by
        rw [← Real.exp_sub]
        congr 1
        ring

/-- Quantitative two-point total positivity for an ordered theta-atom pair.
The usual nonnegative determinant retains a source-specific exponential margin. -/
theorem thetaCuspAtom_pairTwoPointGap_ge_expMargin
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    let κ := 2 * (thetaCuspMorseScale n 0 - thetaCuspMorseScale m 0)
    (1 - Real.exp (-κ * (y - x))) *
        thetaCuspSourceTerm x n * thetaCuspSourceTerm y m ≤
      thetaCuspSourceTerm x n * thetaCuspSourceTerm y m -
        thetaCuspSourceTerm y n * thetaCuspSourceTerm x m := by
  dsimp only
  let κ : ℝ := 2 * (thetaCuspMorseScale n 0 - thetaCuspMorseScale m 0)
  let E : ℝ := Real.exp (-κ * (y - x))
  have hn : 0 < n := hm.trans_le hmn
  have hy : 0 < y := hx.trans_le hxy
  have hmx := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx hm
  have hmy := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hy hm
  have hr := thetaCuspAtomPairLikelihoodRatio_le_expGap_mul hm hmn hx hxy
  change thetaCuspSourceTerm y n / thetaCuspSourceTerm y m ≤
    E * (thetaCuspSourceTerm x n / thetaCuspSourceTerm x m) at hr
  have hfrac : E * (thetaCuspSourceTerm x n / thetaCuspSourceTerm x m) =
      (E * thetaCuspSourceTerm x n) / thetaCuspSourceTerm x m := by ring
  rw [hfrac] at hr
  have hcross := (div_le_div_iff₀ hmy hmx).mp hr
  change thetaCuspSourceTerm y n * thetaCuspSourceTerm x m ≤
    (E * thetaCuspSourceTerm x n) * thetaCuspSourceTerm y m at hcross
  change (1 - E) * thetaCuspSourceTerm x n * thetaCuspSourceTerm y m ≤
    thetaCuspSourceTerm x n * thetaCuspSourceTerm y m -
      thetaCuspSourceTerm y n * thetaCuspSourceTerm x m
  nlinarith

end
end RHTower
