import GaloisForLFunctions.HTGeometry.DaiYoshikawa.LogarithmicCutoffEnergy

/-!
# Monomial pairings over an annulus

The computation of (5.2) in Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues
of the Laplacian* (arXiv:2509.06151v2), rests on a single orthogonality: over the vanishing annulus
`|t| ≤ |x| ≤ 1`, the pairing of two Laurent monomials against the cylindrical area element
`dA/|x|²` vanishes unless the two exponents agree, and on the diagonal it is

```text
∫_{a<|x|<b} x^j \overline{x}^j |x|^{-2} dA
   =  2π log(b/a)                 (j = 0),
   =  2π (b^{2j} − a^{2j})/(2j)   (j ≠ 0).
```

Only the `j = 0` term diverges as `a → 0`, and it diverges logarithmically: that is the source of
the `log|t|^{-2}` in Proposition 5.1, whose coefficient is therefore the product of the two residues
— the `x^(0 : ℕ)` Laurent coefficients.

The computation is the polar reduction of `LogarithmicCutoffEnergy` applied to a monomial, together
with the orthogonality `∫_{-π}^{π} e^{ikθ} dθ = 2π δ_{k0}`.
-/

open MeasureTheory Set Real Complex

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

open _root_.HTGeometry (deningerAnnulus polarCoord_symm_eq_circleMap)

/-- The monomial pairing `x^j \overline{x}^{j'}` against the cylindrical area element. -/
noncomputable def annulusMonomial (j j' : ℤ) (w : ℂ) : ℂ :=
  w ^ j * (starRingEnd ℂ) w ^ j' / ((‖w‖ : ℂ) ^ 2)

/-! ## The angular factor -/

/-- **Orthogonality of the circle characters.**
`∫_{-π}^{π} e^{ikθ} dθ = 2π` if `k = 0` and `0` otherwise. -/
theorem integral_Ioo_exp_int_mul_I (k : ℤ) :
    (∫ θ in Ioo (-π) π, Complex.exp (((k : ℂ) * Complex.I) * (θ : ℂ)))
      = if k = 0 then (2 * π : ℂ) else 0 := by
  have hIoo : (∫ θ in Ioo (-π) π, Complex.exp (((k : ℂ) * Complex.I) * (θ : ℂ)))
      = ∫ θ in (-π)..π, Complex.exp (((k : ℂ) * Complex.I) * (θ : ℂ)) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hIoo]
  by_cases hk : k = 0
  · subst hk
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero]
    rw [intervalIntegral.integral_const, Complex.real_smul, mul_one]
    push_cast
    ring
  · rw [if_neg hk]
    have hc : ((k : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast hk
    rw [integral_exp_mul_complex hc]
    have hzero : Complex.exp (((k : ℂ) * Complex.I) * (π : ℂ))
        - Complex.exp (((k : ℂ) * Complex.I) * ((-π : ℝ) : ℂ)) = 0 := by
      have hper : Complex.exp ((k : ℂ) * (2 * (π : ℂ) * Complex.I)) = 1 :=
        Complex.exp_int_mul_two_pi_mul_I k
      have hsplit : ((k : ℂ) * Complex.I) * (π : ℂ)
          = ((k : ℂ) * Complex.I) * ((-π : ℝ) : ℂ) + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
        push_cast
        ring
      rw [hsplit, Complex.exp_add, hper, mul_one, sub_self]
    rw [hzero, zero_div]

/-! ## The radial factor -/

/-- The radial integral `∫_a^b r^{m-1} dr`. -/
theorem integral_Ioo_zpow_sub_one (m : ℤ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ r in Ioo a b, r ^ (m - 1))
      = if m = 0 then Real.log (b / a) else (b ^ m - a ^ m) / m := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hIoo : (∫ r in Ioo a b, r ^ (m - 1)) = ∫ r in a..b, r ^ (m - 1) := by
    rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hIoo]
  have hmem : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro hc
    exact absurd hc.1 (not_le.mpr ha)
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl]
    have hrw : (fun r : ℝ => r ^ ((0 : ℤ) - 1)) = fun r : ℝ => 1 / r := by
      funext r
      rw [zero_sub, zpow_neg_one, one_div]
    rw [hrw]
    exact integral_one_div_of_pos ha hb
  · rw [if_neg hm]
    have hcond : (0 : ℤ) ≤ m - 1 ∨ m - 1 ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc a b := by
      right
      exact ⟨by omega, hmem⟩
    rw [integral_zpow hcond]
    have hm1 : m - 1 + 1 = m := by ring
    rw [hm1]
    push_cast
    ring_nf

/-! ## The pointwise polar form -/

/-- The monomial pairing in polar coordinates. -/
theorem annulusMonomial_circleMap {r : ℝ} (hr : 0 < r) (θ : ℝ) (j j' : ℤ) :
    r • annulusMonomial j j' (circleMap 0 r θ)
      = ((r ^ (j + j' - 1) : ℝ) : ℂ)
          * Complex.exp ((((j - j' : ℤ) : ℂ) * Complex.I) * (θ : ℂ)) := by
  have hrc : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hcm : circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [circleMap]
  have hexpne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hconj : (starRingEnd ℂ) (circleMap 0 r θ)
      = (r : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [hcm, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
  have hnorm : ‖circleMap 0 r θ‖ = r := by
    rw [norm_circleMap_zero, abs_of_pos hr]
  rw [annulusMonomial, hconj, hnorm, hcm, mul_zpow, mul_zpow]
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul]
  have hrz : ((r : ℂ)) ^ j * ((r : ℂ)) ^ j' / ((r : ℂ)) ^ 2 = ((r : ℂ)) ^ (j + j' - 2) := by
    rw [← zpow_add₀ hrc, ← zpow_natCast ((r : ℂ)) 2, ← zpow_sub₀ hrc]
    norm_num
  have hstep : (r : ℂ) ^ j * Complex.exp ((j : ℂ) * ((θ : ℂ) * Complex.I))
        * ((r : ℂ) ^ j' * Complex.exp ((j' : ℂ) * (-((θ : ℂ) * Complex.I)))) / ((r : ℂ)) ^ 2
      = (((r : ℂ)) ^ j * ((r : ℂ)) ^ j' / ((r : ℂ)) ^ 2)
          * (Complex.exp ((j : ℂ) * ((θ : ℂ) * Complex.I))
              * Complex.exp ((j' : ℂ) * (-((θ : ℂ) * Complex.I)))) := by
    ring
  rw [hstep, hrz, ← Complex.exp_add]
  have hsmul : r • (((r : ℂ)) ^ (j + j' - 2)
      * Complex.exp ((j : ℂ) * ((θ : ℂ) * Complex.I)
          + (j' : ℂ) * (-((θ : ℂ) * Complex.I))))
      = ((r : ℂ)) ^ (j + j' - 1)
          * Complex.exp ((((j - j' : ℤ) : ℂ) * Complex.I) * (θ : ℂ)) := by
    rw [Complex.real_smul]
    have hpow : ((r : ℂ)) * ((r : ℂ)) ^ (j + j' - 2) = ((r : ℂ)) ^ (j + j' - 1) := by
      rw [← zpow_one_add₀ hrc]
      congr 1
      ring
    have hexp : (j : ℂ) * ((θ : ℂ) * Complex.I) + (j' : ℂ) * (-((θ : ℂ) * Complex.I))
        = (((j - j' : ℤ) : ℂ) * Complex.I) * (θ : ℂ) := by
      push_cast
      ring
    rw [← mul_assoc, hpow, hexp]
  rw [hsmul, Complex.ofReal_zpow]

/-! ## The annulus integral -/

/-- **The monomial pairing over an annulus.**

`∫_{a<|x|<b} x^j \overline{x}^{j'} |x|^{-2} dA` factors as a radial times an angular integral. -/
theorem setIntegral_annulusMonomial (j j' : ℤ) {a b : ℝ} (ha : 0 < a) :
    (∫ w in deningerAnnulus a b, annulusMonomial j j' w)
      = (∫ r in Ioo a b, ((r ^ (j + j' - 1) : ℝ) : ℂ))
          * ∫ θ in Ioo (-π) π, Complex.exp ((((j - j' : ℤ) : ℂ) * Complex.I) * (θ : ℂ)) := by
  set A : Set ℂ := deningerAnnulus a b with hA
  set f : ℂ → ℂ := annulusMonomial j j' with hf
  have hAopen : IsOpen A := by
    have hpre : A = (fun w : ℂ => ‖w‖) ⁻¹' (Set.Ioo a b) := by
      ext w; simp [hA, deningerAnnulus, Set.mem_Ioo]
    rw [hpre]
    exact isOpen_Ioo.preimage continuous_norm
  have hAmeas : MeasurableSet A := hAopen.measurableSet
  have hBmeas : MeasurableSet (Set.Ioo a b ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hpolar := Complex.integral_comp_polarCoord_symm (Set.indicator A f)
  rw [MeasureTheory.integral_indicator hAmeas] at hpolar
  have htgt : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [← hpolar, htgt]
  have key : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
      p.1 • Set.indicator A f (Complex.polarCoord.symm p)
        = Set.indicator (Set.Ioo a b ×ˢ Set.Ioo (-π) π)
            (fun q : ℝ × ℝ => ((q.1 ^ (j + j' - 1) : ℝ) : ℂ)
              * Complex.exp ((((j - j' : ℤ) : ℂ) * Complex.I) * ((q.2 : ℝ) : ℂ))) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [Set.mem_Ioi] at hr
    have hsymm : Complex.polarCoord.symm (r, θ) = circleMap 0 r θ :=
      polarCoord_symm_eq_circleMap (r, θ)
    have hnorm : ‖circleMap 0 r θ‖ = r := by
      rw [norm_circleMap_zero, abs_of_pos hr]
    by_cases hmem : a < r ∧ r < b
    · have h1 : circleMap 0 r θ ∈ A := by
        rw [hA]
        simp only [deningerAnnulus, Set.mem_setOf_eq, hnorm]
        exact hmem
      have h2 : ((r, θ) : ℝ × ℝ) ∈ Set.Ioo a b ×ˢ Set.Ioo (-π) π := ⟨hmem, hθ⟩
      rw [hsymm, Set.indicator_of_mem h1, Set.indicator_of_mem h2, hf]
      exact annulusMonomial_circleMap hr θ j j'
    · have h1 : circleMap 0 r θ ∉ A := by
        rw [hA]
        simp only [deningerAnnulus, Set.mem_setOf_eq, hnorm]
        exact hmem
      have h2 : ((r, θ) : ℝ × ℝ) ∉ Set.Ioo a b ×ˢ Set.Ioo (-π) π := by
        intro hc
        exact hmem hc.1
      rw [hsymm, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, smul_zero]
  rw [MeasureTheory.setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) key,
    MeasureTheory.setIntegral_indicator hBmeas]
  have hInter : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π ∩ (Set.Ioo a b ×ˢ Set.Ioo (-π) π)
      = Set.Ioo a b ×ˢ Set.Ioo (-π) π :=
    Set.inter_eq_self_of_subset_right
      (Set.prod_mono (fun x hx => lt_trans ha hx.1) (subset_refl _))
  rw [hInter, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.setIntegral_prod_mul (fun r : ℝ => ((r ^ (j + j' - 1) : ℝ) : ℂ))
      (fun θ : ℝ => Complex.exp ((((j - j' : ℤ) : ℂ) * Complex.I) * (θ : ℂ)))
      (Set.Ioo a b) (Set.Ioo (-π) π)]

/-- **Off-diagonal monomials integrate to zero.** -/
theorem setIntegral_annulusMonomial_of_ne {j j' : ℤ} (hne : j ≠ j') {a b : ℝ}
    (ha : 0 < a) :
    (∫ w in deningerAnnulus a b, annulusMonomial j j' w) = 0 := by
  rw [setIntegral_annulusMonomial j j' ha, integral_Ioo_exp_int_mul_I,
    if_neg (sub_ne_zero.mpr hne), mul_zero]

/-- **The diagonal monomial with exponent zero diverges logarithmically.** -/
theorem setIntegral_annulusMonomial_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ w in deningerAnnulus a b, annulusMonomial 0 0 w) = 2 * π * Real.log (b / a) := by
  rw [setIntegral_annulusMonomial 0 0 ha]
  simp only [sub_self]
  rw [integral_Ioo_exp_int_mul_I 0, if_pos rfl, integral_complex_ofReal]
  rw [show (0 : ℤ) + 0 - 1 = (0 : ℤ) - 1 by ring]
  rw [integral_Ioo_zpow_sub_one 0 ha hab, if_pos rfl]
  ring

/-- **The diagonal monomials with nonzero exponent stay bounded.** -/
theorem setIntegral_annulusMonomial_diag {j : ℤ} (hj : j ≠ 0) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ w in deningerAnnulus a b, annulusMonomial j j w)
      = 2 * π * ((b ^ (2 * j) - a ^ (2 * j)) / (2 * j)) := by
  have hj2 : (2 : ℤ) * j ≠ 0 := by omega
  rw [setIntegral_annulusMonomial j j ha]
  simp only [sub_self]
  rw [integral_Ioo_exp_int_mul_I 0, if_pos rfl, integral_complex_ofReal]
  rw [show j + j - 1 = 2 * j - 1 by ring]
  rw [integral_Ioo_zpow_sub_one (2 * j) ha hab, if_neg hj2]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
