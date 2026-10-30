import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheApertureModesCarryTheThetaApertureCharge

/-!
# A windowed aperture mode is an exponential box test

The **windowed aperture mode** has atomic coefficients `y_n = n^{κ−1}` on the window `M < n ≤ N`
and `0` elsewhere. Its Dirichlet factor at a shift `s` is `X_N(s) − X_M(s)`. At a nontrivial zero
`ζ` cancels between the two horizons (`windowSum_eq_horizonBoundary_sub`): the factor is
`B_M(s) − B_N(s)` exactly, with no `ζ` term, so for every C² compact atom

`Q(f) = Re Σ_ρ m_ρ ĝ(γ_ρ) conj ĝ(conj γ_ρ) (B_M − B_N)(1−ρ+a) (B_M − B_N)(ρ+a)`,  `a = 1/2 − κ`
(`weilQuad_windowedApertureMode_eq_tsum`).

The pole parts of the two horizons multiply to the zero-side summand of Weil's exponential box
test `e^{κu} 1_{[log M, log N]}` (`windowPole_mul_eq`): with `z = ρ − 1/2`,

`(N^{2κ} + M^{2κ} − N^{κ−z} M^{κ+z} − M^{κ−z} N^{κ+z}) / (κ² − z²)`.

The two cross terms have modulus `N^{κ}M^{κ}(N/M)^{±Re z}`: a zero with `|Re z| > κ` makes them
outgrow the diagonal as the window `N/M` grows. The Euler–Maclaurin tails of `B_M`, `B_N` are the
aliasing of the atoms. So the windowed aperture modes are exactly the exponential box tests at
aperture `κ` plus aliasing: the atomic realization of the theta apertures inside the window.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri Zeta23

/-- The **windowed aperture mode** `n^{κ−1} 1_{M < n}`. -/
def windowedApertureCoeff (κ : ℝ) (M n : ℕ) : ℝ := if M < n then apertureModeCoeff κ n else 0

/-- The window sum `Σ_{M<n≤N} n^{-s}`. -/
def windowSum (M N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Ioc M N, (n : ℂ) ^ (-s)

theorem windowSum_eq_sub {M N : ℕ} (hMN : M ≤ N) (s : ℂ) :
    windowSum M N s = RHTower.dirichletPoly N s - RHTower.dirichletPoly M s := by
  unfold windowSum RHTower.dirichletPoly
  have hsplit : Icc 1 N = Icc 1 M ∪ Ioc M N := by
    ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 M) (Ioc M N) := by
    rw [disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj]
  ring

/-- **At a zero `ζ` cancels between the horizons**: `Σ_{M<n≤N} n^{-s} = B_M(s) − B_N(s)`. -/
theorem windowSum_eq_horizonBoundary_sub {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    windowSum M N s = horizonBoundary M s - horizonBoundary N s := by
  rw [windowSum_eq_sub hMN, dirichletPoly_eq_riemannZeta_sub_horizonBoundary (hM.trans hMN) hs hs1,
    dirichletPoly_eq_riemannZeta_sub_horizonBoundary hM hs hs1]
  ring

/-- The Dirichlet factor of the windowed mode at the spectral point of `ρ`. -/
theorem dirichletPoly_windowed_gammaOf (κ : ℝ) {M N : ℕ} (hMN : M ≤ N) (ρ : ℂ) :
    dirichletPoly N (windowedApertureCoeff κ M) (gammaOf ρ) =
      windowSum M N (1 - ρ + ((1 / 2 - κ : ℝ) : ℂ)) := by
  rw [dirichletPoly_gammaOf, windowSum]
  have hsplit : Icc 1 N = Icc 1 M ∪ Ioc M N := by
    ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 M) (Ioc M N) := by
    rw [disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj]
  have hlow : ∑ n ∈ Icc 1 M, ((windowedApertureCoeff κ M n : ℝ) : ℂ) *
      Complex.exp ((ρ - 1 / 2) * (Real.log n : ℂ)) = 0 := by
    refine sum_eq_zero fun n hn => ?_
    have : ¬ M < n := by simp only [mem_Icc] at hn; omega
    simp [windowedApertureCoeff, this]
  rw [hlow, zero_add]
  refine sum_congr rfl fun n hn => ?_
  obtain ⟨hMn, -⟩ := mem_Ioc.mp hn
  have hn1 : 1 ≤ n := by omega
  rw [windowedApertureCoeff, if_pos hMn, apertureModeCoeff_eq_exp κ hn1, ← Complex.exp_add,
    natCast_cpow_neg_eq_exp hn1]
  congr 1
  push_cast
  ring

/-- The conjugate Dirichlet factor of the windowed mode is the window sum at `ρ + a`. -/
theorem conj_dirichletPoly_windowed_conj_gammaOf (κ : ℝ) {M N : ℕ} (hMN : M ≤ N) (ρ : ℂ) :
    conj (dirichletPoly N (windowedApertureCoeff κ M) (conj (gammaOf ρ))) =
      windowSum M N (ρ + ((1 / 2 - κ : ℝ) : ℂ)) := by
  rw [conj_gammaOf, dirichletPoly_windowed_gammaOf κ hMN, sub_sub_cancel, windowSum, windowSum,
    map_sum]
  refine sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
  rw [natCast_cpow_neg_eq_exp hn1, natCast_cpow_neg_eq_exp hn1, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, map_add, Complex.conj_conj, Complex.conj_ofReal]

/-- **Horizon law of the windowed aperture mode.** At every nontrivial zero with `0 ≤ a`, the
zero-side summand is the bump factor times the two differences of horizon boundaries. -/
theorem Wsummand_windowedApertureMode {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {κ : ℝ} (hκ : κ ≤ 1 / 2) {M N : ℕ} (hM : 1 ≤ M)
    (hMN : M ≤ N) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    zetaZeroConfig.Wsummand (cx (atomicTest N (windowedApertureCoeff κ M) g))
        (cx (atomicTest N (windowedApertureCoeff κ M) g)) ρ =
      (zetaZeroConfig.mult ρ : ℂ) *
          (paperFT (cx g) (gammaOf ρ) * conj (paperFT (cx g) (conj (gammaOf ρ)))) *
        ((horizonBoundary M (1 - ρ + ((1 / 2 - κ : ℝ) : ℂ)) -
            horizonBoundary N (1 - ρ + ((1 / 2 - κ : ℝ) : ℂ))) *
          (horizonBoundary M (ρ + ((1 / 2 - κ : ℝ) : ℂ)) -
            horizonBoundary N (ρ + ((1 / 2 - κ : ℝ) : ℂ)))) := by
  have ha : (0 : ℝ) ≤ 1 / 2 - κ := by linarith
  have him := im_ne_zero_of_isNontrivialZero hρ
  have hre1 : 0 < (1 - ρ + ((1 / 2 - κ : ℝ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith [hρ.2.2]
  have hre2 : 0 < (ρ + ((1 / 2 - κ : ℝ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith [hρ.2.1]
  have hne1 : 1 - ρ + ((1 / 2 - κ : ℝ) : ℂ) ≠ 1 := by
    intro h; apply him
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im] at this
    linarith
  have hne2 : ρ + ((1 / 2 - κ : ℝ) : ℂ) ≠ 1 := by
    intro h; apply him
    have := congrArg Complex.im h
    simpa using this
  rw [Wsummand_atomicTest zetaZeroConfig hg hgc, dirichletPoly_windowed_gammaOf κ hMN,
    conj_dirichletPoly_windowed_conj_gammaOf κ hMN,
    windowSum_eq_horizonBoundary_sub hM hMN hre1 hne1,
    windowSum_eq_horizonBoundary_sub hM hMN hre2 hne2]

/-- **Windowed aperture modes on the zero side.** For every C² compact atom, every window
`1 ≤ M ≤ N` and every aperture `κ ≤ 1/2`, Weil's form is the zero sum of the bump factor against
the products of horizon-boundary differences; `ζ` does not appear. -/
theorem weilQuad_windowedApertureMode_eq_tsum {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {w : ℝ}
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {κ : ℝ} (hκ : κ ≤ 1 / 2) {M N : ℕ} (hM : 1 ≤ M)
    (hMN : M ≤ N) :
    weilQuad (atomicTest N (windowedApertureCoeff κ M) g) =
      (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
          (paperFT (cx g) (gammaOf ρ) * conj (paperFT (cx g) (conj (gammaOf ρ)))) *
        ((horizonBoundary M (1 - ρ + ((1 / 2 - κ : ℝ) : ℂ)) -
            horizonBoundary N (1 - ρ + ((1 / 2 - κ : ℝ) : ℂ))) *
          (horizonBoundary M (ρ + ((1 / 2 - κ : ℝ) : ℂ)) -
            horizonBoundary N (ρ + ((1 / 2 - κ : ℝ) : ℂ))))).re := by
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc fun u hu => hgsupp u hu
  rw [LogCells.weilQuad_eq_zetaW (contDiff_atomicTest hg N (windowedApertureCoeff κ M))
    (hasCompactSupport_atomicTest hgsupp N (windowedApertureCoeff κ M)), ZeroConfig.W]
  congr 1
  exact tsum_congr fun ρ =>
    Wsummand_windowedApertureMode hg.continuous hgc hκ hM hMN ρ.property

/-! ### The pole parts are Weil's exponential box test -/

/-- **The window charge.** With `a = 1/2 − κ` and `z = s − 1/2`, the pole parts of the two horizon
differences multiply to the zero-side summand of the exponential box test on `[log M, log N]`. -/
theorem windowPole_mul_eq (M N : ℕ) (κ : ℝ) (s : ℂ) :
    (RHTower.emPole M (s + ((1 / 2 - κ : ℝ) : ℂ)) - RHTower.emPole N (s + ((1 / 2 - κ : ℝ) : ℂ))) *
        (RHTower.emPole M (1 - s + ((1 / 2 - κ : ℝ) : ℂ)) -
          RHTower.emPole N (1 - s + ((1 / 2 - κ : ℝ) : ℂ))) =
      ((N : ℂ) ^ ((κ : ℂ) - (s - 1 / 2)) * (N : ℂ) ^ ((κ : ℂ) + (s - 1 / 2)) +
          (M : ℂ) ^ ((κ : ℂ) - (s - 1 / 2)) * (M : ℂ) ^ ((κ : ℂ) + (s - 1 / 2)) -
          (N : ℂ) ^ ((κ : ℂ) - (s - 1 / 2)) * (M : ℂ) ^ ((κ : ℂ) + (s - 1 / 2)) -
          (M : ℂ) ^ ((κ : ℂ) - (s - 1 / 2)) * (N : ℂ) ^ ((κ : ℂ) + (s - 1 / 2))) /
        (κ ^ 2 - (s - 1 / 2) ^ 2) := by
  by_cases hdeg : (κ : ℂ) ^ 2 - (s - 1 / 2) ^ 2 = 0
  · -- both sides vanish: one of the two pole denominators is zero
    have hfac : ((s - 1 / 2) - κ) * (-(s - 1 / 2) - κ) = 0 := by linear_combination hdeg
    rw [hdeg, div_zero]
    rcases mul_eq_zero.mp hfac with h | h
    · have h0 : s + ((1 / 2 - κ : ℝ) : ℂ) - 1 = 0 := by push_cast; linear_combination h
      simp only [RHTower.emPole, h0, div_zero, sub_self, zero_mul]
    · have h0 : 1 - s + ((1 / 2 - κ : ℝ) : ℂ) - 1 = 0 := by push_cast; linear_combination h
      simp only [RHTower.emPole, h0, div_zero, sub_self, mul_zero]
  have e1 : ∀ K : ℕ, (K : ℂ) ^ (1 - (s + ((1 / 2 - κ : ℝ) : ℂ))) =
      (K : ℂ) ^ ((κ : ℂ) - (s - 1 / 2)) := fun K => by congr 1; push_cast; ring
  have e2 : ∀ K : ℕ, (K : ℂ) ^ (1 - (1 - s + ((1 / 2 - κ : ℝ) : ℂ))) =
      (K : ℂ) ^ ((κ : ℂ) + (s - 1 / 2)) := fun K => by congr 1; push_cast; ring
  have hd1 : s + ((1 / 2 - κ : ℝ) : ℂ) - 1 = (s - 1 / 2) - κ := by push_cast; ring
  have hd2 : 1 - s + ((1 / 2 - κ : ℝ) : ℂ) - 1 = -(s - 1 / 2) - κ := by push_cast; ring
  have h3 : (κ : ℂ) ^ 2 - (s - 1 / 2) ^ 2 = ((s - 1 / 2) - κ) * (-(s - 1 / 2) - κ) := by ring
  have h1 : (s - 1 / 2) - (κ : ℂ) ≠ 0 := fun h => hdeg (by rw [h3, h, zero_mul])
  have h2 : -(s - 1 / 2) - (κ : ℂ) ≠ 0 := fun h => hdeg (by rw [h3, h, mul_zero])
  unfold RHTower.emPole
  rw [e1, e1, e2, e2, hd1, hd2, h3]
  field_simp
  ring

/-- **Moduli of the window charge.** A cross term `N^{κ−z} M^{κ+z}` has modulus
`N^{κ − Re z} M^{κ + Re z}`, while a diagonal term `N^{κ−z} N^{κ+z}` has modulus `N^{2κ}`: the
real part of the zero enters only the cross terms, through the window ratio `N/M`. -/
theorem norm_windowCross_eq {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) (κ : ℝ) (z : ℂ) :
    ‖(N : ℂ) ^ ((κ : ℂ) - z) * (M : ℂ) ^ ((κ : ℂ) + z)‖ =
      (N : ℝ) ^ (κ - z.re) * (M : ℝ) ^ (κ + z.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega),
    Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem norm_windowDiag_eq {N : ℕ} (hN : 1 ≤ N) (κ : ℝ) (z : ℂ) :
    ‖(N : ℂ) ^ ((κ : ℂ) - z) * (N : ℂ) ^ ((κ : ℂ) + z)‖ = (N : ℝ) ^ (2 * κ) := by
  rw [norm_windowCross_eq hN hN, ← Real.rpow_add (by exact_mod_cast hN)]
  congr 1
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
