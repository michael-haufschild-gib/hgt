import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheAtomicFamilyIsADirichletPolynomial
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer
import GaloisForLFunctions.RHTower.EMCarrier

/-!
# The zeros meet the pole mode only at the horizon

The pole mode of the complete Weil matrix has atomic coefficients `y_n = n^{-1/2}` on
`1 ≤ n ≤ N`. On the zero side its two Dirichlet factors are the partial sums
`X_N(s) = Σ_{n≤N} n^{-s}` at `1 − ρ` and at `ρ` (`dirichletPoly_poleMode_gammaOf`,
`conj_dirichletPoly_poleMode_conj_gammaOf`). The Euler–Maclaurin identity
`X_N(s) = ζ(s) − B_N(s)`, with the horizon boundary
`B_N(s) = N^{1−s}/(s−1) − s·emTail N s`, holds on `Re s > 0` (`RHTower.zeta_eq_emCarrier_sub`).
Since `ρ` and `1 − ρ` are both zeros, the Dirichlet factors are exactly `−B_N`:

* **Horizon law** (`weilQuad_poleMode_eq_tsum`): for every profile, every width and every
  horizon, `Q(f_pole) = Re Σ_ρ m_ρ ĝ(γ_ρ) conj ĝ(conj γ_ρ) · B_N(1−ρ) B_N(ρ)`.
  The zeros see the pole mode through the boundary of its horizon and through nothing else.
* **The Li charge** (`emPole_mul_emPole_one_sub`, `horizonBoundary_mul_one_sub`): the pole
  parts multiply to `N/(ρ(1−ρ))` exactly, so the boundary product is
  `N/(ρ(1−ρ))` plus terms carrying the Euler–Maclaurin tail, whose Fourier expansion is the
  Poisson dual of the successor shells.

No overlap condition enters: the identity holds at every overlap ratio `c = Nw`.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri Zeta23

/-- The **horizon boundary** `B_N(s) = N^{1−s}/(s−1) − s·emTail N s` of the partial zeta sum. -/
def horizonBoundary (N : ℕ) (s : ℂ) : ℂ := RHTower.emPole N s - s * RHTower.emTail N s

/-- `Σ_{n≤N} n^{-s} = ζ(s) − B_N(s)` on `Re s > 0`, `s ≠ 1`. -/
theorem dirichletPoly_eq_riemannZeta_sub_horizonBoundary {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    RHTower.dirichletPoly N s = riemannZeta s - horizonBoundary N s := by
  rw [RHTower.zeta_eq_emCarrier_sub hN hs hs1, RHTower.emCarrier, horizonBoundary]
  ring

/-- At a zero of `ζ` in `Re s > 0` the partial sum is minus the horizon boundary. -/
theorem dirichletPoly_eq_neg_horizonBoundary {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    RHTower.dirichletPoly N s = -horizonBoundary N s := by
  rw [dirichletPoly_eq_riemannZeta_sub_horizonBoundary hN hs hs1, hz, zero_sub]

/-- **The Li charge of the horizon**: `N^{1−s}/(s−1) · N^{s}/(−s) = N/(s(1−s))`. -/
theorem emPole_mul_emPole_one_sub {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs1 : s ≠ 1) :
    RHTower.emPole N s * RHTower.emPole N (1 - s) = (N : ℂ) / (s * (1 - s)) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpow : (N : ℂ) ^ (1 - s) * (N : ℂ) ^ (1 - (1 - s)) = N := by
    rw [← cpow_add _ _ hN0, show 1 - s + (1 - (1 - s)) = (1 : ℂ) by ring, cpow_one]
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h2 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold RHTower.emPole
  rw [div_mul_div_comm, hpow]
  congr 1
  ring

/-- The boundary product splits into the Li charge, two pole–tail cross terms, and the
tail–tail term. -/
theorem horizonBoundary_mul_one_sub {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs1 : s ≠ 1) :
    horizonBoundary N s * horizonBoundary N (1 - s) =
      (N : ℂ) / (s * (1 - s)) -
        ((1 - s) * RHTower.emPole N s * RHTower.emTail N (1 - s) +
          s * RHTower.emTail N s * RHTower.emPole N (1 - s)) +
        s * (1 - s) * RHTower.emTail N s * RHTower.emTail N (1 - s) := by
  rw [← emPole_mul_emPole_one_sub hN hs1]
  unfold horizonBoundary
  ring

/-! ### The pole mode on the zero side -/

/-- The pole-mode coefficients `n^{-1/2}`. -/
def poleModeCoeff (n : ℕ) : ℝ := (Real.sqrt n)⁻¹

/-- For `n ≥ 1`, `n^{-1/2} = exp(−(1/2) log n)` as a complex number. -/
theorem poleModeCoeff_eq_exp {n : ℕ} (hn : 1 ≤ n) :
    ((poleModeCoeff n : ℝ) : ℂ) = Complex.exp (-(1 / 2) * (Real.log n : ℂ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [poleModeCoeff, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, ← Real.exp_neg,
    Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- `n^{-z} = exp(−z log n)` for `n ≥ 1`. -/
theorem natCast_cpow_neg_eq_exp {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (n : ℂ) ^ (-z) = Complex.exp (-z * (Real.log n : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]
  ring_nf

/-- At the spectral point of `ρ` the pole-mode Dirichlet factor is `X_N(1 − ρ)`. -/
theorem dirichletPoly_poleMode_gammaOf (N : ℕ) (ρ : ℂ) :
    dirichletPoly N poleModeCoeff (gammaOf ρ) = RHTower.dirichletPoly N (1 - ρ) := by
  rw [dirichletPoly_gammaOf, RHTower.dirichletPoly]
  refine sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  rw [poleModeCoeff_eq_exp hn1, ← Complex.exp_add, natCast_cpow_neg_eq_exp hn1]
  congr 1
  ring

/-- Conjugation reflects the spectral point: `conj γ_ρ = γ_{1 − conj ρ}`. -/
theorem conj_gammaOf (ρ : ℂ) : conj (gammaOf ρ) = gammaOf (1 - conj ρ) := by
  simp only [gammaOf, map_div₀, map_sub, Complex.conj_I, map_one, map_div₀, map_ofNat]
  field_simp
  ring

/-- `conj X_N(conj s) = X_N(s)`. -/
theorem conj_dirichletPoly_conj (N : ℕ) (s : ℂ) :
    conj (RHTower.dirichletPoly N (conj s)) = RHTower.dirichletPoly N s := by
  rw [RHTower.dirichletPoly, RHTower.dirichletPoly, map_sum]
  refine sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  rw [natCast_cpow_neg_eq_exp hn1, natCast_cpow_neg_eq_exp hn1, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal]

/-- The conjugate Dirichlet factor of the pole mode is `X_N(ρ)`. -/
theorem conj_dirichletPoly_poleMode_conj_gammaOf (N : ℕ) (ρ : ℂ) :
    conj (dirichletPoly N poleModeCoeff (conj (gammaOf ρ))) = RHTower.dirichletPoly N ρ := by
  rw [conj_gammaOf, dirichletPoly_poleMode_gammaOf, sub_sub_cancel, conj_dirichletPoly_conj]

/-- A nontrivial zero `ρ` and its reflection `1 − ρ` are zeros with positive real part,
different from `1`. -/
theorem nontrivialZero_facts {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ ≠ 1 ∧
      riemannZeta (1 - ρ) = 0 ∧ 0 < (1 - ρ).re ∧ 1 - ρ ≠ 1 ∧ ρ ≠ 0 := by
  obtain ⟨hz, h0, h1⟩ := hρ
  have hne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl _ h1
  have hne0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl _ h0
  have hnat : ∀ n : ℕ, ρ ≠ -n := fun n h => by
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  refine ⟨hz, h0, hne1, ?_, ?_, ?_, hne0⟩
  · rw [riemannZeta_one_sub hnat hne1, hz, mul_zero]
  · simp only [Complex.sub_re, Complex.one_re]; linarith
  · intro h; exact hne0 (by linear_combination -h)

/-- **The zero-side summand of the pole mode** at a nontrivial zero: bump factor times the
product of the two horizon boundaries. -/
theorem Wsummand_poleMode {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {N : ℕ} (hN : 1 ≤ N) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    zetaZeroConfig.Wsummand (cx (atomicTest N poleModeCoeff g))
        (cx (atomicTest N poleModeCoeff g)) ρ =
      (zetaZeroConfig.mult ρ : ℂ) *
          (paperFT (cx g) (gammaOf ρ) * conj (paperFT (cx g) (conj (gammaOf ρ)))) *
        (horizonBoundary N (1 - ρ) * horizonBoundary N ρ) := by
  obtain ⟨hz, h0, h1, hz', h0', h1', -⟩ := nontrivialZero_facts hρ
  rw [Wsummand_atomicTest zetaZeroConfig hg hgc, dirichletPoly_poleMode_gammaOf,
    conj_dirichletPoly_poleMode_conj_gammaOf,
    dirichletPoly_eq_neg_horizonBoundary hN h0' h1' hz',
    dirichletPoly_eq_neg_horizonBoundary hN h0 h1 hz]
  ring

/-- **Horizon law.** For every C² compact atom `g` and every horizon `N ≥ 1`, Weil's form of the
pole mode is the zero sum of the bump factor against the two horizon boundaries. -/
theorem weilQuad_poleMode_eq_tsum {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {w : ℝ}
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) :
    weilQuad (atomicTest N poleModeCoeff g) =
      (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
          (paperFT (cx g) (gammaOf ρ) * conj (paperFT (cx g) (conj (gammaOf ρ)))) *
        (horizonBoundary N (1 - ρ) * horizonBoundary N ρ)).re := by
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc fun u hu => hgsupp u hu
  rw [LogCells.weilQuad_eq_zetaW (contDiff_atomicTest hg N poleModeCoeff)
    (hasCompactSupport_atomicTest hgsupp N poleModeCoeff), ZeroConfig.W]
  congr 1
  refine tsum_congr fun ρ => ?_
  exact Wsummand_poleMode hg.continuous hgc hN ρ.property

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
