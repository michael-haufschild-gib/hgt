import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration
import GaloisForLFunctions.ZeroConfigurationGeometry.SymmetricShiftsPreserveTheAsymptoticAbscissaLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.BeurlingOneOffZeroCountermodelsAndDefectTradeoff
import GaloisForLFunctions.ArithmeticPositiveDuality.TheRationalPrimeOneOffHasMultiplicativeCounting

/-!
# The critical-line firewall

The asymptotic abscissa law for a function `F` on a half-plane `Re s > σ₀`
(`HalfPlaneAbscissaLaw`): for every `σ ≥ σ₀`, finitely many zeros (away from the pole `s = 1`)
right of `σ` means none. For `ζ` at `σ₀ = ½` it is `AsymptoticAbscissaLaw`
(`asymptoticAbscissaLaw_iff_halfPlaneAbscissaLaw_zeta`).

**Theorem** (`criticalLineFirewall`). The law fails, with a finite nonempty top layer, for

1. a continuous Beurling system with nonnegative prime and integer densities and integer count
   `N(x) − ρx − C → 0` (the zeta function is rational and continues across `Re s = ½`);
2. an Euler product over integer norms `≥ 2` with natural coefficients and linear counting,
   holomorphic on `Re s > ½`;
3. an Euler product over rational primes with multiplicative natural coefficients and linear
   counting, holomorphic on `Re s > 17/30`;
4. the zero set of any one reflection pair `{ρ, 1 − ρ̄}`: the reflection symmetry of a zero set,
   which is all the functional equation says about the zeros, does not give the law;

and the law of `ζ` is invariant under every symmetric shift `ξ(s + a)ξ(s − a)`, which keeps the
functional equation and moves every abscissa by `a`.

So positivity, Euler products over integer norms or rational primes, linear counting, continuation
across the line and the reflection symmetry of the zero set each fail to give the law, and no input
can use the position `½` of the line. The reflection `ρ ↦ 1 − ρ̄` keeps heights, while the law is
vertical transport (`ConfigAbscissa.abscissaLaw_iff_transport`): an input that uses the functional
equation must turn it into transport of zeros in height.
-/

open Complex Set Filter Topology
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.CriticalLineFirewall

open ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa

/-- **AAL on a half-plane** for a function `F` with its pole at `1` excluded: for every `σ ≥ σ₀`,
finitely many zeros right of `σ` means none. -/
def HalfPlaneAbscissaLaw (F : ℂ → ℂ) (σ₀ : ℝ) : Prop :=
  ∀ σ : ℝ, σ₀ ≤ σ → {s : ℂ | σ < s.re ∧ s ≠ 1 ∧ F s = 0}.Finite →
    ∀ s : ℂ, σ < s.re → s ≠ 1 → F s ≠ 0

/-- A finite nonempty zero set right of `σ₀` violates the law at `σ₀`. -/
theorem not_halfPlaneAbscissaLaw_of_finite_nonempty {F : ℂ → ℂ} {σ₀ : ℝ}
    (hfin : {s : ℂ | σ₀ < s.re ∧ s ≠ 1 ∧ F s = 0}.Finite)
    (hne : {s : ℂ | σ₀ < s.re ∧ s ≠ 1 ∧ F s = 0}.Nonempty) : ¬ HalfPlaneAbscissaLaw F σ₀ :=
  fun hA => by
    obtain ⟨s, hs, hs1, hF⟩ := hne
    exact hA σ₀ le_rfl hfin s hs hs1 hF

/-- Right of `½` the zeros of `ζ` are the points of its configuration. -/
theorem zeta_zeroSet_eq_rightOf {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    {s : ℂ | σ < s.re ∧ s ≠ 1 ∧ riemannZeta s = 0} = rightOf zetaZeroConfig (σ - 1 / 2) := by
  ext s
  simp only [mem_setOf_eq, rightOf, zetaZeroConfig_carrier, IsNontrivialZero]
  constructor
  · rintro ⟨hs, -, hz⟩
    have h1 : s.re < 1 := not_le.mp fun h => riemannZeta_ne_zero_of_one_le_re h hz
    exact ⟨⟨hz, by linarith, h1⟩, by linarith⟩
  · rintro ⟨⟨hz, -, h1⟩, hs⟩
    refine ⟨by linarith, fun h => ?_, hz⟩
    rw [h, one_re] at h1
    exact lt_irrefl _ h1

/-- **The law of `ζ` on `Re s > ½` is `AsymptoticAbscissaLaw`.** -/
theorem asymptoticAbscissaLaw_iff_halfPlaneAbscissaLaw_zeta :
    _root_.RHTower.AsymptoticAbscissaLaw ↔ HalfPlaneAbscissaLaw riemannZeta (1 / 2) := by
  rw [← ZetaAbscissa.zetaZeroConfig_abscissaLaw_iff]
  constructor
  · intro hA σ hσ hfin s hs hs1 hz
    rw [zeta_zeroSet_eq_rightOf hσ] at hfin
    have hmem : s ∈ rightOf zetaZeroConfig (σ - 1 / 2) := by
      rw [← zeta_zeroSet_eq_rightOf hσ]; exact ⟨hs, hs1, hz⟩
    have := hA (σ - 1 / 2) (by linarith) hfin s hmem.1
    linarith [hmem.2]
  · intro hA h hh hfin ρ hρ
    by_contra hlt
    push Not at hlt
    have hσ : (1 : ℝ) / 2 ≤ 1 / 2 + h := by linarith
    have hfin' : {s : ℂ | 1 / 2 + h < s.re ∧ s ≠ 1 ∧ riemannZeta s = 0}.Finite := by
      rw [zeta_zeroSet_eq_rightOf hσ, show 1 / 2 + h - 1 / 2 = h by ring]; exact hfin
    have hρ' : ρ ∈ {s : ℂ | 1 / 2 + h < s.re ∧ s ≠ 1 ∧ riemannZeta s = 0} := by
      rw [zeta_zeroSet_eq_rightOf hσ, show 1 / 2 + h - 1 / 2 = h by ring]; exact ⟨hρ, hlt⟩
    exact hA _ hσ hfin' ρ hρ'.1 hρ'.2.1 hρ'.2.2

/-- The pair `{3/5 + iγ, 3/5 − iγ}` is finite and nonempty. -/
theorem pair_finite_nonempty (γ : ℝ) :
    ({(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} : Set ℂ).Finite ∧
      ({(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} : Set ℂ).Nonempty :=
  ⟨(finite_singleton _).insert _, insert_nonempty _ _⟩

open RHTower.BeurlingOverRegularIntegers in
/-- **The critical-line firewall.** Each input class below carries a finite nonempty top layer, and
the law of `ζ` does not see the position of the line. -/
theorem criticalLineFirewall :
    -- continuous positive systems with count error `→ 0`, continued across the line
    (∀ μ ν γ : ℝ, 1 / 3 < μ → μ < 1 / 2 → 0 < ν → ν < 3 * μ - 1 →
      (∀ t : ℝ, 0 < t → 0 ≤ primeDensity μ ν γ t) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ integerDensity μ ν γ t) ∧
      (∀ s : ℂ, 1 < s.re → cexp (∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (primeDensity μ ν γ t : ℂ)) =
        overRegularZeta μ ν γ s) ∧
      Tendsto (fun x : ℝ => countLog μ ν γ (Real.log x) - rho μ ν γ * x - countConst μ ν γ) atTop
        (𝓝 0) ∧
      ¬ HalfPlaneAbscissaLaw (overRegularZeta μ ν γ) (1 / 2)) ∧
    -- integer norms, natural coefficients, linear counting
    (∀ γ : ℝ, ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} ∧
      ¬ HalfPlaneAbscissaLaw F (1 / 2)) ∧
    -- rational primes, multiplicative natural coefficients, linear counting
    (∀ γ : ℝ, ∃ q a : ℕ → ℕ, (∀ k, (q k).Prime) ∧ a 1 = 1 ∧
      (∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 17 / 30 < s.re ∧ s ≠ 1} ∧
      ¬ HalfPlaneAbscissaLaw F (17 / 30)) ∧
    -- the reflection symmetry of a zero set
    (∀ ρ : ℂ, ∀ h12 : 1 / 2 < ρ.re, ∀ h1 : ρ.re ≤ 1,
      ApproachesLine (pairConfig ρ (by linarith) h1) ∧
        ¬ AbscissaLawAt (pairConfig ρ (by linarith) h1) 0) ∧
    -- the law does not see the position of the line
    (∀ a : ℝ, 0 ≤ a → (_root_.RHTower.AsymptoticAbscissaLaw ↔ ∀ σ : ℝ,
      (∃ T : ℝ, 0 < T ∧ ∀ z : ℂ,
        _root_.RHTower.symmetricShiftProduct _root_.RHTower.xi a z = 0 → T ≤ |z.im| → z.re ≤ σ) →
          ∀ z : ℂ, _root_.RHTower.symmetricShiftProduct _root_.RHTower.xi a z = 0 → z.re ≤ σ)) := by
  refine ⟨fun μ ν γ hμ1 hμ2 hν0 hν1 => ?_, fun γ => ?_, fun γ => ?_,
    fun ρ h12 h1 => pairConfig_not_abscissaLaw h12 h1,
    fun a ha => asymptoticAbscissaLaw_iff_symmetricShift_eventualToGlobal ha⟩
  · have hμ0 : 0 ≤ μ := by linarith
    refine ⟨fun t ht => primeDensity_nonneg hμ0 ht,
      fun t ht => integerDensity_nonneg hμ0 hν0 (by linarith) ht,
      fun s hs => cexp_integral_primeDensity (by linarith) (by linarith) (by linarith) hs,
      tendsto_count_sub (by linarith) (by linarith), ?_⟩
    have hset := ArithmeticPositiveDuality.overRegularZeta_right_zeroSet_eq_pair (γ := γ) hν0 hν1
      (h := 0) le_rfl (by linarith)
    rw [add_zero] at hset
    refine not_halfPlaneAbscissaLaw_of_finite_nonempty ?_ ?_ <;> rw [hset]
    · exact (finite_singleton _).insert _
    · exact insert_nonempty _ _
  · obtain ⟨q, a, hq, F, A, hA, hprod, hcount, hdiff, hzero⟩ :=
      IntegerNormOneOff.exists_integer_norm_linear_count_one_off γ
    refine ⟨q, a, hq, F, A, hA, hprod, hcount, hdiff, ?_⟩
    have hset : {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} =
        {(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} := hzero
    exact not_halfPlaneAbscissaLaw_of_finite_nonempty (by rw [hset]; exact (pair_finite_nonempty γ).1)
      (by rw [hset]; exact (pair_finite_nonempty γ).2)
  · obtain ⟨q, a, hq, -, ha1, hmul, F, A, hA, hprod, hcount, hdiff, hzero⟩ :=
      RationalPrimeOneOff.exists_rational_prime_multiplicative_linear_count_one_off γ
    refine ⟨q, a, hq, ha1, hmul, F, A, hA, hprod, hcount, hdiff, ?_⟩
    have hset : {s : ℂ | 17 / 30 < s.re ∧ s ≠ 1 ∧ F s = 0} =
        {(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} := hzero
    exact not_halfPlaneAbscissaLaw_of_finite_nonempty (by rw [hset]; exact (pair_finite_nonempty γ).1)
      (by rw [hset]; exact (pair_finite_nonempty γ).2)

end GaloisForLFunctions.ArithmeticPositiveDuality.CriticalLineFirewall
