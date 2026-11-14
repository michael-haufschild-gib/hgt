import GaloisForLFunctions.RingdownOfTheCubicCover.TheWeightHalfThreeTermCalibration
import GaloisForLFunctions.RHTower.HalfWeightThetaMultiplier
import GaloisForLFunctions.RHTower.HalfWeightThetaExceptionalEigenvalue
import GaloisForLFunctions.FamilyContinuationTheory.TheOddPowerOfAGaussSumCarriesTheMoebiusSign
import GaloisForLFunctions.MetaplecticMobiusDescent.CubingTheCompositeGaussSumRecoversMobius
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicResidueIsNonzero
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesHasADoublePole

/-!
# Metaplectic Cusp Reciprocity and Rational Descent Separate Weight `½` from the Cubic Cover

This module isolates and proves unconditionally the exact horizon input that fails on the `n = 2`
metaplectic double cover (weight `½` on `Γ₀(4) ≤ SL₂(ℤ)`) and holds on the `n = 3` cubic cover
of the Bianchi horizon `SL₂(ℤ[ω])\ℍ³`:

1. **Rational modular descent (`SL₂(ℤ)` triviality vs `Γ₀(4)` multiplier twist)**:
   - On `n = 2`, at `U = [[1, 0], [4, 1]] ∈ Γ₀(4) ≤ SL₂(ℤ)`, the quadratic Gauss sum is
     `G(-1; 4) = 2(1 - i)`, forcing `J(U, z)² = 4z + 1` on `ℍ` (in particular `J(U, i)² = 1 + 4i`)
     and `(j_ϑ(U, z))² ≠ 1` at every `z ∈ ℍ`. Thus `j_ϑ` is non-trivial on `Γ₀(4)`, isolating the
     exceptional weight-`½` eigenfunction `y^{1/4} θ` (`λ = 3/16 < 1/4`) from untwisted `SL₂(ℤ)`
     Eisenstein scattering.
   - On `n = 3`, the extended cubic Kubota character `κ₃` on `rationalExtension ≤ SL₂(ℤ[ω])` takes
     values in `μ₃`, normalizes `globalKubotaKernel`, and restricts identically to `1` on all of
     `SL₂(ℤ)` (`extendedComplexCharacter_rational`).

2. **Gauss-sum Möbius sign law (`n` even vs `n` odd)**:
   - On `n = 2`, the constant-term Dirichlet convolution `fN 0 = phiSq` vanishes at every prime
     modulus (`phiSq p = 0`) and is non-negative everywhere; more generally, for any even character
     order `n > 2`, `g(χ)^n ≡ χ(-1) · #F (mod (μ - 1)²)` carries character parity rather than `-1`.
   - On `n = 3` (and every odd character order `n > 2`), `g(χ)^n ≡ -#F (mod (μ - 1)²)` carries the
     universal `-1` prime Möbius sign, and cubing the normalized composite cubic Gauss sum on
     `ℤ[ω]` recovers the exact ideal Möbius function `μ(∏ P_i)` (`normalizedCompositeCubicGauss_cube`).

3. **Residual eigenfunction and simple-pole vs double-pole dichotomy**:
   - The cubic Eisenstein series on `globalKubotaKernel\ℍ³` has a non-zero `L²` simple-pole residue
     `Θ₃ = cubicEisensteinResidue` at `s = 4/3` with `Δ_{ℍ³} Θ₃ = (8/9) Θ₃` (`8/9 < 1`) and
     untwisted `SL₂(ℤ)` cusp symmetry.
   - By contrast, squaring the projected theta series (`thetaSqDirichlet_double_pole`) produces a
     double pole `(s - 4/3)² Λ(s) → 108 π³ r³ ≠ 0` from the rational cusp scattering subtraction,
     destroying rank-one simple-pole residue factorization.
-/

noncomputable section

open Complex Filter MeasureTheory Set ModularGroup
open scoped BigOperators Classical MatrixGroups Topology UpperHalfPlane

namespace GaloisForLFunctions.RingdownOfTheCubicCover

open MetaplecticMobiusDescent
open MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicKubota
open MetaplecticMobiusDescent.CubicEisenstein
open MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ## Pillar I: Rational Modular Descent Fails on `n = 2` and Holds on `n = 3` -/

private theorem cpow_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  by_cases hw : w = 0
  · subst hw; simp
  · rw [Complex.cpow_def_of_ne_zero hw, sq, ← Complex.exp_add]
    have hlog : Complex.log w * (1 / 2 : ℂ) + Complex.log w * (1 / 2 : ℂ) = Complex.log w := by
      ring
    rw [hlog, Complex.exp_log hw]

/-- The generator `U = [[1, 0], [4, 1]]` belongs to `Γ₀(4)`. -/
theorem U_mem_Gamma0_four : RHTower.HalfWeight.U ∈ CongruenceSubgroup.Gamma0 4 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  have h4 : (4 : ℤ) ∣ RHTower.HalfWeight.ent RHTower.HalfWeight.U 1 0 := by
    simp [RHTower.HalfWeight.ent, RHTower.HalfWeight.coe_U]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h4

/-- Exact evaluation of the modulus-`4` quadratic Gauss sum: `G(-1; 4) = 2(1 - i)`. -/
theorem gaussQ_neg_one_four : RHTower.HalfWeight.gaussQ (-1) 4 = 2 * (1 - I) := by
  unfold RHTower.HalfWeight.gaussQ
  rw [Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
    show ((3 : Fin 4) : ℕ) = 3 from rfl, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  have h0 : (2 * (Real.pi : ℂ) * I * ((-1 : ℤ) * (0 : ℂ) ^ 2 / (4 : ℂ))) = 0 := by ring
  have h1 : (2 * (Real.pi : ℂ) * I * ((-1 : ℤ) * (1 : ℂ) ^ 2 / (4 : ℂ))) =
      ((-(Real.pi / 2) : ℝ) : ℂ) * I := by push_cast; ring
  have h2 : (2 * (Real.pi : ℂ) * I * ((-1 : ℤ) * (2 : ℂ) ^ 2 / (4 : ℂ))) =
      ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by push_cast; ring
  have h3 : (2 * (Real.pi : ℂ) * I * ((-1 : ℤ) * (3 : ℂ) ^ 2 / (4 : ℂ))) =
      ((-(Real.pi / 2) : ℝ) : ℂ) * I + ((-2 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    push_cast; ring
  have hexp1 : cexp (((-(Real.pi / 2) : ℝ) : ℂ) * I) = -I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  rw [h0, h1, h2, h3, Complex.exp_zero, Complex.exp_add, hexp1,
    Complex.exp_int_mul_two_pi_mul_I (-1), Complex.exp_int_mul_two_pi_mul_I (-2)]
  ring

/-- On all of `ℍ`, the weight-`½` automorphy factor at `U = [[1, 0], [4, 1]]` satisfies
`J(U, z)² = 4z + 1`. -/
theorem weight_half_J_U_sq (z : ℍ) :
    (RHTower.HalfWeight.J RHTower.HalfWeight.U z) ^ 2 = 4 * (z : ℂ) + 1 := by
  have hcU : RHTower.HalfWeight.ent RHTower.HalfWeight.U 1 0 = (4 : ℕ) := by
    simp [RHTower.HalfWeight.ent, RHTower.HalfWeight.coe_U]
  have hdU : RHTower.HalfWeight.ent RHTower.HalfWeight.U 1 1 = 1 := by
    simp [RHTower.HalfWeight.ent, RHTower.HalfWeight.coe_U]
  have h := RHTower.HalfWeight.J_mul_gauss U_mem_Gamma0_four hcU z
  rw [hdU] at h
  have hsq := congrArg (· ^ 2) h
  simp only [mul_pow, cpow_half_sq, gaussQ_neg_one_four, Nat.cast_ofNat, Int.cast_one] at hsq
  have hsqrt2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have h32L : 2 ^ 2 * (1 - I) ^ 2 * (I * (4 : ℂ)) = 32 := by
    linear_combination (16 * I - 32) * Complex.I_sq
  rw [h32L, hsqrt2] at hsq
  linear_combination hsq / 32

/-- Specialization at `z = i`: `J(U, i)² = 1 + 4i`. -/
theorem weight_half_J_U_sq_at_I :
    (RHTower.HalfWeight.J RHTower.HalfWeight.U UpperHalfPlane.I) ^ 2 = 1 + 4 * I := by
  rw [weight_half_J_U_sq UpperHalfPlane.I, UpperHalfPlane.coe_I]
  ring

/-- At every point `z ∈ ℍ`, the unitary weight-`½` theta multiplier `j_ϑ(U, z)` satisfies
`j_ϑ(U, z)² ≠ 1`. -/
theorem weight_half_jU_U_sq_ne_one (z : ℍ) :
    (RHTower.HalfWeight.jU RHTower.HalfWeight.U z) ^ 2 ≠ 1 := by
  intro h1
  have hJ0 : (‖RHTower.HalfWeight.J RHTower.HalfWeight.U z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (RHTower.HalfWeight.norm_J_pos RHTower.HalfWeight.U z).ne'
  have hdiv : (RHTower.HalfWeight.J RHTower.HalfWeight.U z) ^ 2 /
      (‖RHTower.HalfWeight.J RHTower.HalfWeight.U z‖ : ℂ) ^ 2 = 1 := by
    simpa [RHTower.HalfWeight.jU, div_pow] using h1
  have heq : (RHTower.HalfWeight.J RHTower.HalfWeight.U z) ^ 2 =
      ((‖RHTower.HalfWeight.J RHTower.HalfWeight.U z‖ ^ 2 : ℝ) : ℂ) := by
    rw [div_eq_iff (pow_ne_zero 2 hJ0), one_mul] at hdiv
    simpa using hdiv
  rw [weight_half_J_U_sq z] at heq
  have him := congrArg Complex.im heq
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.one_im,
    UpperHalfPlane.coe_im, add_zero] at him
  have hre4 : (4 : ℂ).re = 4 := by norm_num
  have him4 : (4 : ℂ).im = 0 := by norm_num
  rw [hre4, him4] at him
  linarith [z.im_pos]

/-- At every `z ∈ ℍ`, the unitary weight-`½` multiplier `j_ϑ(U, z)` is neither `1` nor `-1`. -/
theorem weight_half_jU_U_ne_one (z : ℍ) :
    RHTower.HalfWeight.jU RHTower.HalfWeight.U z ≠ 1 := by
  intro h
  exact weight_half_jU_U_sq_ne_one z (by rw [h, one_pow])

/-- The weight-`½` multiplier `j_ϑ` fails to trivialize on `Γ₀(4) ≤ SL₂(ℤ)`. -/
theorem weight_half_jU_nontrivial_on_Gamma0_four :
    ∃ γ ∈ CongruenceSubgroup.Gamma0 4,
      ∀ z : ℍ, RHTower.HalfWeight.jU γ z ≠ 1 ∧ (RHTower.HalfWeight.jU γ z) ^ 2 ≠ 1 :=
  ⟨RHTower.HalfWeight.U, U_mem_Gamma0_four,
    fun z => ⟨weight_half_jU_U_ne_one z, weight_half_jU_U_sq_ne_one z⟩⟩

/-- By contrast, on the `n = 3` cubic cover of `SL₂(ℤ[ω])`, the extended Kubota character `κ₃`
is unitary of order dividing `3`, normalizes the metaplectic kernel `globalKubotaKernel`, and
restricts identically to `1` on the entire rational modular group `SL₂(ℤ)`. -/
theorem cubic_multiplier_trivial_on_SL2Z :
    (∀ r : SL(2, ℤ),
      extendedComplexCharacter ⟨rationalEmbedding r, rational_mem_rationalExtension r⟩ = 1) ∧
    (∀ g : rationalExtension,
      extendedComplexCharacter g ^ 3 = 1 ∧ ‖extendedComplexCharacter g‖ = 1) ∧
    (∀ r : SL(2, ℤ), ∀ k : SL(2, O), k ∈ globalKubotaKernel →
      rationalEmbedding r * k * (rationalEmbedding r)⁻¹ ∈ globalKubotaKernel) := by
  refine ⟨extendedComplexCharacter_rational,
    fun g => ⟨extendedComplexCharacter_cube g, norm_extendedComplexCharacter g⟩,
    fun r k hk => ?_⟩
  exact globalKubotaKernel_conjugate ⟨rationalEmbedding r, rational_mem_rationalExtension r⟩ k hk

/-! ## Pillar II: Gauss-Sum Möbius Sign Failure on `n = 2` vs Ideal Möbius Recovery on `n = 3` -/

/-- No rational prime is a square in `ℕ`. -/
theorem not_isSquare_of_prime {p : ℕ} (hp : p.Prime) : ¬ IsSquare p := by
  rintro ⟨k, rfl⟩
  rcases hp.eq_one_or_self_of_dvd k ⟨k, rfl⟩ with rfl | hk
  · exact hp.ne_one rfl
  · have hk1 : 1 < k := by nlinarith [hp.one_lt]
    nlinarith

/-- In weight `½`, the Eisenstein constant-term arithmetic `(μ * N(0)) = phiSq` vanishes at every
prime modulus `p` (`phiSq p = 0`) and is non-negative at every modulus `c`, carrying no prime
Möbius sign. -/
theorem weight_half_constant_term_vanishes_on_primes :
    RHTower.HalfWeight.fN 0 = RHTower.HalfWeight.phiSq ∧
    (∀ c : ℕ, 0 ≤ (RHTower.HalfWeight.phiSq c).re ∧ (RHTower.HalfWeight.phiSq c).im = 0) ∧
    (∀ p : ℕ, p.Prime → RHTower.HalfWeight.phiSq p = 0) := by
  refine ⟨RHTower.HalfWeight.fN_zero_eq, fun c => ?_, fun p hp => ?_⟩
  · rw [RHTower.HalfWeight.phiSq_apply]
    split_ifs <;> simp [Nat.cast_nonneg]
  · rw [RHTower.HalfWeight.phiSq_apply, if_neg (not_isSquare_of_prime hp)]

/-- Algebraic parity dichotomy across metaplectic orders `n > 2`: odd-order Gauss sums satisfy
`g(χ)^n ≡ -#F (mod (μ - 1)²)` (the prime Möbius sign `-1`), whereas even-order Gauss sums satisfy
`g(χ)^n ≡ χ(-1) · #F (mod (μ - 1)²)` (character parity). -/
theorem gaussSum_power_moebius_dichotomy
    {F R : Type*} [Field F] [Fintype F] [CommRing R] [IsDomain R]
    {χ : MulChar F R} {ψ : AddChar F R} {μ : R}
    (h2 : 2 < orderOf χ) (hψ : ψ.IsPrimitive) (hμ : IsPrimitiveRoot μ (orderOf χ)) :
    (Odd (orderOf χ) →
      ∃ z ∈ Algebra.adjoin ℤ {μ},
        gaussSum χ ψ ^ orderOf χ = -(Fintype.card F : R) + z * (μ - 1) ^ 2) ∧
    (Even (orderOf χ) →
      ∃ z ∈ Algebra.adjoin ℤ {μ},
        gaussSum χ ψ ^ orderOf χ = χ (-1) * (Fintype.card F : R) + z * (μ - 1) ^ 2) :=
  ⟨fun hodd => FamilyContinuationTheory.exists_gaussSum_pow_orderOf_eq_of_odd hodd h2 hψ hμ,
   fun heven => FamilyContinuationTheory.exists_gaussSum_pow_orderOf_eq_of_even heven h2 hψ hμ⟩

/-- On the `n = 3` cubic cover over `ℤ[ω]`, cubing the normalized composite cubic Gauss sum on a
product of distinct prime ideals away from `λ = 1 - ω` recovers the exact ideal Möbius sign
`μ(∏_i P_i)` times the unit angular generator. -/
theorem cubic_composite_gauss_recovers_ideal_moebius
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i) :
    normalizedCompositeCubicGauss P hinj hgood ^ 3 =
      (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) *
        (ringComplex (∏ i, primaryGenerator (P i) (hgood i)) /
          (‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ : ℂ)) :=
  normalizedCompositeCubicGauss_cube P hinj hgood

/-! ## Pillar III: Residual Eigenvalues (`3/16` Twisted vs `8/9` Untwisted) and Double-Pole Obstruction -/

/-- Spectral comparison of residual horizon states and the squared-theta double-pole obstruction:
- Weight `½` (`n = 2` on `ℍ²`): `y^{1/4} θ` has eigenvalue `3/16 < 1/4` under `Δ_{1/2}`, but is
  twisted by `j_ϑ` (`j_ϑ(U, z) ≠ 1`).
- Cubic cover (`n = 3` on `ℍ³`): `cubicEisensteinResidue` (`Θ₃`) is a non-zero `L²` simple-pole
  residue at `s = 4/3` with eigenvalue `(4/3)(2 - 4/3) = 8/9 < 1` under `Δ_{ℍ³}` and trivial
  `SL₂(ℤ)` multiplier (`κ₃|_{SL₂(ℤ)} = 1`).
- Squared theta (`Θ₃²`, analogous to `n = 2` squaring): the completed squared-theta Dirichlet
  series has a double pole `(s - 4/3)² Λ(s) → 108 π³ r³ ≠ 0` at `s = 4/3`. -/
theorem residual_eigenvalue_and_pole_order_comparison :
    ((3 / 4 : ℝ) * (1 - 3 / 4) = 3 / 16 ∧ (3 / 16 : ℝ) < 1 / 4) ∧
    ((4 / 3 : ℝ) * (2 - 4 / 3) = 8 / 9 ∧ (8 / 9 : ℝ) < 1) ∧
    (cubicEisensteinResidue ≠ 0 ∧
      (cubicEisensteinResidue, (8 / 9 : ℂ) • cubicEisensteinResidue) ∈
        kernelEnergyLaplacian.graph) ∧
    (∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = SpectralTheoryOfTheCubicCover.besselSqMellin s *
          SpectralTheoryOfTheCubicCover.thetaSqDirichlet s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3)) ∧
      (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 ≠ 0)) := by
  obtain ⟨Λ, hΛeq, -, hΛdiff, hΛlim, hΛne⟩ :=
    SpectralTheoryOfTheCubicCover.thetaSqDirichlet_double_pole
  exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨cubicEisensteinResidue_ne_zero, cubicEisensteinResidue_eigenvector⟩,
    ⟨Λ, hΛeq, hΛdiff, hΛlim, hΛne⟩⟩

/-! ## Master Separation Theorem Answering §2.7 & §2.12 -/

/-- **Exact Horizon Separation Theorem**:
In weight `½` (`n = 2` on `Γ₀(4)\ℍ²`), cusp finite volume, Laplacian positivity, and unitarity of
the multiplier all survive, yet `y^{1/4} θ` (`λ = 3/16 < 1/4`) and its non-coboundary holomorphic
period vector `Ψ_ϑ` (`w = 3/2`) exist because two coupled metaplectic inputs fail:
1. **Rational modular descent fails**: `j_ϑ(U, z)² ≠ 1` on `Γ₀(4) ≤ SL₂(ℤ)` (`J(U, z)² = 4z + 1`),
   whereas on the `n = 3` cubic cover `κ₃` restricts identically to `1` on `SL₂(ℤ)`.
2. **Odd-order Gauss-sum Möbius reciprocity fails**: `fN 0 = phiSq` vanishes at all primes and is
   non-negative everywhere, whereas on `n = 3` cubing the normalized composite cubic Gauss sum on
   `ℤ[ω]` recovers the ideal Möbius sign `μ(∏_i P_i)` while `Θ₃` (`s = 4/3`, `λ = 8/9 < 1`) arises
   from a simple pole (in contrast to the double pole of `Θ₃²`). -/
theorem metaplectic_horizon_input_separates_weight_half_from_cubic_cover :
    -- (1) Weight-½ exceptional Maass state and unitary-multiplier three-term period vector exist
    ((∀ z : ℍ, RHTower.HalfWeight.thetaMaass z ≠ 0) ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma0 4, ∀ z : ℍ,
        RHTower.HalfWeight.thetaMaass (γ • z) =
          RHTower.HalfWeight.jU γ z * RHTower.HalfWeight.thetaMaass z) ∧
      (∀ j : Fin 3, DifferentiableOn ℂ (fun z => thetaLewisPeriod z j) {z : ℂ | 0 < z.re}) ∧
      (¬ ∃ v : Fin 3 → ℂ, ∀ a : ℝ, 0 < a →
        thetaLewisPeriod (a : ℂ) = v - ((a : ℂ) ^ (-3 / 2 : ℂ)) • thetaUT v) ∧
      (∀ a : ℝ, 0 < a →
        thetaLewisPeriod (a : ℂ) =
          thetaUT (thetaLewisPeriod ((a + 1 : ℝ) : ℂ)) +
            (((a + 1 : ℝ) : ℂ) ^ (-3 / 2 : ℂ)) •
              thetaUTPrime (thetaLewisPeriod ((a / (a + 1) : ℝ) : ℂ)))) ∧
    -- (2) Rational modular descent fails on n = 2 (Γ₀(4)) and holds on n = 3 (SL₂(ℤ) ≤ SL₂(ℤ[ω]))
    ((∃ γ ∈ CongruenceSubgroup.Gamma0 4,
        ∀ z : ℍ, RHTower.HalfWeight.jU γ z ≠ 1 ∧ (RHTower.HalfWeight.jU γ z) ^ 2 ≠ 1) ∧
      (∀ r : SL(2, ℤ),
        extendedComplexCharacter ⟨rationalEmbedding r, rational_mem_rationalExtension r⟩ = 1)) ∧
    -- (3) Prime Möbius sign vanishes on n = 2 and is recovered on n = 3
    ((RHTower.HalfWeight.fN 0 = RHTower.HalfWeight.phiSq ∧
        ∀ p : ℕ, p.Prime → RHTower.HalfWeight.phiSq p = 0) ∧
      (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i),
        normalizedCompositeCubicGauss P hinj hgood ^ 3 =
          (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) *
            (ringComplex (∏ i, primaryGenerator (P i) (hgood i)) /
              (‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ : ℂ)))) ∧
    -- (4) Simple-pole cubic residual state Θ₃ (λ = 8/9 < 1) vs double-pole squared theta Θ₃²
    ((cubicEisensteinResidue ≠ 0 ∧
        (cubicEisensteinResidue, (8 / 9 : ℂ) • cubicEisensteinResidue) ∈
          kernelEnergyLaplacian.graph) ∧
      (∃ Λ : ℂ → ℂ,
        (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
        Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
          (𝓝 (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3)) ∧
        (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 ≠ 0))) := by
  obtain ⟨hθ0, hθsmul, -, -, -⟩ := RHTower.HalfWeight.weight_half_exceptional
  obtain ⟨-, -, hhol, -, hncob, -, h3term, -⟩ := weight_half_horizon_calibration
  obtain ⟨hfN, -, hprime0⟩ := weight_half_constant_term_vanishes_on_primes
  obtain ⟨-, -, hres, ⟨Λ, -, hΛdiff, hΛlim, hΛne⟩⟩ :=
    residual_eigenvalue_and_pole_order_comparison
  refine ⟨⟨hθ0, hθsmul, hhol, hncob, h3term⟩,
    ⟨weight_half_jU_nontrivial_on_Gamma0_four, extendedComplexCharacter_rational⟩,
    ⟨⟨hfN, hprime0⟩, fun P _ hinj hgood => normalizedCompositeCubicGauss_cube P hinj hgood⟩,
    ⟨hres, ⟨Λ, hΛdiff, hΛlim, hΛne⟩⟩⟩

end GaloisForLFunctions.RingdownOfTheCubicCover

end
