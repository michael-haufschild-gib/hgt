import GaloisForLFunctions.OrderSixMetaplecticTheory.TheQuadraticGradeVanishesWhenMinusOneIsNotASquare
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesSplitsIntoNineTwists

/-!
# The twisted theta square factors through a twisted cube factor

For a completely multiplicative twist `ψ : O →* ℂ` with `|ψ| ≤ 1` (a character of `O/q`, of `O/4`, or a
product of such) the twist `L_ψ(s) = Σ_h ψ(h)T(h)²(4π|ξ_h|)^{−s}` splits like `D`
(`twistDirichletG_eq_zeta_mul`):

`L_ψ(s) = C̄² Z_{ψ³}(3s/2 − 1) Σ_{u,m} ψ(uλ^m)(T(uλ^m)/T(1))²(4π|ξ_{uλ^m}|)^{−s} S^ψ_{uλ^m}(s/2)`.

Here `Z_{ψ³}(z) = Σ_B ψ(gen B)³N(B)^{−z}` runs over unramified ideals, and the twisted squarefree series (the
**layers**) are `S^ψ_{h₀}(w) = Σ_{A squarefree} ψ(gen A)(h₀/gen A)₃²σ(A)N(A)^{−w}`. The cube frequencies `B³`
carry `ψ³` (`T(ab³) = |b|T(a)`). For a character `φ` of `O/q` (`PrimaryPrime.twistDirichlet_eq_zeta_mul`) the
cubic grade (`φ³ = 1` off `q`) has the cube factor `Z₀` up to the Euler factor at `q`, with its pole; the
quadratic grade has the series of the character `φ³ ≠ 1`.
-/

noncomputable section

open MeasureTheory UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi SpectralTheoryOfTheCubicCover

/-! ### Multiplicative twists -/

/-- `L_ψ(s) = Σ_h ψ(h)T(h)²(4π|ξ_h|)^{−s}`. -/
def twistDirichletG (ψ : O →* ℂ) (s : ℂ) : ℂ :=
  besselDirichlet (fun h => ψ h * rationalSourceResidualFourierCoefficient h ^ 2) s

/-- `P^ψ_{h₀}(w) = Σ_I N(I)^{−w} ψ(gen I)(h₀/gen I)₃² T(gen I)²` over unramified ideals. -/
def twistedPrimarySeriesG (ψ : O →* ℂ) (h₀ : O) (w : ℂ) : ℂ :=
  ∑' I : Ideal O, unramifiedNormWeight w I * (ψ (primaryIdealGenerator I) *
    (ringComplex (symbol h₀ (primaryIdealGenerator I)) ^ 2 *
      rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2))

/-- The layer `S^ψ_{h₀}(w) = Σ_{A squarefree} N(A)^{−w} ψ(gen A)(h₀/gen A)₃² σ(A)`. -/
def twistedSquarefreeSeriesG (ψ : O →* ℂ) (h₀ : O) (w : ℂ) : ℂ :=
  ∑' A : Ideal O, if Squarefree A then unramifiedNormWeight w A * (ψ (primaryIdealGenerator A) *
    (ringComplex (symbol h₀ (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A)) else 0

/-- The cube factor `Z_{ψ³}(z) = Σ_B N(B)^{−z} ψ(gen B)³` over unramified ideals. -/
def cubeZetaG (ψ : O →* ℂ) (z : ℂ) : ℂ :=
  ∑' B : Ideal O, unramifiedNormWeight z B * ψ (primaryIdealGenerator B) ^ 3

/-- **Every twisted layer carries the twisted cube factor.** -/
theorem twistedPrimarySeriesG_eq (ψ : O →* ℂ) (hψb : ∀ x, ‖ψ x‖ ≤ 1) (u : Oˣ) (m : ℕ) (w : ℂ) (hw : 1 < w.re) :
    twistedPrimarySeriesG ψ ((u : O) * lambda ^ m) w =
      star rationalSourceThetaScalar ^ 2 * cubeZetaG ψ (3 * w - 1) *
        twistedSquarefreeSeriesG ψ ((u : O) * lambda ^ m) w := by
  set h₀ := (u : O) * lambda ^ m with hh₀
  set χ : O → ℂ := fun a => ringComplex (symbol h₀ a) with hχ
  set f : Ideal O → ℂ := fun I => unramifiedNormWeight w I * (ψ (primaryIdealGenerator I) *
    (χ (primaryIdealGenerator I) ^ 2 * rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2))
    with hf
  set x : Ideal O → ℂ := fun B => unramifiedNormWeight (3 * w - 1) B * ψ (primaryIdealGenerator B) ^ 3 with hx
  set y : Ideal O → ℂ := fun A => if Squarefree A then
    unramifiedNormWeight w A * (ψ (primaryIdealGenerator A) * (χ (primaryIdealGenerator A) ^ 2 *
      thetaSquareWeight A)) else 0 with hy
  have hw3 : 1 < (3 * w - 1).re := by
    have : (3 * w - 1).re = 3 * w.re - 1 := by simp
    rw [this]
    linarith
  have hψ1 : ∀ a, ‖ψ a‖ ≤ 1 := hψb
  have hxs : Summable (fun B => ‖x B‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun B => ?_)
      (unramifiedNormWeight_summable_norm _ hw3)
    simp only [hx, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hψ1 _))
  have hys : Summable (fun A => ‖y A‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun A => ?_)
      (unramifiedNormWeight_summable_norm w hw)
    simp only [hy]
    split_ifs with hsq
    · by_cases hA : primaryIdealGenerator A = 0
      · rw [unramifiedNormWeight_of_bad w A hA, zero_mul, norm_zero]
      · rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_thetaSquareWeight A hA hsq, hχ,
          symbol_norm_one _ _ (primaryIdealGenerator_spec A hA).2 (ramified_isCoprime_gen u m A hA)]
        simp only [one_pow, mul_one]
        exact mul_le_of_le_one_right (norm_nonneg _) (hψ1 _)
    · rw [norm_zero]
      exact norm_nonneg _
  have hpair : ∀ p : Ideal O × Ideal O, star rationalSourceThetaScalar ^ 2 * (x p.1 * y p.2) =
      admissiblePairs.indicator (fun p => f (p.2 * p.1 ^ 3)) p := by
    rintro ⟨B, A⟩
    by_cases hp : (B, A) ∈ admissiblePairs
    · obtain ⟨hsq, hA, hB⟩ := hp
      rw [Set.indicator_of_mem (show (B, A) ∈ admissiblePairs from ⟨hsq, hA, hB⟩)]
      have hs3 : symbol h₀ (primaryIdealGenerator A * primaryIdealGenerator B ^ 3) =
          symbol h₀ (primaryIdealGenerator A) := by
        rw [symbol_mul_denominator, show primaryIdealGenerator B ^ 3 =
            primaryIdealGenerator B * primaryIdealGenerator B * primaryIdealGenerator B by ring,
          symbol_mul_denominator, symbol_mul_denominator,
          ← pow_three' (symbol h₀ (primaryIdealGenerator B)),
          symbol_cube_of_isCoprime h₀ _ (primaryIdealGenerator_spec B hB).2
            (ramified_isCoprime_gen u m B hB), mul_one]
      have hψ3 : ψ (primaryIdealGenerator A * primaryIdealGenerator B ^ 3) =
          ψ (primaryIdealGenerator A) * ψ (primaryIdealGenerator B) ^ 3 := by
        simp only [map_mul, map_pow]
      simp only [hf, hx, hy, if_pos hsq]
      rw [map_mul (unramifiedNormWeight w), map_pow (unramifiedNormWeight w), primaryIdealGenerator_mul,
        primaryIdealGenerator_pow, hψ3]
      simp only [hχ]
      rw [hs3, sourceCoefficient_sq A B hA hB hsq, normWeight_shift w B hB]
      ring
    · rw [Set.indicator_of_notMem hp]
      simp only [admissiblePairs, Set.mem_setOf_eq, not_and_or] at hp
      simp only [hx, hy]
      rcases hp with hsq | hA | hB
      · rw [if_neg hsq, mul_zero, mul_zero]
      · push Not at hA
        by_cases hsq : Squarefree A
        · rw [if_pos hsq, unramifiedNormWeight_of_bad w A hA, zero_mul, mul_zero, mul_zero]
        · rw [if_neg hsq, mul_zero, mul_zero]
      · push Not at hB
        rw [unramifiedNormWeight_of_bad _ B hB, zero_mul, zero_mul, mul_zero]
  have hinj : Function.Injective (fun p : admissiblePairs => p.1.2 * p.1.1 ^ 3) := by
    rintro ⟨⟨B₁, A₁⟩, hsq₁, hA₁, hB₁⟩ ⟨⟨B₂, A₂⟩, hsq₂, hA₂, hB₂⟩ h
    obtain ⟨hA, hB⟩ := mul_cube_injective hsq₁ hsq₂ (primaryIdealGenerator_ne_zero_ideal B₁ hB₁)
      (primaryIdealGenerator_ne_zero_ideal B₂ hB₂) h
    subst hA hB
    rfl
  have hsupp : Function.support f ⊆ Set.range (fun p : admissiblePairs => p.1.2 * p.1.1 ^ 3) := by
    intro I hI
    have hI' : f I ≠ 0 := hI
    simp only [hf] at hI'
    have hg : primaryIdealGenerator I ≠ 0 := by
      intro hz
      exact hI' (by rw [unramifiedNormWeight_of_bad w I hz, zero_mul])
    have hT : rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ≠ 0 := by
      intro hz
      exact hI' (by rw [hz]; ring)
    obtain ⟨A, B, hsq, hA, hB, hAB⟩ := (sourceFourier_squarefree_cube_support_iff I hg).mp hT
    exact ⟨⟨(B, A), hsq, hA, hB⟩, hAB⟩
  calc twistedPrimarySeriesG ψ h₀ w = ∑' I : Ideal O, f I := rfl
    _ = ∑' p : admissiblePairs, f (p.1.2 * p.1.1 ^ 3) := (hinj.tsum_eq hsupp).symm
    _ = ∑' p : Ideal O × Ideal O, admissiblePairs.indicator (fun p => f (p.2 * p.1 ^ 3)) p :=
        tsum_subtype admissiblePairs (fun p => f (p.2 * p.1 ^ 3))
    _ = ∑' p : Ideal O × Ideal O, star rationalSourceThetaScalar ^ 2 * (x p.1 * y p.2) :=
        tsum_congr fun p => (hpair p).symm
    _ = star rationalSourceThetaScalar ^ 2 * ((∑' B, x B) * ∑' A, y A) := by
        rw [tsum_mul_left, tsum_mul_tsum_of_summable_norm hxs hys]
    _ = _ := by
        simp only [hx, hy, cubeZetaG, twistedSquarefreeSeriesG, hχ]
        ring


theorem summable_twistDirichletG_term (ψ : O →* ℂ) (hψb : ∀ x, ‖ψ x‖ ≤ 1) (s : ℂ) (hs : 4 < s.re) :
    Summable (fun h : O => if h = 0 then (0 : ℂ) else
      ψ h * rationalSourceResidualFourierCoefficient h ^ 2 *
        ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded (summable_thetaSqDirichlet_term s hs).norm (fun h => ?_)
  by_cases hh : h = 0
  · simp [hh]
  · simp only [hh, if_false, norm_mul]
    rw [mul_assoc]
    exact mul_le_of_le_one_left (by positivity) (hψb _)

/-- **The split of the twisted theta square.** For `Re s > 4`,
`L_ψ(s) = Σ_{u,m} ψ(uλ^m)(T(uλ^m)/T(1))²(4π|ξ_{uλ^m}|)^{−s} P^ψ_{uλ^m}(s/2)`. -/
theorem twistDirichletG_eq_twisted (ψ : O →* ℂ) (hψb : ∀ x, ‖ψ x‖ ≤ 1) (s : ℂ) (hs : 4 < s.re) :
    twistDirichletG ψ s = ∑' u : Oˣ, ∑' m : ℕ, ψ ((u : O) * lambda ^ m) *
      (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
          rationalSourceResidualFourierCoefficient 1) ^ 2 *
        ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) *
          twistedPrimarySeriesG ψ ((u : O) * lambda ^ m) (s / 2) := by
  set F : O → ℂ := fun h => if h = 0 then (0 : ℂ) else
    ψ h * rationalSourceResidualFourierCoefficient h ^ 2 *
      ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s) with hF
  set c : Oˣ → ℕ → ℂ := fun u m => ψ ((u : O) * lambda ^ m) *
    (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
        rationalSourceResidualFourierCoefficient 1) ^ 2 *
      ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) with hc
  set g : O → Ideal O → ℂ := fun h₀ I => unramifiedNormWeight (s / 2) I *
    (ψ (primaryIdealGenerator I) * (ringComplex (symbol h₀ (primaryIdealGenerator I)) ^ 2 *
      rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2)) with hg
  have hT1 : rationalSourceResidualFourierCoefficient 1 ≠ 0 := fun hz =>
    rationalSourceThetaScalar_ne_zero (by rw [rationalSourceThetaScalar, hz, star_zero])
  have hterm : ∀ p : Oˣ × ℕ × GoodIdeal,
      F (frequencySplit p) = c p.1 p.2.1 * g ((p.1 : O) * lambda ^ p.2.1) p.2.2.1 := by
    rintro ⟨u, m, I, hI⟩
    have hmul := sourceCoefficient_twisted_mul _ (ramified_ne_zero u m) I hI (ramified_isCoprime_gen u m I hI)
    have hT := eq_div_of_mul_eq hT1 hmul
    simp only [hF, hc, hg, frequencySplit]
    rw [if_neg (mul_ne_zero (ramified_ne_zero u m) hI), hT, frequencyWeight_split s _ I hI,
      map_mul ψ]
    ring
  have hFs : Summable F := summable_twistDirichletG_term ψ hψb s hs
  have hGs : Summable (fun p : Oˣ × ℕ × GoodIdeal => F (frequencySplit p)) :=
    hFs.comp_injective frequencySplit_injective
  have hsupp : Function.support F ⊆ Set.range frequencySplit := by
    intro h hh
    have hh0 : h ≠ 0 := by
      intro hz
      exact hh (by simp only [hF, hz, if_true])
    exact frequencySplit_surjective h hh0
  have hgood : ∀ h₀ : O, ∑' I : GoodIdeal, g h₀ I.1 = twistedPrimarySeriesG ψ h₀ (s / 2) := by
    intro h₀
    refine tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryIdealGenerator I ≠ 0}) ?_
    intro I hI
    by_contra hb
    exact hI (by simp only [hg]; rw [unramifiedNormWeight_of_bad _ _ (not_not.mp hb), zero_mul])
  calc twistDirichletG ψ s = ∑' h : O, F h := rfl
    _ = ∑' p : Oˣ × ℕ × GoodIdeal, F (frequencySplit p) := (frequencySplit_injective.tsum_eq hsupp).symm
    _ = ∑' u : Oˣ, ∑' q : ℕ × GoodIdeal, F (frequencySplit (u, q)) := hGs.tsum_prod
    _ = ∑' u : Oˣ, ∑' m : ℕ, ∑' I : GoodIdeal, F (frequencySplit (u, m, I)) :=
        tsum_congr fun u => (hGs.prod_factor u).tsum_prod
    _ = _ := by
        refine tsum_congr fun u => tsum_congr fun m => ?_
        simp only [hterm]
        rw [tsum_mul_left, hgood]

/-- **The twisted cube factor of `L_ψ`.** For `Re s > 4`,
`L_ψ(s) = C̄² Z_{ψ³}(3s/2 − 1) Σ_{u,m} ψ(uλ^m)(T(uλ^m)/T(1))²(4π|ξ_{uλ^m}|)^{−s} S^ψ_{uλ^m}(s/2)`. -/
theorem twistDirichletG_eq_zeta_mul (ψ : O →* ℂ) (hψb : ∀ x, ‖ψ x‖ ≤ 1) (s : ℂ) (hs : 4 < s.re) :
    twistDirichletG ψ s = star rationalSourceThetaScalar ^ 2 * cubeZetaG ψ (3 * (s / 2) - 1) *
      ∑' u : Oˣ, ∑' m : ℕ, ψ ((u : O) * lambda ^ m) *
        (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
            rationalSourceResidualFourierCoefficient 1) ^ 2 *
          ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) *
            twistedSquarefreeSeriesG ψ ((u : O) * lambda ^ m) (s / 2) := by
  have hw : 1 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  rw [twistDirichletG_eq_twisted ψ hψb s hs, ← tsum_mul_left]
  refine tsum_congr fun u => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [twistedPrimarySeriesG_eq ψ hψb u m _ hw]
  ring


namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Characters of `O/q` -/

theorem norm_mulChar_le (φ : MulChar P.Res ℂ) (x : P.Res) : ‖φ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · rw [hx, MulChar.map_zero, norm_zero]
    exact zero_le_one
  · have h : φ x ^ (Fintype.card P.Res - 1) = 1 := by
      rw [← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, MulChar.map_one]
    have hcard : 1 < Fintype.card P.Res := Fintype.one_lt_card
    have hn : ‖φ x‖ ^ (Fintype.card P.Res - 1) = 1 := by rw [← norm_pow, h, norm_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp hn)

/-- `h ↦ φ(h mod q)`. -/
def resTwist (φ : MulChar P.Res ℂ) : O →* ℂ := φ.toMonoidHom.comp P.res.toMonoidHom

theorem norm_resTwist_le (φ : MulChar P.Res ℂ) (x : O) : ‖P.resTwist φ x‖ ≤ 1 := P.norm_mulChar_le φ _

/-- `L_φ(s) = Σ_h φ(h)T(h)²(4π|ξ_h|)^{−s}`. -/
def twistDirichlet (φ : MulChar P.Res ℂ) (s : ℂ) : ℂ :=
  besselDirichlet (fun h => φ (P.res h) * rationalSourceResidualFourierCoefficient h ^ 2) s

/-- `P^φ_{h₀}(w)` for `φ` a character of `O/q`. -/
def twistedPrimarySeriesW (φ : MulChar P.Res ℂ) (h₀ : O) (w : ℂ) : ℂ :=
  ∑' I : Ideal O, unramifiedNormWeight w I * (φ (P.res (primaryIdealGenerator I)) *
    (ringComplex (symbol h₀ (primaryIdealGenerator I)) ^ 2 *
      rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2))

/-- `S^φ_{h₀}(w)` for `φ` a character of `O/q`. -/
def twistedSquarefreeSeriesW (φ : MulChar P.Res ℂ) (h₀ : O) (w : ℂ) : ℂ :=
  ∑' A : Ideal O, if Squarefree A then unramifiedNormWeight w A * (φ (P.res (primaryIdealGenerator A)) *
    (ringComplex (symbol h₀ (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A)) else 0

/-- `Z_{φ³}(z) = Σ_B N(B)^{−z} φ(gen B)³`. -/
def cubeZetaW (φ : MulChar P.Res ℂ) (z : ℂ) : ℂ :=
  ∑' B : Ideal O, unramifiedNormWeight z B * φ (P.res (primaryIdealGenerator B)) ^ 3

theorem twistedPrimarySeriesW_eq (φ : MulChar P.Res ℂ) (u : Oˣ) (m : ℕ) (w : ℂ) (hw : 1 < w.re) :
    P.twistedPrimarySeriesW φ ((u : O) * lambda ^ m) w =
      star rationalSourceThetaScalar ^ 2 * P.cubeZetaW φ (3 * w - 1) *
        P.twistedSquarefreeSeriesW φ ((u : O) * lambda ^ m) w :=
  twistedPrimarySeriesG_eq (P.resTwist φ) (P.norm_resTwist_le φ) u m w hw

theorem summable_twistDirichlet_term (φ : MulChar P.Res ℂ) (s : ℂ) (hs : 4 < s.re) :
    Summable (fun h : O => if h = 0 then (0 : ℂ) else
      φ (P.res h) * rationalSourceResidualFourierCoefficient h ^ 2 *
        ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) :=
  summable_twistDirichletG_term (P.resTwist φ) (P.norm_resTwist_le φ) s hs

/-- **The split of the twisted theta square** at a character of `O/q`. -/
theorem twistDirichlet_eq_twisted (φ : MulChar P.Res ℂ) (s : ℂ) (hs : 4 < s.re) :
    P.twistDirichlet φ s = ∑' u : Oˣ, ∑' m : ℕ, φ (P.res ((u : O) * lambda ^ m)) *
      (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
          rationalSourceResidualFourierCoefficient 1) ^ 2 *
        ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) *
          P.twistedPrimarySeriesW φ ((u : O) * lambda ^ m) (s / 2) :=
  twistDirichletG_eq_twisted (P.resTwist φ) (P.norm_resTwist_le φ) s hs

/-- **The twisted cube factor of `L_φ`** at a character of `O/q`. -/
theorem twistDirichlet_eq_zeta_mul (φ : MulChar P.Res ℂ) (s : ℂ) (hs : 4 < s.re) :
    P.twistDirichlet φ s = star rationalSourceThetaScalar ^ 2 * P.cubeZetaW φ (3 * (s / 2) - 1) *
      ∑' u : Oˣ, ∑' m : ℕ, φ (P.res ((u : O) * lambda ^ m)) *
        (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
            rationalSourceResidualFourierCoefficient 1) ^ 2 *
          ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) *
            P.twistedSquarefreeSeriesW φ ((u : O) * lambda ^ m) (s / 2) :=
  twistDirichletG_eq_zeta_mul (P.resTwist φ) (P.norm_resTwist_le φ) s hs

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
