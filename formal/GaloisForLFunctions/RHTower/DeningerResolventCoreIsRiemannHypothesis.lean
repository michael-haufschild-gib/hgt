import GaloisForLFunctions.RHTower.DeningerArithmeticDenseResolventPurity
import GaloisForLFunctions.RHTower.ConformalHodgeBlindness
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# The Hodge–Schwartz resolvent core is the Riemann hypothesis

The arithmetic Hodge route asks for a carrier `E` with a centred generator whose off-axis
resolvents are surjective (or have dense range), together with a nonzero transpose eigenfunctional
of eigenvalue `ρ - 1/2` for every Xi zero `ρ`.  The corpus proves that such a carrier forces RH.

The converse holds with the most naive carrier: the space of all functions on the Xi divisor
support, with the generator acting diagonally by `ρ - 1/2` and the evaluations at the zeros as
eigenfunctionals.  Under RH every eigenvalue is purely imaginary, so each off-axis resolvent is
bijective.  Hence the existence of the resolvent-core package is equivalent to RH, and it is
realized by a carrier indexed by the zeros themselves.  The package carries no information beyond
RH.

On the positivity side, a conformally scaled positive seminorm is compatible with an eigencharacter
of any off-line exponent (`exists_conformal_seminorm_with_offLine_character`): the two coexist,
and the character is not bounded by the seminorm (`not_bounded_of_conformal_offLine`).  So
conformal Hodge positivity does not constrain the location of the spectrum.

These are constraints on the Hodge route, not a refutation of it. The abstract package carries no
information beyond RH unless its carrier is built independently of the zeros, and conformal
scaling alone cannot supply positivity. A geometric carrier with structural positivity (a category
with `ζ` as one member among many) is not affected.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Under RH every Xi zero is on the critical line -/

theorem re_eq_half_of_xi_eq_zero (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : xi ρ = 0) :
    ρ.re = 1 / 2 := by
  have hright := (rh_iff_xi_ne_zero_right).mp hRH
  rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hmem : (1 - ρ) ∈ rightHalf := by
      rw [mem_rightHalf]
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact hright (1 - ρ) hmem (by rw [xi_one_sub]; exact hρ)
  · exact heq
  · exfalso
    exact hright ρ (mem_rightHalf.mpr hgt) hρ

/-! ## The diagonal carrier -/

/-- The centred eigenvalue `ρ - 1/2` of a Xi zero. -/
def xiCentredEigenvalue (q : XiDivisorSupport) : ℂ :=
  (1 / 2 + Complex.I * xiSpectralPointSupport q) - 1 / 2

theorem xiCentredEigenvalue_eq (q : XiDivisorSupport) :
    xiCentredEigenvalue q = (q : ℂ) - 1 / 2 := by
  unfold xiCentredEigenvalue xiSpectralPointSupport
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The diagonal generator on functions on the divisor support. -/
def xiDiagonalGenerator : (XiDivisorSupport → ℂ) →ₗ[ℂ] (XiDivisorSupport → ℂ) where
  toFun x q := xiCentredEigenvalue q * x q
  map_add' x y := by
    funext q
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem xiDiagonalGenerator_sub_surjective (hRH : RiemannHypothesis) {z : ℂ} (hz : z.re ≠ 0) :
    Function.Surjective
      (xiDiagonalGenerator - z • (LinearMap.id : (XiDivisorSupport → ℂ) →ₗ[ℂ] _)) := by
  have hne : ∀ q : XiDivisorSupport, xiCentredEigenvalue q - z ≠ 0 := by
    intro q h
    have hre := congrArg Complex.re h
    rw [xiCentredEigenvalue_eq, Complex.zero_re, Complex.sub_re, Complex.sub_re] at hre
    have hq := re_eq_half_of_xi_eq_zero hRH (xi_eq_zero_of_mem_divisor_support q)
    norm_num at hre
    apply hz
    linarith
  intro y
  refine ⟨fun q => y q / (xiCentredEigenvalue q - z), ?_⟩
  funext q
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  change xiCentredEigenvalue q * (y q / (xiCentredEigenvalue q - z)) -
    z * (y q / (xiCentredEigenvalue q - z)) = y q
  field_simp [hne q]

/-- **RH produces the Hodge–Schwartz resolvent-core package** on the naive diagonal carrier. -/
def hodgeSchwartzResolventXiSpectrum_of_riemannHypothesis (hRH : RiemannHypothesis) :
    DeningerHodgeSchwartzResolventXiSpectrum (XiDivisorSupport → ℂ) where
  centeredGenerator := xiDiagonalGenerator
  offAxis_resolvent_surjective _ hz := xiDiagonalGenerator_sub_surjective hRH hz
  evaluation q := LinearMap.proj q
  evaluation_ne_zero q := by
    intro h
    have := LinearMap.congr_fun h (Pi.single q 1)
    simp at this
  transpose_centeredGenerator q x := rfl

/-- **The resolvent-core package is equivalent to RH.** -/
theorem riemannHypothesis_iff_nonempty_hodgeSchwartzResolventXiSpectrum :
    RiemannHypothesis ↔
      Nonempty (DeningerHodgeSchwartzResolventXiSpectrum (XiDivisorSupport → ℂ)) :=
  ⟨fun hRH => ⟨hodgeSchwartzResolventXiSpectrum_of_riemannHypothesis hRH⟩,
    fun ⟨S⟩ => riemannHypothesis_of_hodgeSchwartzResolventXiSpectrum S⟩

/-- The dense-range package on the product topology is also equivalent to RH. -/
theorem riemannHypothesis_iff_nonempty_hodgeSchwartzDenseRangeXiSpectrum :
    RiemannHypothesis ↔
      Nonempty (DeningerHodgeSchwartzDenseRangeXiSpectrum (XiDivisorSupport → ℂ)) := by
  constructor
  · intro hRH
    exact ⟨{
      centeredGenerator := xiDiagonalGenerator
      offAxis_resolvent_denseRange := fun _ hz =>
        (xiDiagonalGenerator_sub_surjective hRH hz).denseRange
      evaluation := fun q => LinearMap.proj q
      evaluation_ne_zero := fun q h => by
        have := LinearMap.congr_fun h (Pi.single q 1)
        simp at this
      evaluation_continuous := fun q => continuous_apply q
      transpose_centeredGenerator := fun _ _ => rfl }⟩
  · rintro ⟨S⟩
    exact riemannHypothesis_of_hodgeSchwartzDenseRangeXiSpectrum S

/-! ## Conformal positivity coexists with off-line characters -/

/-- For every exponent `κ` and every off-line character exponent `λ` (`Re λ ≠ κ`) there is a flow
with a nonzero conformally scaled seminorm and a nonzero eigencharacter of exponent `λ`; the
character is not bounded by the seminorm. -/
theorem exists_conformal_seminorm_with_offLine_character (κ : ℝ) (lam : ℂ) (hoff : lam.re ≠ κ) :
    ∃ (V : ℝ → (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ)) (p : Seminorm ℂ (ℂ × ℂ)) (E : (ℂ × ℂ) →ₗ[ℂ] ℂ),
      (∀ c u, p (V c u) = Real.exp (κ * c) * p u) ∧
      (∀ c u, E (V c u) = Complex.exp (lam * c) * E u) ∧
      p (1, 0) = 1 ∧ E (0, 1) = 1 ∧ ¬ ∃ C : ℝ, ∀ u, ‖E u‖ ≤ C * p u := by
  let V : ℝ → (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) := fun c =>
    ((Real.exp (κ * c) : ℂ) • LinearMap.fst ℂ ℂ ℂ).prod
      (Complex.exp (lam * c) • LinearMap.snd ℂ ℂ ℂ)
  let p : Seminorm ℂ (ℂ × ℂ) := (normSeminorm ℂ ℂ).comp (LinearMap.fst ℂ ℂ ℂ)
  let E : (ℂ × ℂ) →ₗ[ℂ] ℂ := LinearMap.snd ℂ ℂ ℂ
  have hp : ∀ c u, p (V c u) = Real.exp (κ * c) * p u := by
    intro c u
    change ‖(Real.exp (κ * c) : ℂ) * u.1‖ = Real.exp (κ * c) * ‖u.1‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hE : ∀ c u, E (V c u) = Complex.exp (lam * c) * E u := by
    intro c u
    simp [E, V]
  refine ⟨V, p, E, hp, hE, by simp [p], by simp [E], ?_⟩
  exact not_bounded_of_conformal_offLine V p E κ lam hp hE hoff (u₀ := (0, 1)) (by simp [E])

end

end RHTower
