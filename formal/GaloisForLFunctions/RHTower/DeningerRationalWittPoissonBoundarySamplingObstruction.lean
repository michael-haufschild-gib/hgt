import GaloisForLFunctions.RHTower.DeningerRationalWittSchwartzBesselRestriction
import GaloisForLFunctions.RHTower.DeningerMeyerRadialEndpoints
import GaloisForLFunctions.HTGeometry.HermiteFourierEigen
import GaloisForLFunctions.RHTower.MeyerPoissonTest
import Mathlib.Analysis.PSeries

/-!
# Poisson-boundary obstruction to raw prime sampling

The source-derived Schwartz--Witt Bessel map is analytically valid, but it cannot be relabelled as
a map on arithmetic middle cohomology.  This module proves the obstruction by an explicit boundary.

The Fourier-fixed Hermite combination `h₄ - h₄(0)h₀` is sixteen times the repository's canonical
Meyer--Poisson test

`x² (x² - 3/(2π)) exp(-πx²)`.

It lies in Meyer's endpoint domain.  At every prime `p`, every term of its Poisson sum
`∑ n, f((n+1)p)` is strictly positive, and the series is summable by one Schwartz estimate.
Consequently literal evaluation at `p` does not annihilate the range of the Meyer--Poisson
differential and cannot factor through the Meyer quotient.

The same boundary has nonzero raw polarized first-suspension value against every nonzero packet.
In particular actual arithmetic-Frobenius-fixed finite rational-Witt witnesses exhibit this
leakage.  Thus Route L requires a genuinely secondary or quotient-corrected regulator; raw prime
sampling is not the arithmetic Cauchy map.
-/

namespace RHTower

open scoped Real FourierTransform SchwartzMap BigOperators

noncomputable section

open GaloisForLFunctions

/-- Fourier-fixed endpoint-cancelled Hermite realization of the canonical Meyer test. -/
def deningerMeyerPrimeBoundaryProbe : SchwartzMap ℝ ℂ :=
  hermiteSchwartz 4 -
    (hermiteSchwartz 4 0) • hermiteSchwartz 0

/-- Real profile of `deningerMeyerPrimeBoundaryProbe`. -/
def deningerMeyerPrimeBoundaryProbeReal (x : ℝ) : ℝ :=
  8 * x ^ 2 * (2 * x ^ 2 - 3 / Real.pi) * gaussReal x

theorem deningerMeyerPrimeBoundaryProbe_apply (x : ℝ) :
    deningerMeyerPrimeBoundaryProbe x =
      (deningerMeyerPrimeBoundaryProbeReal x : ℂ) := by
  rw [deningerMeyerPrimeBoundaryProbe]
  simp only [sub_apply, _root_.smul_apply, smul_eq_mul,
    hermiteSchwartz_apply]
  have hEval (y : ℝ) :
      (hermitePoly 4).eval y =
        16 * y ^ 4 - (24 / Real.pi) * y ^ 2 +
          3 / Real.pi ^ 2 := by
    simp [hermitePoly, hermiteStep]
    field_simp [Real.pi_ne_zero]
    ring_nf
  rw [hEval x, hEval 0, hermitePoly_zero]
  simp [deningerMeyerPrimeBoundaryProbeReal]
  simp [gaussReal]
  field_simp [Real.pi_ne_zero]
  ring_nf

/-- The probe is not a new arbitrary test: it is exactly sixteen times `meyerPoissonTest`. -/
theorem deningerMeyerPrimeBoundaryProbe_eq_meyerPoissonTest (x : ℝ) :
    deningerMeyerPrimeBoundaryProbe x =
      ((16 * meyerPoissonTest x : ℝ) : ℂ) := by
  rw [deningerMeyerPrimeBoundaryProbe_apply]
  simp only [Complex.ofReal_inj]
  rw [deningerMeyerPrimeBoundaryProbeReal, meyerPoissonTest, gaussReal]
  ring_nf

theorem deningerMeyerPrimeBoundaryProbeReal_pos
    {x : ℝ} (hx : 2 ≤ x) :
    0 < deningerMeyerPrimeBoundaryProbeReal x := by
  have hpi : 3 / Real.pi < 2 * x ^ 2 := by
    have hpi3 : 3 / Real.pi < 1 := by
      rw [div_lt_one Real.pi_pos]
      exact Real.pi_gt_three
    nlinarith
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num)
        (sq_pos_of_pos (lt_of_lt_of_le (by norm_num) hx)))
      (sub_pos.mpr hpi))
    (gaussReal_pos x)

theorem deningerMeyerPrimeBoundaryProbe_fourier_fixed :
    FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ)
        deningerMeyerPrimeBoundaryProbe =
      deningerMeyerPrimeBoundaryProbe := by
  change fourierSCLM deningerMeyerPrimeBoundaryProbe =
    deningerMeyerPrimeBoundaryProbe
  rw [deningerMeyerPrimeBoundaryProbe, map_sub, map_smul,
    fourierSCLM_hermiteSchwartz, fourierSCLM_hermiteSchwartz]
  have h4 : ((-Complex.I) ^ 4 : ℂ) = 1 := by
    rw [show (-Complex.I) ^ 4 =
        (Complex.I * Complex.I) * (Complex.I * Complex.I) by ring_nf,
      Complex.I_mul_I]
    norm_num
  rw [h4, pow_zero, one_smul, one_smul]

/-- The explicit probe lies in Meyer's even two-endpoint source domain. -/
theorem deningerMeyerPrimeBoundaryProbe_mem :
    deningerMeyerPrimeBoundaryProbe ∈ DeningerMeyerCap := by
  rw [deningerMeyerCap_mem_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [deningerMeyerPrimeBoundaryProbe_apply,
      deningerMeyerPrimeBoundaryProbe_apply]
    simp only [Complex.ofReal_inj]
    simp [deningerMeyerPrimeBoundaryProbeReal, gaussReal]
  · rw [deningerMeyerPrimeBoundaryProbe_apply]
    norm_num [deningerMeyerPrimeBoundaryProbeReal]
  · rw [deningerMeyerPrimeBoundaryProbe_fourier_fixed,
      deningerMeyerPrimeBoundaryProbe_apply]
    norm_num [deningerMeyerPrimeBoundaryProbeReal]

/-- The prime-dilation series of the boundary probe is absolutely summable. -/
theorem deningerMeyerPrimeBoundaryProbe_dilation_summable
    (p : Nat.Primes) :
    Summable (fun n : ℕ =>
      deningerMeyerPrimeBoundaryProbe
        (((n : ℝ) + 1) * (p : ℝ))) := by
  apply Summable.of_norm
  let S :=
    SchwartzMap.seminorm ℂ 2 0 deningerMeyerPrimeBoundaryProbe
  have hmajor :
      Summable (fun n : ℕ =>
        S * (1 / |(n : ℝ) + 1| ^ (2 : ℝ))) :=
    ((Real.summable_one_div_nat_add_rpow 1 2).2
      (by norm_num)).mul_left S
  refine Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_) hmajor
  let y : ℝ := (n : ℝ) + 1
  let x : ℝ := y * (p : ℝ)
  have hy : 0 < y := by positivity
  have hp : 1 ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hxy : y ≤ x := by
    dsimp [x]
    nlinarith
  have hseminorm :=
    SchwartzMap.norm_pow_mul_le_seminorm ℂ
      deningerMeyerPrimeBoundaryProbe 2 x
  have hsemi :
      x ^ 2 * ‖deningerMeyerPrimeBoundaryProbe x‖ ≤ S := by
    simpa [S, Real.norm_eq_abs,
      abs_of_pos (lt_of_lt_of_le hy hxy)] using hseminorm
  have hsquares : y ^ 2 ≤ x ^ 2 := by nlinarith
  have hybound :
      y ^ 2 * ‖deningerMeyerPrimeBoundaryProbe x‖ ≤ S := by
    calc
      y ^ 2 * ‖deningerMeyerPrimeBoundaryProbe x‖
          ≤ x ^ 2 * ‖deningerMeyerPrimeBoundaryProbe x‖ :=
        mul_le_mul_of_nonneg_right hsquares (norm_nonneg _)
      _ ≤ S := hsemi
  have hnorm :
      ‖deningerMeyerPrimeBoundaryProbe x‖ ≤ S / y ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hy)).2
      (by simpa [mul_comm] using hybound)
  calc
    ‖deningerMeyerPrimeBoundaryProbe
        (((n : ℝ) + 1) * (p : ℝ))‖
        = ‖deningerMeyerPrimeBoundaryProbe x‖ := rfl
    _ ≤ S / y ^ 2 := hnorm
    _ = S * (1 / |(n : ℝ) + 1| ^ (2 : ℝ)) := by
      rw [abs_of_pos hy]
      dsimp [y]
      rw [show ((n : ℝ) + 1) ^ (2 : ℝ) =
          ((n : ℝ) + 1) ^ (2 : ℕ) by norm_num]
      ring_nf

/-- The explicit Meyer boundary has strictly positive Poisson sum at every arithmetic prime. -/
theorem deningerMeyerPrimeBoundaryProbe_meyerSum_pos
    (p : Nat.Primes) :
    0 < (deningerMeyerSum
      deningerMeyerPrimeBoundaryProbe (p : ℝ)).re := by
  have hsum :=
    deningerMeyerPrimeBoundaryProbe_dilation_summable p
  rw [deningerMeyerSum, Complex.re_tsum hsum]
  have hsumRe :
      Summable (fun n : ℕ =>
        (deningerMeyerPrimeBoundaryProbe
          (((n : ℝ) + 1) * (p : ℝ))).re) := by
    have hnorm := hsum.norm
    convert hnorm using 1
    funext n
    rw [deningerMeyerPrimeBoundaryProbe_apply,
      Complex.ofReal_re]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg
        ((deningerMeyerPrimeBoundaryProbeReal_pos
          (x := ((n : ℝ) + 1) * (p : ℝ))
          (by
            have hp : 2 ≤ (p : ℝ) := by
              exact_mod_cast p.2.two_le
            nlinarith)).le)]
  exact hsumRe.tsum_pos
    (fun n => by
      rw [deningerMeyerPrimeBoundaryProbe_apply,
        Complex.ofReal_re]
      exact
        (deningerMeyerPrimeBoundaryProbeReal_pos
          (x := ((n : ℝ) + 1) * (p : ℝ))
          (by
            have hp : 2 ≤ (p : ℝ) := by
              exact_mod_cast p.2.two_le
            nlinarith)).le)
    0
    (by
      rw [deningerMeyerPrimeBoundaryProbe_apply,
        Complex.ofReal_re]
      exact
        deningerMeyerPrimeBoundaryProbeReal_pos
          (x := (((0 : ℕ) : ℝ) + 1) * (p : ℝ))
          (by
            have hp : 2 ≤ (p : ℝ) := by
              exact_mod_cast p.2.two_le
            norm_num at *
            exact hp))

theorem deningerMeyerPrimeBoundaryProbe_meyerSum_ne_zero
    (p : Nat.Primes) :
    deningerMeyerSum
        deningerMeyerPrimeBoundaryProbe (p : ℝ) ≠ 0 := by
  intro hzero
  have hpos :=
    deningerMeyerPrimeBoundaryProbe_meyerSum_pos p
  rw [hzero, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- The explicit boundary witness as an element of Meyer's endpoint domain. -/
def DeningerMeyerPrimeBoundaryCap : DeningerMeyerCap :=
  ⟨deningerMeyerPrimeBoundaryProbe,
    deningerMeyerPrimeBoundaryProbe_mem⟩

section NoQuotientDescent

variable {Hminus : Type*}
variable [AddCommGroup Hminus] [Module ℂ Hminus]

/-- Any prime evaluation compatible with the literal Meyer sum fails to annihilate its range. -/
theorem deningerPrimeEvaluation_not_annihilate_meyerRange
    (p : Nat.Primes)
    (Z : DeningerMeyerCap →ₗ[ℂ] Hminus)
    (ev : Hminus →ₗ[ℂ] ℂ)
    (hcompat : ∀ f,
      ev (Z f) =
        deningerMeyerSum
          (f : SchwartzMap ℝ ℂ) (p : ℝ)) :
    ¬ LinearMap.range Z ≤ LinearMap.ker ev := by
  intro hle
  have hrange :
      Z DeningerMeyerPrimeBoundaryCap ∈ LinearMap.range Z :=
    ⟨DeningerMeyerPrimeBoundaryCap, rfl⟩
  have hzero := hle hrange
  rw [LinearMap.mem_ker, hcompat] at hzero
  exact
    deningerMeyerPrimeBoundaryProbe_meyerSum_ne_zero p hzero

/-- Consequently literal prime evaluation cannot factor through the Meyer quotient. -/
theorem deningerPrimeEvaluation_no_meyerQuotientFactor
    (p : Nat.Primes)
    (Z : DeningerMeyerCap →ₗ[ℂ] Hminus)
    (ev : Hminus →ₗ[ℂ] ℂ)
    (hcompat : ∀ f,
      ev (Z f) =
        deningerMeyerSum
          (f : SchwartzMap ℝ ℂ) (p : ℝ)) :
    ¬ ∃ q : (Hminus ⧸ LinearMap.range Z) →ₗ[ℂ] ℂ,
      q.comp (LinearMap.range Z).mkQ = ev := by
  rintro ⟨q, hq⟩
  apply
    deningerPrimeEvaluation_not_annihilate_meyerRange
      p Z ev hcompat
  intro x hx
  rw [LinearMap.mem_ker]
  obtain ⟨f, rfl⟩ := hx
  have hmk :
      (LinearMap.range Z).mkQ (Z f) = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (LinearMap.range Z)).2 ⟨f, rfl⟩
  have h := LinearMap.congr_fun hq (Z f)
  change
    q ((LinearMap.range Z).mkQ (Z f)) = ev (Z f) at h
  rw [hmk, map_zero] at h
  exact h.symm

end NoQuotientDescent

/-- Naive polarized first-mode value of the explicit Meyer boundary at one arithmetic prime. -/
def deningerMeyerBoundaryFirstModeValue
    (p : Nat.Primes)
    (v : DeningerPrimePacketComplexHaarL2 p) :
    DeningerPrimeSuspensionHaarL2 p :=
  ((deningerPrimePolarizedHalfDensity p : ℝ) : ℂ) •
    (deningerMeyerSum
      deningerMeyerPrimeBoundaryProbe (p : ℝ) •
        deningerPrimeSuspensionFirstMode p v)

/-- Raw Poisson-boundary sampling leaks into every nonzero first suspension packet. -/
theorem deningerMeyerBoundaryFirstModeValue_ne_zero
    (p : Nat.Primes)
    {v : DeningerPrimePacketComplexHaarL2 p}
    (hv : v ≠ 0) :
    deningerMeyerBoundaryFirstModeValue p v ≠ 0 := by
  intro hzero
  rcases smul_eq_zero.mp hzero with hhalf | hrest
  · exact
      (Complex.ofReal_ne_zero.mpr
        (deningerPrimePolarizedHalfDensity_pos p).ne') hhalf
  · rcases smul_eq_zero.mp hrest with hsum | hmode
    · exact
        deningerMeyerPrimeBoundaryProbe_meyerSum_ne_zero p hsum
    · apply hv
      apply deningerPrimeSuspensionFirstMode_injective p
      rw [map_zero]
      exact hmode

/-- Actual finite Wrat witnesses exhibit nonzero leakage of a Poisson boundary into the raw
first-mode sampling formula. -/
theorem
    deningerFiniteRationalWitt_exists_witness_nonzero_boundarySampling
    (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient
      (p : ℕ) s → ℂ)
    (hF : F ≠ 0) :
    ∃ w : DeningerFiniteCyclotomicWittAlgebra s.modulus,
      deningerPrimeComplexifiedRationalWittFrobenius p
          (deningerPrimeFiniteCyclotomicWittInclusion p s w) =
        deningerPrimeFiniteCyclotomicWittInclusion p s w ∧
      (∀ u : (ZMod s.modulus)ˣ,
        deningerFiniteCyclotomicWittEvaluation
            s.modulus u w =
          F (QuotientGroup.mk u)) ∧
      deningerMeyerBoundaryFirstModeValue p
        (deningerPrimeFiniteStageComplexHaarL2 p s F) ≠ 0 := by
  obtain ⟨w, hwfixed, heval⟩ :=
    deningerPrimeComplexifiedRationalWitt_finiteRestriction_surjective
      p s F
  refine ⟨w, hwfixed, heval,
    deningerMeyerBoundaryFirstModeValue_ne_zero p ?_⟩
  intro hv
  have hmode :
      deningerPrimeFiniteStageFirstSuspensionMode p s F = 0 := by
    change
      deningerPrimeSuspensionFirstMode p
        (deningerPrimeFiniteStageComplexHaarL2 p s F) = 0
    rw [hv, map_zero]
  exact
    deningerPrimeFiniteStageFirstSuspensionMode_ne_zero
      p s hF hmode

end

end RHTower
