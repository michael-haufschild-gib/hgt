import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFullMirrorBogoliubovEndpoint

/-!
# Full theta-mirror Bogoliubov scattering in its canonical Krein--Cayley chart

The ordinary sectorwise `SU(2)` Cayley identification is false for exact Davies--Fulling
scattering: its even coupling jets do not disappear, and bosonic pair creation has `SU(1,1)`
rather than positive-Hermitian signature.  The correct nonperturbative Cayley statement uses the
open-disk coordinate of the actual bosonic Bogoliubov block.

For exact full-mirror pair amplitude `beta` and positive CCR gain

`g = sqrt (1 + |beta|^(2 : ℕ))`,

define the source-faithful disk coordinate

`chi = beta / (g + 1)`.

Then `|chi| < 1`, and the Krein--Cayley transform of the off-diagonal Nambu generator is

`S_chi = (1 - |chi|^(2 : ℕ))^(-1) [[1 + |chi|^(2 : ℕ), 2 chi],
                              [2 conj chi, 1 + |chi|^(2 : ℕ)]]`.

This file proves that `S_chi` is exactly the existing full theta-mirror Bogoliubov scattering
matrix, not a postulated beam splitter.  The disk coordinate is the unique open-disk coordinate
recovering both the physical pair coefficient and positive bosonic gain.  The resulting block
preserves the Nambu signed Hermitian form and has an exact signed-adjoint inverse.

The construction also closes the finite-coupling mixing branch: one arbitrarily weak common
coupling activates every countable tilted family in the exact Krein--Cayley chart, unconditionally.
On the common van-Hove clock, however, its transition rate is exactly one quarter of the existing
Bogoliubov pair rate.  Thus the correct Cayley chart does not evade the RH-bearing first-jet
obstruction: universal standard-clock activity is still equivalent to RH.

The bosonic symplectic/Bogoliubov provenance is standard; see Bruneau--Derezinski
(`arXiv:math-ph/0511069`) and Cariolaro--Pierobon (`arXiv:1704.02008`).  The moving-mirror
open-system provenance remains Butera (`arXiv:2306.03813`).  This endpoint is
`[LITERATURE] [BRIDGE] [PAPER-PROVED] [LEAN-PROVED]`; it does not claim a proof of RH.
-/

open Complex Real Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Source-faithful open-disk coordinate -/

/-- Canonical open-disk coordinate of the exact full-mirror bosonic Bogoliubov block. -/
def thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate
    (a lambda omega : ℝ) : ℂ :=
  thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega /
    ((thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1 : ℝ) : ℂ)

theorem thetaCuspHawkingFullMirrorBogoliubovGain_add_one_pos
    (a lambda omega : ℝ) :
    0 < thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1 := by
  linarith [thetaCuspHawkingFullMirrorBogoliubovGain_pos a lambda omega]

/-- Disk intensity in terms of the exact pair number and positive CCR gain. -/
theorem normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate
    (a lambda omega : ℝ) :
    Complex.normSq
        (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega) =
      thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega /
        (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1) ^ 2 := by
  rw [thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate,
    Complex.normSq_div, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq]
  simp only [thetaCuspHawkingFullMirrorBogoliubovNumber, pow_two]

/-- Hyperbolic half-angle law for the exact bosonic disk coordinate. -/
theorem normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate_eq_gain
    (a lambda omega : ℝ) :
    Complex.normSq
        (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega) =
      (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega - 1) /
        (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1) := by
  rw [normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate]
  have hgain := thetaCuspHawkingFullMirrorBogoliubovGain_sq a lambda omega
  have hden :=
    (thetaCuspHawkingFullMirrorBogoliubovGain_add_one_pos a lambda omega).ne'
  field_simp [hden]
  nlinarith

/-- Exact full-mirror Bogoliubov data always lie strictly inside the Krein--Cayley disk. -/
theorem normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate_lt_one
    (a lambda omega : ℝ) :
    Complex.normSq
      (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega) < 1 := by
  rw [normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate_eq_gain]
  exact (div_lt_one
    (thetaCuspHawkingFullMirrorBogoliubovGain_add_one_pos a lambda omega)).2
      (by linarith)

theorem one_sub_normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate
    (a lambda omega : ℝ) :
    1 - Complex.normSq
        (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega) =
      2 / (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1) := by
  rw [normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate_eq_gain]
  have hden :=
    (thetaCuspHawkingFullMirrorBogoliubovGain_add_one_pos a lambda omega).ne'
  field_simp [hden]
  ring_nf

theorem one_add_normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate
    (a lambda omega : ℝ) :
    1 + Complex.normSq
        (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega) =
      2 * thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega /
        (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1) := by
  rw [normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate_eq_gain]
  have hden :=
    (thetaCuspHawkingFullMirrorBogoliubovGain_add_one_pos a lambda omega).ne'
  field_simp [hden]
  ring_nf

/-! ## Generic two-mode Krein--Cayley chart and exact recovery -/

/-- Positive-sheet gain of the two-mode bosonic Krein--Cayley chart. -/
def twoModeBosonicKreinCayleyGain (z : ℂ) : ℝ :=
  (1 + Complex.normSq z) / (1 - Complex.normSq z)

/-- Pair coefficient of the two-mode bosonic Krein--Cayley chart. -/
def twoModeBosonicKreinCayleyPair (z : ℂ) : ℂ :=
  (2 : ℂ) * z / (1 - Complex.normSq z)

/-- The Krein--Cayley pair coefficient recovers the literal Davies--Fulling Bogoliubov pair
amplitude, including every nonlinear eikonal channel. -/
theorem twoModeBosonicKreinCayleyPair_fullMirrorCoordinate_eq
    (a lambda omega : ℝ) :
    twoModeBosonicKreinCayleyPair
        (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega) =
      thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega := by
  have hgp :=
    thetaCuspHawkingFullMirrorBogoliubovGain_add_one_pos a lambda omega
  have hgpC :
      (((thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1 : ℝ) : ℂ)) ≠
        0 :=
    Complex.ofReal_ne_zero.mpr hgp.ne'
  have hgpC' :
      (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega : ℂ) + 1 ≠ 0 := by
    simpa using hgpC
  have hsubC := congrArg (fun r : ℝ => (r : ℂ))
    (one_sub_normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate
      a lambda omega)
  push_cast at hsubC
  rw [twoModeBosonicKreinCayleyPair, hsubC,
    thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate]
  push_cast
  field_simp [hgpC']

/-- The Krein--Cayley positive-sheet coefficient recovers the minimal bosonic CCR gain. -/
theorem twoModeBosonicKreinCayleyGain_fullMirrorCoordinate_eq
    (a lambda omega : ℝ) :
    twoModeBosonicKreinCayleyGain
        (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega) =
      thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega := by
  have hgp :=
    thetaCuspHawkingFullMirrorBogoliubovGain_add_one_pos a lambda omega
  rw [twoModeBosonicKreinCayleyGain,
    one_add_normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate,
    one_sub_normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate,
    div_div]
  field_simp [hgp.ne']

/-- **Canonical-coordinate uniqueness.**  Any open-disk Krein--Cayley coordinate reproducing
both the actual positive gain and actual Davies--Fulling pair coefficient is the displayed
source-faithful coordinate. -/
theorem eq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate_of_gain_pair
    (a lambda omega : ℝ) {z : ℂ}
    (hz : Complex.normSq z < 1)
    (hgain : twoModeBosonicKreinCayleyGain z =
      thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega)
    (hpair : twoModeBosonicKreinCayleyPair z =
      thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega) :
    z = thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate
      a lambda omega := by
  have hden : (1 : ℝ) - Complex.normSq z ≠ 0 :=
    ne_of_gt (sub_pos.mpr hz)
  have hdenC : (((1 : ℝ) - Complex.normSq z : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  have hdenC' : (1 : ℂ) - (Complex.normSq z : ℂ) ≠ 0 := by
    simpa using hdenC
  rw [thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate,
    ← hgain, ← hpair]
  unfold twoModeBosonicKreinCayleyGain twoModeBosonicKreinCayleyPair
  push_cast
  field_simp [hden, hdenC, hdenC']
  ring_nf

/-! ## Full nonperturbative Krein--Cayley scattering matrix -/

/-- Positive diagonal coefficient of the exact full-mirror Krein--Cayley matrix. -/
def thetaCuspHawkingFullMirrorKreinCayleyGain
    (a lambda omega : ℝ) : ℝ :=
  twoModeBosonicKreinCayleyGain
    (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega)

/-- Off-diagonal coefficient of the exact full-mirror Krein--Cayley matrix. -/
def thetaCuspHawkingFullMirrorKreinCayleyPair
    (a lambda omega : ℝ) : ℂ :=
  twoModeBosonicKreinCayleyPair
    (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega)

theorem thetaCuspHawkingFullMirrorKreinCayleyGain_eq
    (a lambda omega : ℝ) :
    thetaCuspHawkingFullMirrorKreinCayleyGain a lambda omega =
      thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega := by
  exact twoModeBosonicKreinCayleyGain_fullMirrorCoordinate_eq a lambda omega

theorem thetaCuspHawkingFullMirrorKreinCayleyPair_eq
    (a lambda omega : ℝ) :
    thetaCuspHawkingFullMirrorKreinCayleyPair a lambda omega =
      thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega := by
  exact twoModeBosonicKreinCayleyPair_fullMirrorCoordinate_eq a lambda omega

/-- Exterior Nambu output of the exact Krein--Cayley matrix. -/
def thetaCuspHawkingFullMirrorKreinCayleyExteriorOutput
    (a lambda omega : ℝ) (x h : ℂ) : ℂ :=
  (thetaCuspHawkingFullMirrorKreinCayleyGain a lambda omega : ℂ) * x +
    thetaCuspHawkingFullMirrorKreinCayleyPair a lambda omega * h

/-- Partner Nambu output of the exact Krein--Cayley matrix. -/
def thetaCuspHawkingFullMirrorKreinCayleyPartnerOutput
    (a lambda omega : ℝ) (x h : ℂ) : ℂ :=
  conj (thetaCuspHawkingFullMirrorKreinCayleyPair a lambda omega) * x +
    (thetaCuspHawkingFullMirrorKreinCayleyGain a lambda omega : ℂ) * h

/-- Krein--Cayley exterior output is definitionally the full physical Bogoliubov output after
the exact coefficient recovery. -/
theorem thetaCuspHawkingFullMirrorKreinCayleyExteriorOutput_eq
    (a lambda omega : ℝ) (x h : ℂ) :
    thetaCuspHawkingFullMirrorKreinCayleyExteriorOutput
        a lambda omega x h =
      thetaCuspHawkingFullMirrorBogoliubovExteriorOutput
        a lambda omega x h := by
  rw [thetaCuspHawkingFullMirrorKreinCayleyExteriorOutput,
    thetaCuspHawkingFullMirrorKreinCayleyGain_eq,
    thetaCuspHawkingFullMirrorKreinCayleyPair_eq]
  rfl

/-- Krein--Cayley partner output is the full physical Bogoliubov partner output. -/
theorem thetaCuspHawkingFullMirrorKreinCayleyPartnerOutput_eq
    (a lambda omega : ℝ) (x h : ℂ) :
    thetaCuspHawkingFullMirrorKreinCayleyPartnerOutput
        a lambda omega x h =
      thetaCuspHawkingFullMirrorBogoliubovPartnerOutput
        a lambda omega x h := by
  rw [thetaCuspHawkingFullMirrorKreinCayleyPartnerOutput,
    thetaCuspHawkingFullMirrorKreinCayleyGain_eq,
    thetaCuspHawkingFullMirrorKreinCayleyPair_eq]
  rfl

theorem thetaCuspHawkingFullMirrorKreinCayley_isTwoModeBosonicCCR
    (a lambda omega : ℝ) :
    IsTwoModeBosonicCCR
      (thetaCuspHawkingFullMirrorKreinCayleyGain a lambda omega)
      (thetaCuspHawkingFullMirrorKreinCayleyPair a lambda omega) := by
  rw [thetaCuspHawkingFullMirrorKreinCayleyGain_eq,
    thetaCuspHawkingFullMirrorKreinCayleyPair_eq]
  exact thetaCuspHawkingFullMirrorBogoliubov_isTwoModeBosonicCCR
    a lambda omega

/-- The canonical full-mirror Krein--Cayley S-matrix preserves the Nambu signed Hermitian form. -/
theorem thetaCuspHawkingFullMirrorKreinCayley_preserves_signedHermitian
    (a lambda omega : ℝ) (x h : ℂ) :
    conj (thetaCuspHawkingFullMirrorKreinCayleyExteriorOutput
          a lambda omega x h) *
        thetaCuspHawkingFullMirrorKreinCayleyExteriorOutput
          a lambda omega x h -
      conj (thetaCuspHawkingFullMirrorKreinCayleyPartnerOutput
          a lambda omega x h) *
        thetaCuspHawkingFullMirrorKreinCayleyPartnerOutput
          a lambda omega x h =
      conj x * x - conj h * h := by
  rw [thetaCuspHawkingFullMirrorKreinCayleyExteriorOutput_eq,
    thetaCuspHawkingFullMirrorKreinCayleyPartnerOutput_eq]
  exact thetaCuspHawkingFullMirrorBogoliubov_preserves_signedHermitian
    a lambda omega x h

/-- First coordinate of the exact signed-adjoint inverse. -/
def thetaCuspHawkingFullMirrorKreinCayleyInverseExterior
    (a lambda omega : ℝ) (x h : ℂ) : ℂ :=
  (thetaCuspHawkingFullMirrorKreinCayleyGain a lambda omega : ℂ) * x -
    thetaCuspHawkingFullMirrorKreinCayleyPair a lambda omega * h

/-- Second coordinate of the exact signed-adjoint inverse. -/
def thetaCuspHawkingFullMirrorKreinCayleyInversePartner
    (a lambda omega : ℝ) (x h : ℂ) : ℂ :=
  -conj (thetaCuspHawkingFullMirrorKreinCayleyPair a lambda omega) * x +
    (thetaCuspHawkingFullMirrorKreinCayleyGain a lambda omega : ℂ) * h

/-- The canonical full-mirror Krein--Cayley matrix has the exact bosonic signed-adjoint inverse. -/
theorem thetaCuspHawkingFullMirrorKreinCayley_inverse_after_scattering
    (a lambda omega : ℝ) (x h : ℂ) :
    thetaCuspHawkingFullMirrorKreinCayleyInverseExterior a lambda omega
        (thetaCuspHawkingFullMirrorKreinCayleyExteriorOutput
          a lambda omega x h)
        (thetaCuspHawkingFullMirrorKreinCayleyPartnerOutput
          a lambda omega x h) = x ∧
      thetaCuspHawkingFullMirrorKreinCayleyInversePartner a lambda omega
        (thetaCuspHawkingFullMirrorKreinCayleyExteriorOutput
          a lambda omega x h)
        (thetaCuspHawkingFullMirrorKreinCayleyPartnerOutput
          a lambda omega x h) = h := by
  rw [thetaCuspHawkingFullMirrorKreinCayleyInverseExterior,
    thetaCuspHawkingFullMirrorKreinCayleyInversePartner,
    thetaCuspHawkingFullMirrorKreinCayleyGain_eq,
    thetaCuspHawkingFullMirrorKreinCayleyPair_eq,
    thetaCuspHawkingFullMirrorKreinCayleyExteriorOutput_eq,
    thetaCuspHawkingFullMirrorKreinCayleyPartnerOutput_eq]
  exact thetaCuspHawkingFullMirrorBogoliubov_inverse_after_scattering
    a lambda omega x h

/-! ## Exact finite-coupling resonance-sector mixing -/

theorem thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate_eq_zero_iff
    (a lambda omega : ℝ) :
    thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega = 0 ↔
      thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega = 0 := by
  have hgp :=
    thetaCuspHawkingFullMirrorBogoliubovGain_add_one_pos a lambda omega
  have hgpC :
      (((thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1 : ℝ) : ℂ)) ≠
        0 :=
    Complex.ofReal_ne_zero.mpr hgp.ne'
  have hgpC' :
      (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega : ℂ) + 1 ≠ 0 := by
    simpa using hgpC
  simp [thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate, hgpC']

/-- One exact full-mirror resonance sector mixes in the canonical Krein--Cayley chart. -/
def ThetaCuspHawkingFullMirrorKreinCayleySectorMixes
    (a lambda omega : ℝ) : Prop :=
  thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega ≠ 0

theorem thetaCuspHawkingFullMirrorKreinCayleySectorMixes_iff_squeezes
    (a lambda omega : ℝ) :
    ThetaCuspHawkingFullMirrorKreinCayleySectorMixes a lambda omega ↔
      ThetaCuspHawkingFullMirrorBogoliubovSectorSqueezes a lambda omega := by
  simpa [ThetaCuspHawkingFullMirrorKreinCayleySectorMixes,
    ThetaCuspHawkingFullMirrorBogoliubovSectorSqueezes] using
      not_congr
        (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate_eq_zero_iff
          a lambda omega)

/-- Exact Krein--Cayley mixing is equivalent to nonvanishing of the full nonlinear
Davies--Fulling amplitude, not only its Born tangent. -/
theorem thetaCuspHawkingFullMirrorKreinCayleySectorMixes_iff_amplitude_ne_zero
    {a lambda omega : ℝ} (homega : 0 < omega) :
    ThetaCuspHawkingFullMirrorKreinCayleySectorMixes a lambda omega ↔
      thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega ≠ 0 := by
  rw [thetaCuspHawkingFullMirrorKreinCayleySectorMixes_iff_squeezes,
    thetaCuspHawkingFullMirrorBogoliubovSectorSqueezes_iff homega]

/-- **Unconditional all-sector branch.**  One common arbitrarily weak physical mirror coupling
activates every member of any countable tilted resonance family in the exact nonperturbative
Krein--Cayley S-matrix. -/
theorem exists_arbitrarily_weak_common_thetaCuspHawkingFullMirrorKreinCayley_mix
    {ι : Type*} [Countable ι] [Nonempty ι]
    (a omega : ι → ℝ) (ha : ∀ i, |a i| < 1)
    (homega : ∀ i, 0 < omega i) (ε : ℝ) (hε : 0 < ε) :
    ∃ lambda : ℝ, 0 < |lambda| ∧ |lambda| < ε ∧
      ∀ i, ThetaCuspHawkingFullMirrorKreinCayleySectorMixes
        (a i) lambda (omega i) := by
  obtain ⟨lambda, hlambda0, hlambdaε, hall⟩ :=
    exists_arbitrarily_weak_common_thetaCuspHawkingFullMirrorBogoliubov_squeeze
      a omega ha homega ε hε
  exact ⟨lambda, hlambda0, hlambdaε, fun i =>
    (thetaCuspHawkingFullMirrorKreinCayleySectorMixes_iff_squeezes
      (a i) lambda (omega i)).2 (hall i)⟩

/-! ## Standard-clock selection and unchanged RH obstruction -/

/-- Krein--Cayley disk intensity per unit standard van-Hove time. -/
def thetaCuspHawkingFullMirrorKreinCayleyVanHoveRate
    (a lambda omega : ℝ) : ℝ :=
  Complex.normSq
      (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega) /
    lambda ^ 2

theorem thetaCuspHawkingFullMirrorKreinCayleyVanHoveRate_eq
    (a lambda omega : ℝ) :
    thetaCuspHawkingFullMirrorKreinCayleyVanHoveRate a lambda omega =
      thetaCuspHawkingFullMirrorBogoliubovVanHoveRate a lambda omega /
        (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1) ^ 2 := by
  rw [thetaCuspHawkingFullMirrorKreinCayleyVanHoveRate,
    normSq_thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate,
    thetaCuspHawkingFullMirrorBogoliubovVanHoveRate]
  ring_nf

private theorem thetaCuspHawkingBalancedFullMirrorAmplitude_zero_coupling
    {a : ℝ} (ha : |a| < 1) (omega : ℝ) :
    thetaCuspHawkingBalancedFullMirrorAmplitude a 0 omega = 0 := by
  rw [thetaCuspHawkingBalancedFullMirrorAmplitude,
    thetaCuspHawkingFullMirrorAmplitude_eq_eikonalFourier a ha]
  have hzero : thetaCuspHawkingEikonalPhaseDefect a 0 = 0 := by
    funext v
    simp [thetaCuspHawkingEikonalPhaseDefect]
  simp only [zero_mul]
  rw [thetaCuspHawkingEikonalFourier,
    Real.fourier_real_eq_integral_exp_smul, hzero]
  simp

private theorem tendsto_thetaCuspHawkingFullMirrorBogoliubovGain_one
    {a : ℝ} (ha : |a| < 1) (omega : ℝ) :
    Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hampAt : ContinuousAt
      (fun lambda : ℝ =>
        thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega) 0 :=
    (thetaCuspHawkingBalancedFullMirrorAmplitude_analyticOnNhd_coupling
      a omega ha 0 (Set.mem_univ 0)).continuousAt
  have hamp : Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    rw [← thetaCuspHawkingBalancedFullMirrorAmplitude_zero_coupling ha omega]
    exact hampAt.tendsto.mono_left inf_le_left
  have hbeta : Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa [thetaCuspHawkingFullMirrorBogoliubovBeta] using
      (tendsto_const_nhds.mul hamp)
  have hnumber : Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa [thetaCuspHawkingFullMirrorBogoliubovNumber] using
      hbeta.norm.pow 2
  have hadd : Tendsto
      (fun lambda : ℝ =>
        1 + thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.add hnumber
  have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hadd
  change Tendsto
    (fun lambda : ℝ => Real.sqrt
      (1 + thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega))
    (𝓝[≠] (0 : ℝ)) (𝓝 (Real.sqrt 1)) at hsqrt
  simpa only [Real.sqrt_one,
    thetaCuspHawkingFullMirrorBogoliubovGain] using hsqrt

/-- Exact standard-clock Krein--Cayley rate is one quarter of the physical Bogoliubov pair-rate
limit.  The factor is the derivative of the hyperbolic half-angle chart at the identity. -/
theorem tendsto_thetaCuspHawkingFullMirrorKreinCayleyVanHoveRate
    {a : ℝ} (ha : |a| < 1) (omega : ℝ) :
    Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorKreinCayleyVanHoveRate a lambda omega)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ((1 / 4 : ℝ) *
        thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate a omega)) := by
  have hnum :=
    tendsto_thetaCuspHawkingFullMirrorBogoliubovVanHoveRate a ha omega
  have hden : Tendsto
      (fun lambda : ℝ =>
        (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1) ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 4) := by
    have h :=
      ((tendsto_thetaCuspHawkingFullMirrorBogoliubovGain_one ha omega).add_const
        1).pow 2
    norm_num at h
    exact h
  have hquot := hnum.div hden (by norm_num : (4 : ℝ) ≠ 0)
  have hfun :
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorKreinCayleyVanHoveRate a lambda omega) =
      fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorBogoliubovVanHoveRate a lambda omega /
          (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1) ^ 2 := by
    funext lambda
    exact thetaCuspHawkingFullMirrorKreinCayleyVanHoveRate_eq
      a lambda omega
  rw [hfun]
  change Tendsto
    ((fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorBogoliubovVanHoveRate a lambda omega) /
      fun lambda : ℝ =>
        (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1) ^ 2)
    (𝓝[≠] (0 : ℝ))
    (𝓝 ((1 / 4 : ℝ) *
      thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate a omega))
  convert hquot using 1
  ring_nf

/-- Source coefficient selected by the Krein--Cayley disk on the common standard clock. -/
def thetaCuspHawkingFullMirrorKreinCayleyVanHoveLimitRate
    (a omega : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate a omega

theorem tendsto_thetaCuspHawkingFullMirrorKreinCayleyVanHoveLimitRate
    {a : ℝ} (ha : |a| < 1) (omega : ℝ) :
    Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorKreinCayleyVanHoveRate a lambda omega)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (thetaCuspHawkingFullMirrorKreinCayleyVanHoveLimitRate a omega)) := by
  simpa [thetaCuspHawkingFullMirrorKreinCayleyVanHoveLimitRate] using
    tendsto_thetaCuspHawkingFullMirrorKreinCayleyVanHoveRate ha omega

theorem thetaCuspHawkingFullMirrorKreinCayleyVanHoveLimitRate_pos_iff
    {a omega : ℝ} (homega : 0 < omega) :
    0 < thetaCuspHawkingFullMirrorKreinCayleyVanHoveLimitRate a omega ↔
      XiC ((omega : ℂ) + (a : ℂ) * Complex.I) ≠ 0 := by
  have hquarter : 0 < (1 / 4 : ℝ) := by norm_num
  rw [thetaCuspHawkingFullMirrorKreinCayleyVanHoveLimitRate]
  constructor
  · intro hpos
    have hbog :
        0 < thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate a omega :=
      pos_of_mul_pos_right hpos hquarter.le
    exact (thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate_pos_iff
      homega).1 hbog
  · intro hXi
    exact mul_pos hquarter
      ((thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate_pos_iff
        homega).2 hXi)

/-- Every noncentral tilted sector has positive Krein--Cayley disk rate on the same physical
standard Hawking clock. -/
def ThetaCuspHawkingFullMirrorKreinCayleyStandardClockMixing : Prop :=
  ∀ (a omega : ℝ), 0 < omega → |a| < 1 → a ≠ 0 →
    0 < thetaCuspHawkingFullMirrorKreinCayleyVanHoveLimitRate a omega

/-- **[BRIDGE] Correct-signature full-mirror Cayley endpoint.**  The full nonlinear theta mirror
selects its unique bosonic Krein--Cayley chart unconditionally.  RH remains exactly universal
nondegeneracy of that chart on the common first-order Davies clock; finite-coupling mixing alone
is already unconditional. -/
theorem riemannHypothesis_iff_thetaCuspHawkingFullMirrorKreinCayleyStandardClockMixing :
    RiemannHypothesis ↔
      ThetaCuspHawkingFullMirrorKreinCayleyStandardClockMixing := by
  rw [riemannHypothesis_iff_thetaCuspHawkingFullMirrorBogoliubovStandardClockPairProduction]
  constructor
  · intro hproduction a omega homega ha hane
    rw [thetaCuspHawkingFullMirrorKreinCayleyVanHoveLimitRate]
    exact mul_pos (by norm_num) (hproduction a omega homega ha hane)
  · intro hmixing a omega homega ha hane
    have hpos := hmixing a omega homega ha hane
    rw [thetaCuspHawkingFullMirrorKreinCayleyVanHoveLimitRate] at hpos
    exact pos_of_mul_pos_right hpos (by norm_num)

end RHTower
