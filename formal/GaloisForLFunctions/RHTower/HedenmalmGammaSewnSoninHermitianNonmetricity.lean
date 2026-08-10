import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSoninEscapeConservation
import GaloisForLFunctions.RHTower.GammaCoPoissonSoninQuadrantFlatness

/-!
# Flat co-Poisson connection, nonzero Route N Hermitian nonmetricity

Full-quotient flatness kills every two-path curvature before zero specialization.  It therefore
cannot orient an off-line Xi conormal.  The surviving invariant is instead the Hermitian trace
excess of the two reciprocal Sonin edges.  For the Route N Kadison defect `D_t(p)` define

`M_t(p) = D_t(p)^2 / (1 - D_t(p))`.

The defect--escape conservation law gives

`M_t(p) = A_t(p) + A_t(p)⁻¹ - 2`.

Thus reflection reverses edge orientation but preserves a nonnegative nonmetricity energy, which
vanishes exactly at critical grade.  At every actual strict-right zeta zero the two literal
co-Poisson edge images have normalized squared energy exactly `2 + M_t(p)`, and hence strictly
exceed the balanced value `2`.  Flatness and metric compatibility are therefore independent:
the former is unconditional, while imposing the latter on every zero conormal is another RH
receiver.
-/

open Complex Real
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Hermitian trace nonmetricity of the reciprocal Sonin edge pair. -/
def routeNGammaSewnSoninHermitianNonmetricity
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  routeNGammaSewnProjectiveKadisonDefect t p ^ 2 /
    (1 - routeNGammaSewnProjectiveKadisonDefect t p)

/-- Hermitian nonmetricity is nonnegative. -/
theorem routeNGammaSewnSoninHermitianNonmetricity_nonneg
    (t : ℝ) (p : Nat.Primes) :
    0 ≤ routeNGammaSewnSoninHermitianNonmetricity t p := by
  have hD := routeNGammaSewnProjectiveKadisonDefect_mem_Ico t p
  exact div_nonneg (sq_nonneg _) (sub_nonneg.mpr hD.2.le)

/-- Hermitian compatibility occurs exactly at neutral Route N grade. -/
theorem routeNGammaSewnSoninHermitianNonmetricity_eq_zero_iff
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnSoninHermitianNonmetricity t p = 0 ↔ t = 0 := by
  have hD := routeNGammaSewnProjectiveKadisonDefect_mem_Ico t p
  have hden : 1 - routeNGammaSewnProjectiveKadisonDefect t p ≠ 0 := by
    linarith [hD.2]
  constructor
  · intro hzero
    rw [routeNGammaSewnSoninHermitianNonmetricity, div_eq_zero_iff] at hzero
    rcases hzero with hsq | hbad
    · have hdefect : routeNGammaSewnProjectiveKadisonDefect t p = 0 := by
        nlinarith
      exact (routeNGammaSewnProjectiveKadisonDefect_eq_zero_iff t p).mp hdefect
    · exact False.elim (hden hbad)
  · intro ht
    subst t
    rw [routeNGammaSewnSoninHermitianNonmetricity,
      (routeNGammaSewnProjectiveKadisonDefect_eq_zero_iff 0 p).mpr rfl]
    norm_num

/-- **Escape/nonmetricity law.**  Hermitian trace excess is the symmetric excess of the
reciprocal Sonin amplification pair. -/
theorem routeNGammaSewnSoninHermitianNonmetricity_eq_escape_add_inv_sub_two
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnSoninHermitianNonmetricity t p =
      routeNGammaSewnSoninEscapeAmplification t p +
        (routeNGammaSewnSoninEscapeAmplification t p)⁻¹ - 2 := by
  let D := routeNGammaSewnProjectiveKadisonDefect t p
  let S := 1 - D
  let A := routeNGammaSewnSoninEscapeAmplification t p
  have hD := routeNGammaSewnProjectiveKadisonDefect_mem_Ico t p
  have hS : 0 < S := by
    dsimp [S, D]
    linarith [hD.2]
  have hSA : S * A = 1 := by
    dsimp [S, D, A]
    exact routeNGammaSewnKadisonSurvival_mul_soninEscape_eq_one t p
  have hAeq : A = S⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hSA)
  change D ^ 2 / S = A + A⁻¹ - 2
  rw [hAeq, inv_inv]
  field_simp [hS.ne']
  dsimp [S]
  ring

/-- Functional-equation reflection reverses orientation but preserves Hermitian nonmetricity. -/
theorem routeNGammaSewnSoninHermitianNonmetricity_neg
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnSoninHermitianNonmetricity (-t) p =
      routeNGammaSewnSoninHermitianNonmetricity t p := by
  simp [routeNGammaSewnSoninHermitianNonmetricity,
    routeNGammaSewnProjectiveKadisonDefect_eq_one_sub_rpow]

/-- **Paired-character trace law.**  On the right half-strip the two reciprocal Sonin characters
have total squared amplitude `2` plus the exact Route N Hermitian nonmetricity. -/
theorem normSq_soninLadderCharacter_add_inv_eq_two_add_routeNNonmetricity
    {w : ℂ} (hw : 1 / 2 ≤ w.re) (p : Nat.Primes) :
    ‖soninLadderCharacter w (p : ℝ)‖ ^ 2 +
        (‖soninLadderCharacter w (p : ℝ)‖⁻¹) ^ 2 =
      2 + routeNGammaSewnSoninHermitianNonmetricity
        (w.re - 1 / 2) p := by
  let D := routeNGammaSewnProjectiveKadisonDefect (w.re - 1 / 2) p
  let S := 1 - D
  let L := ‖soninLadderCharacter w (p : ℝ)‖
  have hD := routeNGammaSewnProjectiveKadisonDefect_mem_Ico
    (w.re - 1 / 2) p
  have hS : 0 < S := by
    dsimp [S, D]
    linarith [hD.2]
  have hL : 0 < L := norm_soninLadderCharacter_pos
    (by exact_mod_cast p.2.pos) w
  have hSL : S * L ^ 2 = 1 := by
    dsimp [S, D, L]
    exact routeNGammaSewnKadisonSurvival_mul_rightSoninCharacter_sq hw p
  have hL2 : L ^ 2 = S⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hSL)
  change L ^ 2 + (L⁻¹) ^ 2 = 2 + D ^ 2 / S
  rw [inv_pow, hL2, inv_inv]
  field_simp [hS.ne']
  dsimp [S]
  ring

/-- Above the critical line, paired-character energy is strictly larger than its balanced value. -/
theorem two_lt_normSq_soninLadderCharacter_add_inv
    {w : ℂ} (hw : 1 / 2 < w.re) (p : Nat.Primes) :
    2 < ‖soninLadderCharacter w (p : ℝ)‖ ^ 2 +
        (‖soninLadderCharacter w (p : ℝ)‖⁻¹) ^ 2 := by
  rw [normSq_soninLadderCharacter_add_inv_eq_two_add_routeNNonmetricity hw.le p]
  have ht : w.re - 1 / 2 ≠ 0 := by linarith
  have hMne : routeNGammaSewnSoninHermitianNonmetricity
      (w.re - 1 / 2) p ≠ 0 := by
    intro hzero
    exact ht ((routeNGammaSewnSoninHermitianNonmetricity_eq_zero_iff _ _).mp hzero)
  have hMpos : 0 < routeNGammaSewnSoninHermitianNonmetricity
      (w.re - 1 / 2) p :=
    lt_of_le_of_ne
      (routeNGammaSewnSoninHermitianNonmetricity_nonneg _ _) (Ne.symm hMne)
  linarith

/-- **Literal paired-edge energy law at an actual zero.**  The forward and inverse images of one
co-Poisson conormal step have total squared energy `2 + M_t(p)` times the preceding conormal
energy.  The formula is independent of aperture and level. -/
theorem normSq_coPoissonPairedEdges_eq_two_add_routeNNonmetricity_mul
    {w : ℂ} {a : ℝ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} (p : Nat.Primes) (hz : riemannZeta w = 0) (j : ℕ) :
    ‖coPoissonQuotientForward a (p : ℝ) ha (by exact_mod_cast p.2.pos) j
        (coPoissonLadderKernel w hlo hhi a (p : ℝ) ha
          (by exact_mod_cast p.2.pos) (j + 1))‖ ^ 2 +
      ‖coPoissonQuotientInverse a (p : ℝ) ha (by exact_mod_cast p.2.pos) j
        (coPoissonLadderKernel w hlo hhi a (p : ℝ) ha
          (by exact_mod_cast p.2.pos) (j + 1))‖ ^ 2 =
      (2 + routeNGammaSewnSoninHermitianNonmetricity
        (w.re - 1 / 2) p) *
        ‖coPoissonLadderKernel w hlo hhi a (p : ℝ) ha
          (by exact_mod_cast p.2.pos) j‖ ^ 2 := by
  let hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  let hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  have hann : CoPoissonLadderAnnihilator w hlo hhi a (p : ℝ) ha hp0 :=
    coPoissonLadderAnnihilator_of_riemannZeta_eq_zero hz
  rw [coPoissonQuotientForward_ladderKernel hp1 hann j,
    coPoissonQuotientInverse_ladderKernel hp1 hann j,
    norm_smul, norm_smul, RCLike.norm_conj, RCLike.norm_conj, norm_inv]
  let L := ‖soninLadderCharacter w (p : ℝ)‖
  let Y := ‖coPoissonLadderKernel w hlo hhi a (p : ℝ) ha hp0 j‖
  have hchar :=
    normSq_soninLadderCharacter_add_inv_eq_two_add_routeNNonmetricity hlo.le p
  change (L * Y) ^ 2 + (L⁻¹ * Y) ^ 2 =
    (2 + routeNGammaSewnSoninHermitianNonmetricity
      (w.re - 1 / 2) p) * Y ^ 2
  calc
    (L * Y) ^ 2 + (L⁻¹ * Y) ^ 2 =
        (L ^ 2 + (L⁻¹) ^ 2) * Y ^ 2 := by ring
    _ = (2 + routeNGammaSewnSoninHermitianNonmetricity
          (w.re - 1 / 2) p) * Y ^ 2 := by
      rw [hchar]

/-- **Strict metric incompatibility at an actual strict-right zero.**  At the initial aperture,
the paired edge energy is strictly larger than twice the preceding conormal energy. -/
theorem two_mul_normSq_coPoissonLadderKernel_lt_normSq_pairedEdges
    {w : ℂ} {a : ℝ} {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} (ha1 : a < 1) (p : Nat.Primes) (hz : riemannZeta w = 0) :
    2 * ‖coPoissonLadderKernel w hlo hhi a (p : ℝ) ha
          (by exact_mod_cast p.2.pos) 0‖ ^ 2 <
      ‖coPoissonQuotientForward a (p : ℝ) ha (by exact_mod_cast p.2.pos) 0
        (coPoissonLadderKernel w hlo hhi a (p : ℝ) ha
          (by exact_mod_cast p.2.pos) 1)‖ ^ 2 +
      ‖coPoissonQuotientInverse a (p : ℝ) ha (by exact_mod_cast p.2.pos) 0
        (coPoissonLadderKernel w hlo hhi a (p : ℝ) ha
          (by exact_mod_cast p.2.pos) 1)‖ ^ 2 := by
  let hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hann : CoPoissonLadderAnnihilator w hlo hhi a (p : ℝ) ha hp0 :=
    coPoissonLadderAnnihilator_of_riemannZeta_eq_zero hz
  have hb1 : soninAperture a (p : ℝ) 0 < 1 := by
    simpa only [soninAperture_zero] using ha1
  have hambient := burnolExtendedSoninEvaluationVector_ne_zero
    hlo hhi (soninAperture_pos ha hp0 0) hb1
  have hsonin : soninLadderKernel w hlo hhi a (p : ℝ) ha hp0 0 ≠ 0 := by
    intro hk
    apply hambient
    apply Subtype.ext
    exact hk
  have hkernel : coPoissonLadderKernel w hlo hhi a (p : ℝ) ha hp0 0 ≠ 0 := by
    rw [coPoissonLadderKernel_eq_soninLadderKernel hann 0]
    exact hsonin
  let Y := ‖coPoissonLadderKernel w hlo hhi a (p : ℝ) ha hp0 0‖
  have hY : 0 < Y := norm_pos_iff.mpr hkernel
  have ht : w.re - 1 / 2 ≠ 0 := by linarith
  have hMne : routeNGammaSewnSoninHermitianNonmetricity
      (w.re - 1 / 2) p ≠ 0 := by
    intro hzero
    exact ht ((routeNGammaSewnSoninHermitianNonmetricity_eq_zero_iff _ _).mp hzero)
  have hMpos : 0 < routeNGammaSewnSoninHermitianNonmetricity
      (w.re - 1 / 2) p :=
    lt_of_le_of_ne
      (routeNGammaSewnSoninHermitianNonmetricity_nonneg _ _) (Ne.symm hMne)
  have hpair := normSq_coPoissonPairedEdges_eq_two_add_routeNNonmetricity_mul
    (w := w) (a := a) (hlo := hlo) (hhi := hhi) (ha := ha) p hz 0
  change 2 * Y ^ 2 < _
  change _ = (2 + routeNGammaSewnSoninHermitianNonmetricity
    (w.re - 1 / 2) p) * Y ^ 2 at hpair
  rw [hpair]
  nlinarith [sq_pos_of_pos hY]

end

end RHTower
