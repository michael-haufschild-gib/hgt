import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSoninHermitianNonmetricity
import GaloisForLFunctions.RHTower.BurnolBilateralApertureRH
import GaloisForLFunctions.RHTower.GammaCoPoissonSoninActualZeroEscape

/-!
# Route N nonmetricity and Burnol holonomy lie on one mass shell

At an actual right-half zeta zero and prime dilation ratio, the normalized Burnol bilateral
aperture holonomy is exactly the oriented difference of the Route N Sonin escape amplification
and its inverse:

`H = A - A⁻¹`.

The C24 Hermitian nonmetricity is the complementary trace coordinate

`M = A + A⁻¹ - 2`.

Consequently the two satisfy the exact hyperbolic mass-shell equation

`H² = M (M + 4)`.

Equivalently, `H = D(2-D)/(1-D)` for the projective Kadison defect `D`.  Thus the Route N
positive fracture and Route R signed finite-holonomy obstruction are not independent pressures:
they are the trace and orientation coordinates of the same reciprocal transport.  Reflection
reverses `H` while preserving `M`; neither flatness nor reflection makes either coordinate vanish.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- **Zero-fibre orientation coordinate.**  At prime dilation ratio, normalized Burnol holonomy
is the oriented difference of Sonin escape and inverse escape. -/
theorem burnolCoPoissonNormalizedHolonomy_eq_routeNSoninEscape_sub_inv
    {w : ℂ} {a : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (ha : 0 < a) (ha1 : a < 1) (p : Nat.Primes) (hz : riemannZeta w = 0) :
    burnolCoPoissonNormalizedHolonomy (r := (p : ℝ)) hlo hhi ha
        (by exact_mod_cast p.2.one_lt) =
      routeNGammaSewnSoninEscapeAmplification (w.re - 1 / 2) p -
        (routeNGammaSewnSoninEscapeAmplification (w.re - 1 / 2) p)⁻¹ := by
  let hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  let hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  let hb : 0 < (p : ℝ)⁻¹ * a := mul_pos (inv_pos.mpr hp0) ha
  have hann : BurnolCoPoissonAnnihilatorPoint w ((p : ℝ)⁻¹ * a) hlo hhi hb :=
    burnolCoPoissonAnnihilatorPoint_of_riemannZeta_eq_zero hlo hhi hb hz
  have hk : burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 :=
    burnolExtendedSoninEvaluationVector_ne_zero hlo hhi ha ha1
  rw [burnolCoPoissonNormalizedHolonomy_eq_of_annihilator hlo hhi ha hp1 hann hk,
    routeNGammaSewnSoninEscapeAmplification_eq_rpow]
  have ht : 0 < w.re - 1 / 2 := by linarith
  rw [abs_of_pos ht, ← Real.rpow_neg hp0.le]
  congr 2 <;> ring

/-- **Route N--Route R hyperbolic mass shell.**  Squared normalized Burnol holonomy is exactly
`M(M+4)`, where `M` is the Route N Hermitian nonmetricity. -/
theorem sq_burnolCoPoissonNormalizedHolonomy_eq_routeNNonmetricity_massShell
    {w : ℂ} {a : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (ha : 0 < a) (ha1 : a < 1) (p : Nat.Primes) (hz : riemannZeta w = 0) :
    burnolCoPoissonNormalizedHolonomy (r := (p : ℝ)) hlo hhi ha
        (by exact_mod_cast p.2.one_lt) ^ 2 =
      routeNGammaSewnSoninHermitianNonmetricity (w.re - 1 / 2) p *
        (routeNGammaSewnSoninHermitianNonmetricity (w.re - 1 / 2) p + 4) := by
  rw [burnolCoPoissonNormalizedHolonomy_eq_routeNSoninEscape_sub_inv
      hlo hhi ha ha1 p hz,
    routeNGammaSewnSoninHermitianNonmetricity_eq_escape_add_inv_sub_two]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hApos : 0 < routeNGammaSewnSoninEscapeAmplification
      (w.re - 1 / 2) p := by
    rw [routeNGammaSewnSoninEscapeAmplification_eq_rpow]
    exact Real.rpow_pos_of_pos hp0 _
  nlinarith [mul_inv_cancel₀ hApos.ne']

/-- **Kadison rationalization of Burnol holonomy.**  The same oriented source holonomy is the
projective defect times its complementary factor, divided by projective survival. -/
theorem burnolCoPoissonNormalizedHolonomy_eq_routeNKadisonDefect_mul
    {w : ℂ} {a : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (ha : 0 < a) (ha1 : a < 1) (p : Nat.Primes) (hz : riemannZeta w = 0) :
    burnolCoPoissonNormalizedHolonomy (r := (p : ℝ)) hlo hhi ha
        (by exact_mod_cast p.2.one_lt) =
      routeNGammaSewnProjectiveKadisonDefect (w.re - 1 / 2) p *
        (2 - routeNGammaSewnProjectiveKadisonDefect (w.re - 1 / 2) p) /
          (1 - routeNGammaSewnProjectiveKadisonDefect (w.re - 1 / 2) p) := by
  rw [burnolCoPoissonNormalizedHolonomy_eq_routeNSoninEscape_sub_inv
    hlo hhi ha ha1 p hz]
  let D := routeNGammaSewnProjectiveKadisonDefect (w.re - 1 / 2) p
  let S := 1 - D
  let A := routeNGammaSewnSoninEscapeAmplification (w.re - 1 / 2) p
  have hD := routeNGammaSewnProjectiveKadisonDefect_mem_Ico
    (w.re - 1 / 2) p
  have hS : 0 < S := by
    dsimp [S, D]
    linarith [hD.2]
  have hSA : S * A = 1 := by
    dsimp [S, D, A]
    exact routeNGammaSewnKadisonSurvival_mul_soninEscape_eq_one _ _
  have hAeq : A = S⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hSA)
  change A - A⁻¹ = D * (2 - D) / S
  rw [hAeq, inv_inv]
  field_simp [hS.ne']
  dsimp [S]
  ring

end

end RHTower
