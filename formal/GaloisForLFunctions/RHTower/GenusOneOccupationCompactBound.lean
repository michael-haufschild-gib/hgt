import GaloisForLFunctions.RHTower.WoldGaugeCompactUniform
import GaloisForLFunctions.HTGeometry.ParityDigitAffinityExpansion

/-!
# Compact-uniform two-sided bound for the genus-one occupation phase

`(14a)` of `prime-wold-accelerated-type-modular-drift-law`.  The tangent-normalized reflected
occupation phase `Phi^(1)_S(t) = Gamma_1^S(t) / Gamma_1^S(-t)` is bounded above and below by a
constant depending only on a compact set avoiding the real occupation divisor, *uniformly in the
finite prime aperture `S`*.

The mechanism is that the reflected logarithmic defect of the genus-one primary factor,

`E(z) = log |(1-z) e^z| - log |(1+z) e^(-z)| = log|1-z| - log|1+z| + 2 Re z`,

is cubic at the origin: its linear terms cancel against the tangent counterterm and its quadratic
terms cancel by reflection.  Summed over the occupation spectrum, whose monomials are the
reciprocals of the distinct `S`-smooth integers, the cubic majorant is dominated by `∑ n^(-3)`
independently of `S`.
-/

open Complex
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions

/-- The reflected logarithmic defect of the genus-one primary factor. -/
noncomputable def reflectedPrimaryLogDefect (z : ℂ) : ℝ :=
  Real.log ‖HTGeometry.primaryFactor 1 z‖ - Real.log ‖HTGeometry.primaryFactor 1 (-z)‖

theorem norm_primaryFactor_one (z : ℂ) :
    ‖HTGeometry.primaryFactor 1 z‖ = ‖1 - z‖ * Real.exp z.re := by
  rw [primaryFactor_one_genus, norm_mul, Complex.norm_exp]

theorem normSq_one_sub (z : ℂ) : ‖(1 : ℂ) - z‖ ^ 2 = 1 - 2 * z.re + ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp [Complex.normSq_one]
  ring

theorem normSq_one_add (z : ℂ) : ‖(1 : ℂ) + z‖ ^ 2 = 1 + 2 * z.re + ‖z‖ ^ 2 := by
  have h := normSq_one_sub (-z)
  simpa [sub_neg_eq_add] using h

/-- The reflected defect in explicit coordinates. -/
theorem reflectedPrimaryLogDefect_eq {z : ℂ} (h1 : (1 : ℂ) - z ≠ 0) (h2 : (1 : ℂ) + z ≠ 0) :
    reflectedPrimaryLogDefect z
      = Real.log ‖(1 : ℂ) - z‖ - Real.log ‖(1 : ℂ) + z‖ + 2 * z.re := by
  have hn1 : ‖(1 : ℂ) - z‖ ≠ 0 := by simpa using h1
  have hn2 : ‖(1 : ℂ) + z‖ ≠ 0 := by simpa using h2
  have hneg : ‖(1 : ℂ) - -z‖ = ‖(1 : ℂ) + z‖ := by rw [sub_neg_eq_add]
  rw [reflectedPrimaryLogDefect, norm_primaryFactor_one, norm_primaryFactor_one,
    Real.log_mul hn1 (Real.exp_ne_zero _),
    hneg, Real.log_mul hn2 (Real.exp_ne_zero _), Real.log_exp, Real.log_exp,
    Complex.neg_re]
  ring

/-- **The reflected defect is cubic at the origin.**  Both the linear and the quadratic terms
cancel — the linear one against the tangent counterterm, the quadratic one by reflection. -/
theorem abs_reflectedPrimaryLogDefect_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 4) :
    |reflectedPrimaryLogDefect z| ≤ 110 * ‖z‖ ^ 3 := by
  set r := ‖z‖ with hrdef
  set u := z.re with hudef
  have hr0 : 0 ≤ r := norm_nonneg z
  have hur : |u| ≤ r := Complex.abs_re_le_norm z
  have hu1 : -r ≤ u := neg_le_of_abs_le hur
  have hu2 : u ≤ r := le_of_abs_le hur
  set a : ℝ := -(2 * u) + r ^ 2 with hadef
  set b : ℝ := 2 * u + r ^ 2 with hbdef
  have hrsq : r ^ 2 ≤ r / 4 := by nlinarith
  have habs_a : |a| ≤ 3 * r := by
    rw [abs_le]; constructor <;> nlinarith
  have habs_b : |b| ≤ 3 * r := by
    rw [abs_le]; constructor <;> nlinarith
  have h34 : (3 : ℝ) * r ≤ 3 / 4 := by linarith
  have hane : |a| ≤ 3 / 4 := le_trans habs_a h34
  have hbne : |b| ≤ 3 / 4 := le_trans habs_b h34
  have hapos : (0 : ℝ) < 1 + a := by
    have := neg_le_of_abs_le hane; linarith
  have hbpos : (0 : ℝ) < 1 + b := by
    have := neg_le_of_abs_le hbne; linarith
  have hsq1 : ‖(1 : ℂ) - z‖ ^ 2 = 1 + a := by rw [normSq_one_sub]; rw [hadef]; ring
  have hsq2 : ‖(1 : ℂ) + z‖ ^ 2 = 1 + b := by rw [normSq_one_add]; rw [hbdef]; ring
  have hne1 : (1 : ℂ) - z ≠ 0 := by
    intro h
    rw [h] at hsq1
    simp at hsq1
    linarith
  have hne2 : (1 : ℂ) + z ≠ 0 := by
    intro h
    rw [h] at hsq2
    simp at hsq2
    linarith
  have hlog1 : Real.log ‖(1 : ℂ) - z‖ = Real.log (1 + a) / 2 := by
    rw [← hsq1, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log ‖(1 : ℂ) + z‖ = Real.log (1 + b) / 2 := by
    rw [← hsq2, Real.log_pow]; push_cast; ring
  set Ea : ℝ := Real.log (1 + a) - a + a ^ 2 / 2 with hEa
  set Eb : ℝ := Real.log (1 + b) - b + b ^ 2 / 2 with hEb
  have hEabound : |Ea| ≤ 4 * |a| ^ 3 :=
    GaloisForLFunctions.HTGeometry.abs_log_one_add_taylor_le hane
  have hEbbound : |Eb| ≤ 4 * |b| ^ 3 :=
    GaloisForLFunctions.HTGeometry.abs_log_one_add_taylor_le hbne
  have hacube : |a| ^ 3 ≤ 27 * r ^ 3 := by
    have := pow_le_pow_left₀ (abs_nonneg a) habs_a 3
    nlinarith [this]
  have hbcube : |b| ^ 3 ≤ 27 * r ^ 3 := by
    have := pow_le_pow_left₀ (abs_nonneg b) habs_b 3
    nlinarith [this]
  have hkey : reflectedPrimaryLogDefect z = 2 * u * r ^ 2 + (Ea - Eb) / 2 := by
    rw [reflectedPrimaryLogDefect_eq hne1 hne2, hlog1, hlog2]
    rw [hEa, hEb, hadef, hbdef]
    ring
  rw [hkey]
  have h1 : |2 * u * r ^ 2| ≤ 2 * r ^ 3 := by
    have hr2 : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
    have hstep : |2 * u * r ^ 2| = 2 * |u| * r ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr2, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hstep]
    have : 2 * |u| * r ^ 2 ≤ 2 * r * r ^ 2 := by gcongr
    calc 2 * |u| * r ^ 2 ≤ 2 * r * r ^ 2 := this
      _ = 2 * r ^ 3 := by ring
  have h2 : |(Ea - Eb) / 2| ≤ 108 * r ^ 3 := by
    have h3 : |Ea - Eb| ≤ |Ea| + |Eb| := abs_sub _ _
    have h4 : |Ea| + |Eb| ≤ 216 * r ^ 3 := by linarith
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  calc |2 * u * r ^ 2 + (Ea - Eb) / 2| ≤ |2 * u * r ^ 2| + |(Ea - Eb) / 2| := abs_add_le _ _
    _ ≤ 2 * r ^ 3 + 108 * r ^ 3 := by linarith
    _ = 110 * r ^ 3 := by ring

/-- **Crude two-sided bound away from the divisor.**  Only finitely many occupation monomials are
large, and there the defect is controlled by the distance to the divisor. -/
theorem abs_reflectedPrimaryLogDefect_le_of_sep {z : ℂ} {δ R : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hR : ‖z‖ ≤ R)
    (h1 : δ ≤ ‖(1 : ℂ) - z‖) (h2 : δ ≤ ‖(1 : ℂ) + z‖) :
    |reflectedPrimaryLogDefect z| ≤ 2 * (-Real.log δ + Real.log (1 + R)) + 2 * R := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) hR
  have hne1 : (1 : ℂ) - z ≠ 0 := by
    intro h; rw [h] at h1; simp at h1; linarith
  have hne2 : (1 : ℂ) + z ≠ 0 := by
    intro h; rw [h] at h2; simp at h2; linarith
  have hub1 : ‖(1 : ℂ) - z‖ ≤ 1 + R := by
    calc ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ 1 + R := by simpa using hR
  have hub2 : ‖(1 : ℂ) + z‖ ≤ 1 + R := by
    calc ‖(1 : ℂ) + z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 1 + R := by simpa using hR
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ0.le hδ1
  have hlogR : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  have hlow1 : Real.log δ ≤ Real.log ‖(1 : ℂ) - z‖ := Real.log_le_log hδ0 h1
  have hlow2 : Real.log δ ≤ Real.log ‖(1 : ℂ) + z‖ := Real.log_le_log hδ0 h2
  have hhigh1 : Real.log ‖(1 : ℂ) - z‖ ≤ Real.log (1 + R) :=
    Real.log_le_log (lt_of_lt_of_le hδ0 h1) hub1
  have hhigh2 : Real.log ‖(1 : ℂ) + z‖ ≤ Real.log (1 + R) :=
    Real.log_le_log (lt_of_lt_of_le hδ0 h2) hub2
  have hre : |z.re| ≤ R := le_trans (Complex.abs_re_le_norm z) hR
  have hre1 : -R ≤ z.re := neg_le_of_abs_le hre
  have hre2 : z.re ≤ R := le_of_abs_le hre
  rw [reflectedPrimaryLogDefect_eq hne1 hne2, abs_le]
  constructor <;> linarith

/-! ## The occupation spectrum of a finite prime aperture -/

/-- The `S`-smooth integer represented by an occupation vector on the aperture `S`. -/
noncomputable def occupationSmoothIndex (S : Finset Nat.Primes) (ν : S →₀ ℕ) : ℕ :=
  primeProduct (ν.embDomain (Function.Embedding.subtype (fun p : Nat.Primes => p ∈ S)))

theorem occupationSmoothIndex_pos (S : Finset Nat.Primes) (ν : S →₀ ℕ) :
    0 < occupationSmoothIndex S ν :=
  primeProduct_pos _

theorem occupationSmoothIndex_injective (S : Finset Nat.Primes) :
    Function.Injective (occupationSmoothIndex S) := by
  intro a b h
  exact Finsupp.embDomain_injective _ (primeProduct_injective h)

/-- The occupation monomial of the inverse-prime nome family is the reciprocal of the represented
`S`-smooth integer. -/
theorem nomeMonomial_eq_inv_occupationSmoothIndex (S : Finset Nat.Primes) (ν : S →₀ ℕ) :
    HTGeometry.nomeMonomial (fun p : S => primeLinearNome p) ν
      = (((occupationSmoothIndex S ν : ℕ) : ℂ))⁻¹ := by
  have hkey : HTGeometry.nomeMonomial primeLinearNome
      (ν.embDomain (Function.Embedding.subtype (fun p : Nat.Primes => p ∈ S)))
      = HTGeometry.nomeMonomial (fun p : S => primeLinearNome p) ν := by
    unfold HTGeometry.nomeMonomial
    exact Finsupp.prod_embDomain
  rw [← hkey, nomeMonomial_primeLinearNome]
  rfl

/-! ## The compact-uniform majorant -/

/-- Smooth-index cutoff: beyond it every occupation monomial lies in the cubic regime. -/
noncomputable def woldCompactCutoff (R : ℝ) : ℕ := max ⌈4 * R⌉₊ 1

theorem woldCompactCutoff_pos (R : ℝ) : 0 < woldCompactCutoff R :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)

/-- The separation still available at the finitely many small smooth indices. -/
noncomputable def woldCompactSep (R δ : ℝ) : ℝ := min (δ / (woldCompactCutoff R : ℝ)) 1

theorem woldCompactSep_pos {R δ : ℝ} (hδ : 0 < δ) : 0 < woldCompactSep R δ := by
  have h : (0 : ℝ) < (woldCompactCutoff R : ℝ) := by
    exact_mod_cast woldCompactCutoff_pos R
  exact lt_min (div_pos hδ h) zero_lt_one

theorem woldCompactSep_le_one (R δ : ℝ) : woldCompactSep R δ ≤ 1 := min_le_right _ _

/-- The crude bound at the small smooth indices. -/
noncomputable def woldCompactCrude (R δ : ℝ) : ℝ :=
  2 * (-Real.log (woldCompactSep R δ) + Real.log (1 + R)) + 2 * R

theorem woldCompactCrude_nonneg {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    0 ≤ woldCompactCrude R δ := by
  have h1 : Real.log (woldCompactSep R δ) ≤ 0 :=
    Real.log_nonpos (woldCompactSep_pos hδ).le (woldCompactSep_le_one R δ)
  have h2 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  unfold woldCompactCrude
  linarith

/-- The compact-uniform cubic majorant amplitude. -/
noncomputable def woldCompactAmplitude (R δ : ℝ) : ℝ :=
  110 * R ^ 3 + woldCompactCrude R δ * (woldCompactCutoff R : ℝ) ^ 3

theorem woldCompactAmplitude_nonneg {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    0 ≤ woldCompactAmplitude R δ := by
  have h := woldCompactCrude_nonneg hR hδ
  unfold woldCompactAmplitude
  positivity

/-- **The cubic majorant.**  At every smooth index the reflected defect of the corresponding
occupation monomial is at most `A / n ^ 3`, with `A` depending only on the compact datum. -/
theorem abs_reflectedPrimaryLogDefect_smooth_le {R δ : ℝ} (hR : 0 ≤ R) (hδ0 : 0 < δ)
    {t : ℂ} (ht : ‖t‖ ≤ R)
    (hsep : ∀ n : ℕ, 1 ≤ n → δ ≤ ‖t - (n : ℂ)‖ ∧ δ ≤ ‖t + (n : ℂ)‖)
    {n : ℕ} (hn : 1 ≤ n) :
    |reflectedPrimaryLogDefect (t * ((n : ℂ))⁻¹)| ≤ woldCompactAmplitude R δ / (n : ℝ) ^ 3 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnorm : ‖t * ((n : ℂ))⁻¹‖ = ‖t‖ / (n : ℝ) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv]
  have hzle : ‖t * ((n : ℂ))⁻¹‖ ≤ R / (n : ℝ) := by
    rw [hnorm]; gcongr
  have hcrude := woldCompactCrude_nonneg hR hδ0
  have hcut0 : (0 : ℝ) < (woldCompactCutoff R : ℝ) := by
    exact_mod_cast woldCompactCutoff_pos R
  by_cases hbig : woldCompactCutoff R ≤ n
  · have h4R : 4 * R ≤ (n : ℝ) := by
      have h1 : (⌈4 * R⌉₊ : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast le_trans (le_max_left _ _) hbig
      exact le_trans (Nat.le_ceil _) h1
    have hquarter : ‖t * ((n : ℂ))⁻¹‖ ≤ 1 / 4 := by
      refine le_trans hzle ?_
      rw [div_le_div_iff₀ hn0 (by norm_num : (0:ℝ) < 4)]
      linarith
    have hcube := abs_reflectedPrimaryLogDefect_le hquarter
    have hmono : 110 * ‖t * ((n : ℂ))⁻¹‖ ^ 3 ≤ 110 * (R / (n : ℝ)) ^ 3 := by
      have : ‖t * ((n : ℂ))⁻¹‖ ^ 3 ≤ (R / (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) hzle 3
      linarith
    have hnum : 110 * R ^ 3 ≤ woldCompactAmplitude R δ := by
      have hpos : (0 : ℝ) ≤ woldCompactCrude R δ * (woldCompactCutoff R : ℝ) ^ 3 := by positivity
      unfold woldCompactAmplitude
      linarith
    have hfin : 110 * (R / (n : ℝ)) ^ 3 ≤ woldCompactAmplitude R δ / (n : ℝ) ^ 3 := by
      have he : 110 * (R / (n : ℝ)) ^ 3 = (110 * R ^ 3) / (n : ℝ) ^ 3 := by
        rw [div_pow]; ring
      rw [he]
      gcongr
    linarith
  · rw [not_le] at hbig
    have hle : (n : ℝ) ≤ (woldCompactCutoff R : ℝ) := by exact_mod_cast hbig.le
    have hsp := hsep n hn
    have hid1 : (1 : ℂ) - t * ((n : ℂ))⁻¹ = ((n : ℂ) - t) * ((n : ℂ))⁻¹ := by
      have hnc : ((n : ℂ)) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℂ)).2 (by omega : n ≠ 0)
      field_simp
    have hid2 : (1 : ℂ) + t * ((n : ℂ))⁻¹ = ((n : ℂ) + t) * ((n : ℂ))⁻¹ := by
      have hnc : ((n : ℂ)) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℂ)).2 (by omega : n ≠ 0)
      field_simp
    have hnorm1 : ‖(1 : ℂ) - t * ((n : ℂ))⁻¹‖ = ‖t - (n : ℂ)‖ / (n : ℝ) := by
      rw [hid1, norm_mul, norm_inv, Complex.norm_natCast, norm_sub_rev, div_eq_mul_inv]
    have hnorm2 : ‖(1 : ℂ) + t * ((n : ℂ))⁻¹‖ = ‖t + (n : ℂ)‖ / (n : ℝ) := by
      rw [hid2, norm_mul, norm_inv, Complex.norm_natCast, add_comm ((n : ℂ)) t, div_eq_mul_inv]
    have hsepdiv : woldCompactSep R δ ≤ δ / (n : ℝ) := by
      refine le_trans (min_le_left _ _) ?_
      gcongr
    have hb1 : woldCompactSep R δ ≤ ‖(1 : ℂ) - t * ((n : ℂ))⁻¹‖ := by
      rw [hnorm1]
      refine le_trans hsepdiv ?_
      gcongr
      exact hsp.1
    have hb2 : woldCompactSep R δ ≤ ‖(1 : ℂ) + t * ((n : ℂ))⁻¹‖ := by
      rw [hnorm2]
      refine le_trans hsepdiv ?_
      gcongr
      exact hsp.2
    have hzR : ‖t * ((n : ℂ))⁻¹‖ ≤ R := by
      refine le_trans hzle ?_
      rw [div_le_iff₀ hn0]
      nlinarith
    have hkey := abs_reflectedPrimaryLogDefect_le_of_sep (woldCompactSep_pos (R := R) hδ0)
      (woldCompactSep_le_one R δ) hzR hb1 hb2
    refine le_trans hkey ?_
    have hpow : (n : ℝ) ^ 3 ≤ (woldCompactCutoff R : ℝ) ^ 3 := pow_le_pow_left₀ hn0.le hle 3
    have hmul : woldCompactCrude R δ * (n : ℝ) ^ 3
        ≤ woldCompactCrude R δ * (woldCompactCutoff R : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow hcrude
    have h110 : (0 : ℝ) ≤ 110 * R ^ 3 := by positivity
    rw [show (2 * (-Real.log (woldCompactSep R δ) + Real.log (1 + R)) + 2 * R)
        = woldCompactCrude R δ from rfl]
    rw [woldCompactAmplitude, le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)]
    linarith

/-! ## The compact-uniform two-sided bound -/

theorem summable_one_div_nat_cube : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 3) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

/-- The reciprocal-cube total mass of the positive integers. -/
noncomputable def cubeTotalMass : ℝ := ∑' n : ℕ, 1 / ((n : ℝ)) ^ 3

theorem cubeTotalMass_nonneg : 0 ≤ cubeTotalMass :=
  tsum_nonneg fun n => by positivity

/-- The compact-uniform bound on the logarithm of the genus-one occupation phase. -/
noncomputable def woldCompactBound (R δ : ℝ) : ℝ := woldCompactAmplitude R δ * cubeTotalMass

theorem woldCompactBound_nonneg {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    0 ≤ woldCompactBound R δ :=
  mul_nonneg (woldCompactAmplitude_nonneg hR hδ) cubeTotalMass_nonneg

/-- **`(14a)`.**  On a compact disc of radius `R` at distance at least `δ` from every point of the
real occupation divisor, the tangent-normalized reflected occupation phase is bounded above and
below by explicit constants, **uniformly in the finite prime aperture `S`**. -/
theorem norm_finitePrimeGenusOnePolarizedPhase_two_sided
    {R δ : ℝ} (hR : 0 ≤ R) (hδ0 : 0 < δ) (S : Finset Nat.Primes) {t : ℂ}
    (ht : ‖t‖ ≤ R) (hsep : ∀ n : ℕ, 1 ≤ n → δ ≤ ‖t - (n : ℂ)‖ ∧ δ ≤ ‖t + (n : ℂ)‖) :
    Real.exp (-woldCompactBound R δ) ≤ ‖finitePrimeGenusOnePolarizedPhase S t‖ ∧
      ‖finitePrimeGenusOnePolarizedPhase S t‖ ≤ Real.exp (woldCompactBound R δ) := by
  classical
  set q : S → ℂ := fun p => primeLinearNome p with hqdef
  have hq_ne : ∀ a, q a ≠ 0 := fun a => primeLinearNome_ne_zero _
  have hq_lt : ∀ a, ‖q a‖ < 1 := fun a => norm_primeLinearNome_lt_one _
  have hsumq : Summable (fun a : S => ‖q a‖ ^ 2) := Summable.of_finite
  set Q : (S →₀ ℕ) → ℂ := HTGeometry.nomeMonomial q with hQdef
  have hQ_ne : ∀ ν, Q ν ≠ 0 := fun ν => HTGeometry.nomeMonomial_ne_zero q hq_ne ν
  have hQsum : Summable (fun ν : S →₀ ℕ => ‖Q ν‖ ^ 2) :=
    (HTGeometry.summable_nomeMonomial_pow_iff 1 q hq_lt).2 hsumq
  set idx : (S →₀ ℕ) → ℕ := occupationSmoothIndex S with hidxdef
  have hidx1 : ∀ ν, 1 ≤ idx ν := fun ν => occupationSmoothIndex_pos S ν
  have hQidx : ∀ ν, Q ν = (((idx ν : ℕ) : ℂ))⁻¹ := fun ν =>
    nomeMonomial_eq_inv_occupationSmoothIndex S ν
  -- the two occupation faces do not vanish
  have hnc : ∀ ν, ((idx ν : ℕ) : ℂ) ≠ 0 := by
    intro ν
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).2 (Nat.one_le_iff_ne_zero.mp (hidx1 ν))
  have hpf_ne : ∀ ν, HTGeometry.primaryFactor 1 (t * Q ν) ≠ 0 := by
    intro ν
    rw [primaryFactor_one_genus]
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    rw [hQidx ν]
    have hid : (1 : ℂ) - t * (((idx ν : ℕ) : ℂ))⁻¹
        = (((idx ν : ℕ) : ℂ) - t) * (((idx ν : ℕ) : ℂ))⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ (hnc ν)]
    rw [hid]
    refine mul_ne_zero ?_ (inv_ne_zero (hnc ν))
    intro h
    have hz : ‖t - ((idx ν : ℕ) : ℂ)‖ = 0 := by
      rw [norm_sub_rev]; simp [h]
    have := (hsep (idx ν) (hidx1 ν)).1
    rw [hz] at this
    linarith
  have hpf_ne' : ∀ ν, HTGeometry.primaryFactor 1 (-t * Q ν) ≠ 0 := by
    intro ν
    rw [primaryFactor_one_genus]
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    rw [hQidx ν]
    have hid : (1 : ℂ) - -t * (((idx ν : ℕ) : ℂ))⁻¹
        = (((idx ν : ℕ) : ℂ) + t) * (((idx ν : ℕ) : ℂ))⁻¹ := by
      rw [neg_mul, sub_neg_eq_add, add_mul, mul_inv_cancel₀ (hnc ν)]
    rw [hid]
    refine mul_ne_zero ?_ (inv_ne_zero (hnc ν))
    intro h
    have hz : ‖t + ((idx ν : ℕ) : ℂ)‖ = 0 := by
      rw [add_comm]; simp [h]
    have := (hsep (idx ν) (hidx1 ν)).2
    rw [hz] at this
    linarith
  -- summability of the two logarithm families
  have hsub1 : Summable (fun ν => HTGeometry.primaryFactor 1 (t * Q ν) - 1) :=
    (HTGeometry.canonicalWeightProduct_sub_one_norm_summable 1 Q hQ_ne hQsum t).of_norm
  have hsub2 : Summable (fun ν => HTGeometry.primaryFactor 1 (-t * Q ν) - 1) :=
    (HTGeometry.canonicalWeightProduct_sub_one_norm_summable 1 Q hQ_ne hQsum (-t)).of_norm
  have hlog1 : Summable (fun ν => Complex.log (HTGeometry.primaryFactor 1 (t * Q ν))) := by
    have h := Complex.summable_log_one_add_of_summable hsub1
    simpa using h
  have hlog2 : Summable (fun ν => Complex.log (HTGeometry.primaryFactor 1 (-t * Q ν))) := by
    have h := Complex.summable_log_one_add_of_summable hsub2
    simpa using h
  have hexp1 : Complex.exp (∑' ν, Complex.log (HTGeometry.primaryFactor 1 (t * Q ν)))
      = HTGeometry.infiniteMultipleEllipticGamma 1 q t := by
    rw [Complex.cexp_tsum_eq_tprod hpf_ne hlog1]
    rfl
  have hexp2 : Complex.exp (∑' ν, Complex.log (HTGeometry.primaryFactor 1 (-t * Q ν)))
      = HTGeometry.infiniteMultipleEllipticGamma 1 q (-t) := by
    rw [Complex.cexp_tsum_eq_tprod hpf_ne' hlog2]
    rfl
  -- the phase is the exponential of the difference
  have hPhi : finitePrimeGenusOnePolarizedPhase S t
      = Complex.exp ((∑' ν, Complex.log (HTGeometry.primaryFactor 1 (t * Q ν)))
        - ∑' ν, Complex.log (HTGeometry.primaryFactor 1 (-t * Q ν))) := by
    rw [Complex.exp_sub, hexp1, hexp2, finitePrimeGenusOnePolarizedPhase]
  -- the real part is the reflected defect series
  have hre1 : Summable (fun ν => (Complex.log (HTGeometry.primaryFactor 1 (t * Q ν))).re) :=
    (Complex.hasSum_re hlog1.hasSum).summable
  have hre2 : Summable (fun ν => (Complex.log (HTGeometry.primaryFactor 1 (-t * Q ν))).re) :=
    (Complex.hasSum_re hlog2.hasSum).summable
  have hdefect : ∀ ν, reflectedPrimaryLogDefect (t * Q ν)
      = (Complex.log (HTGeometry.primaryFactor 1 (t * Q ν))).re
        - (Complex.log (HTGeometry.primaryFactor 1 (-t * Q ν))).re := by
    intro ν
    rw [Complex.log_re, Complex.log_re, reflectedPrimaryLogDefect, neg_mul]
  have hsumdef : Summable (fun ν => reflectedPrimaryLogDefect (t * Q ν)) := by
    simpa [hdefect] using hre1.sub hre2
  have hnormPhi : ‖finitePrimeGenusOnePolarizedPhase S t‖
      = Real.exp (∑' ν, reflectedPrimaryLogDefect (t * Q ν)) := by
    rw [hPhi, Complex.norm_exp, Complex.sub_re, Complex.re_tsum hlog1, Complex.re_tsum hlog2,
      ← hre1.tsum_sub hre2]
    exact congrArg Real.exp (tsum_congr fun ν => (hdefect ν).symm)
  -- the majorant
  have hmaj : ∀ ν, |reflectedPrimaryLogDefect (t * Q ν)|
      ≤ woldCompactAmplitude R δ / ((idx ν : ℕ) : ℝ) ^ 3 := by
    intro ν
    rw [hQidx ν]
    exact abs_reflectedPrimaryLogDefect_smooth_le hR hδ0 ht hsep (hidx1 ν)
  have hgsum : Summable (fun n : ℕ => woldCompactAmplitude R δ / ((n : ℝ)) ^ 3) := by
    have h := summable_one_div_nat_cube.mul_left (woldCompactAmplitude R δ)
    refine h.congr (fun n => ?_)
    rw [mul_one_div]
  have hfsum : Summable (fun ν : S →₀ ℕ => woldCompactAmplitude R δ / ((idx ν : ℕ) : ℝ) ^ 3) :=
    hgsum.comp_injective (occupationSmoothIndex_injective S)
  have habs_sum : Summable (fun ν => |reflectedPrimaryLogDefect (t * Q ν)|) :=
    hfsum.of_nonneg_of_le (fun ν => abs_nonneg _) hmaj
  have hchain : ∑' ν, |reflectedPrimaryLogDefect (t * Q ν)| ≤ woldCompactBound R δ := by
    have h1 : ∑' ν, |reflectedPrimaryLogDefect (t * Q ν)|
        ≤ ∑' ν : S →₀ ℕ, woldCompactAmplitude R δ / ((idx ν : ℕ) : ℝ) ^ 3 :=
      habs_sum.tsum_le_tsum hmaj hfsum
    have h2 : ∑' ν : S →₀ ℕ, woldCompactAmplitude R δ / ((idx ν : ℕ) : ℝ) ^ 3
        ≤ ∑' n : ℕ, woldCompactAmplitude R δ / ((n : ℝ)) ^ 3 := by
      refine hfsum.tsum_le_tsum_of_inj idx (occupationSmoothIndex_injective S)
        (fun c _ => div_nonneg (woldCompactAmplitude_nonneg hR hδ0) (by positivity))
        (fun ν => le_of_eq rfl) hgsum
    have h3 : ∑' n : ℕ, woldCompactAmplitude R δ / ((n : ℝ)) ^ 3 = woldCompactBound R δ := by
      rw [woldCompactBound, cubeTotalMass, ← tsum_mul_left]
      exact tsum_congr fun n => by rw [div_eq_mul_one_div]
    linarith
  have hfinal : |∑' ν, reflectedPrimaryLogDefect (t * Q ν)| ≤ woldCompactBound R δ := by
    refine le_trans ?_ hchain
    have := norm_tsum_le_tsum_norm (f := fun ν => reflectedPrimaryLogDefect (t * Q ν))
      (by simpa using habs_sum)
    simpa using this
  rw [hnormPhi]
  constructor
  · exact Real.exp_le_exp.mpr (neg_le_of_abs_le hfinal)
  · exact Real.exp_le_exp.mpr (le_of_abs_le hfinal)

/-! ## `(14c)` with every hypothesis discharged -/

/-- The two entrywise maxima of the finite-aperture comparison `(14b)`. -/
noncomputable def blockComparisonGauge (S : Finset Nat.Primes) (t : ℂ) : ℝ :=
  max
    (max ‖finitePrimeGenusOnePolarizedPhase S t‖
      (Real.exp (2 * t.re / finitePrimeWoldBoundaryVolume S)))
    (max ‖finitePrimeGenusOnePolarizedPhase S t‖⁻¹
      (Real.exp (-(2 * t.re / finitePrimeWoldBoundaryVolume S))))

theorem one_le_blockComparisonGauge {S : Finset Nat.Primes} {t : ℂ}
    (h : finitePrimeGenusOnePolarizedPhase S t ≠ 0) : 1 ≤ blockComparisonGauge S t := by
  set φ := ‖finitePrimeGenusOnePolarizedPhase S t‖ with hφ
  have hφ0 : 0 < φ := norm_pos_iff.mpr h
  rcases le_or_gt 1 φ with h1 | h1
  · exact le_trans (le_trans h1 (le_max_left _ _)) (le_max_left _ _)
  · have : 1 ≤ φ⁻¹ := by
      rw [le_inv_comm₀ zero_lt_one hφ0]
      simpa using h1.le
    exact le_trans (le_trans this (le_max_left _ _)) (le_max_right _ _)

/-- **`(14c)`, unconditional.**  With `(14a)` proved, the finite-aperture comparison's gauge
logarithm is at most `log C_K + 2 M_K / eps_S`, with `C_K` and `M_K` depending only on the compact
datum and not on the aperture `S`. -/
theorem log_blockComparisonGauge_le
    {R δ : ℝ} (hR : 0 ≤ R) (hδ0 : 0 < δ) (S : Finset Nat.Primes) {t : ℂ}
    (ht : ‖t‖ ≤ R) (hsep : ∀ n : ℕ, 1 ≤ n → δ ≤ ‖t - (n : ℂ)‖ ∧ δ ≤ ‖t + (n : ℂ)‖) :
    Real.log (blockComparisonGauge S t)
      ≤ woldCompactBound R δ + 2 * R / finitePrimeWoldBoundaryVolume S := by
  obtain ⟨hlow, hup⟩ := norm_finitePrimeGenusOnePolarizedPhase_two_sided hR hδ0 S ht hsep
  have hC : (1 : ℝ) ≤ Real.exp (woldCompactBound R δ) :=
    Real.one_le_exp (woldCompactBound_nonneg hR hδ0)
  have hlow' : (Real.exp (woldCompactBound R δ))⁻¹
      ≤ ‖finitePrimeGenusOnePolarizedPhase S t‖ := by
    rw [← Real.exp_neg]; exact hlow
  have htre : |t.re| ≤ R := le_trans (Complex.abs_re_le_norm t) ht
  have h := log_max_blockComparison_le hC hlow' hup htre
  rw [Real.log_exp] at h
  exact h

/-- The phase never vanishes on the compact datum. -/
theorem finitePrimeGenusOnePolarizedPhase_ne_zero
    {R δ : ℝ} (hR : 0 ≤ R) (hδ0 : 0 < δ) (S : Finset Nat.Primes) {t : ℂ}
    (ht : ‖t‖ ≤ R) (hsep : ∀ n : ℕ, 1 ≤ n → δ ≤ ‖t - (n : ℂ)‖ ∧ δ ≤ ‖t + (n : ℂ)‖) :
    finitePrimeGenusOnePolarizedPhase S t ≠ 0 := by
  obtain ⟨hlow, -⟩ := norm_finitePrimeGenusOnePolarizedPhase_two_sided hR hδ0 S ht hsep
  intro h
  rw [h] at hlow
  simp only [norm_zero] at hlow
  exact absurd hlow (not_le.mpr (Real.exp_pos _))

/-- **Section 5.1's compact-uniform conclusion, unconditional.**  The literal full-clock plus
Wold–Gamma determinant comparison has compact-uniform accelerated type zero. -/
theorem tendsto_mertensProduct_mul_ell2_blockComparisonGauge
    {R δ : ℝ} (hR : 0 ≤ R) (hδ0 : 0 < δ) {t : ℂ}
    (ht : ‖t‖ ≤ R) (hsep : ∀ n : ℕ, 1 ≤ n → δ ≤ ‖t - (n : ℂ)‖ ∧ δ ≤ ‖t + (n : ℂ)‖) :
    Filter.Tendsto
      (fun N : ℕ => mertensPrimeProductBelow N *
        ell2 (blockComparisonGauge (primesBelowSubtype N) t - 1))
      Filter.atTop (nhds 0) := by
  have hvol : ∀ N : ℕ,
      finitePrimeWoldBoundaryVolume (primesBelowSubtype N) = mertensPrimeProductBelow N := by
    intro N
    have h := primeWoldBoundaryVolumeBelow_eq N
    rw [primeWoldBoundaryVolumeBelow] at h
    exact h
  refine tendsto_mertensProduct_mul_ell2_zero_of_log_gauge_le
    (C := Real.exp (woldCompactBound R δ)) (M := R)
    (Real.one_le_exp (woldCompactBound_nonneg hR hδ0)) hR
    (fun N => ?_) (Filter.Eventually.of_forall fun N => ?_)
  · have := one_le_blockComparisonGauge
      (finitePrimeGenusOnePolarizedPhase_ne_zero hR hδ0 (primesBelowSubtype N) ht hsep)
    linarith
  · have hone := one_le_blockComparisonGauge
      (finitePrimeGenusOnePolarizedPhase_ne_zero hR hδ0 (primesBelowSubtype N) ht hsep)
    have hrw : 1 + (blockComparisonGauge (primesBelowSubtype N) t - 1)
        = blockComparisonGauge (primesBelowSubtype N) t := by ring
    rw [hrw, Real.log_exp, ← hvol N]
    exact log_blockComparisonGauge_le hR hδ0 (primesBelowSubtype N) ht hsep

end RHTower
