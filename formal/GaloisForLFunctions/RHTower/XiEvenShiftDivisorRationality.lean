import GaloisForLFunctions.RHTower.XiEvenShiftPrimeDefectTelescope
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure
import GaloisForLFunctions.RHTower.XiShiftDivisorFaithful

/-!
# Rationality of the archimedean correction on even shifts

The Gamma recurrence makes the archimedean logarithmic-derivative difference across a shift by two
an explicit rational function.  Iterating gives the closed form for every even shift: the
archimedean correction at shift `2m` is the rational telescope

  `∑_{j<m} (1/(s+2j+2) + 1/(s+2j+1) - 1/(s+2j-1))`

pointwise on the Euler half-plane, not merely as an upper-end germ.  Consequently the even-shift
prime defect and the general corrected transverse defect agree pointwise there.

At divisor level this says: a family of even shifts whose coefficients sum to zero has an
archimedean correction that is a rational function, because the common digamma mode is carried
entirely by the total mass.
-/

namespace RHTower

open Complex

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- **Shift-two archimedean correction on the full right half-plane.** The Euler-half-plane
hypothesis is not needed: positivity of the real part together with `s ≠ 1` suffices. -/
theorem logDeriv_archFactor_shift_two_of_re_pos {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    logDeriv archFactor (s + 2) - logDeriv archFactor s =
      1 / (s + 2) + 1 / (s + 1) - 1 / (s - 1) := by
  have hsp2 : 0 < (s + 2).re := by
    rw [Complex.add_re]
    norm_num
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs2 : s + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re] at hre
    norm_num at hre
    linarith
  have hs3 : s + 2 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re] at hre
    norm_num at hre
    linarith
  have hdig : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    norm_num [Complex.div_re] at hre
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [logDeriv_archFactor_closed hsp2 hs2 hs3, logDeriv_archFactor_closed hs hs0 h1,
    show (s + 2) - 1 = s + 1 by ring]
  unfold gammaRealLogConnection
  rw [show (s + 2) / 2 = s / 2 + 1 by ring,
    GaloisForLFunctions.digamma_half_add_one hdig]
  field_simp [hs0, h1, hs2, sub_ne_zero.mpr h1]
  ring

/-- **Closed form of the even-shift archimedean correction on the right half-plane.** -/
theorem xiTransverseShiftArchimedeanCorrection_even_of_re_pos
    {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) (m : ℕ) :
    xiTransverseShiftArchimedeanCorrection (2 * m) s = xiEvenShiftPrimeCorrection m s := by
  have hrepos : ∀ k : ℕ, 0 < (s + (k : ℂ)).re := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [Complex.add_re, Complex.natCast_re]
    linarith
  have hne1 : ∀ k : ℕ, s + (k : ℂ) ≠ 1 := by
    intro k h
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact h1 (by simpa using h)
    · have hre := congrArg Complex.re h
      rw [Complex.add_re, Complex.natCast_re, Complex.one_re] at hre
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
  induction m with
  | zero => simp [xiTransverseShiftArchimedeanCorrection, xiEvenShiftPrimeCorrection]
  | succ m ih =>
      have hstep := logDeriv_archFactor_shift_two_of_re_pos (hrepos (2 * m)) (hne1 (2 * m))
      have hcast : ((2 * (m + 1) : ℕ) : ℂ) = ((2 * m : ℕ) : ℂ) + 2 := by push_cast; ring
      have hcorr : xiEvenShiftPrimeCorrection (m + 1) s =
          xiEvenShiftPrimeCorrection m s +
            (1 / (s + ((2 * m : ℕ) : ℂ) + 2) + 1 / (s + ((2 * m : ℕ) : ℂ) + 1) -
              1 / (s + ((2 * m : ℕ) : ℂ) - 1)) := by
        rw [xiEvenShiftPrimeCorrection, xiEvenShiftPrimeCorrection, Finset.sum_range_succ]
      rw [xiTransverseShiftArchimedeanCorrection] at ih ⊢
      rw [hcast, hcorr, show s + (((2 * m : ℕ) : ℂ) + 2) = s + ((2 * m : ℕ) : ℂ) + 2 by ring]
      linear_combination hstep + ih

/-- **Closed form of the even-shift archimedean correction.** For every even shift the correction is
the explicit rational telescope, pointwise on the Euler half-plane. -/
theorem xiTransverseShiftArchimedeanCorrection_even {s : ℂ} (hs : 1 < s.re) (m : ℕ) :
    xiTransverseShiftArchimedeanCorrection (2 * m) s = xiEvenShiftPrimeCorrection m s := by
  refine xiTransverseShiftArchimedeanCorrection_even_of_re_pos (lt_trans zero_lt_one hs) ?_ m
  intro h
  rw [h] at hs
  norm_num at hs

/-- **Pointwise even-shift defect identification.** On the Euler half-plane the explicitly corrected
even-shift defect is the general corrected transverse defect. -/
theorem xiEvenShiftPrimeDefect_eq_xiTransverseShiftPrimeDefect {s : ℂ} (hs : 1 < s.re) (m : ℕ) :
    xiEvenShiftPrimeDefect m s = xiTransverseShiftPrimeDefect (2 * m) s := by
  rw [xiEvenShiftPrimeDefect, xiTransverseShiftPrimeDefect,
    xiTransverseShiftRawLogDerivDefect,
    xiTransverseShiftArchimedeanCorrection_even hs m]

/-! ## Same-parity pairs -/

/-- **Same-parity pairwise archimedean correction.** For integral shifts of equal parity the
pairwise archimedean correction is the explicit rational telescope of their half-difference. -/
theorem xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit {a b : ℕ} (hba : b ≤ a)
    (hpar : a % 2 = b % 2) {s : ℂ} (hs : 0 < (s + b).re) (h1 : s + b ≠ 1) :
    xiPairwiseShiftArchimedeanCorrectionDifference a b s =
      xiEvenShiftPrimeCorrection ((a - b) / 2) (s + b) := by
  obtain ⟨m, hm⟩ : ∃ m, a - b = 2 * m := ⟨(a - b) / 2, by omega⟩
  rw [xiPairwiseShiftArchimedeanCorrectionDifference_eq_relativeShift_of_le a b s hba, hm,
    xiTransverseShiftArchimedeanCorrection_even_of_re_pos hs h1 m]
  congr 1
  omega

/-- **Same-parity pairwise prime difference.** For integral shifts of equal parity the corrected
pairwise completed-Xi value is the raw logarithmic-derivative difference minus an explicit rational
function. -/
theorem xiPairwiseShiftPrimeDifference_eq_explicit {a b : ℕ} (hba : b ≤ a)
    (hpar : a % 2 = b % 2) {s : ℂ} (hs : 0 < (s + b).re) (h1 : s + b ≠ 1) :
    xiPairwiseShiftPrimeDifference a b s =
      (logDeriv xi (s + (a : ℂ)) - logDeriv xi (s + (b : ℂ))) -
        xiEvenShiftPrimeCorrection ((a - b) / 2) (s + b) := by
  rw [xiPairwiseShiftPrimeDifference_eq_raw_sub_correction,
    xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit hba hpar hs h1,
    xiPairwiseShiftRawLogDerivDifference]

/-- **Same-parity pairs are exactly the parity-balanced two-point families.** -/
theorem pairShiftDivisor_parityBalanced {a b : ℕ} (hpar : a % 2 = b % 2) {s : ℂ}
    (hsb : 0 < (s + (b : ℂ)).re) (hba : b ≤ a) (h1 : s + b ≠ 1) :
    xiShiftDivisorArchimedeanCorrection (pairShiftDivisor (a : ℂ) (b : ℂ)) s =
      xiEvenShiftPrimeCorrection ((a - b) / 2) (s + b) := by
  rw [xiShiftDivisorArchimedeanCorrection, pairShiftDivisor, shiftDivisorValue_sub,
    shiftDivisorValue_single, shiftDivisorValue_single, one_mul, one_mul,
    ← xiPairwiseShiftArchimedeanCorrectionDifference_eq_explicit hba hpar hsb h1,
    xiPairwiseShiftArchimedeanCorrectionDifference, xiTransverseShiftArchimedeanCorrection,
    xiTransverseShiftArchimedeanCorrection]
  ring

/-- **Parity reduction of an arbitrary natural shift.** Every archimedean translate splits into the
translate by the shift's parity residue plus an explicit rational telescope. -/
theorem logDeriv_archFactor_shift_split {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) (a : ℕ) :
    logDeriv archFactor (s + (a : ℂ)) =
      logDeriv archFactor (s + ((a % 2 : ℕ) : ℂ)) +
        xiEvenShiftPrimeCorrection (a / 2) (s + ((a % 2 : ℕ) : ℂ)) := by
  have hre : 0 < (s + ((a % 2 : ℕ) : ℂ)).re := by
    have hnn : (0 : ℝ) ≤ ((a % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [Complex.add_re, Complex.natCast_re]
    linarith
  have hne1 : s + ((a % 2 : ℕ) : ℂ) ≠ 1 := by
    intro h
    rcases Nat.eq_zero_or_pos (a % 2) with hz | hpos
    · rw [hz] at h
      exact h1 (by simpa using h)
    · have hre1 := congrArg Complex.re h
      rw [Complex.add_re, Complex.natCast_re, Complex.one_re] at hre1
      have hge : (1 : ℝ) ≤ ((a % 2 : ℕ) : ℝ) := by exact_mod_cast hpos
      linarith
  have hcorr := xiTransverseShiftArchimedeanCorrection_even_of_re_pos hre hne1 (a / 2)
  rw [xiTransverseShiftArchimedeanCorrection] at hcorr
  have hnat : ((2 * (a / 2) : ℕ) : ℂ) + ((a % 2 : ℕ) : ℂ) = (a : ℂ) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  rw [show s + ((a % 2 : ℕ) : ℂ) + ((2 * (a / 2) : ℕ) : ℂ) = s + (a : ℂ) by
    rw [← hnat]; ring] at hcorr
  linear_combination hcorr

/-- **Exact parity decomposition of the archimedean correction.** Every natural-shift family carries
exactly two digamma modes of the archimedean factor, one for each parity class, weighted by the
corresponding coefficient mass; everything else is an explicit rational function.  No hypothesis on
the coefficients is used. -/
theorem archimedeanCorrection_family_parity_decomposition {d : ℕ} (a : Fin d → ℕ) (c : Fin d → ℂ)
    {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    ∑ i, c i * logDeriv archFactor (s + (a i : ℂ)) =
      (∑ i ∈ Finset.univ.filter (fun i => a i % 2 = 0), c i) * logDeriv archFactor s +
        (∑ i ∈ Finset.univ.filter (fun i => ¬ (a i % 2 = 0)), c i) *
          logDeriv archFactor (s + 1) +
        ∑ i, c i * xiEvenShiftPrimeCorrection (a i / 2) (s + ((a i % 2 : ℕ) : ℂ)) := by
  classical
  have hstep : ∀ i, c i * logDeriv archFactor (s + (a i : ℂ)) =
      c i * logDeriv archFactor (s + ((a i % 2 : ℕ) : ℂ)) +
        c i * xiEvenShiftPrimeCorrection (a i / 2) (s + ((a i % 2 : ℕ) : ℂ)) := fun i => by
    rw [logDeriv_archFactor_shift_split hs h1 (a i)]; ring
  have hmode : ∑ i, c i * logDeriv archFactor (s + ((a i % 2 : ℕ) : ℂ)) =
      (∑ i ∈ Finset.univ.filter (fun i => a i % 2 = 0), c i) * logDeriv archFactor s +
        (∑ i ∈ Finset.univ.filter (fun i => ¬ (a i % 2 = 0)), c i) *
          logDeriv archFactor (s + 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => a i % 2 = 0)]
    have h0 : ∀ i ∈ Finset.univ.filter (fun i => a i % 2 = 0),
        c i * logDeriv archFactor (s + ((a i % 2 : ℕ) : ℂ)) =
          c i * logDeriv archFactor s := fun i hi => by
      rw [(Finset.mem_filter.mp hi).2]; norm_num
    have hone : ∀ i ∈ Finset.univ.filter (fun i => ¬ (a i % 2 = 0)),
        c i * logDeriv archFactor (s + ((a i % 2 : ℕ) : ℂ)) =
          c i * logDeriv archFactor (s + 1) := fun i hi => by
      have hne : ¬ (a i % 2 = 0) := (Finset.mem_filter.mp hi).2
      have hres : a i % 2 = 1 := by omega
      rw [hres]; norm_num
    rw [Finset.sum_congr rfl h0, Finset.sum_congr rfl hone, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_add_distrib, hmode]

/-- **Parity-balanced families have rational archimedean corrections.** Both digamma modes are
carried entirely by their parity mass, so they cancel exactly when the even-shift coefficients and
the odd-shift coefficients separately sum to zero — a condition odd shifts can also satisfy. -/
theorem archimedeanCorrection_family_of_parity_balanced {d : ℕ} (a : Fin d → ℕ) (c : Fin d → ℂ)
    (heven : ∑ i ∈ Finset.univ.filter (fun i => a i % 2 = 0), c i = 0)
    (hodd : ∑ i ∈ Finset.univ.filter (fun i => ¬ (a i % 2 = 0)), c i = 0)
    {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    ∑ i, c i * logDeriv archFactor (s + (a i : ℂ)) =
      ∑ i, c i * xiEvenShiftPrimeCorrection (a i / 2) (s + ((a i % 2 : ℕ) : ℂ)) := by
  rw [archimedeanCorrection_family_parity_decomposition a c hs h1, heven, hodd]
  ring

/-- **Mass-zero even families have rational archimedean corrections.** The even-shift case of the
parity-balanced law: with only even shifts, the odd digamma mode is absent and vanishing total mass
suffices. -/
theorem archimedeanCorrection_evenFamily_of_mass_zero {d : ℕ} (k : Fin d → ℕ) (c : Fin d → ℂ)
    (hmass : ∑ i, c i = 0) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    ∑ i, c i * logDeriv archFactor (s + ((2 * k i : ℕ) : ℂ)) =
      ∑ i, c i * xiEvenShiftPrimeCorrection (k i) s := by
  classical
  have hmod : ∀ i, (2 * k i) % 2 = 0 := fun i => by omega
  have hdiv : ∀ i, (2 * k i) / 2 = k i := fun i => by omega
  have hgen := archimedeanCorrection_family_of_parity_balanced
    (fun i => 2 * k i) c (by simpa [hmod] using hmass) (by simp [hmod]) hs h1
  simpa [hmod, hdiv] using hgen

/-- **Parity-balanced divisor rationality.** The archimedean correction of a natural-shift divisor
whose even-shift and odd-shift coefficient masses both vanish is an explicit rational function. -/
theorem xiShiftDivisorArchimedeanCorrection_parityBalanced {d : ℕ} (a : Fin d → ℕ) (c : Fin d → ℂ)
    (heven : ∑ i ∈ Finset.univ.filter (fun i => a i % 2 = 0), c i = 0)
    (hodd : ∑ i ∈ Finset.univ.filter (fun i => ¬ (a i % 2 = 0)), c i = 0)
    {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    xiShiftDivisorArchimedeanCorrection
        (familyShiftDivisor (fun i => ((a i : ℕ) : ℂ)) c) s =
      ∑ i, c i * xiEvenShiftPrimeCorrection (a i / 2) (s + ((a i % 2 : ℕ) : ℂ)) := by
  rw [xiShiftDivisorArchimedeanCorrection, shiftDivisorValue_familyShiftDivisor]
  exact archimedeanCorrection_family_of_parity_balanced a c heven hodd hs h1

/-- **Parity-balanced divisor prime value.** For a parity-balanced natural-shift family the corrected
completed-Xi value is the raw weighted logarithmic derivative minus an explicit rational
function. -/
theorem xiShiftDivisorPrimeValue_parityBalanced {d : ℕ} (a : Fin d → ℕ) (c : Fin d → ℂ)
    (heven : ∑ i ∈ Finset.univ.filter (fun i => a i % 2 = 0), c i = 0)
    (hodd : ∑ i ∈ Finset.univ.filter (fun i => ¬ (a i % 2 = 0)), c i = 0)
    {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    xiShiftDivisorPrimeValue (familyShiftDivisor (fun i => ((a i : ℕ) : ℂ)) c) s =
      (∑ i, c i * logDeriv xi (s + (a i : ℂ))) -
        ∑ i, c i * xiEvenShiftPrimeCorrection (a i / 2) (s + ((a i % 2 : ℕ) : ℂ)) := by
  rw [xiShiftDivisorPrimeValue, xiShiftDivisorLogDeriv, shiftDivisorValue_familyShiftDivisor,
    xiShiftDivisorArchimedeanCorrection_parityBalanced a c heven hodd hs h1]

/-- **Even-shift divisor rationality.** The archimedean correction of a mass-zero even-shift divisor
is the divisor-weighted rational telescope. -/
theorem xiShiftDivisorArchimedeanCorrection_evenFamily {d : ℕ} (k : Fin d → ℕ) (c : Fin d → ℂ)
    (hmass : ∑ i, c i = 0) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    xiShiftDivisorArchimedeanCorrection
        (familyShiftDivisor (fun i => ((2 * k i : ℕ) : ℂ)) c) s =
      ∑ i, c i * xiEvenShiftPrimeCorrection (k i) s := by
  rw [xiShiftDivisorArchimedeanCorrection, shiftDivisorValue_familyShiftDivisor]
  exact archimedeanCorrection_evenFamily_of_mass_zero k c hmass hs h1

/-- **Even-shift divisor prime value.** For a mass-zero even-shift family the corrected completed-Xi
value is the raw weighted logarithmic derivative minus an explicit rational function. -/
theorem xiShiftDivisorPrimeValue_evenFamily {d : ℕ} (k : Fin d → ℕ) (c : Fin d → ℂ)
    (hmass : ∑ i, c i = 0) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    xiShiftDivisorPrimeValue (familyShiftDivisor (fun i => ((2 * k i : ℕ) : ℂ)) c) s =
      (∑ i, c i * logDeriv xi (s + ((2 * k i : ℕ) : ℂ))) -
        ∑ i, c i * xiEvenShiftPrimeCorrection (k i) s := by
  rw [xiShiftDivisorPrimeValue, xiShiftDivisorLogDeriv, shiftDivisorValue_familyShiftDivisor,
    xiShiftDivisorArchimedeanCorrection_evenFamily k c hmass hs h1]

end

end RHTower
