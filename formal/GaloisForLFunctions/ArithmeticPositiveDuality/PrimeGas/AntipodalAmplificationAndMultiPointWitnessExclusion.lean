import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.VaughanStrideDispersionAndTwistedPrimeGas
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.BilateralReflectionRigidity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.HighOrdinateMarginAdvances
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.PrimeParityPartition
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion
import GaloisForLFunctions.RHTower.RouteBChiDecay

/-!
# Antipodal Stirling Amplification, Single-Quartet Surgery Firewall, Multi-Point Witness Production, and Exact Residue-Progression Parseval Laws Above Height 184

Classifying which rank-one omission spectra `missingWaveSpectrum v` are possible (`InverseSpectrum`)
does not produce a spectrum with strict certified excess on the remaining open strip
`Ω_open = {s : ℂ | 3001 / 24000 ≤ Re s ∧ Re s < 1 / 2 ∧ 184 < |Im s|}`. This module establishes five
unconditional structural and witness-production laws across all heights `184 < |Im s|`:

1. **Exact variational supremum over all possible `MissingWave` spectra
   (`iSup_capped_witness_excess_eq_norm_continued`, `iSup_uncapped_witness_excess_eq_norm_continued`,
   `all_possible_spectra_nonpositive_excess_iff_zeta_eq_zero`):**
   Across the entire space of conserving rank-one omissions and finite truncations `(v, K)`, both
   the UV-capped fourth-power excess and the uncapped `(2 / Re s)`-power excess have exact supremum
   `‖continued s‖ = ‖(2^s - 1) ζ(s)‖` on `0 < Re s < 1`. At any zero of `ζ`, every possible
   rank-one spectrum has nonpositive excess `≤ 0`.
2. **Unconditional quantitative Spira–Stirling antipodal amplification and reflected witness transfer
   across all `0 < Re s < 1 / 2`, `184 < |Im s|` (`norm_zetaChi_reflected_le_rpow_above_oneHundredEightyFour`,
   `norm_zetaChi_ge_rpow_above_oneHundredEightyFour`,
   `strict_spira_zeta_amplification_above_oneHundredEightyFour`,
   `left_strict_witness_of_reflected_euler_excess_above_oneHundredEightyFour`,
   `left_strict_witness_of_dirichlet_domination_above_oneHundredEightyFour`):**
   Integrating the vertical digamma lower bound across `[Re s / 2, (1 - Re s) / 2]` proves
   `‖zetaChi s‖ ≥ (|Im s| / 7)^{1/2 - Re s} > (184 / 7)^{1/2 - Re s} > 1` and
   `‖zetaChi (1 - conj s)‖ ≤ (|Im s| / 7)^{-(1/2 - Re s)} < 1` throughout `0 < Re s < 1 / 2`,
   `184 < |Im s|`. Consequently `‖ζ(s)‖ ≥ (|Im s| / 7)^{1/2 - Re s} ‖ζ(1 - conj s)‖`, any strict
   partial-sum excess `η > 0` at `1 - conj s` transfers with `( |Im s| / 7 )^{1/2 - Re s}`
   amplification to explicit finite `MissingWave` and linear-order Euler–Knopp witnesses at `s`, and
   off-line `dirichletPoly` domination at `1 - conj s` produces strict-excess witnesses at `s`
   without archimedean side hypotheses.
3. **Single-quartet positive multiplicative surgery firewall on `Ω_open`
   (`single_quartet_positive_multiplicative_firewall_above_oneHundredEightyFour`):**
   At every point `s₀ ∈ Ω_open`, a 5-term prime-power surgery `a = dirichletSurgWeight M c` at a
   single prime `p ∈ {5, 7}` yields real multiplicative coefficients `a(m n) = a(m) a(n)` (`m ⊥ n`)
   with `a(1) = 1`, `a(n) ≥ 1`, and `a(2^u 3^v) = 1`, satisfies the exact functional equation and
   vanishing `bilateralReflectionDefect` across the entire reflected quartet
   `{s₀, conj s₀, 1 - s₀, 1 - conj s₀}`, and extinguishes every Prime-Gas clock at all four quartet
   points. Hence no single-quartet method using only multiplicativity, `a(n) ≥ 1`, `{2, 3}`-shell
   agreement, and quartet reflection can produce a strict-excess witness on `Ω_open`.
4. **Multi-ordinate repulsion, horizontal pigeonhole witnesses, and dyadic parity-pole laws on `Ω_open`
   (`two_point_repulsion_strict_witness_on_remaining_strip`,
   `pigeonhole_strict_witness_on_remaining_strip`,
   `infinite_strict_witnesses_on_every_horizontal_subinterval_above_oneHundredEightyFour`,
   `dyadic_parity_uncancelled_poles_on_remaining_strip`):**
   Any pair `s₁, s₂ ∈ Ω_open` (`Im s₁ + 4 ≤ Im s₂`) violating the 5-point Hadamard repulsion budget
   unconditionally admits a simultaneous UV-capped + uncapped `MissingWave` witness and linear-order
   Euler–Knopp witness at `s₁` or `s₂`; every finite probe set on `Ω_open` in `[τ - h, τ + h]`
   (`|τ| > 184`) of cardinality `> 4 (1 + h^2) (xiLineTwoLogDerivConstant + log(|τ| + 4))` contains
   an unconditional strict-excess witness; and `ζ(4 s) ≠ 0` on `20999 / 96000 < Re s < 1 / 2` while
   `ζ(8 s) ≠ 0` across all of `Ω_open`, characterizing witness failure via uncancelled dyadic
   `parityPartition` poles in at most two (respectively three) halving steps.
5. **Exact coprime residue-progression Parseval identity, leading-term sieve annihilation, and
   variance power cancellation (`residueProgressionDefect_annihilates_low_residues`,
   `sum_residueProgressionDefect_eq_principal_vaughanEulerDefect`,
   `totient_mul_sum_normSq_residueProgressionDefect_eq_parseval`,
   `totient_mul_sum_normSq_centered_residueProgressionDefect_eq`,
   `sum_normSq_centered_residueProgressionDefect_le_rpow`):**
   Decomposing `vaughanEulerDefect` into reduced residue progressions `u : (ZMod (n + 1))ˣ`
   annihilates the leading progression term `k = u.val < n + 1` for all `u.val ≤ D`, separates the
   principal `ζ` mode `χ = 1` from `χ ≠ 1` by exact finite abelian Parseval and variance identities,
   and proves `∑_u ‖V(u) - V̄‖² ≤ residueProgressionVarianceConstant s · (n + 1)^{-(1 - 2 Re s)² / 4}`
   across all `0 < Re s < 1 / 2` and all `Im s ∈ ℝ`.
-/

noncomputable section

open Complex Filter Set intervalIntegral MeasureTheory
open scoped BigOperators ComplexConjugate Topology

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open AntipodalSpectrum AntipodalSpectrum.ComplementaryHalves
open InverseSpectrum.ShellMixing
open CutoffSeparation

/-! ### 1. Exact Variational Supremum Across All Possible `MissingWave` Spectra -/

/-- Certified UV-capped witness excess of a conserving rank-one omission `v` at truncation `K`. -/
def cappedWitnessExcess (s : ℂ) (Λ : ℝ) (v : MissingWave) (K : ℕ) : ℝ :=
  ‖finiteTriadReading (missingWaveSpectrum v) K s‖ -
    ((uvZeroThresholdFactor s Λ * lineLoss v.val) ^ (1 / 4 : ℝ) + triadTailBound K s)

/-- Certified cap-free witness excess of a conserving rank-one omission `v` at truncation `K`. -/
def uncappedWitnessExcess (s : ℂ) (v : MissingWave) (K : ℕ) : ℝ :=
  ‖finiteTriadReading (missingWaveSpectrum v) K s‖ -
    ((chordZeroThresholdFactor s * lineLoss v.val) ^ (s.re / 2) + triadTailBound K s)

/-- Simultaneous strict-excess witness predicate at `s` (`0 < Re s < 1`) with UV cap `Λ > 0`:
existence of a finite surviving-eigenvalue witness `(v, K)` passing both the UV-capped fourth-power
test and the uncapped `(2 / Re s)`-power test, together with a linear-order `3 M`-term Euler–Knopp
partial sum beating `3 / 2^{M / 2}` and `eulerEtaTailBound (2 * M) M s`. -/
def HasStrictPrimeGasWitness (s : ℂ) (hs0 : 0 < s.re) (Λ : ℝ) : Prop :=
  (∃ (v : MissingWave) (K : ℕ),
    uvRegularRankOne s hs0 Λ v ∧
    0 < cappedWitnessExcess s Λ v K ∧
    0 < uncappedWitnessExcess s v K) ∧
  ∃ M : ℕ, max 10 ⌈|s.im|⌉₊ ≤ M ∧
    eulerEtaTailBound (2 * M) M s ≤ 3 / (2 : ℝ) ^ (M / 2) ∧
    3 / (2 : ℝ) ^ (M / 2) < ‖eulerEtaPartialSum (2 * M) M s‖

/-- Pointwise equivalence between `HasStrictPrimeGasWitness` and `riemannZeta s ≠ 0` across the open
critical strip `0 < Re s < 1` (`Λ > 0`). -/
theorem hasStrictPrimeGasWitness_iff_zeta_ne_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    HasStrictPrimeGasWitness s hs0 Λ ↔ riemannZeta s ≠ 0 := by
  have hs_ne1 : s ≠ 1 := fun h => hs1.ne (by rw [h, Complex.one_re])
  constructor
  · rintro ⟨_, M, hM, hle, hgt⟩
    have hM1 : 1 ≤ M := le_trans (by norm_num : 1 ≤ 10) ((le_max_left 10 _).trans hM)
    exact (zeta_ne_zero_of_eulerEtaPartialSum_beats_tail hs0 hs_ne1 hM1 (hle.trans_lt hgt)).2
  · intro hzeta
    have h2s_ne : (2 : ℂ) ^ s - 1 ≠ 0 := by
      have hgt : (1 : ℝ) < (2 : ℝ) ^ s.re := Real.one_lt_rpow one_lt_two hs0
      have hlb := norm_sub_norm_le ((2 : ℂ) ^ s) 1
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos zero_lt_two, Complex.ofReal_ofNat, norm_one] at hlb
      exact norm_pos_iff.mp (by linarith)
    have hcont_pos : 0 < ‖continued s‖ := norm_pos_iff.mpr (mul_ne_zero h2s_ne hzeta)
    obtain ⟨v, K, huv, hcap, huncap⟩ :=
      exists_simultaneous_witness_surplus_gt_norm_continued_sub hs0 hs1 hΛ (half_pos hcont_pos)
    have hex_lin := ((exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).1).mpr hzeta
    obtain ⟨M, hM, hbeat⟩ := hex_lin
    have hM10 : 10 ≤ M := (le_max_left 10 _).trans hM
    have him_le : |s.im| ≤ (M : ℝ) :=
      (Nat.le_ceil |s.im|).trans (by exact_mod_cast (le_max_right 10 _).trans hM)
    have hexp := eulerEtaTailBound_two_mul_le_three_div_two_pow_half hs0 hs1.le hM10 him_le
    refine ⟨⟨v, K, huv, ?_, ?_⟩, ⟨M, hM, hexp, hbeat⟩⟩
    · unfold cappedWitnessExcess; linarith
    · unfold uncappedWitnessExcess; linarith

/-- **Exact variational supremum of UV-capped witness excess over all possible spectra:**
across all `(v : MissingWave, K : ℕ)` satisfying `uvRegularRankOne s hs0 Λ v`, the supremum of
`cappedWitnessExcess s Λ v K` equals `‖continued s‖ = ‖(2^s - 1) ζ(s)‖`. -/
theorem iSup_capped_witness_excess_eq_norm_continued {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (⨆ p : {q : MissingWave × ℕ // uvRegularRankOne s hs0 Λ q.1},
      cappedWitnessExcess s Λ p.1.1 p.1.2) = ‖continued s‖ := by
  obtain ⟨v₀, K₀, huv₀, -, -⟩ :=
    exists_simultaneous_witness_surplus_gt_norm_continued_sub hs0 hs1 hΛ zero_lt_one
  haveI : Nonempty {q : MissingWave × ℕ // uvRegularRankOne s hs0 Λ q.1} := ⟨⟨(v₀, K₀), huv₀⟩⟩
  have hbdd : BddAbove (Set.range fun p : {q : MissingWave × ℕ // uvRegularRankOne s hs0 Λ q.1} =>
      cappedWitnessExcess s Λ p.1.1 p.1.2) :=
    ⟨‖continued s‖, by
      rintro _ ⟨p, rfl⟩
      exact (capped_witness_surplus_le_norm_continued hs0 hs1 hΛ p.2 p.1.2).2⟩
  have hle : (⨆ p : {q : MissingWave × ℕ // uvRegularRankOne s hs0 Λ q.1},
      cappedWitnessExcess s Λ p.1.1 p.1.2) ≤ ‖continued s‖ :=
    ciSup_le fun p => (capped_witness_surplus_le_norm_continued hs0 hs1 hΛ p.2 p.1.2).2
  refine le_antisymm hle ?_
  by_contra hlt
  rw [not_le] at hlt
  set S : ℝ := ⨆ p : {q : MissingWave × ℕ // uvRegularRankOne s hs0 Λ q.1},
    cappedWitnessExcess s Λ p.1.1 p.1.2
  have hε : 0 < ‖continued s‖ - S := sub_pos.mpr hlt
  obtain ⟨v, K, huv, hcap, -⟩ :=
    exists_simultaneous_witness_surplus_gt_norm_continued_sub hs0 hs1 hΛ (half_pos hε)
  have hcap' : ‖continued s‖ - (‖continued s‖ - S) / 2 < cappedWitnessExcess s Λ v K := hcap
  have hle_sup : cappedWitnessExcess s Λ v K ≤ S :=
    le_ciSup (f := fun p : {q : MissingWave × ℕ // uvRegularRankOne s hs0 Λ q.1} =>
      cappedWitnessExcess s Λ p.1.1 p.1.2) hbdd ⟨(v, K), huv⟩
  linarith only [hε, hcap', hle_sup]

/-- **Exact variational supremum of cap-free witness excess over all possible spectra:**
across all `(v : MissingWave, K : ℕ)`, the supremum of `uncappedWitnessExcess s v K` equals
`‖continued s‖ = ‖(2^s - 1) ζ(s)‖`. -/
theorem iSup_uncapped_witness_excess_eq_norm_continued {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (⨆ p : MissingWave × ℕ, uncappedWitnessExcess s p.1 p.2) = ‖continued s‖ := by
  obtain ⟨v₀, K₀, -, -, -⟩ :=
    exists_simultaneous_witness_surplus_gt_norm_continued_sub hs0 hs1 zero_lt_one zero_lt_one
  haveI : Nonempty (MissingWave × ℕ) := ⟨(v₀, K₀)⟩
  have hbdd : BddAbove (Set.range fun p : MissingWave × ℕ => uncappedWitnessExcess s p.1 p.2) :=
    ⟨‖continued s‖, by
      rintro _ ⟨p, rfl⟩
      exact (uncapped_witness_surplus_le_norm_continued hs0 hs1 p.1 p.2).2⟩
  have hle : (⨆ p : MissingWave × ℕ, uncappedWitnessExcess s p.1 p.2) ≤ ‖continued s‖ :=
    ciSup_le fun p => (uncapped_witness_surplus_le_norm_continued hs0 hs1 p.1 p.2).2
  refine le_antisymm hle ?_
  by_contra hlt
  rw [not_le] at hlt
  set S : ℝ := ⨆ p : MissingWave × ℕ, uncappedWitnessExcess s p.1 p.2
  have hε : 0 < ‖continued s‖ - S := sub_pos.mpr hlt
  obtain ⟨v, K, -, -, huncap⟩ :=
    exists_simultaneous_witness_surplus_gt_norm_continued_sub hs0 hs1 zero_lt_one (half_pos hε)
  have huncap' : ‖continued s‖ - (‖continued s‖ - S) / 2 < uncappedWitnessExcess s v K := huncap
  have hle_sup : uncappedWitnessExcess s v K ≤ S :=
    le_ciSup (f := fun p : MissingWave × ℕ => uncappedWitnessExcess s p.1 p.2) hbdd (v, K)
  linarith only [hε, huncap', hle_sup]

/-- **Spectrum-classification obstruction to strict excess:** knowing all possible spectra
`{missingWaveSpectrum v | v : MissingWave}` yields strictly nonpositive excess across every `(v, K)`
if and only if `riemannZeta s = 0`. -/
theorem all_possible_spectra_nonpositive_excess_iff_zeta_eq_zero {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) {Λ : ℝ} (hΛ : 0 < Λ) :
    ((∀ (v : MissingWave) (K : ℕ), uvRegularRankOne s hs0 Λ v →
        cappedWitnessExcess s Λ v K ≤ 0) ↔ riemannZeta s = 0) ∧
    ((∀ (v : MissingWave) (K : ℕ), uncappedWitnessExcess s v K ≤ 0) ↔ riemannZeta s = 0) := by
  have h2s_ne : (2 : ℂ) ^ s - 1 ≠ 0 := by
    have hgt : (1 : ℝ) < (2 : ℝ) ^ s.re := Real.one_lt_rpow one_lt_two hs0
    have hlb := norm_sub_norm_le ((2 : ℂ) ^ s) 1
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos zero_lt_two, Complex.ofReal_ofNat, norm_one] at hlb
    exact norm_pos_iff.mp (by linarith)
  constructor
  · constructor
    · intro hall
      by_contra hne
      have hpos : 0 < ‖continued s‖ := norm_pos_iff.mpr (mul_ne_zero h2s_ne hne)
      obtain ⟨v, K, huv, hcap, -⟩ :=
        exists_simultaneous_witness_surplus_gt_norm_continued_sub hs0 hs1 hΛ (half_pos hpos)
      have hle := hall v K huv
      unfold cappedWitnessExcess at hle
      linarith
    · intro hz v K huv
      have hle := (capped_witness_surplus_le_norm_continued hs0 hs1 hΛ huv K).2
      unfold continued at hle
      rw [hz, mul_zero, norm_zero] at hle
      exact hle
  · constructor
    · intro hall
      by_contra hne
      have hpos : 0 < ‖continued s‖ := norm_pos_iff.mpr (mul_ne_zero h2s_ne hne)
      obtain ⟨v, K, -, -, huncap⟩ :=
        exists_simultaneous_witness_surplus_gt_norm_continued_sub hs0 hs1 zero_lt_one (half_pos hpos)
      have hle := hall v K
      unfold uncappedWitnessExcess at hle
      linarith
    · intro hz v K
      have hle := (uncapped_witness_surplus_le_norm_continued hs0 hs1 v K).2
      unfold continued at hle
      rw [hz, mul_zero, norm_zero] at hle
      exact hle

/-! ### 2. Quantitative Spira–Stirling Antipodal Amplification and Witness Transfer Above Height 184 -/

private lemma log_seven_div_two_pi_gt_tenth :
    (1 / 10 : ℝ) < Real.log (7 / (2 * Real.pi)) := by
  have hpi_hi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hratio_pos : 0 < 2 * Real.pi / 7 := by positivity
  have hratio_lt : 2 * Real.pi / 7 < 9 / 10 := by linarith only [hpi_hi]
  have hlog_le := Real.log_le_sub_one_of_pos hratio_pos
  have hlog_inv : Real.log (7 / (2 * Real.pi)) = -Real.log (2 * Real.pi / 7) := by
    rw [← Real.log_inv, inv_div]
  linarith only [hratio_lt, hlog_le, hlog_inv]

private lemma norm_zetaChi_right_strip_le_rpow {σ t : ℝ}
    (hσ1 : 1 / 2 < σ) (hσ2 : σ < 1) (ht : 184 < t) :
    ‖_root_.RHTower.zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ (t / 7) ^ (-(σ - 1 / 2)) := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * I
  set a : ℝ := (1 - σ) / 2
  set b : ℝ := σ / 2
  set y : ℝ := t / 2
  have hy92 : 92 < y := by dsimp [y]; linarith only [ht]
  have hy0 : 0 < y := by linarith only [hy92]
  have ha0 : 0 ≤ a := by dsimp [a]; linarith only [hσ2]
  have hab : a ≤ b := by dsimp [a, b]; linarith only [hσ1]
  have hba : b - a = σ - 1 / 2 := by dsimp [a, b]; ring
  have hzre : z.re = σ := by simp [z]
  have h1z : (1 - z) / 2 = (a : ℂ) - (y : ℂ) * I := by
    dsimp [z, a, y]; push_cast; ring
  have hnorm1 : ‖Complex.Gamma ((1 - z) / 2)‖ = ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
    rw [h1z, show (a : ℂ) - (y : ℂ) * I = conj ((a : ℂ) + (y : ℂ) * I) by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring,
      Complex.Gamma_conj, RCLike.norm_conj]
  have h2z : z / 2 = (b : ℂ) + (y : ℂ) * I := by dsimp [z, b, y]; push_cast; ring
  have hnorm2 : ‖Complex.Gamma (z / 2)‖ = ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ := by rw [h2z]
  have hΓne : ∀ u : ℝ, Complex.Gamma ((u : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro u
    apply Complex.Gamma_ne_zero
    intro m hc
    have him := congrArg Complex.im hc
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, mul_one, zero_add, add_zero, Complex.neg_im, Complex.natCast_im,
      neg_zero] at him
    linarith only [him, hy0]
  have hga : 0 < ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := norm_pos_iff.mpr (hΓne a)
  have hgb : 0 < ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ := norm_pos_iff.mpr (hΓne b)
  set C : ℝ := 1 / y ^ (2 : ℕ) + Real.pi / (2 * y)
  have hftc := _root_.RHTower.ftc_log_norm_Gamma (a := a) (b := b) hy0
  have hintge : (b - a) * (Real.log y - C) ≤
      ∫ x in a..b, (Complex.digamma ((x : ℂ) + (y : ℂ) * I)).re := by
    have hconst : ∫ _x in a..b, (Real.log y - C) = (b - a) * (Real.log y - C) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [← hconst]
    apply intervalIntegral.integral_mono_on hab
    · exact intervalIntegrable_const
    · apply ContinuousOn.intervalIntegrable
      have hφ : ContinuousOn (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (Set.uIcc a b) := by fun_prop
      have hmaps : Set.MapsTo (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) (Set.uIcc a b)
          {w : ℂ | 0 < w.im} := by
        intro x _
        simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, mul_one, zero_add, add_zero]
        exact hy0
      exact Complex.continuous_re.comp_continuousOn
        (_root_.RHTower.digamma_continuousOn_uhp.comp hφ hmaps)
    · intro x hx
      rw [Set.mem_Icc] at hx
      exact _root_.RHTower.re_digamma_ge (by linarith only [ha0, hx.1]) hy0
  have hlogratio : (σ - 1 / 2) * (Real.log y - C) ≤
      Real.log ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ -
        Real.log ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
    rw [← hftc, ← hba]; exact hintge
  rw [_root_.RHTower.norm_zetaChi_eq z, hnorm1, hnorm2, hzre]
  have hpi : Real.pi ^ (σ - 1 / 2) = Real.exp ((σ - 1 / 2) * Real.log Real.pi) := by
    rw [Real.rpow_def_of_pos Real.pi_pos]; congr 1; ring
  have hexpr : Real.pi ^ (σ - 1 / 2) * ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ =
      Real.exp ((σ - 1 / 2) * Real.log Real.pi +
        (Real.log ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ -
          Real.log ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖)) := by
    rw [Real.exp_add, hpi, Real.exp_sub, Real.exp_log hga, Real.exp_log hgb]; ring
  rw [hexpr, Real.rpow_def_of_pos (by positivity : 0 < t / 7)]
  apply Real.exp_le_exp.mpr
  have hC_small : C < 1 / 10 := by
    have h1 : 1 / y ^ (2 : ℕ) < 1 / 100 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [hy92]
    have h2 : Real.pi / (2 * y) < 9 / 100 := by
      have hpi4 := Real.pi_lt_d4
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith only [hy92, hpi4]
    dsimp [C]
    linarith only [h1, h2]
  have hlog_split : Real.log Real.pi - Real.log y =
      -Real.log (t / 7) - Real.log (7 / (2 * Real.pi)) := by
    have ht_pos : 0 < t := by linarith only [ht]
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hy_eq : Real.log y = Real.log t - Real.log 2 := by
      dsimp [y]; exact Real.log_div ht_pos.ne' two_ne_zero
    have ht7 : Real.log (t / 7) = Real.log t - Real.log 7 :=
      Real.log_div ht_pos.ne' (by norm_num)
    have h7pi : Real.log (7 / (2 * Real.pi)) = Real.log 7 - (Real.log 2 + Real.log Real.pi) := by
      rw [Real.log_div (by norm_num) (by positivity), Real.log_mul two_ne_zero hpi_pos.ne']
    linarith only [hy_eq, ht7, h7pi]
  have hgap_log := log_seven_div_two_pi_gt_tenth
  have hinner : Real.log Real.pi - Real.log y + C ≤ -Real.log (t / 7) := by
    linarith only [hlog_split, hgap_log, hC_small]
  have hσpos : 0 < σ - 1 / 2 := by linarith only [hσ1]
  have hstep1 : (σ - 1 / 2) * Real.log Real.pi +
      (Real.log ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ -
        Real.log ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖) ≤
      (σ - 1 / 2) * (Real.log Real.pi - Real.log y + C) := by
    nlinarith only [hlogratio]
  have hstep2 : (σ - 1 / 2) * (Real.log Real.pi - Real.log y + C) ≤
      Real.log (t / 7) * -(σ - 1 / 2) := by
    have hm := mul_le_mul_of_nonneg_left hinner hσpos.le
    linarith only [hm]
  exact hstep1.trans hstep2

/-- **Unconditional right-strip `zetaChi` contraction above height `184`:** across all
`0 < Re s < 1 / 2` and `184 < |Im s|`, both `1 - s` and `1 - conj s` satisfy
`‖zetaChi (1 - s)‖ = ‖zetaChi (1 - conj s)‖ ≤ (|Im s| / 7)^{-(1/2 - Re s)} < (184 / 7)^{-(1/2 - Re s)} < 1`. -/
theorem norm_zetaChi_reflected_le_rpow_above_oneHundredEightyFour
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|) :
    ‖_root_.RHTower.zetaChi (1 - s)‖ = ‖_root_.RHTower.zetaChi (1 - conj s)‖ ∧
      ‖_root_.RHTower.zetaChi (1 - conj s)‖ ≤
        (|s.im| / 7) ^ (-(1 / 2 - s.re)) ∧
      (|s.im| / 7) ^ (-(1 / 2 - s.re)) <
        (184 / 7 : ℝ) ^ (-(1 / 2 - s.re)) ∧
      (184 / 7 : ℝ) ^ (-(1 / 2 - s.re)) < 1 := by
  have h1s_conj : conj (1 - conj s) = 1 - s := by simp
  have hnorm_eq : ‖_root_.RHTower.zetaChi (1 - s)‖ = ‖_root_.RHTower.zetaChi (1 - conj s)‖ := by
    rw [← h1s_conj, _root_.RHTower.zetaChi_conj, Complex.norm_conj]
  have hbound : ‖_root_.RHTower.zetaChi (1 - conj s)‖ ≤ (|s.im| / 7) ^ (-(1 / 2 - s.re)) := by
    have hre1 : 1 / 2 < 1 - s.re := by linarith only [hhi]
    have hre2 : 1 - s.re < 1 := by linarith only [hs0]
    have hmain := norm_zetaChi_right_strip_le_rpow hre1 hre2 him
    have hexp_eq : -((1 - s.re) - 1 / 2) = -(1 / 2 - s.re) := by ring
    rw [hexp_eq] at hmain
    rcases le_or_gt 0 s.im with him_nn | him_neg
    · have habs : |s.im| = s.im := abs_of_nonneg him_nn
      have hpt : ((1 - s.re : ℝ) : ℂ) + ((|s.im| : ℝ) : ℂ) * I = 1 - conj s := by
        rw [habs]
        apply Complex.ext <;> simp
      rwa [hpt] at hmain
    · have habs : |s.im| = -s.im := abs_of_neg him_neg
      have hpt : ((1 - s.re : ℝ) : ℂ) + ((|s.im| : ℝ) : ℂ) * I = 1 - s := by
        rw [habs]
        apply Complex.ext <;> simp
      rw [hpt, hnorm_eq] at hmain
      exact hmain
  have hneg : -(1 / 2 - s.re) < 0 := by linarith only [hhi]
  have hstrict1 : (|s.im| / 7) ^ (-(1 / 2 - s.re)) < (184 / 7 : ℝ) ^ (-(1 / 2 - s.re)) :=
    Real.rpow_lt_rpow_of_neg (by norm_num) (by linarith only [him]) hneg
  have hstrict2 : (184 / 7 : ℝ) ^ (-(1 / 2 - s.re)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  exact ⟨hnorm_eq, hbound, hstrict1, hstrict2⟩

/-- **Unconditional left-strip Spira–Stirling amplification above height `184`:** across all
`0 < Re s < 1 / 2` and `184 < |Im s|`,
`‖zetaChi s‖ ≥ (|Im s| / 7)^{1/2 - Re s} > (184 / 7)^{1/2 - Re s} > 1`. -/
theorem norm_zetaChi_ge_rpow_above_oneHundredEightyFour
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|) :
    1 < (184 / 7 : ℝ) ^ (1 / 2 - s.re) ∧
      (184 / 7 : ℝ) ^ (1 / 2 - s.re) < (|s.im| / 7) ^ (1 / 2 - s.re) ∧
      (|s.im| / 7) ^ (1 / 2 - s.re) ≤ ‖_root_.RHTower.zetaChi s‖ := by
  have hδ : 0 < 1 / 2 - s.re := by linarith only [hhi]
  have h1 : 1 < (184 / 7 : ℝ) ^ (1 / 2 - s.re) :=
    Real.one_lt_rpow (by norm_num) hδ
  have h2 : (184 / 7 : ℝ) ^ (1 / 2 - s.re) < (|s.im| / 7) ^ (1 / 2 - s.re) :=
    Real.rpow_lt_rpow (by norm_num) (by linarith only [him]) hδ
  obtain ⟨hnorm_eq, hrefl_le, -, -⟩ :=
    norm_zetaChi_reflected_le_rpow_above_oneHundredEightyFour hs0 hhi him
  have hprod := congrArg norm
    (_root_.RHTower.zetaChi_mul_one_sub_of_mem_strip hs0 (by linarith only [hhi]))
  rw [norm_mul, norm_one, hnorm_eq] at hprod
  have hrefl_pos : 0 < ‖_root_.RHTower.zetaChi (1 - conj s)‖ := by
    by_contra hle0
    have hz0 : ‖_root_.RHTower.zetaChi (1 - conj s)‖ = 0 :=
      le_antisymm (not_lt.mp hle0) (norm_nonneg _)
    rw [hz0, mul_zero] at hprod
    exact zero_ne_one hprod
  have hrpow_inv : ((|s.im| / 7) ^ (-(1 / 2 - s.re)))⁻¹ = (|s.im| / 7) ^ (1 / 2 - s.re) := by
    rw [Real.rpow_neg (by positivity), inv_inv]
  have hge : (|s.im| / 7) ^ (1 / 2 - s.re) ≤ ‖_root_.RHTower.zetaChi s‖ := by
    rw [← hrpow_inv]
    have hinv := inv_anti₀ hrefl_pos hrefl_le
    have heq_inv : ‖_root_.RHTower.zetaChi s‖ = (‖_root_.RHTower.zetaChi (1 - conj s)‖)⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    rwa [← heq_inv] at hinv
  exact ⟨h1, h2, hge⟩

/-- **Quantitative Spira `ζ`-modulus amplification across all `0 < Re s < 1 / 2`, `184 < |Im s|`:**
`‖riemannZeta s‖ ≥ (|Im s| / 7)^{1/2 - Re s} * ‖riemannZeta (1 - conj s)‖`, and whenever
`riemannZeta s ≠ 0` one has strict inequality `‖riemannZeta (1 - conj s)‖ < ‖riemannZeta s‖`. -/
theorem strict_spira_zeta_amplification_above_oneHundredEightyFour
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|) :
    (|s.im| / 7) ^ (1 / 2 - s.re) * ‖riemannZeta (1 - conj s)‖ ≤ ‖riemannZeta s‖ ∧
      (riemannZeta s ≠ 0 → ‖riemannZeta (1 - conj s)‖ < ‖riemannZeta s‖) := by
  have hs_ne0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hhi; linarith only [hhi]
  have h1s_pos : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith only [hhi]
  have hfe := _root_.RHTower.zeta_eq_zetaChi_mul hs_ne0 hs_ne1
    (Complex.Gammaℝ_ne_zero_of_re_pos h1s_pos)
  have h1s_conj : conj (1 - conj s) = 1 - s := by simp
  have hzeta_conj : ‖riemannZeta (1 - s)‖ = ‖riemannZeta (1 - conj s)‖ := by
    rw [← h1s_conj, riemannZeta_conj, Complex.norm_conj]
  have hnorm_fe : ‖riemannZeta s‖ =
      ‖_root_.RHTower.zetaChi s‖ * ‖riemannZeta (1 - conj s)‖ := by
    rw [hfe, norm_mul, hzeta_conj]
  obtain ⟨h1_lt, h2_lt, hchi_ge⟩ := norm_zetaChi_ge_rpow_above_oneHundredEightyFour hs0 hhi him
  have hamp : (|s.im| / 7) ^ (1 / 2 - s.re) * ‖riemannZeta (1 - conj s)‖ ≤ ‖riemannZeta s‖ := by
    rw [hnorm_fe]
    exact mul_le_mul_of_nonneg_right hchi_ge (norm_nonneg _)
  refine ⟨hamp, fun hne => ?_⟩
  have hr_pos : 0 < ‖riemannZeta (1 - conj s)‖ := by
    by_contra hle0
    have hz0 : ‖riemannZeta (1 - conj s)‖ = 0 := le_antisymm (not_lt.mp hle0) (norm_nonneg _)
    rw [hz0, mul_zero] at hnorm_fe
    exact (norm_pos_iff.mpr hne).ne' hnorm_fe
  have hgt1 : 1 < (|s.im| / 7) ^ (1 / 2 - s.re) := h1_lt.trans h2_lt
  have hmul_lt : 1 * ‖riemannZeta (1 - conj s)‖ <
      (|s.im| / 7) ^ (1 / 2 - s.re) * ‖riemannZeta (1 - conj s)‖ :=
    mul_lt_mul_of_pos_right hgt1 hr_pos
  rw [one_mul] at hmul_lt
  exact hmul_lt.trans_le hamp

/-- **Amplified reflected-to-left witness production above height `184`:** if at `w = 1 - conj s`
(`0 < Re s < 1 / 2`, `184 < |Im s|`) any `(N₁, M₁)` Euler–Knopp partial sum (`M₁ ≥ 1`) beats its
tail by `η > 0`, then `‖(1 - 2^{1 - s}) ζ(s)‖ ≥ (2 / 15) * (|Im s| / 7)^{1/2 - Re s} * η > 0`,
producing an explicit `HasStrictPrimeGasWitness` at `s`. -/
theorem left_strict_witness_of_reflected_euler_excess_above_oneHundredEightyFour
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|)
    {Λ : ℝ} (hΛ : 0 < Λ) {N₁ M₁ : ℕ} (hM₁ : 1 ≤ M₁) {η : ℝ} (hη : 0 < η)
    (hbeat : eulerEtaTailBound N₁ M₁ (1 - conj s) + η ≤
      ‖eulerEtaPartialSum N₁ M₁ (1 - conj s)‖) :
    (2 / 15 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) * η ≤
        ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s‖ ∧
      HasStrictPrimeGasWitness s hs0 Λ := by
  set w : ℂ := 1 - conj s
  have hw_re : w.re = 1 - s.re := by simp [w]
  have hw0 : 0 < w.re := by rw [hw_re]; linarith only [hhi]
  have hw_ne1 : w ≠ 1 := fun h => by
    have := congrArg Complex.re h
    rw [hw_re, Complex.one_re] at this
    linarith only [this, hs0]
  have htb := norm_eta_sub_eulerEtaPartialSum_le hw0 hw_ne1 N₁ M₁ hM₁
  have htri : ‖eulerEtaPartialSum N₁ M₁ w‖ ≤
      ‖(1 - (2 : ℂ) ^ (1 - w)) * riemannZeta w‖ +
        ‖(1 - (2 : ℂ) ^ (1 - w)) * riemannZeta w - eulerEtaPartialSum N₁ M₁ w‖ := by
    have h := norm_sub_norm_le (eulerEtaPartialSum N₁ M₁ w)
      ((1 - (2 : ℂ) ^ (1 - w)) * riemannZeta w)
    rw [norm_sub_rev] at h
    linarith only [h]
  have hη_le_prod : η ≤ ‖1 - (2 : ℂ) ^ (1 - w)‖ * ‖riemannZeta w‖ := by
    rw [← norm_mul]
    linarith only [hbeat, htb, htri]
  have hfac_w_le : ‖1 - (2 : ℂ) ^ (1 - w)‖ ≤ 3 := by
    have h1w_re : (1 - w).re = s.re := by simp [w]
    have h2_le : ‖(2 : ℂ) ^ (1 - w)‖ ≤ 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos zero_lt_two, h1w_re]
      calc (2 : ℝ) ^ s.re ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith only [hhi])
        _ = 2 := Real.rpow_one 2
    have h := norm_sub_le (1 : ℂ) ((2 : ℂ) ^ (1 - w))
    rw [norm_one] at h
    linarith only [h, h2_le]
  have hzeta_w_ge : η / 3 ≤ ‖riemannZeta w‖ := by
    have h3 : η ≤ 3 * ‖riemannZeta w‖ :=
      hη_le_prod.trans (mul_le_mul_of_nonneg_right hfac_w_le (norm_nonneg _))
    linarith only [h3]
  have hspira := (strict_spira_zeta_amplification_above_oneHundredEightyFour hs0 hhi him).1
  have hzeta_s_ge : (|s.im| / 7) ^ (1 / 2 - s.re) * (η / 3) ≤ ‖riemannZeta s‖ :=
    (mul_le_mul_of_nonneg_left hzeta_w_ge (by positivity)).trans hspira
  have hfac_s_ge : (2 / 5 : ℝ) ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
    have hsq : ((7 / 5 : ℝ)) ^ (2 : ℕ) ≤ ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul zero_le_two]
      norm_num
    have h75 : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) :=
      (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : 2 ≠ 0)).mp hsq
    have h2_ge : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 - s.re) :=
      h75.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith only [hhi]))
    have hnorm2 : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos zero_lt_two, Complex.sub_re, Complex.one_re]
    have hlb := norm_sub_norm_le ((2 : ℂ) ^ (1 - s)) 1
    rw [hnorm2, norm_one, norm_sub_rev] at hlb
    linarith only [h2_ge, hlb]
  have heta_s_ge : (2 / 15 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) * η ≤
      ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s‖ := by
    rw [norm_mul]
    calc (2 / 15 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) * η
        = (2 / 5 : ℝ) * ((|s.im| / 7) ^ (1 / 2 - s.re) * (η / 3)) := by ring
      _ ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ * ‖riemannZeta s‖ :=
          mul_le_mul hfac_s_ge hzeta_s_ge (by positivity) (norm_nonneg _)
  have hpos_lhs : 0 < (2 / 15 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) * η := by
    have hr_pos : 0 < (|s.im| / 7) ^ (1 / 2 - s.re) :=
      Real.rpow_pos_of_pos (by linarith only [him]) _
    positivity
  have hzeta_ne : riemannZeta s ≠ 0 := by
    intro hz0
    rw [hz0, mul_zero, norm_zero] at heta_s_ge
    linarith only [hpos_lhs, heta_s_ge]
  exact ⟨heta_s_ge, (hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 (by linarith only [hhi]) hΛ).mpr hzeta_ne⟩

/-- **Riemann–Siegel / `gN` off-line Dirichlet-domination witness bridge above height `184`:**
for any `s` with `0 < Re s < 1 / 2` and `184 < |Im s|`, because `‖zetaChi (1 - conj s)‖ < 1` holds
unconditionally, if some cutoff `N` satisfies
`‖dirichletPoly N (conj s)‖ + ‖riemannZeta (1 - conj s) - gN N (1 - conj s)‖ < ‖dirichletPoly N (1 - conj s)‖`,
then `s` unconditionally carries a `HasStrictPrimeGasWitness`. -/
theorem left_strict_witness_of_dirichlet_domination_above_oneHundredEightyFour
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|)
    {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ}
    (hdom : ‖_root_.RHTower.dirichletPoly N (conj s)‖ +
        ‖riemannZeta (1 - conj s) - _root_.RHTower.gN N (1 - conj s)‖ <
      ‖_root_.RHTower.dirichletPoly N (1 - conj s)‖) :
    HasStrictPrimeGasWitness s hs0 Λ := by
  obtain ⟨-, hchi_le, h1, h2⟩ := norm_zetaChi_reflected_le_rpow_above_oneHundredEightyFour hs0 hhi him
  have hchi_le1 : ‖_root_.RHTower.zetaChi (1 - conj s)‖ ≤ 1 :=
    (hchi_le.trans h1.le).trans h2.le
  have hsub : 1 - (1 - conj s) = conj s := by ring
  have hdom' : ‖_root_.RHTower.dirichletPoly N (1 - (1 - conj s))‖ +
        ‖riemannZeta (1 - conj s) - _root_.RHTower.gN N (1 - conj s)‖ <
      ‖_root_.RHTower.dirichletPoly N (1 - conj s)‖ := by
    rwa [hsub]
  have hgN_gt := _root_.RHTower.norm_gN_ge_of_dirichlet_domination hchi_le1 hdom'
  have hzeta_w_ne : riemannZeta (1 - conj s) ≠ 0 := by
    intro hzw
    rw [hzw, zero_sub, norm_neg] at hgN_gt
    exact lt_irrefl _ hgN_gt
  have hspira := (strict_spira_zeta_amplification_above_oneHundredEightyFour hs0 hhi him).1
  have hr_pos : 0 < (|s.im| / 7) ^ (1 / 2 - s.re) :=
    Real.rpow_pos_of_pos (by linarith only [him]) _
  have hzeta_s_pos : 0 < ‖riemannZeta s‖ :=
    (mul_pos hr_pos (norm_pos_iff.mpr hzeta_w_ne)).trans_le hspira
  exact (hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 (by linarith only [hhi]) hΛ).mpr
    (norm_pos_iff.mp hzeta_s_pos)

/-! ### 3. Single-Quartet Positive Multiplicative Surgery Firewall on `Ω_open` -/

private lemma dirichletSurgPoly_conj (M : ℕ) (c : ℕ → ℝ) (z : ℂ) :
    dirichletSurgPoly M c (conj z) = conj (dirichletSurgPoly M c z) := by
  unfold dirichletSurgPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_nn : (0 : ℝ) ≤ (d : ℕ) := Nat.cast_nonneg d
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  have hcast : (d : ℂ) = ((d : ℝ) : ℂ) := by norm_cast
  rcases eq_or_ne (d : ℝ) 0 with hd0 | hd_ne
  · have : d = 0 := by exact_mod_cast hd0
    have h1 := (Finset.mem_Icc.mp hd).1
    omega
  · rw [hcast, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hd_ne),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hd_ne),
      ← Complex.exp_conj, ← Complex.ofReal_log hd_nn]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal]

private lemma dirichletSurgWeight_prime_pow_coprime_mul {p M : ℕ} (hp : p.Prime)
    {c : ℕ → ℝ} (hc1 : c 1 = 1)
    (hsupp : ∀ d ∈ Finset.Icc 2 M, c d ≠ 0 → ∃ r : ℕ, 1 ≤ r ∧ d = p ^ r)
    (hM1 : 1 ≤ M) {m n : ℕ} (hcop : Nat.Coprime m n) :
    dirichletSurgWeight M c (m * n) = dirichletSurgWeight M c m * dirichletSurgWeight M c n := by
  have hnot_both : ¬(p ∣ m ∧ p ∣ n) := fun ⟨hm, hn⟩ =>
    hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hm hn)
  have hunit_of_not_dvd : ∀ k : ℕ, ¬(p ∣ k) → dirichletSurgWeight M c k = 1 := by
    intro k hnk
    unfold dirichletSurgWeight
    rw [Finset.sum_eq_single 1]
    · simp [hc1]
    · intro d hd hd1
      have hd2 : d ∈ Finset.Icc 2 M :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega, (Finset.mem_Icc.mp hd).2⟩
      by_cases hcd : c d = 0
      · simp [hcd]
      · obtain ⟨r, hr1, rfl⟩ := hsupp d hd2 hcd
        have hnd : ¬(p ^ r ∣ k) := fun hdvd =>
          hnk ((dvd_pow_self p (by omega : r ≠ 0)).trans hdvd)
        rw [if_neg hnd]
    · intro hnot
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hM1⟩) hnot
  have hmul_of_not_dvd : ∀ u v : ℕ, ¬(p ∣ u) →
      dirichletSurgWeight M c (u * v) = dirichletSurgWeight M c v := by
    intro u v hnu
    have hcop_pu : Nat.Coprime p u := hp.coprime_iff_not_dvd.mpr hnu
    unfold dirichletSurgWeight
    refine Finset.sum_congr rfl fun d hd => ?_
    by_cases hd1 : d = 1
    · subst hd1; simp
    · have hd2 : d ∈ Finset.Icc 2 M :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega, (Finset.mem_Icc.mp hd).2⟩
      by_cases hcd : c d = 0
      · simp [hcd]
      · obtain ⟨r, _, rfl⟩ := hsupp d hd2 hcd
        have hcop_ru : Nat.Coprime (p ^ r) u := hcop_pu.pow_left r
        have hdvd_iff : p ^ r ∣ u * v ↔ p ^ r ∣ v :=
          ⟨fun h => hcop_ru.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h u⟩
        by_cases hv_dvd : p ^ r ∣ v
        · rw [if_pos (hdvd_iff.mpr hv_dvd), if_pos hv_dvd]
        · rw [if_neg (mt hdvd_iff.mp hv_dvd), if_neg hv_dvd]
  by_cases hpm : p ∣ m
  · have hpn : ¬(p ∣ n) := fun h => hnot_both ⟨hpm, h⟩
    rw [mul_comm m n, hmul_of_not_dvd n m hpn, hunit_of_not_dvd n hpn, mul_one]
  · rw [hmul_of_not_dvd m n hpm, hunit_of_not_dvd m hpm, one_mul]

/-- **Single-quartet positive multiplicative surgery firewall on `Ω_open`:**
for every remaining point `s₀` (`3001 / 24000 ≤ Re s₀ < 1 / 2`, `184 < |Im s₀|`), there exist a
prime `p ∈ {5, 7}`, cutoff `M ≥ 1`, and nonnegative coefficients `c : ℕ → ℝ` (`c 1 = 1`) such that
`a = dirichletSurgWeight M c` and `F(z) = dirichletSurgPoly M c z * riemannZeta z` satisfy:
1. `a(1) = 1`, `a(n) ≥ 1` (`n ≥ 1`), `a(2^u 3^v) = 1`, and `a(m n) = a(m) a(n)` for all coprime `m, n`;
2. Across the **entire** four-point quartet `Q = {s₀, conj s₀, 1 - s₀, 1 - conj s₀}`, `F(z) = 0`,
   `F(z) = zetaChi z * F(1 - z)`, `bilateralReflectionDefect a K z → 0`, and every Prime-Gas clock
   `weightedAdjacentCutoff a t j X z → 0`. -/
theorem single_quartet_positive_multiplicative_firewall_above_oneHundredEightyFour
    {s₀ : ℂ} (hlo : 3001 / 24000 ≤ s₀.re) (hhi : s₀.re < 1 / 2) (him : 184 < |s₀.im|) :
    ∃ (p M : ℕ) (c : ℕ → ℝ),
      (p = 5 ∨ p = 7) ∧ 1 ≤ M ∧ c 1 = 1 ∧ (∀ d : ℕ, 0 ≤ c d) ∧
      dirichletSurgWeight M c 1 = 1 ∧
      (∀ n : ℕ, 1 ≤ n → 1 ≤ dirichletSurgWeight M c n) ∧
      (∀ u v : ℕ, dirichletSurgWeight M c (2 ^ u * 3 ^ v) = 1) ∧
      (∀ m n : ℕ, Nat.Coprime m n →
        dirichletSurgWeight M c (m * n) =
          dirichletSurgWeight M c m * dirichletSurgWeight M c n) ∧
      (∀ z ∈ ({s₀, conj s₀, 1 - s₀, 1 - conj s₀} : Finset ℂ),
        dirichletSurgPoly M c z * riemannZeta z = 0 ∧
        dirichletSurgPoly M c z * riemannZeta z =
          _root_.RHTower.zetaChi z * (dirichletSurgPoly M c (1 - z) * riemannZeta (1 - z)) ∧
        Tendsto (fun K : ℕ => bilateralReflectionDefect (dirichletSurgWeight M c) K z)
          atTop (𝓝 0) ∧
        ∀ (t : ExceptionalTime) (j : ℕ),
          Tendsto (fun X : ℕ => weightedAdjacentCutoff (dirichletSurgWeight M c) t j X z)
            atTop (𝓝 0)) := by
  have hs₀_pos : 0 < s₀.re := by linarith only [hlo]
  have hs₀_lt1 : s₀.re < 1 := by linarith only [hhi]
  have hs₀_im_ne : s₀.im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at him
    linarith only [him]
  have hphase := five_seven_phase_ne_one hs₀_im_ne
  obtain ⟨p, hp57, hu_ne1⟩ : ∃ p : ℕ, (p = 5 ∨ p = 7) ∧
      Complex.exp (-(Real.log p : ℂ) * (s₀.im : ℂ) * I) ≠ 1 := by
    rcases hphase with h5 | h7
    · exact ⟨5, Or.inl rfl, by simpa using h5⟩
    · exact ⟨7, Or.inr rfl, by simpa using h7⟩
  have hp_prime : Nat.Prime p := by rcases hp57 with rfl | rfl <;> decide
  have hp_gt1 : 1 < p := hp_prime.one_lt
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_prime.pos
  set u : ℂ := Complex.exp (-(Real.log p : ℂ) * (s₀.im : ℂ) * I)
  have hu_norm : ‖u‖ = 1 := by
    dsimp only [u]; rw [Complex.norm_exp]
    have hre0 : (-(Real.log p : ℂ) * (s₀.im : ℂ) * I).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hre0, Real.exp_zero]
  obtain ⟨k, hk1, hvk_neg⟩ := PositiveAnnihilator.exists_large_pow_re_neg hu_norm hu_ne1 1
  set v : ℂ := u ^ k
  have hv_norm : ‖v‖ = 1 := by dsimp only [v]; rw [norm_pow, hu_norm, one_pow]
  set r₀ : ℝ := (p : ℝ) ^ (-(k : ℝ) * s₀.re)
  set r₁ : ℝ := (p : ℝ) ^ (-(k : ℝ) * (1 - s₀.re))
  have hr₀_pos : 0 < r₀ := Real.rpow_pos_of_pos hp_pos _
  have hr₁_pos : 0 < r₁ := Real.rpow_pos_of_pos hp_pos _
  let a₁ : ℝ := -2 * v.re * r₀⁻¹
  let a₂ : ℝ := (r₀⁻¹) ^ 2
  let b₁ : ℝ := -2 * v.re * r₁⁻¹
  let b₂ : ℝ := (r₁⁻¹) ^ 2
  have ha₁ : 0 < a₁ := mul_pos (by linarith only [hvk_neg]) (inv_pos.mpr hr₀_pos)
  have ha₂ : 0 < a₂ := pow_pos (inv_pos.mpr hr₀_pos) 2
  have hb₁ : 0 < b₁ := mul_pos (by linarith only [hvk_neg]) (inv_pos.mpr hr₁_pos)
  have hb₂ : 0 < b₂ := pow_pos (inv_pos.mpr hr₁_pos) 2
  let d₁ := p ^ k
  let d₂ := p ^ (2 * k)
  let d₃ := p ^ (3 * k)
  let d₄ := p ^ (4 * k)
  have h1_lt_d1 : 1 < d₁ := one_lt_pow₀ hp_gt1 (by omega)
  have hd12 : d₁ < d₂ := Nat.pow_lt_pow_right hp_gt1 (by omega)
  have hd23 : d₂ < d₃ := Nat.pow_lt_pow_right hp_gt1 (by omega)
  have hd34 : d₃ < d₄ := Nat.pow_lt_pow_right hp_gt1 (by omega)
  let c (d : ℕ) : ℝ :=
    if d = 1 then 1
    else if d = d₁ then a₁ + b₁
    else if d = d₂ then a₂ + a₁ * b₁ + b₂
    else if d = d₃ then a₁ * b₂ + a₂ * b₁
    else if d = d₄ then a₂ * b₂
    else 0
  have hc1 : c 1 = 1 := by simp [c]
  have hc_nn : ∀ d : ℕ, 0 ≤ c d := fun d => by
    dsimp only [c]; split_ifs <;> positivity
  have hsupp : ∀ d ∈ Finset.Icc 2 d₄, c d ≠ 0 → ∃ r : ℕ, 1 ≤ r ∧ d = p ^ r := by
    intro d hd hcd
    have hd_ne1 : d ≠ 1 := by have := (Finset.mem_Icc.mp hd).1; omega
    dsimp only [c] at hcd
    rw [if_neg hd_ne1] at hcd
    by_cases h1 : d = d₁
    · exact ⟨k, hk1, h1⟩
    · rw [if_neg h1] at hcd
      by_cases h2 : d = d₂
      · exact ⟨2 * k, by omega, h2⟩
      · rw [if_neg h2] at hcd
        by_cases h3 : d = d₃
        · exact ⟨3 * k, by omega, h3⟩
        · rw [if_neg h3] at hcd
          by_cases h4 : d = d₄
          · exact ⟨4 * k, by omega, h4⟩
          · rw [if_neg h4] at hcd
            exact absurd rfl hcd
  have hpow_Z : ∀ (m : ℕ) (z : ℂ), ((p ^ (m * k) : ℕ) : ℂ) ^ (-z) = (((p ^ k : ℕ) : ℂ) ^ (-z)) ^ m := by
    intro m z
    induction m with
    | zero => simp
    | succ m ih =>
      have ha_nn : (0 : ℝ) ≤ (p ^ (m * k) : ℕ) := Nat.cast_nonneg _
      have hb_nn : (0 : ℝ) ≤ (p ^ k : ℕ) := Nat.cast_nonneg _
      rw [Nat.succ_mul, pow_add, Nat.cast_mul,
        show ((p ^ (m * k) : ℕ) : ℂ) * ((p ^ k : ℕ) : ℂ) =
          (((p ^ (m * k) : ℕ) : ℝ) : ℂ) * (((p ^ k : ℕ) : ℝ) : ℂ) by simp,
        Complex.mul_cpow_ofReal_nonneg ha_nn hb_nn]
      simp only [Complex.ofReal_natCast]
      rw [ih, pow_succ]
  have hpoly_fac : ∀ z : ℂ, dirichletSurgPoly d₄ c z =
      (1 + (a₁ : ℂ) * ((d₁ : ℕ) : ℂ) ^ (-z) + (a₂ : ℂ) * (((d₁ : ℕ) : ℂ) ^ (-z)) ^ 2) *
      (1 + (b₁ : ℂ) * ((d₁ : ℕ) : ℂ) ^ (-z) + (b₂ : ℂ) * (((d₁ : ℕ) : ℂ) ^ (-z)) ^ 2) := by
    intro z
    classical
    let S₅ : Finset ℕ := {1, d₁, d₂, d₃, d₄}
    have hsub : S₅ ⊆ Finset.Icc 1 d₄ := by
      intro x hx
      simp only [S₅, Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
    have hzero_out : ∀ x ∈ Finset.Icc 1 d₄, x ∉ S₅ → (c x : ℂ) * (x : ℂ) ^ (-z) = 0 := by
      intro x _ hx
      simp only [S₅, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      rcases hx with ⟨h1, h2, h3, h4, h5⟩
      simp [c, h1, h2, h3, h4, h5]
    rw [dirichletSurgPoly, ← Finset.sum_subset hsub hzero_out]
    have hn1 : (1 : ℕ) ∉ ({d₁, d₂, d₃, d₄} : Finset ℕ) := by simp; omega
    have hn2 : d₁ ∉ ({d₂, d₃, d₄} : Finset ℕ) := by simp; omega
    have hn3 : d₂ ∉ ({d₃, d₄} : Finset ℕ) := by simp; omega
    have hn4 : d₃ ∉ ({d₄} : Finset ℕ) := by simp; omega
    dsimp only [S₅]
    rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_insert hn3,
      Finset.sum_insert hn4, Finset.sum_singleton]
    have hc_d1 : c d₁ = a₁ + b₁ := by simp [c, show d₁ ≠ 1 by omega]
    have hc_d2 : c d₂ = a₂ + a₁ * b₁ + b₂ := by
      simp [c, show d₂ ≠ 1 by omega, show d₂ ≠ d₁ by omega]
    have hc_d3 : c d₃ = a₁ * b₂ + a₂ * b₁ := by
      simp [c, show d₃ ≠ 1 by omega, show d₃ ≠ d₁ by omega, show d₃ ≠ d₂ by omega]
    have hc_d4 : c d₄ = a₂ * b₂ := by
      simp [c, show d₄ ≠ 1 by omega, show d₄ ≠ d₁ by omega,
        show d₄ ≠ d₂ by omega, show d₄ ≠ d₃ by omega]
    rw [hc1, hc_d1, hc_d2, hc_d3, hc_d4]
    dsimp only [d₂, d₃, d₄]
    rw [hpow_Z 2 z, hpow_Z 3 z, hpow_Z 4 z]
    dsimp only [d₁]
    push_cast
    rw [Complex.one_cpow]
    ring
  have hd1_s0 : ((d₁ : ℕ) : ℂ) ^ (-s₀) = (r₀ : ℂ) * v := by
    dsimp only [d₁]
    have hpk_pos : (0 : ℝ) < (p ^ k : ℕ) := by exact_mod_cast pow_pos hp_prime.pos k
    rw [show ((p ^ k : ℕ) : ℂ) = (((p ^ k : ℕ) : ℝ) : ℂ) by simp,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpk_pos.ne'),
      ← Complex.ofReal_log hpk_pos.le, Nat.cast_pow, Real.log_pow]
    dsimp only [r₀, v, u]
    rw [Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im s₀]
    push_cast; ring
  have hd1_1s0 : ((d₁ : ℕ) : ℂ) ^ (-(1 - s₀)) = (r₁ : ℂ) * conj v := by
    dsimp only [d₁]
    have hpk_pos : (0 : ℝ) < (p ^ k : ℕ) := by exact_mod_cast pow_pos hp_prime.pos k
    have hcv : conj v = Complex.exp ((k : ℂ) * ((Real.log p : ℂ) * (s₀.im : ℂ) * I)) := by
      dsimp only [v, u]
      rw [← Complex.exp_nat_mul, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_neg, map_natCast, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [show ((p ^ k : ℕ) : ℂ) = (((p ^ k : ℕ) : ℝ) : ℂ) by simp,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpk_pos.ne'),
      ← Complex.ofReal_log hpk_pos.le, Nat.cast_pow, Real.log_pow]
    dsimp only [r₁]
    rw [hcv, Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have h1s0 : 1 - s₀ = (((1 - s₀.re : ℝ) : ℂ) - (s₀.im : ℂ) * I) := by
      conv_lhs => rw [← Complex.re_add_im s₀]
      push_cast; ring
    rw [h1s0]; push_cast; ring
  have hpoly_s0 : dirichletSurgPoly d₄ c s₀ = 0 := by
    rw [hpoly_fac s₀, hd1_s0]
    have hr_ne : (r₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₀_pos.ne'
    have hq0 : 1 + (a₁ : ℂ) * ((r₀ : ℂ) * v) + (a₂ : ℂ) * ((r₀ : ℂ) * v) ^ 2 =
        1 + ((-2 * v.re : ℝ) : ℂ) * v + v ^ 2 := by
      dsimp only [a₁, a₂]; push_cast; field_simp [hr_ne]
    rw [hq0, PositiveAnnihilator.unit_quadratic hv_norm, zero_mul]
  have hpoly_1s0 : dirichletSurgPoly d₄ c (1 - s₀) = 0 := by
    rw [hpoly_fac (1 - s₀), hd1_1s0]
    have hr_ne : (r₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₁_pos.ne'
    have hcv_norm : ‖conj v‖ = 1 := by rw [Complex.norm_conj, hv_norm]
    have hq1 : 1 + (b₁ : ℂ) * ((r₁ : ℂ) * conj v) + (b₂ : ℂ) * ((r₁ : ℂ) * conj v) ^ 2 =
        1 + ((-2 * (conj v).re : ℝ) : ℂ) * conj v + (conj v) ^ 2 := by
      rw [Complex.conj_re]
      dsimp only [b₁, b₂]; push_cast; field_simp [hr_ne]
    rw [hq1, PositiveAnnihilator.unit_quadratic hcv_norm, mul_zero]
  have hpoly_cs0 : dirichletSurgPoly d₄ c (conj s₀) = 0 := by
    rw [dirichletSurgPoly_conj, hpoly_s0, map_zero]
  have hpoly_1cs0 : dirichletSurgPoly d₄ c (1 - conj s₀) = 0 := by
    have heq : 1 - conj s₀ = conj (1 - s₀) := by simp
    rw [heq, dirichletSurgPoly_conj, hpoly_1s0, map_zero]
  have ha_one : dirichletSurgWeight d₄ c 1 = 1 := by
    unfold dirichletSurgWeight
    rw [Finset.sum_eq_single 1]
    · simp [hc1]
    · intro d _ hd1
      have hnd : ¬(d ∣ 1) := fun h => hd1 (Nat.dvd_one.mp h)
      rw [if_neg hnd]
    · intro hnot
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) hnot
  have hw_ge1 : ∀ n : ℕ, 1 ≤ n → 1 ≤ dirichletSurgWeight d₄ c n := by
    intro n _
    unfold dirichletSurgWeight
    have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 d₄ := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hle := Finset.single_le_sum (f := fun d => if d ∣ n then c d else 0)
      (fun d _ => by split_ifs <;> [exact hc_nn d; exact le_rfl]) h1_mem
    simpa only [one_dvd, ↓reduceIte, hc1] using hle
  have hsmooth : ∀ u₂ v₃ : ℕ, dirichletSurgWeight d₄ c (2 ^ u₂ * 3 ^ v₃) = 1 := by
    intro u₂ v₃
    have hcop2 : Nat.Coprime 2 p := by rcases hp57 with rfl | rfl <;> decide
    have hcop3 : Nat.Coprime 3 p := by rcases hp57 with rfl | rfl <;> decide
    have hcop : Nat.Coprime (2 ^ u₂ * 3 ^ v₃) p :=
      (hcop2.pow_left u₂).mul_left (hcop3.pow_left v₃)
    have hnot_p : ¬(p ∣ 2 ^ u₂ * 3 ^ v₃) := fun hd =>
      hp_prime.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hd (dvd_refl p))
    unfold dirichletSurgWeight
    rw [Finset.sum_eq_single 1]
    · simp [hc1]
    · intro d hd hd1
      have hd2 : d ∈ Finset.Icc 2 d₄ :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega, (Finset.mem_Icc.mp hd).2⟩
      by_cases hcd : c d = 0
      · simp [hcd]
      · obtain ⟨r, hr1, rfl⟩ := hsupp d hd2 hcd
        have hnd : ¬(p ^ r ∣ 2 ^ u₂ * 3 ^ v₃) := fun hdvd =>
          hnot_p ((dvd_pow_self p (by omega)).trans hdvd)
        rw [if_neg hnd]
    · intro hnot
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) hnot
  have hmul : ∀ m n : ℕ, Nat.Coprime m n →
      dirichletSurgWeight d₄ c (m * n) =
        dirichletSurgWeight d₄ c m * dirichletSurgWeight d₄ c n :=
    fun m n hcop => dirichletSurgWeight_prime_pow_coprime_mul hp_prime hc1 hsupp (by omega) hcop
  have hQ_zero : ∀ z ∈ ({s₀, conj s₀, 1 - s₀, 1 - conj s₀} : Finset ℂ),
      0 < z.re ∧ z.re < 1 ∧ dirichletSurgPoly d₄ c z = 0 ∧ dirichletSurgPoly d₄ c (1 - z) = 0 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨hs₀_pos, hs₀_lt1, hpoly_s0, hpoly_1s0⟩
    · exact ⟨by simp [hs₀_pos], by simp [hs₀_lt1], hpoly_cs0, hpoly_1cs0⟩
    · refine ⟨by simp; linarith only [hs₀_lt1], by simp; linarith only [hs₀_pos], hpoly_1s0, ?_⟩
      rwa [show 1 - (1 - s₀) = s₀ by ring]
    · refine ⟨by simp; linarith only [hs₀_lt1], by simp; linarith only [hs₀_pos], hpoly_1cs0, ?_⟩
      rwa [show 1 - (1 - conj s₀) = conj s₀ by ring]
  refine ⟨p, d₄, c, hp57, by omega, hc1, hc_nn, ha_one, hw_ge1, hsmooth, hmul, fun z hz => ?_⟩
  obtain ⟨hz0, hz1, hQz, hQ1z⟩ := hQ_zero z hz
  refine ⟨by rw [hQz, zero_mul], by rw [hQz, hQ1z, zero_mul, zero_mul, mul_zero], ?_, ?_⟩
  · simpa only [hQz, hQ1z, sub_self, zero_mul] using
      tendsto_bilateralReflectionDefect_dirichletSurgWeight d₄ c hz0 hz1
  · intro t j
    simpa only [hQz, zero_mul] using
      tendsto_weightedAdjacentCutoff_dirichletSurgWeight d₄ c t j hz0

/-! ### 4. Multi-Ordinate Repulsion, Pigeonhole Witnesses, and Dyadic Parity Poles on `Ω_open` -/

private lemma zeta_ne_zero_left_of_reflected {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    (hne : riemannZeta (1 - conj s) ≠ 0) : riemannZeta s ≠ 0 := by
  intro hzs
  have h1s : riemannZeta (1 - s) = 0 :=
    (_root_.RHTower.riemannZeta_one_sub_eq_zero_iff hs0 (by linarith only [hhi])).mpr hzs
  have hconj : riemannZeta (1 - conj s) = 0 := by
    have heq : 1 - conj s = conj (1 - s) := by simp
    rw [heq, riemannZeta_conj, h1s, map_zero]
  exact hne hconj

/-- **Two-point Hadamard zero-repulsion witness production on `Ω_open`:**
for any `1 < σs ≤ 2`, `Λ > 0`, and any two points `s₁, s₂` in
`{3001 / 24000 ≤ Re s < 1 / 2 ∧ 184 < Im s}` with `Im s₁ + 4 ≤ Im s₂` violating the 5-point
repulsion budget at `(1 - Re s₁, 1 - Re s₂)`, at least one of `s₁` or `s₂` unconditionally
possesses a `HasStrictPrimeGasWitness`. -/
theorem two_point_repulsion_strict_witness_on_remaining_strip
    {σs Λ : ℝ} (hσ1 : 1 < σs) (hσ2 : σs ≤ 2) (hΛ : 0 < Λ) {s₁ s₂ : ℂ}
    (hlo₁ : 3001 / 24000 ≤ s₁.re) (hhi₁ : s₁.re < 1 / 2)
    (hlo₂ : 3001 / 24000 ≤ s₂.re) (hhi₂ : s₂.re < 1 / 2)
    (him₁ : 184 < s₁.im) (hgap : s₁.im + 4 ≤ s₂.im)
    (hviol : 2 / (σs - 1) + Real.log s₁.im + Real.log s₂.im +
        (Real.log (s₂.im + s₁.im) + Real.log (s₂.im - s₁.im)) / 2 + 13 / 5 <
      2 / (σs - (1 - s₁.re)) + 2 / (σs - (1 - s₂.re))) :
    HasStrictPrimeGasWitness s₁ (by linarith only [hlo₁]) Λ ∨
      HasStrictPrimeGasWitness s₂ (by linarith only [hlo₂]) Λ := by
  set w₁ : ℂ := 1 - conj s₁
  set w₂ : ℂ := 1 - conj s₂
  have hw₁_re : w₁.re = 1 - s₁.re := by simp [w₁]
  have hw₂_re : w₂.re = 1 - s₂.re := by simp [w₂]
  have hw₁_im : w₁.im = s₁.im := by simp [w₁]
  have hw₂_im : w₂.im = s₂.im := by simp [w₂]
  have hrep := five_point_repulsion_forces_zetaFree_margin halfTurnClock 0 hσ1 hσ2
    (w₁ := w₁) (w₂ := w₂)
    (by rw [hw₁_re]; linarith only [hhi₁])
    (by rw [hw₁_re]; linarith only [hlo₁])
    (by rw [hw₂_re]; linarith only [hhi₂])
    (by rw [hw₂_re]; linarith only [hlo₂])
    (by rw [hw₁_im]; linarith only [him₁])
    (by rw [hw₁_im, hw₂_im]; exact hgap)
    (by rwa [hw₁_re, hw₂_re, hw₁_im, hw₂_im])
  rcases hrep with h₁ | h₂
  · have hw₁0 : 0 < w₁.re := by rw [hw₁_re]; linarith only [hhi₁]
    have hw₁_ne1 : w₁ ≠ 1 := fun he => by
      have := congrArg Complex.re he; rw [hw₁_re, Complex.one_re] at this; linarith only [this, hlo₁]
    have hzw₁ := (exists_zetaFree_margin_iff_zeta_ne_zero halfTurnClock 0 hw₁0 hw₁_ne1).mp h₁
    have hzs₁ := zeta_ne_zero_left_of_reflected (by linarith only [hlo₁]) hhi₁ hzw₁
    exact Or.inl ((hasStrictPrimeGasWitness_iff_zeta_ne_zero (by linarith only [hlo₁])
      (by linarith only [hhi₁]) hΛ).mpr hzs₁)
  · have hw₂0 : 0 < w₂.re := by rw [hw₂_re]; linarith only [hhi₂]
    have hw₂_ne1 : w₂ ≠ 1 := fun he => by
      have := congrArg Complex.re he; rw [hw₂_re, Complex.one_re] at this; linarith only [this, hlo₂]
    have hzw₂ := (exists_zetaFree_margin_iff_zeta_ne_zero halfTurnClock 0 hw₂0 hw₂_ne1).mp h₂
    have hzs₂ := zeta_ne_zero_left_of_reflected (by linarith only [hlo₂]) hhi₂ hzw₂
    exact Or.inr ((hasStrictPrimeGasWitness_iff_zeta_ne_zero (by linarith only [hlo₂])
      (by linarith only [hhi₂]) hΛ).mpr hzs₂)

/-- **Unconditional pigeonhole strict-witness production on `Ω_open` at every height `|τ| > 184`:**
in any ordinate window `[τ - h, τ + h]` (`|τ| > 184`), every finite probe set
`S ⊆ {3001 / 24000 ≤ Re s < 1 / 2 ∧ |Im s - τ| ≤ h}` of cardinality exceeding
`4 (1 + h^2) (xiLineTwoLogDerivConstant + log(|τ| + 4))` contains at least one point `s ∈ S`
carrying an unconditional `HasStrictPrimeGasWitness`. -/
theorem pigeonhole_strict_witness_on_remaining_strip
    {h τ Λ : ℝ} (hΛ : 0 < Λ) {S : Finset ℂ}
    (hS : ∀ s ∈ S, 3001 / 24000 ≤ s.re ∧ s.re < 1 / 2 ∧ |s.im - τ| ≤ h)
    (hcard : 4 * (1 + h ^ 2) * (_root_.RHTower.xiLineTwoLogDerivConstant + Real.log (|τ| + 4)) <
      (S.card : ℝ)) :
    ∃ s : ℂ, ∃ hs : s ∈ S,
      HasStrictPrimeGasWitness s (by linarith only [(hS s hs).1]) Λ := by
  classical
  let reflMap : ℂ → ℂ := fun s => 1 - conj s
  have hrefl_inj : Function.Injective reflMap := by
    intro x y hxy
    have h1 : conj x = conj y := by
      dsimp [reflMap] at hxy
      linear_combination -hxy
    simpa only [Complex.conj_conj] using congrArg conj h1
  let S' : Finset ℂ := S.image reflMap
  have hS'_card : S'.card = S.card := Finset.card_image_of_injective S hrefl_inj
  have hS'_mem : ∀ w ∈ S', 1 / 2 < w.re ∧ w.re ≤ 20999 / 24000 ∧ |w.im - τ| ≤ h := by
    intro w hw
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨h1, h2, h3⟩ := hS s hs
    refine ⟨?_, ?_, ?_⟩
    · simp only [reflMap, Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith only [h2]
    · simp only [reflMap, Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith only [h1]
    · simpa only [reflMap, Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg] using h3
  obtain ⟨w, hwS', hmarg⟩ := exists_point_with_zetaFree_margin_of_card_gt halfTurnClock 0 hS'_mem
    (by rwa [hS'_card])
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hwS'
  obtain ⟨hlo, hhi, -⟩ := hS s hs
  have hw0 : 0 < (reflMap s).re := by
    simp only [reflMap, Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith only [hhi]
  have hw_ne1 : reflMap s ≠ 1 := fun he => by
    have := congrArg Complex.re he
    simp only [reflMap, Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    linarith only [this, hlo]
  have hzw := (exists_zetaFree_margin_iff_zeta_ne_zero halfTurnClock 0 hw0 hw_ne1).mp hmarg
  have hzs := zeta_ne_zero_left_of_reflected (by linarith only [hlo]) hhi hzw
  exact ⟨s, hs, (hasStrictPrimeGasWitness_iff_zeta_ne_zero (by linarith only [hlo])
    (by linarith only [hhi]) hΛ).mpr hzs⟩

/-- On **every** nonempty open horizontal subinterval `(a, b) ⊆ [3001 / 24000, 1 / 2)` at **every**
height `τ ∈ ℝ` (including all `|τ| > 184`), infinitely many points `σ + i τ` (`a < σ < b`)
unconditionally possess a `HasStrictPrimeGasWitness`. -/
theorem infinite_strict_witnesses_on_every_horizontal_subinterval_above_oneHundredEightyFour
    (τ : ℝ) {Λ a b : ℝ} (hΛ : 0 < Λ) (hab : a < b)
    (ha : 3001 / 24000 ≤ a) (hb : b ≤ 1 / 2) :
    {σ : ℝ | a < σ ∧ σ < b ∧ ∃ hs0 : 0 < (((σ : ℂ) + (τ : ℂ) * I)).re,
      HasStrictPrimeGasWitness ((σ : ℂ) + (τ : ℂ) * I) hs0 Λ}.Infinite := by
  have hinf := infinite_zetaFree_margin_on_horizontal_interval halfTurnClock 0 τ
    (a := 1 - b) (b := 1 - a) (by linarith only [hab]) (by linarith only [hb]) (by linarith only [ha])
  let φ : ℝ → ℝ := fun u => 1 - u
  have hφ_inj : Function.Injective φ := fun x y hxy => by dsimp [φ] at hxy; linarith only [hxy]
  refine (hinf.image hφ_inj.injOn).mono ?_
  rintro σ ⟨u, ⟨hu1, hu2, hmarg⟩, rfl⟩
  dsimp only [φ]
  have hre_eq : (((1 - u : ℝ) : ℂ) + (τ : ℂ) * I).re = 1 - u := by simp
  have hσ0 : 0 < (((1 - u : ℝ) : ℂ) + (τ : ℂ) * I).re := by rw [hre_eq]; linarith only [hu2, ha]
  have hσ_hi : (((1 - u : ℝ) : ℂ) + (τ : ℂ) * I).re < 1 / 2 := by rw [hre_eq]; linarith only [hu1, hb]
  refine ⟨by linarith only [hu2], by linarith only [hu1], hσ0, ?_⟩
  have hw0 : 0 < ((u : ℂ) + (τ : ℂ) * I).re := by simp; linarith only [hu1, hb]
  have hw_ne1 : ((u : ℂ) + (τ : ℂ) * I) ≠ 1 := fun he => by
    have := congrArg Complex.re he; simp at this; linarith only [this, hu2, ha]
  have hzw := (exists_zetaFree_margin_iff_zeta_ne_zero halfTurnClock 0 hw0 hw_ne1).mp hmarg
  have hrefl_eq : 1 - conj (((1 - u : ℝ) : ℂ) + (τ : ℂ) * I) = (u : ℂ) + (τ : ℂ) * I := by
    apply Complex.ext <;> simp
  have hzs := zeta_ne_zero_left_of_reflected hσ0 hσ_hi (by rwa [hrefl_eq])
  exact (hasStrictPrimeGasWitness_iff_zeta_ne_zero hσ0 (by linarith only [hσ_hi]) hΛ).mpr hzs

/-- **Uncancelled dyadic Prime-Gas `parityPartition` poles across `Ω_open`:**
1. Across `20999 / 96000 < Re s < 1 / 2` (`> 73%` of the width of `Ω_open`) and `Im s ≠ 0`,
   `4 * Re s > 20999 / 24000` forces `riemannZeta (4 * s) ≠ 0` unconditionally, so `s` lacks
   `HasStrictPrimeGasWitness` if and only if the two-step dyadic parity order sum
   `meromorphicOrderAt parityPartition s + meromorphicOrderAt parityPartition (2 * s)` is `< 0`.
2. Across **all** of `Ω_open` (`3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`), `8 * Re s > 1`
   forces `riemannZeta (8 * s) ≠ 0`, so `s` lacks `HasStrictPrimeGasWitness` if and only if
   `∑ j ∈ Finset.range 3, meromorphicOrderAt parityPartition (2 ^ j * s) < 0`. -/
theorem dyadic_parity_uncancelled_poles_on_remaining_strip {Λ : ℝ} (hΛ : 0 < Λ) :
    (∀ (s : ℂ) (hlo : (20999 / 96000 : ℝ) < s.re), s.re < 1 / 2 → s.im ≠ 0 →
      riemannZeta (4 * s) ≠ 0 ∧
        (¬ HasStrictPrimeGasWitness s (by linarith only [hlo]) Λ ↔
          meromorphicOrderAt parityPartition s +
            meromorphicOrderAt parityPartition (2 * s) < 0)) ∧
    (∀ (s : ℂ) (hlo : (3001 / 24000 : ℝ) ≤ s.re), s.re < 1 / 2 → 184 < |s.im| →
      riemannZeta (8 * s) ≠ 0 ∧
        (¬ HasStrictPrimeGasWitness s (by linarith only [hlo]) Λ ↔
          (∑ j ∈ Finset.range 3, meromorphicOrderAt parityPartition ((2 : ℂ) ^ j * s)) < 0)) := by
  constructor
  · intro s hlo hhi him
    have hs0 : 0 < s.re := by linarith only [hlo]
    have hs1 : s.re < 1 := by linarith only [hhi]
    have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs1; exact lt_irrefl 1 hs1
    have h4re : (20999 / 24000 : ℝ) < (4 * s).re := by
      have hre4 : (4 * s).re = 4 * s.re := by
        rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      linarith only [hre4, hlo]
    have h4nz : riemannZeta (4 * s) ≠ 0 :=
      MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re h4re
    have h4_ne1 : 4 * s ≠ 1 := fun h => by
      have him4 := congrArg Complex.im h
      rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul, Complex.one_im] at him4
      exact (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) him) him4
    have hord4 : meromorphicOrderAt riemannZeta (4 * s) = 0 :=
      ZeroForcingCalculus.meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero
        (HTGeometry.analyticAt_riemannZeta h4_ne1) h4nz
    have hdyad := parityPartition_dyadic_orders s 2
    rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, one_mul, pow_one,
      show ((2 : ℂ) ^ 2 * s) = 4 * s by ring, hord4, zero_sub] at hdyad
    refine ⟨h4nz, ?_⟩
    rw [hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 hs1 hΛ, not_not, hdyad]
    constructor
    · intro hzs
      have hpos := ZeroForcingCalculus.meromorphicOrderAt_pos_of_analyticAt_eq_zero
        (HTGeometry.analyticAt_riemannZeta hs_ne1) hzs
      lift meromorphicOrderAt riemannZeta s to ℤ using
        ZeroForcingCalculus.meromorphicOrderAt_riemannZeta_ne_top s with m hm
      have hm_pos : (0 : ℤ) < m := by exact_mod_cast hpos
      exact (WithTop.LinearOrderedAddCommGroup.coe_neg m).symm ▸
        WithTop.coe_lt_coe.mpr (neg_lt_zero.mpr hm_pos)
    · intro hneg
      by_contra hnz
      have ho0 := ZeroForcingCalculus.meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero
        (HTGeometry.analyticAt_riemannZeta hs_ne1) hnz
      rw [ho0, neg_zero] at hneg
      exact lt_irrefl 0 hneg
  · intro s hlo hhi _him
    have hs0 : 0 < s.re := by linarith only [hlo]
    have hs1 : s.re < 1 := by linarith only [hhi]
    have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs1; exact lt_irrefl 1 hs1
    have h8re : 1 < ((2 : ℂ) ^ 3 * s).re := by
      have hre8 : ((2 : ℂ) ^ 3 * s).re = 8 * s.re := by
        rw [show ((2 : ℂ) ^ 3 : ℂ) = ((8 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      linarith only [hre8, hlo]
    have h8_eq : (2 : ℂ) ^ 3 * s = 8 * s := by ring
    have h8nz : riemannZeta (8 * s) ≠ 0 := by
      rw [← h8_eq]; exact riemannZeta_ne_zero_of_one_lt_re h8re
    have hdyad := partition_order_from_parity s ⟨3, h8re⟩
    refine ⟨h8nz, ?_⟩
    rw [hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 hs1 hΛ, not_not, hdyad]
    constructor
    · intro hzs
      have hpos := ZeroForcingCalculus.meromorphicOrderAt_pos_of_analyticAt_eq_zero
        (HTGeometry.analyticAt_riemannZeta hs_ne1) hzs
      lift meromorphicOrderAt riemannZeta s to ℤ using
        ZeroForcingCalculus.meromorphicOrderAt_riemannZeta_ne_top s with m hm
      have hm_pos : (0 : ℤ) < m := by exact_mod_cast hpos
      exact (WithTop.LinearOrderedAddCommGroup.coe_neg m).symm ▸
        WithTop.coe_lt_coe.mpr (neg_lt_zero.mpr hm_pos)
    · intro hneg
      by_contra hnz
      have ho0 := ZeroForcingCalculus.meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero
        (HTGeometry.analyticAt_riemannZeta hs_ne1) hnz
      rw [ho0, neg_zero] at hneg
      exact lt_irrefl 0 hneg

/-! ### 5. Exact Coprime Residue-Progression Parseval Identity and Variance Power Cancellation -/

/-- Trans-sieve weighted sequence `k ↦ -vaughanEulerCoeff (n + 1) D N M k * k^{-w}` supported on
`D + 1 ≤ k`. -/
def vaughanEulerProgressionSeq (n D N M : ℕ) (w : ℂ) (k : ℕ) : ℂ :=
  if D + 1 ≤ k then -(vaughanEulerCoeff (n + 1) D N M k : ℂ) * (k : ℂ) ^ (-w) else 0

/-- Reduced residue-progression Vaughan–Euler defect on `u : (ZMod (n + 1))ˣ` (`q = n + 1 ≥ 2`),
summing `vaughanEulerProgressionSeq` across `1 ≤ k ≤ D * (N + M * n)` with `(k : ZMod (n + 1)) = u`. -/
def residueProgressionDefect (n D N M : ℕ) (w : ℂ) (u : (ZMod (n + 1))ˣ) : ℂ :=
  _root_.RHTower.classSum n (D * (N + M * n)) (vaughanEulerProgressionSeq n D N M w) u

/-- Mean of `residueProgressionDefect` across the `φ(n + 1)` reduced residue classes. -/
def residueProgressionMean (n D N M : ℕ) (w : ℂ) : ℂ :=
  (((n + 1).totient : ℂ))⁻¹ * ∑ u : (ZMod (n + 1))ˣ, residueProgressionDefect n D N M w u

private lemma vaughanEulerDefect_eq_charSum_progressionSeq {n D N M : ℕ}
    (_hn : 1 ≤ n) (hD : 1 ≤ D) (hDN : D ≤ N) (χ : DirichletCharacter ℂ (n + 1)) (w : ℂ) :
    vaughanEulerDefect χ D N M w =
      _root_.RHTower.charSum n (D * (N + M * n)) (vaughanEulerProgressionSeq n D N M w) χ := by
  have hsub_eq : n + 1 - 1 = n := Nat.add_sub_cancel n 1
  have h1 := (vaughanEulerDefect_eq_typeIIShort_sub_tail (q := n + 1) (M := M)
    (Nat.le_add_left 1 n) hD hDN χ w).1
  rw [hsub_eq] at h1
  rw [h1]
  unfold _root_.RHTower.charSum vaughanEulerProgressionSeq
  have hDL : D ≤ D * (N + M * n) :=
    Nat.le_mul_of_pos_right D (by have := le_trans hD hDN; omega)
  have hsplit : Finset.Icc 1 (D * (N + M * n)) =
      Finset.Icc 1 D ∪ Finset.Icc (D + 1) (D * (N + M * n)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdj : Disjoint (Finset.Icc 1 D) (Finset.Icc (D + 1) (D * (N + M * n))) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2; rw [Finset.mem_Icc] at hk1 hk2; omega
  rw [hsplit, Finset.sum_union hdj]
  have hzero : (∑ k ∈ Finset.Icc 1 D,
      (if D + 1 ≤ k then -(vaughanEulerCoeff (n + 1) D N M k : ℂ) * (k : ℂ) ^ (-w) else 0) *
        χ (k : ZMod (n + 1))) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkD := (Finset.mem_Icc.mp hk).2
    rw [if_neg (by omega), zero_mul]
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [if_pos (Finset.mem_Icc.mp hk).1]

/-- **Exact leading-term sieve annihilation in coprime arithmetic progressions:**
for every `u : (ZMod (n + 1))ˣ` whose least residue `(u : ZMod (n + 1)).val` satisfies
`(u : ZMod (n + 1)).val ≤ D` (`D < n + 1`, including `u = 1`), the leading progression term
`k = u.val < n + 1` vanishes identically, so `residueProgressionDefect` is supported strictly
above the modulus (`n + 2 ≤ k`). -/
theorem residueProgressionDefect_annihilates_low_residues {n D N M : ℕ}
    (hn : 1 ≤ n) (hD_lt : D < n + 1) (w : ℂ) (u : (ZMod (n + 1))ˣ)
    (hu_le : (u : ZMod (n + 1)).val ≤ D) :
    residueProgressionDefect n D N M w u =
      ∑ k ∈ (Finset.Icc (n + 2) (D * (N + M * n))).filter
          (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1))),
        -(vaughanEulerCoeff (n + 1) D N M k : ℂ) * (k : ℂ) ^ (-w) := by
  classical
  haveI : Fact (1 < n + 1) := ⟨by omega⟩
  unfold residueProgressionDefect _root_.RHTower.classSum
  have hsub : (Finset.Icc (n + 2) (D * (N + M * n))).filter
        (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1))) ⊆
      (Finset.Icc 1 (D * (N + M * n))).filter
        (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1))) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨by omega, hk.1.2⟩, hk.2⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk_Icc, _⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk_lo, _⟩ := Finset.mem_Icc.mp hk_Icc
    unfold vaughanEulerProgressionSeq
    rw [if_pos (by omega : D + 1 ≤ k)]
  · intro k hk hnot
    obtain ⟨hk_Icc, hk_mod⟩ := Finset.mem_filter.mp hk
    obtain ⟨_, hkL⟩ := Finset.mem_Icc.mp hk_Icc
    have hk_le_q : k ≤ n + 1 := by
      by_contra hgt
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hkL⟩, hk_mod⟩)
    rcases eq_or_lt_of_le hk_le_q with rfl | hk_lt
    · have hzero : (Nat.cast (n + 1) : ZMod (n + 1)) = 0 := ZMod.natCast_self (n + 1)
      rw [hzero] at hk_mod
      exact absurd (hk_mod ▸ u.isUnit) (not_isUnit_zero)
    · have hval : k = (u : ZMod (n + 1)).val := by
        have hv := congrArg ZMod.val hk_mod
        rwa [ZMod.val_natCast_of_lt hk_lt] at hv
      have hk_le_D : k ≤ D := hval ▸ hu_le
      unfold vaughanEulerProgressionSeq
      rw [if_neg (by omega)]

/-- **Exact sum of progression defects equals the principal (`χ = 1`) defect:**
summing `residueProgressionDefect` over `u : (ZMod (n + 1))ˣ` recovers
`vaughanEulerDefect (1 : DirichletCharacter ℂ (n + 1)) D N M w` identically. -/
theorem sum_residueProgressionDefect_eq_principal_vaughanEulerDefect {n D N M : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) (hDN : D ≤ N) (w : ℂ) :
    (∑ u : (ZMod (n + 1))ˣ, residueProgressionDefect n D N M w u) =
      vaughanEulerDefect (1 : DirichletCharacter ℂ (n + 1)) D N M w := by
  rw [vaughanEulerDefect_eq_charSum_progressionSeq hn hD hDN 1 w,
    _root_.RHTower.charSum_eq_sum_classSum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hone : (1 : DirichletCharacter ℂ (n + 1)) (u : ZMod (n + 1)) = 1 :=
    MulChar.one_apply u.isUnit
  rw [hone, mul_one]
  rfl

/-- **Exact finite abelian Parseval identity separating principal (`χ = 1`) from nonprincipal (`χ ≠ 1`):**
`φ(n + 1) ∑_u ‖residueProgressionDefect u‖² = ‖vaughanEulerDefect 1‖² + ∑_{χ ≠ 1} ‖vaughanEulerDefect χ‖²`. -/
theorem totient_mul_sum_normSq_residueProgressionDefect_eq_parseval {n D N M : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) (hDN : D ≤ N) (w : ℂ) :
    ((n + 1).totient : ℝ) *
        (∑ u : (ZMod (n + 1))ˣ, ‖residueProgressionDefect n D N M w u‖ ^ (2 : ℕ)) =
      ‖vaughanEulerDefect (1 : DirichletCharacter ℂ (n + 1)) D N M w‖ ^ (2 : ℕ) +
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (n + 1))).erase 1,
          ‖vaughanEulerDefect χ D N M w‖ ^ (2 : ℕ) := by
  classical
  have hmv := (_root_.RHTower.sum_normSq_charSum n (D * (N + M * n))
    (vaughanEulerProgressionSeq n D N M w)).symm
  rw [show (∑ u : (ZMod (n + 1))ˣ,
      ‖_root_.RHTower.classSum n (D * (N + M * n)) (vaughanEulerProgressionSeq n D N M w) u‖ ^ 2) =
    ∑ u : (ZMod (n + 1))ˣ, ‖residueProgressionDefect n D N M w u‖ ^ (2 : ℕ) from rfl] at hmv
  rw [hmv]
  have hcongr : (∑ χ : DirichletCharacter ℂ (n + 1),
        ‖_root_.RHTower.charSum n (D * (N + M * n)) (vaughanEulerProgressionSeq n D N M w) χ‖ ^ 2) =
      ∑ χ : DirichletCharacter ℂ (n + 1), ‖vaughanEulerDefect χ D N M w‖ ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [← vaughanEulerDefect_eq_charSum_progressionSeq hn hD hDN χ w]
  rw [hcongr, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ (n + 1)))]

private lemma card_mul_sum_norm_sub_mean_sq {ι : Type*} [Fintype ι]
    (hcard : 0 < Fintype.card ι) (f : ι → ℂ) :
    (Fintype.card ι : ℝ) *
        (∑ i : ι, ‖f i - ((Fintype.card ι : ℂ)⁻¹ * ∑ j : ι, f j)‖ ^ (2 : ℕ)) =
      (Fintype.card ι : ℝ) * (∑ i : ι, ‖f i‖ ^ (2 : ℕ)) - ‖∑ i : ι, f i‖ ^ (2 : ℕ) := by
  set m : ℝ := (Fintype.card ι : ℝ)
  have hm_pos : 0 < m := Nat.cast_pos.mpr hcard
  have hm_ne : m ≠ 0 := hm_pos.ne'
  set S : ℂ := ∑ j : ι, f j
  set μ : ℂ := (Fintype.card ι : ℂ)⁻¹ * S
  have hμ_re : μ.re = m⁻¹ * S.re := by
    dsimp [μ, m]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  have hμ_im : μ.im = m⁻¹ * S.im := by
    dsimp [μ, m]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
  have hnorm_sq : ∀ z : ℂ, ‖z‖ ^ (2 : ℕ) = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hterm : ∀ i : ι, ‖f i - μ‖ ^ (2 : ℕ) =
      ‖f i‖ ^ (2 : ℕ) - (2 * μ.re * (f i).re + 2 * μ.im * (f i).im) + ‖μ‖ ^ (2 : ℕ) := by
    intro i
    rw [hnorm_sq (f i - μ), hnorm_sq (f i), hnorm_sq μ, Complex.sub_re, Complex.sub_im]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hS_re : (∑ i : ι, (f i).re) = S.re := (Complex.re_sum _ _).symm
  have hS_im : (∑ i : ι, (f i).im) = S.im := (Complex.im_sum _ _).symm
  rw [hS_re, hS_im, hnorm_sq μ, hnorm_sq S, hμ_re, hμ_im]
  change m * ((∑ i : ι, ‖f i‖ ^ (2 : ℕ)) -
      (2 * (m⁻¹ * S.re) * S.re + 2 * (m⁻¹ * S.im) * S.im) +
      m * ((m⁻¹ * S.re) ^ (2 : ℕ) + (m⁻¹ * S.im) ^ (2 : ℕ))) =
    m * (∑ i : ι, ‖f i‖ ^ (2 : ℕ)) - (S.re ^ (2 : ℕ) + S.im ^ (2 : ℕ))
  field_simp [hm_ne]
  ring

/-- **Exact centered progression variance identity:** subtracting `residueProgressionMean` cancels
the principal `χ = 1` channel identically, equating `φ(n + 1)` times the progression variance to
the exact nonprincipal character energy `∑_{χ ≠ 1} ‖vaughanEulerDefect χ D N M w‖²`. -/
theorem totient_mul_sum_normSq_centered_residueProgressionDefect_eq {n D N M : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) (hDN : D ≤ N) (w : ℂ) :
    ((n + 1).totient : ℝ) *
        (∑ u : (ZMod (n + 1))ˣ,
          ‖residueProgressionDefect n D N M w u - residueProgressionMean n D N M w‖ ^ (2 : ℕ)) =
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (n + 1))).erase 1,
        ‖vaughanEulerDefect χ D N M w‖ ^ (2 : ℕ) := by
  classical
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hcard_eq : Fintype.card (ZMod (n + 1))ˣ = (n + 1).totient := ZMod.card_units_eq_totient (n + 1)
  have htot_pos : 0 < (n + 1).totient := Nat.totient_pos.mpr (by omega)
  have hvar := card_mul_sum_norm_sub_mean_sq (ι := (ZMod (n + 1))ˣ)
    (by rw [hcard_eq]; exact htot_pos) (residueProgressionDefect n D N M w)
  have hmean_eq : ((Fintype.card (ZMod (n + 1))ˣ : ℂ)⁻¹ *
      ∑ j : (ZMod (n + 1))ˣ, residueProgressionDefect n D N M w j) =
      residueProgressionMean n D N M w := by
    unfold residueProgressionMean
    rw [hcard_eq]
  simp_rw [hmean_eq] at hvar
  rw [hcard_eq, sum_residueProgressionDefect_eq_principal_vaughanEulerDefect hn hD hDN w,
    totient_mul_sum_normSq_residueProgressionDefect_eq_parseval hn hD hDN w] at hvar
  linarith only [hvar]

/-- Explicit `s`-dependent constant governing the centered residue-progression variance decay across
all `0 < Re s < 1 / 2` and `Im s ∈ ℝ`. -/
def residueProgressionVarianceConstant (s : ℂ) : ℝ :=
  let δ := 1 - 2 * s.re
  let η := δ ^ (2 : ℕ) / 16
  let M₀ := (⌈|s.im|⌉₊ : ℝ) + 21 + 2 * (⌈4 / s.re⌉₊ : ℝ)
  (4 / (1 - (2 : ℝ) ^ (-δ))) *
    (1 + Real.log (3 * M₀) + 3 / η) ^ (3 : ℕ) *
    (2 * (2 : ℝ) ^ δ + 4 * (M₀ + 20 / η))

theorem residueProgressionVarianceConstant_pos {s : ℂ} (hhi : s.re < 1 / 2) :
    0 < residueProgressionVarianceConstant s := by
  unfold residueProgressionVarianceConstant
  dsimp only
  have hδ : 0 < 1 - 2 * s.re := by linarith only [hhi]
  have hη : 0 < (1 - 2 * s.re) ^ (2 : ℕ) / 16 := by positivity
  have hdenom : 0 < 1 - (2 : ℝ) ^ (-(1 - 2 * s.re)) := by
    linarith [Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith only [hδ] : -(1 - 2 * s.re) < 0)]
  have hM₀ : 1 ≤ (⌈|s.im|⌉₊ : ℝ) + 21 + 2 * (⌈4 / s.re⌉₊ : ℝ) := by
    linarith [Nat.cast_nonneg (α := ℝ) ⌈|s.im|⌉₊, Nat.cast_nonneg (α := ℝ) ⌈4 / s.re⌉₊]
  have hlog : 0 ≤ Real.log (3 * ((⌈|s.im|⌉₊ : ℝ) + 21 + 2 * (⌈4 / s.re⌉₊ : ℝ))) :=
    Real.log_nonneg (by linarith only [hM₀])
  have h3η : 0 < 3 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16) := div_pos (by norm_num) hη
  have hblog : 0 < 1 + Real.log (3 * ((⌈|s.im|⌉₊ : ℝ) + 21 + 2 * (⌈4 / s.re⌉₊ : ℝ))) +
      3 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16) := by
    linarith only [hlog, h3η]
  have h20η : 0 < 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16) := div_pos (by norm_num) hη
  have h2δ : 0 < (2 : ℝ) ^ (1 - 2 * s.re) := Real.rpow_pos_of_pos zero_lt_two _
  have htail : 0 < 2 * (2 : ℝ) ^ (1 - 2 * s.re) +
      4 * (((⌈|s.im|⌉₊ : ℝ) + 21 + 2 * (⌈4 / s.re⌉₊ : ℝ)) + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) := by
    linarith only [h2δ, hM₀, h20η]
  exact mul_pos (mul_pos (div_pos (by norm_num) hdenom) (pow_pos hblog 3)) htail

/-- **Unconditional all-height residue-progression variance power cancellation across all `0 < Re s < 1 / 2`:**
at every `s` with `0 < Re s < 1 / 2` and every height `Im s ∈ ℝ`, for every modulus `q = n + 1 ≥ 2`,
setting `D = ⌊q^{(1 - 2 Re s) / 2}⌋₊` and `M = vaughanDispersionOrder q s`, `N = 2 q M + q - 1`,
the centered progression variance across `u : (ZMod q)ˣ` decays by the explicit power law
`≤ residueProgressionVarianceConstant s * q^{-(1 - 2 Re s)^2 / 4}`. -/
theorem sum_normSq_centered_residueProgressionDefect_le_rpow
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    let q := n + 1
    let D := ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊
    let M := vaughanDispersionOrder q s
    let N := 2 * q * M + q - 1
    (∑ u : (ZMod (n + 1))ˣ,
        ‖residueProgressionDefect n D N M (1 - conj s) u -
          residueProgressionMean n D N M (1 - conj s)‖ ^ (2 : ℕ)) ≤
      residueProgressionVarianceConstant s * ((n + 1 : ℕ) : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 4)) := by
  classical
  dsimp only
  set q := n + 1
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hδ_pos : 0 < 1 - 2 * s.re := by linarith only [hhi]
  have hK_pos : 0 < 1 - (2 : ℝ) ^ (-(1 - 2 * s.re)) := by
    have hr := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith only [hδ_pos] : -(1 - 2 * s.re) < 0)
    linarith only [hr]
  have hq_δ2_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) :=
    Real.one_le_rpow hq_ge1 (by linarith only [hδ_pos])
  have hq_δ2_le_q : (q : ℝ) ^ ((1 - 2 * s.re) / 2) ≤ (q : ℝ) := by
    calc (q : ℝ) ^ ((1 - 2 * s.re) / 2) ≤ (q : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hq_ge1 (by linarith only [hs0])
      _ = (q : ℝ) := Real.rpow_one _
  set D := ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊
  set M := vaughanDispersionOrder q s
  set N := 2 * q * M + q - 1
  have hD1 : 1 ≤ D := Nat.le_floor (by simpa using hq_δ2_ge1)
  have hDq : D ≤ q := Nat.floor_le_of_le hq_δ2_le_q
  have hNq : q ≤ N := by
    have hM1 : 1 ≤ M := by dsimp [M, vaughanDispersionOrder]; omega
    have hqM : 2 ≤ 2 * q * M := by nlinarith only [hq, hM1]
    dsimp [N]; omega
  have hvar_eq := totient_mul_sum_normSq_centered_residueProgressionDefect_eq (M := M) hn hD1
    (hDq.trans hNq) (1 - conj s)
  have herase_le : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (n + 1))).erase 1,
        ‖vaughanEulerDefect χ D N M (1 - conj s)‖ ^ (2 : ℕ)) ≤
      ∑ χ : DirichletCharacter ℂ (n + 1),
        ‖vaughanEulerDefect χ D N M (1 - conj s)‖ ^ (2 : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => sq_nonneg _
  have hw_re : (1 - conj s).re = 1 - s.re := by simp
  have h2w_sub1 : 2 * (1 - conj s).re - 1 = 1 - 2 * s.re := by rw [hw_re]; ring
  have hsecond := sum_normSq_vaughanEulerDefect_le (q := q) (D := D) (N := N) (M := M)
    hq hD1 hDq hNq (w := 1 - conj s) (by rw [hw_re]; linarith only [hhi])
  rw [h2w_sub1] at hsecond
  have hM₀_ge1 : (1 : ℝ) ≤ ((⌈|s.im|⌉₊ : ℝ) + 21 + 2 * (⌈4 / s.re⌉₊ : ℝ)) := by
    have h1 := Nat.cast_nonneg (α := ℝ) ⌈|s.im|⌉₊
    have h2 := Nat.cast_nonneg (α := ℝ) ⌈4 / s.re⌉₊
    linarith only [h1, h2]
  set M₀ : ℝ := (⌈|s.im|⌉₊ : ℝ) + 21 + 2 * (⌈4 / s.re⌉₊ : ℝ)
  set η : ℝ := (1 - 2 * s.re) ^ (2 : ℕ) / 16
  have hη_pos : 0 < η := by dsimp [η]; positivity
  have hlog_q_eta : Real.log (q : ℝ) ≤ (q : ℝ) ^ η / η := by
    have hexp := Real.add_one_le_exp (Real.log (q : ℝ) * η)
    rw [← Real.rpow_def_of_pos hq_pos] at hexp
    rw [le_div_iff₀ hη_pos]
    linarith only [hexp]
  have hq_eta_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ η := Real.one_le_rpow hq_ge1 hη_pos.le
  have hM_add1_rpow : (M : ℝ) + 1 ≤ (M₀ + 20 / η) * (q : ℝ) ^ η := by
    have hln2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hexp2 := Real.add_one_le_exp (-Real.log 2)
      rw [Real.exp_neg, Real.exp_log zero_lt_two, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at hexp2
      linarith only [hexp2]
    have hlog2_q : (Nat.log 2 q : ℝ) ≤ 2 * Real.log (q : ℝ) := by
      have hpow_le : (2 : ℝ) ^ (Nat.log 2 q) ≤ (q : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : q ≠ 0)
      have hlog_le := Real.log_le_log (by positivity) hpow_le
      rw [Real.log_pow] at hlog_le
      have hnn := Nat.cast_nonneg (α := ℝ) (Nat.log 2 q)
      nlinarith only [hlog_le, hln2, hnn]
    have hM_eq : (M : ℝ) + 1 = M₀ + 10 * (Nat.log 2 q : ℝ) := by
      dsimp [M, M₀, vaughanDispersionOrder]; push_cast; ring
    rw [hM_eq]
    calc M₀ + 10 * (Nat.log 2 q : ℝ)
        ≤ M₀ + 20 * Real.log (q : ℝ) := by linarith only [hlog2_q]
      _ ≤ M₀ * (q : ℝ) ^ η + 20 * ((q : ℝ) ^ η / η) :=
          add_le_add (le_mul_of_one_le_right (by linarith only [hM₀_ge1]) hq_eta_ge1)
            (mul_le_mul_of_nonneg_left hlog_q_eta (by norm_num))
      _ = (M₀ + 20 / η) * (q : ℝ) ^ η := by ring
  have hlin_hor : (N + M * (q - 1) : ℕ) ≤ 3 * q * (M + 1) := by
    calc (2 * q * M + q - 1) + M * (q - 1)
        ≤ (2 * q * M + q) + M * q :=
          Nat.add_le_add (Nat.sub_le _ _) (Nat.mul_le_mul_left M (Nat.sub_le q 1))
      _ ≤ (2 * q * M + q) + M * q + 2 * q := Nat.le_add_right _ _
      _ = 3 * q * (M + 1) := by ring
  have hinv_cube : (_root_.RHTower.Sieve.invSum (D * (N + M * (q - 1)))) ^ (3 : ℕ) ≤
      (1 + Real.log (3 * M₀) + 3 / η) ^ (3 : ℕ) * (q : ℝ) ^ (3 * η) := by
    have hL_ge1 : 1 ≤ D * (N + M * (q - 1)) := Nat.mul_pos hD1 (by omega)
    have hM_mul_q : (M : ℝ) + 1 ≤ M₀ * (q : ℝ) := by
      have hnat_le : (Nat.log 2 q : ℝ) + 1 ≤ (q : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.log_lt_self 2 (by omega : q ≠ 0))
      have hM_eq2 : (M : ℝ) + 1 = (M₀ - 10) + 10 * ((Nat.log 2 q : ℝ) + 1) := by
        dsimp [M, M₀, vaughanDispersionOrder]; push_cast; ring
      have hpos_c : 0 ≤ M₀ - 10 := by
        dsimp [M₀]
        linarith [Nat.cast_nonneg (α := ℝ) ⌈|s.im|⌉₊, Nat.cast_nonneg (α := ℝ) ⌈4 / s.re⌉₊]
      rw [hM_eq2]
      nlinarith only [hq_ge1, hnat_le, hpos_c]
    have hL_le : ((D * (N + M * (q - 1)) : ℕ) : ℝ) ≤ 3 * M₀ * (q : ℝ) ^ (3 : ℕ) := by
      have hhor_r : ((N + M * (q - 1) : ℕ) : ℝ) ≤ 3 * (q : ℝ) * ((M : ℝ) + 1) :=
        (show ((N + M * (q - 1) : ℕ) : ℝ) ≤ ((3 * q * (M + 1) : ℕ) : ℝ) by
          exact_mod_cast hlin_hor).trans_eq (by push_cast; ring)
      calc ((D * (N + M * (q - 1)) : ℕ) : ℝ)
          = (D : ℝ) * ((N + M * (q - 1) : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ (q : ℝ) * (3 * (q : ℝ) * ((M : ℝ) + 1)) :=
            mul_le_mul (by exact_mod_cast hDq) hhor_r (Nat.cast_nonneg _) hq_pos.le
        _ ≤ (q : ℝ) * (3 * (q : ℝ) * (M₀ * (q : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM_mul_q (by positivity)) hq_pos.le
        _ = 3 * M₀ * (q : ℝ) ^ (3 : ℕ) := by ring
    have h1 := _root_.RHTower.Sieve.invSum_le_one_add_log hL_ge1
    have hlog_L : Real.log ((D * (N + M * (q - 1)) : ℕ) : ℝ) ≤
        Real.log (3 * M₀) + 3 * Real.log (q : ℝ) := by
      calc Real.log ((D * (N + M * (q - 1)) : ℕ) : ℝ)
          ≤ Real.log (3 * M₀ * (q : ℝ) ^ (3 : ℕ)) :=
            Real.log_le_log (by exact_mod_cast hL_ge1) hL_le
        _ = Real.log (3 * M₀) + Real.log ((q : ℝ) ^ (3 : ℕ)) :=
            Real.log_mul (by linarith only [hM₀_ge1]) (by positivity)
        _ = Real.log (3 * M₀) + 3 * Real.log (q : ℝ) := by rw [Real.log_pow]; ring
    have hconst_nn : 0 ≤ 1 + Real.log (3 * M₀) := by
      linarith [Real.log_nonneg (show 1 ≤ 3 * M₀ by linarith only [hM₀_ge1])]
    have hinv_le : _root_.RHTower.Sieve.invSum (D * (N + M * (q - 1))) ≤
        (1 + Real.log (3 * M₀) + 3 / η) * (q : ℝ) ^ η := by
      calc _root_.RHTower.Sieve.invSum (D * (N + M * (q - 1)))
          ≤ (1 + Real.log (3 * M₀)) + 3 * Real.log (q : ℝ) := by linarith only [h1, hlog_L]
        _ ≤ (1 + Real.log (3 * M₀)) * (q : ℝ) ^ η + 3 * ((q : ℝ) ^ η / η) :=
            add_le_add (le_mul_of_one_le_right hconst_nn hq_eta_ge1)
              (mul_le_mul_of_nonneg_left hlog_q_eta (by norm_num))
        _ = (1 + Real.log (3 * M₀) + 3 / η) * (q : ℝ) ^ η := by ring
    calc (_root_.RHTower.Sieve.invSum (D * (N + M * (q - 1)))) ^ (3 : ℕ)
        ≤ ((1 + Real.log (3 * M₀) + 3 / η) * (q : ℝ) ^ η) ^ (3 : ℕ) :=
          pow_le_pow_left₀ (_root_.RHTower.Sieve.invSum_nonneg _) hinv_le 3
      _ = (1 + Real.log (3 * M₀) + 3 / η) ^ (3 : ℕ) * (q : ℝ) ^ (3 * η) := by
          rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ η) 3, ← Real.rpow_mul hq_pos.le]
          congr 2; push_cast; ring
  have hocc_le : 2 * (D : ℝ) ^ (-(1 - 2 * s.re)) +
        (((D * (N + M * (q - 1)) : ℕ) : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(1 - 2 * s.re)) ≤
      (2 * (2 : ℝ) ^ (1 - 2 * s.re) + 4 * (M₀ + 20 / η)) *
        (q : ℝ) ^ (η - (1 - 2 * s.re) ^ (2 : ℕ) / 2) := by
    have hD_le_rpow : (D : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) := Nat.floor_le (by positivity)
    have hD_ge_half : (q : ℝ) ^ ((1 - 2 * s.re) / 2) / 2 ≤ (D : ℝ) := by
      have hlt := Nat.lt_floor_add_one ((q : ℝ) ^ ((1 - 2 * s.re) / 2))
      have h1D : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
      linarith only [hlt, h1D]
    have hD_neg : (D : ℝ) ^ (-(1 - 2 * s.re)) ≤
        (2 : ℝ) ^ (1 - 2 * s.re) * (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 2)) := by
      calc (D : ℝ) ^ (-(1 - 2 * s.re))
          ≤ ((q : ℝ) ^ ((1 - 2 * s.re) / 2) / 2) ^ (-(1 - 2 * s.re)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hD_ge_half (by linarith only [hδ_pos])
        _ = ((q : ℝ) ^ ((1 - 2 * s.re) / 2) * (2 : ℝ)⁻¹) ^ (-(1 - 2 * s.re)) := by rw [div_eq_mul_inv]
        _ = ((q : ℝ) ^ ((1 - 2 * s.re) / 2)) ^ (-(1 - 2 * s.re)) *
              ((2 : ℝ)⁻¹) ^ (-(1 - 2 * s.re)) := Real.mul_rpow (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (1 - 2 * s.re) * (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 2)) := by
            rw [← Real.rpow_mul hq_pos.le, Real.inv_rpow zero_le_two,
              Real.rpow_neg zero_le_two, inv_inv]
            have hexp : (1 - 2 * s.re) / 2 * -(1 - 2 * s.re) =
                -((1 - 2 * s.re) ^ (2 : ℕ) / 2) := by ring
            rw [hexp]; ring
    have hdiv_le : ((D * (N + M * (q - 1)) : ℕ) : ℝ) / (q : ℝ) ≤
        3 * (q : ℝ) ^ ((1 - 2 * s.re) / 2) * ((M : ℝ) + 1) := by
      rw [div_le_iff₀ hq_pos]
      have hhor_r : ((N + M * (q - 1) : ℕ) : ℝ) ≤ 3 * (q : ℝ) * ((M : ℝ) + 1) :=
        (show ((N + M * (q - 1) : ℕ) : ℝ) ≤ ((3 * q * (M + 1) : ℕ) : ℝ) by
          exact_mod_cast hlin_hor).trans_eq (by push_cast; ring)
      calc ((D * (N + M * (q - 1)) : ℕ) : ℝ)
          = (D : ℝ) * ((N + M * (q - 1) : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) * (3 * (q : ℝ) * ((M : ℝ) + 1)) :=
            mul_le_mul hD_le_rpow hhor_r (Nat.cast_nonneg _) (by positivity)
        _ = 3 * (q : ℝ) ^ ((1 - 2 * s.re) / 2) * ((M : ℝ) + 1) * (q : ℝ) := by ring
    have h1_le : (1 : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) * ((M : ℝ) + 1) := by
      have hM_nn := Nat.cast_nonneg (α := ℝ) M
      nlinarith only [hq_δ2_ge1, hM_nn]
    have hLq : ((D * (N + M * (q - 1)) : ℕ) : ℝ) / (q : ℝ) + 1 ≤
        4 * (q : ℝ) ^ ((1 - 2 * s.re) / 2) * ((M : ℝ) + 1) := by
      linarith only [hdiv_le, h1_le]
    have hocc2 : (((D * (N + M * (q - 1)) : ℕ) : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(1 - 2 * s.re)) ≤
        4 * (M₀ + 20 / η) * (q : ℝ) ^ (η - (1 - 2 * s.re) / 2) := by
      calc (((D * (N + M * (q - 1)) : ℕ) : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(1 - 2 * s.re))
          ≤ (4 * (q : ℝ) ^ ((1 - 2 * s.re) / 2) * ((M : ℝ) + 1)) *
              (q : ℝ) ^ (-(1 - 2 * s.re)) :=
            mul_le_mul_of_nonneg_right hLq (Real.rpow_nonneg hq_pos.le _)
        _ ≤ (4 * (q : ℝ) ^ ((1 - 2 * s.re) / 2) * ((M₀ + 20 / η) * (q : ℝ) ^ η)) *
              (q : ℝ) ^ (-(1 - 2 * s.re)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hM_add1_rpow (by positivity))
              (Real.rpow_nonneg hq_pos.le _)
        _ = 4 * (M₀ + 20 / η) *
              ((q : ℝ) ^ ((1 - 2 * s.re) / 2) * (q : ℝ) ^ η * (q : ℝ) ^ (-(1 - 2 * s.re))) := by ring
        _ = 4 * (M₀ + 20 / η) * (q : ℝ) ^ (η - (1 - 2 * s.re) / 2) := by
            rw [← Real.rpow_add hq_pos, ← Real.rpow_add hq_pos]
            congr 2; ring
    have hD_eta_le : (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 2)) ≤
        (q : ℝ) ^ (η - (1 - 2 * s.re) ^ (2 : ℕ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hq_ge1 (by linarith only [hη_pos])
    have hsq_le : (1 - 2 * s.re) ^ (2 : ℕ) ≤ 1 - 2 * s.re := by
      have hlt1 : 1 - 2 * s.re < 1 := by linarith only [hs0]
      nlinarith only [hδ_pos, hlt1]
    have hq_exp_cmp : (q : ℝ) ^ (η - (1 - 2 * s.re) / 2) ≤
        (q : ℝ) ^ (η - (1 - 2 * s.re) ^ (2 : ℕ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hq_ge1 (by linarith only [hsq_le])
    have ht1 : 2 * (D : ℝ) ^ (-(1 - 2 * s.re)) ≤
        2 * (2 : ℝ) ^ (1 - 2 * s.re) * (q : ℝ) ^ (η - (1 - 2 * s.re) ^ (2 : ℕ) / 2) := by
      calc 2 * (D : ℝ) ^ (-(1 - 2 * s.re))
          ≤ 2 * ((2 : ℝ) ^ (1 - 2 * s.re) * (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 2))) :=
            mul_le_mul_of_nonneg_left hD_neg zero_le_two
        _ ≤ 2 * (2 : ℝ) ^ (1 - 2 * s.re) * (q : ℝ) ^ (η - (1 - 2 * s.re) ^ (2 : ℕ) / 2) := by
            have := mul_le_mul_of_nonneg_left hD_eta_le
              (show 0 ≤ 2 * (2 : ℝ) ^ (1 - 2 * s.re) by positivity)
            linarith only [this]
    have hcoef2_nn : 0 ≤ 4 * (M₀ + 20 / η) := by
      have hd_pos : 0 < 20 / η := div_pos (by norm_num) hη_pos
      linarith only [hM₀_ge1, hd_pos]
    have ht2 := hocc2.trans (mul_le_mul_of_nonneg_left hq_exp_cmp hcoef2_nn)
    exact (add_le_add ht1 ht2).trans_eq (by ring)
  have hS₁_nn : 0 ≤ 2 * (D : ℝ) ^ (-(1 - 2 * s.re)) +
      (((D * (N + M * (q - 1)) : ℕ) : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(1 - 2 * s.re)) :=
    add_nonneg (mul_nonneg zero_le_two (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg (add_nonneg (div_nonneg (Nat.cast_nonneg _) hq_pos.le) zero_le_one)
        (Real.rpow_nonneg hq_pos.le _))
  have htot_pos : (0 : ℝ) < ((n + 1).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hprod_bound : ((n + 1).totient : ℝ) *
        (∑ u : (ZMod (n + 1))ˣ,
          ‖residueProgressionDefect n D N M (1 - conj s) u -
            residueProgressionMean n D N M (1 - conj s)‖ ^ (2 : ℕ)) ≤
      ((n + 1).totient : ℝ) *
        (residueProgressionVarianceConstant s * (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 4))) := by
    calc ((n + 1).totient : ℝ) *
            (∑ u : (ZMod (n + 1))ˣ,
              ‖residueProgressionDefect n D N M (1 - conj s) u -
                residueProgressionMean n D N M (1 - conj s)‖ ^ (2 : ℕ))
        ≤ ∑ χ : DirichletCharacter ℂ (n + 1),
            ‖vaughanEulerDefect χ D N M (1 - conj s)‖ ^ (2 : ℕ) := by
          linarith only [hvar_eq, herase_le]
      _ ≤ (q.totient : ℝ) * (4 / (1 - (2 : ℝ) ^ (-(1 - 2 * s.re)))) *
            (_root_.RHTower.Sieve.invSum (D * (N + M * (q - 1)))) ^ (3 : ℕ) *
            (2 * (D : ℝ) ^ (-(1 - 2 * s.re)) +
              (((D * (N + M * (q - 1)) : ℕ) : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(1 - 2 * s.re))) :=
          hsecond
      _ ≤ (q.totient : ℝ) * (4 / (1 - (2 : ℝ) ^ (-(1 - 2 * s.re)))) *
            ((1 + Real.log (3 * M₀) + 3 / η) ^ (3 : ℕ) * (q : ℝ) ^ (3 * η)) *
            ((2 * (2 : ℝ) ^ (1 - 2 * s.re) + 4 * (M₀ + 20 / η)) *
              (q : ℝ) ^ (η - (1 - 2 * s.re) ^ (2 : ℕ) / 2)) := by
          have hAK_nn : 0 ≤ (q.totient : ℝ) * (4 / (1 - (2 : ℝ) ^ (-(1 - 2 * s.re)))) :=
            mul_nonneg htot_pos.le (div_nonneg (by norm_num) hK_pos.le)
          have hI₂_nn : 0 ≤ (1 + Real.log (3 * M₀) + 3 / η) ^ (3 : ℕ) * (q : ℝ) ^ (3 * η) :=
            (pow_nonneg (_root_.RHTower.Sieve.invSum_nonneg _) 3).trans hinv_cube
          exact mul_le_mul (mul_le_mul_of_nonneg_left hinv_cube hAK_nn) hocc_le hS₁_nn
            (mul_nonneg hAK_nn hI₂_nn)
      _ = ((n + 1).totient : ℝ) *
            (residueProgressionVarianceConstant s *
              ((q : ℝ) ^ (3 * η) * (q : ℝ) ^ (η - (1 - 2 * s.re) ^ (2 : ℕ) / 2))) := by
          unfold residueProgressionVarianceConstant
          dsimp only [q, M₀, η]
          ring
      _ = ((n + 1).totient : ℝ) *
            (residueProgressionVarianceConstant s *
              (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 4))) := by
          rw [← Real.rpow_add hq_pos]
          congr 3
          dsimp [η]; ring
  exact le_of_mul_le_mul_left hprod_bound htot_pos

#print axioms hasStrictPrimeGasWitness_iff_zeta_ne_zero
#print axioms iSup_capped_witness_excess_eq_norm_continued
#print axioms iSup_uncapped_witness_excess_eq_norm_continued
#print axioms all_possible_spectra_nonpositive_excess_iff_zeta_eq_zero
#print axioms norm_zetaChi_reflected_le_rpow_above_oneHundredEightyFour
#print axioms norm_zetaChi_ge_rpow_above_oneHundredEightyFour
#print axioms strict_spira_zeta_amplification_above_oneHundredEightyFour
#print axioms left_strict_witness_of_reflected_euler_excess_above_oneHundredEightyFour
#print axioms left_strict_witness_of_dirichlet_domination_above_oneHundredEightyFour
#print axioms single_quartet_positive_multiplicative_firewall_above_oneHundredEightyFour
#print axioms two_point_repulsion_strict_witness_on_remaining_strip
#print axioms pigeonhole_strict_witness_on_remaining_strip
#print axioms infinite_strict_witnesses_on_every_horizontal_subinterval_above_oneHundredEightyFour
#print axioms dyadic_parity_uncancelled_poles_on_remaining_strip
#print axioms residueProgressionDefect_annihilates_low_residues
#print axioms sum_residueProgressionDefect_eq_principal_vaughanEulerDefect
#print axioms totient_mul_sum_normSq_residueProgressionDefect_eq_parseval
#print axioms totient_mul_sum_normSq_centered_residueProgressionDefect_eq
#print axioms sum_normSq_centered_residueProgressionDefect_le_rpow

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
