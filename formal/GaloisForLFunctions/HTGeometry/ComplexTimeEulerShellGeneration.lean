import GaloisForLFunctions.HTGeometry.ComplexTimeGenerativeMechanics
import GaloisForLFunctions.HTGeometry.CofinalGenerativeAdmission
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.MarkedEulerShellWall

/-!
# Complex-time marked Euler-shell generation

Exact countable realization of complex-time exponential generation by the marked Euler shell.
The module identifies its analytic source-ratio germ, full centered-moment derivative tower,
nonlinear Gibbs transport, zero straight admission radius, positive-observer Fisher law, and sharp
normalization wall.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex _root_.RHTower Filter MeasureTheory
open scoped LSeries.notation Topology

/-- Mean logarithmic clock used to center the shell score. -/
def shellScoreMean (m : ℕ) (σ : ℝ) : ℝ := shellLogMoment m 1 σ

/-- Centered shell score `-log n + E[log n]`. -/
def shellCenteredScore (m : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  -Real.log n + shellScoreMean m σ

/-- Complex-time partition germ of the centered shell score. -/
def shellComplexPartition (m : ℕ) (σ : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (shellProbability m σ n : ℂ) *
    Complex.exp (z * (shellCenteredScore m σ n : ℂ))

/-- Exact source-ratio law for the shell complex-time partition. -/
theorem shellComplexPartition_eq_sourceRatio {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) {z : ℂ} (hz : 1 < ((σ : ℂ) + z).re) :
    shellComplexPartition m σ z =
      Complex.exp (z * (shellScoreMean m σ : ℂ)) *
        shellSource m ((σ : ℂ) + z) / shellSource m (σ : ℂ) := by
  have hLS : LSeries ↗(shellIndicator m) ((σ : ℂ) + z) =
      shellSource m ((σ : ℂ) + z) := LSeries_shellIndicator hm hz
  have hZ : ((shellMellin m σ : ℝ) : ℂ) = shellSource m (σ : ℂ) :=
    ofReal_shellMellin hm hσ
  have hZ0 : ((shellMellin m σ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (shellMellin_pos hm hσ).ne'
  rw [shellComplexPartition, ← hLS, LSeries]
  rw [← tsum_mul_left]
  rw [← tsum_div_const]
  rw [← hZ]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [shellProbability, shellMass, LSeries.term]
  · have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn.ne', shellProbability, shellMass,
      shellCenteredScore, shellScoreMean]
    have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log hnR.le]
    have hrp : ((((n : ℝ)) ^ σ : ℝ) : ℂ) = (n : ℂ) ^ ((σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) σ, Complex.ofReal_natCast]
    rw [Complex.cpow_add _ _ hnC, ← hrp, Complex.cpow_def_of_ne_zero hnC, hlog]
    push_cast
    field_simp
    have hexp : Complex.exp (z * (-Complex.log n + (shellLogMoment m 1 σ : ℂ))) *
        Complex.exp (z * Complex.log n) =
        Complex.exp (z * (shellLogMoment m 1 σ : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      _ = (shellIndicator m n : ℂ) *
          (Complex.exp (z * (-Complex.log n + (shellLogMoment m 1 σ : ℂ))) *
            Complex.exp (z * Complex.log n)) / (↑((n : ℝ) ^ σ) : ℂ) := by ring
      _ = _ := by rw [hexp]

/-- The shell score is centered under its Gibbs probability. -/
theorem shellCenteredScore_hasSum_zero {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun n : ℕ => shellProbability m σ n * shellCenteredScore m σ n) 0 := by
  have hlog : HasSum (fun n : ℕ => shellProbability m σ n * Real.log n)
      (shellLogMoment m 1 σ) := by
    have hs := (_root_.HTGeometry.ConstraintMotiveRelativity.summable_shellProbability_mul_log_pow
      m 1 hσ).hasSum
    have hs' : HasSum (fun n : ℕ => shellProbability m σ n * Real.log n)
        (_root_.HTGeometry.ConstraintMotiveRelativity.shellGNS m σ 1) := by
      simpa [_root_.HTGeometry.ConstraintMotiveRelativity.shellGNS, pow_one] using hs
    rw [_root_.HTGeometry.ConstraintMotiveRelativity.shellGNS_eq_shellLogMoment] at hs'
    exact hs'
  have hmean := (hasSum_shellProbability hm hσ).mul_right (shellLogMoment m 1 σ)
  have hzero := hlog.neg.add hmean
  have hfun : (fun n : ℕ => shellProbability m σ n * shellCenteredScore m σ n) =
      (fun n : ℕ => -(shellProbability m σ n * Real.log n) +
        shellProbability m σ n * shellLogMoment m 1 σ) := by
    funext n
    rw [shellCenteredScore, shellScoreMean]
    ring
  rw [hfun]
  simpa using hzero

/-- The raw logarithmic moment series sums to the shell logarithmic moment. -/
theorem shellLogMoment_hasSum {m : ℕ} {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    HasSum (fun n : ℕ => shellProbability m σ n * (Real.log n) ^ k)
      (shellLogMoment m k σ) := by
  have hs := (_root_.HTGeometry.ConstraintMotiveRelativity.summable_shellProbability_mul_log_pow
    m k hσ).hasSum
  have hs' : HasSum (fun n : ℕ => shellProbability m σ n * (Real.log n) ^ k)
      (_root_.HTGeometry.ConstraintMotiveRelativity.shellGNS m σ k) := by
    simpa [_root_.HTGeometry.ConstraintMotiveRelativity.shellGNS] using hs
  rw [_root_.HTGeometry.ConstraintMotiveRelativity.shellGNS_eq_shellLogMoment] at hs'
  exact hs'

/-- Centered logarithmic moment of the shell score. -/
def shellCenteredMoment (m k : ℕ) (σ : ℝ) : ℝ :=
  ∑' n : ℕ, shellProbability m σ n * (shellCenteredScore m σ n) ^ k

/-- Exact binomial expression for every centered shell moment. -/
theorem shellCenteredMoment_eq_binomial {m : ℕ} {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    shellCenteredMoment m k σ =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (shellScoreMean m σ) ^ i *
          (-1 : ℝ) ^ (k - i) * shellLogMoment m (k - i) σ := by
  have hterm (i : ℕ) : HasSum
      (fun n : ℕ => (k.choose i : ℝ) * (shellScoreMean m σ) ^ i *
        (-1 : ℝ) ^ (k - i) *
        (shellProbability m σ n * (Real.log n) ^ (k - i)))
      ((k.choose i : ℝ) * (shellScoreMean m σ) ^ i *
        (-1 : ℝ) ^ (k - i) * shellLogMoment m (k - i) σ) :=
    (shellLogMoment_hasSum hσ (k - i)).mul_left
      ((k.choose i : ℝ) * (shellScoreMean m σ) ^ i * (-1 : ℝ) ^ (k - i))
  have hfun : (fun n : ℕ => shellProbability m σ n * (shellCenteredScore m σ n) ^ k) =
      (fun n : ℕ => ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * (shellScoreMean m σ) ^ i *
          (-1 : ℝ) ^ (k - i) *
          (shellProbability m σ n * (Real.log n) ^ (k - i))) := by
    funext n
    rw [shellCenteredScore]
    have hbin := add_pow (shellScoreMean m σ) (-Real.log n) k
    rw [add_comm (-Real.log n) (shellScoreMean m σ), hbin]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [neg_pow]
    ring
  rw [shellCenteredMoment, hfun]
  rw [Summable.tsum_finsetSum (fun i _ => (hterm i).summable)]
  apply Finset.sum_congr rfl
  intro i _
  exact (hterm i).tsum_eq

section ShellMarkovFisher

variable {κ : Type*}

/-- Positive Markov observation of the centered shell score remains centered. -/
theorem shellMarkov_scoreMean_zero {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) {K : ℕ → κ → ℝ} {s : κ → ℝ}
    (hrow : ∀ n, HasSum (K n) 1)
    (hscore : ∀ y,
      countableMarkovPushforward (shellProbability m σ) K y * s y =
        countableMarkovScoreCurrent (shellProbability m σ)
          (shellCenteredScore m σ) K y)
    (hjoint : Summable (fun p : ℕ × κ =>
      shellProbability m σ p.1 * K p.1 p.2 * shellCenteredScore m σ p.1)) :
    ∑' y, countableMarkovPushforward (shellProbability m σ) K y * s y = 0 := by
  apply countableMarkov_scoreMean_zero hrow hscore hjoint
  exact (shellCenteredScore_hasSum_zero hm hσ).tsum_eq

/-- Exact Fisher conservation for every summably admitted shell observer. -/
theorem shellMarkov_fisher_conservation {m : ℕ} {σ : ℝ}
    {K : ℕ → κ → ℝ} {s : κ → ℝ}
    (hrow : ∀ n, HasSum (K n) 1)
    (hscore : ∀ y,
      countableMarkovPushforward (shellProbability m σ) K y * s y =
        countableMarkovScoreCurrent (shellProbability m σ)
          (shellCenteredScore m σ) K y)
    (hfirst : Summable (fun p : ℕ × κ =>
      shellProbability m σ p.1 * K p.1 p.2 * shellCenteredScore m σ p.1 ^ 2))
    (hcross : Summable (fun p : ℕ × κ =>
      shellProbability m σ p.1 * K p.1 p.2 * shellCenteredScore m σ p.1 * s p.2))
    (hlast : Summable (fun p : ℕ × κ =>
      shellProbability m σ p.1 * K p.1 p.2 * s p.2 ^ 2)) :
    shellCenteredMoment m 2 σ =
      ∑' y, countableMarkovPushforward (shellProbability m σ) K y * s y ^ 2 +
        countableMarkovConditionalLoss (shellProbability m σ)
          (shellCenteredScore m σ) K s := by
  simpa [shellCenteredMoment] using
    (countableMarkov_secondMoment_conservation hrow hscore hfirst hcross hlast)

/-- Every positive summably admitted shell observer has Fisher information at most the source. -/
theorem shellMarkov_fisher_dataProcessing {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) {K : ℕ → κ → ℝ} {s : κ → ℝ}
    (hK : ∀ n y, 0 ≤ K n y)
    (hrow : ∀ n, HasSum (K n) 1)
    (hscore : ∀ y,
      countableMarkovPushforward (shellProbability m σ) K y * s y =
        countableMarkovScoreCurrent (shellProbability m σ)
          (shellCenteredScore m σ) K y)
    (hfirst : Summable (fun p : ℕ × κ =>
      shellProbability m σ p.1 * K p.1 p.2 * shellCenteredScore m σ p.1 ^ 2))
    (hcross : Summable (fun p : ℕ × κ =>
      shellProbability m σ p.1 * K p.1 p.2 * shellCenteredScore m σ p.1 * s p.2))
    (hlast : Summable (fun p : ℕ × κ =>
      shellProbability m σ p.1 * K p.1 p.2 * s p.2 ^ 2)) :
    (∑' y, countableMarkovPushforward (shellProbability m σ) K y * s y ^ 2) ≤
      shellCenteredMoment m 2 σ := by
  simpa [shellCenteredMoment] using
    (countableMarkov_secondMoment_dataProcessing
      (shellProbability_nonneg hm hσ) hK hrow hscore hfirst hcross hlast)

/-- Equality in shell Fisher data processing is exactly preservation of the log-clock score. -/
theorem shellMarkov_fisher_eq_iff_scorePreserved {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) {K : ℕ → κ → ℝ} {s : κ → ℝ}
    (hK : ∀ n y, 0 ≤ K n y)
    (hrow : ∀ n, HasSum (K n) 1)
    (hscore : ∀ y,
      countableMarkovPushforward (shellProbability m σ) K y * s y =
        countableMarkovScoreCurrent (shellProbability m σ)
          (shellCenteredScore m σ) K y)
    (hfirst : Summable (fun p : ℕ × κ =>
      shellProbability m σ p.1 * K p.1 p.2 * shellCenteredScore m σ p.1 ^ 2))
    (hcross : Summable (fun p : ℕ × κ =>
      shellProbability m σ p.1 * K p.1 p.2 * shellCenteredScore m σ p.1 * s p.2))
    (hlast : Summable (fun p : ℕ × κ =>
      shellProbability m σ p.1 * K p.1 p.2 * s p.2 ^ 2)) :
    (∑' y, countableMarkovPushforward (shellProbability m σ) K y * s y ^ 2) =
        shellCenteredMoment m 2 σ ↔
      ∀ n y, 0 < shellProbability m σ n * K n y →
        shellCenteredScore m σ n = s y := by
  simpa [shellCenteredMoment] using
    (countableMarkov_secondMoment_eq_iff_scorePreserved
      (shellProbability_nonneg hm hσ) hK hrow hscore hfirst hcross hlast)

end ShellMarkovFisher

/-- Centered infinitesimal tangent of the shell exponential family. -/
def shellExponentialTangent (m : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  shellProbability m σ n * shellCenteredScore m σ n

/-- The centered shell score is unbounded below on positive-probability atoms. -/
theorem shellCenteredScore_unboundedBelow_on_support {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) (B : ℝ) :
    ∃ n : ℕ, 0 < shellProbability m σ n ∧ shellCenteredScore m σ n < B := by
  let C : ℝ := |shellScoreMean m σ - B| + 1
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (Nat.ceil (Real.exp C) + 1)
  have hpgt : Nat.ceil (Real.exp C) < p := by omega
  have hbig : Real.exp C < (p : ℝ) := by
    have hceil : Real.exp C ≤ (Nat.ceil (Real.exp C) : ℝ) := Nat.le_ceil _
    have hpcast : (Nat.ceil (Real.exp C) : ℝ) < (p : ℝ) := by exact_mod_cast hpgt
    exact hceil.trans_lt hpcast
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlog : C < Real.log p := (Real.lt_log_iff_exp_lt hpR).mpr hbig
  have hlogpos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have hmlog : Real.log p ≤ (m : ℝ) * Real.log p := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    nlinarith
  refine ⟨p ^ m, _root_.HTGeometry.ConstraintMotiveRelativity.shellProbability_prime_pow_pos
    hp hm hσ, ?_⟩
  rw [shellCenteredScore, Nat.cast_pow, Real.log_pow]
  have hCB : shellScoreMean m σ - B < C := by
    dsimp [C]
    linarith [le_abs_self (shellScoreMean m σ - B)]
  linarith

/-- The shell tangent obeys the finite-carrier compatibility condition. -/
theorem shellExponentialTangent_finitelyAdmitted {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) :
    FinitelyAdmitted (shellProbability m σ) (shellExponentialTangent m σ) := by
  apply finitelyAdmitted_of_contingentlyLegal
  · exact shellProbability_nonneg hm hσ
  · intro n hn
    rw [shellExponentialTangent, hn, zero_mul]

/-- Unbounded negative score gives the shell tangent zero straight admission radius. -/
theorem shellExponentialTangent_not_straightAdmitted {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) :
    ¬ StraightAdmitted (shellProbability m σ) (shellExponentialTangent m σ) := by
  rintro ⟨ε, hε, hall⟩
  obtain ⟨n, hnP, hnscore⟩ :=
    shellCenteredScore_unboundedBelow_on_support hm hσ (-1 / ε)
  have hneg : shellProbability m σ n + ε * shellExponentialTangent m σ n < 0 := by
    rw [shellExponentialTangent]
    have hfactor : shellProbability m σ n +
        ε * (shellProbability m σ n * shellCenteredScore m σ n) =
      shellProbability m σ n * (1 + ε * shellCenteredScore m σ n) := by ring
    rw [hfactor]
    apply mul_neg_of_pos_of_neg hnP
    have := (lt_div_iff₀ hε).mp hnscore
    linarith
  exact (not_lt_of_ge (hall n)) hneg

/-- Imaginary time is the centered phase reporter of the same source-ratio germ. -/
theorem shellComplexPartition_imaginary {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) (s : ℝ) :
    shellComplexPartition m σ ((s : ℂ) * Complex.I) =
      Complex.exp (((s : ℂ) * Complex.I) * (shellScoreMean m σ : ℂ)) *
        shellSource m ((σ : ℂ) + (s : ℂ) * Complex.I) /
          shellSource m (σ : ℂ) := by
  apply shellComplexPartition_eq_sourceRatio hm hσ
  simpa using hσ

/-- A finite measure is uniquely determined by its phase reporter on the entire real line. -/
theorem finiteMeasure_eq_of_phaseReporter_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hphase : ∀ s : ℝ, charFun μ s = charFun ν s) :
    μ = ν := by
  apply Measure.ext_of_charFun
  funext s
  exact hphase s

/-- Real exponential partition of the centered shell score. -/
def shellRealPartition (m : ℕ) (σ t : ℝ) : ℝ :=
  ∑' n : ℕ, shellProbability m σ n *
    Real.exp (t * shellCenteredScore m σ n)

/-- Every unnormalized tilt term is a positive scalar times shell mass at the shifted abscissa. -/
theorem shellRealPartition_term_eq_shiftedMass {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (n : ℕ) :
    shellProbability m σ n * Real.exp (t * shellCenteredScore m σ n) =
      (Real.exp (t * shellScoreMean m σ) / shellMellin m σ) *
        shellMass m (σ + t) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [shellProbability, shellMass]
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [shellProbability, shellMass, shellMass, shellCenteredScore, shellScoreMean]
    have hpow : (n : ℝ) ^ (σ + t) = (n : ℝ) ^ σ * (n : ℝ) ^ t :=
      Real.rpow_add hnR σ t
    have hexp : Real.exp (t * (-Real.log n + shellLogMoment m 1 σ)) =
        Real.exp (t * shellLogMoment m 1 σ) / (n : ℝ) ^ t := by
      rw [Real.rpow_def_of_pos hnR, ← Real.exp_sub]
      congr 1
      ring
    rw [hpow, hexp]
    have hZσ : shellMellin m σ ≠ 0 := (shellMellin_pos hm hσ).ne'
    have hEt : Real.exp (t * shellLogMoment m 1 σ) ≠ 0 := (Real.exp_pos _).ne'
    have hpowσ : (n : ℝ) ^ σ ≠ 0 := (Real.rpow_pos_of_pos hnR σ).ne'
    have hpowt : (n : ℝ) ^ t ≠ 0 := (Real.rpow_pos_of_pos hnR t).ne'
    field_simp [hZσ, hEt, hpowσ, hpowt]

/-- Normalized real exponential tilt of the shell score. -/
def shellExponentialTilt (m : ℕ) (σ t : ℝ) (n : ℕ) : ℝ :=
  shellProbability m σ n * Real.exp (t * shellCenteredScore m σ n) /
    shellRealPartition m σ t

/-- The real shell partition is the exact shifted Mellin-source ratio. -/
theorem shellRealPartition_eq_mellinRatio {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) {t : ℝ} (hst : 1 < σ + t) :
    shellRealPartition m σ t =
      Real.exp (t * shellScoreMean m σ) * shellMellin m (σ + t) / shellMellin m σ := by
  apply Complex.ofReal_injective
  have hcast : ((shellRealPartition m σ t : ℝ) : ℂ) =
      shellComplexPartition m σ (t : ℂ) := by
    rw [shellRealPartition, Complex.ofReal_tsum, shellComplexPartition]
    refine tsum_congr fun n => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    rfl
  rw [hcast, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp,
    ofReal_shellMellin hm hσ, ofReal_shellMellin hm hst]
  simpa only [Complex.ofReal_add, Complex.ofReal_mul] using
    (shellComplexPartition_eq_sourceRatio (z := (t : ℂ)) hm hσ (by simpa using hst))

theorem shellRealPartition_pos {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) {t : ℝ} (hst : 1 < σ + t) :
    0 < shellRealPartition m σ t := by
  rw [shellRealPartition_eq_mellinRatio hm hσ hst]
  exact div_pos (mul_pos (Real.exp_pos _) (shellMellin_pos hm hst))
    (shellMellin_pos hm hσ)

/-- Real exponential tilting is literally transport to the shifted shell Gibbs fibre. -/
theorem shellExponentialTilt_eq_shift {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) {t : ℝ} (hst : 1 < σ + t) (n : ℕ) :
    shellExponentialTilt m σ t n = shellProbability m (σ + t) n := by
  rw [shellExponentialTilt, shellRealPartition_eq_mellinRatio hm hσ hst]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [shellProbability, shellMass]
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [shellProbability, shellProbability, shellMass, shellMass,
      shellCenteredScore, shellScoreMean]
    have hpow : (n : ℝ) ^ (σ + t) = (n : ℝ) ^ σ * (n : ℝ) ^ t := by
      exact Real.rpow_add hnR σ t
    have hexp : Real.exp (t * (-Real.log n + shellLogMoment m 1 σ)) =
        Real.exp (t * shellLogMoment m 1 σ) / (n : ℝ) ^ t := by
      rw [Real.rpow_def_of_pos hnR, ← Real.exp_sub]
      congr 1
      ring
    rw [hpow, hexp]
    have hZσ : shellMellin m σ ≠ 0 := (shellMellin_pos hm hσ).ne'
    have hZst : shellMellin m (σ + t) ≠ 0 := (shellMellin_pos hm hst).ne'
    have hEt : Real.exp (t * shellLogMoment m 1 σ) ≠ 0 := (Real.exp_pos _).ne'
    have hpowσ : (n : ℝ) ^ σ ≠ 0 := (Real.rpow_pos_of_pos hnR σ).ne'
    have hpowt : (n : ℝ) ^ t ≠ 0 := (Real.rpow_pos_of_pos hnR t).ne'
    field_simp [hZσ, hZst, hEt, hpowσ, hpowt]

/-- The shifted shell tilt is normalized throughout its exact real domain. -/
theorem hasSum_shellExponentialTilt {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) {t : ℝ} (hst : 1 < σ + t) :
    HasSum (shellExponentialTilt m σ t) 1 := by
  have hfun : shellExponentialTilt m σ t = shellProbability m (σ + t) := by
    funext n
    exact shellExponentialTilt_eq_shift hm hσ hst n
  rw [hfun]
  exact hasSum_shellProbability hm hst

/-- The shell Mellin mass diverges to infinity on approach to the normalization wall. -/
theorem tendsto_shellMellin_at_wall {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (shellMellin m) (𝓝[>] (1 : ℝ)) atTop := by
  have hsub0 : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hbase : Tendsto (fun σ : ℝ => σ - 1) (𝓝 (1 : ℝ)) (𝓝 0) := by
      have hid : Tendsto (id : ℝ → ℝ) (𝓝 (1 : ℝ)) (𝓝 (1 : ℝ)) := tendsto_id
      simpa using hid.sub_const (1 : ℝ)
    exact hbase.mono_left nhdsWithin_le_nhds
  have hsubpos : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), 0 < σ - 1 := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact sub_pos.mpr hσ
  have hsubGT' : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsub0, hsubpos⟩
  have hinv := hsubGT'.inv_tendsto_nhdsGT_zero
  have hprod := hinv.atTop_mul_pos (shellResidue_pos (by omega))
    (tendsto_shellMellin_residue hm)
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hne : σ - 1 ≠ 0 := (sub_pos.mpr hσ).ne'
  change (σ - 1)⁻¹ * ((σ - 1) * shellMellin m σ) = shellMellin m σ
  field_simp

/-- Shell mass is not summable at the exact abscissa wall `σ = 1`. -/
theorem not_summable_shellMass_at_wall {m : ℕ} (hm : 12 ≤ m) :
    ¬ Summable (shellMass m 1) := by
  intro hsum
  have hle : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      shellMellin m σ ≤ ∑' n : ℕ, shellMass m 1 n := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [shellMellin_eq_tsum (by omega) hσ]
    exact Summable.tsum_le_tsum (fun n => by
      unfold shellMass
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hind : (0 : ℝ) ≤ (shellIndicator m n : ℝ) := by
          rcases shellIndicator_eq_zero_or_one m n with h | h <;> rw [h]
          · exact_mod_cast (le_rfl : (0 : ℤ) ≤ 0)
          · exact_mod_cast (zero_le_one : (0 : ℤ) ≤ 1)
        apply mul_le_mul_of_nonneg_left _ hind
        rw [← Real.rpow_neg (Nat.cast_nonneg n), ← Real.rpow_neg (Nat.cast_nonneg n)]
        exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hσ.le))
      (summable_shellMass m hσ) hsum
  have hgt := (tendsto_shellMellin_at_wall hm).eventually
    (eventually_gt_atTop (∑' n : ℕ, shellMass m 1 n))
  obtain ⟨σ, hleσ, hgtσ⟩ := (hle.and hgt).exists
  exact (not_lt_of_ge hleσ) hgtσ

/-- Exact negative-time lifetime of a shell fibre. -/
def shellNegativeLifetime (σ : ℝ) : ℝ := σ - 1

theorem shell_negative_time_domain_iff {σ t : ℝ} :
    1 < σ + t ↔ -shellNegativeLifetime σ < t := by
  constructor <;> intro h <;> dsimp [shellNegativeLifetime] at * <;> linarith

theorem shell_hits_wall_at_negative_lifetime (σ : ℝ) :
    σ + (-shellNegativeLifetime σ) = 1 := by
  unfold shellNegativeLifetime
  ring

/-- The real partition series itself diverges at its exact negative lifetime. -/
theorem not_summable_shellRealPartition_at_wall {m : ℕ} (hm : 12 ≤ m)
    {σ : ℝ} (hσ : 1 < σ) :
    ¬ Summable (fun n : ℕ => shellProbability m σ n *
      Real.exp ((-shellNegativeLifetime σ) * shellCenteredScore m σ n)) := by
  intro hsum
  let c : ℝ := Real.exp ((-shellNegativeLifetime σ) * shellScoreMean m σ) /
    shellMellin m σ
  have hc : c ≠ 0 := by
    exact div_ne_zero (Real.exp_ne_zero _)
      (shellMellin_pos (by omega) hσ).ne'
  have hcmass : Summable (fun n : ℕ => c * shellMass m 1 n) := by
    refine hsum.congr ?_
    intro n
    rw [shellRealPartition_term_eq_shiftedMass (by omega) hσ]
    rw [shell_hits_wall_at_negative_lifetime]
  exact not_summable_shellMass_at_wall hm ((summable_mul_left_iff hc).mp hcmass)

/-- The shell source is analytic throughout its positive-convergence half-plane. -/
theorem analyticAt_shellSource_of_one_lt {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) :
    AnalyticAt ℂ (shellSource m) (σ : ℂ) := by
  have h1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have habs := abscissaOfAbsConv_shellIndicator_lt m h1
  have hL : AnalyticAt ℂ (LSeries ↗(shellIndicator m)) (σ : ℂ) :=
    LSeries_analyticOnNhd ↗(shellIndicator m) (σ : ℂ) habs
  exact hL.congr (LSeries_shellIndicator_eventuallyEq_shellSource m hm h1)

/-- Every source derivative is its logarithmic moment times the exact parity and source value. -/
theorem iteratedDeriv_shellSource_eq_logMoment {m : ℕ} (hm : m ≠ 0)
    (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    iteratedDeriv k (shellSource m) (σ : ℂ) =
      (-1 : ℂ) ^ k * (shellLogMoment m k σ : ℂ) * shellSource m (σ : ℂ) := by
  have hZ0 : shellSource m (σ : ℂ) ≠ 0 := by
    rw [← ofReal_shellMellin hm hσ]
    exact_mod_cast (shellMellin_pos hm hσ).ne'
  have hmom := ofReal_shellLogMoment hm k hσ
  have hmul : (shellLogMoment m k σ : ℂ) * shellSource m (σ : ℂ) =
      (-1 : ℂ) ^ k * iteratedDeriv k (shellSource m) (σ : ℂ) :=
    (eq_div_iff hZ0).mp hmom
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc
    iteratedDeriv k (shellSource m) (σ : ℂ) =
        ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) *
          iteratedDeriv k (shellSource m) (σ : ℂ) := by rw [hsign, one_mul]
    _ = (-1 : ℂ) ^ k *
        ((-1 : ℂ) ^ k * iteratedDeriv k (shellSource m) (σ : ℂ)) := by ring
    _ = (-1 : ℂ) ^ k *
        ((shellLogMoment m k σ : ℂ) * shellSource m (σ : ℂ)) := by rw [← hmul]
    _ = _ := by ring

/-- Explicit analytic germ equal to the countable partition near zero. -/
def shellComplexPartitionGerm (m : ℕ) (σ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((shellScoreMean m σ : ℂ) * z) *
    shellSource m ((σ : ℂ) + z) / shellSource m (σ : ℂ)

theorem shellComplexPartition_eventuallyEq_germ {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) :
    shellComplexPartition m σ =ᶠ[𝓝 0] shellComplexPartitionGerm m σ := by
  have h1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hopen : {w : ℂ | 1 < w.re} ∈ 𝓝 (σ : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1
  have hc : ContinuousAt (fun z : ℂ => (σ : ℂ) + z) (0 : ℂ) :=
    continuousAt_const.add continuousAt_id
  have hshift : Tendsto (fun z : ℂ => (σ : ℂ) + z) (𝓝 0) (𝓝 (σ : ℂ)) := by
    change Tendsto (fun z : ℂ => (σ : ℂ) + z) (𝓝 0)
      (𝓝 ((σ : ℂ) + (0 : ℂ))) at hc
    simpa using hc
  filter_upwards [hshift.eventually hopen] with z hz
  simpa [shellComplexPartitionGerm, mul_comm] using
    (shellComplexPartition_eq_sourceRatio (z := z) hm hσ hz)

/-- Full all-order countable derivative tower: derivatives at zero are centered shell moments. -/
theorem iteratedDeriv_shellComplexPartition {m : ℕ} (hm : m ≠ 0)
    {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    iteratedDeriv k (shellComplexPartition m σ) 0 =
      (shellCenteredMoment m k σ : ℂ) := by
  rw [(shellComplexPartition_eventuallyEq_germ hm hσ).iteratedDeriv_eq k]
  change iteratedDeriv k
      (fun z : ℂ => Complex.exp ((shellScoreMean m σ : ℂ) * z) *
        shellSource m ((σ : ℂ) + z) / shellSource m (σ : ℂ)) 0 = _
  rw [iteratedDeriv_div_const]
  have hexp : ContDiffAt ℂ k
      (fun z : ℂ => Complex.exp ((shellScoreMean m σ : ℂ) * z)) 0 := by
    fun_prop
  have hshiftAna : AnalyticAt ℂ (fun z : ℂ => (σ : ℂ) + z) 0 :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (σ : ℂ)) 0).add analyticAt_id
  have hsource : ContDiffAt ℂ k
      (fun z : ℂ => shellSource m ((σ : ℂ) + z)) 0 :=
    ((analyticAt_shellSource_of_one_lt hm hσ).comp_of_eq hshiftAna (by simp)).contDiffAt
  change iteratedDeriv k
      ((fun z : ℂ => Complex.exp ((shellScoreMean m σ : ℂ) * z)) *
        (fun z : ℂ => shellSource m ((σ : ℂ) + z))) 0 /
      shellSource m (σ : ℂ) = _
  rw [iteratedDeriv_mul hexp hsource]
  simp_rw [iteratedDeriv_cexp_const_mul]
  simp_rw [iteratedDeriv_comp_const_add]
  simp_rw [mul_zero, Complex.exp_zero, mul_one, add_zero]
  simp_rw [iteratedDeriv_shellSource_eq_logMoment hm _ hσ]
  rw [shellCenteredMoment_eq_binomial hσ k]
  push_cast
  have hZ0 : shellSource m (σ : ℂ) ≠ 0 := by
    rw [← ofReal_shellMellin hm hσ]
    exact_mod_cast (shellMellin_pos hm hσ).ne'
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hZ0]

/-- One theorem packages the exact positive, phase, moment, and wall faces of the shell germ. -/
theorem shellComplexTime_fourOrganFusion {m : ℕ} (hm : 12 ≤ m)
    {σ : ℝ} (hσ : 1 < σ) :
    (∀ z : ℂ, 1 < ((σ : ℂ) + z).re →
      shellComplexPartition m σ z =
        Complex.exp (z * (shellScoreMean m σ : ℂ)) *
          shellSource m ((σ : ℂ) + z) / shellSource m (σ : ℂ)) ∧
    (∀ t : ℝ, 1 < σ + t → ∀ n : ℕ,
      shellExponentialTilt m σ t n = shellProbability m (σ + t) n) ∧
    (∀ s : ℝ,
      shellComplexPartition m σ ((s : ℂ) * Complex.I) =
        Complex.exp (((s : ℂ) * Complex.I) * (shellScoreMean m σ : ℂ)) *
          shellSource m ((σ : ℂ) + (s : ℂ) * Complex.I) /
            shellSource m (σ : ℂ)) ∧
    (∀ k : ℕ, iteratedDeriv k (shellComplexPartition m σ) 0 =
      (shellCenteredMoment m k σ : ℂ)) ∧
    (∀ t : ℝ, 1 < σ + t ↔ -shellNegativeLifetime σ < t) ∧
    σ + (-shellNegativeLifetime σ) = 1 ∧
    ¬ Summable (fun n : ℕ => shellProbability m σ n *
      Real.exp ((-shellNegativeLifetime σ) * shellCenteredScore m σ n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, shell_hits_wall_at_negative_lifetime σ,
    not_summable_shellRealPartition_at_wall hm hσ⟩
  · intro z hz
    exact shellComplexPartition_eq_sourceRatio (by omega) hσ hz
  · intro t ht n
    exact shellExponentialTilt_eq_shift (by omega) hσ ht n
  · intro s
    exact shellComplexPartition_imaginary (by omega) hσ s
  · intro k
    exact iteratedDeriv_shellComplexPartition (by omega) hσ k
  · intro t
    exact shell_negative_time_domain_iff

end GaloisForLFunctions.HTGeometry
