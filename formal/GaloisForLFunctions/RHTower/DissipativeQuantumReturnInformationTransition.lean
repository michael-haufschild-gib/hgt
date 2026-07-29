import GaloisForLFunctions.RHTower.ProjectiveWeightedFloquetRecurrence
import GaloisForLFunctions.HTGeometry.PeripheralContractionPointSpectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Dissipative quantum return information transition

A finite contractive evolution separates into a persistent phase packet and a
transient term.  This file isolates the quantitative law after that
decomposition.  The persistent mass is an asymptotic return-amplitude ceiling.
Below it, the existing reverse-water recurrence deadline controls a return
after any certified transient burn-in; above it, sufficiently late return is
impossible.

The operator-theoretic peripheral/transient decomposition and the
bistochastic-channel specialization are developed in downstream files.
-/

open Filter
open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- A persistent weighted phase packet, scaled by its surviving mass and
perturbed by an arbitrary transient amplitude. -/
def dissipativeWeightedReturnAmplitude {d : ℕ}
    (persistentMass : ℝ) (w : Fin d → ℝ) (omega : Fin d → ℝ)
    (transient : ℕ → ℂ) (n : ℕ) : ℂ :=
  (persistentMass : ℂ) * weightedFloquetReturnAmplitude w omega n +
    transient n

/-- Transient autocorrelation of a finite damped spectral packet. -/
def finiteDampedTransientAmplitude {s : ℕ}
    (coefficient eigenvalue : Fin s → ℂ) (n : ℕ) : ℂ :=
  ∑ j, coefficient j * eigenvalue j ^ n

/-- Transient amplitude allowing every finite Jordan correction: a finite
sum of polynomially weighted modes `n^k λ^n`. -/
def finitePolynomialDampedTransientAmplitude {s degree : ℕ}
    (coefficient : Fin s → Fin degree → ℂ)
    (eigenvalue : Fin s → ℂ) (n : ℕ) : ℂ :=
  ∑ j, ∑ k, coefficient j k * (n : ℂ) ^ (k : ℕ) *
    eigenvalue j ^ n

/-- Every finite packet supported strictly inside the unit disk decays to
zero. -/
theorem tendsto_finiteDampedTransientAmplitude_zero
    {s : ℕ} (coefficient eigenvalue : Fin s → ℂ)
    (heigenvalue : ∀ j, ‖eigenvalue j‖ < 1) :
    Tendsto (finiteDampedTransientAmplitude coefficient eigenvalue)
      atTop (𝓝 0) := by
  rw [show (0 : ℂ) = ∑ _j : Fin s, 0 by simp]
  apply tendsto_finsetSum
  intro j _hj
  simpa only [finiteDampedTransientAmplitude, mul_zero] using
    (tendsto_const_nhds :
      Tendsto (fun _n : ℕ => coefficient j) atTop
        (𝓝 (coefficient j))).mul
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (heigenvalue j))

/-- Every polynomially weighted mode strictly inside the unit disk decays
to zero. -/
theorem tendsto_polynomialDampedMode_zero
    (degree : ℕ) (coefficient eigenvalue : ℂ)
    (heigenvalue : ‖eigenvalue‖ < 1) :
    Tendsto
      (fun n : ℕ => coefficient * (n : ℂ) ^ degree *
        eigenvalue ^ n)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hreal :
      Tendsto
        (fun n : ℕ => (n : ℝ) ^ degree * ‖eigenvalue‖ ^ n)
        atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one degree
      (norm_nonneg eigenvalue) heigenvalue
  simpa only [norm_mul, norm_pow, Complex.norm_natCast, mul_assoc,
    mul_zero] using hreal.const_mul ‖coefficient‖

/-- Every finite polynomially damped packet supported strictly inside the
unit disk decays to zero.  This includes all finite Jordan-block
transients, not only diagonalizable damped modes. -/
theorem tendsto_finitePolynomialDampedTransientAmplitude_zero
    {s degree : ℕ} (coefficient : Fin s → Fin degree → ℂ)
    (eigenvalue : Fin s → ℂ)
    (heigenvalue : ∀ j, ‖eigenvalue j‖ < 1) :
    Tendsto
      (finitePolynomialDampedTransientAmplitude coefficient eigenvalue)
      atTop (𝓝 0) := by
  rw [show (0 : ℂ) = ∑ _j : Fin s, ∑ _k : Fin degree, 0 by simp]
  apply tendsto_finsetSum
  intro j _hj
  apply tendsto_finsetSum
  intro k _hk
  simpa only [finitePolynomialDampedTransientAmplitude] using
    tendsto_polynomialDampedMode_zero (k : ℕ)
      (coefficient j k) (eigenvalue j) (heigenvalue j)

/-- Explicit geometric envelope for a finite damped spectral packet. -/
theorem norm_finiteDampedTransientAmplitude_le_geometric
    {s : ℕ} (coefficient eigenvalue : Fin s → ℂ)
    (q : ℝ)
    (heigenvalue : ∀ j, ‖eigenvalue j‖ ≤ q) (n : ℕ) :
    ‖finiteDampedTransientAmplitude coefficient eigenvalue n‖ ≤
      q ^ n * ∑ j, ‖coefficient j‖ := by
  rw [finiteDampedTransientAmplitude]
  calc
    ‖∑ j, coefficient j * eigenvalue j ^ n‖ ≤
        ∑ j, ‖coefficient j * eigenvalue j ^ n‖ :=
      norm_sum_le _ _
    _ = ∑ j, ‖coefficient j‖ * ‖eigenvalue j‖ ^ n := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_mul, norm_pow]
    _ ≤ ∑ j, ‖coefficient j‖ * q ^ n := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (heigenvalue j) n)
        (norm_nonneg _)
    _ = q ^ n * ∑ j, ‖coefficient j‖ := by
      rw [← Finset.sum_mul]
      ring

/-- Quantifier form of an exact asymptotic amplitude ceiling.  The first
clause is eventual upper control; the second says the ceiling is approached
at arbitrarily late clocks. -/
def IsExactAsymptoticReturnAmplitudeCeiling
    (amplitude : ℕ → ℂ) (ceiling : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∀ n : ℕ, B ≤ n →
      ‖amplitude n‖ < ceiling + ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ M : ℕ, ∃ n : ℕ, M < n ∧
      ceiling - ε ≤ ‖amplitude n‖)

/-- Quantifier form of an exact asymptotic fidelity ceiling. -/
def IsExactAsymptoticReturnFidelityCeiling
    (amplitude : ℕ → ℂ) (ceiling : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∀ n : ℕ, B ≤ n →
      ‖amplitude n‖ ^ 2 < ceiling + ε) ∧
    (∀ ε : ℝ, 0 < ε → ∀ M : ℕ, ∃ n : ℕ, M < n ∧
      ceiling - ε ≤ ‖amplitude n‖ ^ 2)

/-- Squaring a nonnegative exact amplitude ceiling produces the exact
fidelity ceiling. -/
theorem IsExactAsymptoticReturnAmplitudeCeiling.fidelity
    {amplitude : ℕ → ℂ} {ceiling : ℝ}
    (hceiling :
      IsExactAsymptoticReturnAmplitudeCeiling amplitude ceiling)
    (hceiling0 : 0 ≤ ceiling) :
    IsExactAsymptoticReturnFidelityCeiling amplitude (ceiling ^ 2) := by
  constructor
  · intro ε hε
    let δ : ℝ := min 1 (ε / (4 * (ceiling + 1)))
    have hdenom : 0 < 4 * (ceiling + 1) := by positivity
    have hδ0 : 0 < δ := by
      exact lt_min one_pos (div_pos hε hdenom)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδbudget : 4 * (ceiling + 1) * δ ≤ ε := by
      have hδle : δ ≤ ε / (4 * (ceiling + 1)) :=
        min_le_right _ _
      simpa only [mul_comm] using (le_div_iff₀ hdenom).mp hδle
    obtain ⟨B, hB⟩ := hceiling.1 δ hδ0
    refine ⟨B, fun n hn => ?_⟩
    have hnorm := hB n hn
    have hsum0 : 0 ≤ ceiling + δ := add_nonneg hceiling0 hδ0.le
    have hsquare :
        ‖amplitude n‖ ^ 2 < (ceiling + δ) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) hsum0).2 hnorm
    nlinarith [sq_nonneg δ]
  · intro ε hε M
    by_cases hsmall : ceiling ^ 2 ≤ ε
    · refine ⟨M + 1, Nat.lt_succ_self M, ?_⟩
      exact le_trans (sub_nonpos.mpr hsmall) (sq_nonneg _)
    · have hceilingPos : 0 < ceiling := by
        by_contra hnot
        have hzero : ceiling = 0 := le_antisymm (le_of_not_gt hnot) hceiling0
        rw [hzero, zero_pow (by norm_num)] at hsmall
        exact hsmall (le_of_lt hε)
      let δ : ℝ :=
        min (ceiling / 2) (ε / (4 * (ceiling + 1)))
      have hdenom : 0 < 4 * (ceiling + 1) := by positivity
      have hδ0 : 0 < δ := by
        exact lt_min (half_pos hceilingPos) (div_pos hε hdenom)
      have hδhalf : δ ≤ ceiling / 2 := min_le_left _ _
      have hδbudget : 4 * (ceiling + 1) * δ ≤ ε := by
        have hδle : δ ≤ ε / (4 * (ceiling + 1)) :=
          min_le_right _ _
        simpa only [mul_comm] using (le_div_iff₀ hdenom).mp hδle
      obtain ⟨n, hnM, hn⟩ := hceiling.2 δ hδ0 M
      refine ⟨n, hnM, ?_⟩
      have hlower0 : 0 ≤ ceiling - δ := by linarith
      have hsquare :
          (ceiling - δ) ^ 2 ≤ ‖amplitude n‖ ^ 2 :=
        (sq_le_sq₀ hlower0 (norm_nonneg _)).2 hn
      nlinarith [sq_nonneg δ]

/-- A normalized nonnegative weighted Floquet amplitude has norm at most
one at every clock. -/
theorem norm_weightedFloquetReturnAmplitude_le_one
    {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1) (omega : Fin d → ℝ) (n : ℕ) :
    ‖weightedFloquetReturnAmplitude w omega n‖ ≤ 1 := by
  rw [weightedFloquetReturnAmplitude]
  calc
    ‖∑ j, (w j : ℂ) * Complex.exp
        (Complex.I * ((((n : ℝ) * omega j : ℝ) : ℂ)))‖ ≤
        ∑ j, ‖(w j : ℂ) * Complex.exp
          (Complex.I * ((((n : ℝ) * omega j : ℝ) : ℂ)))‖ :=
      norm_sum_le _ _
    _ = ∑ j, w j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw j), Complex.norm_exp_I_mul_ofReal, mul_one]
    _ = 1 := hmass

/-- A universal weighted Floquet deadline exists in every finite
dimension.  Normalization excludes dimension zero; dimension one returns
exactly at the first positive clock; all higher dimensions use the
projective recurrence theorem. -/
theorem exists_universalWeightedFloquetFidelityDeadline_allDimensions
    {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1)
    (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ N : ℕ, IsUniversalWeightedFloquetFidelityDeadline w eta N := by
  by_cases hd : 2 ≤ d
  · exact ⟨universalWeightedFloquetFidelityRecurrenceTime
        hd w hw hmass eta heta0 heta1,
      universalWeightedFloquetFidelityRecurrenceTime_isDeadline
        hd w hw hmass eta heta0 heta1⟩
  · have hdle : d ≤ 1 := by omega
    interval_cases d
    · simp at hmass
    · refine ⟨1, fun omega => ⟨1, by norm_num, by norm_num, ?_⟩⟩
      have hw0 : w 0 = 1 := by
        simpa only [Fin.sum_univ_one] using hmass
      have hfidelity :
          weightedFloquetReturnFidelity w omega 1 = 1 := by
        rw [weightedFloquetReturnFidelity,
          weightedFloquetReturnAmplitude, Fin.sum_univ_one, hw0]
        simp only [Nat.cast_one, one_mul, Complex.ofReal_one,
          Complex.norm_exp_I_mul_ofReal, one_pow]
      rw [hfidelity]
      have htarget0 : 0 ≤ 1 - eta := sub_nonneg.mpr heta1
      nlinarith

/-- The persistent part of a dissipative packet has norm at most its
surviving mass. -/
theorem norm_persistentWeightedReturnAmplitude_le
    {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1) {persistentMass : ℝ}
    (hpersistent : 0 ≤ persistentMass)
    (omega : Fin d → ℝ) (n : ℕ) :
    ‖(persistentMass : ℂ) * weightedFloquetReturnAmplitude w omega n‖ ≤
      persistentMass := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpersistent]
  calc
    persistentMass * ‖weightedFloquetReturnAmplitude w omega n‖ ≤
        persistentMass * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_weightedFloquetReturnAmplitude_le_one w hw hmass omega n)
        hpersistent
    _ = persistentMass := mul_one _

/-- A transient bound and one persistent recurrence give a full dissipative
return.  Dissipation contributes only the burn-in multiplier; the phase
resolution is paid by the persistent packet. -/
theorem IsUniversalWeightedFloquetFidelityDeadline.exists_dissipative_return_after
    {d N B : ℕ} {w : Fin d → ℝ} {eta persistentMass : ℝ}
    (hdeadline : IsUniversalWeightedFloquetFidelityDeadline w eta N)
    (heta1 : eta ≤ 1)
    (hpersistent : 0 ≤ persistentMass)
    (omega : Fin d → ℝ) (transient : ℕ → ℂ)
    (htransient : ∀ n : ℕ, B < n →
      ‖transient n‖ ≤ persistentMass * eta) :
    ∃ n : ℕ, B < n ∧ n ≤ (B + 1) * N ∧
      persistentMass * (1 - 2 * eta) ≤
        ‖dissipativeWeightedReturnAmplitude
          persistentMass w omega transient n‖ := by
  obtain ⟨n, hnB, hnN, hnfid⟩ :=
    isUniversalWeightedFloquetFidelityDeadline.exists_after
      hdeadline omega B
  have htarget : 0 ≤ 1 - eta := sub_nonneg.mpr heta1
  have hphase :
      1 - eta ≤ ‖weightedFloquetReturnAmplitude w omega n‖ := by
    exact (sq_le_sq₀ htarget (norm_nonneg _)).mp hnfid
  have hpersist :
      persistentMass * (1 - eta) ≤
        ‖(persistentMass : ℂ) *
          weightedFloquetReturnAmplitude w omega n‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hpersistent]
    exact mul_le_mul_of_nonneg_left hphase hpersistent
  have hreverse :
      ‖(persistentMass : ℂ) *
          weightedFloquetReturnAmplitude w omega n‖ -
          ‖transient n‖ ≤
        ‖dissipativeWeightedReturnAmplitude
          persistentMass w omega transient n‖ := by
    rw [dissipativeWeightedReturnAmplitude]
    simpa only [sub_neg_eq_add, norm_neg] using
      (norm_sub_norm_le
        ((persistentMass : ℂ) *
          weightedFloquetReturnAmplitude w omega n)
        (-transient n))
  refine ⟨n, hnB, hnN, ?_⟩
  have htr := htransient n hnB
  nlinarith

/-- Explicit target form of the dissipative return theorem.  If the
transient amplitude is at most half the gap from the persistent ceiling,
then the same half-gap is allocated to persistent phase recurrence. -/
theorem IsUniversalWeightedFloquetFidelityDeadline.exists_dissipative_return_at_target
    {d N B : ℕ} {w : Fin d → ℝ} {eta persistentMass target : ℝ}
    (hdeadline : IsUniversalWeightedFloquetFidelityDeadline w eta N)
    (hpersistent : 0 < persistentMass)
    (htarget0 : 0 ≤ target)
    (heta : eta = (persistentMass - target) / (2 * persistentMass))
    (omega : Fin d → ℝ) (transient : ℕ → ℂ)
    (htransient : ∀ n : ℕ, B < n →
      ‖transient n‖ ≤ (persistentMass - target) / 2) :
    ∃ n : ℕ, B < n ∧ n ≤ (B + 1) * N ∧
      target ≤ ‖dissipativeWeightedReturnAmplitude
        persistentMass w omega transient n‖ := by
  have heta1 : eta ≤ 1 := by
    rw [heta]
    have hp : 0 < 2 * persistentMass := by positivity
    apply (div_le_iff₀ hp).2
    nlinarith
  have htransient' : ∀ n : ℕ, B < n →
      ‖transient n‖ ≤ persistentMass * eta := by
    intro n hn
    calc
      ‖transient n‖ ≤ (persistentMass - target) / 2 :=
        htransient n hn
      _ = persistentMass * eta := by
        rw [heta]
        field_simp [hpersistent.ne']
  obtain ⟨n, hnB, hnN, hn⟩ :=
    hdeadline.exists_dissipative_return_after
      heta1 hpersistent.le omega transient htransient'
  refine ⟨n, hnB, hnN, ?_⟩
  convert hn using 1
  rw [heta]
  field_simp [hpersistent.ne']
  ring

/-- Quantitative finite-packet form.  A certified geometric burn-in bound
and the closed persistent-packet deadline together force a dissipative
return above the requested target. -/
theorem IsUniversalWeightedFloquetFidelityDeadline.exists_finiteDampedSpectralPacket_return_at_target
    {d s N B : ℕ} {w : Fin d → ℝ}
    {eta persistentMass target q : ℝ}
    (hdeadline : IsUniversalWeightedFloquetFidelityDeadline w eta N)
    (hpersistent : 0 < persistentMass)
    (htarget0 : 0 ≤ target)
    (heta : eta = (persistentMass - target) / (2 * persistentMass))
    (omega : Fin d → ℝ)
    (coefficient eigenvalue : Fin s → ℂ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (heigenvalue : ∀ j, ‖eigenvalue j‖ ≤ q)
    (hburn : q ^ (B + 1) * ∑ j, ‖coefficient j‖ ≤
      (persistentMass - target) / 2) :
    ∃ n : ℕ, B < n ∧ n ≤ (B + 1) * N ∧
      target ≤ ‖dissipativeWeightedReturnAmplitude
        persistentMass w omega
        (finiteDampedTransientAmplitude coefficient eigenvalue) n‖ := by
  apply hdeadline.exists_dissipative_return_at_target
    hpersistent htarget0 heta omega
  intro n hn
  calc
    ‖finiteDampedTransientAmplitude coefficient eigenvalue n‖ ≤
        q ^ n * ∑ j, ‖coefficient j‖ :=
      norm_finiteDampedTransientAmplitude_le_geometric
        coefficient eigenvalue q heigenvalue n
    _ ≤ q ^ (B + 1) * ∑ j, ‖coefficient j‖ := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hq0 hq1
          (Nat.succ_le_iff.mpr hn))
        (Finset.sum_nonneg fun j _hj => norm_nonneg (coefficient j))
    _ ≤ (persistentMass - target) / 2 := hburn

/-- Above the persistent ceiling, every sufficiently late return is
impossible as soon as the transient term tends to zero. -/
theorem eventually_norm_dissipativeWeightedReturnAmplitude_lt_of_ceiling_lt
    {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1) {persistentMass target : ℝ}
    (hpersistent : 0 ≤ persistentMass) (htarget : persistentMass < target)
    (omega : Fin d → ℝ) (transient : ℕ → ℂ)
    (htransient : Tendsto transient atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      ‖dissipativeWeightedReturnAmplitude
        persistentMass w omega transient n‖ < target := by
  have hgap : 0 < target - persistentMass := sub_pos.mpr htarget
  have heventually : ∀ᶠ n in atTop, ‖transient n‖ <
      target - persistentMass := by
    obtain ⟨B, hB⟩ :=
      Metric.tendsto_atTop.1 htransient
        (target - persistentMass) hgap
    filter_upwards [eventually_atTop.2 ⟨B, hB⟩] with n hn
    simpa only [dist_zero_right] using hn
  filter_upwards [heventually] with n hn
  rw [dissipativeWeightedReturnAmplitude]
  calc
    ‖(persistentMass : ℂ) * weightedFloquetReturnAmplitude w omega n +
        transient n‖ ≤
        ‖(persistentMass : ℂ) *
          weightedFloquetReturnAmplitude w omega n‖ + ‖transient n‖ :=
      norm_add_le _ _
    _ ≤ persistentMass + ‖transient n‖ :=
      by
        simpa only [add_comm] using
          add_le_add_right
            (norm_persistentWeightedReturnAmplitude_le
              w hw hmass hpersistent omega n) ‖transient n‖
    _ < target := by linarith

/-- **Exact dissipative return ceiling.**  For every normalized persistent
spectral packet of positive mass and every transient amplitude tending to
zero, the persistent mass is the exact asymptotic return-amplitude ceiling:
all late values lie below every larger threshold, while values arbitrarily
close to the ceiling occur after every prescribed delay. -/
theorem dissipativeWeightedReturnAmplitude_exactAsymptoticCeiling
    {d : ℕ} (hd : 2 ≤ d)
    (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1) {persistentMass : ℝ}
    (hpersistent : 0 < persistentMass)
    (omega : Fin d → ℝ) (transient : ℕ → ℂ)
    (htransient : Tendsto transient atTop (𝓝 0)) :
    IsExactAsymptoticReturnAmplitudeCeiling
      (dissipativeWeightedReturnAmplitude
        persistentMass w omega transient) persistentMass := by
  constructor
  · intro ε hε
    have heventually :=
      eventually_norm_dissipativeWeightedReturnAmplitude_lt_of_ceiling_lt
        w hw hmass hpersistent.le (by linarith : persistentMass <
          persistentMass + ε) omega transient htransient
    exact eventually_atTop.1 heventually
  · intro ε hε M
    by_cases hsmall : persistentMass ≤ ε
    · refine ⟨M + 1, Nat.lt_succ_self M, ?_⟩
      exact le_trans (by linarith : persistentMass - ε ≤ 0)
        (norm_nonneg _)
    · have hεp : ε < persistentMass := lt_of_not_ge hsmall
      let eta : ℝ := ε / (2 * persistentMass)
      have heta0 : 0 < eta := by
        dsimp only [eta]
        positivity
      have heta1 : eta ≤ 1 := by
        dsimp only [eta]
        have hp2 : 0 < 2 * persistentMass := by positivity
        apply (div_le_iff₀ hp2).2
        nlinarith
      let N : ℕ :=
        universalWeightedFloquetFidelityRecurrenceTime
          hd w hw hmass eta heta0 heta1
      have hdeadline : IsUniversalWeightedFloquetFidelityDeadline w eta N :=
        universalWeightedFloquetFidelityRecurrenceTime_isDeadline
          hd w hw hmass eta heta0 heta1
      obtain ⟨B₀, hB₀⟩ :=
        Metric.tendsto_atTop.1 htransient (ε / 2) (by positivity)
      let B : ℕ := max M B₀
      have htransientBound : ∀ n : ℕ, B < n →
          ‖transient n‖ ≤
            (persistentMass - (persistentMass - ε)) / 2 := by
        intro n hn
        have hB₀n : B₀ ≤ n :=
          (Nat.le_max_right M B₀).trans (Nat.le_of_lt hn)
        have hntr := hB₀ n hB₀n
        have hntr' : ‖transient n‖ ≤ ε / 2 := by
          simpa only [dist_zero_right] using hntr.le
        nlinarith
      obtain ⟨n, hnB, _hnN, hnreturn⟩ :=
        hdeadline.exists_dissipative_return_at_target
          hpersistent (by linarith)
          (by
            dsimp only [eta]
            congr 1
            ring)
          omega transient htransientBound
      refine ⟨n, (Nat.le_max_left M B₀).trans_lt hnB, hnreturn⟩

/-- The exact dissipative return ceiling in every finite packet dimension.
The zero-dimensional case is excluded automatically by normalization; the
one-dimensional case has constant persistent norm, and all higher
dimensions use simultaneous phase recurrence. -/
theorem dissipativeWeightedReturnAmplitude_exactAsymptoticCeiling_allDimensions
    {d : ℕ}
    (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1) {persistentMass : ℝ}
    (hpersistent : 0 ≤ persistentMass)
    (omega : Fin d → ℝ) (transient : ℕ → ℂ)
    (htransient : Tendsto transient atTop (𝓝 0)) :
    IsExactAsymptoticReturnAmplitudeCeiling
      (dissipativeWeightedReturnAmplitude
        persistentMass w omega transient) persistentMass := by
  rcases hpersistent.eq_or_lt with rfl | hpersistent
  · constructor
    · intro ε hε
      obtain ⟨B, hB⟩ :=
        Metric.tendsto_atTop.1 htransient ε hε
      refine ⟨B, fun n hn => ?_⟩
      simpa [dissipativeWeightedReturnAmplitude] using hB n hn
    · intro ε hε M
      refine ⟨M + 1, Nat.lt_succ_self M, ?_⟩
      have hnorm := norm_nonneg
        (dissipativeWeightedReturnAmplitude 0 w omega transient (M + 1))
      linarith
  · by_cases hd : 2 ≤ d
    · exact dissipativeWeightedReturnAmplitude_exactAsymptoticCeiling
        hd w hw hmass hpersistent omega transient htransient
    · have hdle : d ≤ 1 := by omega
      have hdne : d ≠ 0 := by
        intro hd0
        subst d
        simpa using hmass
      have hd1 : d = 1 := Nat.le_antisymm hdle (Nat.one_le_iff_ne_zero.mpr hdne)
      subst d
      have hwzero : w 0 = 1 := by simpa using hmass
      have hpersistentNorm (n : ℕ) :
          ‖(persistentMass : ℂ) *
              weightedFloquetReturnAmplitude w omega n‖ =
            persistentMass := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hpersistent]
        have hpacket :
            ‖weightedFloquetReturnAmplitude w omega n‖ = 1 := by
          simp [weightedFloquetReturnAmplitude, hwzero, Complex.norm_exp]
        rw [hpacket, mul_one]
      constructor
      · intro ε hε
        have heventually :=
          eventually_norm_dissipativeWeightedReturnAmplitude_lt_of_ceiling_lt
            w hw hmass hpersistent.le
              (by linarith : persistentMass < persistentMass + ε)
            omega transient htransient
        exact eventually_atTop.1 heventually
      · intro ε hε M
        obtain ⟨B, hB⟩ :=
          Metric.tendsto_atTop.1 htransient ε hε
        let n : ℕ := max B (M + 1)
        have hnB : B ≤ n := Nat.le_max_left _ _
        have hnM : M < n :=
          (Nat.lt_succ_self M).trans_le (Nat.le_max_right _ _)
        have hsmall : ‖transient n‖ < ε := by
          simpa only [dist_zero_right] using hB n hnB
        refine ⟨n, hnM, ?_⟩
        have hreverse :
            ‖(persistentMass : ℂ) *
                weightedFloquetReturnAmplitude w omega n‖ -
                ‖transient n‖ ≤
              ‖dissipativeWeightedReturnAmplitude
                persistentMass w omega transient n‖ := by
          rw [dissipativeWeightedReturnAmplitude]
          simpa only [sub_neg_eq_add, norm_neg] using
            (norm_sub_norm_le
              ((persistentMass : ℂ) *
                weightedFloquetReturnAmplitude w omega n)
              (-transient n))
        rw [hpersistentNorm] at hreverse
        linarith

/-- **Finite damped spectral-packet law.**  Every finite family of modes
strictly inside the unit disk can be appended to an arbitrary normalized
persistent packet without changing its exact asymptotic return ceiling. -/
theorem finiteDampedSpectralPacket_exactAsymptoticCeiling
    {d s : ℕ} (hd : 2 ≤ d)
    (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1) {persistentMass : ℝ}
    (hpersistent : 0 < persistentMass)
    (omega : Fin d → ℝ)
    (coefficient eigenvalue : Fin s → ℂ)
    (heigenvalue : ∀ j, ‖eigenvalue j‖ < 1) :
    IsExactAsymptoticReturnAmplitudeCeiling
      (dissipativeWeightedReturnAmplitude persistentMass w omega
        (finiteDampedTransientAmplitude coefficient eigenvalue))
      persistentMass := by
  exact dissipativeWeightedReturnAmplitude_exactAsymptoticCeiling
    hd w hw hmass hpersistent omega
      (finiteDampedTransientAmplitude coefficient eigenvalue)
      (tendsto_finiteDampedTransientAmplitude_zero
        coefficient eigenvalue heigenvalue)

/-- **Finite Jordan-complete damped spectral-packet law.**  Appending any
finite polynomially damped packet to a normalized persistent phase packet
does not change its exact asymptotic return ceiling. -/
theorem finitePolynomialDampedSpectralPacket_exactAsymptoticCeiling
    {d s degree : ℕ} (hd : 2 ≤ d)
    (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1) {persistentMass : ℝ}
    (hpersistent : 0 < persistentMass)
    (omega : Fin d → ℝ)
    (coefficient : Fin s → Fin degree → ℂ)
    (eigenvalue : Fin s → ℂ)
    (heigenvalue : ∀ j, ‖eigenvalue j‖ < 1) :
    IsExactAsymptoticReturnAmplitudeCeiling
      (dissipativeWeightedReturnAmplitude persistentMass w omega
        (finitePolynomialDampedTransientAmplitude
          coefficient eigenvalue))
      persistentMass := by
  exact dissipativeWeightedReturnAmplitude_exactAsymptoticCeiling
    hd w hw hmass hpersistent omega
      (finitePolynomialDampedTransientAmplitude coefficient eigenvalue)
      (tendsto_finitePolynomialDampedTransientAmplitude_zero
        coefficient eigenvalue heigenvalue)

/-! ## Universal peripheral/transient law for finite contractions -/

/-- Powers of an element of a complete complex normed algebra converge to
zero whenever its spectral radius is strictly below one. -/
theorem tendsto_pow_atTop_nhds_zero_of_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] [NormOneClass A]
    (a : A) (hradius : spectralRadius ℂ a < 1) :
    Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  have hroot :=
    spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  have hroot_lt : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ)) < 1 :=
    hroot.eventually (Iio_mem_nhds hradius)
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_gt_atTop 0
  obtain ⟨N, hNroot, hNpos⟩ :=
    (hroot_lt.and hpositive).exists
  have hNne : N ≠ 0 := Nat.ne_of_gt hNpos
  have hNrootReal : ‖a ^ N‖ ^ (1 / N : ℝ) < 1 :=
    ENNReal.ofReal_lt_one.mp hNroot
  have hNnorm : ‖a ^ N‖ < 1 := by
    rw [Real.rpow_lt_one_iff' (norm_nonneg _) (by positivity)] at hNrootReal
    exact hNrootReal
  let C : ℝ := max 1 (‖a‖ ^ N)
  have hrem (n : ℕ) : ‖a ^ (n % N)‖ ≤ C := by
    calc
      ‖a ^ (n % N)‖ ≤ ‖a‖ ^ (n % N) := norm_pow_le _ _
      _ ≤ C := by
        dsimp only [C]
        by_cases ha : ‖a‖ ≤ 1
        · exact (pow_le_one₀ (norm_nonneg _) ha).trans (le_max_left _ _)
        · exact (pow_le_pow_right₀ (le_of_not_ge ha)
            (Nat.le_of_lt (Nat.mod_lt n hNpos))).trans
              (le_max_right _ _)
  have hbound (n : ℕ) :
      ‖a ^ n‖ ≤ ‖a ^ N‖ ^ (n / N) * C := by
    calc
      ‖a ^ n‖ =
          ‖(a ^ N) ^ (n / N) * a ^ (n % N)‖ := by
        congr 1
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      _ ≤ ‖(a ^ N) ^ (n / N)‖ * ‖a ^ (n % N)‖ :=
        norm_mul_le _ _
      _ ≤ ‖a ^ N‖ ^ (n / N) * C := by
        exact mul_le_mul (norm_pow_le _ _) (hrem n)
          (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg (a ^ n)) hbound ?_
  simpa only [zero_mul] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (norm_nonneg (a ^ N)) hNnorm).comp
        (Nat.tendsto_div_const_atTop hNne)).mul_const C

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Unit-modulus eigenvalues of a finite contraction. -/
abbrev FiniteContractionPeripheralEigenvalue (T : H →L[ℂ] H) :=
  {μ : Module.End.Eigenvalues T.toLinearMap // ‖(μ : ℂ)‖ = 1}

/-- Eigenspace belonging to a bundled peripheral eigenvalue. -/
def finiteContractionPeripheralEigenspace (T : H →L[ℂ] H)
    (μ : FiniteContractionPeripheralEigenvalue T) : Submodule ℂ H :=
  Module.End.eigenspace T.toLinearMap (μ : ℂ)

/-- Span of all unit-modulus eigenspaces. -/
def finiteContractionPeripheralSubspace (T : H →L[ℂ] H) :
    Submodule ℂ H :=
  ⨆ μ : FiniteContractionPeripheralEigenvalue T,
    finiteContractionPeripheralEigenspace T μ

/-- Distinct peripheral eigenspaces of a contraction are orthogonal. -/
theorem finiteContractionPeripheralEigenspaces_orthogonal
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    OrthogonalFamily ℂ
      (fun μ : FiniteContractionPeripheralEigenvalue T =>
        finiteContractionPeripheralEigenspace T μ)
      (fun μ => (finiteContractionPeripheralEigenspace T μ).subtypeₗᵢ) := by
  rintro μ ν hμν ⟨x, hx⟩ ⟨y, hy⟩
  apply HTGeometry.inner_eq_zero_of_distinct_peripheral_eigenvectors T hT
  · exact Module.End.mem_eigenspace_iff.mp hx
  · exact Module.End.mem_eigenspace_iff.mp hy
  · exact μ.property
  · intro h
    apply hμν
    exact Subtype.ext (Subtype.ext h)

/-- The contraction preserves its peripheral span. -/
theorem finiteContractionPeripheralSubspace_invariant
    (T : H →L[ℂ] H) :
    ∀ x ∈ finiteContractionPeripheralSubspace T,
      T x ∈ finiteContractionPeripheralSubspace T := by
  intro x hx
  induction hx using Submodule.iSup_induction' with
  | mem μ x hx =>
      apply Submodule.mem_iSup_of_mem μ
      unfold finiteContractionPeripheralEigenspace at hx ⊢
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      exact (congrArg T hx).trans (map_smul T _ _)
  | zero =>
      simpa using (Submodule.zero_mem
        (finiteContractionPeripheralSubspace T))
  | add x y _ _ hx hy =>
      simpa only [map_add] using Submodule.add_mem _ hx hy

/-- The adjoint preserves the peripheral span. -/
theorem finiteContractionPeripheralSubspace_adjoint_invariant
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∀ x ∈ finiteContractionPeripheralSubspace T,
      T.adjoint x ∈ finiteContractionPeripheralSubspace T := by
  intro x hx
  induction hx using Submodule.iSup_induction' with
  | mem μ x hx =>
      have hadj :=
        HTGeometry.adjoint_eigenvector_of_contraction T hT
          (Module.End.mem_eigenspace_iff.mp hx) μ.property
      apply Submodule.mem_iSup_of_mem μ
      rw [hadj]
      exact Submodule.smul_mem _ _ hx
  | zero =>
      simpa using (Submodule.zero_mem
        (finiteContractionPeripheralSubspace T))
  | add x y _ _ hx hy =>
      simpa only [map_add] using Submodule.add_mem _ hx hy

/-- Orthogonal transient complement of the peripheral span. -/
def finiteContractionTransientSubspace (T : H →L[ℂ] H) :
    Submodule ℂ H :=
  (finiteContractionPeripheralSubspace T)ᗮ

/-- The orthogonal transient complement is invariant under the
contraction. -/
theorem finiteContractionTransientSubspace_invariant
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∀ x ∈ finiteContractionTransientSubspace T,
      T x ∈ finiteContractionTransientSubspace T := by
  intro x hx
  rw [finiteContractionTransientSubspace,
    Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  rw [← T.adjoint_inner_right]
  exact hx _ (finiteContractionPeripheralSubspace_adjoint_invariant
    T hT y hy)

/-- Restriction of a contraction to its transient complement. -/
def finiteContractionTransientRestriction
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    finiteContractionTransientSubspace T →L[ℂ]
      finiteContractionTransientSubspace T :=
  T.restrict (finiteContractionTransientSubspace_invariant T hT)

@[simp]
theorem finiteContractionTransientRestriction_apply_coe
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (x : finiteContractionTransientSubspace T) :
    ((finiteContractionTransientRestriction T hT x :
      finiteContractionTransientSubspace T) : H) = T x := rfl

/-- Every spectral value of the transient restriction lies strictly inside
the unit disk. -/
theorem norm_lt_one_of_mem_spectrum_finiteContractionTransientRestriction
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ
      (finiteContractionTransientRestriction T hT)) :
    ‖μ‖ < 1 := by
  have hμlin : μ ∈ spectrum ℂ
      (finiteContractionTransientRestriction T hT).toLinearMap := by
    rw [← ContinuousLinearMap.spectrum_eq]
    exact hμ
  have heigen : Module.End.HasEigenvalue
      (finiteContractionTransientRestriction T hT).toLinearMap μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμlin
  obtain ⟨x, hxmem, hxne⟩ := heigen.exists_hasEigenvector
  have hxrestrict :
      finiteContractionTransientRestriction T hT x = μ • x :=
    Module.End.mem_eigenspace_iff.mp hxmem
  have hlift : T (x : H) = μ • (x : H) := by
    exact congrArg Subtype.val hxrestrict
  have hxcoe_ne : (x : H) ≠ 0 := by
    intro hx0
    apply hxne
    exact Subtype.ext hx0
  have hxnorm : 0 < ‖(x : H)‖ := norm_pos_iff.mpr hxcoe_ne
  have hμle : ‖μ‖ ≤ 1 := by
    apply le_of_mul_le_mul_right (a := ‖(x : H)‖) _ hxnorm
    calc
      ‖μ‖ * ‖(x : H)‖ = ‖T (x : H)‖ := by
        rw [hlift, norm_smul]
      _ ≤ ‖T‖ * ‖(x : H)‖ := T.le_opNorm _
      _ ≤ 1 * ‖(x : H)‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg _)
  apply lt_of_le_of_ne hμle
  intro hμeq
  have hμT : Module.End.HasEigenvalue T.toLinearMap μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hlift, hxcoe_ne⟩
  let ν : FiniteContractionPeripheralEigenvalue T :=
    ⟨⟨μ, hμT⟩, hμeq⟩
  have hxPeripheral :
      (x : H) ∈ finiteContractionPeripheralSubspace T := by
    apply Submodule.mem_iSup_of_mem ν
    exact Module.End.mem_eigenspace_iff.mpr hlift
  have hxTransient :
      (x : H) ∈ finiteContractionTransientSubspace T := x.property
  have hinner :
      inner ℂ (x : H) (x : H) = 0 := by
    exact (Submodule.mem_orthogonal'
      (finiteContractionPeripheralSubspace T) (x : H)).mp
        hxTransient (x : H) hxPeripheral
  exact hxcoe_ne (inner_self_eq_zero.mp hinner)

/-- The transient restriction has spectral radius strictly below one. -/
theorem spectralRadius_finiteContractionTransientRestriction_lt_one
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    [Nontrivial (finiteContractionTransientSubspace T)] :
    spectralRadius ℂ (finiteContractionTransientRestriction T hT) < 1 := by
  apply spectrum.spectralRadius_lt_of_forall_lt
    (finiteContractionTransientRestriction T hT)
  intro μ hμ
  exact_mod_cast
    norm_lt_one_of_mem_spectrum_finiteContractionTransientRestriction
      T hT hμ

/-- Powers of the transient restriction converge to zero in operator norm. -/
theorem tendsto_pow_finiteContractionTransientRestriction_zero
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    Tendsto
      (fun n : ℕ => (finiteContractionTransientRestriction T hT) ^ n)
      atTop (𝓝 0) := by
  by_cases hnontrivial :
      Nontrivial (finiteContractionTransientSubspace T)
  · letI := hnontrivial
    exact tendsto_pow_atTop_nhds_zero_of_spectralRadius_lt_one
      (finiteContractionTransientRestriction T hT)
      (spectralRadius_finiteContractionTransientRestriction_lt_one T hT)
  · letI : Subsingleton (finiteContractionTransientSubspace T) :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    have hconstant :
        (fun n : ℕ => (finiteContractionTransientRestriction T hT) ^ n) =
          (fun _ : ℕ => (0 :
            finiteContractionTransientSubspace T →L[ℂ]
              finiteContractionTransientSubspace T)) := by
      funext n
      exact Subsingleton.elim _ _
    rw [hconstant]
    exact tendsto_const_nhds

/-- Restriction and taking powers commute after inclusion into the ambient
Hilbert space. -/
@[simp]
theorem finiteContractionTransientRestriction_pow_apply_coe
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (n : ℕ) (x : finiteContractionTransientSubspace T) :
    ((((finiteContractionTransientRestriction T hT) ^ n) x :
      finiteContractionTransientSubspace T) : H) = (T ^ n) (x : H) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change T ((((finiteContractionTransientRestriction T hT) ^ n) x :
        finiteContractionTransientSubspace T) : H) = T ((T ^ n) (x : H))
      rw [ih]

/-- Every transient vector is driven to zero by repeated application of the
finite contraction. -/
theorem tendsto_finiteContraction_pow_apply_transient_zero
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (x : finiteContractionTransientSubspace T) :
    Tendsto (fun n : ℕ => (T ^ n) (x : H)) atTop (𝓝 0) := by
  have hrestricted :
      Tendsto
        (fun n : ℕ =>
          ((finiteContractionTransientRestriction T hT) ^ n) x)
        atTop (𝓝 0) :=
    (ContinuousLinearMap.apply ℂ
      (finiteContractionTransientSubspace T) x).continuous.tendsto 0
      |>.comp (tendsto_pow_finiteContractionTransientRestriction_zero T hT)
  have hinclusion :
      Tendsto
        (fun n : ℕ =>
          (finiteContractionTransientSubspace T).subtypeL
            (((finiteContractionTransientRestriction T hT) ^ n) x))
        atTop
        (𝓝 ((finiteContractionTransientSubspace T).subtypeL 0)) :=
    ((finiteContractionTransientSubspace T).subtypeL.continuous.tendsto 0).comp
      hrestricted
  refine hinclusion.congr' ?_
  filter_upwards with n
  exact finiteContractionTransientRestriction_pow_apply_coe T hT n x

/-! ## State-dependent persistent mass and exact spectral packet -/

/-- Projection of a state onto one peripheral eigenspace. -/
def finiteContractionPeripheralComponent (T : H →L[ℂ] H)
    (x : H) (μ : FiniteContractionPeripheralEigenvalue T) : H :=
  (finiteContractionPeripheralEigenspace T μ).starProjection x

/-- State-dependent mass surviving forever under a finite contraction. -/
def finiteContractionPersistentMass (T : H →L[ℂ] H) (x : H) : ℝ :=
  ∑ μ : FiniteContractionPeripheralEigenvalue T,
    ‖finiteContractionPeripheralComponent T x μ‖ ^ 2

/-- Orthogonal transient component of an initial vector. -/
def finiteContractionTransientComponent (T : H →L[ℂ] H) (x : H) :
    finiteContractionTransientSubspace T :=
  ⟨x - (finiteContractionPeripheralSubspace T).starProjection x,
    Submodule.sub_starProjection_mem_orthogonal x⟩

/-- Peripheral components sum to the orthogonal projection onto the full
peripheral subspace. -/
theorem sum_finiteContractionPeripheralComponent
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    (∑ μ : FiniteContractionPeripheralEigenvalue T,
      finiteContractionPeripheralComponent T x μ) =
      (finiteContractionPeripheralSubspace T).starProjection x := by
  let P := finiteContractionPeripheralSubspace T
  let y := P.starProjection x
  have hy : y ∈ P := by
    change P.starProjection x ∈ P
    exact (P.orthogonalProjection x).property
  have hsum :=
    (finiteContractionPeripheralEigenspaces_orthogonal T hT)
      |>.sum_projection_of_mem_iSup y hy
  change (∑ μ,
      (finiteContractionPeripheralEigenspace T μ).starProjection x) = y
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro μ _hμ
  change (finiteContractionPeripheralEigenspace T μ).starProjection x =
    (finiteContractionPeripheralEigenspace T μ).starProjection
      (P.starProjection x)
  rw [Submodule.starProjection_apply, Submodule.starProjection_apply]
  congr 1
  exact (Submodule.orthogonalProjectionOnto_starProjection_of_le
    (show finiteContractionPeripheralEigenspace T μ ≤ P from
      le_iSup (fun ν : FiniteContractionPeripheralEigenvalue T =>
        finiteContractionPeripheralEigenspace T ν) μ) x).symm

/-- Each peripheral component is an eigenvector, allowing the zero
component. -/
theorem finiteContractionPeripheralComponent_eigen
    (T : H →L[ℂ] H) (x : H)
    (μ : FiniteContractionPeripheralEigenvalue T) :
    T (finiteContractionPeripheralComponent T x μ) =
      (μ : ℂ) • finiteContractionPeripheralComponent T x μ := by
  apply Module.End.mem_eigenspace_iff.mp
  change (finiteContractionPeripheralEigenspace T μ).starProjection x ∈
    finiteContractionPeripheralEigenspace T μ
  exact ((finiteContractionPeripheralEigenspace T μ).orthogonalProjection x).property

/-- Exact evolution of each peripheral component. -/
theorem finiteContraction_pow_apply_peripheralComponent
    (T : H →L[ℂ] H) (x : H)
    (μ : FiniteContractionPeripheralEigenvalue T) (n : ℕ) :
    (T ^ n) (finiteContractionPeripheralComponent T x μ) =
      ((μ : ℂ) ^ n) •
        finiteContractionPeripheralComponent T x μ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change T ((T ^ n)
        (finiteContractionPeripheralComponent T x μ)) = _
      rw [ih, map_smul,
        finiteContractionPeripheralComponent_eigen]
      rw [pow_succ, mul_smul]

/-- A peripheral component's overlap with the initial vector is its
nonnegative squared norm. -/
theorem inner_finiteContractionPeripheralComponent
    (T : H →L[ℂ] H) (x : H)
    (μ : FiniteContractionPeripheralEigenvalue T) :
    inner ℂ x (finiteContractionPeripheralComponent T x μ) =
      (‖finiteContractionPeripheralComponent T x μ‖ ^ 2 : ℝ) := by
  let E := finiteContractionPeripheralEigenspace T μ
  have hproj :=
    E.inner_orthogonalProjection_eq_of_mem_right
      (E.orthogonalProjection x) x
  change inner ℂ x (E.starProjection x) =
    (‖E.starProjection x‖ ^ 2 : ℝ)
  rw [show E.starProjection x = (E.orthogonalProjection x : H) by rfl]
  rw [← hproj]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Unit-modulus peripheral eigenvalues admit real phase coordinates
compatible with every natural power. -/
theorem finiteContractionPeripheralEigenvalue_pow_eq_exp_arg
    (T : H →L[ℂ] H)
    (μ : FiniteContractionPeripheralEigenvalue T) (n : ℕ) :
    ((μ : ℂ) ^ n) =
      Complex.exp
        (Complex.I *
          ((((n : ℝ) * Complex.arg (μ : ℂ) : ℝ) : ℂ))) := by
  have hpolar : Complex.exp (Complex.arg (μ : ℂ) * Complex.I) =
      (μ : ℂ) := by
    have h := Complex.norm_mul_exp_arg_mul_I (μ : ℂ)
    simpa [μ.property] using h
  calc
    ((μ : ℂ) ^ n) =
        Complex.exp (Complex.arg (μ : ℂ) * Complex.I) ^ n :=
      congrArg (· ^ n) hpolar.symm
    _ = Complex.exp
        ((n : ℂ) * (Complex.arg (μ : ℂ) * Complex.I)) :=
      (Complex.exp_nat_mul _ n).symm
    _ = Complex.exp
        (Complex.I *
          ((((n : ℝ) * Complex.arg (μ : ℂ) : ℝ) : ℂ))) := by
      congr 1
      push_cast
      ring

/-- Transient contribution to the autocorrelation of a finite contraction. -/
def finiteContractionTransientReturnAmplitude
    (T : H →L[ℂ] H) (x : H) (n : ℕ) : ℂ :=
  inner ℂ x ((T ^ n) (finiteContractionTransientComponent T x : H))

/-- The transient autocorrelation tends to zero. -/
theorem tendsto_finiteContractionTransientReturnAmplitude_zero
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    Tendsto (finiteContractionTransientReturnAmplitude T x)
      atTop (𝓝 0) := by
  have hxconstant :
      Tendsto (fun _ : ℕ => x) atTop (𝓝 x) :=
    tendsto_const_nhds
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ) hxconstant
    (tendsto_finiteContraction_pow_apply_transient_zero T hT
      (finiteContractionTransientComponent T x))
  simpa only [finiteContractionTransientReturnAmplitude, inner_zero_right]
    using hinner

/-- Exact persistent-plus-transient spectral decomposition of every
state autocorrelation under every finite contraction. -/
theorem finiteContraction_returnAmplitude_eq_persistent_sum_add_transient
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) (n : ℕ) :
    inner ℂ x ((T ^ n) x) =
      (∑ μ : FiniteContractionPeripheralEigenvalue T,
        ((‖finiteContractionPeripheralComponent T x μ‖ ^ 2 : ℝ) : ℂ) *
          ((μ : ℂ) ^ n)) +
        finiteContractionTransientReturnAmplitude T x n := by
  have hx :
      x =
        (∑ μ : FiniteContractionPeripheralEigenvalue T,
          finiteContractionPeripheralComponent T x μ) +
          (finiteContractionTransientComponent T x : H) := by
    rw [sum_finiteContractionPeripheralComponent T hT x]
    change x =
      (finiteContractionPeripheralSubspace T).starProjection x +
        (x - (finiteContractionPeripheralSubspace T).starProjection x)
    abel
  calc
    inner ℂ x ((T ^ n) x) =
        inner ℂ x ((T ^ n)
          ((∑ μ : FiniteContractionPeripheralEigenvalue T,
            finiteContractionPeripheralComponent T x μ) +
            (finiteContractionTransientComponent T x : H))) := by
      rw [← hx]
    _ = inner ℂ x
          (∑ μ : FiniteContractionPeripheralEigenvalue T,
            (T ^ n) (finiteContractionPeripheralComponent T x μ)) +
        finiteContractionTransientReturnAmplitude T x n := by
      simp only [map_add, map_sum, inner_add_right, inner_sum,
        finiteContractionTransientReturnAmplitude]
    _ = (∑ μ : FiniteContractionPeripheralEigenvalue T,
          ((‖finiteContractionPeripheralComponent T x μ‖ ^ 2 : ℝ) : ℂ) *
            ((μ : ℂ) ^ n)) +
        finiteContractionTransientReturnAmplitude T x n := by
      rw [inner_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro μ _hμ
      rw [finiteContraction_pow_apply_peripheralComponent,
        inner_smul_right,
        inner_finiteContractionPeripheralComponent]
      ring

/-- The persistent mass equals the squared norm of the full peripheral
projection. -/
theorem finiteContractionPersistentMass_eq_norm_sq_projection
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    finiteContractionPersistentMass T x =
      ‖(finiteContractionPeripheralSubspace T).starProjection x‖ ^ 2 := by
  have hnorm :=
    (finiteContractionPeripheralEigenspaces_orthogonal T hT).norm_sum
      (fun μ : FiniteContractionPeripheralEigenvalue T =>
        (finiteContractionPeripheralEigenspace T μ).orthogonalProjection x)
      Finset.univ
  have hsum :
      (∑ μ : FiniteContractionPeripheralEigenvalue T,
        (finiteContractionPeripheralEigenspace T μ).subtypeₗᵢ
          ((finiteContractionPeripheralEigenspace T μ).orthogonalProjection x)) =
        (finiteContractionPeripheralSubspace T).starProjection x := by
    change
      (∑ μ : FiniteContractionPeripheralEigenvalue T,
        (finiteContractionPeripheralEigenspace T μ).starProjection x) =
          (finiteContractionPeripheralSubspace T).starProjection x
    exact sum_finiteContractionPeripheralComponent T hT x
  rw [hsum] at hnorm
  simpa [finiteContractionPersistentMass] using hnorm.symm

/-- The surviving mass cannot exceed the squared norm of the initial
vector. -/
theorem finiteContractionPersistentMass_le_norm_sq
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    finiteContractionPersistentMass T x ≤ ‖x‖ ^ 2 := by
  rw [finiteContractionPersistentMass_eq_norm_sq_projection T hT x]
  have hprojection :=
    (finiteContractionPeripheralSubspace T).norm_starProjection_apply_le x
  nlinarith [norm_nonneg
    ((finiteContractionPeripheralSubspace T).starProjection x),
    norm_nonneg x]

/-- Persistent mass is nonnegative. -/
theorem finiteContractionPersistentMass_nonneg
    (T : H →L[ℂ] H) (x : H) :
    0 ≤ finiteContractionPersistentMass T x :=
  Finset.sum_nonneg fun μ _hμ => sq_nonneg
    ‖finiteContractionPeripheralComponent T x μ‖

/-- Canonical enumeration of the finite peripheral spectrum. -/
def finiteContractionPeripheralAt
    (T : H →L[ℂ] H)
    (i : Fin (Fintype.card (FiniteContractionPeripheralEigenvalue T))) :
    FiniteContractionPeripheralEigenvalue T :=
  (Fintype.equivFin (FiniteContractionPeripheralEigenvalue T)).symm i

/-- Raw persistent spectral weight in the canonical finite enumeration. -/
def finiteContractionPeripheralRawWeight
    (T : H →L[ℂ] H) (x : H)
    (i : Fin (Fintype.card (FiniteContractionPeripheralEigenvalue T))) : ℝ :=
  ‖finiteContractionPeripheralComponent T x
    (finiteContractionPeripheralAt T i)‖ ^ 2

/-- Real phase of each canonically enumerated peripheral eigenvalue. -/
def finiteContractionPeripheralPhase
    (T : H →L[ℂ] H)
    (i : Fin (Fintype.card (FiniteContractionPeripheralEigenvalue T))) : ℝ :=
  Complex.arg (finiteContractionPeripheralAt T i : ℂ)

/-- Normalized persistent spectral weights, defined when persistent mass is
positive. -/
def finiteContractionPeripheralWeight
    (T : H →L[ℂ] H) (x : H)
    (i : Fin (Fintype.card (FiniteContractionPeripheralEigenvalue T))) : ℝ :=
  finiteContractionPeripheralRawWeight T x i /
    finiteContractionPersistentMass T x

/-- Canonical enumeration preserves total persistent mass. -/
theorem sum_finiteContractionPeripheralRawWeight
    (T : H →L[ℂ] H) (x : H) :
    ∑ i, finiteContractionPeripheralRawWeight T x i =
      finiteContractionPersistentMass T x := by
  exact Equiv.sum_comp
    (Fintype.equivFin (FiniteContractionPeripheralEigenvalue T)).symm
    (fun μ : FiniteContractionPeripheralEigenvalue T =>
      ‖finiteContractionPeripheralComponent T x μ‖ ^ 2)

/-- Canonical normalized weights are nonnegative. -/
theorem finiteContractionPeripheralWeight_nonneg
    (T : H →L[ℂ] H) (x : H)
    (hpersistent : 0 < finiteContractionPersistentMass T x) :
    ∀ i, 0 ≤ finiteContractionPeripheralWeight T x i := by
  intro i
  exact div_nonneg (sq_nonneg _) hpersistent.le

/-- Canonical normalized weights have total mass one. -/
theorem sum_finiteContractionPeripheralWeight
    (T : H →L[ℂ] H) (x : H)
    (hpersistent : 0 < finiteContractionPersistentMass T x) :
    ∑ i, finiteContractionPeripheralWeight T x i = 1 := by
  change (∑ i, finiteContractionPeripheralRawWeight T x i /
    finiteContractionPersistentMass T x) = 1
  rw [← Finset.sum_div,
    sum_finiteContractionPeripheralRawWeight]
  exact div_self hpersistent.ne'

/-- The canonical normalized Floquet packet is exactly the persistent
autocorrelation of the finite contraction. -/
theorem finiteContraction_persistentSum_eq_scaledWeightedFloquet
    (T : H →L[ℂ] H) (x : H)
    (hpersistent : 0 < finiteContractionPersistentMass T x)
    (n : ℕ) :
    (∑ μ : FiniteContractionPeripheralEigenvalue T,
      ((‖finiteContractionPeripheralComponent T x μ‖ ^ 2 : ℝ) : ℂ) *
        ((μ : ℂ) ^ n)) =
      (finiteContractionPersistentMass T x : ℂ) *
        weightedFloquetReturnAmplitude
          (finiteContractionPeripheralWeight T x)
          (finiteContractionPeripheralPhase T) n := by
  let e :=
    (Fintype.equivFin
      (FiniteContractionPeripheralEigenvalue T)).symm
  rw [weightedFloquetReturnAmplitude, Finset.mul_sum]
  rw [show
      (∑ μ : FiniteContractionPeripheralEigenvalue T,
        ((‖finiteContractionPeripheralComponent T x μ‖ ^ 2 : ℝ) : ℂ) *
          ((μ : ℂ) ^ n)) =
        ∑ i,
          ((‖finiteContractionPeripheralComponent T x (e i)‖ ^ 2 : ℝ) : ℂ) *
            (((e i : FiniteContractionPeripheralEigenvalue T) : ℂ) ^ n) by
      exact (Equiv.sum_comp e
        (fun μ : FiniteContractionPeripheralEigenvalue T =>
          ((‖finiteContractionPeripheralComponent T x μ‖ ^ 2 : ℝ) : ℂ) *
            ((μ : ℂ) ^ n))).symm]
  apply Finset.sum_congr rfl
  intro i _hi
  have hcoeffReal :
      finiteContractionPersistentMass T x *
          finiteContractionPeripheralWeight T x i =
        finiteContractionPeripheralRawWeight T x i := by
    rw [finiteContractionPeripheralWeight]
    field_simp [hpersistent.ne']
  have hcoeff :
      (finiteContractionPersistentMass T x : ℂ) *
          (finiteContractionPeripheralWeight T x i : ℂ) =
        (finiteContractionPeripheralRawWeight T x i : ℂ) := by
    exact_mod_cast hcoeffReal
  change
    ((‖finiteContractionPeripheralComponent T x
        (finiteContractionPeripheralAt T i)‖ ^ 2 : ℝ) : ℂ) *
          ((finiteContractionPeripheralAt T i : ℂ) ^ n) =
      (finiteContractionPersistentMass T x : ℂ) *
        (((finiteContractionPeripheralWeight T x i : ℝ) : ℂ) *
          Complex.exp
            (Complex.I *
              ((((n : ℝ) *
                Complex.arg
                  (finiteContractionPeripheralAt T i : ℂ) : ℝ) : ℂ))))
  rw [← finiteContractionPeripheralEigenvalue_pow_eq_exp_arg T
    (finiteContractionPeripheralAt T i) n]
  rw [← mul_assoc, hcoeff]
  rfl

/-- Exact reduction of every positive-persistent-mass contraction
autocorrelation to a dissipative weighted phase packet. -/
theorem finiteContraction_returnAmplitude_eq_dissipativeWeighted
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H)
    (hpersistent : 0 < finiteContractionPersistentMass T x)
    (n : ℕ) :
    inner ℂ x ((T ^ n) x) =
      dissipativeWeightedReturnAmplitude
        (finiteContractionPersistentMass T x)
        (finiteContractionPeripheralWeight T x)
        (finiteContractionPeripheralPhase T)
        (finiteContractionTransientReturnAmplitude T x) n := by
  rw [finiteContraction_returnAmplitude_eq_persistent_sum_add_transient
    T hT x n]
  rw [finiteContraction_persistentSum_eq_scaledWeightedFloquet
    T x hpersistent n]
  rfl

/-- Any amplitude tending to zero has exact asymptotic return ceiling
zero. -/
theorem exactAsymptoticReturnAmplitudeCeiling_zero_of_tendsto_zero
    (amplitude : ℕ → ℂ)
    (hamplitude : Tendsto amplitude atTop (𝓝 0)) :
    IsExactAsymptoticReturnAmplitudeCeiling amplitude 0 := by
  constructor
  · intro ε hε
    obtain ⟨B, hB⟩ :=
      Metric.tendsto_atTop.1 hamplitude ε hε
    refine ⟨B, fun n hn => ?_⟩
    simpa only [zero_add, dist_zero_right] using hB n hn
  · intro ε hε M
    refine ⟨M + 1, Nat.lt_succ_self M, ?_⟩
    have hnorm := norm_nonneg (amplitude (M + 1))
    linarith

/-- **Universal finite-contraction return transition.**  For every
finite-dimensional complex Hilbert space, every contraction, and every
initial vector, the squared norm of its peripheral projection is the exact
asymptotic ceiling of the return amplitude.  Values arbitrarily close to
that ceiling occur after every delay; every larger threshold is eventually
impossible. -/
theorem finiteContraction_returnAmplitude_exactAsymptoticCeiling
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    IsExactAsymptoticReturnAmplitudeCeiling
      (fun n : ℕ => inner ℂ x ((T ^ n) x))
      (finiteContractionPersistentMass T x) := by
  by_cases hpersistent :
      finiteContractionPersistentMass T x = 0
  · have hprojectionNorm :
        ‖(finiteContractionPeripheralSubspace T).starProjection x‖ ^ 2 =
          0 := by
      rw [← finiteContractionPersistentMass_eq_norm_sq_projection T hT x]
      exact hpersistent
    have hprojection :
        (finiteContractionPeripheralSubspace T).starProjection x = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg
        ((finiteContractionPeripheralSubspace T).starProjection x)]
    have htransientComponent :
        (finiteContractionTransientComponent T x : H) = x := by
      change x -
        (finiteContractionPeripheralSubspace T).starProjection x = x
      rw [hprojection, sub_zero]
    have hamplitude :
        Tendsto (fun n : ℕ => inner ℂ x ((T ^ n) x))
          atTop (𝓝 0) := by
      have htransient :=
        tendsto_finiteContractionTransientReturnAmplitude_zero T hT x
      refine htransient.congr' ?_
      filter_upwards with n
      rw [finiteContractionTransientReturnAmplitude,
        htransientComponent]
    rw [hpersistent]
    exact exactAsymptoticReturnAmplitudeCeiling_zero_of_tendsto_zero
      _ hamplitude
  · have hpersistentPos :
        0 < finiteContractionPersistentMass T x :=
      lt_of_le_of_ne
        (finiteContractionPersistentMass_nonneg T x)
        (Ne.symm hpersistent)
    have hpacket :=
      dissipativeWeightedReturnAmplitude_exactAsymptoticCeiling_allDimensions
        (finiteContractionPeripheralWeight T x)
        (finiteContractionPeripheralWeight_nonneg T x hpersistentPos)
        (sum_finiteContractionPeripheralWeight T x hpersistentPos)
        hpersistentPos.le
        (finiteContractionPeripheralPhase T)
        (finiteContractionTransientReturnAmplitude T x)
        (tendsto_finiteContractionTransientReturnAmplitude_zero T hT x)
    have hamplitude :
        (fun n : ℕ => inner ℂ x ((T ^ n) x)) =
          dissipativeWeightedReturnAmplitude
            (finiteContractionPersistentMass T x)
            (finiteContractionPeripheralWeight T x)
            (finiteContractionPeripheralPhase T)
            (finiteContractionTransientReturnAmplitude T x) := by
      funext n
      exact finiteContraction_returnAmplitude_eq_dissipativeWeighted
        T hT x hpersistentPos n
    rw [hamplitude]
    exact hpacket

/--
**Sharp return-threshold dichotomy.**  The persistent mass separates
recurrently attainable late return amplitudes from eventually impossible
ones.  Every lower threshold is reached after every delay; every higher
threshold is excluded after a finite time.
-/
theorem finiteContraction_returnThreshold_dichotomy
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    (∀ target : ℝ, target < finiteContractionPersistentMass T x →
      ∀ M : ℕ, ∃ n : ℕ, M < n ∧
        target ≤ ‖inner ℂ x ((T ^ n) x)‖) ∧
    (∀ target : ℝ, finiteContractionPersistentMass T x < target →
      ∃ B : ℕ, ∀ n : ℕ, B ≤ n →
        ‖inner ℂ x ((T ^ n) x)‖ < target) := by
  have hceiling :=
    finiteContraction_returnAmplitude_exactAsymptoticCeiling T hT x
  constructor
  · intro target htarget M
    let ε := finiteContractionPersistentMass T x - target
    have hε : 0 < ε := sub_pos.mpr htarget
    obtain ⟨n, hnM, hnreturn⟩ := hceiling.2 ε hε M
    refine ⟨n, hnM, ?_⟩
    simpa only [ε, sub_sub_cancel] using hnreturn
  · intro target htarget
    let ε := target - finiteContractionPersistentMass T x
    have hε : 0 < ε := sub_pos.mpr htarget
    obtain ⟨B, hB⟩ := hceiling.1 ε hε
    refine ⟨B, fun n hn ↦ ?_⟩
    have hnreturn := hB n hn
    dsimp only [ε] at hnreturn
    linarith

/-- The persistent mass squared is the exact asymptotic ceiling of squared
return amplitude. -/
theorem finiteContraction_returnFidelity_exactAsymptoticCeiling
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    IsExactAsymptoticReturnFidelityCeiling
      (fun n : ℕ => inner ℂ x ((T ^ n) x))
      ((finiteContractionPersistentMass T x) ^ 2) :=
  (finiteContraction_returnAmplitude_exactAsymptoticCeiling T hT x).fidelity
    (finiteContractionPersistentMass_nonneg T x)

/-- **Coupled ceiling--deadline law for every finite contraction.**
Every nonnegative target strictly below the persistent ceiling is attained
again after a finite transient burn-in.  The post-burn-in waiting time is
controlled by a universal deadline depending only on the normalized
surviving spectral weights and the target resolution. -/
theorem finiteContraction_exists_return_at_target_before_deadline
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H)
    (hpersistent : 0 < finiteContractionPersistentMass T x)
    (target : ℝ) (htarget0 : 0 ≤ target)
    (htarget : target < finiteContractionPersistentMass T x) :
    ∃ B N : ℕ,
      IsUniversalWeightedFloquetFidelityDeadline
        (finiteContractionPeripheralWeight T x)
        ((finiteContractionPersistentMass T x - target) /
          (2 * finiteContractionPersistentMass T x)) N ∧
      ∃ n : ℕ, B < n ∧ n ≤ (B + 1) * N ∧
        target ≤ ‖inner ℂ x ((T ^ n) x)‖ := by
  let eta : ℝ :=
    (finiteContractionPersistentMass T x - target) /
      (2 * finiteContractionPersistentMass T x)
  have heta0 : 0 < eta := by
    dsimp only [eta]
    positivity
  have heta1 : eta ≤ 1 := by
    dsimp only [eta]
    have hdenom :
        0 < 2 * finiteContractionPersistentMass T x := by positivity
    apply (div_le_iff₀ hdenom).2
    nlinarith
  obtain ⟨N, hdeadline⟩ :=
    exists_universalWeightedFloquetFidelityDeadline_allDimensions
      (finiteContractionPeripheralWeight T x)
      (finiteContractionPeripheralWeight_nonneg T x hpersistent)
      (sum_finiteContractionPeripheralWeight T x hpersistent)
      eta heta0 heta1
  have hgap :
      0 < (finiteContractionPersistentMass T x - target) / 2 := by
    positivity
  obtain ⟨B, hB⟩ :=
    Metric.tendsto_atTop.1
      (tendsto_finiteContractionTransientReturnAmplitude_zero T hT x)
      ((finiteContractionPersistentMass T x - target) / 2) hgap
  have htransient : ∀ n : ℕ, B < n →
      ‖finiteContractionTransientReturnAmplitude T x n‖ ≤
        (finiteContractionPersistentMass T x - target) / 2 := by
    intro n hn
    have hn' := hB n (Nat.le_of_lt hn)
    simpa only [dist_zero_right] using hn'.le
  obtain ⟨n, hnB, hnN, hnreturn⟩ :=
    hdeadline.exists_dissipative_return_at_target
      hpersistent htarget0 rfl
      (finiteContractionPeripheralPhase T)
      (finiteContractionTransientReturnAmplitude T x)
      htransient
  refine ⟨B, N, ?_, n, hnB, hnN, ?_⟩
  · simpa only [eta] using hdeadline
  · rw [finiteContraction_returnAmplitude_eq_dissipativeWeighted
      T hT x hpersistent n]
    exact hnreturn

/--
When the peripheral packet has at least two coordinates, the coupled
contraction return can use the least universal weighted Floquet deadline
itself.  Its logarithm is therefore governed by the existing reverse-water
entropy sandwich.
-/
theorem finiteContraction_exists_return_at_target_before_waterDeadline
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H)
    (hpersistent : 0 < finiteContractionPersistentMass T x)
    (hperipheral :
      2 ≤ Fintype.card (FiniteContractionPeripheralEigenvalue T))
    (target : ℝ) (htarget0 : 0 ≤ target)
    (htarget : target < finiteContractionPersistentMass T x) :
    let eta :=
      (finiteContractionPersistentMass T x - target) /
        (2 * finiteContractionPersistentMass T x)
    ∃ (heta0 : 0 < eta) (heta1 : eta ≤ 1) (B n : ℕ),
      B < n ∧
      n ≤ (B + 1) *
        universalWeightedFloquetFidelityRecurrenceTime
          hperipheral
          (finiteContractionPeripheralWeight T x)
          (finiteContractionPeripheralWeight_nonneg T x hpersistent)
          (sum_finiteContractionPeripheralWeight T x hpersistent)
          eta heta0 heta1 ∧
      target ≤ ‖inner ℂ x ((T ^ n) x)‖ := by
  dsimp only
  let eta :=
    (finiteContractionPersistentMass T x - target) /
      (2 * finiteContractionPersistentMass T x)
  have heta0 : 0 < eta := by
    dsimp only [eta]
    positivity
  have heta1 : eta ≤ 1 := by
    dsimp only [eta]
    have hdenom :
        0 < 2 * finiteContractionPersistentMass T x := by positivity
    apply (div_le_iff₀ hdenom).2
    nlinarith
  let N :=
    universalWeightedFloquetFidelityRecurrenceTime
      hperipheral
      (finiteContractionPeripheralWeight T x)
      (finiteContractionPeripheralWeight_nonneg T x hpersistent)
      (sum_finiteContractionPeripheralWeight T x hpersistent)
      eta heta0 heta1
  have hdeadline :
      IsUniversalWeightedFloquetFidelityDeadline
        (finiteContractionPeripheralWeight T x) eta N := by
    dsimp only [N]
    exact universalWeightedFloquetFidelityRecurrenceTime_isDeadline
      hperipheral
      (finiteContractionPeripheralWeight T x)
      (finiteContractionPeripheralWeight_nonneg T x hpersistent)
      (sum_finiteContractionPeripheralWeight T x hpersistent)
      eta heta0 heta1
  have hgap :
      0 < (finiteContractionPersistentMass T x - target) / 2 := by
    positivity
  obtain ⟨B, hB⟩ :=
    Metric.tendsto_atTop.1
      (tendsto_finiteContractionTransientReturnAmplitude_zero T hT x)
      ((finiteContractionPersistentMass T x - target) / 2) hgap
  have htransient : ∀ n : ℕ, B < n →
      ‖finiteContractionTransientReturnAmplitude T x n‖ ≤
        (finiteContractionPersistentMass T x - target) / 2 := by
    intro n hn
    have hn' := hB n (Nat.le_of_lt hn)
    simpa only [dist_zero_right] using hn'.le
  obtain ⟨n, hnB, hnN, hnreturn⟩ :=
    hdeadline.exists_dissipative_return_at_target
      hpersistent htarget0 rfl
      (finiteContractionPeripheralPhase T)
      (finiteContractionTransientReturnAmplitude T x)
      htransient
  refine ⟨heta0, heta1, B, n, hnB, ?_, ?_⟩
  · simpa only [N] using hnN
  · rw [finiteContraction_returnAmplitude_eq_dissipativeWeighted
      T hT x hpersistent n]
    exact hnreturn

/-! ## Open and randomized evolutions -/

/-- Finite statistical mixture of linear evolutions. -/
def finiteMixedEvolution {m : ℕ}
    (probability : Fin m → ℝ)
    (evolution : Fin m → H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i, (probability i : ℂ) • evolution i

/-- A convex mixture of arbitrary contractions is again a contraction.
This includes random-unitary channels as the isometric special case. -/
theorem norm_finiteMixedEvolution_le_one
    {m : ℕ} (probability : Fin m → ℝ)
    (hprobability : ∀ i, 0 ≤ probability i)
    (hmass : ∑ i, probability i = 1)
    (evolution : Fin m → H →L[ℂ] H)
    (hevolution : ∀ i, ‖evolution i‖ ≤ 1) :
    ‖finiteMixedEvolution probability evolution‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [finiteMixedEvolution, _root_.sum_apply]
  calc
    ‖∑ i, ((probability i : ℂ) • evolution i) x‖ ≤
        ∑ i, ‖((probability i : ℂ) • evolution i) x‖ :=
      norm_sum_le _ _
    _ = ∑ i, probability i * ‖evolution i x‖ := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [_root_.smul_apply, norm_smul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hprobability i)]
    _ ≤ ∑ i, probability i * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      apply mul_le_mul_of_nonneg_left _ (hprobability i)
      calc
        ‖evolution i x‖ ≤ ‖evolution i‖ * ‖x‖ :=
          (evolution i).le_opNorm x
        _ ≤ 1 * ‖x‖ :=
          mul_le_mul_of_nonneg_right (hevolution i) (norm_nonneg x)
        _ = ‖x‖ := one_mul _
    _ = 1 * ‖x‖ := by
      rw [← Finset.sum_mul, hmass]

/-- **Universal open-mixture return transition.**  Every finite
statistical mixture of arbitrary contractive evolutions obeys the same exact
state-dependent return ceiling law. -/
theorem finiteMixedEvolution_returnAmplitude_exactAsymptoticCeiling
    {m : ℕ} (probability : Fin m → ℝ)
    (hprobability : ∀ i, 0 ≤ probability i)
    (hmass : ∑ i, probability i = 1)
    (evolution : Fin m → H →L[ℂ] H)
    (hevolution : ∀ i, ‖evolution i‖ ≤ 1)
    (x : H) :
    IsExactAsymptoticReturnAmplitudeCeiling
      (fun n : ℕ =>
        inner ℂ x
          (((finiteMixedEvolution probability evolution) ^ n) x))
      (finiteContractionPersistentMass
        (finiteMixedEvolution probability evolution) x) :=
  finiteContraction_returnAmplitude_exactAsymptoticCeiling
    (finiteMixedEvolution probability evolution)
    (norm_finiteMixedEvolution_le_one probability hprobability hmass
      evolution hevolution)
    x

/-- Exact squared-return ceiling for every finite statistical mixture of
contractive evolutions. -/
theorem finiteMixedEvolution_returnFidelity_exactAsymptoticCeiling
    {m : ℕ} (probability : Fin m → ℝ)
    (hprobability : ∀ i, 0 ≤ probability i)
    (hmass : ∑ i, probability i = 1)
    (evolution : Fin m → H →L[ℂ] H)
    (hevolution : ∀ i, ‖evolution i‖ ≤ 1)
    (x : H) :
    IsExactAsymptoticReturnFidelityCeiling
      (fun n : ℕ =>
        inner ℂ x
          (((finiteMixedEvolution probability evolution) ^ n) x))
      ((finiteContractionPersistentMass
        (finiteMixedEvolution probability evolution) x) ^ 2) :=
  finiteContraction_returnFidelity_exactAsymptoticCeiling
    (finiteMixedEvolution probability evolution)
    (norm_finiteMixedEvolution_le_one probability hprobability hmass
      evolution hevolution)
    x

/-- Coupled ceiling--deadline law for every finite statistical mixture of
contractive evolutions. -/
theorem finiteMixedEvolution_exists_return_at_target_before_deadline
    {m : ℕ} (probability : Fin m → ℝ)
    (hprobability : ∀ i, 0 ≤ probability i)
    (hmass : ∑ i, probability i = 1)
    (evolution : Fin m → H →L[ℂ] H)
    (hevolution : ∀ i, ‖evolution i‖ ≤ 1)
    (x : H)
    (hpersistent : 0 < finiteContractionPersistentMass
      (finiteMixedEvolution probability evolution) x)
    (target : ℝ) (htarget0 : 0 ≤ target)
    (htarget : target < finiteContractionPersistentMass
      (finiteMixedEvolution probability evolution) x) :
    ∃ B N : ℕ,
      IsUniversalWeightedFloquetFidelityDeadline
        (finiteContractionPeripheralWeight
          (finiteMixedEvolution probability evolution) x)
        ((finiteContractionPersistentMass
            (finiteMixedEvolution probability evolution) x - target) /
          (2 * finiteContractionPersistentMass
            (finiteMixedEvolution probability evolution) x)) N ∧
      ∃ n : ℕ, B < n ∧ n ≤ (B + 1) * N ∧
        target ≤
          ‖inner ℂ x
            (((finiteMixedEvolution probability evolution) ^ n) x)‖ :=
  finiteContraction_exists_return_at_target_before_deadline
    (finiteMixedEvolution probability evolution)
    (norm_finiteMixedEvolution_le_one probability hprobability hmass
      evolution hevolution)
    x hpersistent target htarget0 htarget

end RHTower
