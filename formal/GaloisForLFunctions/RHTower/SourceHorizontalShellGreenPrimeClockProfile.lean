import GaloisForLFunctions.RHTower.LegStripThreshold
import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockProfile

/-!
# Gamma-six shell Green / Wold prime-clock profile identity

The Gamma-six Green principal class has shell multiplicity `5 * 6^m` and principal
eigenvalue `(1 / 6)^m`.  Their product is exactly `5`, so its logarithmically rescaled
shell moments are uniform moments on `[0,1]`.  This file proves that every normalized
shell moment converges to `1 / (r + 1)` and hence that the full coefficient-faithful odd
shell response converges to the existing Wold prime-clock universal profile.

This is an unconditional scalar trace theorem.  It does not assume a source comparison
between the two reflected strict critical-edge transports; that comparison remains the
producer needed to turn the receiver at the end of this file into RH.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Multiplicity of the `m`-th Gamma-six shell in the Green principal class. -/
def sourceHorizontalGammaSixShellMultiplicity (m : ℕ) : ℕ :=
  5 * 6 ^ m

/-- Principal Green eigenvalue on the `m`-th Gamma-six shell. -/
def sourceHorizontalGammaSixShellGreenEigenvalue (m : ℕ) : ℝ :=
  (1 / 6 : ℝ) ^ m

/-- Ordinary trace mass of one complete Gamma-six Green shell. -/
def sourceHorizontalGammaSixShellGreenTraceMass (m : ℕ) : ℝ :=
  sourceHorizontalGammaSixShellMultiplicity m *
    sourceHorizontalGammaSixShellGreenEigenvalue m

/-- Shell multiplicity and Green decay cancel exactly.  Thus every logarithmic shell carries
the same nonzero trace mass, rather than merely an asymptotically comparable mass. -/
@[simp] theorem sourceHorizontalGammaSixShellGreenTraceMass_eq_five (m : ℕ) :
    sourceHorizontalGammaSixShellGreenTraceMass m = 5 := by
  rw [sourceHorizontalGammaSixShellGreenTraceMass,
    sourceHorizontalGammaSixShellMultiplicity,
    sourceHorizontalGammaSixShellGreenEigenvalue]
  push_cast
  rw [show 5 * 6 ^ m * (1 / 6 : ℝ) ^ m =
      5 * (6 ^ m * (1 / 6 : ℝ) ^ m) by ring]
  rw [← mul_pow]
  norm_num

/-- Remaining logarithmic shell coordinate.  For `k < N`, this lists the same finite carrier as
the right-endpoint grid `1/N, ..., N/N`, but in reflected shell order. -/
def sourceHorizontalGammaSixShellClock (N k : ℕ) : ℝ :=
  1 - (k : ℝ) / N

/-- Green-trace-normalized `r`-th logarithmic shell moment.  The visible quotient by `5` retains
the literal Gamma-six shell trace weight before normalization. -/
def sourceHorizontalGammaSixShellNormalizedMoment (N r : ℕ) : ℝ :=
  (1 / (N : ℝ)) *
    ∑ k ∈ Finset.range N,
      (sourceHorizontalGammaSixShellGreenTraceMass (N - k) / 5) *
        sourceHorizontalGammaSixShellClock N k ^ r

theorem sourceHorizontalGammaSixShellNormalizedMoment_eq_uniform
    (N r : ℕ) :
    sourceHorizontalGammaSixShellNormalizedMoment N r =
      (1 / (N : ℝ)) *
        ∑ k ∈ Finset.range N,
          (1 - (k : ℝ) / N) ^ r := by
  simp [sourceHorizontalGammaSixShellNormalizedMoment,
    sourceHorizontalGammaSixShellClock]

/-- All Gamma-six logarithmic shell moments have the same limiting coefficients as the ordered
Wold prime-clock moments. -/
theorem tendsto_sourceHorizontalGammaSixShellNormalizedMoment (r : ℕ) :
    Tendsto (fun N : ℕ => sourceHorizontalGammaSixShellNormalizedMoment N r)
      atTop (nhds (1 / (r + 1 : ℕ) : ℝ)) := by
  have hanti : AntitoneOn (fun x : ℝ => (1 - x) ^ r) (Set.Icc 0 1) := by
    intro a ha b hb hab
    exact pow_le_pow_left₀ (by linarith [hb.2]) (by linarith) r
  have hsum := tendsto_riemann_sum_antitone hanti
  have hint : (∫ x in (0 : ℝ)..1, (1 - x) ^ r) =
      (1 / (r + 1 : ℕ) : ℝ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ r) 1]
    rw [integral_pow]
    norm_num
  rw [hint] at hsum
  simpa only [sourceHorizontalGammaSixShellNormalizedMoment_eq_uniform] using hsum

/-- Exact cross-corpus coefficient identity: Gamma-six Green shell moments and Wold ordered
prime-clock moments have the same limit in every degree. -/
theorem sourceHorizontalGammaSixShellMoment_matches_Wold
    (r : ℕ) :
    Tendsto (fun N : ℕ =>
      sourceHorizontalGammaSixShellNormalizedMoment N r -
        sourceHorizontalWoldOrderedNormalizedMoment N r)
      atTop (nhds 0) := by
  have hshell := tendsto_sourceHorizontalGammaSixShellNormalizedMoment r
  have hwold := tendsto_sourceHorizontalWoldOrderedNormalizedMoment r
  simpa using hshell.sub hwold

theorem sourceHorizontalGammaSixShellClock_nonneg
    {N k : ℕ} (hk : k ∈ Finset.range N) :
    0 ≤ sourceHorizontalGammaSixShellClock N k := by
  rw [Finset.mem_range] at hk
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
  rw [sourceHorizontalGammaSixShellClock, sub_nonneg]
  exact (div_le_one (by positivity : (0 : ℝ) < N)).2 (by exact_mod_cast hk.le)

theorem sourceHorizontalGammaSixShellClock_le_one (N k : ℕ) :
    sourceHorizontalGammaSixShellClock N k ≤ 1 := by
  rw [sourceHorizontalGammaSixShellClock]
  exact sub_le_self _ (div_nonneg (by positivity) (by positivity))

theorem sourceHorizontalGammaSixShellNormalizedMoment_nonneg (N r : ℕ) :
    0 ≤ sourceHorizontalGammaSixShellNormalizedMoment N r := by
  rw [sourceHorizontalGammaSixShellNormalizedMoment_eq_uniform]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun k hk =>
      pow_nonneg (sourceHorizontalGammaSixShellClock_nonneg hk) r)

/-- Uniform domination needed to exchange the shell horizon with the full odd Taylor series. -/
theorem sourceHorizontalGammaSixShellNormalizedMoment_le_one (N r : ℕ) :
    sourceHorizontalGammaSixShellNormalizedMoment N r ≤ 1 := by
  cases N with
  | zero => simp [sourceHorizontalGammaSixShellNormalizedMoment_eq_uniform]
  | succ N =>
      rw [sourceHorizontalGammaSixShellNormalizedMoment_eq_uniform]
      have hsum :
          (∑ k ∈ Finset.range (N + 1),
              (1 - (k : ℝ) / (N + 1 : ℕ)) ^ r) ≤
            ∑ _k ∈ Finset.range (N + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply pow_le_one₀
        · exact sourceHorizontalGammaSixShellClock_nonneg hk
        · exact sourceHorizontalGammaSixShellClock_le_one (N + 1) k
      calc
        (1 / ((N + 1 : ℕ) : ℝ)) *
              ∑ k ∈ Finset.range (N + 1),
                (1 - (k : ℝ) / (N + 1 : ℕ)) ^ r
            ≤ (1 / ((N + 1 : ℕ) : ℝ)) *
                ∑ _k ∈ Finset.range (N + 1), (1 : ℝ) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 := by
          simp
          apply inv_mul_cancel₀
          positivity

/-- Finite-stage odd response of the normalized Gamma-six shell Green trace. -/
def sourceHorizontalGammaSixShellPrimeClockProfileSeries (N : ℕ) (u : ℝ) : ℝ :=
  ∑' k : ℕ,
    u ^ (2 * k + 1) / (2 * k + 1).factorial *
      (sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) - 1)

/-- The complete Gamma-six shell Green response and the complete Wold prime-clock response have
the same horizon, coefficient by coefficient at every odd order. -/
theorem tendsto_sourceHorizontalGammaSixShellPrimeClockProfileSeries (u : ℝ) :
    Tendsto (fun N : ℕ =>
      sourceHorizontalGammaSixShellPrimeClockProfileSeries N u) atTop
      (nhds (sourceHorizontalWoldPrimeClockUniversalProfile u)) := by
  unfold sourceHorizontalGammaSixShellPrimeClockProfileSeries
  unfold sourceHorizontalWoldPrimeClockUniversalProfile
  apply tendsto_tsum_of_dominated_convergence
      (Real.hasSum_sinh |u|).summable
  · intro k
    have hk := tendsto_sourceHorizontalGammaSixShellNormalizedMoment (2 * k)
    exact tendsto_const_nhds.mul (hk.sub tendsto_const_nhds)
  · filter_upwards with N
    intro k
    have hk0 : 0 ≤ sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) :=
      sourceHorizontalGammaSixShellNormalizedMoment_nonneg N (2 * k)
    have hk1 : sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) ≤ 1 :=
      sourceHorizontalGammaSixShellNormalizedMoment_le_one N (2 * k)
    have habs :
        |sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) - 1| ≤ 1 :=
      (abs_le).2 ⟨by linarith, by linarith⟩
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow]
    simp only [Nat.cast_nonneg, abs_of_nonneg]
    exact mul_le_of_le_one_right (by positivity) habs

theorem sourceHorizontalGammaSixShellClock_pos
    {N k : ℕ} (hk : k ∈ Finset.range N) :
    0 < sourceHorizontalGammaSixShellClock N k := by
  rw [Finset.mem_range] at hk
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
  rw [sourceHorizontalGammaSixShellClock, sub_pos]
  exact (div_lt_one (by positivity : (0 : ℝ) < N)).2 (by exact_mod_cast hk)

private theorem sourceHorizontalGammaSixShellProfileSeries_term_eq
    (N k : ℕ) (u : ℝ) :
    u ^ (2 * k + 1) / (2 * k + 1).factorial *
        (sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) - 1) =
      (1 / (N : ℝ)) *
          ∑ j ∈ Finset.range N,
            (sourceHorizontalGammaSixShellClock N j)⁻¹ *
              ((u * sourceHorizontalGammaSixShellClock N j) ^ (2 * k + 1) /
                (2 * k + 1).factorial) -
        u ^ (2 * k + 1) / (2 * k + 1).factorial := by
  rw [sourceHorizontalGammaSixShellNormalizedMoment_eq_uniform]
  calc
    u ^ (2 * k + 1) / (2 * k + 1).factorial *
          ((1 / (N : ℝ)) *
              ∑ j ∈ Finset.range N, (1 - (j : ℝ) / N) ^ (2 * k) - 1) =
        (1 / (N : ℝ)) *
            (u ^ (2 * k + 1) / (2 * k + 1).factorial *
              ∑ j ∈ Finset.range N, (1 - (j : ℝ) / N) ^ (2 * k)) -
          u ^ (2 * k + 1) / (2 * k + 1).factorial := by ring
    _ = (1 / (N : ℝ)) *
          ∑ j ∈ Finset.range N,
            (sourceHorizontalGammaSixShellClock N j)⁻¹ *
              ((u * sourceHorizontalGammaSixShellClock N j) ^ (2 * k + 1) /
                (2 * k + 1).factorial) -
          u ^ (2 * k + 1) / (2 * k + 1).factorial := by
      congr 2
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← sourceHorizontalGammaSixShellClock]
      have hx : sourceHorizontalGammaSixShellClock N j ≠ 0 :=
        (sourceHorizontalGammaSixShellClock_pos hj).ne'
      rw [inv_mul_eq_div]
      field_simp [hx]
      rw [mul_pow, show 2 * k + 1 = 2 * k + 1 by rfl, pow_succ]
      ring

/-- Exact finite Taylor resummation of the shell trace.  Every shell, multiplicity, Green
eigenvalue, reflection orientation, and odd Taylor coefficient survives this equality. -/
theorem sourceHorizontalGammaSixShellPrimeClockProfileSeries_eq_finiteTrace
    {N : ℕ} (_hN : 0 < N) (u : ℝ) :
    sourceHorizontalGammaSixShellPrimeClockProfileSeries N u =
      (1 / (N : ℝ)) *
          ∑ j ∈ Finset.range N,
            (sourceHorizontalGammaSixShellClock N j)⁻¹ *
              Real.sinh (u * sourceHorizontalGammaSixShellClock N j) -
        Real.sinh u := by
  have hshell : ∀ j ∈ Finset.range N, Summable (fun k : ℕ =>
      (sourceHorizontalGammaSixShellClock N j)⁻¹ *
        ((u * sourceHorizontalGammaSixShellClock N j) ^ (2 * k + 1) /
          (2 * k + 1).factorial)) := by
    intro j hj
    exact (Real.hasSum_sinh
      (u * sourceHorizontalGammaSixShellClock N j)).summable.mul_left _
  have hfiniteBase : Summable (fun k : ℕ =>
      ∑ j ∈ Finset.range N,
        (sourceHorizontalGammaSixShellClock N j)⁻¹ *
          ((u * sourceHorizontalGammaSixShellClock N j) ^ (2 * k + 1) /
            (2 * k + 1).factorial)) :=
    summable_sum hshell
  have hfinite : Summable (fun k : ℕ =>
      (1 / (N : ℝ)) *
        ∑ j ∈ Finset.range N,
          (sourceHorizontalGammaSixShellClock N j)⁻¹ *
            ((u * sourceHorizontalGammaSixShellClock N j) ^ (2 * k + 1) /
              (2 * k + 1).factorial)) :=
    hfiniteBase.mul_left _
  have hu : Summable (fun k : ℕ =>
      u ^ (2 * k + 1) / (2 * k + 1).factorial) :=
    (Real.hasSum_sinh u).summable
  rw [sourceHorizontalGammaSixShellPrimeClockProfileSeries]
  rw [show (∑' k : ℕ,
      u ^ (2 * k + 1) / (2 * k + 1).factorial *
        (sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) - 1)) =
      ∑' k : ℕ,
        ((1 / (N : ℝ)) *
            ∑ j ∈ Finset.range N,
              (sourceHorizontalGammaSixShellClock N j)⁻¹ *
                ((u * sourceHorizontalGammaSixShellClock N j) ^ (2 * k + 1) /
                  (2 * k + 1).factorial) -
          u ^ (2 * k + 1) / (2 * k + 1).factorial) by
    exact tsum_congr fun k =>
      sourceHorizontalGammaSixShellProfileSeries_term_eq N k u]
  rw [hfinite.tsum_sub hu]
  rw [Summable.tsum_mul_left _ hfiniteBase]
  rw [Summable.tsum_finsetSum hshell]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_mul_left _
    (Real.hasSum_sinh
      (u * sourceHorizontalGammaSixShellClock N j)).summable]
  rw [(Real.hasSum_sinh
    (u * sourceHorizontalGammaSixShellClock N j)).tsum_eq]
  exact (Real.hasSum_sinh u).tsum_eq

/-- Reflection reverses the complete finite shell response before passage to the singular
horizon. -/
@[simp] theorem sourceHorizontalGammaSixShellPrimeClockProfileSeries_neg
    (N : ℕ) (u : ℝ) :
    sourceHorizontalGammaSixShellPrimeClockProfileSeries N (-u) =
      -sourceHorizontalGammaSixShellPrimeClockProfileSeries N u := by
  unfold sourceHorizontalGammaSixShellPrimeClockProfileSeries
  calc
    (∑' k : ℕ,
        (-u) ^ (2 * k + 1) / (2 * k + 1).factorial *
          (sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) - 1)) =
      ∑' k : ℕ,
        -(u ^ (2 * k + 1) / (2 * k + 1).factorial *
          (sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) - 1)) := by
            apply tsum_congr
            intro k
            have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
            rw [hodd.neg_pow]
            ring
    _ = -(∑' k : ℕ,
        u ^ (2 * k + 1) / (2 * k + 1).factorial *
          (sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) - 1)) := tsum_neg

/-- Finite-cutoff anomaly of commuting source reflection with oriented shell evaluation. -/
def sourceHorizontalGammaSixShellReflectionBaseChangeDefect
    (N : ℕ) (u : ℝ) : ℝ :=
  sourceHorizontalGammaSixShellPrimeClockProfileSeries N u -
    sourceHorizontalGammaSixShellPrimeClockProfileSeries N (-u)

theorem sourceHorizontalGammaSixShellReflectionBaseChangeDefect_eq
    (N : ℕ) (u : ℝ) :
    sourceHorizontalGammaSixShellReflectionBaseChangeDefect N u =
      2 * sourceHorizontalGammaSixShellPrimeClockProfileSeries N u := by
  rw [sourceHorizontalGammaSixShellReflectionBaseChangeDefect,
    sourceHorizontalGammaSixShellPrimeClockProfileSeries_neg]
  ring

/-- The singular-horizon base-change anomaly is exactly twice the Wold universal profile. -/
theorem tendsto_sourceHorizontalGammaSixShellReflectionBaseChangeDefect
    (u : ℝ) :
    Tendsto (fun N : ℕ =>
      sourceHorizontalGammaSixShellReflectionBaseChangeDefect N u) atTop
      (nhds (2 * sourceHorizontalWoldPrimeClockUniversalProfile u)) := by
  rw [show (fun N : ℕ =>
      sourceHorizontalGammaSixShellReflectionBaseChangeDefect N u) =
      fun N : ℕ =>
        2 * sourceHorizontalGammaSixShellPrimeClockProfileSeries N u by
    funext N
    exact sourceHorizontalGammaSixShellReflectionBaseChangeDefect_eq N u]
  exact tendsto_const_nhds.mul
    (tendsto_sourceHorizontalGammaSixShellPrimeClockProfileSeries u)

/-- The base-change anomaly vanishes only at the neutral horizontal character. -/
theorem sourceHorizontalGammaSixShellReflectionBaseChangeLimit_eq_zero_iff
    (u : ℝ) :
    2 * sourceHorizontalWoldPrimeClockUniversalProfile u = 0 ↔ u = 0 := by
  rw [mul_eq_zero]
  norm_num
  exact sourceHorizontalWoldPrimeClockUniversalProfile_eq_zero_iff u

/-! ### The exact missing producer and its RH receiver -/

/-- Pointwise producer requested by the strict critical-edge route: the two reflected shell-trace
responses are identified on the same multiplicity-labelled Xi carrier.  Reflection by itself only
exchanges the two sides and does not prove this proposition. -/
def SourceZeroHorizontalGammaSixShellReflectedResponseIdentified
    (q : XiZeroCopy) : Prop :=
  sourceHorizontalWoldPrimeClockUniversalProfile
      (primeDepthBVWoldXiCenteredRate q.1) =
    sourceHorizontalWoldPrimeClockUniversalProfile
      (primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1)

/-- Exact pointwise receiver: coefficient-faithful equality of the two reflected Gamma-six shell
responses forces, and is forced by, critical-line placement. -/
theorem sourceZeroHorizontalGammaSixShellReflectedResponseIdentified_iff
    (q : XiZeroCopy) :
    SourceZeroHorizontalGammaSixShellReflectedResponseIdentified q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hrate :
      primeDepthBVWoldXiCenteredRate (xiZeroCopyLineConjEquiv q).1 =
        -primeDepthBVWoldXiCenteredRate q.1 := by
    change primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv q.1) =
      -primeDepthBVWoldXiCenteredRate q.1
    exact primeDepthBVWoldXiCenteredRate_reflection q.1
  rw [SourceZeroHorizontalGammaSixShellReflectedResponseIdentified, hrate,
    sourceHorizontalWoldPrimeClockUniversalProfile_neg]
  constructor
  · intro h
    have hzero : sourceHorizontalWoldPrimeClockUniversalProfile
        (primeDepthBVWoldXiCenteredRate q.1) = 0 := by linarith
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).1
      ((sourceHorizontalWoldPrimeClockUniversalProfile_eq_zero_iff _).1 hzero)
  · intro hline
    have hzero : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hline
    simp [hzero, sourceHorizontalWoldPrimeClockUniversalProfile]

/-- Global coefficient-faithful strict-edge producer. -/
def SourceZeroHorizontalGammaSixShellReflectedResponsesIdentified : Prop :=
  ∀ q : XiZeroCopy, SourceZeroHorizontalGammaSixShellReflectedResponseIdentified q

/-- The new Frankenstein receiver: proving one source theorem that identifies the two strict-edge
shell traces is now exactly equivalent to RH.  The equivalence is unconditional; it does not assert
the still-missing producer. -/
theorem sourceZeroHorizontalGammaSixShellReflectedResponsesIdentified_iff_riemannHypothesis :
    SourceZeroHorizontalGammaSixShellReflectedResponsesIdentified ↔ RiemannHypothesis := by
  constructor
  · intro hidentified
    have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
      intro q
      exact (sourceZeroHorizontalGammaSixShellReflectedResponseIdentified_iff q).1
        (hidentified q)
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline q]
  · intro hRH q
    apply (sourceZeroHorizontalGammaSixShellReflectedResponseIdentified_iff q).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end RHTower
