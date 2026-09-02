import GaloisForLFunctions.RHTower.XiWardCubicPositiveShiftDampedDiagonalSeparator
import GaloisForLFunctions.HTGeometry.HolomorphicSchwarzPolarization

/-!
# Positive-shift scale resonance and finite-mixture no-go

The damped cubic separator is not monotone in depth-to-shift ratio.  Its full diagonal quantum is
attained exactly at the resonant scale `eps = 2a`; beyond that point the profile drops, so signed
dyadic scale differences need not be positive.

More generally, every fixed finite weighted mixture of source shifts becomes blind as horizontal
depth tends to zero.  Thus neither finitely many fixed shifts nor a nonnegative dyadic-difference
telescope can replace the missing all-scale or source-adaptive Stokes landing.  The positive
survivor is the exact resonance law: a displacement-matched shift pays the full quantum.
-/

open Complex Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Signed dyadic increment of the positive-shift diagonal profile. -/
def xiWardCubicPositiveShiftDyadicShellProfile (x : ℝ) : ℝ :=
  xiWardCubicPositiveShiftDiagonalSeparatorProfile (2 * x) -
    xiWardCubicPositiveShiftDiagonalSeparatorProfile x

/-- At depth-to-shift ratio `1/2`, the damped anomaly vanishes exactly. -/
theorem xiWardCubicPositiveShiftDiagonalAnomalyProfile_half :
    xiWardCubicPositiveShiftDiagonalAnomalyProfile (1 / 2) = 0 := by
  norm_num [xiWardCubicPositiveShiftDiagonalAnomalyProfile]

/-- The resonant ratio `1/2` receives the complete cubic Hellinger quantum. -/
theorem xiWardCubicPositiveShiftDiagonalSeparatorProfile_half :
    xiWardCubicPositiveShiftDiagonalSeparatorProfile (1 / 2) = 115 / 108 := by
  rw [xiWardCubicPositiveShiftDiagonalSeparatorProfile,
    xiWardCubicPositiveShiftDiagonalAnomalyProfile_half]
  ring

/-- The profile has already fallen strictly below its resonant value at ratio one. -/
theorem xiWardCubicPositiveShiftDiagonalSeparatorProfile_one_lt_half :
    xiWardCubicPositiveShiftDiagonalSeparatorProfile 1 <
      xiWardCubicPositiveShiftDiagonalSeparatorProfile (1 / 2) := by
  norm_num [xiWardCubicPositiveShiftDiagonalSeparatorProfile,
    xiWardCubicPositiveShiftDiagonalAnomalyProfile]

/-- Dyadic shell differences are not positive: the shell starting at the resonant ratio is
strictly negative. -/
theorem xiWardCubicPositiveShiftDyadicShellProfile_half_neg :
    xiWardCubicPositiveShiftDyadicShellProfile (1 / 2) < 0 := by
  rw [xiWardCubicPositiveShiftDyadicShellProfile]
  norm_num
  exact xiWardCubicPositiveShiftDiagonalSeparatorProfile_one_lt_half

/-- The separator profile is not monotone on the nonnegative depth ray. -/
theorem not_monotoneOn_xiWardCubicPositiveShiftDiagonalSeparatorProfile :
    ¬ MonotoneOn xiWardCubicPositiveShiftDiagonalSeparatorProfile (Ici 0) := by
  intro hmono
  have hle := hmono (by norm_num) (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  exact (not_le_of_gt
    xiWardCubicPositiveShiftDiagonalSeparatorProfile_one_lt_half) hle

/-- A displacement-matched source shift `eps = 2a` pays the complete quantum. -/
theorem xiWardCubicPositiveShiftDiagonalSeparatorProfile_resonant
    {a : ℝ} (ha : a ≠ 0) :
    xiWardCubicPositiveShiftDiagonalSeparatorProfile (a / (2 * a)) = 115 / 108 := by
  rw [show a / (2 * a) = (1 / 2 : ℝ) by field_simp]
  exact xiWardCubicPositiveShiftDiagonalSeparatorProfile_half

theorem continuousAt_xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero :
    ContinuousAt xiWardCubicPositiveShiftDiagonalSeparatorProfile 0 := by
  unfold xiWardCubicPositiveShiftDiagonalSeparatorProfile
    xiWardCubicPositiveShiftDiagonalAnomalyProfile
  fun_prop (disch := norm_num)

/-- **Finite-mixture shallow-collar no-go.**  Any fixed finite collection of source shifts, with
arbitrary real weights, loses all diagonal charge as displacement approaches the critical line.
Hence a uniform all-depth quantum requires an unbounded scale family or source-adaptive scale. -/
theorem tendsto_finset_weighted_xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero
    {ι : Type*} (S : Finset ι) (eps w : ι → ℝ) :
    Tendsto
      (fun a : ℝ => ∑ i ∈ S,
        w i * xiWardCubicPositiveShiftDiagonalSeparatorProfile (a / eps i))
      (nhds 0) (nhds 0) := by
  have hterm (i : ι) : Tendsto
      (fun a : ℝ => w i *
        xiWardCubicPositiveShiftDiagonalSeparatorProfile (a / eps i))
      (nhds 0) (nhds 0) := by
    have hratio : Tendsto (fun a : ℝ => a / eps i) (nhds 0) (nhds 0) := by
      by_cases heps : eps i = 0
      · simp [heps]
      · simpa [heps] using
          (show ContinuousAt (fun a : ℝ => a / eps i) 0 by fun_prop).tendsto
    have hprofile :=
      continuousAt_xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero.tendsto.comp hratio
    have hmul := (tendsto_const_nhds (x := w i)).mul hprofile
    simpa only [Function.comp_apply,
      xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero, mul_zero] using hmul
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum S (fun i _hi => hterm i)

/-- **Finite scale-mass no-go.**  The same blindness holds for every fixed finite measure on
positive source scales, not only for a finite combination.  Dominated convergence applies because
the separator lies between zero and `115/108` on the positive depth ray.  Therefore uniform
all-depth charge requires infinite scale mass or a scale law that moves with the tested depth. -/
theorem tendsto_integral_xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero
    (μ : MeasureTheory.Measure (Ioi (0 : ℝ))) [MeasureTheory.IsFiniteMeasure μ]
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (nhds 0)) :
    Tendsto
      (fun n => ∫ eps : Ioi (0 : ℝ),
        xiWardCubicPositiveShiftDiagonalSeparatorProfile (a n / (eps : ℝ)) ∂μ)
      atTop (nhds 0) := by
  have hmeas (n : ℕ) : MeasureTheory.AEStronglyMeasurable
      (fun eps : Ioi (0 : ℝ) =>
        xiWardCubicPositiveShiftDiagonalSeparatorProfile (a n / (eps : ℝ))) μ := by
    apply Measurable.aestronglyMeasurable
    unfold xiWardCubicPositiveShiftDiagonalSeparatorProfile
      xiWardCubicPositiveShiftDiagonalAnomalyProfile
    measurability
  have hbound (n : ℕ) : ∀ᵐ eps : Ioi (0 : ℝ) ∂μ,
      ‖xiWardCubicPositiveShiftDiagonalSeparatorProfile (a n / (eps : ℝ))‖ ≤
        (115 / 108 : ℝ) := by
    filter_upwards with eps
    have hratio : 0 ≤ a n / (eps : ℝ) := div_nonneg (ha n) eps.property.le
    rw [Real.norm_eq_abs, abs_of_nonneg
      (xiWardCubicPositiveShiftDiagonalSeparatorProfile_nonneg hratio)]
    exact xiWardCubicPositiveShiftDiagonalSeparatorProfile_le_quantum hratio
  have hlim : ∀ᵐ eps : Ioi (0 : ℝ) ∂μ, Tendsto
      (fun n => xiWardCubicPositiveShiftDiagonalSeparatorProfile (a n / (eps : ℝ)))
      atTop (nhds 0) := by
    filter_upwards with eps
    have hratio : Tendsto (fun n => a n / (eps : ℝ)) atTop (nhds 0) := by
      simpa using ha0.div_const (eps : ℝ)
    have hprofile :=
      continuousAt_xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero.tendsto.comp hratio
    change Tendsto
      (xiWardCubicPositiveShiftDiagonalSeparatorProfile ∘
        fun n => a n / (eps : ℝ)) atTop (nhds 0)
    simpa only [xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero] using hprofile
  simpa using MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : Ioi (0 : ℝ) => (115 / 108 : ℝ)) hmeas
    (MeasureTheory.integrable_const _) (fun n => hbound n) hlim

/-! ## Positive survivor: signed infinite scale transport -/

/-- Finite signed dyadic shells telescope exactly.  Unlike a positive finite scale mixture, this
retains cancellation between adjacent source scales. -/
theorem sum_range_xiWardCubicPositiveShiftDyadicShellProfile
    (n : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range n,
      xiWardCubicPositiveShiftDyadicShellProfile ((2 : ℝ) ^ j * x)) =
      xiWardCubicPositiveShiftDiagonalSeparatorProfile ((2 : ℝ) ^ n * x) -
        xiWardCubicPositiveShiftDiagonalSeparatorProfile x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [xiWardCubicPositiveShiftDyadicShellProfile, pow_succ]
      ring_nf

/-- On the Route-T shallow band, the signed scale-tail quantum at every Euler-safe endpoint is
uniformly positive.  The rational `1/20` is deliberately conservative. -/
theorem one_twentieth_le_xiWardCubicPositiveShiftDiagonalAnomalyProfile
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 5) :
    (1 / 20 : ℝ) ≤ xiWardCubicPositiveShiftDiagonalAnomalyProfile x := by
  unfold xiWardCubicPositiveShiftDiagonalAnomalyProfile
  have h0 : 0 < 2 * x + 2 := by linarith
  have h1 : 0 < 3 * x + 3 / 2 := by linarith
  have h2 : 0 < 4 * x + 1 := by linarith
  field_simp [h0.ne', h1.ne', h2.ne']
  nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), sq_nonneg (x ^ 3),
    mul_nonneg hx0 (sub_nonneg.mpr hx1)]

/-- The separator tends to its full off-diagonal quantum at the remote end of the signed scale
transport. -/
theorem tendsto_xiWardCubicPositiveShiftDiagonalSeparatorProfile_atTop :
    Tendsto xiWardCubicPositiveShiftDiagonalSeparatorProfile atTop
      (nhds (115 / 108 : ℝ)) := by
  have h :=
    (tendsto_const_nhds.sub
      tendsto_xiWardCubicPositiveShiftDiagonalAnomalyProfile_atTop :
      Tendsto
        (fun x : ℝ => (115 / 108 : ℝ) -
          xiWardCubicPositiveShiftDiagonalAnomalyProfile x)
        atTop (nhds ((115 / 108 : ℝ) - 0)))
  convert h using 1
  · rfl
  · norm_num

/-- Exact signed infinite-scale survivor.  For every positive transverse displacement, partial
dyadic shell sums converge to the anomaly left at the fixed safe endpoint. -/
theorem tendsto_sum_range_xiWardCubicPositiveShiftDyadicShellProfile
    {x : ℝ} (hx : 0 < x) :
    Tendsto
      (fun n : ℕ => ∑ j ∈ Finset.range n,
        xiWardCubicPositiveShiftDyadicShellProfile ((2 : ℝ) ^ j * x))
      atTop
      (nhds (xiWardCubicPositiveShiftDiagonalAnomalyProfile x)) := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * x) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hx
  have hprofile :=
    tendsto_xiWardCubicPositiveShiftDiagonalSeparatorProfile_atTop.comp hpow
  have hsub := hprofile.sub_const
    (xiWardCubicPositiveShiftDiagonalSeparatorProfile x)
  convert hsub using 1
  · funext n
    rw [sum_range_xiWardCubicPositiveShiftDyadicShellProfile]
    rfl
  · rw [xiWardCubicPositiveShiftDiagonalSeparatorProfile]
    ring_nf

/-- Signed dyadic scale transport commutes with every finite multiplicity packet. -/
theorem tendsto_finset_sum_range_xiWardCubicPositiveShiftDyadicShellProfile
    {ι : Type*} (S : Finset ι) (a : ι → ℝ) {eps : ℝ}
    (heps : 0 < eps) (ha : ∀ i ∈ S, 0 < a i) :
    Tendsto
      (fun n : ℕ => ∑ i ∈ S, ∑ j ∈ Finset.range n,
        xiWardCubicPositiveShiftDyadicShellProfile
          ((2 : ℝ) ^ j * (a i / eps)))
      atTop
      (nhds (∑ i ∈ S,
        xiWardCubicPositiveShiftDiagonalAnomalyProfile (a i / eps))) := by
  apply tendsto_finsetSum S
  intro i hi
  exact tendsto_sum_range_xiWardCubicPositiveShiftDyadicShellProfile
    (div_pos (ha i hi) heps)

/-- Uniform linear-multiplicity receiver for the signed scale-tail limit.  It survives precisely
because the scale shells are signed; the preceding finite-positive-mass no-go does not apply. -/
theorem card_div_twenty_le_sum_xiWardCubicPositiveShiftDiagonalAnomalyProfile
    {ι : Type*} (S : Finset ι) (a : ι → ℝ) {eps : ℝ}
    (heps : 0 < eps) (ha0 : ∀ i ∈ S, 0 ≤ a i)
    (ha1 : ∀ i ∈ S, a i ≤ eps / 5) :
    (S.card : ℝ) / 20 ≤
      ∑ i ∈ S,
        xiWardCubicPositiveShiftDiagonalAnomalyProfile (a i / eps) := by
  rw [show (S.card : ℝ) / 20 = ∑ _i ∈ S, (1 / 20 : ℝ) by
    simp [div_eq_mul_inv]]
  apply Finset.sum_le_sum
  intro i hi
  apply one_twentieth_le_xiWardCubicPositiveShiftDiagonalAnomalyProfile
    (div_nonneg (ha0 i hi) heps.le)
  rw [div_le_iff₀ heps]
  nlinarith [ha1 i hi]

/-! ## Source-realization audit -/

/-- Unit-normalized signed dyadic shell. -/
def xiWardCubicPositiveShiftDyadicShellMask (x : ℝ) : ℝ :=
  (108 / 115) * xiWardCubicPositiveShiftDyadicShellProfile x

theorem xiWardCubicPositiveShiftDyadicShellMask_zero :
    xiWardCubicPositiveShiftDyadicShellMask 0 = 0 := by
  simp [xiWardCubicPositiveShiftDyadicShellMask,
    xiWardCubicPositiveShiftDyadicShellProfile,
    xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero]

theorem xiWardCubicPositiveShiftDyadicShellMask_half_neg :
    xiWardCubicPositiveShiftDyadicShellMask (1 / 2) < 0 := by
  unfold xiWardCubicPositiveShiftDyadicShellMask
  exact mul_neg_of_pos_of_neg (by norm_num)
    xiWardCubicPositiveShiftDyadicShellProfile_half_neg

/-- Signed scale transport escapes the finite-positive-mixture no-go, but not holomorphic
scalarization.  Even one dyadic shell is real-valued and nonconstant on the reflection graph, so
it cannot be the restriction of a jointly entire source weight.  A legitimate shell landing must
therefore retain a real Stokes/Wirtinger term (or the fixed poles of a meromorphic source kernel). -/
theorem not_exists_entire_xiWardCubicPositiveShiftDyadicShellMaskLanding
    {eps : ℝ} (heps : 0 < eps) :
    ¬ ∃ F : ℂ × ℂ → ℂ,
      Differentiable ℂ F ∧
      ∀ z : ℂ,
        F (1 - z, z) =
          (xiWardCubicPositiveShiftDyadicShellMask (z.re / eps) : ℂ) := by
  rintro ⟨F, hF, hland⟩
  let g : ℂ → ℂ := fun z => F (1 - z, z)
  have hg : Differentiable ℂ g := by
    dsimp only [g]
    fun_prop
  have hstarEq : (fun z : ℂ => star (g z)) = g := by
    funext z
    change star (F (1 - z, z)) = F (1 - z, z)
    rw [hland]
    exact Complex.conj_ofReal _
  have hgstar : Differentiable ℂ (fun z : ℂ => star (g z)) := by
    rw [hstarEq]
    exact hg
  have hconst :=
    GaloisForLFunctions.HTGeometry.eq_of_differentiable_pointwiseStar
      hg hgstar ((eps / 2 : ℝ) : ℂ)
  dsimp only [g] at hconst
  rw [hland, hland, Complex.ofReal_inj] at hconst
  norm_num [heps.ne'] at hconst
  rw [xiWardCubicPositiveShiftDyadicShellMask_zero] at hconst
  have hratio : eps / 2 / eps = (1 / 2 : ℝ) := by
    field_simp [heps.ne']
  rw [hratio] at hconst
  exact (ne_of_lt xiWardCubicPositiveShiftDyadicShellMask_half_neg) hconst

end

end RHTower
