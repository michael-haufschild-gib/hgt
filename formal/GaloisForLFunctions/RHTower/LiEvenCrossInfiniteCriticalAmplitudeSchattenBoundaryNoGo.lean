import GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelFiniteCriticalPrefixOscillationNoGo
import GaloisForLFunctions.RHTower.XiOrderedPrimeSchattenThreshold
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap

/-!
# Infinite critical-amplitude Schatten boundary for the even Li current

The finite critical-prefix recurrence argument cannot be passed to the complete positive Xi
divisor through an absolutely summable pure-point limit. At the endpoint squared mass `v = 1/4`,
a critical copy of positive ordinate `gamma` has exact current amplitude

`gamma / (gamma^2 + 1/4)`.

For the multiplicity-ordered positive Xi ordinates, this amplitude sequence lies in every
`ℓ^p`, `p > 1`, but not in `ℓ^1`. Thus no multiplicity-exact critical enumeration can supply the
absolutely summable packet required by the corpus Bohr recurrence theorem.

Exact LI proof branch killed:

`finite critical-prefix cofinal sign change`
`=> absolutely summable full critical pure-point packet`
`=> full-current cofinal sign change`
`=> current zero`
`=> RH`.

Positive survivor: the full endpoint packet has the sharp Schatten boundary `p = 1`. Any viable
infinite-tail LI argument must work in the conditional `ℓ^p \ ℓ^1` regime and retain the
accumulation of frequencies at zero; uniform Bohr-tail truncation is unavailable.

All capstones are closed and unconditional. No numerical computation is used.
-/

open Filter

namespace RHTower

noncomputable section

/-- Canonical endpoint amplitude attached to the `n`-th positive Xi ordinate. -/
def liEvenCrossOrderedEndpointAmplitude (n : ℕ) : ℝ :=
  xiOrderedPositiveOrdinate n /
    (xiOrderedPositiveOrdinate n ^ 2 + 1 / 4)

/-- The endpoint source gap transfers to every multiplicity-ordered positive ordinate. -/
theorem one_lt_xiOrderedPositiveOrdinate (n : ℕ) :
    1 < xiOrderedPositiveOrdinate n := by
  obtain ⟨z, hz, him⟩ := exists_xi_zero_im_eq_xiOrderedPositiveOrdinate n
  have hgap := one_lt_abs_im_of_xi_eq_zero hz
  rw [him, abs_of_pos (xiOrderedPositiveOrdinate_pos n)] at hgap
  exact hgap

/-- On the critical line, shifted reciprocal mass is the real Cauchy resolvent in the ordinate. -/
theorem liEvenCrossCriticalAtomMass_eq_imaginary
    {v : ℝ} (hv : 0 ≤ v) (q : XiCriticalLineResolventCopy) :
    liEvenCrossCriticalAtomMass v q =
      1 / (v + (q.1.1 : ℂ).im ^ 2) := by
  rw [liEvenCrossCriticalAtomMass,
    xiShiftedReciprocalSquare_eq_coordinate hv q.1]
  have hcrit : (q.1.1 : ℂ).re - 1 / 2 = 0 := by
    rw [q.2]
    ring
  rw [hcrit]
  norm_num only [zero_pow, sub_zero, mul_zero,
    Complex.ofReal_zero, zero_mul]
  rw [Complex.inv_re]
  simp only [Complex.ofReal_re, Complex.normSq_ofReal]
  have hden : v + (q.1.1 : ℂ).im ^ 2 ≠ 0 := by
    have him := xi_divisor_support_im_ne_zero q.1.1
    nlinarith [sq_pos_of_ne_zero him]
  field_simp [hden]

/-- Exact critical-atom amplitude at the LI endpoint `v = 1/4`. -/
theorem liEvenCrossCriticalAtomAmplitude_oneFourth_eq_imaginary
    (q : XiCriticalLineResolventCopy)
    (him : 0 < (q.1.1 : ℂ).im) :
    liEvenCrossCriticalAtomAmplitude (1 / 4) q =
      (q.1.1 : ℂ).im / ((q.1.1 : ℂ).im ^ 2 + 1 / 4) := by
  set gamma : ℝ := (q.1.1 : ℂ).im with hgamma
  set den : ℝ := gamma ^ 2 + 1 / 4 with hden
  have hgammaPos : 0 < gamma := by simpa [hgamma] using him
  have hdenPos : 0 < den := by dsimp [den]; positivity
  have hmass : liEvenCrossCriticalAtomMass (1 / 4) q = 1 / den := by
    simpa [hgamma, hden, add_comm] using
      liEvenCrossCriticalAtomMass_eq_imaginary (v := 1 / 4) (by norm_num) q
  have hnode : liEvenCrossCriticalAtomNode (1 / 4) q = (1 / 4) / den := by
    rw [liEvenCrossCriticalAtomNode, hmass]
    ring
  have hcos := liEvenCrossCriticalAtomAngle_cos
    (v := 1 / 4) (by norm_num) (by norm_num) q
  have hcos' : Real.cos (liEvenCrossCriticalAtomAngle (1 / 4) q) =
      (1 / 4 - gamma ^ 2) / den := by
    rw [hcos, hnode]
    dsimp [den]
    field_simp
    ring
  obtain ⟨hthetaHalf, hthetaPi⟩ := liEvenCrossCriticalAtomAngle_mem
    (v := 1 / 4) (by norm_num) (by norm_num) q
  have hsinPos : 0 < Real.sin (liEvenCrossCriticalAtomAngle (1 / 4) q) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hthetaPi
  have htrig := Real.sin_sq_add_cos_sq
    (liEvenCrossCriticalAtomAngle (1 / 4) q)
  have hsinSq :
      Real.sin (liEvenCrossCriticalAtomAngle (1 / 4) q) ^ 2 =
        (gamma / den) ^ 2 := by
    rw [hcos'] at htrig
    field_simp [hdenPos.ne'] at htrig ⊢
    nlinarith
  have hsin : Real.sin (liEvenCrossCriticalAtomAngle (1 / 4) q) =
      gamma / den := by
    have hrightPos : 0 < gamma / den := div_pos hgammaPos hdenPos
    nlinarith
  rw [liEvenCrossCriticalAtomAmplitude, hmass, hnode, hsin]
  change (1 / den) * (1 - (1 / 4) / den) / (gamma / den) =
    gamma / den
  field_simp [hdenPos.ne', hgammaPos.ne']
  dsimp [den]
  ring

theorem liEvenCrossOrderedEndpointAmplitude_pos (n : ℕ) :
    0 < liEvenCrossOrderedEndpointAmplitude n := by
  unfold liEvenCrossOrderedEndpointAmplitude
  exact div_pos (xiOrderedPositiveOrdinate_pos n) (by positivity)

theorem liEvenCrossOrderedEndpointAmplitude_le_inv (n : ℕ) :
    liEvenCrossOrderedEndpointAmplitude n ≤
      (xiOrderedPositiveOrdinate n)⁻¹ := by
  set gamma := xiOrderedPositiveOrdinate n
  have hgamma : 0 < gamma := xiOrderedPositiveOrdinate_pos n
  rw [liEvenCrossOrderedEndpointAmplitude]
  change gamma / (gamma ^ 2 + 1 / 4) ≤ gamma⁻¹
  rw [show gamma⁻¹ = gamma / gamma ^ 2 by
    field_simp [hgamma.ne']]
  exact div_le_div_of_nonneg_left hgamma.le (sq_pos_of_pos hgamma)
    (by norm_num)

theorem inv_le_two_mul_liEvenCrossOrderedEndpointAmplitude (n : ℕ) :
    (xiOrderedPositiveOrdinate n)⁻¹ ≤
      2 * liEvenCrossOrderedEndpointAmplitude n := by
  set gamma := xiOrderedPositiveOrdinate n
  have hgamma : 0 < gamma := xiOrderedPositiveOrdinate_pos n
  have hone : 1 < gamma := one_lt_xiOrderedPositiveOrdinate n
  rw [liEvenCrossOrderedEndpointAmplitude]
  change gamma⁻¹ ≤ 2 * (gamma / (gamma ^ 2 + 1 / 4))
  calc
    gamma⁻¹ = gamma / gamma ^ 2 := by field_simp [hgamma.ne']
    _ ≤ (2 * gamma) / (gamma ^ 2 + 1 / 4) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hgamma) (by positivity)]
      nlinarith [sq_pos_of_pos hgamma]
    _ = 2 * (gamma / (gamma ^ 2 + 1 / 4)) := by ring

/-- Ordered reciprocal Xi ordinates are `p`-summable for every `p > 1`. -/
theorem summable_xiOrderedPositiveOrdinate_inv_rpow
    {q : ℝ} (hq : 1 < q) :
    Summable (fun n : ℕ => (xiOrderedPositiveOrdinate n)⁻¹ ^ q) := by
  have hall := xiOrderedSignedPrimeOperator_memSchattenClass hq
  change Summable (fun n =>
    approxNumber xiOrderedSignedPrimeOperator n ^ q) at hall
  have heven := hall.comp_injective (i := fun n : ℕ => 2 * n) (by
    intro i j hij
    exact Nat.mul_left_cancel (by norm_num) hij)
  simpa [Function.comp_def, xiOrderedSignedPrimeOperator_approxNumber_even]
    using heven

theorem summable_liEvenCrossOrderedEndpointAmplitude_rpow
    {q : ℝ} (hq : 1 < q) :
    Summable (fun n : ℕ => liEvenCrossOrderedEndpointAmplitude n ^ q) := by
  refine Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (liEvenCrossOrderedEndpointAmplitude_pos n).le q)
    (fun n => Real.rpow_le_rpow
      (liEvenCrossOrderedEndpointAmplitude_pos n).le
      (liEvenCrossOrderedEndpointAmplitude_le_inv n) (by linarith))
    (summable_xiOrderedPositiveOrdinate_inv_rpow hq)

/-- The full endpoint amplitude packet is not absolutely summable. -/
theorem not_summable_liEvenCrossOrderedEndpointAmplitude :
    ¬ Summable liEvenCrossOrderedEndpointAmplitude := by
  intro hamp
  apply not_summable_routeKRVMQuantile_reciprocal
  have hactual : Summable (fun n : ℕ => (xiOrderedPositiveOrdinate n)⁻¹) :=
    Summable.of_nonneg_of_le
      (fun n => inv_nonneg.mpr (xiOrderedPositiveOrdinate_pos n).le)
      inv_le_two_mul_liEvenCrossOrderedEndpointAmplitude
      (hamp.mul_left 2)
  have hdiffAbs :=
    summable_abs_xiOrderedPositiveOrdinate_inv_sub_routeKRVMQuantile_inv
  have hdiff : Summable (fun n : ℕ =>
      (xiOrderedPositiveOrdinate n)⁻¹ - (routeKRVMQuantile n)⁻¹) := by
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using hdiffAbs
  have hmodel := hactual.sub hdiff
  exact hmodel.congr fun n => by ring

/-- Sharp critical-amplitude Schatten boundary: every exponent above one converges, while the
trace endpoint diverges. -/
theorem liEvenCrossOrderedEndpointAmplitude_schattenBoundary :
    (∀ q : ℝ, 1 < q →
      Summable (fun n : ℕ => liEvenCrossOrderedEndpointAmplitude n ^ q)) ∧
      ¬ Summable liEvenCrossOrderedEndpointAmplitude := by
  exact ⟨fun _ hq => summable_liEvenCrossOrderedEndpointAmplitude_rpow hq,
    not_summable_liEvenCrossOrderedEndpointAmplitude⟩

/-- **LI infinite-packet no-go.** No multiplicity-ordered realization of all positive Xi
ordinates by critical-line copies has an absolutely summable endpoint amplitude packet. -/
theorem not_exists_summable_liEvenCross_fullCriticalEndpointAmplitude :
    ¬ ∃ q : ℕ → XiCriticalLineResolventCopy,
      (∀ n : ℕ, ((q n).1.1 : ℂ).im = xiOrderedPositiveOrdinate n) ∧
      Summable (fun n : ℕ =>
        liEvenCrossCriticalAtomAmplitude (1 / 4) (q n)) := by
  rintro ⟨q, hordinate, hsum⟩
  apply not_summable_liEvenCrossOrderedEndpointAmplitude
  refine hsum.congr fun n => ?_
  have him : 0 < ((q n).1.1 : ℂ).im := by
    rw [hordinate n]
    exact xiOrderedPositiveOrdinate_pos n
  rw [liEvenCrossCriticalAtomAmplitude_oneFourth_eq_imaginary (q n) him,
    liEvenCrossOrderedEndpointAmplitude, hordinate n]

end

end RHTower
