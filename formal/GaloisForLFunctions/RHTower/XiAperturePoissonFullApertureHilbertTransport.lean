import GaloisForLFunctions.RHTower.XiApertureResponseGainPrimeRenormalization
import GaloisForLFunctions.RHTower.XiTransversePrimeSourceHilbertMetric

/-!
# Full-aperture Hilbert transport and its compactness phase

The unit-aperture theorem identifies the unique identity-like boundary gain.  This file computes
the actual transport gain at every positive integral valuation aperture against the true
continuous-aperture Möbius--Szegő metric.

For `q=p⁻¹` and `r=p⁻ᵃ`, the exact squared gain is

`a² (r/q)² (1+q)² (1+r)/(1-r)³`.

At `a=1` this is the noncompact gain `((1+q)/(1-q))³`.  At every `a≥2`, the extra ratio
`(r/q)²` makes the all-prime gain summable, with the uniform pointwise bound `27 a²/p²`.
Thus aperture one is the unique noncompact boundary of the true valuation-depth transport; every
deeper integral aperture is compactified into trace-class squared gain.  The fused response itself
remains an all-prime Hilbert vector at every positive aperture.

This is a source-depth phase theorem, not the missing off-diagonal cross-aperture coupling and not
an RH proof.
-/

namespace RHTower

noncomputable section

open scoped BigOperators

/-- Exact squared gain from the valuation-fused Poisson response to the true aperture ray. -/
def xiAperturePrimeFusedResponseGainSq (a : ℕ) (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiTransversePrimeApertureDiskNode a p
  (a : ℝ) ^ 2 * (r / q) ^ 2 * (1 + q) ^ 2 * (1 + r) / (1 - r) ^ 3

private theorem xiTransversePrimeApertureDiskNode_eq_one_pow
    (a : ℕ) (p : Nat.Primes) :
    xiTransversePrimeApertureDiskNode a p =
      xiTransversePrimeApertureDiskNode 1 p ^ a := by
  simpa using xiTransversePrimeApertureDiskNode_mul 1 a p

private theorem xiPrimeValuationGeometricNode_nat_eq_transverse
    (a : ℕ) (p : Nat.Primes) :
    xiPrimeValuationGeometricNode (a : ℝ) p =
      xiTransversePrimeApertureDiskNode a p := by
  unfold xiPrimeValuationGeometricNode xiTransversePrimeApertureDiskNode
  norm_num

private theorem xiMobiusContinuousApertureDiskNode_nat_eq_transverse
    (a : ℕ) (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode (a : ℝ) p =
      xiTransversePrimeApertureDiskNode a p := by
  unfold xiMobiusContinuousApertureDiskNode xiTransversePrimeApertureDiskNode
  norm_num

private theorem xiTransversePrimeApertureDiskNode_one_le_half
    (p : Nat.Primes) :
    xiTransversePrimeApertureDiskNode 1 p ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  rw [xiTransversePrimeApertureDiskNode_one_eq_inv]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2)

/-- Exact local energy identity at every positive integral aperture. -/
theorem poissonPrimeValuationFusedHalfDensity_nat_sq_eq_gain_mul_trueApertureMetric
    {a : ℕ} (ha : 0 < a) (p : Nat.Primes) :
    poissonPrimeValuationFusedHalfDensity (a : ℝ) p ^ 2 =
      xiAperturePrimeFusedResponseGainSq a p *
        xiMobiusPrimeContinuousApertureSzegoMetric (a : ℝ) (a : ℝ) p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiTransversePrimeApertureDiskNode a p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiTransversePrimeApertureDiskNode_pos a p
  have hr1 : r < 1 := xiTransversePrimeApertureDiskNode_lt_one ha p
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hqne : q ≠ 0 := hq0.ne'
  have hrplus : 1 + r ≠ 0 := by linarith
  have hrminus : 1 - r ≠ 0 := by linarith
  rw [poissonPrimeValuationFusedHalfDensity_eq_geometric haR,
    xiMobiusPrimeContinuousApertureSzegoMetric_self haR]
  rw [xiPrimeValuationGeometricNode_nat_eq_transverse,
    xiMobiusContinuousApertureDiskNode_nat_eq_transverse]
  change (((a : ℝ) * r * (1 - r)⁻¹) ^ 2) =
    ((a : ℝ) ^ 2 * (r / q) ^ 2 * (1 + q) ^ 2 * (1 + r) /
      (1 - r) ^ 3) * ((q / (1 + q)) ^ 2 * ((1 - r) / (1 + r)))
  field_simp [hqne, hrplus, hrminus]

/-- The full-aperture squared gain is strictly positive. -/
theorem xiAperturePrimeFusedResponseGainSq_pos
    {a : ℕ} (ha : 0 < a) (p : Nat.Primes) :
    0 < xiAperturePrimeFusedResponseGainSq a p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiTransversePrimeApertureDiskNode a p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiTransversePrimeApertureDiskNode_pos a p
  have hr1 : r < 1 := xiTransversePrimeApertureDiskNode_lt_one ha p
  rw [xiAperturePrimeFusedResponseGainSq]
  change 0 < (a : ℝ) ^ 2 * (r / q) ^ 2 * (1 + q) ^ 2 * (1 + r) /
    (1 - r) ^ 3
  positivity

/-- The full gain specializes exactly to the previously proved unit-aperture gain. -/
theorem xiAperturePrimeFusedResponseGainSq_one (p : Nat.Primes) :
    xiAperturePrimeFusedResponseGainSq 1 p =
      xiApertureOnePrimeFusedResponseGainSq p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  rw [xiAperturePrimeFusedResponseGainSq,
    xiApertureOnePrimeFusedResponseGainSq]
  norm_num only [Nat.cast_one, one_pow]
  dsimp [q] at hq0 hq1 ⊢
  field_simp [hq0.ne', (sub_pos.mpr hq1).ne']

/-- Every deeper integral aperture has a prime-square gain majorant. -/
theorem xiAperturePrimeFusedResponseGainSq_le_invSq
    {a : ℕ} (ha : (2 : ℕ) ≤ a) (p : Nat.Primes) :
    xiAperturePrimeFusedResponseGainSq a p ≤
      27 * (a : ℝ) ^ 2 * xiTransversePrimeApertureDiskNode 1 p ^ 2 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a = k + 2 := ⟨a - 2, by omega⟩
  subst a
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiTransversePrimeApertureDiskNode (k + 2) p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hqhalf : q ≤ 1 / 2 := xiTransversePrimeApertureDiskNode_one_le_half p
  have hrpow : r = q ^ (k + 2) := by
    exact xiTransversePrimeApertureDiskNode_eq_one_pow (k + 2) p
  have hr0 : 0 < r := xiTransversePrimeApertureDiskNode_pos (k + 2) p
  have hrle : r ≤ q := by
    rw [hrpow, show k + 2 = (k + 1) + 1 by omega, pow_succ]
    simpa using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (n := k + 1) hq0.le hq1.le) hq0.le
  have hrhalf : r ≤ 1 / 2 := hrle.trans hqhalf
  have hratio : r / q = q ^ (k + 1) := by
    rw [hrpow, show k + 2 = (k + 1) + 1 by omega, pow_succ]
    field_simp [hq0.ne']
  have hratio0 : 0 ≤ r / q := div_nonneg hr0.le hq0.le
  have hratiole : r / q ≤ q := by
    rw [hratio, pow_succ]
    simpa using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (n := k) hq0.le hq1.le) hq0.le
  have hratioSq : (r / q) ^ 2 ≤ q ^ 2 :=
    (sq_le_sq₀ hratio0 hq0.le).2 hratiole
  have hqplus : 1 + q ≤ 3 / 2 := by linarith
  have hrplus : 1 + r ≤ 3 / 2 := by linarith
  have hrminus : 1 / 2 ≤ 1 - r := by linarith
  rw [xiAperturePrimeFusedResponseGainSq]
  change ((k + 2 : ℕ) : ℝ) ^ 2 * (r / q) ^ 2 * (1 + q) ^ 2 * (1 + r) /
      (1 - r) ^ 3 ≤ 27 * ((k + 2 : ℕ) : ℝ) ^ 2 * q ^ 2
  calc
    ((k + 2 : ℕ) : ℝ) ^ 2 * (r / q) ^ 2 * (1 + q) ^ 2 * (1 + r) /
        (1 - r) ^ 3 ≤
      ((k + 2 : ℕ) : ℝ) ^ 2 * q ^ 2 * (3 / 2 : ℝ) ^ 2 * (3 / 2 : ℝ) /
        (1 / 2 : ℝ) ^ 3 := by gcongr
    _ = 27 * ((k + 2 : ℕ) : ℝ) ^ 2 * q ^ 2 := by ring

/-- At every integral aperture at least two, the squared gain is trace class. -/
theorem summable_xiAperturePrimeFusedResponseGainSq_of_two_le
    {a : ℕ} (ha : (2 : ℕ) ≤ a) :
    Summable (xiAperturePrimeFusedResponseGainSq a) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  have hnodes : Summable (fun p : Nat.Primes =>
      xiTransversePrimeApertureDiskNode 1 p ^ 2) := by
    simpa [xiTransversePrimeApertureDiskNode_one_eq_inv, inv_pow] using hprime
  exact Summable.of_nonneg_of_le
    (fun p => (xiAperturePrimeFusedResponseGainSq_pos (by omega) p).le)
    (xiAperturePrimeFusedResponseGainSq_le_invSq ha)
    (hnodes.mul_left (27 * (a : ℝ) ^ 2))

/-- The unit-aperture squared gain is not summable. -/
theorem not_summable_xiAperturePrimeFusedResponseGainSq_one :
    ¬ Summable (xiAperturePrimeFusedResponseGainSq 1) := by
  intro hsum
  have hcorr : Summable (fun p : Nat.Primes =>
      xiAperturePrimeFusedResponseGainSq 1 p - 1) := by
    exact Summable.of_nonneg_of_le
      (fun p => by
        rw [xiAperturePrimeFusedResponseGainSq_one]
        exact (mul_nonneg (by norm_num)
          (xiTransversePrimeApertureDiskNode_pos 1 p).le).trans
            (six_mul_diskNode_le_xiApertureOnePrimeFusedResponseGainSq_sub_one p))
      (fun p => by linarith)
      hsum
  exact not_summable_xiApertureOnePrimeFusedResponseGainSq_sub_one
    (by simpa only [xiAperturePrimeFusedResponseGainSq_one] using hcorr)

/-- Exact compactness phase: among positive integral apertures, the squared gain is summable
exactly beyond the unit boundary. -/
theorem summable_xiAperturePrimeFusedResponseGainSq_iff
    {a : ℕ} (ha : 0 < a) :
    Summable (xiAperturePrimeFusedResponseGainSq a) ↔ 2 ≤ a := by
  constructor
  · intro hsum
    by_contra hnot
    have ha1 : a = 1 := by omega
    subst a
    exact not_summable_xiAperturePrimeFusedResponseGainSq_one hsum
  · exact summable_xiAperturePrimeFusedResponseGainSq_of_two_le

/-- The valuation-fused response is an all-prime Hilbert vector at every positive integral
aperture. -/
theorem summable_poissonPrimeValuationFusedHalfDensity_nat_sq
    {a : ℕ} (ha : 0 < a) :
    Summable (fun p : Nat.Primes =>
      poissonPrimeValuationFusedHalfDensity (a : ℝ) p ^ 2) := by
  rcases eq_or_lt_of_le (show 1 ≤ a by omega) with ha1 | ha2
  · have : a = 1 := by omega
    subst a
    simpa using summable_poissonPrimeValuationFusedHalfDensity_one_sq
  · have hgain := summable_xiAperturePrimeFusedResponseGainSq_of_two_le ha2
    exact Summable.of_nonneg_of_le
      (fun p => sq_nonneg _)
      (fun p => by
        rw [poissonPrimeValuationFusedHalfDensity_nat_sq_eq_gain_mul_trueApertureMetric ha]
        have hmetric := xiMobiusPrimeContinuousApertureSzegoMetric_self_le_invSq
          (show (0 : ℝ) < a by exact_mod_cast ha) p
        have hqhalf := xiTransversePrimeApertureDiskNode_one_le_half p
        have hq0 := (xiTransversePrimeApertureDiskNode_pos 1 p).le
        have hmetricOne :
            xiMobiusPrimeContinuousApertureSzegoMetric (a : ℝ) (a : ℝ) p ≤ 1 := by
          calc
            xiMobiusPrimeContinuousApertureSzegoMetric (a : ℝ) (a : ℝ) p ≤
                xiTransversePrimeApertureDiskNode 1 p ^ 2 := hmetric
            _ ≤ 1 := by
              simpa only [one_pow] using
                (sq_le_sq₀ hq0 (by norm_num : (0 : ℝ) ≤ 1)).2
                  (hqhalf.trans (by norm_num))
        exact mul_le_of_le_one_right
          (xiAperturePrimeFusedResponseGainSq_pos ha p).le hmetricOne)
      hgain

/-- **Exact-recovery/trace-class packet phase.**  A finite integral aperture packet has complete
prime-jet dual recovery after every finite prime deletion and trace-class squared transport gain
in every channel exactly when its labels are collision-free and all lie beyond the unique
noncompact unit-aperture boundary. -/
theorem
    xiTransversePrimeJetApertureCofiniteHilbertReconstruction_and_traceClassGain_iff
    {N : ℕ} (shift : Fin N → ℕ) (m : ℕ) :
    XiTransversePrimeJetApertureCofiniteHilbertReconstruction shift m ∧
        (∀ j, Summable (xiAperturePrimeFusedResponseGainSq (shift j))) ↔
      Function.Injective shift ∧ ∀ j, 2 ≤ shift j := by
  rw [
    xiTransversePrimeJetApertureCofiniteHilbertReconstruction_iff_injective_ne_zero]
  constructor
  · rintro ⟨⟨hinjective, hnonzero⟩, hsummable⟩
    refine ⟨hinjective, fun j => ?_⟩
    exact
      (summable_xiAperturePrimeFusedResponseGainSq_iff
        (Nat.pos_of_ne_zero (hnonzero j))).1 (hsummable j)
  · rintro ⟨hinjective, htwo⟩
    exact ⟨⟨hinjective, fun j =>
      Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (htwo j))⟩,
      fun j => summable_xiAperturePrimeFusedResponseGainSq_of_two_le (htwo j)⟩

end

end RHTower
