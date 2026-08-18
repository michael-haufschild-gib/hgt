import GaloisForLFunctions.RHTower.ProlateWindowPairingConst
import GaloisForLFunctions.RHTower.OscillatorEvenRigidity

/-!
# The limiting window pairing against a Hermite function does not vanish

At an even rung the Hermite function is, after normalising its value at the origin, exactly the
limit oscillator profile: both solve `v″ = (ξ² − (2n+1))v` with `v(0)=1`, `v′(0)=0`, and second-order
uniqueness identifies them.  The limiting window pairing is therefore the Hermite value at the
origin times the profile's window square mass, which is positive.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace RHTower

/-- An even Hermite function has vanishing derivative at the origin. -/
theorem deriv_hermiteFun_at_zero_of_even {n : ℕ} (hn : Even n) : deriv (hermiteFun n) 0 = 0 := by
  have hfun : (fun y : ℝ => hermiteFun n (-y)) = hermiteFun n := funext (even_hermiteFun hn)
  have hneg : HasDerivAt (fun z : ℝ => -z) (-1 : ℝ) 0 := (hasDerivAt_id (0 : ℝ)).neg
  have hcomp : HasDerivAt (fun y : ℝ => hermiteFun n (-y))
      (-deriv (hermiteFun n) (-0)) 0 :=
    ((hasDerivAt_hermiteFun n (-0)).comp 0 hneg).congr_deriv (by ring)
  rw [hfun] at hcomp
  have huniq := hcomp.unique (hasDerivAt_hermiteFun n 0)
  rw [neg_zero] at huniq
  linarith

/-- An even Hermite function does not vanish at the origin. -/
theorem hermiteFun_zero_ne_zero {n : ℕ} (hn : Even n) : hermiteFun n 0 ≠ 0 := by
  intro h0
  rcases hermiteFun_nontrivial n 0 with h | h
  · exact h h0
  · exact h (deriv_hermiteFun_at_zero_of_even hn)

/-- **The normalised even Hermite function is the limit oscillator profile at its rung.** -/
theorem hermiteFun_div_eq_oscProfile {n : ℕ} (hn : Even n) :
    (fun x : ℝ => hermiteFun n x / hermiteFun n 0) = oscProfile (2 * (n : ℝ) + 1) := by
  have h0 : hermiteFun n 0 ≠ 0 := hermiteFun_zero_ne_zero hn
  refine eq_oscProfile (v' := fun x => deriv (hermiteFun n) x / hermiteFun n 0) ?_ ?_ ?_ ?_
  · intro x
    exact (hasDerivAt_hermiteFun n x).div_const _
  · intro x
    have h := (hasDerivAt_deriv_hermiteFun n x).div_const (hermiteFun n 0)
    refine h.congr_deriv ?_
    rw [oscPotential, hermiteRungP]
    field_simp
  · field_simp
  · rw [deriv_hermiteFun_at_zero_of_even hn]
    simp

/-- **The limiting window pairing is nonzero.** -/
theorem integral_oscProfile_mul_hermiteFun_ne_zero {n : ℕ} (hn : Even n) {K : ℝ} (hK : 0 < K) :
    (∫ x in (-K)..K, oscProfile (2 * (n : ℝ) + 1) x * hermiteFun n x) ≠ 0 := by
  have h0 : hermiteFun n 0 ≠ 0 := hermiteFun_zero_ne_zero hn
  have hpt : ∀ x : ℝ, hermiteFun n x
      = hermiteFun n 0 * oscProfile (2 * (n : ℝ) + 1) x := by
    intro x
    have h := congrFun (hermiteFun_div_eq_oscProfile hn) x
    field_simp at h
    linarith [h]
  have hrw : (∫ x in (-K)..K, oscProfile (2 * (n : ℝ) + 1) x * hermiteFun n x)
      = hermiteFun n 0
        * ∫ x in (-K)..K, oscProfile (2 * (n : ℝ) + 1) x * oscProfile (2 * (n : ℝ) + 1) x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [hpt x]
    ring
  rw [hrw]
  exact mul_ne_zero h0 (integral_oscProfile_mul_self_pos _ hK).ne'


/-- **The eventual window-pairing floor.**  Once the rescaled separation constant approaches an even
rung, the window pairing of the profile against the Hermite function at that rung stays above half
its nonzero limit. -/
theorem eventually_abs_window_pairing_ge {ι : Type*} {L : Filter ι}
    {mu c : ι → ℝ} {K B : ℝ} {n : ℕ} {u u' u'' : ι → ℝ → ℝ}
    (hn : Even n) (hK : 0 < K)
    (hu : ∀ i x, HasDerivAt (u i) (u' i x) x) (hu' : ∀ i x, HasDerivAt (u' i) (u'' i x) x)
    (heu : ∀ i, Function.Even (u i))
    (hev : ∀ᶠ i in L, 0 < c i ∧ 2 * K ^ 2 ≤ c i ∧
      (∀ x ∈ Icc (0 : ℝ) K, u'' i x = rescaledProlateP (c i) (mu i) x * u i x
        + rescaledProlateQ (c i) x * u' i x) ∧
      (∀ x ∈ Icc (0 : ℝ) K, max |u i x| |u' i x| ≤ B) ∧ u i 0 = 1 ∧ u' i 0 = 0)
    (hmu : Tendsto mu L (𝓝 (2 * (n : ℝ) + 1))) (hc : Tendsto c L atTop) :
    ∀ᶠ i in L,
      |∫ x in (-K)..K, oscProfile (2 * (n : ℝ) + 1) x * hermiteFun n x| / 2
        ≤ |∫ x in (-K)..K, u i x * hermiteFun n x| := by
  have hlim := tendsto_prolateWindowPairing_const (g := hermiteFun n) hK
    (continuous_hermiteFun n) hu hu' heu hev hmu hc
  have habs := hlim.abs
  have hne := integral_oscProfile_mul_hermiteFun_ne_zero hn hK
  have hpos : 0 < |∫ x in (-K)..K, oscProfile (2 * (n : ℝ) + 1) x * hermiteFun n x| :=
    abs_pos.2 hne
  have hhalf : |∫ x in (-K)..K, oscProfile (2 * (n : ℝ) + 1) x * hermiteFun n x| / 2
      < |∫ x in (-K)..K, oscProfile (2 * (n : ℝ) + 1) x * hermiteFun n x| := by
    linarith
  exact (habs.eventually (eventually_gt_nhds hhalf)).mono fun i hi => hi.le

end RHTower

end
