import GaloisForLFunctions.RHTower.MobiusDivisorFirstPrimeCertificateObstruction
import GaloisForLFunctions.RHTower.MobiusDivisorLargePrimeOrientation

/-!
# Actual prime-grid minors retain the finite quotient profile

At cutoff N*a*b, exact homothety keeps the top product channel at quotient N.
The other three normalized channels approach the common unsigned mean as
both dilations grow. The joint normalized minor therefore has an exact limit
given by the deviation of the quotient-N profile from that mean.

The actual quotient twelve overshoots the mean, while quotient two lies below
it. The same cofinally large distinct prime pair has opposite signed-channel
minors at these two fully active cutoffs, each with a fixed linear margin.
This excludes either uniform prime-grid minor sign. It does not estimate the
complete signed pair sum or supply the native Route-P history floor.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower

local notation "c₀" => Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4

/-- The literal four-channel multiplicative minor at a finite cutoff. -/
def routePPrimeGridMinor (M a b : ℕ) : ℝ :=
  divisorUnsignedDilationChannel M 1 * divisorUnsignedDilationChannel M (a*b) -
    divisorUnsignedDilationChannel M a * divisorUnsignedDilationChannel M b

/-- The actual Möbius signs preserve the minor on a distinct-prime grid. -/
theorem routeP_prime_grid_minor_eq_signed (M : ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    routePPrimeGridMinor M p q =
      mobiusDivisorDilationChannel M 1 * mobiusDivisorDilationChannel M (p*q) -
        mobiusDivisorDilationChannel M p * mobiusDivisorDilationChannel M q := by
  have hcop := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))
  simp [routePPrimeGridMinor, mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_prime hq]

private lemma normalized_homothety (r N : ℕ) (hr : 0 < r) :
    divisorUnsignedDilationChannel (r*N) r / Real.sqrt (r*N : ℕ) =
      divisorUnsignedDilationChannel N 1 / Real.sqrt N := by
  have he := divisorUnsignedDilationChannel_mul r N 1
  simp only [Nat.mul_one] at he
  rw [he, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg r)]
  have hs : Real.sqrt (r:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hr)).ne'
  exact mul_div_mul_left _ _ hs

private lemma normalized_minor (N a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    routePPrimeGridMinor (N*a*b) a b / (N*a*b : ℕ) =
      (divisorUnsignedDilationChannel (N*a*b) 1 / Real.sqrt (N*a*b : ℕ)) *
        (divisorUnsignedDilationChannel N 1 / Real.sqrt N) -
      (divisorUnsignedDilationChannel (N*a) 1 / Real.sqrt (N*a : ℕ)) *
        (divisorUnsignedDilationChannel (N*b) 1 / Real.sqrt (N*b : ℕ)) := by
  have ht := normalized_homothety (a*b) N (Nat.mul_pos ha hb)
  have hl := normalized_homothety a (N*b) ha
  have hr := normalized_homothety b (N*a) hb
  have htop : a*b*N=N*a*b := by ac_rfl
  have hleft : a*(N*b)=N*a*b := by ac_rfl
  have hright : b*(N*a)=N*a*b := by ac_rfl
  rw [htop] at ht
  rw [hleft] at hl
  rw [hright] at hr
  unfold routePPrimeGridMinor
  calc
    _ = (divisorUnsignedDilationChannel (N*a*b) 1 / Real.sqrt (N*a*b : ℕ)) *
        (divisorUnsignedDilationChannel (N*a*b) (a*b) / Real.sqrt (N*a*b : ℕ)) -
        (divisorUnsignedDilationChannel (N*a*b) a / Real.sqrt (N*a*b : ℕ)) *
        (divisorUnsignedDilationChannel (N*a*b) b / Real.sqrt (N*a*b : ℕ)) := by
      rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, ← pow_two,
        Real.sq_sqrt (Nat.cast_nonneg _)]
    _ = _ := by rw [ht, hl, hr]; ring

/-- Joint dilation limit, retaining the original top quotient exactly. -/
theorem routeP_prime_grid_minor_limit {N : ℕ} (hN : 0 < N) :
    Tendsto (fun ab : ℕ × ℕ =>
      routePPrimeGridMinor (N*ab.1*ab.2) ab.1 ab.2 / (N*ab.1*ab.2 : ℕ))
      atTop (𝓝 (c₀ * (divisorUnsignedDilationChannel N 1 / Real.sqrt N - c₀))) := by
  have ha : Tendsto (fun ab : ℕ × ℕ => ab.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hb : Tendsto (fun ab : ℕ × ℕ => ab.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hNa : Tendsto (fun ab : ℕ × ℕ => N*ab.1) atTop atTop := by
    apply tendsto_atTop_mono' _ _ ha
    exact Eventually.of_forall fun ab => Nat.le_mul_of_pos_left _ hN
  have hNb : Tendsto (fun ab : ℕ × ℕ => N*ab.2) atTop atTop := by
    apply tendsto_atTop_mono' _ _ hb
    exact Eventually.of_forall fun ab => Nat.le_mul_of_pos_left _ hN
  have hNab := hNa.atTop_mul_atTop₀ hb
  have h := ((tendsto_divisorUnsignedDilationChannel_one_div_sqrt.comp hNab).mul_const
    (divisorUnsignedDilationChannel N 1 / Real.sqrt N)).sub
      ((tendsto_divisorUnsignedDilationChannel_one_div_sqrt.comp hNa).mul
        (tendsto_divisorUnsignedDilationChannel_one_div_sqrt.comp hNb))
  have hc : c₀ * (divisorUnsignedDilationChannel N 1 / Real.sqrt N) - c₀*c₀ =
      c₀ * (divisorUnsignedDilationChannel N 1 / Real.sqrt N - c₀) := by ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [ha.eventually (eventually_gt_atTop 0),
    hb.eventually (eventually_gt_atTop 0)] with ab hap hbp
  exact (normalized_minor N ab.1 ab.2 hap hbp).symm

private lemma mean_gt : (1/12:ℝ) < c₀ := by
  have h := divisorHyperbolaSmoothMean_gt_one_sixth
  unfold divisorHyperbolaSmoothMean at h
  linarith

/-- The quotient-twelve overshoot forces a positive minor with a linear margin. -/
theorem routeP_prime_grid_minor_positive_tail :
    ∃ δ : ℝ, 0 < δ ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ a b : ℕ, T ≤ a → T ≤ b →
      δ*(12*a*b : ℕ) < routePPrimeGridMinor (12*a*b) a b := by
  let L := c₀ * (divisorUnsignedDilationChannel 12 1 / Real.sqrt 12 - c₀)
  have hs : 0 < Real.sqrt (12:ℝ) := by positivity
  have hg : c₀+1/2000 ≤ divisorUnsignedDilationChannel 12 1 / Real.sqrt 12 :=
    (le_div_iff₀ hs).mpr divisorUnsignedDilationChannel_twelve_mean_overshoot
  have hL : 0 < L := mul_pos (by linarith [mean_gt]) (by linarith)
  have hlim : Tendsto (fun ab : ℕ × ℕ =>
      routePPrimeGridMinor (12*ab.1*ab.2) ab.1 ab.2 / (12*ab.1*ab.2 : ℕ))
      atTop (𝓝 L) := routeP_prime_grid_minor_limit (by norm_num)
  obtain ⟨ab₀, hab₀⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_gt_nhds (show L/2 < L by linarith)))
  refine ⟨L/2, by positivity, max 1 (max ab₀.1 ab₀.2), le_max_left _ _, ?_⟩
  intro a b ha hb
  have ha₀ : ab₀.1 ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans ha)
  have hb₀ : ab₀.2 ≤ b := (le_max_right _ _).trans ((le_max_right _ _).trans hb)
  have hap : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans ha)
  have hbp : 0 < b := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hb)
  have h := hab₀ (a,b) ⟨ha₀,hb₀⟩
  exact (lt_div_iff₀ (show (0:ℝ) < (12*a*b : ℕ) by positivity)).mp h

/-- A fully active quotient-two grid has the opposite sign with a linear margin. -/
theorem routeP_prime_grid_minor_negative_tail :
    ∃ δ : ℝ, 0 < δ ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ a b : ℕ, T ≤ a → T ≤ b →
      routePPrimeGridMinor (2*a*b) a b < -δ*(2*a*b : ℕ) := by
  let L := c₀ * (divisorUnsignedDilationChannel 2 1 / Real.sqrt 2 - c₀)
  have hs : 0 < Real.sqrt (2:ℝ) := by positivity
  have hg : divisorUnsignedDilationChannel 2 1 / Real.sqrt 2 ≤ (1/15:ℝ) :=
    (div_le_iff₀ hs).mpr (by simpa only [Nat.cast_ofNat, div_eq_mul_inv, one_mul, mul_comm] using
      divisorUnsignedDilationChannel_one_le_fifteenth_of_le_five (by norm_num : 2 ≤ 5))
  have hL : L < 0 := mul_neg_of_pos_of_neg (by linarith [mean_gt]) (by linarith [mean_gt])
  have hlim : Tendsto (fun ab : ℕ × ℕ =>
      routePPrimeGridMinor (2*ab.1*ab.2) ab.1 ab.2 / (2*ab.1*ab.2 : ℕ))
      atTop (𝓝 L) := routeP_prime_grid_minor_limit (by norm_num)
  obtain ⟨ab₀, hab₀⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_lt_nhds (show L < L/2 by linarith)))
  refine ⟨-L/2, by linarith only [hL], max 1 (max ab₀.1 ab₀.2), le_max_left _ _, ?_⟩
  intro a b ha hb
  have ha₀ : ab₀.1 ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans ha)
  have hb₀ : ab₀.2 ≤ b := (le_max_right _ _).trans ((le_max_right _ _).trans hb)
  have hap : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans ha)
  have hbp : 0 < b := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hb)
  have h := (div_lt_iff₀ (show (0:ℝ) < (2*a*b : ℕ) by positivity)).mp
    (hab₀ (a,b) ⟨ha₀,hb₀⟩)
  simpa only [neg_div, neg_neg] using h

/-- Cofinal actual distinct-prime grids have both opposite signed minor phases. -/
theorem routeP_prime_grid_opposite_minors_cofinal :
    ∃ δpos δneg : ℝ, 0 < δpos ∧ 0 < δneg ∧ ∀ N : ℕ,
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N ≤ p ∧ p < q ∧
        δpos*(12*p*q : ℕ) <
          mobiusDivisorDilationChannel (12*p*q) 1 * mobiusDivisorDilationChannel (12*p*q) (p*q) -
            mobiusDivisorDilationChannel (12*p*q) p * mobiusDivisorDilationChannel (12*p*q) q ∧
        mobiusDivisorDilationChannel (2*p*q) 1 * mobiusDivisorDilationChannel (2*p*q) (p*q) -
          mobiusDivisorDilationChannel (2*p*q) p * mobiusDivisorDilationChannel (2*p*q) q <
            -δneg*(2*p*q : ℕ) := by
  obtain ⟨δpos, hδpos, Tpos, _, hTpos⟩ := routeP_prime_grid_minor_positive_tail
  obtain ⟨δneg, hδneg, Tneg, _, hTneg⟩ := routeP_prime_grid_minor_negative_tail
  refine ⟨δpos, δneg, hδpos, hδneg, ?_⟩
  intro N
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N (max Tpos Tneg))
  obtain ⟨q, hpq, hq⟩ := Nat.exists_infinite_primes (p+1)
  have hpq' : p ≠ q := by omega
  refine ⟨p, q, hp, hq, by omega, by omega, ?_, ?_⟩
  · rw [← routeP_prime_grid_minor_eq_signed _ hp hq hpq']
    exact hTpos p q (by omega) (by omega)
  · rw [← routeP_prime_grid_minor_eq_signed _ hp hq hpq']
    exact hTneg p q (by omega) (by omega)

end RHTower
