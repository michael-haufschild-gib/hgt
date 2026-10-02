import GaloisForLFunctions.RHTower.MobiusFactorCountEulerGrowth
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Full signed dominance in factor-count interpolation

At real part three quarters, the highest integer Euler parameter dominates
all lower parameters on the moving height sector. A uniform log-modulus gap
pays every binomial interpolation coefficient. Their complete relative norm
is bounded by a geometric sum whose ratio tends to zero.

Consequently the complete signed interpolation, not just one selected term,
has norm at least half the exponential Euler-growth lower bound. This is an
unconditional theorem for finite Euler completions, uniformly in every prime
truncation covering the central range.

The theorem does not bound the signed Mellin inversion or its pole contribution.
Those can cancel despite large absolute vertical values. No RH conclusion or
complete Möbius-energy ceiling follows here.
-/

noncomputable section
namespace RHTower
open Filter Topology

local notation "L" => mobiusFactorCountLogModulus

private lemma eventually_low_loss_small (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ D : ℝ in atTop, C*D^(6/5 : ℝ) ≤ D^(4/3 : ℝ)/(8192*Real.log D) := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<2/15)).tendsto_div_nhds_zero
  have hb := hlim.eventually (gt_mem_nhds (by positivity : (0:ℝ)<1/(8192*(C+1))))
  filter_upwards [hb, eventually_gt_atTop (1:ℝ)] with D hsmall hD
  have hD0 : 0 < D := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hp : 0 < D^(2/15 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hs := (div_le_iff₀ hp).mp hsmall.le
  have hs' : Real.log D*(8192*(C+1)) ≤ D^(2/15 : ℝ) := by
    have he : 1/(8192*(C+1))*D^(2/15 : ℝ) = D^(2/15 : ℝ)/(8192*(C+1)) := by ring
    rw [he] at hs
    exact (le_div_iff₀ (by positivity : (0:ℝ)<8192*(C+1))).mp hs
  have hm := mul_le_mul_of_nonneg_right hs' (Real.rpow_nonneg hD0.le (6/5:ℝ))
  have he : D^(2/15 : ℝ)*D^(6/5 : ℝ) = D^(4/3 : ℝ) := by
    rw [← Real.rpow_add hD0]
    norm_num
  rw [he] at hm
  apply (le_div_iff₀ (by positivity : (0:ℝ)<8192*Real.log D)).mpr
  nlinarith [Real.rpow_nonneg hD0.le (6/5:ℝ)]

private lemma increment {N : ℕ} {t u v C : ℝ} (huv : u ≤ v)
    (hd : ∀ a ∈ Set.Icc u v, DifferentiableAt ℝ (fun b : ℝ => L N b t) a ∧
      C ≤ deriv (fun b : ℝ => L N b t) a) :
    C*(v-u) ≤ L N v t - L N u t := by
  rcases eq_or_lt_of_le huv with he | hl
  · rw [he]; simp
  obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope (fun b : ℝ => L N b t) hl
    (fun a ha => (hd a ha).1.continuousAt.continuousWithinAt)
    (fun a ha => (hd a ⟨ha.1.le, ha.2.le⟩).1.differentiableWithinAt)
  have hb := (hd c ⟨hc.1.le, hc.2.le⟩).2
  rw [he] at hb
  exact (le_div_iff₀ (sub_pos.mpr hl)).mp hb

/-- One uniform gap controls every lower integer parameter, with all prime factors retained. -/
theorem eventually_mobiusFactorCountLogModulus_gap :
    ∀ᶠ D : ℝ in atTop, ∀ t : ℝ,
      7*Real.pi/(16*Real.log D) ≤ t → t ≤ 15*Real.pi/(32*Real.log D) →
      ∀ j : ℕ, (j:ℝ) ≤ D → ∀ N : ℕ, ⌊2*D^(4/3 : ℝ)⌋₊ ≤ N →
        (D-j)*D^(1/3 : ℝ)/(8192*Real.log D) ≤ L N D t - L N j t := by
  obtain ⟨B, hB, hlow⟩ := eventually_mobiusFactorCountLogModulus_abs_le
  filter_upwards [eventually_mobiusFactorCountLogModulus_derivative_lower,
    eventually_mobiusFactorCountLogModulus_growth, hlow,
    eventually_low_loss_small (B+24) (by positivity), eventually_gt_atTop (1:ℝ)]
    with D hderivD hgrowth hlowD hloss hD
  intro t htLo htHi j hj N hN
  have hD0 : 0 < D := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hD
  have ht0 : 0 ≤ t := (by positivity : 0 ≤ 7*Real.pi/(16*Real.log D)).trans htLo
  have hAgt : 1 < D^(9/10 : ℝ) := Real.one_lt_rpow hD (by norm_num)
  have hderiv : ∀ a ∈ Set.Icc (D^(9/10 : ℝ)) D,
      DifferentiableAt ℝ (fun b : ℝ => L N b t) a ∧
      a^(1/3 : ℝ)/(512*Real.log a) ≤ deriv (fun b : ℝ => L N b t) a := by
    intro a ha
    apply hderivD a t ha.1 ha.2 htLo htHi N
    apply le_trans _ hN
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [ha.1]) ha.2 (by norm_num)) (by norm_num)
  have hpow : D*D^(1/3 : ℝ) = D^(4/3 : ℝ) := by
    calc
      _ = D^(1:ℝ)*D^(1/3:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hD0]; norm_num
  by_cases hjA : (j:ℝ) ≤ D^(9/10 : ℝ)
  · have hjbound : L N j t ≤ (B+24)*D^(6/5 : ℝ) := by
      by_cases hj0 : j=0
      · subst j
        simp only [Nat.cast_zero, mobiusFactorCountLogModulus, zero_mul, Complex.ofReal_zero,
          norm_one, Real.log_one, add_zero, Finset.sum_const_zero]
        positivity
      · have hj1 : (1:ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
        have ha := (abs_le.mp (hlowD j t hj1 hj ht0 htHi N)).2
        have hA : (D^(9/10 : ℝ))^(4/3:ℝ) = D^(6/5:ℝ) := by
          rw [← Real.rpow_mul hD0.le]; norm_num
        have hje := Real.rpow_le_rpow (Nat.cast_nonneg j) hjA (by norm_num : (0:ℝ)≤4/3)
        rw [hA] at hje
        have hjle : (j:ℝ) ≤ D^(6/5 : ℝ) := hjA.trans
          (Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num))
        nlinarith [mul_le_mul_of_nonneg_left hjle hB]
    have hg := hgrowth t htLo htHi N hN
    have he : D^(4/3:ℝ)/(4096*Real.log D) = 2*(D^(4/3:ℝ)/(8192*Real.log D)) := by ring
    rw [he] at hg
    have htop : (D-j)*D^(1/3:ℝ)/(8192*Real.log D) ≤ D^(4/3:ℝ)/(8192*Real.log D) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [← hpow]
      exact mul_le_mul_of_nonneg_right (by linarith [(Nat.cast_nonneg j : (0:ℝ)≤j)]) (by positivity)
    linarith
  · have hAj : D^(9/10:ℝ) ≤ (j:ℝ) := le_of_not_ge hjA
    let m : ℝ := (D+j)/2
    have hjm : (j:ℝ) ≤ m := by dsimp [m]; linarith
    have hmD : m ≤ D := by dsimp [m]; linarith
    have hmhalf : D/2 ≤ m := by dsimp [m]; linarith [(Nat.cast_nonneg j : (0:ℝ)≤j)]
    have hfirst : 0 ≤ L N m t - L N j t := by
      have hh := increment (N := N) (t := t) (C := 0) hjm ?_
      · simpa using hh
      intro a ha
      have hd := hderiv a ⟨hAj.trans ha.1, ha.2.trans hmD⟩
      have ha1 : 1 < a := hAgt.trans_le (hAj.trans ha.1)
      have hla : 0 < Real.log a := Real.log_pos ha1
      have ha0 : 0 < a := by linarith
      exact ⟨hd.1, (by positivity : 0 ≤ a^(1/3:ℝ)/(512*Real.log a)).trans hd.2⟩
    have hsecond : D^(1/3:ℝ)/(1024*Real.log D)*(D-m) ≤ L N D t - L N m t := by
      apply increment hmD
      intro a ha
      have hd := hderiv a ⟨(hAj.trans hjm).trans ha.1, ha.2⟩
      refine ⟨hd.1, le_trans ?_ hd.2⟩
      have ha1 : 1 < a := hAgt.trans_le ((hAj.trans hjm).trans ha.1)
      have ha0 : 0 < a := by linarith
      have hla : 0 < Real.log a := Real.log_pos ha1
      have hlD := Real.log_le_log ha0 ha.2
      have hpowA : D^(1/3:ℝ) ≤ 2*a^(1/3:ℝ) := by
        have hDa : D ≤ 2*a := by linarith [ha.1]
        have hh := Real.rpow_le_rpow hD0.le hDa (by norm_num : (0:ℝ)≤1/3)
        rw [Real.mul_rpow (by norm_num) ha0.le] at hh
        have htwo : (2:ℝ)^(1/3:ℝ) ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
            (by norm_num : (1/3:ℝ)≤1)
        exact hh.trans (mul_le_mul_of_nonneg_right htwo (by positivity))
      calc
        _ ≤ (2*a^(1/3:ℝ))/(1024*Real.log D) := div_le_div_of_nonneg_right hpowA (by positivity)
        _ = a^(1/3:ℝ)/(512*Real.log D) := by ring
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have he : D^(1/3:ℝ)/(1024*Real.log D)*(D-m) =
        4*((D-j)*D^(1/3:ℝ)/(8192*Real.log D)) := by dsimp [m]; ring
    rw [he] at hsecond
    have hnonneg : 0 ≤ (D-j)*D^(1/3:ℝ)/(8192*Real.log D) := by positivity
    linarith

private def decayRate (D : ℝ) : ℝ := D^(1/3 : ℝ)/(8192*Real.log D)
private def decayRatio (D : ℝ) : ℝ := (D+1)*Real.exp (-decayRate D)

private lemma eventually_decayRate_ge_two_log :
    ∀ᶠ D : ℝ in atTop, 2*Real.log D ≤ decayRate D := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/6)).tendsto_div_nhds_zero
  have hb := hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/128))
  filter_upwards [hb, eventually_gt_atTop (1:ℝ)] with D hsmall hD
  have hD0 : 0 < D := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hp : 0 < D^(1/6:ℝ) := Real.rpow_pos_of_pos hD0 _
  have hs := (div_le_iff₀ hp).mp hsmall.le
  have hm : 0 ≤ (D^(1/6:ℝ)-128*Real.log D)*(D^(1/6:ℝ)+128*Real.log D) :=
    mul_nonneg (by linarith) (by positivity)
  have he : (D^(1/6:ℝ))^2 = D^(1/3:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]
    norm_num
  unfold decayRate
  apply (le_div_iff₀ (by positivity : (0:ℝ)<8192*Real.log D)).mpr
  nlinarith [he]

private lemma eventually_decayRatio_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, 0 ≤ decayRatio D ∧ decayRatio D ≤ ε := by
  filter_upwards [eventually_decayRate_ge_two_log, eventually_gt_atTop (1:ℝ),
    eventually_ge_atTop (2/ε)] with D hrate hD hlarge
  have hD0 : 0 < D := by linarith
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hrate)
  have he : Real.exp (-(2*Real.log D)) = 1/D^2 := by
    rw [show -(2*Real.log D) = -(Real.log (D^2)) by rw [Real.log_pow]; norm_num,
      Real.exp_neg, Real.exp_log (by positivity)]
    exact (one_div _).symm
  rw [he] at hexp
  have hratio : decayRatio D ≤ 2/D := by
    unfold decayRatio
    calc
      _ ≤ (D+1)*(1/D^2) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (D+1)/D^2 := by ring
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity : (0:ℝ)<D^2) hD0).mpr
        nlinarith
  refine ⟨by unfold decayRatio; positivity, hratio.trans ?_⟩
  have hlarge' := (div_le_iff₀ hε).mp hlarge
  apply (div_le_iff₀ hD0).mpr
  nlinarith

private lemma sum_geometric_shift_le {r : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1/2) (D : ℕ) :
    (∑ i ∈ Finset.range D, r^(i+1)) ≤ 2*r := by
  have hr1 : r ≠ 1 := by linarith
  have he : (∑ i ∈ Finset.range D, r^(i+1)) = r*(∑ i ∈ Finset.range D, r^i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ]
    ring
  rw [he, geom_sum_eq hr1]
  have hid : r*((r^D-1)/(r-1)) = (r*(1-r^D))/(1-r) := by field_simp; ring
  rw [hid]
  apply (div_le_iff₀ (by linarith : (0:ℝ)<1-r)).mpr
  nlinarith [mul_nonneg hr0 (pow_nonneg hr0 D), mul_le_mul_of_nonneg_left hrh hr0]

/-- The full signed interpolation at minus one from integer parameters zero through D. -/
def mobiusFactorCountSignedInterpolation (N D : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (D+1), (-1:ℂ)^j * ((D+1).choose (j+1):ℂ) *
    mobiusFactorCountEulerPartial N j t

private theorem eventually_eulerPartial_ratio :
    ∀ᶠ D : ℕ in atTop, ∀ t : ℝ,
      7*Real.pi/(16*Real.log D) ≤ t → t ≤ 15*Real.pi/(32*Real.log D) →
      ∀ N : ℕ, ⌊2*(D:ℝ)^(4/3:ℝ)⌋₊ ≤ N → ∀ j : ℕ, j ≤ D →
        ‖mobiusFactorCountEulerPartial N j t‖ ≤
          Real.exp (-((D-j:ℕ):ℝ)*decayRate D) * ‖mobiusFactorCountEulerPartial N D t‖ := by
  have he := tendsto_natCast_atTop_atTop.eventually
    (eventually_mobiusFactorCountLogModulus_gap.and
      (eventually_mobiusFactorCountEulerPartial_logNorm.and (eventually_gt_atTop (1:ℝ))))
  filter_upwards [he] with D hD
  intro t htLo htHi N hN j hj
  obtain ⟨hgapD, hprod, hD1⟩ := hD
  have hLD : 0 < Real.log (D:ℝ) := Real.log_pos hD1
  have ht0 : 0 ≤ t := (by positivity : 0 ≤ 7*Real.pi/(16*Real.log (D:ℝ))).trans htLo
  have hjR : (j:ℝ) ≤ D := by exact_mod_cast hj
  obtain ⟨hnzj, hlogj⟩ := hprod t ht0 htHi j hjR N
  obtain ⟨hnzD, hlogD⟩ := hprod t ht0 htHi D le_rfl N
  have hg := hgapD t htLo htHi j hjR N hN
  have hcost : ((D-j:ℕ):ℝ)*decayRate D = ((D:ℝ)-j)*(D:ℝ)^(1/3:ℝ)/(8192*Real.log D) := by
    rw [Nat.cast_sub hj]
    unfold decayRate
    ring
  rw [← hcost] at hg
  have he : L N j t ≤ -((D-j:ℕ):ℝ)*decayRate D + L N D t := by linarith
  rw [← hlogj, ← hlogD] at he
  have hexp := Real.exp_le_exp.mpr he
  rwa [Real.exp_add, Real.exp_log (norm_pos_iff.mpr hnzj),
    Real.exp_log (norm_pos_iff.mpr hnzD)] at hexp

private lemma signedInterpolation_remainder (N D : ℕ) (t : ℝ) :
    mobiusFactorCountSignedInterpolation N D t - (-1:ℂ)^D*mobiusFactorCountEulerPartial N D t =
      ∑ j ∈ Finset.range D, (-1:ℂ)^j*((D+1).choose (j+1):ℂ)*mobiusFactorCountEulerPartial N j t := by
  rw [mobiusFactorCountSignedInterpolation, Finset.sum_range_succ]
  simp

private lemma binomial_weight_le (D j : ℕ) (hj : j ≤ D) :
    ((D+1).choose (j+1):ℝ) ≤ ((D:ℝ)+1)^(D-j) := by
  have hsym : (D+1).choose (j+1) = (D+1).choose (D-j) := by
    simpa using (Nat.choose_symm (show j+1 ≤ D+1 by omega)).symm
  rw [hsym]
  exact_mod_cast Nat.choose_le_pow (D+1) (D-j)

private lemma sum_reverse_decay_le {r : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1/2) (D : ℕ) :
    (∑ j ∈ Finset.range D, r^(D-j)) ≤ 2*r := by
  have he : (∑ j ∈ Finset.range D, r^(D-j)) = ∑ j ∈ Finset.range D, r^(j+1) := by
    calc
      _ = ∑ j ∈ Finset.range D, r^((D-1-j)+1) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        have hjD := Finset.mem_range.mp hj
        omega
      _ = _ := Finset.sum_range_reflect (fun j => r^(j+1)) D
  rw [he]
  exact sum_geometric_shift_le hr0 hrh D

private lemma signedInterpolation_error_bound {D N : ℕ} {t : ℝ}
    (hr0 : 0 ≤ decayRatio D) (hrh : decayRatio D ≤ 1/2)
    (hterms : ∀ j : ℕ, j ≤ D → ‖mobiusFactorCountEulerPartial N j t‖ ≤
      Real.exp (-((D-j:ℕ):ℝ)*decayRate D)*‖mobiusFactorCountEulerPartial N D t‖) :
    ‖mobiusFactorCountSignedInterpolation N D t - (-1:ℂ)^D*mobiusFactorCountEulerPartial N D t‖ ≤
      2*decayRatio D*‖mobiusFactorCountEulerPartial N D t‖ := by
  rw [signedInterpolation_remainder]
  calc
    _ ≤ ∑ j ∈ Finset.range D,
        ‖(-1:ℂ)^j*((D+1).choose (j+1):ℂ)*mobiusFactorCountEulerPartial N j t‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range D, (decayRatio D)^(D-j)*‖mobiusFactorCountEulerPartial N D t‖ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjD : j ≤ D := (Finset.mem_range.mp hj).le
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
      have hchoose := binomial_weight_le D j hjD
      have hterm := hterms j hjD
      calc
        _ ≤ (((D:ℝ)+1)^(D-j)) *
            (Real.exp (-((D-j:ℕ):ℝ)*decayRate D)*‖mobiusFactorCountEulerPartial N D t‖) :=
          mul_le_mul hchoose hterm (norm_nonneg _) (by positivity)
        _ = _ := by
          unfold decayRatio
          rw [mul_pow, ← Real.exp_nat_mul]
          rw [show ((D-j:ℕ):ℝ)*(-decayRate D) = -((D-j:ℕ):ℝ)*decayRate D by ring]
          ring
    _ = (∑ j ∈ Finset.range D, (decayRatio D)^(D-j))*‖mobiusFactorCountEulerPartial N D t‖ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_reverse_decay_le hr0 hrh D) (norm_nonneg _)

/-- The full signed interpolation is asymptotic to its highest term, uniformly in height and prime truncation. -/
theorem eventually_mobiusFactorCountSignedInterpolation_dominance {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, ∀ t : ℝ,
      7*Real.pi/(16*Real.log D) ≤ t → t ≤ 15*Real.pi/(32*Real.log D) →
      ∀ N : ℕ, ⌊2*(D:ℝ)^(4/3:ℝ)⌋₊ ≤ N →
        ‖mobiusFactorCountSignedInterpolation N D t - (-1:ℂ)^D*mobiusFactorCountEulerPartial N D t‖ ≤
          ε*‖mobiusFactorCountEulerPartial N D t‖ := by
  have hr := tendsto_natCast_atTop_atTop.eventually
    (eventually_decayRatio_small (by positivity : (0 : ℝ) < min (1/2) (ε/2)))
  filter_upwards [eventually_eulerPartial_ratio, hr] with D hterms hrD
  intro t htLo htHi N hN
  have hrh := hrD.2.trans (min_le_left _ _)
  have hre := hrD.2.trans (min_le_right _ _)
  exact (signedInterpolation_error_bound hrD.1 hrh (hterms t htLo htHi N hN)).trans
    (mul_le_mul_of_nonneg_right (by linarith : 2*decayRatio D ≤ ε) (norm_nonneg _))

/-- Exponential moving-sector growth survives the complete signed interpolation. -/
theorem eventually_mobiusFactorCountSignedInterpolation_growth :
    ∀ᶠ D : ℕ in atTop, ∀ t : ℝ,
      7*Real.pi/(16*Real.log D) ≤ t → t ≤ 15*Real.pi/(32*Real.log D) →
      ∀ N : ℕ, ⌊2*(D:ℝ)^(4/3:ℝ)⌋₊ ≤ N →
        Real.exp ((D:ℝ)^(4/3:ℝ)/(4096*Real.log D))/2 ≤ ‖mobiusFactorCountSignedInterpolation N D t‖ := by
  filter_upwards [eventually_mobiusFactorCountSignedInterpolation_dominance (by norm_num : (0:ℝ)<1/2),
    eventually_mobiusFactorCountEulerPartial_growth] with D hdom hgrowth
  intro t htLo htHi N hN
  have he := hdom t htLo htHi N hN
  have hg := hgrowth t htLo htHi N hN
  have ht := norm_sub_norm_le ((-1:ℂ)^D*mobiusFactorCountEulerPartial N D t)
    (mobiusFactorCountSignedInterpolation N D t)
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at ht
  rw [norm_sub_rev] at ht
  linarith

end RHTower
