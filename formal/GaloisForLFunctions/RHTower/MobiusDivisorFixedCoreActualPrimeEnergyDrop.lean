import GaloisForLFunctions.RHTower.MobiusDivisorCofinalNegativeMixedCurvature
import GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreProfile

/-!
# Actual late-prime energy drop after a fixed processed core

For every fixed core with at least two primes, the processed head is
`o(sqrt M)`. A negative continuous source band and prime supply create a
positive singleton contribution of order `sqrt M` at every large cutoff.
The resulting positive head lets a fresh late prime strictly decrease the
complete literal selection energy, using the exact late-prime identity.

The band and threshold depend on the fixed core. This does not establish a
uniform growing-core margin or an exhaustive CCM-FU payment schedule.
-/

noncomputable section
open Finset Filter Topology Set
namespace RHTower

/-- A fixed two-prime core has one negative continuous-head band with fixed
source margin. -/
theorem fixed_core_negative_band
    (P : Finset ℕ) (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime) :
    ∃ l u c : ℝ, 1 < l ∧ l < u ∧ 0 < c ∧
      ∀ x ∈ Ioo l u, mobiusDivisorContinuousHead P x ≤ -c := by
  have hsign := (mobiusDivisorDelayedProfile_both_signs P {1} (fun _ => 1)
    hP hprime (by simp) ⟨1, by simp, by norm_num⟩).1
  obtain ⟨x, hx, hnegative⟩ := hsign
  have he (y : ℝ) : mobiusDivisorDelayedProfile P {1} (fun _ => 1) y =
      mobiusDivisorContinuousHead P y := by
    simp [mobiusDivisorDelayedProfile]
  rw [he] at hnegative
  let c := -mobiusDivisorContinuousHead P x / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hcont : Continuous (mobiusDivisorContinuousHead P) := by
    have h := continuous_mobiusDivisorDelayedProfile P {1} (fun _ => 1)
    have hEq : mobiusDivisorDelayedProfile P {1} (fun _ => 1) =
        mobiusDivisorContinuousHead P := funext he
    rw [hEq] at h
    exact h
  have hnear : {y : ℝ | mobiusDivisorContinuousHead P y < -c} ∈ 𝓝 x :=
    hcont.continuousAt.eventually (eventually_lt_nhds (by dsimp [c]; linarith))
  obtain ⟨l, u, hxu, hband⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let l' := (max 1 l + x) / 2
  have hl' : 1 < l' := by dsimp [l']; linarith [le_max_left (1 : ℝ) l]
  have hlx : l' < x := by
    dsimp [l']
    have hh : max 1 l < x := max_lt hx hxu.1
    linarith
  have hll' : l ≤ l' := by dsimp [l']; linarith [le_max_right (1 : ℝ) l, hxu.1]
  refine ⟨l', u, c, hl', hlx.trans hxu.2, hc, ?_⟩
  intro y hy
  exact (hband ⟨hll'.trans_lt hy.1, hy.2⟩).le

/-- Every sufficiently large cutoff has a fresh prime in any fixed quotient
band above one. -/
theorem prime_in_fixed_child_band {l u : ℝ} (hl : 1 < l) (hlu : l < u)
    (B : ℕ) :
    ∀ᶠ M : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ B < p ∧
      (M : ℝ) / p ∈ Ioo l u := by
  have hu : 0 < u := by linarith
  have hl0 : 0 < l := by linarith
  have he : 0 < u / l - 1 := by
    rw [sub_pos, one_lt_div hl0]
    exact hlu
  have hlim : Tendsto (fun M : ℕ => (M : ℝ) / u) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hu
  have hp := hlim.eventually (prime_between he)
  filter_upwards [hp, hlim.eventually_gt_atTop (B : ℝ)] with M hp hB
  obtain ⟨p, hp, hlo, hhi⟩ := hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hfrac : (1 + (u / l - 1)) * ((M : ℝ) / u) = (M : ℝ) / l := by
    field_simp
    ring
  rw [hfrac] at hhi
  refine ⟨p, hp, by exact_mod_cast hB.trans hlo, ?_⟩
  constructor
  · apply (lt_div_iff₀ hpR).mpr
    have := (lt_div_iff₀ hl0).mp hhi
    nlinarith
  · apply (div_lt_iff₀ hpR).mpr
    have := (div_lt_iff₀ hu).mp hlo
    nlinarith

private theorem late_prime_fresh (B : ℕ) :
    ∀ᶠ M : ℕ in atTop, ∃ q : ℕ,
      q.Prime ∧ q < M ∧ M < 2 * q ∧ B < q := by
  have hhalf : Tendsto (fun M : ℕ => (M : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have hpr := hhalf.eventually (prime_between (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hpr, eventually_ge_atTop (2 * (B + 1))] with M hM hB
  obtain ⟨q, hq, hlo, hhi⟩ := hM
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hqMr : (q : ℝ) < M := by nlinarith only [hhi, hMr]
  have hMqr : (M : ℝ) < 2 * q := by nlinarith only [hlo]
  have hBqr : (B : ℝ) < q := by
    have hBr : (2 * (B + 1) : ℝ) ≤ M := by exact_mod_cast hB
    nlinarith only [hlo, hBr]
  exact ⟨q, hq, by exact_mod_cast hqMr,
    by exact_mod_cast hMqr, by exact_mod_cast hBqr⟩

private theorem late_dilation_neg {M q : ℕ} (hq : q.Prime)
    (hqM : q < M) (hMq : M < 2 * q) :
    mobiusDivisorDilationChannel M q < 0 := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have hx : (M : ℝ) / q ∈ Ioo (1 : ℝ) 2 := by
    constructor
    · exact (one_lt_div hq0).mpr (by exact_mod_cast hqM)
    · exact (div_lt_iff₀ hq0).mpr (by exact_mod_cast hMq)
  have hF := divisorContinuousUnitHead_pos_first hx
  have hU := divisorContinuousUnitHead_dilation M q hq.pos
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
      ArithmeticFunction.moebius_apply_prime hq]
  push_cast
  nlinarith [Real.sqrt_pos.mpr hq0]

/-- Every large cutoff admits an actual energy-decreasing late prime after
one source-selected fresh prime, for each fixed two-prime processed core. -/
theorem eventually_exists_fixedCore_actual_latePrime_energy_drop
    (P : Finset ℕ) (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime) :
    ∀ᶠ M : ℕ in atTop, ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ p ∉ P ∧ q ∉ P ∧ p ≠ q ∧
      0 < mobiusDivisorSelectionFibre M (insert p P) ∅ ∧
      mobiusDivisorSelectionEnergy M (insert q (insert p P)) <
        mobiusDivisorSelectionEnergy M (insert p P) := by
  obtain ⟨l, u, c, hl, hlu, hc, hnegative⟩ := fixed_core_negative_band P hP hprime
  have hu : 0 < u := by linarith
  let κ : ℝ := c / (2 * u)
  have hκ : 0 < κ := div_pos hc (by positivity)
  have hnegκ : -κ < (0 : ℝ) := by linarith
  have hsmall := (tendsto_mobiusDivisorSelectionHead_div_sqrt_zero P hprime
    (Finset.card_pos.mp (by omega : 0 < P.card))).eventually
    (eventually_gt_nhds hnegκ)
  have hps := prime_in_fixed_child_band hl hlu (P.sup id)
  have hqs := late_prime_fresh (P.sup id)
  filter_upwards [hsmall, hps, hqs, eventually_gt_atTop (0 : ℕ)] with M hsmall hps hqs hM
  obtain ⟨p, hp, hpB, hpband⟩ := hps
  obtain ⟨q, hq, hqM, hMq, hqB⟩ := hqs
  have hpP : p ∉ P := by
    intro hmem
    exact (not_le_of_gt hpB) (Finset.le_sup (f := id) hmem)
  have hqP : q ∉ P := by
    intro hmem
    exact (not_le_of_gt hqB) (Finset.le_sup (f := id) hmem)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hrootp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
  have hrootM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM0
  have hMp : (M : ℝ) < u * p := by
    exact (div_lt_iff₀ hp0).mp hpband.2
  have hu2 : u ≤ u ^ (2 : ℕ) := by nlinarith [hl, hlu]
  have hsq : (M : ℝ) < u ^ (2 : ℕ) * p :=
    hMp.trans_le (mul_le_mul_of_nonneg_right hu2 hp0.le)
  have hscale : Real.sqrt (M : ℝ) < u * Real.sqrt (p : ℝ) := by
    have hupos : 0 < u * Real.sqrt (p : ℝ) := mul_pos hu hrootp
    have hsq' : (u * Real.sqrt (p : ℝ)) ^ (2 : ℕ) = u ^ (2 : ℕ) * p := by
      rw [mul_pow, Real.sq_sqrt hp0.le]
    rw [← hsq'] at hsq
    nlinarith only [hsq, Real.sq_sqrt hM0.le, hupos, hrootM]
  have hprof : mobiusDivisorInterpolatedFibre M p P ∅ ≤ -c := by
    rw [← mobiusDivisorContinuousHead_div P hprime M p hp.pos]
    exact hnegative _ hpband
  have hF : c * Real.sqrt (p : ℝ) ≤
      mobiusDivisorSelectionFibre M P {p} := by
    change c * Real.sqrt (p : ℝ) ≤
      mobiusDivisorSelectionFibre M P (insert p ∅)
    rw [mobiusDivisorSelectionFibre_prime_interpolation hp M P ∅ hpP (by simp)]
    nlinarith only [hprof, hrootp]
  have hhead : -κ * Real.sqrt (M : ℝ) <
      mobiusDivisorSelectionFibre M P ∅ := by
    have h := mul_lt_mul_of_pos_right hsmall hrootM
    field_simp at h ⊢
    exact h
  have hpositive : 0 < mobiusDivisorSelectionFibre M (insert p P) ∅ := by
    rw [mobiusDivisorSelectionFibre_insert]
    have hpempty : p ∉ (∅ : Finset ℕ) := by simp
    simp only [if_neg hpempty, Finset.insert_empty]
    have hgain : 2 * κ * Real.sqrt (M : ℝ) < c * Real.sqrt (p : ℝ) := by
      have hgain0 := mul_lt_mul_of_pos_left hscale hc
      calc
        2 * κ * Real.sqrt (M : ℝ) =
            (c * Real.sqrt (M : ℝ)) / u := by dsimp [κ]; field_simp
        _ < c * Real.sqrt (p : ℝ) :=
          (div_lt_iff₀ hu).mpr (by nlinarith only [hgain0])
    have hmargin : 0 < κ * Real.sqrt (M : ℝ) := mul_pos hκ hrootM
    linarith only [hhead, hF, hgain, hmargin]
  have hqD := late_dilation_neg hq hqM hMq
  have hpq : p ≠ q := by
    intro he
    subst q
    have hsingle := mobiusDivisorSelectionFibre_late_prime
      hp hqM hMq.le P {p} hpP (by simp)
    simp only [if_true] at hsingle
    rw [hsingle] at hF
    linarith [mul_pos hc hrootp]
  have hqPp : q ∉ insert p P := by simp [hqP, hpq.symm]
  have hdrop := mobiusDivisorSelectionEnergy_insert_late_prime
    hq hqM hMq.le (insert p P) hqPp
  refine ⟨p, q, hp, hq, hpP, hqP, hpq, hpositive, ?_⟩
  rw [sub_eq_iff_eq_add] at hdrop
  nlinarith [mul_neg_of_pos_of_neg (mul_pos (by norm_num : (0 : ℝ) < 2) hpositive) hqD]

end RHTower
