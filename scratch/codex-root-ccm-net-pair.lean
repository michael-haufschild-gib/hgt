import GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreActualPrimeEnergyDrop
import GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreMovingPrimeEnergySublinear

noncomputable section
open Finset Filter Topology Set
namespace RHTower

private theorem first_unit_head_mono_band {x : ℝ}
    (hx : x ∈ Ioo (4 / 3 : ℝ) (3 / 2)) :
    divisorContinuousUnitHead (4 / 3 : ℝ) ≤ divisorContinuousUnitHead x := by
  have hbase0 : 0 < divisorContinuousUnitHead (4 / 3 : ℝ) :=
    divisorContinuousUnitHead_pos_first (by constructor <;> norm_num)
  have hb : divisorContinuousUnitHead (4 / 3 : ℝ) =
      (Real.sqrt (4 / 3 : ℝ) - 1) * primeFreeDivisorDefect 1 := by
    rw [divisorContinuousUnitHead_between (k := 1) le_rfl (by norm_num) (by norm_num)]
    simp [divisorUnsignedDilationChannel]
  have hcoef : 0 < primeFreeDivisorDefect 1 := by
    have hroot : 0 < Real.sqrt (4 / 3 : ℝ) - 1 := by
      rw [sub_pos, ← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [hb] at hbase0
    by_contra h
    exact (not_le_of_gt hbase0)
      (mul_nonpos_of_nonneg_of_nonpos hroot.le (le_of_not_gt h))
  have hxform : divisorContinuousUnitHead x =
      (Real.sqrt x - 1) * primeFreeDivisorDefect 1 := by
    have hx1 : (1 : ℝ) ≤ x :=
      (by norm_num : (1 : ℝ) ≤ 4 / 3).trans hx.1.le
    have hx2 : x ≤ (2 : ℝ) :=
      hx.2.le.trans (by norm_num : (3 / 2 : ℝ) ≤ 2)
    rw [divisorContinuousUnitHead_between (k := 1) le_rfl
      (by simpa using hx1) (by simpa using hx2)]
    simp [divisorUnsignedDilationChannel]
  rw [hb, hxform]
  exact mul_le_mul_of_nonneg_right
    (sub_le_sub_right (Real.sqrt_le_sqrt hx.1.le) 1) hcoef.le

private theorem eventually_macroscopic_negative_late_prime (B : ℕ) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ M : ℕ in atTop, ∃ q : ℕ,
      q.Prime ∧ B < q ∧ q < M ∧ M < 2 * q ∧
      mobiusDivisorDilationChannel M q ≤ -d * Real.sqrt M := by
  let u₀ : ℝ := divisorContinuousUnitHead (4 / 3 : ℝ)
  have hu₀ : 0 < u₀ := divisorContinuousUnitHead_pos_first
    (by constructor <;> norm_num)
  let d := u₀ / 2
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨d, hd, ?_⟩
  filter_upwards [prime_in_fixed_child_band (by norm_num : (1 : ℝ) < 4 / 3)
      (by norm_num : (4 / 3 : ℝ) < 3 / 2) B] with M hM
  obtain ⟨q, hq, hqB, hband⟩ := hM
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hMr : (0 : ℝ) < M := by
    have h := (lt_div_iff₀ hq0).mp hband.1
    nlinarith only [h, hq0]
  have hqM : q < M := by
    have hh : (1 : ℝ) < M / q := by linarith [hband.1]
    exact_mod_cast (one_lt_div hq0).mp hh
  have hMq : M < 2 * q := by
    have hh : (M : ℝ) < 2 * q := by
      have h := (div_lt_iff₀ hq0).mp hband.2
      nlinarith only [h, hq0]
    exact_mod_cast hh
  have hqU : u₀ ≤ divisorContinuousUnitHead ((M : ℝ) / q) :=
    first_unit_head_mono_band hband
  have hrootq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq0
  have hrootM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMr
  have hM4q : (M : ℝ) < 4 * q := by
    have h := (div_lt_iff₀ hq0).mp hband.2
    nlinarith only [h, hq0]
  have hroot : Real.sqrt (M : ℝ) < 2 * Real.sqrt (q : ℝ) := by
    have hsq : (2 * Real.sqrt (q : ℝ)) ^ (2 : ℕ) = 4 * q := by
      rw [mul_pow, Real.sq_sqrt hq0.le]
      ring
    rw [← hsq] at hM4q
    nlinarith only [hM4q, Real.sq_sqrt hMr.le, hrootM, hrootq]
  have hprod : d * Real.sqrt (M : ℝ) <
      Real.sqrt (q : ℝ) * divisorContinuousUnitHead ((M : ℝ) / q) := by
    have h₁ : d * Real.sqrt (M : ℝ) < u₀ * Real.sqrt (q : ℝ) := by
      dsimp [d]
      have hh := mul_lt_mul_of_pos_left hroot hu₀
      nlinarith only [hh]
    have h₂ : u₀ * Real.sqrt (q : ℝ) ≤
        divisorContinuousUnitHead ((M : ℝ) / q) * Real.sqrt (q : ℝ) :=
      mul_le_mul_of_nonneg_right hqU hrootq.le
    nlinarith only [h₁, h₂]
  have hU := divisorContinuousUnitHead_dilation M q hq.pos
  have hD : mobiusDivisorDilationChannel M q ≤ -d * Real.sqrt M := by
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
      ArithmeticFunction.moebius_apply_prime hq]
    push_cast
    nlinarith only [hU, hprod]
  exact ⟨q, hq, hqB, hqM, hMq, hD⟩

private theorem eventually_fixed_core_macroscopic_preparation
    (P : Finset ℕ) (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ K : ℕ, ∀ᶠ M : ℕ in atTop, ∃ p : ℕ,
      p.Prime ∧ p ∉ P ∧ p < M ∧ M / p ≤ K ∧
      κ * Real.sqrt M ≤ mobiusDivisorSelectionFibre M (insert p P) ∅ ∧
      0 < mobiusDivisorSelectionFibre M P {p} := by
  obtain ⟨l, u, c, hl, hlu, hc, hnegative⟩ := fixed_core_negative_band P hP hprime
  have hu : 0 < u := by linarith
  let κ : ℝ := c / (2 * u)
  have hκ : 0 < κ := div_pos hc (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_gt u
  refine ⟨κ, hκ, K, ?_⟩
  have hsmall := (tendsto_mobiusDivisorSelectionHead_div_sqrt_zero P hprime
    (Finset.card_pos.mp (by omega : 0 < P.card))).eventually
    (eventually_gt_nhds (show -κ < (0 : ℝ) by linarith))
  have hps := prime_in_fixed_child_band hl hlu (P.sup id)
  filter_upwards [hsmall, hps, eventually_gt_atTop (0 : ℕ)] with M hsmall hps hM
  obtain ⟨p, hp, hpB, hpband⟩ := hps
  have hpP : p ∉ P := by
    intro hmem
    exact (not_le_of_gt hpB) (Finset.le_sup (f := id) hmem)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hrootp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
  have hrootM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hM0
  have hMp : (M : ℝ) < u * p := (div_lt_iff₀ hp0).mp hpband.2
  have hpM : p < M := by
    have hh : (1 : ℝ) < (M : ℝ) / p := hl.trans hpband.1
    exact_mod_cast (one_lt_div hp0).mp hh
  have hMK : M / p ≤ K := by
    have hMpK : (M : ℝ) < K * p :=
      hMp.trans (mul_lt_mul_of_pos_right hK hp0)
    have hMpK' : M < K * p := by exact_mod_cast hMpK
    exact (Nat.div_lt_iff_lt_mul hp.pos).mpr hMpK' |>.le
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
  have hgain : 2 * κ * Real.sqrt (M : ℝ) < c * Real.sqrt (p : ℝ) := by
    have hgain0 := mul_lt_mul_of_pos_left hscale hc
    calc
      2 * κ * Real.sqrt (M : ℝ) =
          (c * Real.sqrt (M : ℝ)) / u := by dsimp [κ]; field_simp
      _ < c * Real.sqrt (p : ℝ) :=
        (div_lt_iff₀ hu).mpr (by nlinarith only [hgain0])
  have hprep : κ * Real.sqrt (M : ℝ) ≤
      mobiusDivisorSelectionFibre M (insert p P) ∅ := by
    rw [mobiusDivisorSelectionFibre_insert]
    have hpempty : p ∉ (∅ : Finset ℕ) := by simp
    simp only [if_neg hpempty, Finset.insert_empty]
    linarith only [hhead, hF, hgain]
  refine ⟨p, hp, hpP, hpM, hMK, hprep, ?_⟩
  exact lt_of_lt_of_le (mul_pos hc hrootp) hF

theorem eventually_fixed_core_macroscopic_net_pair_drop
    (P : Finset ℕ) (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ M : ℕ in atTop, ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ p ∉ P ∧ q ∉ P ∧ p ≠ q ∧
      mobiusDivisorSelectionEnergy M (insert q (insert p P)) + η * M ≤
        mobiusDivisorSelectionEnergy M P := by
  obtain ⟨κ, hκ, K, hpreps⟩ :=
    eventually_fixed_core_macroscopic_preparation P hP hprime
  obtain ⟨d, hd, hqs⟩ := eventually_macroscopic_negative_late_prime (P.sup id)
  let η := κ * d
  have hη : 0 < η := mul_pos hκ hd
  refine ⟨η, hη, ?_⟩
  have hcosts := eventually_fixedCore_movingPrimeInsertion_energy_sublinear
    P hprime (Finset.card_pos.mp (by omega : 0 < P.card)) K η hη
  filter_upwards [hpreps, hqs, hcosts, eventually_gt_atTop (0 : ℕ)]
    with M hprep hq hcost hM
  obtain ⟨p, hp, hpP, hpM, hpK, hhead, hsingle⟩ := hprep
  obtain ⟨q, hqprime, hqB, hqM, hMq, hD⟩ := hq
  have hqP : q ∉ P := by
    intro hmem
    exact (not_le_of_gt hqB) (Finset.le_sup (f := id) hmem)
  have hrootM : 0 < Real.sqrt (M : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hM)
  have hDneg : mobiusDivisorDilationChannel M q < 0 := by
    have hηroot : 0 < d * Real.sqrt (M : ℝ) := mul_pos hd hrootM
    linarith only [hD, hηroot]
  have hpq : p ≠ q := by
    intro he
    subst q
    have hsingle' := mobiusDivisorSelectionFibre_late_prime
      hp hqM hMq.le P {p} hpP (by simp)
    simp only [if_true] at hsingle'
    rw [hsingle'] at hsingle
    linarith only [hsingle, hDneg]
  have hqPp : q ∉ insert p P := by simp [hqP, hpq.symm]
  have hcost' := hcost p hp hpM hpP hpK
  have hcostUp : mobiusDivisorSelectionEnergy M (insert p P) ≤
      mobiusDivisorSelectionEnergy M P + η * M := by
    have hh := le_abs_self
      (mobiusDivisorSelectionEnergy M (insert p P) -
        mobiusDivisorSelectionEnergy M P)
    linarith only [hh, hcost']
  have hhead0 : 0 ≤ mobiusDivisorSelectionFibre M (insert p P) ∅ := by
    have hh : 0 ≤ κ * Real.sqrt (M : ℝ) :=
      mul_nonneg hκ.le hrootM.le
    exact hh.trans hhead
  have hneg : -d * Real.sqrt (M : ℝ) ≤ 0 := by
    have hh : 0 ≤ d * Real.sqrt (M : ℝ) :=
      mul_nonneg hd.le hrootM.le
    linarith only [hh]
  have hprod :
      mobiusDivisorSelectionFibre M (insert p P) ∅ *
        mobiusDivisorDilationChannel M q ≤ -η * M := by
    calc
      _ ≤ mobiusDivisorSelectionFibre M (insert p P) ∅ *
            (-d * Real.sqrt (M : ℝ)) :=
        mul_le_mul_of_nonneg_left hD hhead0
      _ ≤ (κ * Real.sqrt (M : ℝ)) *
            (-d * Real.sqrt (M : ℝ)) :=
        mul_le_mul_of_nonpos_right hhead hneg
      _ = -η * M := by
        dsimp [η]
        calc
          _ = -(κ * d) * (Real.sqrt (M : ℝ) * Real.sqrt M) := by ring
          _ = -(κ * d) * M := by rw [Real.mul_self_sqrt (Nat.cast_nonneg M)]
  have hdrop := mobiusDivisorSelectionEnergy_insert_late_prime
    hqprime hqM hMq.le (insert p P) hqPp
  have hdropUp : mobiusDivisorSelectionEnergy M (insert q (insert p P)) ≤
      mobiusDivisorSelectionEnergy M (insert p P) - 2 * η * M := by
    have hh := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
    linarith only [hdrop, hh]
  refine ⟨p, q, hp, hqprime, hpP, hqP, hpq, ?_⟩
  linarith only [hcostUp, hdropUp]

end RHTower
