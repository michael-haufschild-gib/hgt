import GaloisForLFunctions.BezoutValuationIncidence.InteriorJumpOrbitCenteringAndCompensatedBounds
import GaloisForLFunctions.BezoutValuationIncidence.BezoutPronicTotientInteriorMartingaleSynthesis

/-!
# Birth-delayed interior centering and uniform pair bounds

The initial-value correction in the horizon-free BVI prefix must be kept
when studying interior atoms along a jump progression. For `d >= 2`, set
`A_e = (e-1)/(2e)`, `F_e = interiorSawtoothAtom e - A_e`, and `K = e/d`.
Subtract the conditional mean `interiorJumpOrbitMean d e - A_e` only at
jump indices `k >= K`, equivalently when `e <= d-1+d*k`.

Before this threshold, the entire compensated contribution is bounded by
`K/e`. After it, shifted centered prefixes are bounded by two reduced
orbit lengths, giving a tail bound `2*(e/gcd(d,e))/(d*(K+1))`. Their sum
is at most `1/d + 2/gcd(d,e)`, uniformly in both finite horizons. This
removes the growth with the interior modulus from the unshifted orbit
bound. The jump modulus in the public pair theorems is parametrized by
`d+2`, so no domain premise or analytic hypothesis is required.

The final estimates retain arbitrary signed finite-cutoff coefficients
and connect to the existing horizon-free arithmetic prefix with its
linear density correction displayed explicitly. The remaining signed
modulus sum and strict energy contraction are not established here.
-/

open Finset GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The interior atom with the initial sawtooth value subtracted. -/
def anchoredInteriorSawtoothAtom (e n : ℕ) : ℝ :=
  interiorSawtoothAtom e n - ((e : ℝ) - 1) / (2 * (e : ℝ))

/-- Conditional centering starts after the interior modulus's initial segment. -/
def birthDelayedInteriorJumpResidual (d e k : ℕ) : ℝ :=
  anchoredInteriorSawtoothAtom e (d - 1 + d * k) -
    if e / d ≤ k then interiorJumpOrbitMean d e - ((e : ℝ) - 1) / (2 * (e : ℝ))
    else 0

private theorem compensated_nonneg (d : ℕ+) (T k : ℕ) :
    0 ≤ interiorJumpCompensatedWeight d T k := le_max_right _ _

private theorem compensated_le (d : ℕ+) (T k : ℕ) :
    interiorJumpCompensatedWeight d T k ≤ 1 / ((d : ℝ) * ((k : ℝ) + 1)) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
  exact max_le (sub_le_self _ (by positivity)) (by positivity)

private theorem compensated_antitone (d : ℕ+) (T : ℕ) :
    Antitone (interiorJumpCompensatedWeight d T) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
  intro i j hij
  apply max_le_max _ le_rfl
  apply sub_le_sub_right
  apply one_div_le_one_div_of_le (by positivity)
  apply mul_le_mul_of_nonneg_left _ hd.le
  exact_mod_cast (Nat.add_le_add_right hij 1)

/-- Starting a centered progression at an arbitrary offset costs at most two reduced orbits. -/
theorem abs_interiorSawtoothAtom_centered_jump_shifted_prefix_le
    (d e : ℕ+) (K L : ℕ) :
    |∑ j ∈ range L,
      (interiorSawtoothAtom e ((d : ℕ) - 1 + d * (K + j)) -
        interiorJumpOrbitMean d e)| ≤
      2 * (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ) := by
  let a := fun k => interiorSawtoothAtom e ((d : ℕ) - 1 + d * k) -
    interiorJumpOrbitMean d e
  have heq : (∑ j ∈ range L, a (K + j)) =
      (∑ j ∈ range (K + L), a j) - ∑ j ∈ range K, a j := by
    rw [sum_range_add]
    ring
  change |∑ j ∈ range L, a (K + j)| ≤ _
  rw [heq]
  apply (abs_sub _ _).trans
  have h1 := abs_interiorSawtoothAtom_centered_jump_prefix_le d e (K + L)
  have h2 := abs_interiorSawtoothAtom_centered_jump_prefix_le d e K
  change |∑ j ∈ range (K + L), a j| ≤ _ at h1
  change |∑ j ∈ range K, a j| ≤ _ at h2
  linarith

/-- The compensated centered tail decays with its starting jump index. -/
theorem abs_interiorSawtoothAtom_centered_jump_shifted_compensated_le
    (d e : ℕ+) (T K L : ℕ) :
    |∑ j ∈ range L, interiorJumpCompensatedWeight d T (K + j) *
      (interiorSawtoothAtom e ((d : ℕ) - 1 + d * (K + j)) -
        interiorJumpOrbitMean d e)| ≤
      2 * (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ) /
        ((d : ℝ) * ((K : ℝ) + 1)) := by
  have h := abs_sum_range_mul_antitone_le
    (fun j => interiorSawtoothAtom e ((d : ℕ) - 1 + d * (K + j)) -
      interiorJumpOrbitMean d e)
    (fun j => interiorJumpCompensatedWeight d T (K + j)) L
    (by positivity : 0 ≤ 2 * (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ))
    (fun j => compensated_nonneg d T (K + j))
    (fun i j hij => compensated_antitone d T (Nat.add_le_add_left hij K))
    (fun J _ => abs_interiorSawtoothAtom_centered_jump_shifted_prefix_le d e K J)
  simp only [add_zero] at h
  calc
    _ ≤ _ := h
    _ ≤ 2 * (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ) *
        (1 / ((d : ℝ) * ((K : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (compensated_le d T K) (by positivity)
    _ = _ := by ring

private theorem anchored_prebirth_le {d e k : ℕ} (hd : 2 ≤ d) (he : 0 < e)
    (hk : k < e / d) :
    |anchoredInteriorSawtoothAtom e (d - 1 + d * k)| ≤
      (d : ℝ) * ((k : ℝ) + 1) / (e : ℝ) := by
  let n := d - 1 + d * k
  have hn1 : 0 < n := by dsimp [n]; omega
  have hnk : n + 1 = d * (k + 1) := by dsimp [n]; rw [Nat.mul_add, Nat.mul_one]; omega
  have hprod : d * (k + 1) ≤ e :=
    (Nat.mul_le_mul_left d hk).trans (Nat.mul_div_le e d)
  have hne : n < e := by omega
  have hnd : ¬ e ∣ n := fun h => (Nat.not_le_of_gt hne) (Nat.le_of_dvd hn1 h)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  change |anchoredInteriorSawtoothAtom e n| ≤ _
  by_cases hnext : e ∣ n + 1
  · have hhit : n + 1 = e := by
      have := Nat.le_of_dvd (by omega : 0 < n + 1) hnext
      omega
    have hprodR : (d : ℝ) * ((k : ℝ) + 1) = e := by
      exact_mod_cast (hnk.symm.trans hhit)
    simp only [anchoredInteriorSawtoothAtom, interiorSawtoothAtom, hnext,
      or_true, ite_true, zero_sub, abs_neg]
    rw [abs_of_nonneg (by positivity), hprodR, div_self heR.ne']
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * e)).mpr
    linarith
  · have hval : anchoredInteriorSawtoothAtom e n = -(n : ℝ) / (e : ℝ) := by
      simp only [anchoredInteriorSawtoothAtom, interiorSawtoothAtom, hnd, hnext,
        or_self, ite_false, centeredDiscreteSawtooth_eq_mod_sub_half he,
        Nat.mod_eq_of_lt hne]
      field_simp
      ring
    rw [hval, neg_div, abs_neg, abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ heR.le
    have : (n : ℝ) + 1 = (d : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hnk
    linarith

private theorem delayed_prebirth_term_le (d e : ℕ+) (hd : 2 ≤ (d : ℕ))
    (T k : ℕ) (hk : k < (e : ℕ) / d) :
    |interiorJumpCompensatedWeight d T k * birthDelayedInteriorJumpResidual d e k| ≤
      1 / (e : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast d.pos
  have heR : (0 : ℝ) < e := by exact_mod_cast e.pos
  have heq : birthDelayedInteriorJumpResidual d e k =
      anchoredInteriorSawtoothAtom e ((d : ℕ) - 1 + d * k) := by
    simp only [birthDelayedInteriorJumpResidual, not_le_of_gt hk, ite_false, sub_zero]
  rw [heq, abs_mul, abs_of_nonneg (compensated_nonneg d T k)]
  calc
    _ ≤ (1 / ((d : ℝ) * ((k : ℝ) + 1))) *
        ((d : ℝ) * ((k : ℝ) + 1) / (e : ℝ)) :=
      mul_le_mul (compensated_le d T k) (anchored_prebirth_le hd e.pos hk)
        (abs_nonneg _) (by positivity)
    _ = _ := by field_simp


private theorem delayed_head_le (d e : ℕ+) (hd : 2 ≤ (d : ℕ))
    (T L : ℕ) (hL : L ≤ (e : ℕ) / d) :
    |∑ k ∈ range L, interiorJumpCompensatedWeight d T k *
      birthDelayedInteriorJumpResidual d e k| ≤
      (((e : ℕ) / d : ℕ) : ℝ) / (e : ℝ) := by
  calc
    _ ≤ ∑ k ∈ range L, |interiorJumpCompensatedWeight d T k *
        birthDelayedInteriorJumpResidual d e k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range L, (1 / (e : ℝ)) := by
      apply sum_le_sum
      intro k hk
      exact delayed_prebirth_term_le d e hd T k ((mem_range.mp hk).trans_le hL)
    _ = (L : ℝ) / (e : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hL) (by positivity)

private theorem delayed_after_birth (d e : ℕ) (j : ℕ) :
    birthDelayedInteriorJumpResidual d e (e / d + j) =
      interiorSawtoothAtom e (d - 1 + d * (e / d + j)) - interiorJumpOrbitMean d e := by
  simp only [birthDelayedInteriorJumpResidual, Nat.le_add_right, ite_true,
    anchoredInteriorSawtoothAtom]
  ring

private theorem delayed_envelope_le (d e : ℕ+) (hd : 2 ≤ (d : ℕ)) (T L : ℕ) :
    |∑ k ∈ range L, interiorJumpCompensatedWeight d T k *
      birthDelayedInteriorJumpResidual d e k| ≤
      (((e : ℕ) / d : ℕ) : ℝ) / (e : ℝ) +
        2 * (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ) /
          ((d : ℝ) * ((((e : ℕ) / d : ℕ) : ℝ) + 1)) := by
  by_cases hL : L ≤ (e : ℕ) / d
  · apply (delayed_head_le d e hd T L hL).trans
    exact le_add_of_nonneg_right (by positivity)
  · have hK : (e : ℕ) / d ≤ L := (not_le.mp hL).le
    have hsum :
        (∑ k ∈ range L, interiorJumpCompensatedWeight d T k *
          birthDelayedInteriorJumpResidual d e k) =
        (∑ k ∈ range ((e : ℕ) / d), interiorJumpCompensatedWeight d T k *
          birthDelayedInteriorJumpResidual d e k) +
        ∑ j ∈ range (L - (e : ℕ) / d), interiorJumpCompensatedWeight d T ((e : ℕ) / d + j) *
          birthDelayedInteriorJumpResidual d e ((e : ℕ) / d + j) := by
      conv_lhs => rw [← Nat.add_sub_of_le hK]
      exact sum_range_add _ _ _
    rw [hsum]
    apply (abs_add_le _ _).trans
    apply add_le_add (delayed_head_le d e hd T ((e : ℕ) / d) le_rfl)
    simp only [delayed_after_birth]
    exact abs_interiorSawtoothAtom_centered_jump_shifted_compensated_le d e T
      ((e : ℕ) / d) (L - (e : ℕ) / d)

private theorem delayed_envelope_uniform (d e : ℕ+) :
    (((e : ℕ) / d : ℕ) : ℝ) / (e : ℝ) +
        2 * (((e : ℕ) / Nat.gcd d e : ℕ) : ℝ) /
          ((d : ℝ) * ((((e : ℕ) / d : ℕ) : ℝ) + 1)) ≤
      1 / (d : ℝ) + 2 / (Nat.gcd (d : ℕ) e : ℝ) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
  have he : (0 : ℝ) < e := by exact_mod_cast e.pos
  have hg : (0 : ℝ) < (Nat.gcd (d : ℕ) e : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left (e : ℕ) d.pos
  have hKe : (d : ℝ) * (((e : ℕ) / d : ℕ) : ℝ) ≤ e := by
    exact_mod_cast Nat.mul_div_le (e : ℕ) d
  have heK : (e : ℝ) < (d : ℝ) * ((((e : ℕ) / d : ℕ) : ℝ) + 1) := by
    have hmod := Nat.mod_lt (e : ℕ) d.pos
    have heq := Nat.mod_add_div (e : ℕ) d
    have : (e : ℕ) < (d : ℕ) * ((e : ℕ) / d + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact_mod_cast this
  apply add_le_add
  · apply (div_le_div_iff₀ he hd).mpr
    simpa only [one_mul, mul_comm] using hKe
  · rw [Nat.cast_div_charZero (Nat.gcd_dvd_right (d : ℕ) e)]
    apply (div_le_div_iff₀ (by positivity) hg).mpr
    have hcancel : (2 * ((e : ℝ) / (Nat.gcd (d : ℕ) e : ℝ))) *
        (Nat.gcd (d : ℕ) e : ℝ) = 2 * (e : ℝ) := by field_simp
    rw [hcancel]
    linarith

/-- Delaying the conditional mean until birth gives an explicit initial-segment/tail envelope. -/
theorem abs_birthDelayedInteriorJumpResidual_compensated_envelope
    (d : ℕ) (e : ℕ+) (T L : ℕ) :
    |∑ k ∈ range L, interiorJumpCompensatedWeight ⟨d + 2, by omega⟩ T k *
      birthDelayedInteriorJumpResidual (d + 2) e k| ≤
      (((e : ℕ) / (d + 2) : ℕ) : ℝ) / (e : ℝ) +
        2 * (((e : ℕ) / Nat.gcd (d + 2) e : ℕ) : ℝ) /
          (((d : ℝ) + 2) * ((((e : ℕ) / (d + 2) : ℕ) : ℝ) + 1)) := by
  have h := delayed_envelope_le ⟨d + 2, by omega⟩ e
    (by change 2 ≤ d + 2; omega) T L
  change |∑ k ∈ range L, interiorJumpCompensatedWeight ⟨d + 2, by omega⟩ T k *
      birthDelayedInteriorJumpResidual (d + 2) e k| ≤
      (((e : ℕ) / (d + 2) : ℕ) : ℝ) / (e : ℝ) +
        2 * (((e : ℕ) / Nat.gcd (d + 2) e : ℕ) : ℝ) /
          (((d + 2 : ℕ) : ℝ) * ((((e : ℕ) / (d + 2) : ℕ) : ℝ) + 1)) at h
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

/-- Uniform pair cancellation: no growth with the interior modulus remains. -/
theorem abs_birthDelayedInteriorJumpResidual_compensated_le
    (d : ℕ) (e : ℕ+) (T L : ℕ) :
    |∑ k ∈ range L, interiorJumpCompensatedWeight ⟨d + 2, by omega⟩ T k *
      birthDelayedInteriorJumpResidual (d + 2) e k| ≤
      1 / ((d : ℝ) + 2) + 2 / (Nat.gcd (d + 2) (e : ℕ) : ℝ) := by
  have h := (delayed_envelope_le ⟨d + 2, by omega⟩ e
    (by change 2 ≤ d + 2; omega) T L).trans
    (delayed_envelope_uniform ⟨d + 2, by omega⟩ e)
  simpa only [PNat.mk_coe, Nat.cast_add, Nat.cast_ofNat] using h

/-- The finite BVI interior observable with its initial value removed is the sum of anchored atoms. -/
theorem bezoutInteriorSawtoothSum_sub_initial_eq_sum_anchored
    (N n : ℕ) (c : ℕ → ℝ) :
    bezoutInteriorSawtoothSum N c n - weightedCenteredSawtoothSum N c 0 =
      ∑ e ∈ Icc 1 N, c e * anchoredInteriorSawtoothAtom e n := by
  rw [bezoutInteriorSawtoothSum_eq_sum_interiorSawtoothAtom,
    weightedCenteredSawtoothSum, sub_neg_eq_add, ← sum_add_distrib]
  apply sum_congr rfl
  intro e he
  rw [centeredDiscreteSawtooth_of_dvd (mem_Icc.mp he).1 (dvd_zero e)]
  unfold anchoredInteriorSawtoothAtom
  ring

/-- The signed finite-cutoff estimate retains the initial-value correction and all coefficient dependence. -/
theorem abs_bezoutInteriorSawtoothSum_birthDelayed_compensated_le
    (N T L d : ℕ) (c : ℕ → ℝ) :
    |∑ k ∈ range L, interiorJumpCompensatedWeight ⟨d + 2, by omega⟩ T k *
      (bezoutInteriorSawtoothSum N c (d + 2 - 1 + (d + 2) * k) -
        weightedCenteredSawtoothSum N c 0 -
        ∑ e ∈ Icc 1 N, c e *
          (if e / (d + 2) ≤ k then
            interiorJumpOrbitMean (d + 2) e - ((e : ℝ) - 1) / (2 * (e : ℝ))
          else 0))| ≤
      ∑ e ∈ Icc 1 N, |c e| *
        (1 / ((d : ℝ) + 2) + 2 / (Nat.gcd (d + 2) e : ℝ)) := by
  have heq :
      (∑ k ∈ range L, interiorJumpCompensatedWeight ⟨d + 2, by omega⟩ T k *
        (bezoutInteriorSawtoothSum N c (d + 2 - 1 + (d + 2) * k) -
          weightedCenteredSawtoothSum N c 0 -
          ∑ e ∈ Icc 1 N, c e *
            (if e / (d + 2) ≤ k then
              interiorJumpOrbitMean (d + 2) e - ((e : ℝ) - 1) / (2 * (e : ℝ))
            else 0))) =
      ∑ e ∈ Icc 1 N, c e * ∑ k ∈ range L,
        interiorJumpCompensatedWeight ⟨d + 2, by omega⟩ T k *
          birthDelayedInteriorJumpResidual (d + 2) e k := by
    calc
      _ = ∑ k ∈ range L, ∑ e ∈ Icc 1 N, c e *
          (interiorJumpCompensatedWeight ⟨d + 2, by omega⟩ T k *
            birthDelayedInteriorJumpResidual (d + 2) e k) := by
        apply sum_congr rfl
        intro k _
        rw [bezoutInteriorSawtoothSum_sub_initial_eq_sum_anchored,
          ← sum_sub_distrib, mul_sum]
        apply sum_congr rfl
        intro e _
        unfold birthDelayedInteriorJumpResidual
        ring
      _ = _ := by rw [sum_comm]; simp only [mul_sum]
  rw [heq]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro e he
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_birthDelayedInteriorJumpResidual_compensated_le d
      ⟨e, (mem_Icc.mp he).1⟩ T L) (abs_nonneg _)


/-- The delayed mean is switched on exactly when the interior modulus is no larger than the observed predecessor. -/
theorem birthDelayedInteriorJumpResidual_eq_predecessor_cutoff (d e k : ℕ) :
    birthDelayedInteriorJumpResidual (d + 2) e k =
      anchoredInteriorSawtoothAtom e (d + 2 - 1 + (d + 2) * k) -
        (if e ≤ d + 2 - 1 + (d + 2) * k then
          interiorJumpOrbitMean (d + 2) e - ((e : ℝ) - 1) / (2 * (e : ℝ))
        else 0) := by
  have hnk : (k + 1) * (d + 2) = d + 2 - 1 + (d + 2) * k + 1 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm k (d + 2)]
    omega
  have hiff : e / (d + 2) ≤ k ↔ e ≤ d + 2 - 1 + (d + 2) * k := by
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega), hnk]
    omega
  simp only [birthDelayedInteriorJumpResidual, hiff]

/-- The signed conditional mean with the exact modulus-birth threshold. -/
def birthDelayedInteriorJumpDrift (N d k : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ e ∈ Icc 1 N, c e *
    (if e / d ≤ k then
      interiorJumpOrbitMean d e - ((e : ℝ) - 1) / (2 * (e : ℝ)) else 0)

/-- The horizon-free arithmetic prefix satisfies the pair estimate after both explicit drift corrections are retained. -/
theorem abs_pmBezoutInteriorPrefix_birthDelayed_compensated_le
    (ε : ℝ) (d T L : ℕ) :
    let N := (d + 2) * L
    |∑ k ∈ range L, interiorJumpCompensatedWeight ⟨d + 2, by omega⟩ T k *
      (pmBezoutInteriorPrefix ε (d + 2 - 1 + (d + 2) * k) -
        ((d + 2 - 1 + (d + 2) * k : ℕ) : ℝ) *
          (selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1 -
            (RHTower.pmPowerDampedDivisorDensity ε).re) -
        birthDelayedInteriorJumpDrift N (d + 2) k (pmPowerDampedRealWeight ε))| ≤
      ∑ e ∈ Icc 1 N, |pmPowerDampedRealWeight ε e| *
        (1 / ((d : ℝ) + 2) + 2 / (Nat.gcd (d + 2) e : ℝ)) := by
  dsimp only
  have heq (k : ℕ) (hk : k ∈ range L) :
      pmBezoutInteriorPrefix ε (d + 2 - 1 + (d + 2) * k) -
          ((d + 2 - 1 + (d + 2) * k : ℕ) : ℝ) *
            (selbergMultiplesCoord ((d + 2) * L) (pmPowerDampedRealWeight ε) 1 -
              (RHTower.pmPowerDampedDivisorDensity ε).re) =
        bezoutInteriorSawtoothSum ((d + 2) * L) (pmPowerDampedRealWeight ε)
          (d + 2 - 1 + (d + 2) * k) -
          weightedCenteredSawtoothSum ((d + 2) * L) (pmPowerDampedRealWeight ε) 0 := by
    have hkL : k + 1 ≤ L := mem_range.mp hk
    have hnk : d + 2 - 1 + (d + 2) * k + 1 = (d + 2) * (k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have h := pmBezoutInteriorPrefix_sub_bezoutInteriorSawtoothSum_eq_affine ε
      (N := (d + 2) * L) (n := d + 2 - 1 + (d + 2) * k) (by omega)
      (by rw [hnk]; exact Nat.mul_le_mul_left (d + 2) hkL)
    linarith
  have h := abs_bezoutInteriorSawtoothSum_birthDelayed_compensated_le
    ((d + 2) * L) T L d (pmPowerDampedRealWeight ε)
  simp only [birthDelayedInteriorJumpDrift]
  refine le_of_eq_of_le ?_ h
  apply congrArg abs
  apply sum_congr rfl
  intro k hk
  rw [heq k hk]

end
end GaloisForLFunctions.BezoutValuationIncidence
