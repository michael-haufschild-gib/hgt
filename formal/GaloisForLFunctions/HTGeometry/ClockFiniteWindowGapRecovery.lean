import GaloisForLFunctions.HTGeometry.ClockPowerGapRecovery

/-!
# Exact recovery from a finite observation window

For a power gap of positive integral order `k = q + 1`, a globally `L`-Lipschitz
error field with anchor `a` and weighted noise bounded on `|x| ≤ R` exists exactly
when an endpoint inequality holds and the global sharp inequality holds whenever
the critical radius lies in the observed window. The signed distance tent realizes
every feasible value. Zero radius and zero Lipschitz constant are included.

The critical-radius identity uses totalized division at `L = 0`; its zero value
there asserts no global maximum. The finite-window classification requires no
observations outside the stated radius and no extension assumption.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Exact envelope value at the algebraic critical radius, including totalized `L = 0`. -/
theorem powerClockGap_critical_radius_value (q : ℕ) (L : NNReal) (a : ℝ) :
    let t : ℝ := ((q + 1 : ℕ) : ℝ) * |a| / (((q + 2 : ℕ) : ℝ) * L)
    |t| ^ (q + 1) * clockGapEnvelope L 0 a t =
      (((q + 1 : ℕ) : ℝ) ^ (q + 1) * |a| ^ (q + 2)) /
        (((q + 2 : ℕ) : ℝ) ^ (q + 2) * (L : ℝ) ^ (q + 1)) := by
  dsimp only
  by_cases hL : (L : ℝ) = 0
  · simp [hL, clockGapEnvelope]
  · let k := q + 1
    let t : ℝ := (k : ℝ) * |a| / (((k + 1 : ℕ) : ℝ) * L)
    let B : ℝ := ((k + 1 : ℕ) : ℝ) ^ (k + 1) * (L : ℝ) ^ k
    have hLpos : 0 < (L : ℝ) := lt_of_le_of_ne L.coe_nonneg (Ne.symm hL)
    have hB : 0 < B := by dsimp [B]; positivity
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have htrel : ((k + 1 : ℕ) : ℝ) * L * t = (k : ℝ) * |a| := by
      dsimp [t]
      field_simp
    have hcrest : ((k + 1 : ℕ) : ℝ) * (|a| - (L : ℝ) * t) = |a| := by
      push_cast at htrel ⊢
      nlinarith
    have hcone : 0 ≤ |a| - (L : ℝ) * t := by
      have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      nlinarith [abs_nonneg a]
    change |t| ^ k * clockGapEnvelope L 0 a t = (k : ℝ) ^ k * |a| ^ (k + 1) / B
    rw [clockGapEnvelope, Real.dist_eq, sub_zero, abs_of_nonneg ht, max_eq_right hcone]
    apply (eq_div_iff hB.ne').mpr
    calc
      _ = (((k + 1 : ℕ) : ℝ) * L * t) ^ k *
          (((k + 1 : ℕ) : ℝ) * (|a| - (L : ℝ) * t)) := by
            dsimp [B]
            simp only [mul_pow, pow_succ]
            ring
      _ = (k : ℝ) ^ k * |a| ^ (k + 1) := by
        rw [htrel, hcrest, mul_pow, pow_succ]
        ring

/-- Every finite-window envelope bound is equivalent to two scalar tests. -/
theorem finiteWindowClockGap_envelope_iff (q : ℕ) (L epsilon R : NNReal) (a : ℝ) :
    (∀ x : ℝ, |x| ≤ R → |x| ^ (q + 1) * clockGapEnvelope L 0 a x ≤ epsilon) ↔
      (R : ℝ) ^ (q + 1) * |a| ≤ (epsilon : ℝ) + (L : ℝ) * (R : ℝ) ^ (q + 2) ∧
      (((q + 1 : ℕ) : ℝ) * |a| ≤ ((q + 2 : ℕ) : ℝ) * L * R →
        ((q + 1 : ℕ) : ℝ) ^ (q + 1) * |a| ^ (q + 2) ≤
          ((q + 2 : ℕ) : ℝ) ^ (q + 2) * (L : ℝ) ^ (q + 1) * epsilon) := by
  let k := q + 1
  have hk : (0 : ℝ) < k := by dsimp [k]; positivity
  constructor
  · intro h
    constructor
    · have he := h R (by rw [abs_of_nonneg R.coe_nonneg])
      simp only [clockGapEnvelope, Real.dist_eq, sub_zero, abs_of_nonneg R.coe_nonneg] at he
      have hlo := mul_le_mul_of_nonneg_left
        (le_max_right (0 : ℝ) (|a| - (L : ℝ) * R)) (pow_nonneg R.coe_nonneg k)
      change (R : ℝ) ^ k * |a| ≤ (epsilon : ℝ) + (L : ℝ) * (R : ℝ) ^ (k + 1)
      rw [pow_succ (R : ℝ) k]
      nlinarith
    · intro hcrit
      by_cases hL : (L : ℝ) = 0
      · have ha : |a| = 0 := by
          simp only [hL, mul_zero, zero_mul] at hcrit
          change (k : ℝ) * |a| ≤ 0 at hcrit
          nlinarith [abs_nonneg a]
        simp [ha, hL]
      · have hLpos : 0 < (L : ℝ) := lt_of_le_of_ne L.coe_nonneg (Ne.symm hL)
        let t : ℝ := (k : ℝ) * |a| / (((k + 1 : ℕ) : ℝ) * L)
        have ht : 0 ≤ t := by dsimp [t]; positivity
        have htR : t ≤ R := by
          dsimp [t]
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * L)).mpr
          nlinarith only [hcrit]
        have hp := h t (by rw [abs_of_nonneg ht]; exact htR)
        have hval := powerClockGap_critical_radius_value q L a
        change |t| ^ k * clockGapEnvelope L 0 a t = _ at hval
        rw [hval] at hp
        have hB : (0 : ℝ) < ((q + 2 : ℕ) : ℝ) ^ (q + 2) * (L : ℝ) ^ (q + 1) :=
          by positivity
        have hc := (div_le_iff₀ hB).mp hp
        nlinarith only [hc]
  · rintro ⟨hedge, hcrit⟩ x hxR
    by_cases hinside : ((q + 1 : ℕ) : ℝ) * |a| ≤ ((q + 2 : ℕ) : ℝ) * L * R
    · exact (powerClockGap_envelope_iff q L epsilon a).mpr (hcrit hinside) x
    · have hD : 0 ≤ (k : ℝ) * |a| - ((k + 1 : ℕ) : ℝ) * L * R := by
        change ¬ (k : ℝ) * |a| ≤ ((k + 1 : ℕ) : ℝ) * L * R at hinside
        linarith
      dsimp [clockGapEnvelope]
      rw [Real.dist_eq, sub_zero]
      by_cases hx : 0 ≤ |a| - (L : ℝ) * |x|
      · rw [max_eq_right hx]
        have hber := pow_add_mul_le_add_pow (a := |x|) (b := (R : ℝ) - |x|)
          (abs_nonneg x) (by linarith [abs_nonneg x, R.coe_nonneg]) (k + 1)
        simp only [Nat.add_sub_cancel] at hber
        rw [show |x| + ((R : ℝ) - |x|) = R by ring, pow_succ |x| k] at hber
        have hbern : |x| ^ k * (((k + 1 : ℕ) : ℝ) * R - (k : ℝ) * |x|) ≤
            (R : ℝ) ^ (k + 1) := by
          push_cast at hber ⊢
          nlinarith only [hber]
        have hl := mul_le_mul_of_nonneg_left hbern L.coe_nonneg
        have hp := pow_le_pow_left₀ (abs_nonneg x) hxR k
        have hd := mul_le_mul_of_nonneg_left hp hD
        have hm : (k : ℝ) * (|x| ^ k * (|a| - (L : ℝ) * |x|)) ≤
            (k : ℝ) * ((R : ℝ) ^ k * (|a| - (L : ℝ) * R)) := by
          rw [pow_succ (R : ℝ) k] at hl
          push_cast at hl hd ⊢
          nlinarith only [hl, hd]
        have hmono := (mul_le_mul_iff_right₀ hk).mp hm
        change (R : ℝ) ^ k * |a| ≤ (epsilon : ℝ) + (L : ℝ) * (R : ℝ) ^ (k + 1) at hedge
        rw [pow_succ (R : ℝ) k] at hedge
        change |x| ^ k * (|a| - (L : ℝ) * |x|) ≤ epsilon
        nlinarith only [hmono, hedge]
      · rw [max_eq_left (le_of_not_ge hx), mul_zero]
        exact epsilon.coe_nonneg

/-- Exact finite-window feasible-anchor classification for every positive integer order. -/
theorem finiteWindowClockGap_feasible_iff (q : ℕ) (L epsilon R : NNReal) (a : ℝ) :
    (∃ u : ℝ → ℝ, LipschitzWith L u ∧ u 0 = a ∧
      ∀ x : ℝ, |x| ≤ R → |x| ^ (q + 1) * |u x| ≤ epsilon) ↔
      (R : ℝ) ^ (q + 1) * |a| ≤ (epsilon : ℝ) + (L : ℝ) * (R : ℝ) ^ (q + 2) ∧
      (((q + 1 : ℕ) : ℝ) * |a| ≤ ((q + 2 : ℕ) : ℝ) * L * R →
        ((q + 1 : ℕ) : ℝ) ^ (q + 1) * |a| ^ (q + 2) ≤
          ((q + 2 : ℕ) : ℝ) ^ (q + 2) * (L : ℝ) ^ (q + 1) * epsilon) := by
  rw [← finiteWindowClockGap_envelope_iff]
  constructor
  · rintro ⟨u, hu, ha, hbound⟩ x hx
    exact (mul_le_mul_of_nonneg_left
      ((clockGapEnvelope_isLeast L 0 a x).2 ⟨u, hu, ha, rfl⟩)
      (pow_nonneg (abs_nonneg x) _)).trans (hbound x hx)
  · intro h
    refine ⟨clockGapExtremizer L 0 a, clockGapExtremizer_lipschitz L 0 a,
      clockGapExtremizer_anchor L 0 a, ?_⟩
    intro x hx
    rw [clockGapExtremizer_abs]
    exact h x hx

/-- The explicit signed tent satisfies precisely the two finite-window scalar tests. -/
theorem finiteWindowClockGap_extremizer_bound_iff (q : ℕ) (L epsilon R : NNReal) (a : ℝ) :
    (∀ x : ℝ, |x| ≤ R → |x| ^ (q + 1) * |clockGapExtremizer L 0 a x| ≤ epsilon) ↔
      (R : ℝ) ^ (q + 1) * |a| ≤ (epsilon : ℝ) + (L : ℝ) * (R : ℝ) ^ (q + 2) ∧
      (((q + 1 : ℕ) : ℝ) * |a| ≤ ((q + 2 : ℕ) : ℝ) * L * R →
        ((q + 1 : ℕ) : ℝ) ^ (q + 1) * |a| ^ (q + 2) ≤
          ((q + 2 : ℕ) : ℝ) ^ (q + 2) * (L : ℝ) ^ (q + 1) * epsilon) := by
  simp only [clockGapExtremizer_abs]
  exact finiteWindowClockGap_envelope_iff q L epsilon R a

end GaloisForLFunctions.HTGeometry
