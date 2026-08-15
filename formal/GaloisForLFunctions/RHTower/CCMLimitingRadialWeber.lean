import GaloisForLFunctions.RHTower.ArcsineZetaTransform

/-!
# The limiting radial first row: exact phases and the arithmetic sum

Three exact mechanisms of the card are formalized.

*The bulk difference phase and its unique critical point.*  For `φ_k(r) = r − √(k²r² + k² − 1)` the
derivative is `1 − k²r/√(k²r²+k²−1)`; it vanishes exactly at `r = 1/k`, and the second derivative
there is `−(k²−1)/k`.  These are `(7)`–`(8)`.

*The endpoint phase is nonstationary.*  After `w = z²` the second Bessel phase
`Θ(w) = √(k²w + c²(k²−1))` has derivative `k²/(2√(k²w+c²(k²−1)))`, which is `(10)`; it never
vanishes, which is why one integration by parts suffices.

*The logarithmically weighted first row sums.*  From the uniform bound `(3)` the weighted sum `(4)`
is bounded by `C c^{-1/2}` times the convergent constant `∑_{k≥2} log k/k²`.

Dunster's radial Bessel model, the Bessel symbol decomposition `(5)`, the stationary-phase lemma,
and the Weber transform `(13)` are cited parents and stay outside the Lean statement.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The bulk difference phase -/

/-- The bulk difference phase `(7)`. -/
def radialPhase (k r : ℝ) : ℝ := r - Real.sqrt (k ^ 2 * r ^ 2 + k ^ 2 - 1)

/-- The derivative of the bulk difference phase. -/
def radialPhaseDeriv (k r : ℝ) : ℝ :=
  1 - k ^ 2 * r / Real.sqrt (k ^ 2 * r ^ 2 + k ^ 2 - 1)

theorem hasDerivAt_radialPhase {k r : ℝ} (hpos : 0 < k ^ 2 * r ^ 2 + k ^ 2 - 1) :
    HasDerivAt (radialPhase k) (radialPhaseDeriv k r) r := by
  have hs : 0 < Real.sqrt (k ^ 2 * r ^ 2 + k ^ 2 - 1) := Real.sqrt_pos.mpr hpos
  have hu : HasDerivAt (fun s : ℝ => k ^ 2 * s ^ 2 + k ^ 2 - 1) (k ^ 2 * (2 * r)) r := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_id r).fun_pow 2
    simpa using ((h1.const_mul (k ^ 2)).add_const (k ^ 2)).sub_const 1
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (k ^ 2 * s ^ 2 + k ^ 2 - 1))
      (k ^ 2 * (2 * r) / (2 * Real.sqrt (k ^ 2 * r ^ 2 + k ^ 2 - 1))) r :=
    hu.sqrt (ne_of_gt hpos)
  have hid : HasDerivAt (fun s : ℝ => s) 1 r := hasDerivAt_id r
  have hsub := hid.fun_sub hsqrt
  refine hsub.congr_deriv ?_
  rw [radialPhaseDeriv]
  field_simp

/-- **Equation (8), critical point.**  The bulk phase is stationary exactly at `r = 1/k`. -/
theorem radialPhaseDeriv_critical {k : ℝ} (hk : 1 < k) : radialPhaseDeriv k (1 / k) = 0 := by
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk
  have hinner : k ^ 2 * (1 / k) ^ 2 + k ^ 2 - 1 = k ^ 2 := by
    field_simp
    ring
  rw [radialPhaseDeriv, hinner, Real.sqrt_sq (le_of_lt hk0)]
  field_simp
  norm_num

/-- The second derivative of the bulk difference phase. -/
def radialPhaseSecondDeriv (k r : ℝ) : ℝ :=
  -(k ^ 2) / Real.sqrt (k ^ 2 * r ^ 2 + k ^ 2 - 1)
    + k ^ 4 * r ^ 2 / (Real.sqrt (k ^ 2 * r ^ 2 + k ^ 2 - 1)) ^ 3

theorem hasDerivAt_radialPhaseDeriv {k r : ℝ} (hpos : 0 < k ^ 2 * r ^ 2 + k ^ 2 - 1) :
    HasDerivAt (radialPhaseDeriv k) (radialPhaseSecondDeriv k r) r := by
  have hs : 0 < Real.sqrt (k ^ 2 * r ^ 2 + k ^ 2 - 1) := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt (k ^ 2 * r ^ 2 + k ^ 2 - 1) ^ 2 = k ^ 2 * r ^ 2 + k ^ 2 - 1 :=
    Real.sq_sqrt (le_of_lt hpos)
  have hu : HasDerivAt (fun s : ℝ => k ^ 2 * s ^ 2 + k ^ 2 - 1) (k ^ 2 * (2 * r)) r := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_id r).fun_pow 2
    simpa using ((h1.const_mul (k ^ 2)).add_const (k ^ 2)).sub_const 1
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (k ^ 2 * s ^ 2 + k ^ 2 - 1))
      (k ^ 2 * (2 * r) / (2 * Real.sqrt (k ^ 2 * r ^ 2 + k ^ 2 - 1))) r :=
    hu.sqrt (ne_of_gt hpos)
  have hnum : HasDerivAt (fun s : ℝ => k ^ 2 * s) (k ^ 2) r := by
    simpa using (hasDerivAt_id r).const_mul (k ^ 2)
  have hdiv := hnum.fun_div hsqrt (ne_of_gt hs)
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 r := hasDerivAt_const r 1
  have hsub := hone.fun_sub hdiv
  refine hsub.congr_deriv ?_
  rw [radialPhaseSecondDeriv]
  rw [show k ^ 2 * r ^ 2 + k ^ 2 - 1 = Real.sqrt (k ^ 2 * r ^ 2 + k ^ 2 - 1) ^ 2 from hsq.symm]
  field_simp
  ring

/-- **Equation (8), curvature.**  At the critical point the curvature is `−(k²−1)/k`. -/
theorem radialPhaseSecondDeriv_critical {k : ℝ} (hk : 1 < k) :
    radialPhaseSecondDeriv k (1 / k) = -((k ^ 2 - 1) / k) := by
  have hk0 : (0 : ℝ) < k := lt_trans zero_lt_one hk
  have hinner : k ^ 2 * (1 / k) ^ 2 + k ^ 2 - 1 = k ^ 2 := by
    field_simp
    ring
  rw [radialPhaseSecondDeriv, hinner, Real.sqrt_sq (le_of_lt hk0)]
  field_simp
  ring

/-! ## The endpoint phase is nonstationary -/

/-- The endpoint phase `(10)` after the substitution `w = z²`. -/
def weberPhase (c k w : ℝ) : ℝ := Real.sqrt (k ^ 2 * w + c ^ 2 * (k ^ 2 - 1))

/-- **Equation (10).**  The endpoint phase derivative is `k²/(2√(k²w + c²(k²−1)))`, which never
vanishes. -/
theorem hasDerivAt_weberPhase {c k w : ℝ} (hpos : 0 < k ^ 2 * w + c ^ 2 * (k ^ 2 - 1)) :
    HasDerivAt (weberPhase c k)
      (k ^ 2 / (2 * Real.sqrt (k ^ 2 * w + c ^ 2 * (k ^ 2 - 1)))) w := by
  have hu : HasDerivAt (fun s : ℝ => k ^ 2 * s + c ^ 2 * (k ^ 2 - 1)) (k ^ 2) w := by
    simpa using ((hasDerivAt_id w).const_mul (k ^ 2)).add_const (c ^ 2 * (k ^ 2 - 1))
  exact hu.sqrt (ne_of_gt hpos)

theorem weberPhase_deriv_ne_zero {c k w : ℝ} (hk : k ≠ 0)
    (hpos : 0 < k ^ 2 * w + c ^ 2 * (k ^ 2 - 1)) :
    k ^ 2 / (2 * Real.sqrt (k ^ 2 * w + c ^ 2 * (k ^ 2 - 1))) ≠ 0 := by
  have hs : 0 < Real.sqrt (k ^ 2 * w + c ^ 2 * (k ^ 2 - 1)) := Real.sqrt_pos.mpr hpos
  have hk2 : (0 : ℝ) < k ^ 2 := by positivity
  positivity

/-! ## The logarithmically weighted first row -/

/-- **Equation (4), finite form.**  The uniform bound `(3)` makes the logarithmically weighted first
row bounded termwise by `C c^{-1/2}` times the arithmetic weight `log k / k²`, whose sum converges
(corpus lemma `GaloisForLFunctions.summable_log_div_sq`). -/
theorem weighted_firstRow_le {M : ℕ → ℝ} {C c : ℝ} (hc : 0 < c)
    (hM : ∀ k : ℕ, |M k| ≤ C / (Real.sqrt c * (k : ℝ) ^ 2)) (s : Finset ℕ) :
    (∑ k ∈ s, Real.log k * |M k|)
      ≤ (C / Real.sqrt c) * ∑ k ∈ s, Real.log k / (k : ℝ) ^ 2 := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hlog : (0 : ℝ) ≤ Real.log k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · refine Real.log_nonneg ?_
      exact_mod_cast hk
  have hbound := hM k
  have hrw : C / Real.sqrt c * (Real.log k / (k : ℝ) ^ 2)
      = Real.log k * (C / (Real.sqrt c * (k : ℝ) ^ 2)) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk0 : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hbound hlog

/-- **Equation (4).**  The full logarithmically weighted first row is `O(c^{-1/2})`. -/
theorem tsum_weighted_firstRow_le {M : ℕ → ℝ} {C c : ℝ} (hc : 0 < c)
    (hM : ∀ k : ℕ, |M k| ≤ C / (Real.sqrt c * (k : ℝ) ^ 2)) :
    (∑' k : ℕ, Real.log k * |M k|)
      ≤ (C / Real.sqrt c) * ∑' k : ℕ, Real.log k / (k : ℝ) ^ 2 := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hweight : Summable (fun k : ℕ => Real.log k / (k : ℝ) ^ 2) := summable_log_div_sq
  have hscaled : Summable (fun k : ℕ => (C / Real.sqrt c) * (Real.log k / (k : ℝ) ^ 2)) :=
    hweight.mul_left _
  have hterm : ∀ k : ℕ, Real.log k * |M k|
      ≤ (C / Real.sqrt c) * (Real.log k / (k : ℝ) ^ 2) := by
    intro k
    have hlog : (0 : ℝ) ≤ Real.log k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · refine Real.log_nonneg ?_
        exact_mod_cast hk
    have hbound := hM k
    have hrw : C / Real.sqrt c * (Real.log k / (k : ℝ) ^ 2)
        = Real.log k * (C / (Real.sqrt c * (k : ℝ) ^ 2)) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have hk0 : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hbound hlog
  have hnonneg : ∀ k : ℕ, 0 ≤ Real.log k * |M k| := by
    intro k
    have hlog : (0 : ℝ) ≤ Real.log k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · refine Real.log_nonneg ?_
        exact_mod_cast hk
    exact mul_nonneg hlog (abs_nonneg _)
  have hsummable : Summable (fun k : ℕ => Real.log k * |M k|) :=
    Summable.of_nonneg_of_le hnonneg hterm hscaled
  rw [← tsum_mul_left]
  exact Summable.tsum_mono hsummable hscaled hterm

end GaloisForLFunctions.RHTower

end
