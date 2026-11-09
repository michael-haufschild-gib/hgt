import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates

/-!
# The other side at every gap set

The upper side has no blind spot: a real zero `½ + x`, `x > 0`, enters the traces with a positive
coefficient and pushes them up. With the odd two-bump width criterion
(`re_le_iff_lag_twoBump_ge_neg_exp_of_pos`: `Re W(B − τ_v B) = 2 Re S(0) − 2 Re S(v) ≥ −C e^{σv}`
iff every zero has `Re ρ ≤ ½ + σ`, real zeros included) the gap method iterates from above as from
below (`width_step_of_powGaps_above`).

**Theorem** (`onLine_of_bddAbove_of_powGaps`). For every tempered configuration in the open strip
and every degree set with gaps `O(x^θ)`, `θ < 1`, an upper bound `2 Re S_Z(log d) ≤ K` at the degrees
puts every zero on the critical line. No hypothesis on real zeros and no attained maximum.

At the primes (`onLine_of_bddAbove_primes`), at the `pᵏ` (`onLine_of_bddAbove_kthPrimePowers`); for
a primitive character, an upper bound at the primes is GRH for `L(s, χ)`
(`grh_of_bddAbove_primes`), Siegel zeros included.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **One step of the gap method from above.** At width `a`, an upper bound `K d^σ` at a degree set
with gaps `O(x^θ)` gives width `max(σ, a + θ − 1)`. -/
theorem width_step_of_powGaps_above (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {σ θ a : ℝ} (hσ0 : 0 ≤ σ) (hθ1 : θ < 1) (ha0 : 0 ≤ a)
    (hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a) {D : Set ℕ} (hD : PowGaps θ D) {K : ℝ}
    (hK : ∀ d ∈ D, 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re ≤ K * (d : ℝ) ^ σ) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + max σ (a + θ - 1) := by
  have hb := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hbc := hasCompactSupport_of_support_subset_abs hbs
  have hsees : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → evenCoeff Z (boxSpline 1 3) (ρ - 1 / 2) ≠ 0 :=
    fun ρ hρ h => evenCoeff_sub_half_ne_zero_of_conj_symm Z hb.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  set a' := max σ (a + θ - 1) with ha'
  have ha'0 : 0 ≤ a' := hσ0.trans (le_max_left _ _)
  obtain ⟨C, T₀, hC0, hT₀0, htrans⟩ := exists_degree_trace_near hZ ha0 hwid hθ1 hD
  set A := 2 * (lagStructure Z (boxSpline 1 3) 0).re with hA
  have hrate : ∃ C' V : ℝ, ∀ v : ℝ, V ≤ v → -(C' * Real.exp (a' * v)) ≤
      (Z.W (twoBump (boxSpline 1 3) v (-1)) (twoBump (boxSpline 1 3) v (-1))).re := by
    refine ⟨|K| + C + |A|, T₀, fun v hv => ?_⟩
    rw [re_W_lag_eq Z hZ hb hbs v, ← hA]
    have hv0 : 0 ≤ v := hT₀0.trans hv
    obtain ⟨d, hdD, hdle, hvar⟩ := htrans v hv
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hD.1 d hdD
    have he : Real.exp ((a + θ - 1) * v) ≤ Real.exp (a' * v) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hv0)
    have hdσ : (d : ℝ) ^ σ ≤ Real.exp (a' * v) :=
      calc (d : ℝ) ^ σ ≤ Real.exp v ^ σ := Real.rpow_le_rpow hd0.le hdle hσ0
        _ = Real.exp (σ * v) := by rw [← Real.exp_mul, mul_comm]
        _ ≤ Real.exp (a' * v) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hv0)
    have hKd : K * (d : ℝ) ^ σ ≤ |K| * Real.exp (a' * v) :=
      (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hdσ (abs_nonneg K))
    have hvar' := (abs_le.mp hvar).2
    have hCe := mul_le_mul_of_nonneg_left he hC0
    have hone : 1 ≤ Real.exp (a' * v) := Real.one_le_exp (by positivity)
    have hAe : -A ≤ |A| * Real.exp (a' * v) := by nlinarith [neg_abs_le A, abs_nonneg A]
    linarith [hK d hdD]
  exact (re_le_iff_lag_twoBump_ge_neg_exp_of_pos Z hZ hlt hb hbs
    (fun x hx hxre him => evenCoeff_spline_pos_of_real Z hx hxre him) hsees ha'0).mpr hrate

/-- **The gap method iterates from above.** An upper bound `K d^σ`, `σ ≥ 0`, at a degree set with
power-saving gaps puts every zero at `Re ρ ≤ ½ + σ`, real zeros included. -/
theorem re_le_of_bddAbove_rpow_of_powGaps (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {σ θ : ℝ} (hσ0 : 0 ≤ σ) (hθ1 : θ < 1) {D : Set ℕ}
    (hD : PowGaps θ D) {K : ℝ}
    (hK : ∀ d ∈ D, 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re ≤ K * (d : ℝ) ^ σ) :
    ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + σ := by
  have hstep : ∀ n : ℕ, ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + max σ (1 / 2 - n * (1 - θ)) := by
    intro n
    induction n with
    | zero =>
      intro ρ hρ
      have h1 := hlt ρ hρ
      have : (1 : ℝ) / 2 ≤ max σ (1 / 2 - ((0 : ℕ) : ℝ) * (1 - θ)) := by
        rw [Nat.cast_zero, zero_mul, sub_zero]; exact le_max_right _ _
      linarith
    | succ n ih =>
      have ha0 : 0 ≤ max σ (1 / 2 - n * (1 - θ)) := hσ0.trans (le_max_left _ _)
      have h := width_step_of_powGaps_above Z hZ hlt hσ0 hθ1 ha0 ih hD hK
      have hnew : max σ (max σ (1 / 2 - n * (1 - θ)) + θ - 1) ≤
          max σ (1 / 2 - ((n + 1 : ℕ) : ℝ) * (1 - θ)) := by
        push_cast
        apply max_le (le_max_left _ _)
        rcases le_total σ (1 / 2 - n * (1 - θ)) with h0 | h0
        · rw [max_eq_right h0]; exact le_max_of_le_right (by linarith)
        · rw [max_eq_left h0]; exact le_max_of_le_left (by linarith)
      intro ρ hρ
      linarith [h ρ hρ]
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * (1 - θ)))
  have hθ0 : 0 < 1 - θ := by linarith
  have hn' : 1 / 2 - n * (1 - θ) ≤ σ := by
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  intro ρ hρ
  have := hstep n ρ hρ
  rw [max_eq_left hn'] at this
  exact this

/-- **From above, every degree set with power-saving gaps decides the line**, real zeros included. -/
theorem onLine_of_bddAbove_of_powGaps (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ} (hD : PowGaps θ D)
    {K : ℝ} (hK : ∀ d ∈ D, 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have h := re_le_of_bddAbove_rpow_of_powGaps Z hZ hlt le_rfl hθ1 hD (K := K)
    fun d hd => by rw [Real.rpow_zero, mul_one]; exact hK d hd
  intro ρ hρ
  have h1 := h ρ hρ
  have h2 := h _ (Z.reflect_mem ρ hρ)
  have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
  rw [hrefl] at h2
  linarith

/-- **An upper bound at the primes decides the line** for every configuration in the open strip. -/
theorem onLine_of_bddAbove_primes (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_bddAbove_of_powGaps Z hZ hlt (θ := 2 / 3) (K := K) (by norm_num)
    (powGaps_primes (by norm_num) (by norm_num)) fun d hd => hK d hd

/-- **An upper bound at the `k`-th prime powers decides the line.** -/
theorem onLine_of_bddAbove_kthPrimePowers (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {k : ℕ} (hk : 1 ≤ k) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → 2 * (lagStructure Z (boxSpline 1 3) (k * Real.log p)).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hk0 : (0 : ℝ) < 3 * k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine onLine_of_bddAbove_of_powGaps Z hZ hlt (θ := 1 - 1 / (3 * k)) (K := K)
    (by have := one_div_pos.mpr hk0; linarith) (powGaps_kthPrimePowers hk) ?_
  rintro d ⟨p, hp, rfl⟩
  have := hK p hp
  rwa [Nat.cast_pow, Real.log_pow]

/-- **GRH from above at the primes.** For a primitive character, an upper bound on the spline traces
of the zeros of `L(s, χ)` at the primes puts every zero on the critical line. -/
theorem grh_of_bddAbove_primes {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 1 < q)
    (hprim : χ.IsPrimitive) {K : ℝ}
    (hK : ∀ p : ℕ, p.Prime → 2 * (lagStructure (ThmE.LZeros (ThmE.LSeam_of hq hprim))
      (boxSpline 1 3) (Real.log p)).re ≤ K) :
    ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re = 1 / 2 :=
  onLine_of_bddAbove_primes _ (temperedConfig_LZeros hq hprim) (fun _ hρ => hρ.2.2) hK

end GaloisForLFunctions.SurfaceOfSpecZ
