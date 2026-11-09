import GaloisForLFunctions.SurfaceOfSpecZ.OneFrobeniusIsNotASamplingSet

/-!
# The tensor powers at every gap set

`TheTensorPowersHaveACommonAbscissa` reads RH as Deligne's uniformity in `k`: the series of the even
tensor powers `M^{⊗2k}` of the virtual motive of the zeros have a common half-plane of convergence.
With the width law at every gap set (`TheWidthLawAtEveryGapSet`) the same holds at any degree set
`D` with power-saving gaps and for every configuration without real zeros:

**Theorem** (`onLine_iff_tensorPowers_commonAbscissa_of_powGaps`). For a tempered configuration
without real zeros and `D` with gaps `O(x^θ)`, `θ < 1`, every zero lies on the line iff there is
`σ₀` with `Σ_{d ∈ D} (2 Re S(log d))^{2k} d^{−σ₀} < ∞` for every `k ≥ 1`.

On the line the traces are bounded, and `σ₀ = 2` works for every `k`. Conversely one term gives
`|2 Re S(log d)| ≤ C_k d^{|σ₀|/(2k)}` on `D`, the width law gives width `≤ |σ₀|/(2k)`, and `k → ∞`.
For `ζ` at the `nᵏ`, `D` has `O(x^{1/k})` elements.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- The `d`-th term of the `2k`-th moment at the degrees `D`. -/
def gapMomentTerm (Z : ZeroConfig) (D : Set ℕ) (k : ℕ) (σ : ℝ) (d : D) : ℝ :=
  (2 * (lagStructure Z (boxSpline 1 3) (Real.log (d : ℕ))).re) ^ (2 * k) * ((d : ℕ) : ℝ) ^ (-σ)

theorem gapMomentTerm_nonneg (Z : ZeroConfig) (D : Set ℕ) (k : ℕ) (σ : ℝ) (d : D) :
    0 ≤ gapMomentTerm Z D k σ d := by
  unfold gapMomentTerm
  refine mul_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _

/-- **The tensor powers at a gap set have a common abscissa iff the line.** -/
theorem onLine_iff_tensorPowers_commonAbscissa_of_powGaps (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {θ : ℝ} (hθ1 : θ < 1) {D : Set ℕ} (hD : PowGaps θ D) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔
      ∃ σ₀ : ℝ, ∀ k : ℕ, 1 ≤ k → Summable (gapMomentTerm Z D k σ₀) := by
  constructor
  · intro hon
    have hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + 0 := fun ρ hρ => by rw [hon ρ hρ]; simp
    set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖
    refine ⟨2, fun k _ => ?_⟩
    have hsum : Summable fun d : D => E ^ (2 * k) * (((d : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ :=
      ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).subtype D).mul_left _
    refine Summable.of_nonneg_of_le (gapMomentTerm_nonneg Z D k 2) (fun d => ?_) hsum
    have hd := hD.1 d d.2
    have hb := abs_two_re_lagStructure_log_le_of_width hZ hwid hd
    rw [Real.rpow_zero, mul_one] at hb
    have hpow : (2 * (lagStructure Z (boxSpline 1 3) (Real.log (d : ℕ))).re) ^ (2 * k) ≤
        E ^ (2 * k) := by
      rw [pow_mul, pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) (by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2) k
    unfold gapMomentTerm
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · rintro ⟨σ₀, hσ₀⟩
    -- every large `k` bounds the width by `|σ₀|/(2k)`
    have hwidth : ∀ k : ℕ, 1 + |σ₀| < k → ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + |σ₀| / (2 * k) := by
      intro k hk
      have hk1 : 1 ≤ k := by
        have : (1 : ℝ) < k := by linarith [abs_nonneg σ₀]
        exact_mod_cast this.le
      have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg σ₀]
      have hs := hσ₀ k hk1
      set T := ∑' d, gapMomentTerm Z D k σ₀ d with hT
      set a : ℝ := |σ₀| / (2 * k) with ha
      have ha0 : 0 ≤ a := by rw [ha]; positivity
      have ha1 : a < 1 / 2 := by rw [ha, div_lt_iff₀ (by positivity)]; linarith
      refine (re_le_iff_bddBelow_rpow_of_powGaps Z hZ hnoreal ha0 ha1 hθ1 hD).mpr
        ⟨|T| ^ ((1 : ℝ) / (2 * k)), fun d hd => ?_⟩
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hD.1 d hd
      have hd0 : (0 : ℝ) < d := by linarith
      set c := 2 * (lagStructure Z (boxSpline 1 3) (Real.log d)).re with hc
      have hone : c ^ (2 * k) * (d : ℝ) ^ (-σ₀) ≤ T :=
        hs.le_tsum ⟨d, hd⟩ (fun j _ => gapMomentTerm_nonneg Z D k σ₀ j)
      have hc2k0 : 0 ≤ c ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
      have hc2k : |c| ^ (2 * k) ≤ |T| * (d : ℝ) ^ |σ₀| := by
        rw [show |c| ^ (2 * k) = c ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
        have hinv : (d : ℝ) ^ (-σ₀) * (d : ℝ) ^ σ₀ = 1 := by
          rw [← Real.rpow_add hd0]; simp
        have h1 : c ^ (2 * k) ≤ T * (d : ℝ) ^ σ₀ := by
          have := mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg hd0.le σ₀)
          calc c ^ (2 * k) = c ^ (2 * k) * ((d : ℝ) ^ (-σ₀) * (d : ℝ) ^ σ₀) := by
                rw [hinv, mul_one]
            _ = c ^ (2 * k) * (d : ℝ) ^ (-σ₀) * (d : ℝ) ^ σ₀ := by ring
            _ ≤ _ := this
        have h2 : T * (d : ℝ) ^ σ₀ ≤ |T| * (d : ℝ) ^ |σ₀| :=
          mul_le_mul (le_abs_self T) (Real.rpow_le_rpow_of_exponent_le hd1 (le_abs_self σ₀))
            (Real.rpow_nonneg hd0.le _) (abs_nonneg T)
        linarith
      have hroot : |c| ≤ |T| ^ ((1 : ℝ) / (2 * k)) * (d : ℝ) ^ a := by
        have h1 := Real.rpow_le_rpow (by positivity) hc2k (by positivity : (0 : ℝ) ≤ 1 / (2 * k))
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c),
          show ((2 * k : ℕ) : ℝ) * (1 / (2 * k)) = 1 by push_cast; field_simp, Real.rpow_one,
          Real.mul_rpow (abs_nonneg T) (by positivity), ← Real.rpow_mul hd0.le] at h1
        rw [ha]
        convert h1 using 3
        ring
      linarith [neg_abs_le c]
    -- let `k → ∞`
    intro ρ hρ
    have hhalf : 1 / 2 ≤ ρ.re := by
      by_contra hlt
      push Not at hlt
      obtain ⟨k, hk⟩ := exists_nat_gt (max (1 + |σ₀|)
        (|σ₀| / (2 * (1 / 2 - ρ.re))))
      have hk1 : 1 + |σ₀| < k := (le_max_left _ _).trans_lt hk
      have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg σ₀]
      have := hwidth k hk1 _ (Z.reflect_mem ρ hρ)
      have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
      rw [hrefl] at this
      have hk2 : |σ₀| / (2 * (1 / 2 - ρ.re)) < k := (le_max_right _ _).trans_lt hk
      rw [div_lt_iff₀ (by linarith)] at hk2
      have : |σ₀| / (2 * k) < 1 / 2 - ρ.re := by
        rw [div_lt_iff₀ (by positivity)]; nlinarith
      linarith
    have hle : ρ.re ≤ 1 / 2 := by
      by_contra hlt
      push Not at hlt
      obtain ⟨k, hk⟩ := exists_nat_gt (max (1 + |σ₀|) (|σ₀| / (2 * (ρ.re - 1 / 2))))
      have hk1 : 1 + |σ₀| < k := (le_max_left _ _).trans_lt hk
      have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg σ₀]
      have := hwidth k hk1 ρ hρ
      have hk2 : |σ₀| / (2 * (ρ.re - 1 / 2)) < k := (le_max_right _ _).trans_lt hk
      rw [div_lt_iff₀ (by linarith)] at hk2
      have : |σ₀| / (2 * k) < ρ.re - 1 / 2 := by
        rw [div_lt_iff₀ (by positivity)]; nlinarith
      linarith
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
