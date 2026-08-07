import GaloisForLFunctions.HTGeometry.EntireBezout
import GaloisForLFunctions.RHTower.HedenmalmTwoPrimeNormalFrame

/-!
# The two-prime Bezout identity for the centered interval multipliers

The centered multiplier `a_n(z) = 2 n^{-1/2} sin(z log n / 2) / z` extends across the origin with
the value `n^{-1/2} log n`; `centeredMultiplierE` is that entire representative, written as a
difference quotient of the sine.

Its zeros are the nonzero points of the arithmetic progression `2 pi k / log n`, all simple, and
the progressions for `n = 2` and `n = 3` are disjoint.  Wedderburn's lemma therefore produces
entire `b_2`, `b_3` with

```text
b_2 a_2 + b_3 a_3 = 1,
```

so the two centered prime windows generate the unit ideal of the ring of entire functions.  This is
equation `(13)` of the two-prime normal frame, and with `hat c_n = a_n Xi_C` it gives the ideal
identity `(14)`.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly

/-- The sine of the centered phase `z log n / 2`. -/
def sinPhase (n : ℕ) : ℂ → ℂ := fun w => Complex.sin (w * ((Real.log n / 2 : ℝ) : ℂ))

theorem hasDerivAt_sinPhase (n : ℕ) (w : ℂ) :
    HasDerivAt (sinPhase n)
      (Complex.cos (w * ((Real.log n / 2 : ℝ) : ℂ)) * ((Real.log n / 2 : ℝ) : ℂ)) w := by
  have h := ((hasDerivAt_id w).mul_const ((Real.log n / 2 : ℝ) : ℂ)).csin
  simp only [id_eq, one_mul] at h
  exact h

theorem differentiable_sinPhase (n : ℕ) : Differentiable ℂ (sinPhase n) :=
  fun w => (hasDerivAt_sinPhase n w).differentiableAt

@[simp] theorem sinPhase_zero (n : ℕ) : sinPhase n 0 = 0 := by
  simp [sinPhase]

/-- **The entire representative of the centered multiplier.**  The removable singularity at the
origin is filled in by the difference quotient of the sine. -/
def centeredMultiplierE (n : ℕ) : ℂ → ℂ := fun z =>
  2 * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * dslope (sinPhase n) 0 z

theorem differentiable_centeredMultiplierE (n : ℕ) :
    Differentiable ℂ (centeredMultiplierE n) := by
  have hd : Differentiable ℂ (dslope (sinPhase n) 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
      (differentiable_sinPhase n).differentiableOn
  exact (differentiable_const _).mul hd

/-- Off the origin the entire representative is the centered multiplier. -/
theorem centeredMultiplierE_eq (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    centeredMultiplierE n z = centeredMultiplier n z := by
  rw [centeredMultiplierE, dslope_of_ne _ hz, slope_def_field, sinPhase_zero, sinPhase,
    centeredMultiplier_eq_sin n hz]
  field_simp
  ring

/-- The value of the entire representative at the origin is `n^{-1/2} log n`. -/
theorem centeredMultiplierE_at_zero (n : ℕ) :
    centeredMultiplierE n 0
      = 2 * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * ((Real.log n / 2 : ℝ) : ℂ) := by
  rw [centeredMultiplierE, dslope_same, (hasDerivAt_sinPhase n 0).deriv]
  simp

theorem centeredMultiplierE_at_zero_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    centeredMultiplierE n 0 ≠ 0 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  rw [centeredMultiplierE_at_zero]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_
  · exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hnpos _).ne'
  · exact Complex.ofReal_ne_zero.mpr (by positivity)

/-- **The zero set of the entire centered multiplier** is exactly the nonzero part of the
arithmetic progression `2 pi k / log n`. -/
theorem centeredMultiplierE_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) {z : ℂ} :
    centeredMultiplierE n z = 0 ↔ ∃ k : {j : ℤ // j ≠ 0}, z = centeredZero n k := by
  rcases eq_or_ne z 0 with rfl | hz
  · constructor
    · intro h
      exact absurd h (centeredMultiplierE_at_zero_ne_zero hn)
    · rintro ⟨k, hk⟩
      exact absurd hk.symm (centeredZero_ne_zero hn k)
  · rw [centeredMultiplierE_eq n hz]
    exact centeredMultiplier_eq_zero_iff_mem_zeros hn hz

theorem eventuallyEq_centeredMultiplierE {n : ℕ} {w : ℂ} (hw : w ≠ 0) :
    centeredMultiplierE n =ᶠ[nhds w] centeredMultiplier n := by
  filter_upwards [isOpen_ne.mem_nhds hw] with z hz
  exact centeredMultiplierE_eq n hz

/-- The zeros of the entire centered multiplier are simple. -/
theorem deriv_centeredMultiplierE_ne_zero {n : ℕ} (hn : 2 ≤ n) (k : {j : ℤ // j ≠ 0}) :
    deriv (centeredMultiplierE n) (centeredZero n k) ≠ 0 := by
  rw [(eventuallyEq_centeredMultiplierE (n := n) (centeredZero_ne_zero hn k)).deriv_eq]
  exact deriv_centeredMultiplier_ne_zero hn k

theorem injective_centeredZero {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (centeredZero n) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hn1
  intro k l hkl
  rw [centeredZero, centeredZero, centeredMultiplierZero, centeredMultiplierZero,
    Complex.ofReal_inj] at hkl
  have hpi := Real.pi_pos
  have h1 : 2 * Real.pi * ((k : ℤ) : ℝ) = 2 * Real.pi * ((l : ℤ) : ℝ) := by
    have h := congrArg (fun x : ℝ => x * Real.log n) hkl
    simpa [div_mul_cancel₀, hlog.ne'] using h
  exact Subtype.ext
    (Int.cast_injective (mul_left_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0) h1))

theorem tendsto_norm_centeredZero_cofinite {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun k : {j : ℤ // j ≠ 0} => ‖centeredZero n k‖) cofinite atTop := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hpi := Real.pi_pos
  have habsZ : Tendsto (fun k : ℤ => |k|) cofinite atTop := by
    rw [Int.cofinite_eq]
    exact tendsto_sup.mpr ⟨tendsto_abs_atBot_atTop, tendsto_abs_atTop_atTop⟩
  have habs : Tendsto (fun k : ℤ => |(k : ℝ)|) cofinite atTop := by
    refine (tendsto_intCast_atTop_atTop.comp habsZ).congr fun k => ?_
    simp
  have hsub : Tendsto (fun k : {j : ℤ // j ≠ 0} => |((k : ℤ) : ℝ)|) cofinite atTop :=
    habs.comp (Subtype.val_injective.tendsto_cofinite)
  have hscale : Tendsto (fun k : {j : ℤ // j ≠ 0} =>
      (2 * Real.pi / Real.log n) * |((k : ℤ) : ℝ)|) cofinite atTop :=
    Tendsto.const_mul_atTop (by positivity) hsub
  refine hscale.congr fun k => ?_
  rw [centeredZero, norm_centeredMultiplierZero]
  rw [abs_div, abs_of_pos hlog, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  ring

/-- **The two-prime Bezout identity.**  The centered prime-2 and prime-3 multipliers generate the
unit ideal of the ring of entire functions. -/
theorem exists_two_prime_bezout :
    ∃ b₂ b₃ : ℂ → ℂ, Differentiable ℂ b₂ ∧ Differentiable ℂ b₃ ∧
      ∀ z : ℂ, b₂ z * centeredMultiplierE 2 z + b₃ z * centeredMultiplierE 3 z = 1 := by
  obtain ⟨a, b, ha, hb, hid⟩ :=
    exists_entire_bezout (ι := {j : ℤ // j ≠ 0})
      (differentiable_centeredMultiplierE 2) (differentiable_centeredMultiplierE 3)
      (w := centeredZero 2)
      (fun k => centeredZero_ne_zero (by norm_num) k)
      (fun k => (centeredMultiplierE_eq_zero_iff (by norm_num)).mpr ⟨k, rfl⟩)
      (fun k => deriv_centeredMultiplierE_ne_zero (by norm_num) k)
      (injective_centeredZero (by norm_num))
      (tendsto_norm_centeredZero_cofinite (by norm_num))
      (fun z hz => (centeredMultiplierE_eq_zero_iff (by norm_num)).mp hz)
      ⟨0, centeredMultiplierE_at_zero_ne_zero (by norm_num)⟩
      (fun k => by
        have hw : centeredZero 2 k ≠ 0 := centeredZero_ne_zero (by norm_num) k
        rw [centeredMultiplierE_eq 3 hw]
        intro h3
        have h2 : centeredMultiplier 2 (centeredZero 2 k) = 0 := by
          rw [← centeredMultiplierE_eq 2 hw]
          exact (centeredMultiplierE_eq_zero_iff (by norm_num)).mpr ⟨k, rfl⟩
        exact hw (no_common_zero_centered_two_three h2 h3))
  exact ⟨b, a, hb, ha, hid⟩

/-! ### The multiplier is even and real -/

theorem sinPhase_neg (n : ℕ) (w : ℂ) : sinPhase n (-w) = -sinPhase n w := by
  rw [sinPhase, sinPhase, show (-w) * ((Real.log n / 2 : ℝ) : ℂ)
    = -(w * ((Real.log n / 2 : ℝ) : ℂ)) by ring, Complex.sin_neg]

/-- **The centered multiplier is even**, `a_n(-z) = a_n(z)`. -/
theorem centeredMultiplierE_neg (n : ℕ) (z : ℂ) :
    centeredMultiplierE n (-z) = centeredMultiplierE n z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [centeredMultiplierE, centeredMultiplierE, dslope_of_ne _ (neg_ne_zero.mpr hz),
      dslope_of_ne _ hz, slope_def_field, slope_def_field, sinPhase_zero, sinPhase_neg]
    simp only [sub_zero, neg_div_neg_eq]

/-- **The centered multiplier is real**, `a_n(conj z) = conj (a_n z)`. -/
theorem centeredMultiplierE_conj (n : ℕ) (z : ℂ) :
    centeredMultiplierE n ((starRingEnd ℂ) z) = (starRingEnd ℂ) (centeredMultiplierE n z) := by
  have hsin : ∀ w : ℂ, sinPhase n ((starRingEnd ℂ) w) = (starRingEnd ℂ) (sinPhase n w) := by
    intro w
    rw [sinPhase, sinPhase, ← Complex.sin_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal]
  rcases eq_or_ne z 0 with rfl | hz
  · rw [map_zero, centeredMultiplierE_at_zero]
    simp only [map_mul, Complex.conj_ofReal, map_ofNat]
  · have hzc : (starRingEnd ℂ) z ≠ 0 := by
      simpa using (map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr hz
    rw [centeredMultiplierE, centeredMultiplierE, dslope_of_ne _ hzc, dslope_of_ne _ hz,
      slope_def_field, slope_def_field, sinPhase_zero, hsin]
    simp only [sub_zero, map_mul, map_div₀, Complex.conj_ofReal, map_ofNat]

end HedenmalmThetaSource

end

end RHTower
