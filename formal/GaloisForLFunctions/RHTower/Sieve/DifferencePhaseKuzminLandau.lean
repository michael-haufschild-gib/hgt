import GaloisForLFunctions.RHTower.Sieve.DifferencePhaseCurvature
import GaloisForLFunctions.RHTower.Sieve.KuzminLandauInterval

/-!
# The difference phase below the first-derivative resonance

The same cancellation that makes the second derivative of `F_{s₁} − F_{s₂}` clean also makes the
first derivative clean:

`F'_{s₁}(u) − F'_{s₂}(u) = −(T/2π)·(s₁ − s₂)/((u+s₁)(u+s₂))`,

because `s₁(u+s₂) − s₂(u+s₁) = u(s₁ − s₂)`.  It is negative, monotone increasing, and of size
`T(s₁−s₂)/u²`; when that is below `1/2` the Kuzmin--Landau inequality applies and beats the
second-derivative test by a whole power.
-/

namespace RHTower.Sieve

open Real RHTower

noncomputable section

/-- **The exact first-derivative identity.** -/
theorem diffPhaseD1_eq (T : ℝ) {s₁ s₂ u : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hu : 0 < u) :
    diffPhaseD1 T s₁ s₂ u
      = -(T / (2 * Real.pi)) * ((s₁ - s₂) / ((u + s₁) * (u + s₂))) := by
  have hu1 : (0 : ℝ) < u + s₁ := by linarith
  have hu2 : (0 : ℝ) < u + s₂ := by linarith
  rw [diffPhaseD1, nearDiagonalPhaseD1, nearDiagonalPhaseD1]
  field_simp
  ring

theorem diffPhaseD1_monotoneOn {T s₁ s₂ : ℝ} (hT : 0 < T) (hs₂ : 0 ≤ s₂) (hs : s₂ ≤ s₁)
    {a b : ℝ} (ha : 0 < a) :
    MonotoneOn (diffPhaseD1 T s₁ s₂) (Set.Icc a b) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs₁ : (0 : ℝ) ≤ s₁ := le_trans hs₂ hs
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le ha hy.1
  rw [diffPhaseD1_eq T hs₁ hs₂ hx0, diffPhaseD1_eq T hs₁ hs₂ hy0]
  have hden : (x + s₁) * (x + s₂) ≤ (y + s₁) * (y + s₂) := by nlinarith
  have hdx : (0 : ℝ) < (x + s₁) * (x + s₂) := by positivity
  have hdy : (0 : ℝ) < (y + s₁) * (y + s₂) := by positivity
  have hΔ : (0 : ℝ) ≤ s₁ - s₂ := by linarith
  have hle : (s₁ - s₂) / ((y + s₁) * (y + s₂)) ≤ (s₁ - s₂) / ((x + s₁) * (x + s₂)) := by
    exact div_le_div_of_nonneg_left hΔ hdx hden
  have hcoef : (0 : ℝ) < T / (2 * Real.pi) := by positivity
  nlinarith [hle, hcoef]

/-- Upper bound for the size of the first derivative. -/
theorem abs_diffPhaseD1_le {T s₁ s₂ u : ℝ} (hT : 0 < T) (hs₂ : 0 ≤ s₂) (hs : s₂ ≤ s₁)
    (hu : 0 < u) :
    -(T * (s₁ - s₂) / (2 * Real.pi * u ^ 2)) ≤ diffPhaseD1 T s₁ s₂ u := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs₁ : (0 : ℝ) ≤ s₁ := le_trans hs₂ hs
  have hΔ : (0 : ℝ) ≤ s₁ - s₂ := by linarith
  have hu1 : (0 : ℝ) < u + s₁ := by linarith
  have hu2 : (0 : ℝ) < u + s₂ := by linarith
  have hLHS : diffPhaseD1 T s₁ s₂ u
      = -(T * (s₁ - s₂) / (2 * Real.pi * ((u + s₁) * (u + s₂)))) := by
    rw [diffPhaseD1_eq T hs₁ hs₂ hu]
    field_simp
  have hbase : u ^ 2 ≤ (u + s₁) * (u + s₂) := by
    nlinarith [mul_nonneg hu.le hs₁, mul_nonneg hu.le hs₂, mul_nonneg hs₁ hs₂]
  rw [hLHS, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (mul_nonneg hT.le hΔ) (by positivity)
    (mul_le_mul_of_nonneg_left hbase (by positivity))

/-- Lower bound for the size of the first derivative on a range whose right endpoint is `b`. -/
theorem diffPhaseD1_le_neg {T s₁ s₂ u b : ℝ} (hT : 0 < T) (hs₂ : 0 ≤ s₂) (hs : s₂ ≤ s₁)
    (hu : 0 < u) (hub : u ≤ b) (h4 : 4 * s₁ ≤ b) :
    diffPhaseD1 T s₁ s₂ u ≤ -(8 * (T * (s₁ - s₂)) / (25 * Real.pi * b ^ 2)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs₁ : (0 : ℝ) ≤ s₁ := le_trans hs₂ hs
  have hΔ : (0 : ℝ) ≤ s₁ - s₂ := by linarith
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le hu hub
  have hu1 : (0 : ℝ) < u + s₁ := by linarith
  have hu2 : (0 : ℝ) < u + s₂ := by linarith
  have hLHS : diffPhaseD1 T s₁ s₂ u
      = -(T * (s₁ - s₂) / (2 * Real.pi * ((u + s₁) * (u + s₂)))) := by
    rw [diffPhaseD1_eq T hs₁ hs₂ hu]
    field_simp
  rw [hLHS, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : 16 * ((u + s₁) * (u + s₂)) ≤ 25 * b ^ 2 := by
    have h1 : u + s₁ ≤ 5 / 4 * b := by linarith
    have h2 : u + s₂ ≤ 5 / 4 * b := by linarith
    nlinarith
  have hcoef : (0 : ℝ) ≤ T * (s₁ - s₂) * Real.pi := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hkey hcoef]

/-- **Kuzmin--Landau for the difference phase.**  Below the first-derivative resonance the whole
range costs only `B²/(T(s₁−s₂))`. -/
theorem norm_curvedSum_diffPhase_kuzminLandau {T s₁ s₂ : ℝ} (hT : 0 < T) (hs₂ : 0 ≤ s₂)
    (hs : s₂ < s₁) {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B) (h4 : 4 * s₁ ≤ (A : ℝ))
    (hsmall : T * (s₁ - s₂) / (2 * Real.pi * (A : ℝ) ^ 2) ≤ 1 / 2) :
    ‖curvedSum (diffPhase T s₁ s₂) A B‖
      ≤ 75 * Real.pi * (B : ℝ) ^ 2 / (16 * (T * (s₁ - s₂))) + 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs₁ : (0 : ℝ) < s₁ := lt_of_le_of_lt hs₂ hs
  have hΔ : (0 : ℝ) < s₁ - s₂ := by linarith
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hB0 : (0 : ℝ) < (B : ℝ) := by
    have : 0 < B := by omega
    exact_mod_cast this
  have hABr : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB.le
  set Y : ℝ := T * (s₁ - s₂) with hYdef
  have hY0 : 0 < Y := by rw [hYdef]; positivity
  set δ : ℝ := 8 * Y / (25 * Real.pi * (B : ℝ) ^ 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  -- the span
  have hspan : ((B - A - 1 : ℕ) : ℝ) + (A : ℝ) ≤ (B : ℝ) := by
    have : ((B - A - 1 : ℕ) : ℝ) ≤ (B : ℝ) - (A : ℝ) := by
      have hnat : B - A - 1 + A ≤ B := by omega
      have : ((B - A - 1 + A : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hnat
      push_cast at this
      linarith
    linarith
  have hmem : ∀ x ∈ Set.Icc (A : ℝ) ((A : ℝ) + ((B - A - 1 : ℕ) : ℝ)),
      (A : ℝ) ≤ x ∧ x ≤ (B : ℝ) := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (by linarith)⟩
  have hδhalf : δ ≤ 1 / 2 := by
    have hbound : Y ≤ Real.pi * (A : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hsmall
      nlinarith [hsmall]
    have hAB2 : (A : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 := by nlinarith
    rw [hδdef, div_le_iff₀ (by positivity)]
    nlinarith [hbound, hAB2]
  have hkl := kuzminLandau_interval (diffPhase T s₁ s₂) (diffPhaseD1 T s₁ s₂) (A : ℝ)
    (B - A - 1) (-1) hδ0
    (fun x hx => hasDerivAt_diffPhase T hs₁.le hs₂
      (lt_of_lt_of_le hA0 (hmem x hx).1))
    (diffPhaseD1_monotoneOn hT hs₂ hs.le hA0)
    (fun x hx => by
      have hxA := (hmem x hx).1
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hA0 hxA
      have hup := abs_diffPhaseD1_le hT hs₂ hs.le hx0
      have hxA2 : (A : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
      have hmono : Y / (2 * Real.pi * x ^ 2) ≤ Y / (2 * Real.pi * (A : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_left hY0.le (by positivity)
        nlinarith
      have hhalf : Y / (2 * Real.pi * x ^ 2) ≤ 1 / 2 := le_trans hmono hsmall
      have : (-1 : ℝ) + δ ≤ -(Y / (2 * Real.pi * x ^ 2)) := by
        linarith [hδhalf, hhalf]
      exact le_trans (by push_cast; linarith) hup)
    (fun x hx => by
      have hxA := (hmem x hx).1
      have hxB := (hmem x hx).2
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hA0 hxA
      have h4B : 4 * s₁ ≤ (B : ℝ) := le_trans h4 hABr
      have hlow := diffPhaseD1_le_neg hT hs₂ hs.le hx0 hxB h4B
      have hval : -(8 * Y / (25 * Real.pi * (B : ℝ) ^ 2)) = -δ := by rw [hδdef]
      rw [hval] at hlow
      have : diffPhaseD1 T s₁ s₂ x ≤ ((-1 : ℤ) : ℝ) + 1 - δ := by push_cast; linarith
      exact this)
  have hsum : curvedSum (diffPhase T s₁ s₂) A B
      = ∑ j ∈ Finset.range ((B - A - 1) + 1),
          Complex.exp (((2 * Real.pi * diffPhase T s₁ s₂ ((A : ℝ) + j) : ℝ) : ℂ) * Complex.I) := by
    rw [curvedSum, Finset.sum_Ico_eq_sum_range]
    have hlen : B - A = (B - A - 1) + 1 := by omega
    rw [hlen]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 3
    push_cast
    ring
  rw [hsum]
  refine hkl.trans (le_of_eq ?_)
  rw [hδdef]
  field_simp
  ring

end

end RHTower.Sieve
