import GaloisForLFunctions.RHTower.LogPhaseCubic

/-!
# The Morse coordinate of the universal phase profile

The substitution that turns the archimedean phase into an exact quadratic is

```text
w(v) = sgn(v) · √(-2 ψ(v)),      ψ(v) = v - (1+v) log(1+v),
```

so that `ψ(v) = -w(v)²/2` identically.  Because `ψ` is universal, so is `w`: one and the same
coordinate change linearises every archimedean stationary point.

The file proves that `w` is well defined and sign-preserving, and — the point of the cubic bound of
`LogPhaseCubic` — that `w` is a near-identity:

```text
|w(v) - v| ≤ 2v²/3        for |v| ≤ 1/2.
```

In particular `w(v)/v → 1` at the stationary point, which is what makes the Jacobian of the
substitution a bounded perturbation of `1`.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- Strict negativity of the profile away from the stationary point. -/
theorem neg_logPhaseProfile_pos {v : ℝ} (hv : -1 < v) (hv0 : v ≠ 0) :
    0 < -logPhaseProfile v := by
  rcases lt_or_gt_of_ne hv0 with h | h
  · have hstrict := strictAntiOn_neg_logPhaseProfile (a := v) hv
    have h1 : (v : ℝ) ∈ Icc v (0 : ℝ) := ⟨le_rfl, h.le⟩
    have h2 : (0 : ℝ) ∈ Icc v (0 : ℝ) := ⟨h.le, le_rfl⟩
    have := hstrict h1 h2 h
    simpa using this
  · have hstrict := strictMonoOn_neg_logPhaseProfile
    have h1 : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.mpr le_rfl
    have h2 : (v : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.mpr h.le
    have := hstrict h1 h2 h
    simpa using this

/-- The Morse coordinate: the sign-preserving square root of `-2ψ`. -/
def logPhaseMorse (v : ℝ) : ℝ :=
  if 0 ≤ v then Real.sqrt (-2 * logPhaseProfile v) else -Real.sqrt (-2 * logPhaseProfile v)

@[simp] theorem logPhaseMorse_zero : logPhaseMorse 0 = 0 := by
  simp [logPhaseMorse]

/-- **The defining identity.**  `w(v)² = -2ψ(v)`, so `ψ(v) = -w(v)²/2`. -/
theorem logPhaseMorse_sq {v : ℝ} (hv : -1 < v) :
    logPhaseMorse v ^ (2 : ℕ) = -2 * logPhaseProfile v := by
  have hnn : (0 : ℝ) ≤ -2 * logPhaseProfile v := by
    have := logPhaseProfile_nonpos hv
    linarith
  unfold logPhaseMorse
  split_ifs with h
  · exact Real.sq_sqrt hnn
  · rw [neg_pow, Real.sq_sqrt hnn]
    simp

/-- The Morse coordinate is positive to the right of the stationary point. -/
theorem logPhaseMorse_pos {v : ℝ} (hv : 0 < v) : 0 < logPhaseMorse v := by
  have hv1 : -1 < v := by linarith
  have hpos : 0 < -logPhaseProfile v := neg_logPhaseProfile_pos hv1 (ne_of_gt hv)
  unfold logPhaseMorse
  rw [if_pos hv.le]
  exact Real.sqrt_pos.mpr (by linarith)

/-- The Morse coordinate is negative to the left of the stationary point. -/
theorem logPhaseMorse_neg {v : ℝ} (hv : -1 < v) (hv0 : v < 0) : logPhaseMorse v < 0 := by
  have hpos : 0 < -logPhaseProfile v := neg_logPhaseProfile_pos hv (ne_of_lt hv0)
  unfold logPhaseMorse
  rw [if_neg (by linarith)]
  have : 0 < Real.sqrt (-2 * logPhaseProfile v) := Real.sqrt_pos.mpr (by linarith)
  linarith

/-- The Morse coordinate never has smaller modulus than the displacement it doubles. -/
theorem abs_le_abs_logPhaseMorse_add {v : ℝ} (hv : -1 < v) :
    |v| ≤ |logPhaseMorse v + v| := by
  rcases lt_trichotomy v 0 with h | h | h
  · have hw := logPhaseMorse_neg hv h
    rw [abs_of_neg h, abs_of_neg (by linarith)]
    linarith
  · simp [h]
  · have hw := logPhaseMorse_pos h
    rw [abs_of_pos h, abs_of_pos (by linarith)]
    linarith

/-- **The Morse coordinate is a near-identity.**  `|w(v) - v| ≤ 2v²/3` for `|v| ≤ 1/2`. -/
theorem abs_logPhaseMorse_sub_le {v : ℝ} (h1 : -(1/2 : ℝ) ≤ v) (h2 : v ≤ 1/2) :
    |logPhaseMorse v - v| ≤ 2 * v ^ (2 : ℕ) / 3 := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hv : -1 < v := by linarith
  have habsv : 0 < |v| := abs_pos.mpr hv0
  have hsq : logPhaseMorse v ^ (2 : ℕ) = -2 * logPhaseProfile v := logPhaseMorse_sq hv
  have hrho : logPhaseMorse v ^ (2 : ℕ) - v ^ (2 : ℕ) = 2 * logPhaseCubicRemainder v := by
    rw [hsq]
    simp only [logPhaseCubicRemainder]
    ring
  have hprod : (logPhaseMorse v - v) * (logPhaseMorse v + v) = 2 * logPhaseCubicRemainder v := by
    rw [← hrho]
    ring
  have hcubic : |logPhaseCubicRemainder v| ≤ |v| ^ (3 : ℕ) / 3 := abs_logPhaseCubicRemainder_le h1 h2
  have hstep : |logPhaseMorse v - v| * |v|
      ≤ |logPhaseMorse v - v| * |logPhaseMorse v + v| :=
    mul_le_mul_of_nonneg_left (abs_le_abs_logPhaseMorse_add hv) (abs_nonneg _)
  have heq : |logPhaseMorse v - v| * |logPhaseMorse v + v| = 2 * |logPhaseCubicRemainder v| := by
    rw [← abs_mul, hprod, abs_mul]
    norm_num
  have hfinal : |logPhaseMorse v - v| * |v| ≤ 2 * (|v| ^ (3 : ℕ) / 3) := by
    rw [heq] at hstep
    linarith
  have hcube : |v| ^ (3 : ℕ) = |v| ^ (2 : ℕ) * |v| := by ring
  have hsqabs : |v| ^ (2 : ℕ) = v ^ (2 : ℕ) := sq_abs v
  rw [hcube, hsqabs] at hfinal
  have hgoal : |logPhaseMorse v - v| * |v| ≤ 2 * v ^ (2 : ℕ) / 3 * |v| := by
    calc |logPhaseMorse v - v| * |v| ≤ 2 * (v ^ (2 : ℕ) * |v| / 3) := hfinal
      _ = 2 * v ^ (2 : ℕ) / 3 * |v| := by ring
  exact le_of_mul_le_mul_right hgoal habsv

/-- **The Morse coordinate is a strictly increasing reparametrisation.**  Hence the substitution
`v ↦ w(v)` is injective on the whole admissible range. -/
theorem strictMonoOn_logPhaseMorse : StrictMonoOn logPhaseMorse (Ioi (-1 : ℝ)) := by
  intro a ha b hb hab
  have ha1 : -1 < a := ha
  have hb1 : -1 < b := hb
  rcases le_or_gt 0 a with h0a | h0a
  · have h0b : (0 : ℝ) ≤ b := le_of_lt (lt_of_le_of_lt h0a hab)
    have hlt : -logPhaseProfile a < -logPhaseProfile b :=
      strictMonoOn_neg_logPhaseProfile (mem_Ici.mpr h0a) (mem_Ici.mpr h0b) hab
    have hnn : (0 : ℝ) ≤ -2 * logPhaseProfile a := by
      have := logPhaseProfile_nonpos ha1
      linarith
    unfold logPhaseMorse
    rw [if_pos h0a, if_pos h0b]
    exact Real.sqrt_lt_sqrt hnn (by linarith)
  · rcases lt_or_ge b 0 with h0b | h0b
    · have hlt : -logPhaseProfile b < -logPhaseProfile a :=
        strictAntiOn_neg_logPhaseProfile ha1 ⟨le_rfl, h0a.le⟩ ⟨hab.le, h0b.le⟩ hab
      have hnn : (0 : ℝ) ≤ -2 * logPhaseProfile b := by
        have := logPhaseProfile_nonpos hb1
        linarith
      unfold logPhaseMorse
      rw [if_neg (by linarith), if_neg (by linarith)]
      have := Real.sqrt_lt_sqrt hnn (by linarith : -2 * logPhaseProfile b < -2 * logPhaseProfile a)
      linarith
    · have h1 := logPhaseMorse_neg ha1 h0a
      have h2 : 0 ≤ logPhaseMorse b := by
        unfold logPhaseMorse
        rw [if_pos h0b]
        exact Real.sqrt_nonneg _
      linarith

end GaloisForLFunctions.RHTower
