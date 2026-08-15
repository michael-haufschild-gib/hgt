import GaloisForLFunctions.HTGeometry.FactorialProfileShiftRatio
import GaloisForLFunctions.HTGeometry.NewtonIrrationalLevelVertex

/-!
# One term of a coefficient recursion, measured against the leading shift

At index `n` the shift `μ` contributes `‖Φ_μ(n−μ)‖ · Θ(n−μ)`.  Both factors compare with the same
quantities at a reference shift `ν`: the polynomial factor by its own degree, the profile factor by
the block ratio.  The two comparisons combine into a single exponent,

```text
deg Φ_μ ∓ s(μ − ν)  =  (deg Φ_μ − s μ) + s ν  =  λ_s(μ) + s ν ,
```

the **same** expression whether `μ` lies above or below `ν`.  Dividing by the corresponding quantity
at `ν` therefore leaves exactly the difference of weighted levels — which is what a Newton polygon
controls.

The power form used here is sharp only while `n − μ` stays comparable to `n`; the hypothesis
`2μ ≤ n` is what guarantees that, and the complementary range is handled by the factorial form.
-/

namespace GaloisForLFunctions.HTGeometry

/-- `((n − μ : ℕ) : ℝ) = (n : ℝ) − (μ : ℝ)` for `μ ≤ n`, in the form the estimates use. -/
theorem cast_sub_add_one {n μ : ℕ} (h : μ ≤ n) :
    (((n - μ : ℕ) : ℝ)) + 1 = ((n : ℝ) - (μ : ℝ)) + 1 := by
  rw [Nat.cast_sub h]

theorem cast_sub_add_one_le {n μ : ℕ} : (((n - μ : ℕ) : ℝ)) + 1 ≤ (n : ℝ) + 1 := by
  have h : ((n - μ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (Nat.sub_le n μ)
  linarith

/-- Half of the index survives the shift when the shift is at most half the index. -/
theorem half_le_cast_sub_add_one {n μ : ℕ} (h : 2 * μ ≤ n) :
    ((n : ℝ) + 1) / 2 ≤ (((n - μ : ℕ) : ℝ)) + 1 := by
  have hμn : μ ≤ n := by omega
  have hcast : (2 : ℝ) * (μ : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  rw [cast_sub_add_one hμn]
  linarith

/-! ### The shift polynomial, read on the whole index -/

theorem norm_eval_le_index {Φ : ℕ → Polynomial ℂ} {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ)
    (hbd : ∀ μ k : ℕ, ‖(Φ μ).eval ((k : ℕ) : ℂ)‖ ≤ C * ρ ^ μ * (((k : ℝ)) + 1) ^ (Φ μ).natDegree)
    (n μ : ℕ) :
    ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖
      ≤ C * ρ ^ μ * ((n : ℝ) + 1) ^ (((Φ μ).natDegree : ℕ) : ℝ) := by
  refine le_trans (hbd μ (n - μ)) ?_
  have hmono : ((((n - μ : ℕ) : ℝ)) + 1) ^ (Φ μ).natDegree
      ≤ ((n : ℝ) + 1) ^ (Φ μ).natDegree :=
    pow_le_pow_left₀ (by positivity) cast_sub_add_one_le _
  have hrpow : ((n : ℝ) + 1) ^ (((Φ μ).natDegree : ℕ) : ℝ) = ((n : ℝ) + 1) ^ (Φ μ).natDegree :=
    Real.rpow_natCast _ _
  rw [hrpow]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-! ### The term at a shift below the reference one -/

theorem shiftTerm_le_of_lt {Φ : ℕ → Polynomial ℂ} {C ρ s c₁ c₂ : ℝ} {Θ : ℕ → ℝ}
    (hC : 0 < C) (hρ : 0 < ρ) (hs : 0 < s)
    (hbd : ∀ μ k : ℕ, ‖(Φ μ).eval ((k : ℕ) : ℂ)‖ ≤ C * ρ ^ μ * (((k : ℝ)) + 1) ^ (Φ μ).natDegree)
    (hprof : IsRegularFactorialProfile s c₁ c₂ Θ) {n μ ν : ℕ} (hμν : μ ≤ ν) (hνn : ν ≤ n) :
    ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
      ≤ (C * ρ ^ μ * c₂ ^ (ν - μ)) *
          (((n : ℝ) + 1) ^ (weightedLevel s Φ μ + s * (ν : ℝ)) * Θ (n - ν)) := by
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hpolyn := norm_eval_le_index hC hρ hbd n μ
  -- the profile grows by at most the weight the level already accounts for
  have hprofile := hprof.shift_below_pow hs.le hμν hνn
  have hprofile' : Θ (n - μ) ≤ Θ (n - ν) * c₂ ^ (ν - μ) *
      ((n : ℝ) + 1) ^ (s * ((ν - μ : ℕ) : ℝ)) := by
    refine le_trans hprofile ?_
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (hprof.pos (n - ν)).le (pow_nonneg hprof.c₂_pos.le _))
    refine Real.rpow_le_rpow (by positivity) cast_sub_add_one_le ?_
    have : (0 : ℝ) ≤ ((ν - μ : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity
  -- the two exponents combine
  have hcastsub : ((ν - μ : ℕ) : ℝ) = (ν : ℝ) - (μ : ℝ) := by
    rw [Nat.cast_sub hμν]
  have hexp : (((Φ μ).natDegree : ℕ) : ℝ) + s * ((ν - μ : ℕ) : ℝ)
      = weightedLevel s Φ μ + s * (ν : ℝ) := by
    rw [hcastsub, weightedLevel]
    ring
  have hsplit : ((n : ℝ) + 1) ^ (weightedLevel s Φ μ + s * (ν : ℝ))
      = ((n : ℝ) + 1) ^ (((Φ μ).natDegree : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ (s * ((ν - μ : ℕ) : ℝ)) := by
    rw [← Real.rpow_add (by linarith), hexp]
  calc ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
      ≤ (C * ρ ^ μ * ((n : ℝ) + 1) ^ (((Φ μ).natDegree : ℕ) : ℝ)) *
          (Θ (n - ν) * c₂ ^ (ν - μ) * ((n : ℝ) + 1) ^ (s * ((ν - μ : ℕ) : ℝ))) :=
        mul_le_mul hpolyn hprofile' (hprof.pos (n - μ)).le (by positivity)
    _ = (C * ρ ^ μ * c₂ ^ (ν - μ)) *
          ((((n : ℝ) + 1) ^ (((Φ μ).natDegree : ℕ) : ℝ) *
            ((n : ℝ) + 1) ^ (s * ((ν - μ : ℕ) : ℝ))) * Θ (n - ν)) := by ring
    _ = (C * ρ ^ μ * c₂ ^ (ν - μ)) *
          (((n : ℝ) + 1) ^ (weightedLevel s Φ μ + s * (ν : ℝ)) * Θ (n - ν)) := by
        rw [hsplit]

/-! ### The term at a shift above the reference one, in the power regime -/

theorem shiftTerm_le_of_gt {Φ : ℕ → Polynomial ℂ} {C ρ s c₁ c₂ : ℝ} {Θ : ℕ → ℝ}
    (hC : 0 < C) (hρ : 0 < ρ) (hs : 0 < s)
    (hbd : ∀ μ k : ℕ, ‖(Φ μ).eval ((k : ℕ) : ℂ)‖ ≤ C * ρ ^ μ * (((k : ℝ)) + 1) ^ (Φ μ).natDegree)
    (hprof : IsRegularFactorialProfile s c₁ c₂ Θ) {n μ ν : ℕ} (hνμ : ν ≤ μ) (hhalf : 2 * μ ≤ n) :
    ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
      ≤ (C * ρ ^ μ * (1 / c₁) ^ (μ - ν) * (2 : ℝ) ^ (s * ((μ - ν : ℕ) : ℝ))) *
          (((n : ℝ) + 1) ^ (weightedLevel s Φ μ + s * (ν : ℝ)) * Θ (n - ν)) := by
  have hμn : μ ≤ n := by omega
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hjnn : (0 : ℝ) ≤ ((μ - ν : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpolyn := norm_eval_le_index hC hρ hbd n μ
  have hstep := hprof.shift_above_pow hs.le hνμ hμn
  -- invert the profile step and replace the shifted index by half the index
  have hposΘ : 0 < Θ (n - μ) := hprof.pos (n - μ)
  have hposc : (0 : ℝ) < c₁ ^ (μ - ν) := pow_pos hprof.c₁_pos _
  have hposr : (0 : ℝ) < ((((n - μ : ℕ) : ℝ)) + 1) ^ (s * ((μ - ν : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hhalfle : ((n : ℝ) + 1) / 2 ≤ (((n - μ : ℕ) : ℝ)) + 1 := half_le_cast_sub_add_one hhalf
  have hhalfpos : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by linarith
  have hrpowmono : (((n : ℝ) + 1) / 2) ^ (s * ((μ - ν : ℕ) : ℝ))
      ≤ ((((n - μ : ℕ) : ℝ)) + 1) ^ (s * ((μ - ν : ℕ) : ℝ)) :=
    Real.rpow_le_rpow hhalfpos.le hhalfle (by positivity)
  have hdivpos : (0 : ℝ) < (((n : ℝ) + 1) / 2) ^ (s * ((μ - ν : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos hhalfpos _
  have hprofile' : Θ (n - μ) ≤ Θ (n - ν) * ((1 / c₁) ^ (μ - ν) *
      ((2 : ℝ) ^ (s * ((μ - ν : ℕ) : ℝ)) * ((n : ℝ) + 1) ^ (-(s * ((μ - ν : ℕ) : ℝ))))) := by
    have hkey : Θ (n - μ) * (c₁ ^ (μ - ν) * (((n : ℝ) + 1) / 2) ^ (s * ((μ - ν : ℕ) : ℝ)))
        ≤ Θ (n - ν) := by
      refine le_trans ?_ hstep
      refine mul_le_mul_of_nonneg_left ?_ hposΘ.le
      exact mul_le_mul_of_nonneg_left hrpowmono hposc.le
    have hfac : (0 : ℝ) < c₁ ^ (μ - ν) * (((n : ℝ) + 1) / 2) ^ (s * ((μ - ν : ℕ) : ℝ)) :=
      mul_pos hposc hdivpos
    rw [← le_div_iff₀ hfac] at hkey
    have hc₁ne : c₁ ≠ 0 := ne_of_gt hprof.c₁_pos
    have hrne : ((n : ℝ) + 1) ^ (s * ((μ - ν : ℕ) : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
    have h2ne : (2 : ℝ) ^ (s * ((μ - ν : ℕ) : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    have hHinv : (1 / c₁) ^ (μ - ν) * ((2 : ℝ) ^ (s * ((μ - ν : ℕ) : ℝ)) *
        ((n : ℝ) + 1) ^ (-(s * ((μ - ν : ℕ) : ℝ))))
        = (c₁ ^ (μ - ν) * (((n : ℝ) + 1) / 2) ^ (s * ((μ - ν : ℕ) : ℝ)))⁻¹ := by
      rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by linarith), one_div,
        inv_pow]
      field_simp
    rw [hHinv, ← div_eq_mul_inv]
    exact hkey
  have hcastsub : ((μ - ν : ℕ) : ℝ) = (μ : ℝ) - (ν : ℝ) := by
    rw [Nat.cast_sub hνμ]
  have hexp : (((Φ μ).natDegree : ℕ) : ℝ) + -(s * ((μ - ν : ℕ) : ℝ))
      = weightedLevel s Φ μ + s * (ν : ℝ) := by
    rw [hcastsub, weightedLevel]
    ring
  have hsplit : ((n : ℝ) + 1) ^ (weightedLevel s Φ μ + s * (ν : ℝ))
      = ((n : ℝ) + 1) ^ (((Φ μ).natDegree : ℕ) : ℝ) *
        ((n : ℝ) + 1) ^ (-(s * ((μ - ν : ℕ) : ℝ))) := by
    rw [← Real.rpow_add (by linarith), hexp]
  calc ‖(Φ μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)
      ≤ (C * ρ ^ μ * ((n : ℝ) + 1) ^ (((Φ μ).natDegree : ℕ) : ℝ)) *
          (Θ (n - ν) * ((1 / c₁) ^ (μ - ν) *
            ((2 : ℝ) ^ (s * ((μ - ν : ℕ) : ℝ)) *
              ((n : ℝ) + 1) ^ (-(s * ((μ - ν : ℕ) : ℝ)))))) :=
        mul_le_mul hpolyn hprofile' hposΘ.le (by positivity)
    _ = (C * ρ ^ μ * (1 / c₁) ^ (μ - ν) * (2 : ℝ) ^ (s * ((μ - ν : ℕ) : ℝ))) *
          ((((n : ℝ) + 1) ^ (((Φ μ).natDegree : ℕ) : ℝ) *
            ((n : ℝ) + 1) ^ (-(s * ((μ - ν : ℕ) : ℝ)))) * Θ (n - ν)) := by ring
    _ = (C * ρ ^ μ * (1 / c₁) ^ (μ - ν) * (2 : ℝ) ^ (s * ((μ - ν : ℕ) : ℝ))) *
          (((n : ℝ) + 1) ^ (weightedLevel s Φ μ + s * (ν : ℝ)) * Θ (n - ν)) := by
        rw [hsplit]

end GaloisForLFunctions.HTGeometry
