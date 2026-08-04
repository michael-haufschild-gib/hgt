import GaloisForLFunctions.HTGeometry.WimanValironRadius

/-!
# A polynomial form of the Wiman--Valiron bound

The explicit Wiman--Valiron estimate carries exponential damping factors coming from the Gaussian
tail of the coefficient profile.  Once the window half-width is at least the natural scale — `N` at
least `8L`, which is what the parameter choice already forces — those factors are bounded by
absolute constants, and the whole prefactor collapses to a polynomial in `N`:

* the amplitude `sqrt (2N+1) + 2 E` is at most `3 sqrt N`;
* the Cauchy--Schwarz defect is at most `10 N sqrt N`.

The resulting estimate has the shape `3 sqrt N * (2 L h + 2 log(...)/h) + 10 N^{3/2}`, with no
transcendental constants left, which is the form in which the parameters can be tuned.
-/

open MeasureTheory Complex Set

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-! ## An elementary growth comparison -/

private theorem nat_succ_le_three_pow : ∀ m : ℕ, m + 1 ≤ 3 ^ m
  | 0 => by norm_num
  | (m + 1) => by
      have ih := nat_succ_le_three_pow m
      have h1 : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
      have h3 : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
      omega

private theorem nat_sq_le_three_pow : ∀ m : ℕ, m ^ 2 ≤ 3 ^ m
  | 0 => by norm_num
  | (m + 1) => by
      have ih := nat_sq_le_three_pow m
      have hs := nat_succ_le_three_pow m
      have hexp : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
      have h3 : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
      omega

/-- **A geometric factor beats a square.**  For every `m`, `m² (1/3)^m ≤ 1`. -/
theorem sq_mul_third_pow_le_one (m : ℕ) : ((m : ℝ)) ^ 2 * (1 / 3 : ℝ) ^ m ≤ 1 := by
  have hnat : ((m ^ 2 : ℕ) : ℝ) ≤ ((3 ^ m : ℕ) : ℝ) := Nat.cast_le.mpr (nat_sq_le_three_pow m)
  have hcast : ((m : ℝ)) ^ 2 ≤ (3 : ℝ) ^ m := by
    push_cast at hnat
    exact hnat
  have hpos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hinv : (1 / 3 : ℝ) ^ m = ((3 : ℝ) ^ m)⁻¹ := by
    rw [one_div, inv_pow]
  rw [hinv]
  rw [mul_inv_le_iff₀ hpos]
  simpa using hcast

/-! ## The damping factors are bounded -/

section Damping

variable {N : ℕ} {L : ℝ}

/-- Under `8L ≤ N` the damping factor is at most `1/3`. -/
theorem exp_neg_quarter_le (hL : 0 < L) (hNL : 8 * L ≤ (N : ℝ)) :
    Real.exp (-((N : ℝ) / (4 * L))) ≤ 1 / 3 := by
  have h4L : (0 : ℝ) < 4 * L := by linarith
  have hkey : (2 : ℝ) ≤ (N : ℝ) / (4 * L) := by
    have hEq : (N : ℝ) / (4 * L) - 2 = ((N : ℝ) - 8 * L) / (4 * L) := by
      field_simp
      ring
    have hnn : 0 ≤ ((N : ℝ) - 8 * L) / (4 * L) := div_nonneg (by linarith) (by linarith)
    rw [← hEq] at hnn
    linarith
  have hmono : Real.exp (-((N : ℝ) / (4 * L))) ≤ Real.exp (-2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hexp : Real.exp (-(2 : ℝ)) ≤ 1 / 3 := by
    rw [Real.exp_neg]
    have hpos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
    have hmul : (Real.exp 2)⁻¹ * Real.exp 2 = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    nlinarith [inv_pos.mpr hpos, h3, hmul]
  have hneg : (-(2 : ℝ)) = -2 := rfl
  linarith [hmono, hexp]

private theorem third_pow_le_one (m : ℕ) : (1 / 3 : ℝ) ^ m ≤ 1 := by
  have hle : (1 / 3 : ℝ) ^ m ≤ (1 : ℝ) ^ m := by
    gcongr
    norm_num
  simpa using hle

/-- **The amplitude is at most `3 sqrt N`.** -/
theorem wiman_valiron_amplitude_le (hN : 1 ≤ N) (hL : 0 < L) (hNL : 8 * L ≤ (N : ℝ)) :
    Real.sqrt (2 * (N : ℝ) + 1)
        + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
            / (1 - Real.exp (-((N : ℝ) / (4 * L))))) ≤ 3 * Real.sqrt (N : ℝ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hq0 : 0 < Real.exp (-((N : ℝ) / (4 * L))) := Real.exp_pos _
  have hq2 : Real.exp (-((N : ℝ) / (4 * L))) ≤ 1 / 3 := exp_neg_quarter_le hL hNL
  have h1q : (2 / 3 : ℝ) ≤ 1 - Real.exp (-((N : ℝ) / (4 * L))) := by linarith
  have h1qpos : (0 : ℝ) < 1 - Real.exp (-((N : ℝ) / (4 * L))) := by linarith
  have hqpow : Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1) ≤ (1 / 3 : ℝ) ^ (N + 1) := by
    gcongr
  have hsmall : (1 / 3 : ℝ) ^ (N + 1) ≤ 1 / 3 := by
    have : (1 / 3 : ℝ) ^ (N + 1) = (1 / 3 : ℝ) ^ N * (1 / 3) := by ring
    rw [this]
    have := third_pow_le_one N
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/3) N]
  have hE : 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
      / (1 - Real.exp (-((N : ℝ) / (4 * L))))) ≤ 1 := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ h1qpos]
    nlinarith
  have hsq : Real.sqrt (2 * (N : ℝ) + 1) ≤ 2 * Real.sqrt (N : ℝ) := by
    have h1 : Real.sqrt (2 * (N : ℝ) + 1) ≤ Real.sqrt (4 * (N : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (4 * (N : ℝ)) = 2 * Real.sqrt (N : ℝ) := by
      rw [show (4 : ℝ) * (N : ℝ) = 2 ^ 2 * (N : ℝ) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h1, h2.le, h2.ge]
  have hsqN : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have := Real.sqrt_le_sqrt hN1
    simpa using this
  linarith

end Damping

/-! ## The full prefactor -/

/-- **The Wiman--Valiron prefactor is polynomial.**  With `8L ≤ N` the whole right-hand side of the
explicit estimate is at most `3 sqrt N` times the logarithmic bracket plus `10 N^{3/2}`. -/
theorem wiman_valiron_bound_le_polynomial {N : ℕ} {L B : ℝ} (hN : 1 ≤ N) (hL : 0 < L)
    (hNL : 8 * L ≤ (N : ℝ)) (hB : 0 ≤ B) :
    (Real.sqrt (2 * (N : ℝ) + 1)
        + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
            / (1 - Real.exp (-((N : ℝ) / (4 * L)))))) * B
      + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
          * (Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                / (1 - Real.exp (-((N : ℝ) / (4 * L)))))))
      ≤ 3 * Real.sqrt (N : ℝ) * B + 10 * ((N : ℝ) * Real.sqrt (N : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hsqN0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsqN : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have := Real.sqrt_le_sqrt hN1
    simpa using this
  have hsqsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN0
  have hq0 : 0 < Real.exp (-((N : ℝ) / (4 * L))) := Real.exp_pos _
  have hq2 : Real.exp (-((N : ℝ) / (4 * L))) ≤ 1 / 3 := exp_neg_quarter_le hL hNL
  have h1q : (2 / 3 : ℝ) ≤ 1 - Real.exp (-((N : ℝ) / (4 * L))) := by linarith
  have h1qpos : (0 : ℝ) < 1 - Real.exp (-((N : ℝ) / (4 * L))) := by linarith
  have hamp := wiman_valiron_amplitude_le hN hL hNL
  have hamp0 : 0 ≤ Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L))))) := by positivity
  have hsq : Real.sqrt (2 * (N : ℝ) + 1) ≤ 2 * Real.sqrt (N : ℝ) := by
    have h1 : Real.sqrt (2 * (N : ℝ) + 1) ≤ Real.sqrt (4 * (N : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (4 * (N : ℝ)) = 2 * Real.sqrt (N : ℝ) := by
      rw [show (4 : ℝ) * (N : ℝ) = 2 ^ 2 * (N : ℝ) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h1, h2.le, h2.ge]
  -- the cube of the gap
  have hcube : (8 / 27 : ℝ) ≤ (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3 := by
    have : ((2 : ℝ) / 3) ^ 3 ≤ (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3 := by
      gcongr
    nlinarith [this]
  -- the square-times-geometric factor
  have hgeom : ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1) ≤ 1 := by
    have hqpow : Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1) ≤ (1 / 3 : ℝ) ^ (N + 1) := by
      gcongr
    have hcast : ((N : ℝ) + 1) ^ 2 = (((N + 1 : ℕ) : ℝ)) ^ 2 := by push_cast; ring
    have hbase := sq_mul_third_pow_le_one (N + 1)
    rw [hcast]
    calc (((N + 1 : ℕ) : ℝ)) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
        ≤ (((N + 1 : ℕ) : ℝ)) ^ 2 * (1 / 3 : ℝ) ^ (N + 1) := by
          have hnn : (0 : ℝ) ≤ (((N + 1 : ℕ) : ℝ)) ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_left hqpow hnn
      _ ≤ 1 := hbase
  have hterm2 : 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
      / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3) ≤ 14 := by
    have hcubepos : (0 : ℝ) < (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3 := by positivity
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ hcubepos]
    nlinarith [hgeom, hcube]
  -- the inner factor
  have hinner : 2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
      ≤ 4 * (N : ℝ) ^ 2 * Real.sqrt (N : ℝ) + 28 := by
    nlinarith [hsq, hterm2, sq_nonneg ((N : ℝ))]
  have hinner0 : 0 ≤ 2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3)) := by positivity
  -- the product under the root
  have hprod : 2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
        + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
            / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
      * (Real.sqrt (2 * (N : ℝ) + 1)
        + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
            / (1 - Real.exp (-((N : ℝ) / (4 * L))))))
      ≤ 100 * (N : ℝ) ^ 3 := by
    have hstep : 2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
          + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
              / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
        * (Real.sqrt (2 * (N : ℝ) + 1)
          + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
              / (1 - Real.exp (-((N : ℝ) / (4 * L))))))
        ≤ (4 * (N : ℝ) ^ 2 * Real.sqrt (N : ℝ) + 28) * (3 * Real.sqrt (N : ℝ)) :=
      mul_le_mul hinner hamp hamp0 (by positivity)
    have hexpand : (4 * (N : ℝ) ^ 2 * Real.sqrt (N : ℝ) + 28) * (3 * Real.sqrt (N : ℝ))
        = 12 * (N : ℝ) ^ 3 + 84 * Real.sqrt (N : ℝ) := by
      have : (4 * (N : ℝ) ^ 2 * Real.sqrt (N : ℝ) + 28) * (3 * Real.sqrt (N : ℝ))
          = 12 * (N : ℝ) ^ 2 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ))
            + 84 * Real.sqrt (N : ℝ) := by ring
      rw [this, hsqsq]
      ring
    have hsqle : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
      have h1 : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq hN0] at h1
    have hcube3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith
    linarith [hstep, hexpand.le, hexpand.ge, hsqle, hcube3]
  have hroot : Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
        + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
            / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
      * (Real.sqrt (2 * (N : ℝ) + 1)
        + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
            / (1 - Real.exp (-((N : ℝ) / (4 * L)))))))
      ≤ 10 * ((N : ℝ) * Real.sqrt (N : ℝ)) := by
    have hsqrt : Real.sqrt (100 * (N : ℝ) ^ 3) = 10 * ((N : ℝ) * Real.sqrt (N : ℝ)) := by
      have hval : (10 * ((N : ℝ) * Real.sqrt (N : ℝ))) ^ 2 = 100 * (N : ℝ) ^ 3 := by
        have : (10 * ((N : ℝ) * Real.sqrt (N : ℝ))) ^ 2
            = 100 * (N : ℝ) ^ 2 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
        rw [this, hsqsq]
        ring
      rw [← hval, Real.sqrt_sq (by positivity)]
    calc Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3))
          * (Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                / (1 - Real.exp (-((N : ℝ) / (4 * L)))))))
        ≤ Real.sqrt (100 * (N : ℝ) ^ 3) := Real.sqrt_le_sqrt hprod
      _ = 10 * ((N : ℝ) * Real.sqrt (N : ℝ)) := hsqrt
  have hfirst : (Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L)))))) * B ≤ 3 * Real.sqrt (N : ℝ) * B :=
    mul_le_mul_of_nonneg_right hamp hB
  linarith

/-- **The Wiman--Valiron estimate in polynomial form.**  With the sampling height at least `8` the
parameter choice automatically satisfies `8L ≤ N`, and the estimate reads: at some radius the
logarithmic derivative differs from the central index by at most `3 sqrt N` times the logarithmic
bracket plus `10 N^{3/2}`. -/
theorem exists_radius_point_wiman_valiron_polynomial
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H s L h : ℝ}
    (hcd : c ≤ d) (hH8 : 8 ≤ H) (hs : 0 < s)
    (hLdef : L = 2 * s / H) (hhdef : h = H / 2)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c)
    {N : ℕ} (hN1 : 1 ≤ N) (hN2s : 2 * s ≤ (N : ℝ)) (hN4s : (N : ℝ) ≤ 4 * s) :
    ∃ x ∈ Icc (c + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ 3 * Real.sqrt (N : ℝ) * (2 * L * h
            + 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
                + 1 / (Real.exp h - 1)) / h)
          + 10 * ((N : ℝ) * Real.sqrt (N : ℝ)) := by
  have hH : 0 < H := by linarith
  obtain ⟨x, hx, z, hz, hfz, hbound⟩ :=
    exists_radius_point_wiman_valiron_bound ha hn₀ hcd hH hs hLdef hhdef hsmall hN2s hN4s
  refine ⟨x, hx, z, hz, hfz, le_trans hbound ?_⟩
  have hL : 0 < L := by rw [hLdef]; positivity
  have hh : 0 < h := by rw [hhdef]; linarith
  have hNL : 8 * L ≤ (N : ℝ) := by
    have hstep : 8 * L ≤ 2 * s := by
      rw [hLdef]
      have hrw : 8 * (2 * s / H) = 16 * s / H := by ring
      rw [hrw, div_le_iff₀ hH]
      nlinarith
    linarith
  have hexph : 0 < Real.exp h - 1 := by
    have := Real.add_one_le_exp h
    linarith
  have harg : (1 : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
      + 1 / (Real.exp h - 1) := by
    have h1 : (0 : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) < 2 * L * h := by positivity
    have h4 : (0 : ℝ) < 1 / (Real.exp h - 1) := by positivity
    linarith
  have hlog : (0 : ℝ) ≤ Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
      + 1 / (Real.exp h - 1)) := Real.log_nonneg harg
  have hB : (0 : ℝ) ≤ 2 * L * h
      + 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
          + 1 / (Real.exp h - 1)) / h := by
    have h2 : (0 : ℝ) < 2 * L * h := by positivity
    have h3 : (0 : ℝ) ≤ 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
        + 1 / (Real.exp h - 1)) / h := div_nonneg (by linarith) (le_of_lt hh)
    linarith
  exact wiman_valiron_bound_le_polynomial hN1 hL hNL hB

/-- **The estimate in terms of the sampling scale alone.**  Choosing the window half-width in the
band `[2s, 4s]` forced by the parameter tie, the defect between the logarithmic derivative and the
central index is at most `92 s^{3/2}` plus a logarithmic term of size `24 sqrt s log(nu + 2s + 2)/H`
— every transcendental constant absorbed, and the growth in the scale explicit. -/
theorem exists_radius_point_wiman_valiron_scale
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H s : ℝ}
    (hcd : c ≤ d) (hH8 : 8 ≤ H) (hs : 0 < s)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c)
    {N : ℕ} (hN1 : 1 ≤ N) (hN2s : 2 * s ≤ (N : ℝ)) (hN4s : (N : ℝ) ≤ 4 * s) :
    ∃ x ∈ Icc (c + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ 92 * (s * Real.sqrt s)
          + 24 * Real.sqrt s * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * s + 2) / H := by
  have hH : (0 : ℝ) < H := by linarith
  have hHne : H ≠ 0 := ne_of_gt hH
  obtain ⟨x, hx, z, hz, hfz, hbound⟩ :=
    exists_radius_point_wiman_valiron_polynomial ha hn₀ hcd hH8 hs rfl rfl hsmall hN1 hN2s hN4s
  have hrw : 2 * (2 * s / H) * (H / 2) = 2 * s := by field_simp
  rw [hrw] at hbound
  refine ⟨x, hx, z, hz, hfz, le_trans hbound ?_⟩
  set nu : ℝ := ((centralIndex a (Real.exp x) : ℕ) : ℝ) with hnu
  have hnu0 : 0 ≤ nu := Nat.cast_nonneg _
  have hsqs0 : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hsqN0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  -- the tail of the geometric correction is bounded by one
  have hexp2 : (2 : ℝ) ≤ Real.exp (H / 2) - 1 := by
    have := Real.add_one_le_exp (H / 2)
    linarith
  have hinv1 : 1 / (Real.exp (H / 2) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hinv0 : (0 : ℝ) < 1 / (Real.exp (H / 2) - 1) := by
    apply div_pos one_pos
    linarith
  -- the logarithm is monotone in its argument
  have hargpos : (0 : ℝ) < nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1) := by linarith
  have hargle : nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1) ≤ nu + 2 * s + 2 := by linarith
  have hlogmono : Real.log (nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1))
      ≤ Real.log (nu + 2 * s + 2) := Real.log_le_log hargpos hargle
  have hlog0 : (0 : ℝ) ≤ Real.log (nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1)) :=
    Real.log_nonneg (by linarith)
  -- the bracket
  have hbracket : 2 * s + 2 * Real.log (nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1)) / (H / 2)
      ≤ 2 * s + 4 * Real.log (nu + 2 * s + 2) / H := by
    have heq : 2 * Real.log (nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1)) / (H / 2)
        = 4 * Real.log (nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1)) / H := by
      field_simp
      ring
    rw [heq]
    have : 4 * Real.log (nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1)) / H
        ≤ 4 * Real.log (nu + 2 * s + 2) / H := by gcongr
    linarith
  have hbr0 : (0 : ℝ) ≤ 2 * s
      + 2 * Real.log (nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1)) / (H / 2) := by
    have h1 : (0 : ℝ) ≤ 2 * Real.log (nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1)) / (H / 2) :=
      div_nonneg (by linarith) (by linarith)
    linarith
  -- the window half-width against the scale
  have hsqN2 : Real.sqrt (N : ℝ) ≤ 2 * Real.sqrt s := by
    have h1 : Real.sqrt (N : ℝ) ≤ Real.sqrt (4 * s) := Real.sqrt_le_sqrt hN4s
    have h2 : Real.sqrt (4 * s) = 2 * Real.sqrt s := by
      rw [show (4 : ℝ) * s = 2 ^ 2 * s by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h1, h2.le, h2.ge]
  have hstep1 : 3 * Real.sqrt (N : ℝ)
        * (2 * s + 2 * Real.log (nu + 2 * s + 1 + 1 / (Real.exp (H / 2) - 1)) / (H / 2))
      ≤ 6 * Real.sqrt s * (2 * s + 4 * Real.log (nu + 2 * s + 2) / H) :=
    mul_le_mul (by linarith) hbracket hbr0 (by positivity)
  have hstep2 : 6 * Real.sqrt s * (2 * s + 4 * Real.log (nu + 2 * s + 2) / H)
      = 12 * (s * Real.sqrt s) + 24 * Real.sqrt s * Real.log (nu + 2 * s + 2) / H := by
    field_simp
    ring
  have hstep3 : 10 * ((N : ℝ) * Real.sqrt (N : ℝ)) ≤ 80 * (s * Real.sqrt s) := by
    have hmul : (N : ℝ) * Real.sqrt (N : ℝ) ≤ (4 * s) * (2 * Real.sqrt s) :=
      mul_le_mul hN4s hsqN2 hsqN0 (by linarith)
    have heq : (4 * s) * (2 * Real.sqrt s) = 8 * (s * Real.sqrt s) := by ring
    linarith [hmul, heq.le, heq.ge]
  linarith [hstep1, hstep2.le, hstep2.ge, hstep3]

/-! ## The geometric tail with no smallness hypothesis

The bounds above trade the exponential factors for absolute constants, at the price of forcing the
sampling window to be long (`H ≥ 8`).  For a function of positive order the central index rises by a
constant factor across a window of unit logarithmic length, so a long window can only be bought with
a spread comparable to the central index itself, and the resulting estimate is never small.  The
usable regime therefore has a short window, where the damping factor is close to `1` and the bounds
above do not apply.  The following lemmas cover that regime: they bound the geometric tail for every
positive decay rate, with the rate left free for the parameter choice. -/

/-- **The geometric gap.**  For every `κ > 0` one has `κ/(1+κ) ≤ 1 − e^{−κ}`; this is `1 + κ ≤ e^κ`
rearranged, and unlike a numerical bound it degrades gracefully as `κ → 0`. -/
theorem one_sub_exp_neg_ge {κ : ℝ} (hκ : 0 < κ) : κ / (1 + κ) ≤ 1 - Real.exp (-κ) := by
  have hexp : 1 + κ ≤ Real.exp κ := by
    have := Real.add_one_le_exp κ
    linarith
  have hpos : (0 : ℝ) < 1 + κ := by linarith
  have hkey : (1 + κ) * Real.exp (-κ) ≤ 1 := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos κ)]
    simpa using hexp
  have hexpand : (1 - Real.exp (-κ)) * (1 + κ) = (1 + κ) - (1 + κ) * Real.exp (-κ) := by ring
  rw [div_le_iff₀ hpos, hexpand]
  linarith

/-- The decay factor is below one whenever the rate is positive. -/
theorem exp_neg_lt_one {κ : ℝ} (hκ : 0 < κ) : Real.exp (-κ) < 1 := by
  have hexp : 1 + κ ≤ Real.exp κ := by
    have := Real.add_one_le_exp κ
    linarith
  have hkey : (1 + κ) * Real.exp (-κ) ≤ 1 := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos κ)]
    simpa using hexp
  nlinarith [hkey, Real.exp_pos (-κ)]

/-- **The geometric tail at an arbitrary rate.**  `e^{−κm}/(1 − e^{−κ}) ≤ ((1+κ)/κ) e^{−κm}`: the
tail of the Gaussian window is controlled for every positive rate, with the `1/κ` blow-up made
explicit rather than hidden in a hypothesis. -/
theorem exp_pow_div_one_sub_le {κ : ℝ} (hκ : 0 < κ) (m : ℕ) :
    Real.exp (-κ) ^ m / (1 - Real.exp (-κ))
      ≤ (1 + κ) / κ * Real.exp (-((m : ℝ) * κ)) := by
  have hgap : (0 : ℝ) < 1 - Real.exp (-κ) := by
    have := exp_neg_lt_one hκ
    linarith
  have hlow := one_sub_exp_neg_ge hκ
  have hpow : Real.exp (-κ) ^ m = Real.exp (-((m : ℝ) * κ)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hc : (0 : ℝ) < (1 + κ) / κ := by positivity
  have h1 : (1 + κ) / κ * (κ / (1 + κ)) = 1 := by
    field_simp
  have hfrac : (1 : ℝ) ≤ (1 + κ) / κ * (1 - Real.exp (-κ)) := by
    calc (1 : ℝ) = (1 + κ) / κ * (κ / (1 + κ)) := h1.symm
      _ ≤ (1 + κ) / κ * (1 - Real.exp (-κ)) := mul_le_mul_of_nonneg_left hlow (le_of_lt hc)
  rw [hpow, div_le_iff₀ hgap]
  nlinarith [hfrac, Real.exp_pos (-((m : ℝ) * κ))]

/-- The same bound with the gap cubed, as it occurs in the Cauchy--Schwarz defect. -/
theorem exp_pow_div_one_sub_cube_le {κ : ℝ} (hκ : 0 < κ) (m : ℕ) :
    Real.exp (-κ) ^ m / (1 - Real.exp (-κ)) ^ 3
      ≤ ((1 + κ) / κ) ^ 3 * Real.exp (-((m : ℝ) * κ)) := by
  have hgap : (0 : ℝ) < 1 - Real.exp (-κ) := by
    have := exp_neg_lt_one hκ
    linarith
  have hlow := one_sub_exp_neg_ge hκ
  have hpow : Real.exp (-κ) ^ m = Real.exp (-((m : ℝ) * κ)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hc : (0 : ℝ) < (1 + κ) / κ := by positivity
  have h1 : (1 + κ) / κ * (κ / (1 + κ)) = 1 := by
    field_simp
  have hfrac : (1 : ℝ) ≤ (1 + κ) / κ * (1 - Real.exp (-κ)) := by
    calc (1 : ℝ) = (1 + κ) / κ * (κ / (1 + κ)) := h1.symm
      _ ≤ (1 + κ) / κ * (1 - Real.exp (-κ)) := mul_le_mul_of_nonneg_left hlow (le_of_lt hc)
  have hcube : (1 : ℝ) ≤ ((1 + κ) / κ) ^ 3 * (1 - Real.exp (-κ)) ^ 3 := by
    have hprod : ((1 + κ) / κ * (1 - Real.exp (-κ))) ^ 3
        = ((1 + κ) / κ) ^ 3 * (1 - Real.exp (-κ)) ^ 3 := by ring
    have : (1 : ℝ) ^ 3 ≤ ((1 + κ) / κ * (1 - Real.exp (-κ))) ^ 3 := by
      gcongr
    rw [hprod] at this
    simpa using this
  have hcubepos : (0 : ℝ) < (1 - Real.exp (-κ)) ^ 3 := by positivity
  rw [hpow, div_le_iff₀ hcubepos]
  nlinarith [hcube, Real.exp_pos (-((m : ℝ) * κ))]

/-- **The tail in the Wiman--Valiron normalisation.**  With `κ = N/(4L)` the window tail is at most
`((1 + κ)/κ) e^{−(N+1)κ}`, which is small as soon as `(N+1)κ` exceeds `log(1/κ)` — the regime the
parameter choice actually uses, and one that no lower bound on `κ` can reach. -/
theorem window_tail_le {N : ℕ} {L : ℝ} (hN : 0 < N) (hL : 0 < L) :
    Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1) / (1 - Real.exp (-((N : ℝ) / (4 * L))))
      ≤ (1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))
        * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hκ : (0 : ℝ) < (N : ℝ) / (4 * L) := by positivity
  have h := exp_pow_div_one_sub_le hκ (N + 1)
  have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
  rwa [hcast] at h

/-- **Monotonicity of the estimate in its two tail quantities.**  The explicit right-hand side is
increasing in the window tail and in the cubed-gap tail separately, so any upper bound for those two
quantities may be substituted. -/
theorem wiman_valiron_expression_mono {N : ℕ} {B t₁ t₁' t₃ t₃' : ℝ}
    (hB : 0 ≤ B) (h10 : 0 ≤ t₁) (h1 : t₁ ≤ t₁') (h30 : 0 ≤ t₃) (h3 : t₃ ≤ t₃') :
    (Real.sqrt (2 * (N : ℝ) + 1) + 2 * t₁) * B
        + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (2 * ((N : ℝ) + 1) ^ 2 * t₃)) * (Real.sqrt (2 * (N : ℝ) + 1) + 2 * t₁))
      ≤ (Real.sqrt (2 * (N : ℝ) + 1) + 2 * t₁') * B
        + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * (2 * ((N : ℝ) + 1) ^ 2 * t₃')) * (Real.sqrt (2 * (N : ℝ) + 1) + 2 * t₁')) := by
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (2 * (N : ℝ) + 1) := Real.sqrt_nonneg _
  have hsqc : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by positivity
  have hfirst : (0 : ℝ) ≤ (N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1) := by positivity
  have h30' : (0 : ℝ) ≤ t₃' := le_trans h30 h3
  have hcoef : (0 : ℝ) ≤ 2 * (2 * ((N : ℝ) + 1) ^ 2 * t₃) := by nlinarith [h30, hsqc]
  have hcoef' : (0 : ℝ) ≤ 2 * (2 * ((N : ℝ) + 1) ^ 2 * t₃') := by nlinarith [h30', hsqc]
  have hin0 : (0 : ℝ) ≤ 2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (2 * ((N : ℝ) + 1) ^ 2 * t₃)) := by linarith
  have hin0' : (0 : ℝ) ≤ 2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (2 * ((N : ℝ) + 1) ^ 2 * t₃')) := by linarith
  have hamp0 : (0 : ℝ) ≤ Real.sqrt (2 * (N : ℝ) + 1) + 2 * t₁ := by linarith
  have hamp0' : (0 : ℝ) ≤ Real.sqrt (2 * (N : ℝ) + 1) + 2 * t₁' := by linarith
  gcongr

/-- **The estimate with the tail left free.**  Substituting the unconditional geometric bounds for
the two tails turns the explicit estimate into one whose only transcendental ingredient is the single
factor `e^{−(N+1)κ}` at the rate `κ = N/(4L)`, with the `1/κ` blow-up displayed.  This is the form
that survives when the sampling window is short. -/
theorem exists_radius_point_wiman_valiron_tail
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H s L h : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hs : 0 < s)
    (hLdef : L = 2 * s / H) (hhdef : h = H / 2)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c)
    {N : ℕ} (hN0 : 0 < N) (hN2s : 2 * s ≤ (N : ℝ)) (hN4s : (N : ℝ) ≤ 4 * s) :
    ∃ x ∈ Icc (c + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ (Real.sqrt (2 * (N : ℝ) + 1)
            + 2 * ((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))
                * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L))))))
            * (2 * L * h
              + 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
                  + 1 / (Real.exp h - 1)) / h)
          + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
              + 2 * (2 * ((N : ℝ) + 1) ^ 2
                  * (((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))) ^ 3
                      * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))))))
            * (Real.sqrt (2 * (N : ℝ) + 1)
              + 2 * ((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))
                  * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L))))))) := by
  have hL : 0 < L := by rw [hLdef]; positivity
  have hh : 0 < h := by rw [hhdef]; linarith
  obtain ⟨x, hx, z, hz, hfz, hbound⟩ :=
    exists_radius_point_wiman_valiron_bound ha hn₀ hcd hH hs hLdef hhdef hsmall hN2s hN4s
  refine ⟨x, hx, z, hz, hfz, le_trans hbound ?_⟩
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hκ : (0 : ℝ) < (N : ℝ) / (4 * L) := by positivity
  have hgap : (0 : ℝ) < 1 - Real.exp (-((N : ℝ) / (4 * L))) := by
    have := exp_neg_lt_one hκ
    linarith
  have hexph : 0 < Real.exp h - 1 := by
    have := Real.add_one_le_exp h
    linarith
  have harg : (1 : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
      + 1 / (Real.exp h - 1) := by
    have h1 : (0 : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) < 2 * L * h := by positivity
    have h4 : (0 : ℝ) < 1 / (Real.exp h - 1) := by positivity
    linarith
  have hB : (0 : ℝ) ≤ 2 * L * h
      + 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
          + 1 / (Real.exp h - 1)) / h := by
    have h2 : (0 : ℝ) < 2 * L * h := by positivity
    have h3 : (0 : ℝ) ≤ 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
        + 1 / (Real.exp h - 1)) / h :=
      div_nonneg (by linarith [Real.log_nonneg harg]) (le_of_lt hh)
    linarith
  have ht1 : Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
      / (1 - Real.exp (-((N : ℝ) / (4 * L))))
      ≤ (1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))
        * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))) := window_tail_le hN0 hL
  have ht3 : Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
      / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3
      ≤ ((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))) ^ 3
        * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))) := by
    have hcube := exp_pow_div_one_sub_cube_le hκ (N + 1)
    have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
    rwa [hcast] at hcube
  have hassoc : 2 * ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
      / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3
      = 2 * ((N : ℝ) + 1) ^ 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3) := mul_div_assoc _ _ _
  rw [hassoc]
  exact wiman_valiron_expression_mono hB (by positivity) ht1 (by positivity) ht3

end GaloisForLFunctions.HTGeometry
