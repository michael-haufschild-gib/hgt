import GaloisForLFunctions.HTGeometry.WimanValironPolynomialBound

/-!
# The Wiman--Valiron bound in closed form

Once the window tail is below one — the regime the parameter choice arranges — every factor of the
explicit estimate collapses into a power of the sampling scale.  With `1 ≤ s`, `2s ≤ N ≤ 4s`,
`L = 2s/H` and `h = H/2` the right-hand side is at most

  `49 s^{3/2} + 20 sqrt s * log (nu + 2s + 1 + 2/H) / H`,

with no transcendental constant left anywhere.  The first term is the main term and the second is
the logarithmic correction; the parameter choice makes both `o(nu)`.
-/

open MeasureTheory Complex Set

namespace GaloisForLFunctions.HTGeometry

/-! ## Two elementary reciprocals -/

private theorem le_cube_of_one_le {g : ℝ} (hg : 1 ≤ g) : g ≤ g ^ 3 := by
  nlinarith [hg, mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ g) (by linarith : (0 : ℝ) ≤ g - 1))
    (by linarith : (0 : ℝ) ≤ g + 1)]

/-- The geometric correction is below `2/H`. -/
theorem one_div_exp_half_sub_one_le {H : ℝ} (hH : 0 < H) :
    1 / (Real.exp (H / 2) - 1) ≤ 2 / H := by
  have hX : H / 2 ≤ Real.exp (H / 2) - 1 := by
    have := Real.add_one_le_exp (H / 2)
    linarith
  have hXpos : (0 : ℝ) < Real.exp (H / 2) - 1 := by linarith
  rw [div_le_iff₀ hXpos]
  have hstep : (2 / H) * (H / 2) ≤ (2 / H) * (Real.exp (H / 2) - 1) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have heq : (2 / H) * (H / 2) = 1 := by
    field_simp
  linarith

/-- A lower bound on the rate gives an upper bound on its reciprocal amplification. -/
theorem one_add_div_le {k H : ℝ} (hH : 0 < H) (hk : H / 4 ≤ k) (hkpos : 0 < k) :
    (1 + k) / k ≤ 1 + 4 / H := by
  have hinv : 1 / k ≤ 4 / H := by
    rw [div_le_iff₀ hkpos]
    have hstep : (4 / H) * (H / 4) ≤ (4 / H) * k := mul_le_mul_of_nonneg_left hk (by positivity)
    have heq : (4 / H) * (H / 4) = 1 := by field_simp
    linarith
  have hsplit : (1 + k) / k = 1 / k + 1 := by
    field_simp
  rw [hsplit]
  linarith

/-! ## The closed form, abstractly -/

/-- **The shape of the estimate collapses.**  Whatever the analytic meaning of the quantities, an
expression of the Wiman--Valiron shape whose amplitude is below `3 sqrt s`, whose two tails are below
one and whose bracket is below `2s + 4 Lg/H` is at most `49 s^{3/2} + 20 sqrt s Lg/H`. -/
theorem tail_expression_le {N : ℕ} {s Q GD G3D B Lg H : ℝ}
    (hs1 : 1 ≤ s) (hN4 : (N : ℝ) ≤ 4 * s)
    (hQ : Q ≤ 3 * Real.sqrt s) (hQ0 : 0 ≤ Q)
    (hGD : GD ≤ 1) (hGD0 : 0 ≤ GD)
    (hG3D : G3D ≤ 1) (hG3D0 : 0 ≤ G3D)
    (hH : 0 < H) (hB : B ≤ 2 * s + 4 * Lg / H) (hB0 : 0 ≤ B) :
    (Q + 2 * GD) * B
      + Real.sqrt (2 * ((N : ℝ) ^ 2 * Q + 2 * (2 * ((N : ℝ) + 1) ^ 2 * G3D)) * (Q + 2 * GD))
      ≤ 49 * (s * Real.sqrt s) + 20 * Real.sqrt s * Lg / H := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hsqs : (1 : ℝ) ≤ Real.sqrt s := by
    have := Real.sqrt_le_sqrt hs1
    simpa using this
  have hsqs0 : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hsqsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt (le_of_lt hs0)
  have hA : Q + 2 * GD ≤ 5 * Real.sqrt s := by linarith
  have hA0 : (0 : ℝ) ≤ Q + 2 * GD := by linarith
  have hBtop : (0 : ℝ) ≤ 2 * s + 4 * Lg / H := le_trans hB0 hB
  -- the first term
  have hterm1 : (Q + 2 * GD) * B
      ≤ 10 * (s * Real.sqrt s) + 20 * Real.sqrt s * Lg / H := by
    have hmul : (Q + 2 * GD) * B ≤ (5 * Real.sqrt s) * (2 * s + 4 * Lg / H) :=
      mul_le_mul hA hB hB0 (by positivity)
    have hexp : (5 * Real.sqrt s) * (2 * s + 4 * Lg / H)
        = 10 * (s * Real.sqrt s) + 20 * Real.sqrt s * Lg / H := by
      field_simp
      ring
    linarith [hmul, hexp.le, hexp.ge]
  -- the second term
  have hfirst : (N : ℝ) ^ 2 * Q ≤ 48 * (s ^ 2 * Real.sqrt s) := by
    have hNsq16 : (N : ℝ) ^ 2 ≤ 16 * s ^ 2 := by nlinarith [hN4, hs0]
    calc (N : ℝ) ^ 2 * Q ≤ 16 * s ^ 2 * (3 * Real.sqrt s) :=
          mul_le_mul hNsq16 hQ hQ0 (by positivity)
      _ = 48 * (s ^ 2 * Real.sqrt s) := by ring
  have hsecond : 2 * (2 * ((N : ℝ) + 1) ^ 2 * G3D) ≤ 100 * s ^ 2 := by
    have hNb : ((N : ℝ) + 1) ^ 2 ≤ 25 * s ^ 2 := by nlinarith [hN4, hs1]
    have hmul : ((N : ℝ) + 1) ^ 2 * G3D ≤ 25 * s ^ 2 * 1 :=
      mul_le_mul hNb hG3D hG3D0 (by positivity)
    nlinarith [hmul]
  have hs2 : s ^ 2 ≤ s ^ 2 * Real.sqrt s := by nlinarith [hsqs, hs0]
  have hinner : 2 * ((N : ℝ) ^ 2 * Q + 2 * (2 * ((N : ℝ) + 1) ^ 2 * G3D))
      ≤ 296 * (s ^ 2 * Real.sqrt s) := by linarith
  have hprod : 2 * ((N : ℝ) ^ 2 * Q + 2 * (2 * ((N : ℝ) + 1) ^ 2 * G3D)) * (Q + 2 * GD)
      ≤ 1521 * s ^ 3 := by
    calc 2 * ((N : ℝ) ^ 2 * Q + 2 * (2 * ((N : ℝ) + 1) ^ 2 * G3D)) * (Q + 2 * GD)
        ≤ (296 * (s ^ 2 * Real.sqrt s)) * (5 * Real.sqrt s) :=
          mul_le_mul hinner hA hA0 (by positivity)
      _ = 1480 * s ^ 3 := by
          have hr : (296 * (s ^ 2 * Real.sqrt s)) * (5 * Real.sqrt s)
              = 1480 * s ^ 2 * (Real.sqrt s * Real.sqrt s) := by ring
          rw [hr, hsqsq]
          ring
      _ ≤ 1521 * s ^ 3 := by nlinarith [hs0]
  have hterm2 : Real.sqrt (2 * ((N : ℝ) ^ 2 * Q + 2 * (2 * ((N : ℝ) + 1) ^ 2 * G3D))
      * (Q + 2 * GD)) ≤ 39 * (s * Real.sqrt s) := by
    have hval : (39 * (s * Real.sqrt s)) ^ 2 = 1521 * s ^ 3 := by
      have hr : (39 * (s * Real.sqrt s)) ^ 2 = 1521 * s ^ 2 * (Real.sqrt s * Real.sqrt s) := by
        ring
      rw [hr, hsqsq]
      ring
    calc Real.sqrt (2 * ((N : ℝ) ^ 2 * Q + 2 * (2 * ((N : ℝ) + 1) ^ 2 * G3D)) * (Q + 2 * GD))
        ≤ Real.sqrt (1521 * s ^ 3) := Real.sqrt_le_sqrt hprod
      _ = 39 * (s * Real.sqrt s) := by
          rw [← hval, Real.sqrt_sq (by positivity)]
  linarith

/-! ## The closed form of the Wiman--Valiron estimate -/

/-- **The estimate in closed form.**  Under `1 ≤ s`, `2s ≤ N ≤ 4s`, `L = 2s/H`, `h = H/2` and the
tail condition `(1 + 4/H)^3 e^{-sH/2} ≤ 1`, the explicit right-hand side of the Wiman--Valiron
estimate is at most `49 s^{3/2} + 20 sqrt s log(nu + 2s + 1 + 2/H)/H`. -/
theorem wiman_valiron_tail_bound_le_clean {N : ℕ} {s H L h nu : ℝ}
    (hs1 : 1 ≤ s) (hH : 0 < H) (hLdef : L = 2 * s / H) (hhdef : h = H / 2)
    (hN2 : 2 * s ≤ (N : ℝ)) (hN4 : (N : ℝ) ≤ 4 * s) (hnu : 0 ≤ nu)
    (hP : (1 + 4 / H) ^ 3 * Real.exp (-(s * H / 2)) ≤ 1) :
    (Real.sqrt (2 * (N : ℝ) + 1)
        + 2 * ((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))
            * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L))))))
        * (2 * L * h
          + 2 * Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) / h)
      + Real.sqrt (2 * ((N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1)
          + 2 * (2 * ((N : ℝ) + 1) ^ 2
              * (((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))) ^ 3
                  * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))))))
        * (Real.sqrt (2 * (N : ℝ) + 1)
          + 2 * ((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))
              * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))))))
      ≤ 49 * (s * Real.sqrt s)
        + 20 * Real.sqrt s * Real.log (nu + 2 * s + 1 + 2 / H) / H := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hL : 0 < L := by rw [hLdef]; positivity
  have hhpos : (0 : ℝ) < h := by rw [hhdef]; linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  -- the rate
  have hkpos : (0 : ℝ) < (N : ℝ) / (4 * L) := by positivity
  have hkeq : (N : ℝ) / (4 * L) = (N : ℝ) * H / (8 * s) := by
    rw [hLdef]
    field_simp
    ring
  have hk1 : H / 4 ≤ (N : ℝ) / (4 * L) := by
    rw [hkeq, le_div_iff₀ (by positivity : (0 : ℝ) < 8 * s)]
    nlinarith [hN2, hH, hs0]
  have hNsq : 4 * s ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith [hN2, hs0]
  have hk2 : s * H / 2 ≤ ((N : ℝ) + 1) * ((N : ℝ) / (4 * L)) := by
    have hbase : s * H / 2 ≤ (N : ℝ) * ((N : ℝ) / (4 * L)) := by
      rw [hkeq]
      have heq : (N : ℝ) * ((N : ℝ) * H / (8 * s)) = (N : ℝ) ^ 2 * H / (8 * s) := by ring
      rw [heq, le_div_iff₀ (by positivity : (0 : ℝ) < 8 * s)]
      nlinarith [hNsq, hH]
    nlinarith [hbase, hkpos]
  -- the two tails
  have hG : (1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L)) ≤ 1 + 4 / H :=
    one_add_div_le hH hk1 hkpos
  have hG1 : (1 : ℝ) ≤ (1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L)) := by
    rw [le_div_iff₀ hkpos]
    linarith
  have hD : Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))) ≤ Real.exp (-(s * H / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hD0 : (0 : ℝ) < Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))) := Real.exp_pos _
  have hH4 : (1 : ℝ) ≤ 1 + 4 / H := by
    have : (0 : ℝ) < 4 / H := by positivity
    linarith
  have hG3D : ((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))) ^ 3
      * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))) ≤ 1 := by
    calc ((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))) ^ 3
          * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L))))
        ≤ (1 + 4 / H) ^ 3 * Real.exp (-(s * H / 2)) := by gcongr
      _ ≤ 1 := hP
  have hG3D0 : (0 : ℝ) ≤ ((1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))) ^ 3
      * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))) := by positivity
  have hGD0 : (0 : ℝ) ≤ (1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))
      * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))) := by positivity
  have hGD : (1 + (N : ℝ) / (4 * L)) / ((N : ℝ) / (4 * L))
      * Real.exp (-(((N : ℝ) + 1) * ((N : ℝ) / (4 * L)))) ≤ 1 := by
    have hpow := le_cube_of_one_le hG1
    nlinarith [hG3D, hpow, hD0]
  -- the window
  have hQ : Real.sqrt (2 * (N : ℝ) + 1) ≤ 3 * Real.sqrt s := by
    have h1 : Real.sqrt (2 * (N : ℝ) + 1) ≤ Real.sqrt (9 * s) :=
      Real.sqrt_le_sqrt (by nlinarith [hN4, hs1])
    have h2 : Real.sqrt (9 * s) = 3 * Real.sqrt s := by
      rw [show (9 : ℝ) * s = 3 ^ 2 * s by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
    linarith
  have hQ0 : (0 : ℝ) ≤ Real.sqrt (2 * (N : ℝ) + 1) := Real.sqrt_nonneg _
  -- the bracket
  have h2Lh : 2 * L * h = 2 * s := by
    rw [hLdef, hhdef]
    field_simp
  have hgeo : 1 / (Real.exp h - 1) ≤ 2 / H := by
    rw [hhdef]
    exact one_div_exp_half_sub_one_le hH
  have hgeo0 : (0 : ℝ) < 1 / (Real.exp h - 1) := by
    have hX : h ≤ Real.exp h - 1 := by
      have := Real.add_one_le_exp h
      linarith
    have : (0 : ℝ) < Real.exp h - 1 := by linarith
    positivity
  have hlogmono : Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1))
      ≤ Real.log (nu + 2 * s + 1 + 2 / H) := by
    refine Real.log_le_log ?_ ?_
    · rw [h2Lh]; linarith
    · rw [h2Lh]; linarith
  have hlog0 : (0 : ℝ) ≤ Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) := by
    refine Real.log_nonneg ?_
    rw [h2Lh]
    linarith
  have hdivH : ∀ X : ℝ, 2 * X / h = 4 * X / H := by
    intro X
    rw [hhdef]
    field_simp
    ring
  have hdivmono : ∀ X Y : ℝ, X ≤ Y → 4 * X / H ≤ 4 * Y / H := by
    intro X Y hXY
    gcongr
  have hB : 2 * L * h + 2 * Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) / h
      ≤ 2 * s + 4 * Real.log (nu + 2 * s + 1 + 2 / H) / H := by
    have heqh := hdivH (Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)))
    have hstepl := hdivmono (Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)))
      (Real.log (nu + 2 * s + 1 + 2 / H)) hlogmono
    linarith [h2Lh.le, h2Lh.ge, heqh.le, heqh.ge, hstepl]
  have hB0 : (0 : ℝ) ≤ 2 * L * h
      + 2 * Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) / h := by
    have h1 : (0 : ℝ) ≤ 2 * Real.log (nu + 2 * L * h + 1 + 1 / (Real.exp h - 1)) / h :=
      div_nonneg (by linarith) (le_of_lt hhpos)
    have h2 : (0 : ℝ) < 2 * L * h := by rw [h2Lh]; linarith
    linarith
  exact tail_expression_le hs1 hN4 hQ hQ0 hGD hGD0 hG3D hG3D0 hH hB hB0

end GaloisForLFunctions.HTGeometry
