import GaloisForLFunctions.RHTower.Sieve.ChebyshevBalanceOne

/-!
# The five terms collapse to a single shape

Feeding the four term reductions and the three edge-power bounds into the right-hand side of
`norm_tsum_vonMangoldt_sub_full_main_le_explicit` collapses it to

```text
( 2SW + ci(4 + 2W) + 2·wd·(W + 1) + M(4 + 2W) + 2·wd·M·W ) · (Z · E),
```

with `Z` the cutoff, `E` the common exponential factor, `W` the smoothing's price, `S` the von
Mangoldt series, `ci = (1-c)⁻¹`, `wd = d - c` and `M` the edge bound.  Everything that depends on
the zeta function has been discharged; what is left is a polynomial in `log T` times `Z·E`.

The mass term `‖mellin w 1‖/T` joins the shape because `1/T` is itself below `E` — the truncation
height decays faster than the left edge saves.
-/

namespace RHTower.Sieve

/-- **The five terms against a single shape.** -/
theorem cheb_kappa_one_terms_shaped {S W Y Z E T Mm ci wd M c Yc Zc Zd : ℝ}
    (hS0 : 0 ≤ S) (hW0 : 0 ≤ W) (hci0 : 0 ≤ ci) (hwd0 : 0 ≤ wd) (hM0 : 0 ≤ M)
    (hT1 : 1 ≤ T) (hE0 : 0 ≤ E) (hY0 : 0 ≤ Y) (hYZ : Y ≤ Z) (hc : 1 / 2 ≤ c)
    (hMm : Mm ≤ Y) (hTE : 1 / T ≤ E) (hZd0 : 0 ≤ Zd)
    (hZd : Zd ≤ Z * E * T) (hZc : Zc ≤ Z * E) (hYc : Yc ≤ Y * E) :
    2 * (S * (W * Zd)) / T
        + (ci * (2 * (Yc / c) + 2 * (W * Zc))
            + 2 * (wd * ((W * Zd / T ^ (1 + 1) + Mm) / T)))
        + (M * (2 * (Yc / c) + 2 * (W * Zc))
            + 2 * (wd * (M * (W * Zd / T ^ (1 + 1)))))
      ≤ (2 * S * W + ci * (4 + 2 * W) + 2 * wd * (W + 1) + M * (4 + 2 * W) + 2 * wd * M * W)
          * (Z * E) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hZ0 : (0 : ℝ) ≤ Z := le_trans hY0 hYZ
  have hZE0 : (0 : ℝ) ≤ Z * E := mul_nonneg hZ0 hE0
  -- the truncation term
  have h1 := cheb_trunc_term_le (S := S) (W := W) (Zd := Zd) (Z := Z) (E := E) (T := T)
    hS0 hW0 hT0 hZd
  -- the left edge's bracket
  have hbr := cheb_left_bracket_le (Yc := Yc) (Zc := Zc) (Y := Y) (Z := Z) (E := E) (W := W)
    (c := c) hc hW0 hY0 hE0 hYZ hYc hZc
  have h2 : ci * (2 * (Yc / c) + 2 * (W * Zc)) ≤ ci * (4 * (Z * E) + 2 * (W * (Z * E))) :=
    mul_le_mul_of_nonneg_left hbr hci0
  have h4 : M * (2 * (Yc / c) + 2 * (W * Zc)) ≤ M * (4 * (Z * E) + 2 * (W * (Z * E))) :=
    mul_le_mul_of_nonneg_left hbr hM0
  -- the horizontal edges' pole term
  have h3a := cheb_horiz_pole_le (w := wd) (Cd := W * Zd) (Mm := Mm) (T := T) hwd0
    (mul_nonneg hW0 hZd0) hT1
  have hsub : (W * Zd + Mm) / T ≤ W * (Z * E) + Z * E := by
    rw [div_le_iff₀ hT0]
    have ha : W * Zd ≤ W * (Z * E * T) := mul_le_mul_of_nonneg_left hZd hW0
    have hb : Mm * (1 / T) ≤ Y * E := mul_le_mul hMm hTE (one_div_nonneg.mpr hT0.le) hY0
    have hbT : Mm * (1 / T) * T = Mm := by field_simp
    have hb2 : Mm ≤ Y * E * T := by
      have := mul_le_mul_of_nonneg_right hb hT0.le
      linarith [this, hbT]
    have hb3 : Y * E * T ≤ Z * E * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hYZ hE0) hT0.le
    linarith [ha, hb2, hb3]
  have h3b : 2 * (wd * ((W * Zd + Mm) / T)) ≤ 2 * (wd * (W * (Z * E) + Z * E)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub hwd0) (by norm_num)
  -- the horizontal edges' regular term
  have h5 := cheb_horiz_reg_le (w := wd) (R := M) (W := W) (Zd := Zd) (Z := Z) (E := E) (T := T)
    hwd0 hM0 hW0 hT1 hZd hZE0
  linarith [h1, h2, h3a, h3b, h4, h5]

end RHTower.Sieve
