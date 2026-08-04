import GaloisForLFunctions.RHTower.CCMRadialProlateDefect

/-!
# The endpoint layer of the pole-uniform comparison

Away from the endpoint the two Bessel model solutions share the envelope `C u^{-1/2}`, which is what the
Volterra estimate uses.  Through the endpoint layer `c xi_s(x) <= 1` that envelope is useless — the
argument is small — and the right common envelope is logarithmic, because the second solution has a
logarithmic singularity at the origin and the first is bounded:

```text
|J_0(u)| <= 1,        |K(u)| <= (pi/4)|log u| + (pi/2) log 2,
```

so `2 + |log u|` dominates both.  The mass the Volterra estimate integrates is then finite as well, and for
a structural reason: the Liouville weight of the defect is *bounded on the whole ray*,

```text
m(x) |a(x)| = (xi_s/xi_s')(x) |a(x)| <= 40,
```

because `m <= x² - 1` cancels the simple pole of `a` exactly.  Both facts are proved here.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The phase against the endpoint logarithm -/

/-- The endpoint phase is at most `sqrt(x² - s)` times the endpoint logarithm: the speed factorises as
`sqrt(x²-s)/sqrt(x²-1)` and the first factor is increasing. -/
theorem xiEndpointPhase_le_sqrt_mul_endpointLog {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hx : 1 ≤ x) :
    xiEndpointPhase s x
      ≤ Real.sqrt (x ^ 2 - s) * GaloisForLFunctions.HTGeometry.endpointLog x := by
  have hA : (0 : ℝ) < 1 - s := by linarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hconv : Real.sqrt (1 - s) * Real.sqrt (1 + (x ^ 2 - 1) / (1 - s))
      = Real.sqrt (x ^ 2 - s) := by
    rw [← Real.sqrt_mul hA.le]
    congr 1
    field_simp
    ring
  have h := xiEndpointPhase_le_sqrt_one_sub_mul_endpointLog hs0 hs1 hx
  rwa [hconv] at h

/-! ## The Liouville weight is quadratic at the endpoint -/

/-- The Liouville weight `m = xi/xi'` is at most `x² - 1`.  Both halves are the endpoint bracket: the phase
is at most `sqrt(x²-s)` times the endpoint logarithm, the logarithm is at most `sqrt(x²-1)`, and
`xi' (x²-1) = sqrt(x²-s) sqrt(x²-1)`. -/
theorem lgWeight_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    lgWeight s x ≤ x ^ 2 - 1 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hV : 0 < xiSpeed s x := xiSpeed_pos hs1 hx
  have hp : (0 : ℝ) < Real.sqrt (x ^ 2 - s) := Real.sqrt_pos.mpr hn
  have hphase : xiEndpointPhase s x
      ≤ Real.sqrt (x ^ 2 - s) * GaloisForLFunctions.HTGeometry.endpointLog x :=
    xiEndpointPhase_le_sqrt_mul_endpointLog hs0 hs1 hx.le
  have hlog : GaloisForLFunctions.HTGeometry.endpointLog x ≤ Real.sqrt (x ^ 2 - 1) :=
    GaloisForLFunctions.HTGeometry.endpointLog_le_sqrt hx.le
  have hmul : xiSpeed s x * (x ^ 2 - 1)
      = Real.sqrt (x ^ 2 - s) * Real.sqrt (x ^ 2 - 1) := xiSpeed_mul_sub_one hs1 hx
  rw [lgWeight, div_le_iff₀ hV]
  calc xiEndpointPhase s x
      ≤ Real.sqrt (x ^ 2 - s) * GaloisForLFunctions.HTGeometry.endpointLog x := hphase
    _ ≤ Real.sqrt (x ^ 2 - s) * Real.sqrt (x ^ 2 - 1) := by
        exact mul_le_mul_of_nonneg_left hlog hp.le
    _ = (x ^ 2 - 1) * xiSpeed s x := by
        rw [← hmul]
        ring

/-- **The defect is bounded by `40` in the Liouville weight, on the whole ray.**  The weight vanishes
quadratically at the endpoint and the defect has only a simple pole, so their product is bounded — this is
the accounting that makes the Volterra mass finite, and it holds without any restriction on `x`. -/
theorem lgWeight_mul_abs_defect_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    lgWeight s x * |lgNormalFormDefect s c (radialProlateQ s c) x| ≤ 40 := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hm : 0 < lgWeight s x := lgWeight_pos hs0 hs1 hx
  have hmle : lgWeight s x ≤ x ^ 2 - 1 := lgWeight_le hs0 hs1 hx
  have ha : |lgNormalFormDefect s c (radialProlateQ s c) x| ≤ 40 / (x ^ 2 - 1) :=
    abs_lgNormalFormDefect_radialProlate_le hs0 hs1 hx
  have habs : (0 : ℝ) ≤ |lgNormalFormDefect s c (radialProlateQ s c) x| := abs_nonneg _
  calc lgWeight s x * |lgNormalFormDefect s c (radialProlateQ s c) x|
      ≤ (x ^ 2 - 1) * (40 / (x ^ 2 - 1)) := by
        exact mul_le_mul hmle ha habs (by linarith)
    _ = 40 := by
        field_simp

/-! ## The logarithmic envelope of the model pair -/

/-- The second Bessel solution has a logarithmic envelope: `|K(u)| <= 2 + |log u|`, from
`K = (pi/4) log u · J_0 + M` with `|J_0| <= 1` and `|M| <= (pi/2) log 2`. -/
theorem abs_besselK_le_log_envelope (u : ℝ) : |besselK u| ≤ 2 + |Real.log u| := by
  have h1 : |besselJ0 u| ≤ 1 := abs_besselJ0_le_one u
  have h2 : |besselM u| ≤ Real.pi / 2 * Real.log 2 := abs_besselM_le u
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have h3 : Real.pi / 2 * Real.log 2 ≤ 2 := by nlinarith
  have h5 : Real.pi / 4 * |besselJ0 u| ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 - Real.pi) (abs_nonneg (besselJ0 u)), h1,
      abs_nonneg (besselJ0 u)]
  have h4 : |Real.pi / 4 * Real.log u * besselJ0 u| ≤ |Real.log u| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4)]
    calc Real.pi / 4 * |Real.log u| * |besselJ0 u|
        = Real.pi / 4 * |besselJ0 u| * |Real.log u| := by ring
      _ ≤ 1 * |Real.log u| := mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
      _ = |Real.log u| := one_mul _
  rw [besselK]
  calc |Real.pi / 4 * Real.log u * besselJ0 u + besselM u|
      ≤ |Real.pi / 4 * Real.log u * besselJ0 u| + |besselM u| := abs_add_le _ _
    _ ≤ |Real.log u| + 2 := by linarith
    _ = 2 + |Real.log u| := by ring

/-- The first Bessel solution obeys the same logarithmic envelope, trivially. -/
theorem abs_besselJ0_le_log_envelope (u : ℝ) : |besselJ0 u| ≤ 2 + |Real.log u| := by
  have h1 : |besselJ0 u| ≤ 1 := abs_besselJ0_le_one u
  have h2 : (0 : ℝ) ≤ |Real.log u| := abs_nonneg _
  linarith

/-- **The logarithmic common envelope of the model pair.**  Valid for every argument, in particular through
the endpoint layer `c xi_s(x) <= 1` where the square-root envelope carries no information. -/
theorem abs_lgBesselModel_le_log_envelope (s c x : ℝ) :
    |lgBesselModel s c x| ≤ 2 + |Real.log (c * xiEndpointPhase s x)|
      ∧ |lgBesselModel2 s c x| ≤ 2 + |Real.log (c * xiEndpointPhase s x)| := by
  refine ⟨?_, ?_⟩
  · rw [lgBesselModel]
    exact abs_besselJ0_le_log_envelope _
  · rw [lgBesselModel2]
    exact abs_besselK_le_log_envelope _

end GaloisForLFunctions.RHTower

end
