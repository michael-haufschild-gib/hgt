/-
# Hyperbolic cotangent / cosecant infrastructure for the lattice (S-mono) proof

`coth` and `csch` are not in mathlib. This module builds the pieces the SPUR-R
lattice-energy analysis (docs 29–31, tasks #138/#142) needs:

* `rcoth x = cosh x / sinh x`, `rcsch x = 1 / sinh x`;
* positivity and `1 < rcoth x` on `x > 0` (the swap-step bound `coth > 1`);
* strict antitonicity of `rcoth`, `rcsch`, and `phi = rcsch² · rcoth` on `(0,∞)`
  — via the `sinh` subtraction formula and `sinh` monotonicity, no derivatives;
* the derivatives at every nonzero point: `rcoth′ = −rcsch²`,
  `rcsch′ = −rcoth·rcsch`, `(rcsch²)′ = −2·rphi`;
* the asymptote excess `rcoth v − 1 = 2/(e^{2v} − 1)` and the two-sided bound
  `1/v ≤ rcoth v < 1 + 1/v` on `v > 0`.

The lattice field `Σ coth((t−t_k)/2)` is built from these; its strict monotonicity
between consecutive poles and the `coth > 1` swap bound are the two engines of the
`s`-march (doc 29 step (b)).
-/
import Mathlib

namespace RHTower

open Real Set

/-- Real hyperbolic cotangent. -/
noncomputable def rcoth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

/-- Real hyperbolic cosecant. -/
noncomputable def rcsch (x : ℝ) : ℝ := 1 / Real.sinh x

@[simp] theorem rcoth_neg (x : ℝ) : rcoth (-x) = - rcoth x := by
  simp [rcoth, Real.sinh_neg, Real.cosh_neg, div_neg]

@[simp] theorem rcsch_neg (x : ℝ) : rcsch (-x) = - rcsch x := by
  simp [rcsch, Real.sinh_neg, div_neg]

theorem sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x :=
  Real.sinh_pos_iff.mpr hx

theorem rcsch_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < rcsch x := by
  rw [rcsch]
  exact one_div_pos.mpr (sinh_pos_of_pos hx)

theorem rcoth_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < rcoth x := by
  rw [rcoth]
  exact div_pos (Real.cosh_pos x) (sinh_pos_of_pos hx)

/-- The swap-step bound: `1 < coth x` for `x > 0` (each swap term exceeds `1`). -/
theorem one_lt_rcoth_of_pos {x : ℝ} (hx : 0 < x) : 1 < rcoth x := by
  rw [rcoth, lt_div_iff₀ (sinh_pos_of_pos hx), one_mul]
  exact Real.sinh_lt_cosh x

/-- `coth` is strictly decreasing on `(0,∞)` — via `sinh (y−x) > 0`. -/
theorem rcoth_strictAntiOn_pos : StrictAntiOn rcoth (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  have sx : 0 < Real.sinh x := sinh_pos_of_pos hx
  have sy : 0 < Real.sinh y := sinh_pos_of_pos hy
  rw [rcoth, rcoth, div_lt_div_iff₀ sy sx]
  have hsub : Real.sinh (y - x) =
      Real.sinh y * Real.cosh x - Real.cosh y * Real.sinh x := Real.sinh_sub y x
  have hpos : 0 < Real.sinh (y - x) := sinh_pos_of_pos (by linarith)
  nlinarith [hsub, hpos]

/-- `csch` is strictly decreasing on `(0,∞)`. -/
theorem rcsch_strictAntiOn_pos : StrictAntiOn rcsch (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  have sx : 0 < Real.sinh x := sinh_pos_of_pos hx
  have sy : 0 < Real.sinh y := sinh_pos_of_pos hy
  rw [rcsch, rcsch, div_lt_div_iff₀ sy sx, one_mul, one_mul]
  exact Real.sinh_strictMono hxy

/-- The lattice spectator weight `φ = csch² · coth`, positive and strictly decreasing
on `(0,∞)` (product of positive strictly-decreasing functions). -/
noncomputable def rphi (x : ℝ) : ℝ := (rcsch x)^(2 : ℕ) * rcoth x

theorem rphi_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < rphi x := by
  rw [rphi]
  exact mul_pos (pow_pos (rcsch_pos_of_pos hx) 2) (rcoth_pos_of_pos hx)

/-- `sinh u ≥ eᵘ/4` for `u ≥ 1` (since `e^{2u} ≥ 2`): a clean exponential lower bound. -/
theorem sinh_ge_quarter_exp {u : ℝ} (hu : 1 ≤ u) : Real.exp u / 4 ≤ Real.sinh u := by
  have ha : 0 < Real.exp u := Real.exp_pos u
  have hcancel : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]; simp
  have ha2 : 2 ≤ Real.exp u * Real.exp u := by
    rw [← Real.exp_add]
    have h2 : Real.exp 2 ≤ Real.exp (u + u) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [Real.add_one_le_exp (2 : ℝ), h2]
  rw [Real.sinh_eq]
  nlinarith [ha, ha2, hcancel, Real.exp_pos (-u)]

/-- `cosh u ≤ eᵘ` for `u ≥ 0`. -/
theorem cosh_le_exp {u : ℝ} (hu : 0 ≤ u) : Real.cosh u ≤ Real.exp u := by
  rw [Real.cosh_eq]
  have : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- **`φ` exponential tail bound**: `φ(u) = cosh u/sinh³u ≤ 64·e^{−2u}` for `u ≥ 1`. This
controls the far-behind overhang of the outer-range lattice (S-mono), against the cubic near
term `φ(s/2) ~ 8/s³`. -/
theorem rphi_le_exp {u : ℝ} (hu : 1 ≤ u) : rphi u ≤ 64 * Real.exp (-2 * u) := by
  have hs : 0 < Real.sinh u := sinh_pos_of_pos (by linarith)
  have hsq : Real.exp u / 4 ≤ Real.sinh u := sinh_ge_quarter_exp hu
  have hcosh : Real.cosh u ≤ Real.exp u := cosh_le_exp (by linarith)
  have hrphi : rphi u = Real.cosh u / (Real.sinh u) ^ (3 : ℕ) := by
    simp only [rphi, rcsch, rcoth]; field_simp
  have hcube : (Real.exp u / 4) ^ (3 : ℕ) ≤ (Real.sinh u) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hsq 3
  have hexp3 : (Real.exp u / 4) ^ (3 : ℕ) = Real.exp (3 * u) / 64 := by
    rw [div_pow, ← Real.exp_nat_mul]
    norm_num
  have hden : Real.exp (3 * u) / 64 ≤ (Real.sinh u) ^ (3 : ℕ) := hexp3 ▸ hcube
  have hfinal : Real.exp u / (Real.exp (3 * u) / 64) = 64 * Real.exp (-2 * u) := by
    rw [div_div_eq_mul_div, mul_comm, mul_div_assoc]
    congr 1
    rw [← Real.exp_sub]; congr 1; ring
  rw [hrphi]
  calc Real.cosh u / (Real.sinh u) ^ (3 : ℕ)
      ≤ Real.exp u / (Real.exp (3 * u) / 64) := by gcongr
    _ = 64 * Real.exp (-2 * u) := hfinal

/-- **Geometric tail bound**: `Σ_{n<K} φ(a+nδ) ≤ 64 e^{−2a}/(1−e^{−2δ})` for `a ≥ 1`,
`δ > 0`. The far-behind overhang is a convergent geometric series — each `φ` at argument
`≥ 1` decays like `e^{−2·arg}` (via `rphi_le_exp`). -/
theorem rphi_geom_tail_le {a δ : ℝ} (ha : 1 ≤ a) (hδ : 0 < δ) (K : ℕ) :
    ∑ n ∈ Finset.range K, rphi (a + n * δ)
      ≤ 64 * Real.exp (-2 * a) / (1 - Real.exp (-2 * δ)) := by
  set r := Real.exp (-2 * δ) with hr_def
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr_def, Real.exp_lt_one_iff]; linarith
  have hden : (0 : ℝ) < 1 - r := by linarith
  have hbound : ∀ n ∈ Finset.range K, rphi (a + n * δ) ≤ 64 * Real.exp (-2 * a) * r ^ n := by
    intro n _
    have han : (1 : ℝ) ≤ a + n * δ := by
      have : (0 : ℝ) ≤ (n : ℝ) * δ := by positivity
      linarith
    calc rphi (a + n * δ) ≤ 64 * Real.exp (-2 * (a + n * δ)) := rphi_le_exp han
      _ = 64 * Real.exp (-2 * a) * r ^ n := by
          rw [hr_def, ← Real.exp_nat_mul,
            show -2 * (a + (n : ℝ) * δ) = -2 * a + (n : ℝ) * (-2 * δ) from by ring,
            Real.exp_add]
          ring
  have hgeom : ∑ n ∈ Finset.range K, r ^ n ≤ 1 / (1 - r) := by
    rw [le_div_iff₀ hden]
    have htel : (∑ n ∈ Finset.range K, r ^ n) * (1 - r) = 1 - r ^ K := by
      linear_combination -(geom_sum_mul r K)
    rw [htel]; nlinarith [pow_nonneg hr0.le K]
  calc ∑ n ∈ Finset.range K, rphi (a + n * δ)
      ≤ ∑ n ∈ Finset.range K, 64 * Real.exp (-2 * a) * r ^ n := Finset.sum_le_sum hbound
    _ = 64 * Real.exp (-2 * a) * ∑ n ∈ Finset.range K, r ^ n := by rw [Finset.mul_sum]
    _ ≤ 64 * Real.exp (-2 * a) * (1 / (1 - r)) := by gcongr
    _ = 64 * Real.exp (-2 * a) / (1 - r) := by ring

theorem cosh_one_lt_two : Real.cosh 1 < 2 := by
  rw [Real.cosh_eq]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : 0 < Real.exp (-1) := Real.exp_pos _
  have h3 : Real.exp (-1) < 1 := by
    rw [Real.exp_neg]
    exact inv_lt_one_of_one_lt₀ (by nlinarith [Real.exp_one_gt_d9])
  nlinarith [h1, h2, h3]

/-- **`sinh x < x·cosh x` for `x > 0`** — equivalently `tanh x < x`:
`t·cosh t − sinh t` is `0` at `0` and strictly increasing on `[0,∞)`
(derivative `t·sinh t > 0`). -/
theorem sinh_lt_mul_cosh {x : ℝ} (hx : 0 < x) : Real.sinh x < x * Real.cosh x := by
  have key : StrictMonoOn (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact Continuous.continuousOn (by fun_prop)
    · intro t ht
      rw [interior_Ici] at ht
      have htp : (0:ℝ) < t := ht
      have hderiv : HasDerivAt (fun t : ℝ => t * Real.cosh t - Real.sinh t)
          (t * Real.sinh t) t := by
        have h1 : HasDerivAt (fun t : ℝ => t * Real.cosh t)
            (1 * Real.cosh t + t * Real.sinh t) t :=
          (hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)
        have h2 := h1.sub (Real.hasDerivAt_sinh t)
        have hfun :
            ((fun t : ℝ => t * Real.cosh t) - fun t : ℝ => Real.sinh t) =
              (fun t : ℝ => t * Real.cosh t - Real.sinh t) := by
          funext t
          rfl
        rw [hfun] at h2
        apply h2.congr_deriv
        ring
      rw [hderiv.deriv]
      exact mul_pos htp (Real.sinh_pos_iff.mpr htp)
  have h := key (self_mem_Ici) (mem_Ici.mpr hx.le) hx
  simp only [Real.cosh_zero, Real.sinh_zero, mul_one, sub_zero] at h
  linarith

/-- `sinh x ≤ x·cosh x` for `x ≥ 0`. -/
theorem sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  · exact (sinh_lt_mul_cosh hx0).le

/-- **`φ` near-cubic lower bound**: `φ(x) = cosh x/sinh³x ≥ 1/(4x³)` for `0 < x ≤ 1`
(from `sinh x ≤ x cosh x` and `cosh x ≤ cosh 1 < 2`). The cubic near term that dominates the
exponential far-behind overhang in the outer-range lattice (S-mono). -/
theorem rphi_ge_cubic {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : 1 / (4 * x ^ (3 : ℕ)) ≤ rphi x := by
  have hs : 0 < Real.sinh x := sinh_pos_of_pos hx0
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have hsx : Real.sinh x ≤ x * Real.cosh x := sinh_le_mul_cosh hx0.le
  have hcosh1 : Real.cosh x ≤ Real.cosh 1 := by
    rw [Real.cosh_le_cosh]; rw [abs_of_pos hx0, abs_of_pos]; exact hx1; norm_num
  have hcosh2 : Real.cosh x < 2 := lt_of_le_of_lt hcosh1 cosh_one_lt_two
  have hrphi : rphi x = Real.cosh x / (Real.sinh x) ^ (3 : ℕ) := by
    simp only [rphi, rcsch, rcoth]; field_simp
  have hcube : (Real.sinh x) ^ (3 : ℕ) ≤ (x * Real.cosh x) ^ (3 : ℕ) := pow_le_pow_left₀ hs.le hsx 3
  rw [hrphi]
  have hc4 : Real.cosh x ^ (2 : ℕ) < 4 := by nlinarith [hcosh2, hc]
  calc (1 : ℝ) / (4 * x ^ (3 : ℕ)) ≤ Real.cosh x / (x * Real.cosh x) ^ (3 : ℕ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos (pow_pos hx0 3) hc, hc4]
    _ ≤ Real.cosh x / (Real.sinh x) ^ (3 : ℕ) := by gcongr

theorem rphi_strictAntiOn_pos : StrictAntiOn rphi (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  have hcs : (rcsch y)^(2 : ℕ) < (rcsch x)^(2 : ℕ) := by
    have h1 : 0 < rcsch y := rcsch_pos_of_pos hy
    have h2 : rcsch y < rcsch x := rcsch_strictAntiOn_pos (mem_Ioi.mpr hx) (mem_Ioi.mpr hy) hxy
    nlinarith [h1, h2]
  have hco : rcoth y < rcoth x := rcoth_strictAntiOn_pos (mem_Ioi.mpr hx) (mem_Ioi.mpr hy) hxy
  have hcoy : 0 < rcoth y := rcoth_pos_of_pos hy
  have hcsy : 0 < (rcsch y)^(2 : ℕ) := pow_pos (rcsch_pos_of_pos hy) 2
  rw [rphi, rphi]
  nlinarith [hcs, hco, hcoy, hcsy]

end RHTower

namespace RHTower

open Real Set

/-! ### Derivatives at nonzero points, and the exponential form of the asymptote excess -/

/-- `coth' = −csch²` at every nonzero point (quotient rule + `cosh²−sinh²=1`). -/
theorem rcoth_hasDerivAt {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt rcoth (-(rcsch u) ^ (2 : ℕ)) u := by
  have hs : Real.sinh u ≠ 0 := Real.sinh_ne_zero.mpr hu
  have h := (Real.hasDerivAt_cosh u).div (Real.hasDerivAt_sinh u) hs
  have hfun :
      (fun x : ℝ => Real.cosh x) / (fun x : ℝ => Real.sinh x) = rcoth := by
    funext x
    rfl
  rw [hfun] at h
  apply h.congr_deriv
  rw [rcsch]
  have hid : Real.cosh u ^ (2 : ℕ) - Real.sinh u ^ (2 : ℕ) = 1 := Real.cosh_sq_sub_sinh_sq u
  field_simp
  nlinarith [hid]

/-- `csch' = −coth·csch` at every nonzero point. -/
theorem rcsch_hasDerivAt {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt rcsch (-rcoth u * rcsch u) u := by
  have hs : Real.sinh u ≠ 0 := Real.sinh_ne_zero.mpr hu
  have h : HasDerivAt (fun x => (Real.sinh x)⁻¹) (-Real.cosh u / Real.sinh u ^ (2 : ℕ)) u :=
    (Real.hasDerivAt_sinh u).inv hs
  have hfun : (fun x => (Real.sinh x)⁻¹) = rcsch := by funext x; rw [rcsch, one_div]
  rw [hfun] at h
  have hval : -Real.cosh u / Real.sinh u ^ (2 : ℕ) = -rcoth u * rcsch u := by
    unfold rcoth rcsch; field_simp
  rw [hval] at h
  exact h

/-- `(csch²)' = −2φ` where `φ = csch²·coth` (`rphi`). -/
theorem rcsch_sq_hasDerivAt {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun u => (rcsch u) ^ (2 : ℕ)) (-2 * rphi u) u := by
  have h := (rcsch_hasDerivAt hu).pow 2
  have hfun :
      (fun x : ℝ => rcsch x) ^ (2 : ℕ) = (fun x : ℝ => (rcsch x) ^ (2 : ℕ)) := by
    funext x
    rfl
  rw [hfun] at h
  apply h.congr_deriv
  rw [rphi]
  ring

/-- The excess of `coth` over its limit: `coth v − 1 = 2/(e^{2v} − 1)` for `v > 0`. -/
theorem rcoth_sub_one {v : ℝ} (hv : 0 < v) :
    rcoth v - 1 = 2 / (Real.exp (2 * v) - 1) := by
  have hs : 0 < Real.sinh v := sinh_pos_of_pos hv
  have hE : 0 < Real.exp v := Real.exp_pos v
  have h2 : Real.exp (2 * v) = Real.exp v * Real.exp v := by
    rw [← Real.exp_add]; ring_nf
  have hkey : Real.exp (2 * v) - 1 = 2 * Real.exp v * Real.sinh v := by
    rw [h2, Real.sinh_eq, Real.exp_neg]
    field_simp
  have hrc : rcoth v - 1 = (Real.cosh v - Real.sinh v) / Real.sinh v := by
    rw [rcoth]; field_simp
  have hcs : Real.cosh v - Real.sinh v = Real.exp (-v) := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  rw [hrc, hcs, hkey, Real.exp_neg]
  rw [div_eq_div_iff hs.ne' (by positivity)]
  field_simp

/-- `coth v < 1 + 1/v`: the exponential excess `2/(e^{2v} − 1)` is below `1/v` because
`2v + 1 < e^{2v}`. -/
theorem rcoth_lt_one_add_inv {v : ℝ} (hv : 0 < v) : rcoth v < 1 + 1 / v := by
  have h := Real.add_one_lt_exp (show 2 * v ≠ 0 by positivity)
  have hE1 : 0 < Real.exp (2 * v) - 1 := by linarith
  have heq := rcoth_sub_one hv
  have hlt : 2 / (Real.exp (2 * v) - 1) < 1 / v := by
    rw [div_lt_div_iff₀ hE1 hv]
    linarith
  linarith

/-- `1/v ≤ coth v`: the tangent-line comparison `sinh v ≤ v·cosh v` read as a ratio. -/
theorem inv_le_rcoth {v : ℝ} (hv : 0 < v) : 1 / v ≤ rcoth v := by
  have hs : 0 < Real.sinh v := sinh_pos_of_pos hv
  have h := sinh_le_mul_cosh hv.le
  rw [rcoth, div_le_div_iff₀ hv hs]
  linarith

end RHTower
