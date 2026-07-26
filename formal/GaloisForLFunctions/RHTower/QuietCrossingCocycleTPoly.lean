/-
Quiet-crossing rigidity for reflection cocycles with **polynomial height growth** on flanks.

`quiet_crossing_cocycle_bound` consumes a per-depth flank bound `‖h(s)‖ ≤ H(M)` that is uniform
in the height `Im s`.  Gamma-type reflection factors violate that uniformity: by Stirling their
modulus grows like `|Im s|^{(1−2σ)·d/2}` on the line `Re s = σ` — polynomially in height, with an
exponent that grows linearly with the contour depth.  This module extends the machine to the
sub-critical slice: flank bounds of the form

  `‖h(s)‖ ≤ H(M) · (2 + |Im s|)^m`   on `−M ≤ Re s ≤ 1−c`,  with a **fixed** exponent `m < 1`.

* `quiet_crossing_cocycle_bound_tpoly` — `‖aₙ‖ ≤ (12/π)·J(m)·H(M)·B·(n−½)^{1−M}`, where
  `J(m) = ∫ (1+y²)^{(m−2)/2} dy` is finite exactly for `m < 1`.
* `quiet_crossing_cocycle_support_tpoly` — `H(M) ≤ C·r^M` with `r ≥ 1` still forces `aₙ = 0` for
  every `n − ½ > r`: the support radius reads only the depth aspect of the flank growth; the
  height aspect is absorbed by the kernel as long as `m < 1`.
* `quiet_crossing_cocycle_kill_tpoly` — bounded depth aspect plus a zero of `h` still kills the
  carrier outright.

The threshold `m < 1` is structural, not technical: the Perron kernel `1/(s(s+1))` decays like
`|y|^{−2}` on vertical lines, so the left-edge integrand `|y|^m·|y|^{−2}` is integrable exactly
for `m < 1`.  A reflection factor of Selberg degree `d` has height exponent `≈ d·M` at depth `M`,
which exceeds every fixed `m` — the machine saturates exactly at the existence line of the
completed L-functions.  Within its slice it proves the dichotomy: sub-critical height growth
admits only conductor-type functional equations (finite support), and any divisor at all
(a zero of `h`) admits only the zero carrier.
-/
import Mathlib
import GaloisForLFunctions.RHTower.QuietCrossingRigidity
import GaloisForLFunctions.HTGeometry.PerronKernelBound

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set

noncomputable section

namespace RHTower

/-- The height-growth kernel constant: `J(m) = ∫ (1+y²)^{(m−2)/2} dy`, finite for `m < 1`. -/
def tpolyConst (m : ℝ) : ℝ := ∫ y : ℝ, (1 + y ^ 2) ^ ((m - 2) / 2)

private theorem qtp_integrable_J {m : ℝ} (hm1 : m < 1) :
    Integrable (fun y : ℝ => (1 + y ^ 2) ^ ((m - 2) / 2)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := MeasureTheory.volume)
    (r := 2 - m) (by rw [Module.finrank_self]; norm_num; linarith)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  show (1 + ‖y‖ ^ 2) ^ (-(2 - m) / 2) = (1 + y ^ 2) ^ ((m - 2) / 2)
  rw [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

theorem tpolyConst_nonneg (m : ℝ) : 0 ≤ tpolyConst m :=
  integral_nonneg fun y => Real.rpow_nonneg (by positivity) _

/-- Pointwise domination of the height-weighted left-edge kernel: for `M ≥ 2`, `0 ≤ m ≤ 1`,
`(2+|y|)^m · ((M−1)²+y²)⁻¹ ≤ 3·(1+y²)^{(m−2)/2}` — the polynomial height factor is absorbed at
the price of half a power of the quadratic, leaving an integrable exponent exactly when `m < 1`. -/
private theorem qtp_dominating {M m y : ℝ} (hM : 2 ≤ M) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    (2 + |y|) ^ m * ((M - 1) ^ 2 + y ^ 2)⁻¹ ≤ 3 * (1 + y ^ 2) ^ ((m - 2) / 2) := by
  have hy2 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hb : (0 : ℝ) ≤ 2 + |y| := by positivity
  have hsq : (2 + |y|) ^ (2 : ℕ) ≤ 8 * (1 + y ^ 2) := by
    nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y| - 2)]
  have h1 : (2 + |y|) ^ m ≤ 3 * (1 + y ^ 2) ^ (m / 2) := by
    have e1 : (2 + |y|) ^ m = ((2 + |y|) ^ (2 : ℕ)) ^ (m / 2) := by
      rw [← Real.rpow_natCast (2 + |y|) 2, ← Real.rpow_mul hb]
      congr 1
      push_cast
      ring
    have e2 : ((2 + |y|) ^ (2 : ℕ)) ^ (m / 2) ≤ (8 * (1 + y ^ 2)) ^ (m / 2) :=
      Real.rpow_le_rpow (by positivity) hsq (by linarith)
    have e3 : ((8 : ℝ) * (1 + y ^ 2)) ^ (m / 2) = 8 ^ (m / 2) * (1 + y ^ 2) ^ (m / 2) :=
      Real.mul_rpow (by norm_num) hy2.le
    have e4 : (8 : ℝ) ^ (m / 2) ≤ 3 := by
      have h8 : (8 : ℝ) ^ (m / 2) * (8 : ℝ) ^ (m / 2) = 8 ^ m := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 8)]
        congr 1
        ring
      have h8m : (8 : ℝ) ^ m ≤ 8 := by
        calc (8 : ℝ) ^ m ≤ 8 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hm1
          _ = 8 := Real.rpow_one 8
      nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 8) (m / 2)]
    calc (2 + |y|) ^ m = ((2 + |y|) ^ (2 : ℕ)) ^ (m / 2) := e1
      _ ≤ (8 * (1 + y ^ 2)) ^ (m / 2) := e2
      _ = 8 ^ (m / 2) * (1 + y ^ 2) ^ (m / 2) := e3
      _ ≤ 3 * (1 + y ^ 2) ^ (m / 2) :=
          mul_le_mul_of_nonneg_right e4 (Real.rpow_nonneg hy2.le _)
  have h2 : ((M - 1) ^ 2 + y ^ 2)⁻¹ ≤ (1 + y ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ M) (by linarith : (0 : ℝ) ≤ M - 2)]
  calc (2 + |y|) ^ m * ((M - 1) ^ 2 + y ^ 2)⁻¹
      ≤ (3 * (1 + y ^ 2) ^ (m / 2)) * (1 + y ^ 2)⁻¹ :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 3 * (1 + y ^ 2) ^ ((m - 2) / 2) := by
        rw [← Real.rpow_neg_one (1 + y ^ 2), mul_assoc, ← Real.rpow_add hy2,
          show m / 2 + (-1 : ℝ) = (m - 2) / 2 by ring]

/-- **Quiet-crossing coefficient bound with polynomial height growth on flanks.**  As
`quiet_crossing_cocycle_bound`, but the reflection factor may grow polynomially in the height on
the flank region, `‖h(s)‖ ≤ H(M)·(2+|Im s|)^m`, with a fixed exponent `m < 1`.  The height factor
is absorbed by the Perron kernel: the left edge pays the finite constant `J(m)`, and the
horizontal edges still vanish since `(2+T)^m/T² → 0`.  The coefficient bound becomes

  `‖aₙ‖ ≤ (12/π)·J(m)·H(M)·B·(n−½)^{1−M}`. -/
theorem quiet_crossing_cocycle_bound_tpoly {F h : ℂ → ℂ} {a : ℕ → ℂ} {c B m : ℝ} {H : ℕ → ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hm0 : 0 ≤ m) (hm1 : m < 1)
    (hF : Differentiable ℂ F)
    (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hB : ∀ s : ℂ, c ≤ s.re → ‖F s‖ ≤ B)
    (hFE : ∀ s : ℂ, F s = h s * F (1 - s))
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ), Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ k, 0 < T k) ∧ Filter.Tendsto (fun k => q k / (T k) ^ 2) Filter.atTop (nhds 0) ∧
      ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
        ‖F (σ + (T k) * Complex.I)‖ ≤ q k ∧ ‖F (σ - (T k) * Complex.I)‖ ≤ q k)
    {M : ℕ} (hM2 : 2 ≤ M) (hMc : (c : ℝ) ≤ (M : ℝ))
    (hgrow : ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c → ‖h s‖ ≤ H M * (2 + |s.im|) ^ m)
    {n : ℕ} (hn2 : 2 ≤ n) :
    ‖a n‖ ≤ 12 / Real.pi * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨T, q, hTtop, hTpos, hqlim, hquietbd⟩ := hquiet
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB ↑c (by rw [Complex.ofReal_re]))
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hM1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
  have hM2R : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hMle : -(M : ℝ) ≤ 1 - c := by linarith
  have hMcle : -(M : ℝ) ≤ c := by linarith
  have hH0 : (0 : ℝ) ≤ H M := by
    have h1 : -(M : ℝ) ≤ ((1 - c : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith
    have h2 : ((1 - c : ℝ) : ℂ).re ≤ 1 - c := by rw [Complex.ofReal_re]
    have h3 := le_trans (norm_nonneg (h ((1 - c : ℝ) : ℂ))) (hgrow _ h1 h2)
    nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 + |(((1 - c : ℝ) : ℂ)).im|) m,
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
        (by simp [Complex.ofReal_im] : (1 : ℝ) ≤ 2 + |(((1 - c : ℝ) : ℂ)).im|) hm0,
      Real.rpow_natCast (1 : ℝ) 0, Real.one_rpow m]
  -- flank bound through the functional equation, with the height factor
  have hFleft : ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c →
      ‖F s‖ ≤ H M * (2 + |s.im|) ^ m * B := by
    intro s hs1 hs2
    have hre1s : c ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    rw [hFE s, norm_mul]
    exact mul_le_mul (hgrow s hs1 hs2) (hB _ hre1s) (norm_nonneg _)
      (mul_nonneg hH0 (Real.rpow_nonneg (by positivity) _))
  have hEdiff : Differentiable ℂ (perronE n) := perronE_differentiable hn1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hxppos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hxmpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hxm1 : (1 : ℝ) ≤ (n : ℝ) - 1 / 2 := by linarith
  have hbase1p : (1 : ℝ) ≤ (n : ℝ) + 1 / 2 := by linarith
  set Hf : ℂ → ℂ := fun s => F s * perronE n s with hHf
  have hHfp : ∀ p : ℂ, Hf p = F p * perronE n p := fun p => by rw [hHf]
  have hHfdiff : Differentiable ℂ Hf := by rw [hHf]; exact hF.mul hEdiff
  have hHfcont : Continuous Hf := hHfdiff.continuous
  have hKink_c : ∀ p : ℂ, p.re ≤ c → ‖perronKink n p‖ ≤ 4 * ((n : ℝ) + 1 / 2) ^ (c + 1) := by
    intro p hpc
    have hb := perronKink_norm_le hn1 p
    have hc1 : (0 : ℝ) ≤ c + 1 := by linarith
    have hpc1 : p.re + 1 ≤ c + 1 := by linarith
    have t1 : ((n : ℝ) + 1 / 2) ^ (p.re + 1) ≤ ((n : ℝ) + 1 / 2) ^ (c + 1) :=
      Real.rpow_le_rpow_of_exponent_le hbase1p hpc1
    have t2 : ((n : ℝ) - 1 / 2) ^ (p.re + 1) ≤ ((n : ℝ) + 1 / 2) ^ (c + 1) :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hxm1 hpc1)
        (Real.rpow_le_rpow hxmpos.le (by linarith) hc1)
    have t3 : ((n : ℝ)) ^ (p.re + 1) ≤ ((n : ℝ) + 1 / 2) ^ (c + 1) :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hnR hpc1)
        (Real.rpow_le_rpow (by linarith) (by linarith) hc1)
    linarith [hb, t1, t2, t3]
  have hKink_M : ∀ p : ℂ, p.re = -(M : ℝ) →
      ‖perronKink n p‖ ≤ 4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    intro p hpre
    have hb := perronKink_norm_le hn1 p
    rw [hpre, show (-(M : ℝ) + 1) = 1 - (M : ℝ) by ring] at hb
    have hnp : (1 - (M : ℝ)) ≤ 0 := by linarith
    have t1 : ((n : ℝ) + 1 / 2) ^ (1 - (M : ℝ)) ≤ ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hxmpos (by linarith) hnp
    have t3 : ((n : ℝ)) ^ (1 - (M : ℝ)) ≤ ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hxmpos (by linarith) hnp
    linarith [hb, t1, t3]
  have hRint : Integrable (fun t : ℝ => Hf (↑c + ↑t * I)) := by
    have hcont : Continuous (fun t : ℝ => Hf (↑c + ↑t * I)) := hHfcont.comp (by fun_prop)
    have hbd : ∀ t : ℝ, ‖Hf (↑c + ↑t * I)‖
        ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * B) * (c ^ 2 + t ^ 2)⁻¹ := by
      intro t
      have hre : (↑c + ↑t * I : ℂ).re = c := by simp
      rw [hHfp, norm_mul]
      have hF' : ‖F (↑c + ↑t * I)‖ ≤ B := hB _ (le_of_eq hre.symm)
      have h0 : (↑c + ↑t * I : ℂ) ≠ 0 := by
        intro hh; have := congrArg Complex.re hh; rw [hre] at this; simp at this; linarith
      have h1 : (↑c + ↑t * I : ℂ) ≠ -1 := by
        intro hh; have := congrArg Complex.re hh; rw [hre] at this; simp at this; linarith
      have hE' : ‖perronE n (↑c + ↑t * I)‖
          ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹ := by
        rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
        exact mul_le_mul (hKink_c _ (le_of_eq hre)) (HTGeometry.norm_inv_mul_add_one_le_of_re_pos hc0 t) (norm_nonneg _)
          (by positivity)
      calc ‖F (↑c + ↑t * I)‖ * ‖perronE n (↑c + ↑t * I)‖
          ≤ B * ((4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * (c ^ 2 + t ^ 2)⁻¹) :=
            mul_le_mul hF' hE' (norm_nonneg _) hB0
        _ = (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * B) * (c ^ 2 + t ^ 2)⁻¹ := by ring
    exact ((HTGeometry.integrable_inv_sq_add_sq hc0).const_mul _).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hbd)
  -- left edge: the height factor is absorbed by the dominating kernel
  have hleftbd : ∀ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
      ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * (H M * B) * 3) * (1 + y ^ 2) ^ ((m - 2) / 2) := by
    intro y
    have hre : (↑(-(M : ℝ)) + ↑y * I : ℂ).re = -(M : ℝ) := by simp
    have him : (↑(-(M : ℝ)) + ↑y * I : ℂ).im = y := by simp
    rw [hHfp, norm_mul]
    have hF' : ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ≤ H M * (2 + |y|) ^ m * B := by
      have := hFleft _ (by rw [hre]) (by rw [hre]; exact hMle)
      rwa [him] at this
    have h0 : (↑(-(M : ℝ)) + ↑y * I : ℂ) ≠ 0 := by
      intro hh; have := congrArg Complex.re hh; rw [hre] at this; simp at this; linarith
    have h1 : (↑(-(M : ℝ)) + ↑y * I : ℂ) ≠ -1 := by
      intro hh; have := congrArg Complex.re hh; rw [hre] at this; simp at this; linarith
    have hE' : ‖perronE n (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
      rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
      exact mul_le_mul (hKink_M _ hre)
        (HTGeometry.norm_inv_mul_add_one_le_of_re_neg (M := (M : ℝ)) (y := y) hM1) (norm_nonneg _)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hxmpos.le _))
    calc ‖F (↑(-(M : ℝ)) + ↑y * I)‖ * ‖perronE n (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ (H M * (2 + |y|) ^ m * B) *
            ((4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹) :=
          mul_le_mul hF' hE' (norm_nonneg _)
            (mul_nonneg (mul_nonneg hH0 (Real.rpow_nonneg (by positivity) _)) hB0)
      _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * (H M * B)) *
            ((2 + |y|) ^ m * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹) := by ring
      _ ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * (H M * B)) *
            (3 * (1 + y ^ 2) ^ ((m - 2) / 2)) := by
          refine mul_le_mul_of_nonneg_left (qtp_dominating hM2R hm0 hm1.le) ?_
          exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hxmpos.le _))
            (mul_nonneg hH0 hB0)
      _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * (H M * B) * 3) *
            (1 + y ^ 2) ^ ((m - 2) / 2) := by ring
  have hleftint : Integrable (fun y : ℝ => Hf (↑(-(M : ℝ)) + ↑y * I)) := by
    have hcont : Continuous (fun y : ℝ => Hf (↑(-(M : ℝ)) + ↑y * I)) :=
      hHfcont.comp (by fun_prop)
    exact ((qtp_integrable_J hm1).const_mul
      (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * (H M * B) * 3)).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall hleftbd)
  have hleftfull : ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
      ≤ 12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    have hdomint : Integrable (fun y : ℝ =>
        (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * (H M * B) * 3) *
          (1 + y ^ 2) ^ ((m - 2) / 2)) := (qtp_integrable_J hm1).const_mul _
    calc ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ ∫ y : ℝ, (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * (H M * B) * 3) *
            (1 + y ^ 2) ^ ((m - 2) / 2) :=
          integral_mono hleftint.norm hdomint hleftbd
      _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * (H M * B) * 3) * tpolyConst m := by
          rw [MeasureTheory.integral_const_mul]; rfl
      _ = 12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by ring
  have hleftk : ∀ k, ‖∫ y in (-(T k))..(T k), Hf (↑(-(M : ℝ)) + ↑y * I)‖
      ≤ 12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    intro k
    calc ‖∫ y in (-(T k))..(T k), Hf (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ ∫ y in (-(T k))..(T k), ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith [hTpos k])
      _ = ∫ y in Set.Ioc (-(T k)) (T k), ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖ :=
          intervalIntegral.integral_of_le (by linarith [hTpos k])
      _ ≤ ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖ :=
          setIntegral_le_integral hleftint.norm (Eventually.of_forall (fun y => norm_nonneg _))
      _ ≤ 12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := hleftfull
  -- horizontal edges: the height factor `(2+T_k)^m` dies against `T_k^{-2}`
  have hpolyT : Tendsto (fun k => (2 + T k) ^ m * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
    have hneg : Tendsto (fun x : ℝ => x ^ (m - 2)) atTop (nhds 0) := by
      have := tendsto_rpow_neg_atTop (y := 2 - m) (by linarith)
      simpa [show -(2 - m) = m - 2 by ring] using this
    have h32 : Tendsto (fun k => (3 : ℝ) ^ m * (T k) ^ (m - 2)) atTop (nhds 0) := by
      simpa using ((hneg.comp hTtop).const_mul ((3 : ℝ) ^ m))
    refine squeeze_zero' ?_ ?_ h32
    · filter_upwards with k
      have hTk := hTpos k
      positivity
    · filter_upwards [hTtop.eventually_ge_atTop 1] with k hk
      have hTpos' : (0 : ℝ) < T k := hTpos k
      have hb : (2 + T k) ^ m ≤ ((3 : ℝ) * T k) ^ m :=
        Real.rpow_le_rpow (by positivity) (by linarith) hm0
      have he : ((3 : ℝ) * T k) ^ m = 3 ^ m * (T k) ^ m :=
        Real.mul_rpow (by norm_num) hTpos'.le
      calc (2 + T k) ^ m * ((T k) ^ 2)⁻¹
          ≤ (3 ^ m * (T k) ^ m) * ((T k) ^ 2)⁻¹ := by
            rw [← he]; exact mul_le_mul_of_nonneg_right hb (by positivity)
        _ = 3 ^ m * (T k) ^ (m - 2) := by
            have h2 : (T k) ^ ((2 : ℝ)) = (T k) ^ (2 : ℕ) := by
              rw [← Real.rpow_natCast (T k) 2]
              norm_num
            rw [Real.rpow_sub hTpos', h2, div_eq_mul_inv]
            ring
  have hcore : Tendsto
      (fun k => (H M * (2 + T k) ^ m * B + q k) * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
    have h1 : Tendsto (fun k => H M * B * ((2 + T k) ^ m * ((T k) ^ 2)⁻¹)) atTop (nhds 0) := by
      simpa using hpolyT.const_mul (H M * B)
    have h2 : Tendsto (fun k => q k * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
      have := hqlim; simp_rw [div_eq_mul_inv] at this; exact this
    have heq : (fun k => (H M * (2 + T k) ^ m * B + q k) * ((T k) ^ 2)⁻¹)
        = fun k => H M * B * ((2 + T k) ^ m * ((T k) ^ 2)⁻¹) + q k * ((T k) ^ 2)⁻¹ := by
      funext k; ring
    rw [heq]
    simpa using h1.add h2
  set d : ℕ → ℝ := fun k =>
    (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * (c + (M : ℝ))) *
      ((H M * (2 + T k) ^ m * B + q k) * ((T k) ^ 2)⁻¹) with hd
  have hd0 : Tendsto d atTop (nhds 0) := by
    simp only [hd]
    simpa using hcore.const_mul (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * (c + (M : ℝ)))
  have hqk0 : ∀ k, (0 : ℝ) ≤ q k := fun k =>
    le_trans (norm_nonneg _) (hquietbd k c (by linarith) (le_refl c)).1
  have hHT0 : ∀ k, (0 : ℝ) ≤ H M * (2 + T k) ^ m * B := fun k => by
    have hTk := hTpos k
    exact mul_nonneg (mul_nonneg hH0 (Real.rpow_nonneg (by linarith) _)) hB0
  have hedge : ∀ (k : ℕ) (t : ℝ), 0 < T k → |t| = T k →
      ∀ x : ℝ, -(M : ℝ) < x → x ≤ c →
      ‖F (↑x + ↑t * I)‖ ≤ H M * (2 + T k) ^ m * B + q k →
      ‖Hf (↑x + ↑t * I)‖ ≤ (H M * (2 + T k) ^ m * B + q k)
        * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) := by
    intro k t hTk habs x hx1 hx2 hFbd
    have hre : (↑x + ↑t * I : ℂ).re = x := by simp
    rw [hHfp, norm_mul]
    have h0 : (↑x + ↑t * I : ℂ) ≠ 0 := by
      intro hh; have := congrArg Complex.im hh; simp at this; rw [this] at habs
      simp at habs; linarith
    have h1 : (↑x + ↑t * I : ℂ) ≠ -1 := by
      intro hh; have := congrArg Complex.im hh; simp at this; rw [this] at habs
      simp at habs; linarith
    have hE' : ‖perronE n (↑x + ↑t * I)‖
        ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * ((T k) ^ 2)⁻¹ := by
      rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
      exact mul_le_mul (hKink_c _ ((le_of_eq hre).trans hx2))
        (HTGeometry.norm_inv_mul_add_one_le_of_line (t := t) (T := T k) hTk (le_of_eq habs.symm) x) (norm_nonneg _)
        (by positivity)
    calc ‖F (↑x + ↑t * I)‖ * ‖perronE n (↑x + ↑t * I)‖
        ≤ (H M * (2 + T k) ^ m * B + q k)
            * ((4 * ((n : ℝ) + 1 / 2) ^ (c + 1)) * ((T k) ^ 2)⁻¹) :=
          mul_le_mul hFbd hE' (norm_nonneg _) (by linarith [hHT0 k, hqk0 k])
      _ = (H M * (2 + T k) ^ m * B + q k)
            * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) := by ring
  have htop : ∀ k, ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(T k) * I)‖ ≤ d k := by
    intro k
    have hconst : ∀ x ∈ Set.uIoc (-(M : ℝ)) c,
        ‖Hf (↑x + ↑(T k) * I)‖ ≤ (H M * (2 + T k) ^ m * B + q k)
          * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) := by
      intro x hx
      rw [Set.uIoc_of_le hMcle] at hx
      obtain ⟨hx1, hx2⟩ := hx
      refine hedge k (T k) (hTpos k) (abs_of_pos (hTpos k)) x hx1 hx2 ?_
      rcases le_or_gt x (1 - c) with hcase | hcase
      · have hbd := hFleft (↑x + ↑(T k) * I) (by simpa using hx1.le) (by simpa using hcase)
        have him : ((↑x + ↑(T k) * I : ℂ)).im = T k := by simp
        rw [him, abs_of_pos (hTpos k)] at hbd
        exact le_trans hbd (by linarith [hqk0 k])
      · exact le_trans (hquietbd k x (le_of_lt hcase) hx2).1 (by linarith [hHT0 k])
    calc ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(T k) * I)‖
        ≤ ((H M * (2 + T k) ^ m * B + q k)
            * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹)) * |c - -(M : ℝ)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hconst
      _ = d k := by simp only [hd]; rw [abs_of_nonneg (by linarith)]; ring
  have hbot : ∀ k, ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(-(T k)) * I)‖ ≤ d k := by
    intro k
    have hconst : ∀ x ∈ Set.uIoc (-(M : ℝ)) c,
        ‖Hf (↑x + ↑(-(T k)) * I)‖ ≤ (H M * (2 + T k) ^ m * B + q k)
          * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) := by
      intro x hx
      rw [Set.uIoc_of_le hMcle] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hpt : (↑x + ↑(-(T k)) * I : ℂ) = ↑x - ↑(T k) * I := by push_cast; ring
      refine hedge k (-(T k)) (hTpos k) (by rw [abs_neg, abs_of_pos (hTpos k)]) x hx1 hx2 ?_
      rcases le_or_gt x (1 - c) with hcase | hcase
      · have hbd := hFleft (↑x + ↑(-(T k)) * I) (by simpa using hx1.le) (by simpa using hcase)
        have him : ((↑x + ↑(-(T k)) * I : ℂ)).im = -(T k) := by simp
        rw [him, abs_neg, abs_of_pos (hTpos k)] at hbd
        exact le_trans hbd (by linarith [hqk0 k])
      · rw [hpt]
        exact le_trans (hquietbd k x (le_of_lt hcase) hx2).2 (by linarith [hHT0 k])
    calc ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(-(T k)) * I)‖
        ≤ ((H M * (2 + T k) ^ m * B + q k)
            * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹)) * |c - -(M : ℝ)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hconst
      _ = d k := by simp only [hd]; rw [abs_of_nonneg (by linarith)]; ring
  -- rectangle bound and passage to the limit
  have hrighttendsto : Tendsto (fun k => ∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)) atTop
      (nhds (∫ t : ℝ, Hf (↑c + ↑t * I))) :=
    intervalIntegral_tendsto_integral hRint (tendsto_neg_atBot_iff.mpr hTtop) hTtop
  have hnormtendsto : Tendsto (fun k => ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖) atTop
      (nhds ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖) := hrighttendsto.norm
  have hrectbd : ∀ k, ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖
      ≤ (d k + d k) + 12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    intro k
    set z : ℂ := ⟨-(M : ℝ), -(T k)⟩ with hz
    set w : ℂ := ⟨c, T k⟩ with hw
    have hrect := integral_boundary_rect_eq_zero_of_differentiableOn Hf z w
      hHfdiff.differentiableOn
    have hzre : z.re = -(M : ℝ) := rfl
    have hzim : z.im = -(T k) := rfl
    have hwre : w.re = c := rfl
    have hwim : w.im = T k := rfl
    rw [hzre, hzim, hwre, hwim] at hrect
    simp only [smul_eq_mul] at hrect
    set Itop := ∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(T k) * I) with hItop
    set Ibot := ∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(-(T k)) * I) with hIbot
    set Ilft := ∫ y in (-(T k))..(T k), Hf (↑(-(M : ℝ)) + ↑y * I) with hIlft
    have heqI : I * (∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)) = Itop - Ibot + I * Ilft := by
      linear_combination hrect
    have hInorm : ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖ = ‖Itop - Ibot + I * Ilft‖ := by
      rw [← heqI, norm_mul, Complex.norm_I, one_mul]
    rw [hInorm]
    have hb1 : ‖Itop - Ibot + I * Ilft‖ ≤ ‖Itop - Ibot‖ + ‖I * Ilft‖ := norm_add_le _ _
    have hb2 : ‖Itop - Ibot‖ ≤ ‖Itop‖ + ‖Ibot‖ := norm_sub_le _ _
    have hb3 : ‖I * Ilft‖ = ‖Ilft‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [hb3] at hb1
    linarith [hb1, hb2, htop k, hbot k, hleftk k]
  have hdb : Tendsto (fun k => (d k + d k)
      + 12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) atTop
      (nhds (12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))) := by
    simpa using (hd0.add hd0).add_const
      (12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
  have hfin := le_of_tendsto_of_tendsto' hnormtendsto hdb hrectbd
  -- read the coefficient from the right-line integral
  have hR : a n * (1 / 2) = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, Hf (↑c + ↑t * I) := by
    rw [hHf]; exact perronSecondDiff_integral hc0 hsum hF hFeq hn1
  have hnorm_an : ‖a n‖ * (1 / 2) ≤ (1 / (2 * Real.pi)) *
      (12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) := by
    have h1 : ‖a n * (1 / 2 : ℂ)‖ = ‖a n‖ * (1 / 2) := by
      rw [norm_mul]
      norm_num
    calc ‖a n‖ * (1 / 2) = ‖a n * (1 / 2 : ℂ)‖ := h1.symm
      _ = ‖(1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, Hf (↑c + ↑t * I)‖ := by rw [hR]
      _ = (1 / (2 * Real.pi)) * ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (1 / (2 * Real.pi)) *
          (12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) :=
          mul_le_mul_of_nonneg_left hfin (by positivity)
  have hpi : (1 / (2 * Real.pi)) *
      (12 * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
      = (12 / Real.pi * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (1 / 2) := by
    field_simp
  rw [hpi] at hnorm_an
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  exact le_of_mul_le_mul_right (by linarith [hnorm_an]) hhalf

/-- **Support radius with polynomial height growth.**  If the depth aspect of the flank bounds is
exponential, `H(M) ≤ C·r^M` with `r ≥ 1`, and the height exponent is sub-critical (`m < 1`), then
every coefficient with `n − ½ > r` vanishes.  The support radius reads only the depth aspect. -/
theorem quiet_crossing_cocycle_support_tpoly {F h : ℂ → ℂ} {a : ℕ → ℂ} {c B m : ℝ} {H : ℕ → ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hm0 : 0 ≤ m) (hm1 : m < 1)
    (hF : Differentiable ℂ F)
    (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hB : ∀ s : ℂ, c ≤ s.re → ‖F s‖ ≤ B)
    (hFE : ∀ s : ℂ, F s = h s * F (1 - s))
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ), Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ k, 0 < T k) ∧ Filter.Tendsto (fun k => q k / (T k) ^ 2) Filter.atTop (nhds 0) ∧
      ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
        ‖F (σ + (T k) * Complex.I)‖ ≤ q k ∧ ‖F (σ - (T k) * Complex.I)‖ ≤ q k)
    (hgrow : ∀ M : ℕ, 2 ≤ M → ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c →
      ‖h s‖ ≤ H M * (2 + |s.im|) ^ m)
    {C r : ℝ} (hr1 : 1 ≤ r) (hHle : ∀ M : ℕ, H M ≤ C * r ^ M) :
    ∀ n : ℕ, r < (n : ℝ) - 1 / 2 → a n = 0 := by
  intro n hnr
  have hn2 : 2 ≤ n := by
    by_contra hcon
    push Not at hcon
    have hn1 : (n : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hcon
    linarith
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hxmpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  set ρ : ℝ := r * ((n : ℝ) - 1 / 2)⁻¹ with hρ
  have hρ_nn : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ_lt1 : ρ < 1 := by
    rw [hρ, ← div_eq_mul_inv, div_lt_one hxmpos]
    exact hnr
  have hbd : ∀ᶠ M : ℕ in atTop, ‖a n‖
      ≤ (12 / Real.pi * tpolyConst m * C * B * ((n : ℝ) - 1 / 2)) * ρ ^ M := by
    filter_upwards [eventually_ge_atTop (max 2 ⌈c⌉₊)] with M hM
    have hM2 : 2 ≤ M := le_trans (le_max_left _ _) hM
    have hMc : (c : ℝ) ≤ (M : ℝ) :=
      le_trans (Nat.le_ceil c) (by exact_mod_cast le_trans (le_max_right _ _) hM)
    have hkey := quiet_crossing_cocycle_bound_tpoly hc hc0 hm0 hm1 hF hsum hFeq hB hFE hquiet
      hM2 hMc (hgrow M hM2) hn2
    have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB ↑c (by rw [Complex.ofReal_re]))
    have hJ0 : (0 : ℝ) ≤ 12 / Real.pi * tpolyConst m :=
      mul_nonneg (by positivity) (tpolyConst_nonneg m)
    have hsplit : ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))
        = ((n : ℝ) - 1 / 2) * (((n : ℝ) - 1 / 2) ^ M)⁻¹ := by
      rw [Real.rpow_sub hxmpos, Real.rpow_one,
        show ((n : ℝ) - 1 / 2) ^ ((M : ℝ)) = ((n : ℝ) - 1 / 2) ^ (M : ℕ) from
          Real.rpow_natCast _ M]
      ring
    calc ‖a n‖ ≤ 12 / Real.pi * tpolyConst m * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) :=
          hkey
      _ ≤ 12 / Real.pi * tpolyConst m * ((C * r ^ M) * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hxmpos.le _)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hHle M) hB0) hJ0
      _ = (12 / Real.pi * tpolyConst m * C * B * ((n : ℝ) - 1 / 2))
            * (r ^ M * (((n : ℝ) - 1 / 2) ^ M)⁻¹) := by
          rw [hsplit]; ring
      _ = (12 / Real.pi * tpolyConst m * C * B * ((n : ℝ) - 1 / 2)) * ρ ^ M := by
          rw [hρ, mul_pow, inv_pow]
  have hlim : Tendsto (fun M : ℕ =>
      (12 / Real.pi * tpolyConst m * C * B * ((n : ℝ) - 1 / 2)) * ρ ^ M) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ_nn hρ_lt1).const_mul
      (12 / Real.pi * tpolyConst m * C * B * ((n : ℝ) - 1 / 2))
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim hbd) (norm_nonneg _))

/-- **Bounded depth aspect plus a zero still kills the carrier.**  With sub-critical height
growth (`m < 1`) and uniformly bounded depth constants `H(M) ≤ C`, a zero of the reflection
factor annihilates every coefficient: the support collapses to the constant `a₁`, the identity
principle spreads it, and the functional equation at the zero evaluates it to `0`. -/
theorem quiet_crossing_cocycle_kill_tpoly {F h : ℂ → ℂ} {a : ℕ → ℂ} {c B m : ℝ} {H : ℕ → ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hm0 : 0 ≤ m) (hm1 : m < 1)
    (hF : Differentiable ℂ F)
    (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hB : ∀ s : ℂ, c ≤ s.re → ‖F s‖ ≤ B)
    (hFE : ∀ s : ℂ, F s = h s * F (1 - s))
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ), Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ k, 0 < T k) ∧ Filter.Tendsto (fun k => q k / (T k) ^ 2) Filter.atTop (nhds 0) ∧
      ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
        ‖F (σ + (T k) * Complex.I)‖ ≤ q k ∧ ‖F (σ - (T k) * Complex.I)‖ ≤ q k)
    (hgrow : ∀ M : ℕ, 2 ≤ M → ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c →
      ‖h s‖ ≤ H M * (2 + |s.im|) ^ m)
    {C : ℝ} (hHle : ∀ M : ℕ, H M ≤ C)
    {ρ₀ : ℂ} (hzero : h ρ₀ = 0) :
    ∀ n : ℕ, 1 ≤ n → a n = 0 := by
  have hsupp : ∀ n : ℕ, (1 : ℝ) < (n : ℝ) - 1 / 2 → a n = 0 :=
    quiet_crossing_cocycle_support_tpoly hc hc0 hm0 hm1 hF hsum hFeq hB hFE hquiet hgrow
      (C := C) (r := 1) le_rfl (fun M => by simpa using hHle M)
  have hsupp' : ∀ n : ℕ, 2 ≤ n → a n = 0 := by
    intro n hn
    refine hsupp n ?_
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hLconst : ∀ s : ℂ, c ≤ s.re → LSeries a s = a 1 := by
    intro s _
    have hterms : ∀ mm : ℕ, mm ≠ 1 → LSeries.term a s mm = 0 := by
      intro mm hmm
      rcases eq_or_ne mm 0 with rfl | hmm0
      · exact LSeries.term_zero a s
      · rw [LSeries.term_of_ne_zero hmm0, hsupp' mm (by omega), zero_div]
    rw [LSeries, tsum_eq_single 1 hterms, LSeries.term_of_ne_zero one_ne_zero,
      Nat.cast_one, Complex.one_cpow, div_one]
  have hFconst : ∀ s : ℂ, F s = a 1 := by
    have h1 : AnalyticOnNhd ℂ F Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
    have h2 : AnalyticOnNhd ℂ (fun _ : ℂ => a 1) (Set.univ : Set ℂ) := analyticOnNhd_const
    have hopen : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : F =ᶠ[nhds ((c + 1 : ℝ) : ℂ)] fun _ => a 1 := by
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds ?_) fun s hs => ?_
      · simp only [Set.mem_setOf_eq, Complex.ofReal_re]; linarith
      · exact (hFeq s (le_of_lt hs)).trans (hLconst s (le_of_lt hs))
    have heq := h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_univ
      (Set.mem_univ ((c + 1 : ℝ) : ℂ)) hev
    exact fun s => heq (Set.mem_univ s)
  intro n hn
  rcases eq_or_ne n 1 with rfl | hn1
  · have hkill := hFE ρ₀
    rw [hFconst ρ₀, hFconst (1 - ρ₀), hzero, zero_mul] at hkill
    exact hkill
  · exact hsupp' n (by omega)

end RHTower
