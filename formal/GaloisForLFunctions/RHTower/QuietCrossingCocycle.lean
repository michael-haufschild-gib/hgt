/-
Quiet-crossing rigidity with an **abstract reflection cocycle** in place of a conductor datum.

`quiet_crossing_conductor_support` treats functional equations whose reflection factor is a finite
Dirichlet polynomial in the conductors; the factor enters its proof only through its uniform size
`CJ·Q₀^{1+2M}` on the shifted flank `−M ≤ Re s ≤ 1−c`.  This module abstracts that single input:
the carrier satisfies `F(s) = h(s)·F(1−s)` for an arbitrary reflection factor `h`, and the only
datum consumed is a per-depth flank bound `‖h(s)‖ ≤ H(M)` on `−M ≤ Re s ≤ 1−c`.

* `quiet_crossing_cocycle_bound` — the quantitative kernel: at contour depth `M`,
  `‖aₙ‖ ≤ 4·H(M)·B·(n−½)^{1−M}` for every `n ≥ 2`.
* `quiet_crossing_cocycle_support` — the support-radius reading: if `H(M) ≤ C·r^M` with `r ≥ 1`,
  then `aₙ = 0` for every `n` with `n − ½ > r`.  **The support radius of a quiet carrier is
  bounded by the exponential growth rate of its reflection factor on left flanks.**

The two readings frame the dichotomy of realizable functional equations.  A conductor datum has
`H(M) = CJ·Q₀^{1+2M} ≤ (CJ·Q₀)·(Q₀²)^M`: support radius `Q₀²`, recovering the conductor theorem.
A Gamma-type factor has `H(M) ≈ e^{c·M·log M}`, faster than every `r^M`: no support bound — which
is exactly what permits a completed L-function to carry infinitely many coefficients.  A reflection
factor of subexponential-beyond-conductor flank growth therefore forces a quiet carrier to be a
Dirichlet polynomial: non-conductor reflection factors must grow at Gamma scale on left flanks.

The proof is the smoothed-Perron rectangle of `quiet_crossing_rigidity`: the entire integrand
`F·E` (with `E = perronKink/(s(s+1))`) is shifted from `Re s = c` to `Re s = −M`; the horizontal
edges die against the kernel's `T_k^{−2}` along the quiet heights, and the left edge contributes
`≤ 4π·H(M)·B·(n−½)^{1−M}` through the flank bound carried across the functional equation.
-/
import Mathlib
import GaloisForLFunctions.RHTower.QuietCrossingRigidity
import GaloisForLFunctions.HTGeometry.PerronKernelBound

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set

noncomputable section

namespace RHTower

/-- **Quiet-crossing coefficient bound with an abstract reflection cocycle.**  Let `F` be entire,
agree with an absolutely convergent Dirichlet series on `Re s ≥ c` (`½ ≤ c`), be bounded by `B`
there, and satisfy `F(s) = h(s)·F(1−s)`.  Along a quiet height sequence, at any contour depth
`M ≥ max(2, c)` where the reflection factor obeys the flank bound `‖h(s)‖ ≤ H(M)` on
`−M ≤ Re s ≤ 1−c`, every coefficient with `n ≥ 2` satisfies

  `‖aₙ‖ ≤ 4·H(M)·B·(n−½)^{1−M}`.

The functional equation transports the right-flank bound `B` across the strip at the price of the
factor `H(M)`; the smoothed-Perron rectangle then reads the coefficient on the deep line
`Re s = −M`, where the kink numerator contributes `(n−½)^{1−M}`. -/
theorem quiet_crossing_cocycle_bound {F h : ℂ → ℂ} {a : ℕ → ℂ} {c B : ℝ} {H : ℕ → ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
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
    (hgrow : ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c → ‖h s‖ ≤ H M)
    {n : ℕ} (hn2 : 2 ≤ n) :
    ‖a n‖ ≤ 4 * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
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
    exact le_trans (norm_nonneg _) (hgrow _ h1 h2)
  -- Amplified left-flank bound through the functional equation.
  set Bf : ℝ := H M * B with hBf
  have hBf0 : (0 : ℝ) ≤ Bf := mul_nonneg hH0 hB0
  have hFleftM : ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c → ‖F s‖ ≤ Bf := by
    intro s hs1 hs2
    have hre1s : c ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    rw [hFE s, norm_mul, hBf]
    exact mul_le_mul (hgrow s hs1 hs2) (hB _ hre1s) (norm_nonneg _) hH0
  have hEdiff : Differentiable ℂ (perronE n) := perronE_differentiable hn1
  -- Real facts about the knots.
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hxppos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hxmpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hxm1 : (1 : ℝ) ≤ (n : ℝ) - 1 / 2 := by linarith
  have hbase1p : (1 : ℝ) ≤ (n : ℝ) + 1 / 2 := by linarith
  -- The entire integrand.
  set Hf : ℂ → ℂ := fun s => F s * perronE n s with hHf
  have hHfp : ∀ p : ℂ, Hf p = F p * perronE n p := fun p => by rw [hHf]
  have hHfdiff : Differentiable ℂ Hf := by rw [hHf]; exact hF.mul hEdiff
  have hHfcont : Continuous Hf := hHfdiff.continuous
  -- Kink bounds on `Re s ≤ c` and on `Re s = −M`.
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
  -- Right-line integrability.
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
  -- Left-line domination and integral bound.
  have hleftbd : ∀ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
      ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Bf) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
    intro y
    have hre : (↑(-(M : ℝ)) + ↑y * I : ℂ).re = -(M : ℝ) := by simp
    rw [hHfp, norm_mul]
    have hF' : ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ≤ Bf :=
      hFleftM _ (by rw [hre]) (by rw [hre]; exact hMle)
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
        ≤ Bf * ((4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹) :=
          mul_le_mul hF' hE' (norm_nonneg _) hBf0
      _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Bf) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by ring
  have hleftint : Integrable (fun y : ℝ => Hf (↑(-(M : ℝ)) + ↑y * I)) := by
    have hcont : Continuous (fun y : ℝ => Hf (↑(-(M : ℝ)) + ↑y * I)) :=
      hHfcont.comp (by fun_prop)
    exact ((HTGeometry.integrable_inv_sq_add_sq (show (0 : ℝ) < (M : ℝ) - 1 from by linarith)).const_mul
      (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Bf)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hleftbd)
  have hqle : ∫ y : ℝ, (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ ≤ Real.pi := by
    rw [← integral_univ_inv_one_add_sq]
    refine integral_mono (HTGeometry.integrable_inv_sq_add_sq (show (0 : ℝ) < (M : ℝ) - 1 from by linarith))
      integrable_inv_one_add_sq (fun y => ?_)
    refine inv_anti₀ (by positivity) ?_
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (M : ℝ) from hMnn)
      (show (0 : ℝ) ≤ (M : ℝ) - 2 from by linarith), sq_nonneg y]
  have hleftfull : ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
      ≤ 4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    have hdomint : Integrable (fun y : ℝ =>
        (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Bf) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹) :=
      (HTGeometry.integrable_inv_sq_add_sq (show (0 : ℝ) < (M : ℝ) - 1 from by linarith)).const_mul _
    have hCnn : (0 : ℝ) ≤ 4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Bf :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hxmpos.le _)) hBf0
    calc ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ ∫ y : ℝ, (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Bf)
            * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ :=
          integral_mono hleftint.norm hdomint hleftbd
      _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Bf)
            * ∫ y : ℝ, (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := integral_const_mul _ _
      _ ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Bf) * Real.pi :=
          mul_le_mul_of_nonneg_left hqle hCnn
      _ = 4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by ring
  have hleftk : ∀ k, ‖∫ y in (-(T k))..(T k), Hf (↑(-(M : ℝ)) + ↑y * I)‖
      ≤ 4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    intro k
    calc ‖∫ y in (-(T k))..(T k), Hf (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ ∫ y in (-(T k))..(T k), ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith [hTpos k])
      _ = ∫ y in Set.Ioc (-(T k)) (T k), ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖ :=
          intervalIntegral.integral_of_le (by linarith [hTpos k])
      _ ≤ ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖ :=
          setIntegral_le_integral hleftint.norm (Eventually.of_forall (fun y => norm_nonneg _))
      _ ≤ 4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := hleftfull
  -- Horizontal-edge decay.
  have hinvsq : Tendsto (fun k => ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
    have hTsq : Tendsto (fun k => (T k) ^ 2) atTop atTop := by
      simpa [pow_two] using hTtop.atTop_mul_atTop₀ hTtop
    exact hTsq.inv_tendsto_atTop
  have hcore : Tendsto (fun k => (Bf + q k) * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
    have h1 : Tendsto (fun k => Bf * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
      simpa using hinvsq.const_mul Bf
    have h2 : Tendsto (fun k => q k * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
      have := hqlim; simp_rw [div_eq_mul_inv] at this; exact this
    simpa [add_mul] using h1.add h2
  set d : ℕ → ℝ := fun k =>
    (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * (c + (M : ℝ))) * ((Bf + q k) * ((T k) ^ 2)⁻¹) with hd
  have hd0 : Tendsto d atTop (nhds 0) := by
    simp only [hd]
    simpa using hcore.const_mul (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * (c + (M : ℝ)))
  have hqk0 : ∀ k, (0 : ℝ) ≤ q k := fun k =>
    le_trans (norm_nonneg _) (hquietbd k c (by linarith) (le_refl c)).1
  have hedge : ∀ (k : ℕ) (t : ℝ), 0 < T k → |t| = T k →
      ∀ x : ℝ, -(M : ℝ) < x → x ≤ c → ‖F (↑x + ↑t * I)‖ ≤ Bf + q k →
      ‖Hf (↑x + ↑t * I)‖ ≤ (Bf + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) := by
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
    exact mul_le_mul hFbd hE' (norm_nonneg _) (by linarith [hBf0, hqk0 k])
  have htop : ∀ k, ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(T k) * I)‖ ≤ d k := by
    intro k
    have hconst : ∀ x ∈ Set.uIoc (-(M : ℝ)) c,
        ‖Hf (↑x + ↑(T k) * I)‖ ≤ (Bf + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) := by
      intro x hx
      rw [Set.uIoc_of_le hMcle] at hx
      obtain ⟨hx1, hx2⟩ := hx
      refine hedge k (T k) (hTpos k) (abs_of_pos (hTpos k)) x hx1 hx2 ?_
      rcases le_or_gt x (1 - c) with hcase | hcase
      · exact le_trans (hFleftM _ (by simpa using hx1.le) (by simpa using hcase))
          (by linarith [hqk0 k])
      · exact le_trans (hquietbd k x (le_of_lt hcase) hx2).1 (by linarith [hBf0])
    calc ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(T k) * I)‖
        ≤ ((Bf + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹)) * |c - -(M : ℝ)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hconst
      _ = d k := by simp only [hd]; rw [abs_of_nonneg (by linarith)]; ring
  have hbot : ∀ k, ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(-(T k)) * I)‖ ≤ d k := by
    intro k
    have hconst : ∀ x ∈ Set.uIoc (-(M : ℝ)) c,
        ‖Hf (↑x + ↑(-(T k)) * I)‖
          ≤ (Bf + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹) := by
      intro x hx
      rw [Set.uIoc_of_le hMcle] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hpt : (↑x + ↑(-(T k)) * I : ℂ) = ↑x - ↑(T k) * I := by push_cast; ring
      refine hedge k (-(T k)) (hTpos k) (by rw [abs_neg, abs_of_pos (hTpos k)]) x hx1 hx2 ?_
      rcases le_or_gt x (1 - c) with hcase | hcase
      · exact le_trans (hFleftM _ (by simpa using hx1.le) (by simpa using hcase))
          (by linarith [hqk0 k])
      · rw [hpt]; exact le_trans (hquietbd k x (le_of_lt hcase) hx2).2 (by linarith [hBf0])
    calc ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(-(T k)) * I)‖
        ≤ ((Bf + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹)) * |c - -(M : ℝ)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hconst
      _ = d k := by simp only [hd]; rw [abs_of_nonneg (by linarith)]; ring
  -- Rectangle bound and passage to the limit in `k`.
  have hrighttendsto : Tendsto (fun k => ∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)) atTop
      (nhds (∫ t : ℝ, Hf (↑c + ↑t * I))) :=
    intervalIntegral_tendsto_integral hRint (tendsto_neg_atBot_iff.mpr hTtop) hTtop
  have hnormtendsto : Tendsto (fun k => ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖) atTop
      (nhds ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖) := hrighttendsto.norm
  have hrectbd : ∀ k, ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖
      ≤ (d k + d k) + 4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
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
  have hdb : Tendsto (fun k => (d k + d k) + 4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
      atTop (nhds (4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))) := by
    simpa using (hd0.add hd0).add_const (4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
  have hfin := le_of_tendsto_of_tendsto' hnormtendsto hdb hrectbd
  -- Read the coefficient from the right-line integral.
  have hR : a n * (1 / 2) = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, Hf (↑c + ↑t * I) := by
    rw [hHf]; exact perronSecondDiff_integral hc0 hsum hF hFeq hn1
  have hnorm_an : ‖a n‖ * (1 / 2) ≤ (1 / (2 * Real.pi)) *
      (4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) := by
    have h1 : ‖a n * (1 / 2 : ℂ)‖ = ‖a n‖ * (1 / 2) := by
      rw [norm_mul]
      norm_num
    calc ‖a n‖ * (1 / 2) = ‖a n * (1 / 2 : ℂ)‖ := h1.symm
      _ = ‖(1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, Hf (↑c + ↑t * I)‖ := by rw [hR]
      _ = (1 / (2 * Real.pi)) * ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (1 / (2 * Real.pi)) * (4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) :=
          mul_le_mul_of_nonneg_left hfin (by positivity)
  have hpi : (1 / (2 * Real.pi)) * (4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
      = 2 * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    field_simp
    ring
  rw [hpi] at hnorm_an
  rw [hBf] at hnorm_an ⊢
  linarith [hnorm_an]

/-- **The support radius of a quiet carrier is the exponential flank-growth rate of its reflection
factor.**  If the flank bounds satisfy `H(M) ≤ C·r^M` for constants `C ≥ 0`, `r ≥ 1`, then every
Dirichlet coefficient with `n − ½ > r` vanishes: the carrier is a Dirichlet polynomial of degree
at most `r + ½`.  For a conductor datum `H(M) = CJ·Q₀^{1+2M} ≤ (CJ·Q₀)·(Q₀²)^M` this recovers
support `≤ Q₀²`; a Gamma-type factor grows super-exponentially in `M` and yields no bound — the
dichotomy between Dirichlet-polynomial carriers and Gamma-scale functional equations. -/
theorem quiet_crossing_cocycle_support {F h : ℂ → ℂ} {a : ℕ → ℂ} {c B : ℝ} {H : ℕ → ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hF : Differentiable ℂ F)
    (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hB : ∀ s : ℂ, c ≤ s.re → ‖F s‖ ≤ B)
    (hFE : ∀ s : ℂ, F s = h s * F (1 - s))
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ), Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ k, 0 < T k) ∧ Filter.Tendsto (fun k => q k / (T k) ^ 2) Filter.atTop (nhds 0) ∧
      ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
        ‖F (σ + (T k) * Complex.I)‖ ≤ q k ∧ ‖F (σ - (T k) * Complex.I)‖ ≤ q k)
    (hgrow : ∀ M : ℕ, 2 ≤ M → ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c → ‖h s‖ ≤ H M)
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
  have hbd : ∀ᶠ M : ℕ in atTop, ‖a n‖ ≤ (4 * C * B * ((n : ℝ) - 1 / 2)) * ρ ^ M := by
    filter_upwards [eventually_ge_atTop (max 2 ⌈c⌉₊)] with M hM
    have hM2 : 2 ≤ M := le_trans (le_max_left _ _) hM
    have hMc : (c : ℝ) ≤ (M : ℝ) :=
      le_trans (Nat.le_ceil c) (by exact_mod_cast le_trans (le_max_right _ _) hM)
    have hkey := quiet_crossing_cocycle_bound hc hc0 hF hsum hFeq hB hFE hquiet hM2 hMc
      (hgrow M hM2) hn2
    have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB ↑c (by rw [Complex.ofReal_re]))
    have hsplit : ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))
        = ((n : ℝ) - 1 / 2) * (((n : ℝ) - 1 / 2) ^ M)⁻¹ := by
      rw [Real.rpow_sub hxmpos, Real.rpow_one,
        show ((n : ℝ) - 1 / 2) ^ ((M : ℝ)) = ((n : ℝ) - 1 / 2) ^ (M : ℕ) from
          Real.rpow_natCast _ M]
      ring
    calc ‖a n‖ ≤ 4 * (H M * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := hkey
      _ ≤ 4 * ((C * r ^ M) * B) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hxmpos.le _)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hHle M) hB0) (by norm_num)
      _ = (4 * C * B * ((n : ℝ) - 1 / 2)) * (r ^ M * (((n : ℝ) - 1 / 2) ^ M)⁻¹) := by
          rw [hsplit]; ring
      _ = (4 * C * B * ((n : ℝ) - 1 / 2)) * ρ ^ M := by
          rw [hρ, mul_pow, inv_pow]
  have hlim : Tendsto (fun M : ℕ => (4 * C * B * ((n : ℝ) - 1 / 2)) * ρ ^ M) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ_nn hρ_lt1).const_mul
      (4 * C * B * ((n : ℝ) - 1 / 2))
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim hbd) (norm_nonneg _))

/-- **Bounded-flank reflection factors with a zero are quiet-unrealizable.**  If the flank bounds
`H(M)` are uniformly bounded (`H(M) ≤ C`) — as for any finite Blaschke-type quotient whose poles
avoid the closed flank region — then the support radius is `1`, so every coefficient with `n ≥ 2`
dies and the carrier is the constant `a₁`.  Evaluating the functional equation at a zero `ρ₀` of
the reflection factor then kills the constant: `a₁ = F(ρ₀) = h(ρ₀)·F(1−ρ₀) = 0`.  The minimal
non-conductor divisor — a single zero/pole pair `(ρ₀, 1−ρ₀)` — therefore carries no nonzero quiet
Dirichlet series: **realizable divisors are either empty or force unbounded flank growth.** -/
theorem quiet_crossing_cocycle_kill {F h : ℂ → ℂ} {a : ℕ → ℂ} {c B : ℝ} {H : ℕ → ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hF : Differentiable ℂ F)
    (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hB : ∀ s : ℂ, c ≤ s.re → ‖F s‖ ≤ B)
    (hFE : ∀ s : ℂ, F s = h s * F (1 - s))
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ), Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ k, 0 < T k) ∧ Filter.Tendsto (fun k => q k / (T k) ^ 2) Filter.atTop (nhds 0) ∧
      ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
        ‖F (σ + (T k) * Complex.I)‖ ≤ q k ∧ ‖F (σ - (T k) * Complex.I)‖ ≤ q k)
    (hgrow : ∀ M : ℕ, 2 ≤ M → ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c → ‖h s‖ ≤ H M)
    {C : ℝ} (hHle : ∀ M : ℕ, H M ≤ C)
    {ρ₀ : ℂ} (hzero : h ρ₀ = 0) :
    ∀ n : ℕ, 1 ≤ n → a n = 0 := by
  have hsupp : ∀ n : ℕ, (1 : ℝ) < (n : ℝ) - 1 / 2 → a n = 0 :=
    quiet_crossing_cocycle_support hc hc0 hF hsum hFeq hB hFE hquiet hgrow (C := C) (r := 1)
      le_rfl (fun M => by simpa using hHle M)
  have hsupp' : ∀ n : ℕ, 2 ≤ n → a n = 0 := by
    intro n hn
    refine hsupp n ?_
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- the series collapses to the constant `a 1` on the half-plane
  have hLconst : ∀ s : ℂ, c ≤ s.re → LSeries a s = a 1 := by
    intro s _
    have hterms : ∀ m : ℕ, m ≠ 1 → LSeries.term a s m = 0 := by
      intro m hm
      rcases eq_or_ne m 0 with rfl | hm0
      · exact LSeries.term_zero a s
      · rw [LSeries.term_of_ne_zero hm0, hsupp' m (by omega), zero_div]
    rw [LSeries, tsum_eq_single 1 hterms, LSeries.term_of_ne_zero one_ne_zero,
      Nat.cast_one, Complex.one_cpow, div_one]
  -- identity principle: `F` is the constant `a 1` everywhere
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
  -- evaluate the functional equation at the zero of the reflection factor
  intro n hn
  rcases eq_or_ne n 1 with rfl | hn1
  · have hkill := hFE ρ₀
    rw [hFconst ρ₀, hFconst (1 - ρ₀), hzero, zero_mul] at hkill
    exact hkill
  · exact hsupp' n (by omega)

end RHTower
