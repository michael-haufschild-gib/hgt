/-
Quiet-crossing rigidity with a **conductor datum** in place of exact reflection symmetry.

The rigidity theorem `quiet_crossing_rigidity` uses the exact symmetry `F(s) = F(1−s)` to carry the
right-half-plane bound `‖F‖ ≤ B` across to the left flank `Re s ≤ 1−c`.  A completed `L`-function
does not satisfy that bare symmetry; it satisfies a functional equation whose reflection factor is a
finite Dirichlet polynomial in the conductors,

    F(s) = (∑_{j∈J} c_j · Q_j^{1−2s}) · F(1−s),

with each `Q_j ≥ 1` a natural number bounded by a global conductor `Q₀`.  The reflection factor has
modulus `∑_j ‖c_j‖ · Q_j^{1−2σ}` on the line `Re s = σ`; for `σ ≤ 1−c` (so `1−2σ ≥ 2c−1 ≥ 0`) this
is at most `CJ · Q₀^{1−2σ}` where `CJ = ∑_j ‖c_j‖`, and on a contour of depth `Re s = −M` it is at
most `CJ · Q₀^{1+2M}`.  The left flank therefore carries the *polynomially amplified* bound
`‖F(s)‖ ≤ CJ · Q₀^{1+2M} · B` instead of the flat `B`.

Feeding this enlarged left-flank constant through the same Perron / Cauchy-rectangle machinery as
`quiet_crossing_rigidity`, the horizontal edges are still killed by the kernel's `T_k^{-2}` decay
(the amplified constant is fixed in `k` at a fixed depth `M`), and the left edge is bounded by

    ‖(1/2π)·∫_left‖ ≤ const · CJ · B · Q₀^{1+2M} · (n−½)^{1−M}
                    = const' · (Q₀² / (n−½))^M · (per-n constant).

When `Q₀² < n` the ratio `r = Q₀²/(n−½) < 1` (since `Q₀² ≤ n−1 < n−½`), so `r^M → 0` as `M → ∞` and
the whole bound vanishes.  Hence `½·aₙ = 0`, i.e. `aₙ = 0`, for every `n > Q₀²`.  The conclusion is a
*support* statement: the Dirichlet coefficients of a quiet carrier obeying a conductor functional
equation are supported on `{0} ∪ {1 ≤ n ≤ Q₀²}` — a polynomial of degree at most `Q₀²`.

* `quiet_crossing_conductor_support` — `aₙ = 0` for every `n` with `Q₀² < n`.
* `quiet_crossing_conductor_polynomial` — contrapositive support form: `aₙ ≠ 0 ⟹ n ≤ Q₀²`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.QuietCrossingRigidity
import GaloisForLFunctions.HTGeometry.PerronKernelBound

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set

noncomputable section

namespace RHTower

/-- **Quiet-crossing rigidity with a conductor functional equation.**  Let `F` be entire, agree with
an absolutely convergent Dirichlet series `L(s) = Σ aₘ m^{−s}` on `Re s ≥ c` (with `½ ≤ c`), and obey
the conductor functional equation `F(s) = (∑_{j∈J} c_j·Q_j^{1−2s})·F(1−s)` with each conductor
`1 ≤ Q_j ≤ Q₀`.  Suppose there is a sequence of heights `T_k → ∞` along which `F` is *quiet* across
the closed critical strip `1−c ≤ σ ≤ c`: `‖F(σ ± iT_k)‖ ≤ q_k` with `q_k/T_k² → 0`.  Then `aₙ = 0`
for every `n > Q₀²`.

The Mellin representation `½·aₙ = (1/2π)∫ F(c+it)·E(c+it) dt` uses the entire regularization
`E = N/(s(s+1))`.  Since `F·E` is entire, Cauchy's theorem on the rectangle with corners
`(−M,−T_k)` and `(c,T_k)` moves the contour.  The left flank `Re s ≤ 1−c` now carries the amplified
bound `‖F(s)‖ ≤ CJ·Q₀^{1+2M}·B` (with `CJ = ∑_j ‖c_j‖`), because the reflection factor's modulus
`∑_j ‖c_j‖·Q_j^{1−2σ}` is at most `CJ·Q₀^{1+2M}` on `−M ≤ σ ≤ 1−c` (positive exponent, base
monotonicity).  The horizontal edges are still `≤ (CJ·Q₀^{1+2M}·B + q_k)·T_k^{-2}·const` and vanish
as `k → ∞`; the left edge `Re s = −M` is bounded uniformly in `k` by
`4π·CJ·Q₀^{1+2M}·B·(n−½)^{1−M}`.  Passing `k → ∞` gives
`‖½·aₙ‖ ≤ (1/2π)·4π·CJ·Q₀^{1+2M}·B·(n−½)^{1−M}`, and since `Q₀^{1+2M}·(n−½)^{1−M}`
`= Q₀(n−½)·(Q₀²/(n−½))^M` with `Q₀²/(n−½) < 1` (from `Q₀² < n`), the right side tends to `0` as
`M → ∞`. -/
theorem quiet_crossing_conductor_support {ι : Type*} {F : ℂ → ℂ} {a : ℕ → ℂ} {c : ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hF : Differentiable ℂ F)
    (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (J : Finset ι) (cs : ι → ℂ) (Q : ι → ℕ) (Q₀ : ℕ)
    (hQ1 : ∀ j ∈ J, 1 ≤ Q j) (hQ0 : ∀ j ∈ J, Q j ≤ Q₀) (hQ01 : 1 ≤ Q₀)
    (hFE : ∀ s : ℂ, F s = (∑ j ∈ J, cs j * (Q j : ℂ) ^ ((1 : ℂ) - 2 * s)) * F (1 - s))
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ), Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ k, 0 < T k) ∧ Filter.Tendsto (fun k => q k / (T k) ^ 2) Filter.atTop (nhds 0) ∧
      ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
        ‖F (σ + (T k) * Complex.I)‖ ≤ q k ∧ ‖F (σ - (T k) * Complex.I)‖ ≤ q k) :
    ∀ n : ℕ, Q₀ ^ 2 < n → a n = 0 := by
  intro n hnQ
  have hn2 : 2 ≤ n := by
    have h1 : 1 ≤ Q₀ ^ 2 := Nat.one_le_pow 2 Q₀ (by omega)
    omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨T, q, hTtop, hTpos, hqlim, hquietbd⟩ := hquiet
  obtain ⟨B, hB⟩ := lseries_bounded_on_halfplane hsum
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB ↑c (by rw [Complex.ofReal_re]))
  have hFB : ∀ s : ℂ, c ≤ s.re → ‖F s‖ ≤ B := fun s hs => by rw [hFeq s hs]; exact hB s hs
  -- The conductor mass `CJ = ∑ ‖c_j‖`.
  have hCJ0 : (0 : ℝ) ≤ ∑ j ∈ J, ‖cs j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hQ01R : (1 : ℝ) ≤ (Q₀ : ℝ) := by exact_mod_cast hQ01
  -- **Left-flank amplification.**  On `Re s ≤ 1−c`, the reflection factor carries a positive-exponent
  -- Dirichlet-polynomial modulus, giving the amplified bound `‖F s‖ ≤ (∑ ‖c_j‖ Q_j^{1−2σ})·B`.
  have hFflank : ∀ s : ℂ, s.re ≤ 1 - c →
      ‖F s‖ ≤ (∑ j ∈ J, ‖cs j‖ * (Q j : ℝ) ^ (1 - 2 * s.re)) * B := by
    intro s hs2
    have hre1s : c ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hFB1s : ‖F (1 - s)‖ ≤ B := hFB _ hre1s
    have hsumb : ‖∑ j ∈ J, cs j * (Q j : ℂ) ^ ((1 : ℂ) - 2 * s)‖
        ≤ ∑ j ∈ J, ‖cs j‖ * (Q j : ℝ) ^ (1 - 2 * s.re) := by
      calc ‖∑ j ∈ J, cs j * (Q j : ℂ) ^ ((1 : ℂ) - 2 * s)‖
          ≤ ∑ j ∈ J, ‖cs j * (Q j : ℂ) ^ ((1 : ℂ) - 2 * s)‖ := norm_sum_le _ _
        _ = ∑ j ∈ J, ‖cs j‖ * (Q j : ℝ) ^ (1 - 2 * s.re) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [norm_mul, norm_natCast_cpow_of_pos (hQ1 j hj)]
            congr 2
            simp [Complex.sub_re, Complex.mul_re]
    have hsnn : (0 : ℝ) ≤ ∑ j ∈ J, ‖cs j‖ * (Q j : ℝ) ^ (1 - 2 * s.re) :=
      Finset.sum_nonneg (fun j _ => by positivity)
    rw [hFE s, norm_mul]
    exact mul_le_mul hsumb hFB1s (norm_nonneg _) hsnn
  have hEdiff : Differentiable ℂ (perronE n) := perronE_differentiable hn1
  -- Real facts about the three knots.
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hxppos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hxmpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hxm1 : (1 : ℝ) ≤ (n : ℝ) - 1 / 2 := by linarith
  have hbase1p : (1 : ℝ) ≤ (n : ℝ) + 1 / 2 := by linarith
  -- The entire integrand `Hf = F·E`.
  set Hf : ℂ → ℂ := fun s => F s * perronE n s with hHf
  have hHfp : ∀ p : ℂ, Hf p = F p * perronE n p := fun p => by rw [hHf]
  have hHfdiff : Differentiable ℂ Hf := by rw [hHf]; exact hF.mul hEdiff
  have hHfcont : Continuous Hf := hHfdiff.continuous
  -- Numerator bound on the line `Re s ≤ c` (positive exponent regime).
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
  -- Numerator bound on the line `Re s = −M` (negative exponent regime).
  have hKink_M : ∀ (M : ℝ) (p : ℂ), 1 ≤ M → p.re = -M →
      ‖perronKink n p‖ ≤ 4 * ((n : ℝ) - 1 / 2) ^ (1 - M) := by
    intro M p hM hpre
    have hb := perronKink_norm_le hn1 p
    rw [hpre, show (-M + 1) = 1 - M by ring] at hb
    have hnp : (1 - M) ≤ 0 := by linarith
    have t1 : ((n : ℝ) + 1 / 2) ^ (1 - M) ≤ ((n : ℝ) - 1 / 2) ^ (1 - M) :=
      Real.rpow_le_rpow_of_nonpos hxmpos (by linarith) hnp
    have t3 : ((n : ℝ)) ^ (1 - M) ≤ ((n : ℝ) - 1 / 2) ^ (1 - M) :=
      Real.rpow_le_rpow_of_nonpos hxmpos (by linarith) hnp
    linarith [hb, t1, t3]
  -- The right-line integrand is integrable.
  have hRint : Integrable (fun t : ℝ => Hf (↑c + ↑t * I)) := by
    have hcont : Continuous (fun t : ℝ => Hf (↑c + ↑t * I)) := hHfcont.comp (by fun_prop)
    have hbd : ∀ t : ℝ, ‖Hf (↑c + ↑t * I)‖
        ≤ (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * B) * (c ^ 2 + t ^ 2)⁻¹ := by
      intro t
      have hre : (↑c + ↑t * I : ℂ).re = c := by simp
      rw [hHfp, norm_mul]
      have hF' : ‖F (↑c + ↑t * I)‖ ≤ B := hFB _ (le_of_eq hre.symm)
      have h0 : (↑c + ↑t * I : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have h1 : (↑c + ↑t * I : ℂ) ≠ -1 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
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
  -- The bound at a fixed contour depth `M`; the left flank carries `Bf = CJ·Q₀^{1+2M}·B`.
  have keyM : ∀ M : ℕ, 2 ≤ M → (c : ℝ) ≤ (M : ℝ) →
      ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖
        ≤ 4 * Real.pi * ((∑ j ∈ J, ‖cs j‖) * (Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) * B)
            * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    intro M hM2 hMc
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hM1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
    have hM2R : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    have hMle : -(M : ℝ) ≤ 1 - c := by linarith
    have hMcle : -(M : ℝ) ≤ c := by linarith
    set Bf : ℝ := (∑ j ∈ J, ‖cs j‖) * (Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) * B with hBf
    have hBf0 : (0 : ℝ) ≤ Bf :=
      mul_nonneg (mul_nonneg hCJ0 (Real.rpow_nonneg (by positivity) _)) hB0
    -- Amplified flank bound, specialised uniformly over `−M ≤ Re s ≤ 1−c`.
    have hFleftM : ∀ s : ℂ, -(M : ℝ) ≤ s.re → s.re ≤ 1 - c → ‖F s‖ ≤ Bf := by
      intro s hs1 hs2
      refine le_trans (hFflank s hs2) ?_
      rw [hBf]
      refine mul_le_mul_of_nonneg_right ?_ hB0
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hQjQ0 : (Q j : ℝ) ≤ (Q₀ : ℝ) := by exact_mod_cast hQ0 j hj
      have hexp_nn : (0 : ℝ) ≤ 1 - 2 * s.re := by linarith
      have hexp_le : 1 - 2 * s.re ≤ 1 + 2 * (M : ℝ) := by linarith
      calc (Q j : ℝ) ^ (1 - 2 * s.re)
          ≤ (Q₀ : ℝ) ^ (1 - 2 * s.re) := Real.rpow_le_rpow (by positivity) hQjQ0 hexp_nn
        _ ≤ (Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) := Real.rpow_le_rpow_of_exponent_le hQ01R hexp_le
    -- Left-line domination.
    have hleftbd : ∀ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * Bf) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
      intro y
      have hre : (↑(-(M : ℝ)) + ↑y * I : ℂ).re = -(M : ℝ) := by simp
      rw [hHfp, norm_mul]
      have hF' : ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ≤ Bf :=
        hFleftM _ (by rw [hre]) (by rw [hre]; exact hMle)
      have h0 : (↑(-(M : ℝ)) + ↑y * I : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have h1 : (↑(-(M : ℝ)) + ↑y * I : ℂ) ≠ -1 := by
        intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
      have hE' : ‖perronE n (↑(-(M : ℝ)) + ↑y * I)‖
          ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
        rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
        exact mul_le_mul (hKink_M (M : ℝ) _ hM1.le hre)
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
    -- Horizontal-edge domination and its decay.
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
    -- Common per-edge norm-of-integrand const.
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
        rcases le_or_gt x (1 - c) with h | h
        · exact le_trans (hFleftM _ (by simpa using hx1.le) (by simpa using h)) (by linarith [hqk0 k])
        · exact le_trans (hquietbd k x (le_of_lt h) hx2).1 (by linarith [hBf0])
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
        rcases le_or_gt x (1 - c) with h | h
        · exact le_trans (hFleftM _ (by simpa using hx1.le) (by simpa using h)) (by linarith [hqk0 k])
        · rw [hpt]; exact le_trans (hquietbd k x (le_of_lt h) hx2).2 (by linarith [hBf0])
      calc ‖∫ x in (-(M : ℝ))..c, Hf (↑x + ↑(-(T k)) * I)‖
          ≤ ((Bf + q k) * (4 * ((n : ℝ) + 1 / 2) ^ (c + 1) * ((T k) ^ 2)⁻¹)) * |c - -(M : ℝ)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hconst
        _ = d k := by simp only [hd]; rw [abs_of_nonneg (by linarith)]; ring
    -- Right vertical integral converges to the full-line integral.
    have hrighttendsto : Tendsto (fun k => ∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)) atTop
        (nhds (∫ t : ℝ, Hf (↑c + ↑t * I))) :=
      intervalIntegral_tendsto_integral hRint (tendsto_neg_atBot_iff.mpr hTtop) hTtop
    have hnormtendsto : Tendsto (fun k => ‖∫ y in (-(T k))..(T k), Hf (↑c + ↑y * I)‖) atTop
        (nhds ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖) := hrighttendsto.norm
    -- Rectangle (Cauchy) bound: right edge ≤ tops + bottom + left.
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
      have h3 : ‖Itop‖ ≤ d k := htop k
      have h4 : ‖Ibot‖ ≤ d k := hbot k
      have h5 : ‖Ilft‖ ≤ 4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := hleftk k
      linarith [hb1, hb2, h3, h4, h5]
    have hdb : Tendsto (fun k => (d k + d k) + 4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
        atTop (nhds (4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))) := by
      simpa using (hd0.add hd0).add_const (4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
    have hfin := le_of_tendsto_of_tendsto' hnormtendsto hdb hrectbd
    -- `4π·Bf·(n−½)^{1−M}` is exactly the stated right side.
    calc ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖
        ≤ 4 * Real.pi * Bf * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := hfin
      _ = 4 * Real.pi * ((∑ j ∈ J, ‖cs j‖) * (Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) * B)
            * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by rw [hBf]
  -- Send the contour to infinity: `Q₀^{1+2M}·(n−½)^{1−M} = Q₀(n−½)·r^M` with `r = Q₀²/(n−½) < 1`.
  have hMtendsto : Tendsto (fun M : ℕ =>
      4 * Real.pi * ((∑ j ∈ J, ‖cs j‖) * (Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) * B)
        * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) atTop (nhds 0) := by
    have hDpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
    have hQ0pos : (0 : ℝ) < (Q₀ : ℝ) := by linarith
    set r : ℝ := (Q₀ : ℝ) ^ 2 * ((n : ℝ) - 1 / 2)⁻¹ with hr
    have hr_nn : 0 ≤ r := by rw [hr]; positivity
    have hr_lt1 : r < 1 := by
      rw [hr, ← div_eq_mul_inv, div_lt_one hDpos]
      have h1 : ((Q₀ ^ 2 : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
        have : Q₀ ^ 2 + 1 ≤ n := hnQ
        exact_mod_cast this
      push_cast at h1
      nlinarith
    have hbase : Tendsto (fun M : ℕ =>
        (Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) atTop (nhds 0) := by
      have heq : (fun M : ℕ =>
          (Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
          = fun M : ℕ => ((Q₀ : ℝ) * ((n : ℝ) - 1 / 2)) * r ^ M := by
        funext M
        rw [Real.rpow_add hQ0pos, Real.rpow_one, Real.rpow_sub hDpos, Real.rpow_one,
          show (2 : ℝ) * (M : ℝ) = ((2 * M : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
          show ((n : ℝ) - 1 / 2) ^ ((M : ℝ)) = ((n : ℝ) - 1 / 2) ^ (M : ℕ) from by
            rw [Real.rpow_natCast],
          pow_mul, hr, div_eq_mul_inv, mul_pow, inv_pow]
        ring
      rw [heq]
      have := tendsto_pow_atTop_nhds_zero_of_lt_one hr_nn hr_lt1
      simpa using this.const_mul ((Q₀ : ℝ) * ((n : ℝ) - 1 / 2))
    have hfeq : (fun M : ℕ =>
        4 * Real.pi * ((∑ j ∈ J, ‖cs j‖) * (Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) * B)
          * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
        = fun M : ℕ => (4 * Real.pi * (∑ j ∈ J, ‖cs j‖) * B)
            * ((Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) := by
      funext M; ring
    rw [hfeq]
    simpa using hbase.const_mul (4 * Real.pi * (∑ j ∈ J, ‖cs j‖) * B)
  have hbound_an : ‖a n * (1 / 2)‖ ≤ 0 := by
    have hR : a n * (1 / 2) = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, Hf (↑c + ↑t * I) := by
      rw [hHf]; exact perronSecondDiff_integral hc0 hsum hF hFeq hn1
    have hev : ∀ᶠ M : ℕ in atTop, ‖a n * (1 / 2)‖
        ≤ (1 / (2 * Real.pi)) * (4 * Real.pi
            * ((∑ j ∈ J, ‖cs j‖) * (Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) * B)
            * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) := by
      filter_upwards [eventually_ge_atTop (max 2 ⌈c⌉₊)] with M hM
      have hM2 : 2 ≤ M := le_trans (le_max_left _ _) hM
      have hMc : (c : ℝ) ≤ (M : ℝ) :=
        le_trans (Nat.le_ceil c) (by exact_mod_cast le_trans (le_max_right _ _) hM)
      rw [hR, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (keyM M hM2 hMc) (by positivity)
    have hlim : Tendsto (fun M : ℕ => (1 / (2 * Real.pi)) * (4 * Real.pi
        * ((∑ j ∈ J, ‖cs j‖) * (Q₀ : ℝ) ^ (1 + 2 * (M : ℝ)) * B)
        * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))) atTop (nhds 0) := by
      simpa using hMtendsto.const_mul (1 / (2 * Real.pi))
    exact ge_of_tendsto hlim hev
  have han2 : a n * (1 / 2) = 0 := norm_eq_zero.mp (le_antisymm hbound_an (norm_nonneg _))
  exact (mul_eq_zero.mp han2).resolve_right (by norm_num)

/-- **Conductor support (polynomial form).**  Under the quiet-crossing conductor hypotheses, every
nonzero Dirichlet coefficient of the carrier has index at most `Q₀²`: the coefficient support is
contained in `{0} ∪ {1 ≤ n ≤ Q₀²}`.  This is the contrapositive of
`quiet_crossing_conductor_support`, which kills every coefficient with `n > Q₀²`. -/
theorem quiet_crossing_conductor_polynomial {ι : Type*} {F : ℂ → ℂ} {a : ℕ → ℂ} {c : ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hF : Differentiable ℂ F)
    (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (J : Finset ι) (cs : ι → ℂ) (Q : ι → ℕ) (Q₀ : ℕ)
    (hQ1 : ∀ j ∈ J, 1 ≤ Q j) (hQ0 : ∀ j ∈ J, Q j ≤ Q₀) (hQ01 : 1 ≤ Q₀)
    (hFE : ∀ s : ℂ, F s = (∑ j ∈ J, cs j * (Q j : ℂ) ^ ((1 : ℂ) - 2 * s)) * F (1 - s))
    (hquiet : ∃ (T : ℕ → ℝ) (q : ℕ → ℝ), Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ k, 0 < T k) ∧ Filter.Tendsto (fun k => q k / (T k) ^ 2) Filter.atTop (nhds 0) ∧
      ∀ k, ∀ σ : ℝ, 1 - c ≤ σ → σ ≤ c →
        ‖F (σ + (T k) * Complex.I)‖ ≤ q k ∧ ‖F (σ - (T k) * Complex.I)‖ ≤ q k) :
    ∀ n : ℕ, a n ≠ 0 → n ≤ Q₀ ^ 2 := by
  intro n hane
  by_contra h
  exact hane
    (quiet_crossing_conductor_support hc hc0 hF hsum hFeq J cs Q Q₀ hQ1 hQ0 hQ01 hFE hquiet n
      (not_le.mp h))

end RHTower
