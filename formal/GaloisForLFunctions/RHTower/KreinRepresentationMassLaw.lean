import GaloisForLFunctions.RHTower.KreinRepresentationMultiplicities

/-!
# Masses equal multiplicities below the Landau height

**Theorem** (`zeta_krein_representation_masses_below_landau_height`).  For `0 < η ≤ 1/2` and every
bound `M ≥ 1` on multiplicities there is `L₀` such that for `L ≥ L₀`: every positive measure `ν`
representing the level-`L` Hodge form of `ζ` (`∫ |f̂|² dν = |W(f,f)|` on the Hodge class) and every
on-line zero `ρ₀ = 1/2 + iγ₀` of multiplicity `m₀ ≤ M` with `7 ≤ γ₀ ≤ (1-η) 2π e^{2L}`,
`δ`-separated in ordinate from all other zeros (`0 < δ ≤ 1/2`,
`(48 C log(γ₀+1) + 32 M)/δ ≤ π η^{3/2} e^{2L}`), satisfy
`|ν([γ₀ - r_L, γ₀ + r_L]) - m₀| ≤ exp(-π η^{3/2} e^{2L}/(64 M))`,
`r_L = exp(-π η^{3/2} e^{2L}/(8M))`.

Together with the pinning law below the Landau height (`zeta_krein_completion_pinned_below_landau_height`),
every positive representation of the finite-level Weil form is the zero measure of `ζ` below
`(1-η) 2π e^{2L}`, masses included, up to super-exponentially small errors.

The proof tests `ν` against the resolvent-divided tilted test at the zero
(`krein_mass_core`): its Weil form is `m₀ |f̂(γ₀)|²` up to the squared tail; off the ball it is
dominated by the tilted radical test and the plain bump; on the ball it is constant to within
the Borel–Carathéodory variation.  The exponent bookkeeping (`landau_small_package`) reduces all
error terms to one level inequality `B₀ + (14 + 4M) L ≤ π η^{3/2} e^{2L}/(64 M)`.
-/

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real ENNReal
open Bottcher Zeta23

namespace RHTower

noncomputable section

/-- Two-sided mass bounds on a ball give the mass up to `6(M+2)Δ/X + 3E/X²`. -/
theorem mass_close_of_two_sided {ν m X Δ E Mr : ℝ} (hν0 : 0 ≤ ν) (hm0 : 0 ≤ m) (hmM : m ≤ Mr)
    (hX : 0 < X) (hΔ0 : 0 ≤ Δ) (hΔX : 4 * Δ ≤ X) (hE0 : 0 ≤ E) (hEX : E ≤ X ^ 2)
    (hup : ν * (X - Δ) ^ 2 ≤ m * X ^ 2 + E) (hlow : m * X ^ 2 - E ≤ ν * (X + Δ) ^ 2) :
    |ν - m| ≤ 6 * (Mr + 2) * (Δ / X) + 3 * (E / X ^ 2) := by
  set t := Δ / X with ht
  set e := E / X ^ 2 with he
  have hX2 : 0 < X ^ 2 := by positivity
  have hΔt : Δ = t * X := by rw [ht]; field_simp
  have hEe : E = e * X ^ 2 := by rw [he]; field_simp
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht4 : t ≤ 1 / 4 := by rw [ht, div_le_iff₀ hX]; linarith
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he1 : e ≤ 1 := by rw [he, div_le_iff₀ hX2]; linarith
  have hup' : ν * (1 - t) ^ 2 ≤ m + e := by
    have h : X ^ 2 * (ν * (1 - t) ^ 2) ≤ X ^ 2 * (m + e) := by
      have e1 : ν * (X - Δ) ^ 2 = X ^ 2 * (ν * (1 - t) ^ 2) := by rw [hΔt]; ring
      have e2 : m * X ^ 2 + E = X ^ 2 * (m + e) := by rw [hEe]; ring
      rw [← e1, ← e2]; exact hup
    exact le_of_mul_le_mul_left h hX2
  have hlow' : m - e ≤ ν * (1 + t) ^ 2 := by
    have h : X ^ 2 * (m - e) ≤ X ^ 2 * (ν * (1 + t) ^ 2) := by
      have e1 : ν * (X + Δ) ^ 2 = X ^ 2 * (ν * (1 + t) ^ 2) := by rw [hΔt]; ring
      have e2 : m * X ^ 2 - E = X ^ 2 * (m - e) := by rw [hEe]; ring
      rw [← e1, ← e2]; exact hlow
    exact le_of_mul_le_mul_left h hX2
  have hkey : 1 ≤ (1 + 4 * t) * (1 - t) ^ 2 := by
    have hq : 0 ≤ 2 - 7 * t + 4 * t ^ 2 := by nlinarith
    have e : (1 + 4 * t) * (1 - t) ^ 2 = 1 + t * (2 - 7 * t + 4 * t ^ 2) := by ring
    rw [e]; linarith [mul_nonneg ht0 hq]
  have hνup : ν ≤ (m + e) * (1 + 4 * t) := by
    calc ν = ν * 1 := by ring
      _ ≤ ν * ((1 + 4 * t) * (1 - t) ^ 2) := mul_le_mul_of_nonneg_left hkey hν0
      _ = (1 + 4 * t) * (ν * (1 - t) ^ 2) := by ring
      _ ≤ (1 + 4 * t) * (m + e) := mul_le_mul_of_nonneg_left hup' (by linarith)
      _ = (m + e) * (1 + 4 * t) := by ring
  have p1 : t * m ≤ t * Mr := mul_le_mul_of_nonneg_left hmM ht0
  have p2 : t * e ≤ e / 4 := by nlinarith
  have p3 : 0 ≤ t * Mr := mul_nonneg ht0 (hm0.trans hmM)
  have h1 : ν - m ≤ 4 * t * Mr + 2 * e := by nlinarith [hνup]
  have h2 : m - ν ≤ 6 * t * (Mr + 1) + e := by
    have h3 : m - ν ≤ ν * (2 * t + t ^ 2) + e := by nlinarith [hlow']
    have htt : t ^ 2 ≤ t := by nlinarith
    have h4 : ν * (2 * t + t ^ 2) ≤ ν * (3 * t) :=
      mul_le_mul_of_nonneg_left (by linarith) hν0
    have h5 : ν * (3 * t) ≤ (m + e) * (1 + 4 * t) * (3 * t) :=
      mul_le_mul_of_nonneg_right hνup (by linarith)
    have q1 : (m + e) * (1 + 4 * t) ≤ (Mr + 1) * 2 :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have h6 : (m + e) * (1 + 4 * t) * (3 * t) ≤ 6 * t * (Mr + 1) := by
      have := mul_le_mul_of_nonneg_right q1 (by linarith : (0 : ℝ) ≤ 3 * t)
      linarith
    linarith
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- The floor of the divided kernel in exponential form:
`m_V ≥ (c_N/e) e^{-ε(γ₀+1/2)} e^{-G/16}` for `θ = π/4 - ε`, once `3C log(γ₀+1)/δ ≤ G/16`. -/
theorem dividedKernelFloor_ge_exp {ε γ₀ δ G : ℝ} (hε : 0 ≤ ε) (hγ : 7 ≤ γ₀)
    (hZ : 3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ ≤ G / 16) :
    xiNearLineLowerConst / Real.exp 1 * Real.exp (-(ε * (γ₀ + 1 / 2))) * Real.exp (-(G / 16)) ≤
      dividedKernelFloor (π / 4 - ε) γ₀ δ := by
  unfold dividedKernelFloor
  have hc := xiNearLineLowerConst_pos
  have hQ : 1 ≤ (γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hZe : Real.exp (-(G / 16)) ≤ Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (-(ε * (γ₀ + 1 / 2))) / Real.exp 1 ≤
      Real.exp ((π / 4 - ε) * (γ₀ - 1 / 2)) * Real.exp (-(π * (γ₀ + 1 / 2) / 4)) := by
    rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_lt_four]
  calc xiNearLineLowerConst / Real.exp 1 * Real.exp (-(ε * (γ₀ + 1 / 2))) * Real.exp (-(G / 16))
      = xiNearLineLowerConst * (Real.exp (-(ε * (γ₀ + 1 / 2))) / Real.exp 1) * 1 *
          Real.exp (-(G / 16)) := by ring
    _ ≤ xiNearLineLowerConst * (Real.exp ((π / 4 - ε) * (γ₀ - 1 / 2)) *
          Real.exp (-(π * (γ₀ + 1 / 2) / 4))) * ((γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2)) *
          Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ)) := by
        gcongr
    _ = Real.exp ((π / 4 - ε) * (γ₀ - 1 / 2)) * xiNearLineLowerConst *
          ((γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2)) * Real.exp (-(π * (γ₀ + 1 / 2) / 4)) *
          Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ)) := by ring

/-- The ceiling-to-floor ratio of the divided kernel:
`M_V ≤ m_V exp(3 + log(K₁/c_N) + 3 log(γ₀+2) + m log(4/(3δ)) + 3C log(γ₀+1)/δ)`. -/
theorem dividedKernelCeil_le_floor_mul {ε γ₀ δ : ℝ} {m : ℕ} (hε : 0 ≤ ε)
    (hγ : 7 ≤ γ₀) (hδ : 0 < δ) :
    dividedKernelCeil (π / 4 - ε) γ₀ δ m ≤
      dividedKernelFloor (π / 4 - ε) γ₀ δ * Real.exp (3 +
        Real.log (xiNearLineUpperConst / xiNearLineLowerConst) + 3 * Real.log (γ₀ + 2) +
        m * Real.log (4 / (3 * δ)) + 3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ) := by
  unfold dividedKernelCeil dividedKernelFloor
  have hc := xiNearLineLowerConst_pos
  have hK := xiNearLineUpperConst_pos
  have hQ : 1 ≤ (γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have e1 : Real.exp (Real.log (xiNearLineUpperConst / xiNearLineLowerConst)) =
      xiNearLineUpperConst / xiNearLineLowerConst := Real.exp_log (by positivity)
  have e2 : Real.exp (3 * Real.log (γ₀ + 2)) = (γ₀ + 2) ^ 3 := by
    rw [show (3 : ℝ) * Real.log (γ₀ + 2) = ((3 : ℕ) : ℝ) * Real.log (γ₀ + 2) by norm_num,
      ← Real.log_pow, Real.exp_log (by positivity)]
  have e3 : Real.exp (m * Real.log (4 / (3 * δ))) = (4 / (3 * δ)) ^ m := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have e4 : Real.exp (3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ) *
      Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ)) = 1 := by
    rw [← Real.exp_add]; simp
  set Z := Real.exp (-(3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ))
  set Zi := Real.exp (3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ)
  have hsplit : Real.exp (3 + Real.log (xiNearLineUpperConst / xiNearLineLowerConst) +
      3 * Real.log (γ₀ + 2) + m * Real.log (4 / (3 * δ)) +
      3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ) =
      Real.exp 3 * (xiNearLineUpperConst / xiNearLineLowerConst) * (γ₀ + 2) ^ 3 *
        (4 / (3 * δ)) ^ m * Zi := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, e1, e2, e3]
  rw [hsplit]
  have hexp : Real.exp ((π / 4 - ε) * (γ₀ + 1)) * Real.exp (-(π * (γ₀ - 1) / 4)) ≤
      Real.exp ((π / 4 - ε) * (γ₀ - 1 / 2)) * Real.exp (-(π * (γ₀ + 1 / 2) / 4)) *
        Real.exp 3 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_lt_four]
  have hZZ : Z * Zi = 1 := by rw [mul_comm]; exact e4
  have hP0 : 0 ≤ xiNearLineUpperConst * (γ₀ + 2) ^ 3 * (4 / (3 * δ)) ^ m := by positivity
  calc Real.exp ((π / 4 - ε) * (γ₀ + 1)) * xiNearLineUpperConst * (γ₀ + 2) ^ 3 *
        Real.exp (-(π * (γ₀ - 1) / 4)) * (4 / (3 * δ)) ^ m
      = (Real.exp ((π / 4 - ε) * (γ₀ + 1)) * Real.exp (-(π * (γ₀ - 1) / 4))) *
          (xiNearLineUpperConst * (γ₀ + 2) ^ 3 * (4 / (3 * δ)) ^ m) := by ring
    _ ≤ (Real.exp ((π / 4 - ε) * (γ₀ - 1 / 2)) * Real.exp (-(π * (γ₀ + 1 / 2) / 4)) *
          Real.exp 3) * (xiNearLineUpperConst * (γ₀ + 2) ^ 3 * (4 / (3 * δ)) ^ m) *
          ((γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2)) := by
        have := mul_le_mul_of_nonneg_right hexp hP0
        refine this.trans ?_
        exact le_mul_of_one_le_right (by positivity) hQ
    _ = Real.exp ((π / 4 - ε) * (γ₀ - 1 / 2)) * xiNearLineLowerConst *
          ((γ₀ - 1 / 2) ^ 2 / (γ₀ + 3 / 2)) * Real.exp (-(π * (γ₀ + 1 / 2) / 4)) * Z *
          (Real.exp 3 * (xiNearLineUpperConst / xiNearLineLowerConst) * (γ₀ + 2) ^ 3 *
            (4 / (3 * δ)) ^ m * Zi) := by
        field_simp
        rw [show Z * Zi = 1 from hZZ] at *
        ring_nf
        nlinarith [hZZ]

/-- `B + aL ≤ κ e^{2L}` for all large `L`. -/
theorem exists_level_affine_le_exp {B a κ : ℝ} (hB : 0 ≤ B) (hκ : 0 < κ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → B + a * L ≤ κ * Real.exp (2 * L) := by
  refine ⟨max 1 ((B + a) / (2 * κ)), le_max_left _ _, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : (B + a) / (2 * κ) ≤ L := le_trans (le_max_right _ _) hL
  have hexp := two_mul_sq_le_exp_two_mul (by linarith : (0 : ℝ) ≤ L)
  have hk : B + a ≤ 2 * κ * L := by
    rw [div_le_iff₀ (by positivity)] at hL2; linarith
  have h1 : B + a * L ≤ (B + a) * L := by nlinarith
  have h2 : (B + a) * L ≤ 2 * κ * L * L := mul_le_mul_of_nonneg_right hk (by linarith)
  have h3 : 2 * κ * L * L ≤ κ * Real.exp (2 * L) := by
    have := mul_le_mul_of_nonneg_left hexp hκ.le
    nlinarith
  linarith

/-- `K e^{cL} e^{-kQ} ≤ e^{-Q}/4` once `log(4K) + cL ≤ (k-1) Q`. -/
theorem small_of_log_le {K c k Q L : ℝ} (hK : 0 < K)
    (h : Real.log (4 * K) + c * L ≤ (k - 1) * Q) :
    K * Real.exp (c * L) * Real.exp (-(k * Q)) ≤ Real.exp (-Q) / 4 := by
  have h1 : 4 * K * Real.exp (c * L) ≤ Real.exp ((k - 1) * Q) := by
    calc 4 * K * Real.exp (c * L) = Real.exp (Real.log (4 * K) + c * L) := by
          rw [Real.exp_add, Real.exp_log (by positivity)]
      _ ≤ Real.exp ((k - 1) * Q) := Real.exp_le_exp.mpr h
  have h2 : Real.exp ((k - 1) * Q) * Real.exp (-(k * Q)) = Real.exp (-Q) := by
    rw [← Real.exp_add]; ring_nf
  have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(k * Q))).le
  rw [h2] at h3
  linarith

theorem self_le_exp (x : ℝ) : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]

/-- The variation of the test on the ball relative to its value at the zero. -/
theorem variation_ratio_le {Φ₀ εF β κ0 Lr c X mlow ρT : ℝ} (hΦ : mlow ≤ Φ₀) (hm : 0 < mlow)
    (hεF0 : 0 ≤ εF) (hεF : εF ≤ ρT * mlow) (hρT : ρT ≤ 1 / 2) (hβ : 0 ≤ β) (hc : 0 < c)
    (hκ0 : c ≤ κ0) (hLr0 : 0 ≤ Lr) (hLr : Lr ≤ c) (hX : (Φ₀ - εF) * κ0 ≤ X) :
    (β * Φ₀ + 2 * εF) * (κ0 + Lr) + (Φ₀ + εF) * Lr ≤ X * (4 * β + 8 * ρT + 4 * (Lr / c)) := by
  have hΦ0 : 0 < Φ₀ := lt_of_lt_of_le hm hΦ
  have hκ : 0 < κ0 := lt_of_lt_of_le hc hκ0
  have hεΦ : εF ≤ ρT * Φ₀ := hεF.trans (mul_le_mul_of_nonneg_left hΦ (by
    have := mul_nonneg (le_trans hεF0 hεF) hm.le
    nlinarith [hεF0, hεF]))
  have hε2 : εF ≤ Φ₀ / 2 := by nlinarith
  have hXl : Φ₀ / 2 * κ0 ≤ X := le_trans (mul_le_mul_of_nonneg_right (by linarith) hκ.le) hX
  have hLκ : Lr ≤ κ0 := hLr.trans hκ0
  have hLc : Lr / c * c = Lr := div_mul_cancel₀ _ hc.ne'
  have hLκ' : Lr ≤ Lr / c * κ0 := by
    calc Lr = Lr / c * c := hLc.symm
      _ ≤ Lr / c * κ0 := mul_le_mul_of_nonneg_left hκ0 (div_nonneg hLr0 hc.le)
  have hρ0 : 0 ≤ ρT := by
    by_contra h; push Not at h
    have : ρT * mlow < 0 := mul_neg_of_neg_of_pos h hm
    linarith
  calc (β * Φ₀ + 2 * εF) * (κ0 + Lr) + (Φ₀ + εF) * Lr
      ≤ (β * Φ₀ + 2 * (ρT * Φ₀)) * (2 * κ0) + (2 * Φ₀) * (Lr / c * κ0) := by
        apply add_le_add
        · exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
        · exact mul_le_mul (by linarith) hLκ' hLr0 (by positivity)
    _ = (Φ₀ / 2 * κ0) * (4 * β + 8 * ρT + 4 * (Lr / c)) := by ring
    _ ≤ X * (4 * β + 8 * ρT + 4 * (Lr / c)) := by
        apply mul_le_mul_of_nonneg_right hXl
        have : 0 ≤ Lr / c := div_nonneg hLr0 hc.le
        positivity

/-- The total error of the two-sided mass bound. -/
theorem energy_total_le {εF εΦ T TF ρT mlow a P X κ0 κl : ℝ} (hεF0 : 0 ≤ εF) (hεF : εF ≤ TF)
    (hεΦ0 : 0 ≤ εΦ) (hεΦ : εΦ ≤ T) (hTρ : T ≤ ρT * mlow) (hTFρ : TF ≤ ρT * mlow)
    (hm0 : 0 < mlow) (ha1 : 1 ≤ a) (hP0 : 0 ≤ P) (hX : mlow / 2 * κ0 ≤ X)
    (hκl0 : 0 < κl) (hκl : κl ≤ κ0) :
    εF ^ 2 * P + 2 * a ^ 2 * (T ^ 2 * P) + 2 * (a * εΦ + εF) ^ 2 * P ≤
      44 * a ^ 2 * ρT ^ 2 * (P / κl ^ 2) * X ^ 2 := by
  have hT0 : 0 ≤ T := hεΦ0.trans hεΦ
  have hTF0 : 0 ≤ TF := hεF0.trans hεF
  have hρm : 0 ≤ ρT * mlow := hT0.trans hTρ
  have ha0 : 0 ≤ a := by linarith
  set q := ρT * mlow with hq
  have hb : a * εΦ + εF ≤ a * q + q :=
    add_le_add (mul_le_mul_of_nonneg_left (hεΦ.trans hTρ) ha0) (hεF.trans hTFρ)
  have hb0 : 0 ≤ a * εΦ + εF := by positivity
  have hb2 : (a * εΦ + εF) ^ 2 ≤ (2 * a * q) ^ 2 := by
    apply pow_le_pow_left₀ hb0
    have : q ≤ a * q := le_mul_of_one_le_left hρm ha1
    linarith
  have hεF2 : εF ^ 2 ≤ (a * q) ^ 2 := by
    apply pow_le_pow_left₀ hεF0
    exact (hεF.trans hTFρ).trans (le_mul_of_one_le_left hρm ha1)
  have hT2 : T ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hT0 hTρ 2
  have h1 : εF ^ 2 * P + 2 * a ^ 2 * (T ^ 2 * P) + 2 * (a * εΦ + εF) ^ 2 * P ≤
      11 * (a * q) ^ 2 * P := by
    have e1 : εF ^ 2 * P ≤ (a * q) ^ 2 * P := mul_le_mul_of_nonneg_right hεF2 hP0
    have e2 : 2 * a ^ 2 * (T ^ 2 * P) ≤ 2 * a ^ 2 * (q ^ 2 * P) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT2 hP0) (by positivity)
    have e3 : 2 * (a * εΦ + εF) ^ 2 * P ≤ 2 * (2 * a * q) ^ 2 * P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (by norm_num)) hP0
    have e4 : (a * q) ^ 2 * P + 2 * a ^ 2 * (q ^ 2 * P) + 2 * (2 * a * q) ^ 2 * P =
        11 * (a * q) ^ 2 * P := by ring
    linarith
  have hκ0 : 0 < κ0 := lt_of_lt_of_le hκl0 hκl
  have hX0 : 0 ≤ X := le_trans (by positivity) hX
  have hmX : mlow ≤ 2 * X / κ0 := by
    rw [le_div_iff₀ hκ0]; linarith
  have hmX' : mlow ≤ 2 * X / κl := hmX.trans (div_le_div_of_nonneg_left (by positivity) hκl0 hκl)
  have hm2 : mlow ^ 2 ≤ (2 * X / κl) ^ 2 := pow_le_pow_left₀ hm0.le hmX' 2
  calc εF ^ 2 * P + 2 * a ^ 2 * (T ^ 2 * P) + 2 * (a * εΦ + εF) ^ 2 * P
      ≤ 11 * (a * q) ^ 2 * P := h1
    _ = 11 * a ^ 2 * ρT ^ 2 * P * mlow ^ 2 := by rw [hq]; ring
    _ ≤ 11 * a ^ 2 * ρT ^ 2 * P * (2 * X / κl) ^ 2 :=
        mul_le_mul_of_nonneg_left hm2 (by positivity)
    _ = 44 * a ^ 2 * ρT ^ 2 * (P / κl ^ 2) * X ^ 2 := by field_simp; ring

/-- The resolvent test and its two comparison tests are Hodge-class tests at level `L`. -/
theorem resolvent_tests_hodge {L θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {F : ℝ → ℂ}
    (hF : SuperExpDecay F) {U w γ₀ : ℝ} (hw : 0 < w) (hUL : U + w ≤ L) (hwL : w ≤ L) :
    IsHodgeTest L (bumpedTest (cutoffCore U F) w γ₀) ∧
    IsHodgeTest L (bumpedTest (cutoffCore U (tiltedPhi θ)) w γ₀) ∧
    IsHodgeTest L (scaledBumpPolarFree w γ₀) := by
  have hdecay := superExpDecay_tiltedRiemannKernel hθ0 hθ
  have hsuppF : ∀ u, U < |u| → cutoffCore U F u = 0 := fun u hu => cutoffCore_eq_zero hu
  have hsuppΦ : ∀ u, U < |u| → cutoffCore U (tiltedPhi θ) u = 0 := fun u hu => cutoffCore_eq_zero hu
  have hintF := integrable_cutoffCore (U := U) hF.1
  have hintΦ := integrable_cutoffCore (U := U) hdecay.1
  exact ⟨⟨contDiff_bumpedTest hintF hw γ₀, tsupport_bumpedTest hsuppF hw γ₀ hUL,
    paperFT_bumpedTest_half_I hintF hsuppF hw γ₀, paperFT_bumpedTest_neg_half_I hintF hsuppF hw γ₀⟩,
    ⟨contDiff_bumpedTest hintΦ hw γ₀, tsupport_bumpedTest hsuppΦ hw γ₀ hUL,
    paperFT_bumpedTest_half_I hintΦ hsuppΦ hw γ₀, paperFT_bumpedTest_neg_half_I hintΦ hsuppΦ hw γ₀⟩,
    ⟨contDiff_scaledBumpPolarFree w γ₀, tsupport_scaledBumpPolarFree hw γ₀ hwL,
    paperFT_scaledBumpPolarFree_half_I hw γ₀, paperFT_scaledBumpPolarFree_neg_half_I hw γ₀⟩⟩

/-- The value of the resolvent test at the zero: `|f̂(γ₀)| ≥ (|F̂(γ₀)| - ε_F) |κ̂₂(γ₀)|` and
`|κ̂₂(γ₀)| ≥ (γ₀² + 1/4) · 4w c₀`. -/
theorem resolvent_test_value_ge {F : ℝ → ℂ} (hF : SuperExpDecay F) {U w γ₀ : ℝ} (hw : 0 < w)
    (hw4 : 4 * w ≤ 1) :
    (‖paperFT F (γ₀ : ℂ)‖ - expTail F (1 / 2) U) * ‖paperFT (scaledBumpPolarFree w γ₀) (γ₀ : ℂ)‖ ≤
      ‖paperFT (bumpedTest (cutoffCore U F) w γ₀) (γ₀ : ℂ)‖ ∧
    (γ₀ ^ 2 + 1 / 4) * (4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u))) ≤
      ‖paperFT (scaledBumpPolarFree w γ₀) (γ₀ : ℂ)‖ := by
  have hsuppF : ∀ u, U < |u| → cutoffCore U F u = 0 := fun u hu => cutoffCore_eq_zero hu
  have hintF := integrable_cutoffCore (U := U) hF.1
  refine ⟨?_, ?_⟩
  · rw [paperFT_bumpedTest hintF hsuppF hw, paperFT_cutoffCore_eq hF, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h1 := norm_paperFT_cutoffTail_le (U := U) hF (z := (γ₀ : ℂ)) (by simp)
    have h2 := norm_sub_norm_le (paperFT F (γ₀ : ℂ)) (paperFT (cutoffTail U F) (γ₀ : ℂ))
    linarith
  · rw [paperFT_scaledBumpPolarFree hw, sub_self, norm_mul, norm_neg]
    have hq : ‖(γ₀ : ℂ) ^ 2 + 1 / 4‖ = γ₀ ^ 2 + 1 / 4 := by
      rw [show (γ₀ : ℂ) ^ 2 + 1 / 4 = ((γ₀ ^ 2 + 1 / 4 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hq]
    have h0 := norm_paperFT_scaledBump_real_ge hw hw4 (s := 0) (by simp)
    simp only [Complex.ofReal_zero] at h0
    exact mul_le_mul_of_nonneg_left h0 (by positivity)

/-- The Weil energies of the three tests. -/
theorem resolvent_tests_energy {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hline : ρ₀.re = 1 / 2) (hγ7 : 0 ≤ ρ₀.im) {F : ℝ → ℂ} (hF : SuperExpDecay F)
    (hprod : ∀ z : ℂ, (z - (ρ₀.im : ℂ)) ^ (zetaZeroConfig.mult ρ₀) * paperFT F z =
      paperFT (tiltedPhi θ) z)
    {U w T : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1)
    (htail : ∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|) ≤ T) :
    |‖zetaZeroConfig.W (bumpedTest (cutoffCore U F) w ρ₀.im) (bumpedTest (cutoffCore U F) w ρ₀.im)‖ -
        (zetaZeroConfig.mult ρ₀ : ℝ) *
          ‖paperFT (bumpedTest (cutoffCore U F) w ρ₀.im) (ρ₀.im : ℂ)‖ ^ 2| ≤
      expTail F (1 / 2) U ^ 2 * (scaledBumpConst w ^ 2 * (1 + ρ₀.im) ^ 4 *
        (24 * A₀ * Real.log (ρ₀.im + 3))) ∧
    ‖zetaZeroConfig.W (bumpedTest (cutoffCore U (tiltedPhi θ)) w ρ₀.im)
        (bumpedTest (cutoffCore U (tiltedPhi θ)) w ρ₀.im)‖ ≤
      T ^ 2 * (scaledBumpConst w ^ 2 * (1 + ρ₀.im) ^ 4 * (24 * A₀ * Real.log (ρ₀.im + 3))) ∧
    ‖zetaZeroConfig.W (scaledBumpPolarFree w ρ₀.im) (scaledBumpPolarFree w ρ₀.im)‖ ≤
      scaledBumpConst w ^ 2 * (1 + ρ₀.im) ^ 4 * (24 * A₀ * Real.log (ρ₀.im + 3)) := by
  have hγabs : |ρ₀.im| = ρ₀.im := abs_of_nonneg hγ7
  refine ⟨?_, ?_, ?_⟩
  · have h := norm_W_resolventTest_sub_le hA₀ hloc hθ0 hθ hρ₀ hline hF hprod hw hw4 (U := U)
    rw [hγabs] at h
    refine h.trans (le_of_eq ?_); ring
  · have h := norm_W_landauRadicalTest_le hA₀ hloc (U := U) hθ0 hθ hw hw4 ρ₀.im
    rw [hγabs] at h
    have htail0 : 0 ≤ ∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|) :=
      integral_nonneg fun _ => by positivity
    have hsq := pow_le_pow_left₀ htail0 htail 2
    have hP0 : 0 ≤ scaledBumpConst w ^ 2 * (1 + ρ₀.im) ^ 4 * (24 * A₀ * Real.log (ρ₀.im + 3)) := by
      have := scaledBumpConst_nonneg hw
      have : 0 ≤ Real.log (ρ₀.im + 3) := Real.log_nonneg (by linarith)
      have : 0 ≤ A₀ := by linarith
      positivity
    calc _ = ‖zetaZeroConfig.W (landauRadicalTest U θ w ρ₀.im) (landauRadicalTest U θ w ρ₀.im)‖ :=
          rfl
      _ ≤ _ := h
      _ = (∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|)) ^ 2 *
            (scaledBumpConst w ^ 2 * (1 + ρ₀.im) ^ 4 * (24 * A₀ * Real.log (ρ₀.im + 3))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq hP0
  · have h := norm_W_scaledBumpPolarFree_le hA₀ hloc hw hw4 ρ₀.im
    rw [hγabs] at h; exact h

/-- The two measure inequalities for the resolvent test, combined. -/
theorem mass_two_sided_of_representation {L : ℝ} {ν : Measure ℝ} (hν : RepresentsHodgeForm L ν)
    {f g k : ℝ → ℂ} (hfH : IsHodgeTest L f) (hgH : IsHodgeTest L g) (hkH : IsHodgeTest L k)
    {γ₀ r X Δ a b m E₁ Eg Ek : ℝ} (hX : X = ‖paperFT f (γ₀ : ℂ)‖) (hΔX : 4 * Δ ≤ X) (hX0 : 0 < X)
    (hΔball : ∀ τ ∈ Icc (γ₀ - r) (γ₀ + r), ‖paperFT f (τ : ℂ) - paperFT f (γ₀ : ℂ)‖ ≤ Δ)
    (hout : ∀ τ ∉ Icc (γ₀ - r) (γ₀ + r),
      ‖paperFT f (τ : ℂ)‖ ≤ a * ‖paperFT g (τ : ℂ)‖ + b * ‖paperFT k (τ : ℂ)‖)
    (hWf : |‖zetaZeroConfig.W f f‖ - m * X ^ 2| ≤ E₁)
    (hWg : ‖zetaZeroConfig.W g g‖ ≤ Eg) (hWk : ‖zetaZeroConfig.W k k‖ ≤ Ek) :
    ν (Icc (γ₀ - r) (γ₀ + r)) ≠ ⊤ ∧
      (ν (Icc (γ₀ - r) (γ₀ + r))).toReal * (X - Δ) ^ 2 ≤ m * X ^ 2 + E₁ ∧
      m * X ^ 2 - (E₁ + 2 * a ^ 2 * Eg + 2 * b ^ 2 * Ek) ≤
        (ν (Icc (γ₀ - r) (γ₀ + r))).toReal * (X + Δ) ^ 2 := by
  set Bs := Icc (γ₀ - r) (γ₀ + r)
  have hℓ : 0 < X - Δ := by linarith
  have hlowB : ∀ τ ∈ Bs, X - Δ ≤ ‖paperFT f (τ : ℂ)‖ := by
    intro τ hτ
    have h1 := hΔball τ hτ
    have h2 := norm_sub_norm_le (paperFT f (γ₀ : ℂ)) (paperFT f (τ : ℂ))
    rw [norm_sub_rev] at h2
    rw [hX]; linarith
  have hup := measure_le_of_representation hν hfH measurableSet_Icc hℓ hlowB
  have hνfin : ν Bs ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  have hinB : ∀ τ ∈ Bs, ‖paperFT f (τ : ℂ)‖ ≤ X + Δ := by
    intro τ hτ
    have h1 := hΔball τ hτ
    have h2 := norm_le_insert' (paperFT f (τ : ℂ)) (paperFT f (γ₀ : ℂ))
    rw [hX]; linarith
  have hlowW := norm_W_le_of_representation hν hfH hgH hkH measurableSet_Icc hνfin hinB hout
  refine ⟨hνfin, ?_, ?_⟩
  · have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity) hup
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 := (abs_le.mp hWf).2
    linarith
  · have h1 := (abs_le.mp hWf).1
    have h2 : 2 * a ^ 2 * ‖zetaZeroConfig.W g g‖ ≤ 2 * a ^ 2 * Eg :=
      mul_le_mul_of_nonneg_left hWg (by positivity)
    have h3 : 2 * b ^ 2 * ‖zetaZeroConfig.W k k‖ ≤ 2 * b ^ 2 * Ek :=
      mul_le_mul_of_nonneg_left hWk (by positivity)
    linarith

/-- The test is nonzero at the zero and nearly constant on the ball. -/
theorem delta_small_core {M X Φ₀ εF κ0 κl c Lr β ρT mlow a P : ℝ} (hmM : 0 ≤ M) (hc : 0 < c)
    (hκlc : c ≤ κl) (hκ0low : κl ≤ κ0) (hXlow : (Φ₀ - εF) * κ0 ≤ X) (hεF0 : 0 ≤ εF)
    (hm0 : 0 < mlow) (hΦ₀ : mlow ≤ Φ₀) (hεF : εF ≤ ρT * mlow) (hρT : ρT ≤ 1 / 2)
    (hβ0 : 0 ≤ β) (hLr0 : 0 ≤ Lr) (hLr : Lr ≤ c) (hP0 : 0 ≤ P) (hκl0 : 0 < κl)
    (hsmall : 6 * (M + 2) * (4 * β + 8 * ρT + 4 * (Lr / c)) +
      3 * (44 * a ^ 2 * ρT ^ 2 * (P / κl ^ 2)) ≤ 1 / 4) :
    0 < X ∧ 4 * ((β * Φ₀ + 2 * εF) * (κ0 + Lr) + (Φ₀ + εF) * Lr) ≤ X := by
  have hκ0c : c ≤ κ0 := hκlc.trans hκ0low
  have hρ0 : 0 ≤ ρT := by
    by_contra h; push Not at h
    have : ρT * mlow < 0 := mul_neg_of_neg_of_pos h hm0
    linarith
  have hεFm : εF ≤ mlow / 2 := by
    calc εF ≤ ρT * mlow := hεF
      _ ≤ 1 / 2 * mlow := mul_le_mul_of_nonneg_right hρT hm0.le
      _ = mlow / 2 := by ring
  have hκ0pos : 0 < κ0 := lt_of_lt_of_le hc hκ0c
  have hXpos : mlow / 2 * κ0 ≤ X := le_trans (mul_le_mul_of_nonneg_right (by linarith) hκ0pos.le)
    hXlow
  have hX0 : 0 < X := lt_of_lt_of_le (mul_pos (by positivity) hκ0pos) hXpos
  refine ⟨hX0, ?_⟩
  have hΔX := variation_ratio_le hΦ₀ hm0 hεF0 hεF hρT hβ0 hc hκ0c hLr0 hLr hXlow
  have htb0 : 0 ≤ 4 * β + 8 * ρT + 4 * (Lr / c) := by
    have : 0 ≤ Lr / c := div_nonneg hLr0 hc.le
    linarith
  have heb0 : 0 ≤ 3 * (44 * a ^ 2 * ρT ^ 2 * (P / κl ^ 2)) := by positivity
  have h6 : 1 ≤ 6 * (M + 2) := by linarith
  have htb4 : 4 * β + 8 * ρT + 4 * (Lr / c) ≤ 1 / 4 := by
    have h1 := le_mul_of_one_le_left htb0 h6
    linarith
  have : X * (4 * β + 8 * ρT + 4 * (Lr / c)) ≤ X * (1 / 4) :=
    mul_le_mul_of_nonneg_left htb4 hX0.le
  linarith

/-- **The mass law, arithmetic core.**  Abstract form of the final estimate. -/
theorem mass_estimate_core {νB m M X Φ₀ εF εΦ κ0 κl c Lr β ρT mlow a T TF P ϑ E₁ Eg Ek : ℝ}
    (hν0 : 0 ≤ νB) (hm0' : 0 ≤ m) (hmM : m ≤ M) (hc : 0 < c) (hκl0 : 0 < κl) (hκlc : c ≤ κl)
    (hκ0low : κl ≤ κ0) (hXlow : (Φ₀ - εF) * κ0 ≤ X) (hεF0 : 0 ≤ εF) (hεΦ0 : 0 ≤ εΦ)
    (hεF : εF ≤ TF) (hεΦ : εΦ ≤ T) (hm0 : 0 < mlow) (hΦ₀ : mlow ≤ Φ₀)
    (hTρ : T ≤ ρT * mlow) (hTFρ : TF ≤ ρT * mlow) (hρT : ρT ≤ 1 / 2) (hβ0 : 0 ≤ β)
    (hLr0 : 0 ≤ Lr) (hLr : Lr ≤ c) (ha1 : 1 ≤ a) (hP0 : 0 ≤ P)
    (hE₁ : E₁ = εF ^ 2 * P) (hEg : Eg = T ^ 2 * P) (hEk : Ek = P)
    (hsmall : 6 * (M + 2) * (4 * β + 8 * ρT + 4 * (Lr / c)) +
      3 * (44 * a ^ 2 * ρT ^ 2 * (P / κl ^ 2)) ≤ min (1 / 4) ϑ)
    (hup : νB * (X - ((β * Φ₀ + 2 * εF) * (κ0 + Lr) + (Φ₀ + εF) * Lr)) ^ 2 ≤ m * X ^ 2 + E₁)
    (hlow : m * X ^ 2 - (E₁ + 2 * a ^ 2 * Eg + 2 * (a * εΦ + εF) ^ 2 * Ek) ≤
      νB * (X + ((β * Φ₀ + 2 * εF) * (κ0 + Lr) + (Φ₀ + εF) * Lr)) ^ 2) :
    |νB - m| ≤ ϑ := by
  have hκ0c : c ≤ κ0 := hκlc.trans hκ0low
  have hρ0 : 0 ≤ ρT := by
    by_contra h; push Not at h
    have : ρT * mlow < 0 := mul_neg_of_neg_of_pos h hm0
    linarith [hεF0.trans hεF]
  have hεFm : εF ≤ mlow / 2 := by
    calc εF ≤ ρT * mlow := hεF.trans hTFρ
      _ ≤ 1 / 2 * mlow := mul_le_mul_of_nonneg_right hρT hm0.le
      _ = mlow / 2 := by ring
  have hκ0pos : 0 < κ0 := lt_of_lt_of_le hc hκ0c
  have hXpos : mlow / 2 * κ0 ≤ X := le_trans (mul_le_mul_of_nonneg_right (by linarith) hκ0pos.le)
    hXlow
  have hX0 : 0 < X := lt_of_lt_of_le (mul_pos (by positivity) hκ0pos) hXpos
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ, Δ = (β * Φ₀ + 2 * εF) * (κ0 + Lr) + (Φ₀ + εF) * Lr := ⟨_, rfl⟩
  rw [← hΔdef] at hup hlow
  obtain ⟨tb, htb⟩ : ∃ tb, tb = 4 * β + 8 * ρT + 4 * (Lr / c) := ⟨_, rfl⟩
  have hΔX : Δ ≤ X * tb := by
    rw [hΔdef, htb]
    exact variation_ratio_le hΦ₀ hm0 hεF0 (hεF.trans hTFρ) hρT hβ0 hc hκ0c hLr0 hLr hXlow
  have hΦ0 : 0 ≤ Φ₀ := hm0.le.trans hΦ₀
  have hΔ0 : 0 ≤ Δ := by rw [hΔdef]; positivity
  obtain ⟨eb, heb⟩ : ∃ eb, eb = 44 * a ^ 2 * ρT ^ 2 * (P / κl ^ 2) := ⟨_, rfl⟩
  rw [← htb, ← heb] at hsmall
  have heb0 : 0 ≤ eb := by rw [heb]; positivity
  have htb0 : 0 ≤ tb := by
    rw [htb]; have : 0 ≤ Lr / c := div_nonneg hLr0 hc.le
    linarith
  have hMpos : 0 ≤ M := hm0'.trans hmM
  have hsum4 := hsmall.trans (min_le_left _ _)
  have h6 : 1 ≤ 6 * (M + 2) := by linarith
  have htb4 : tb ≤ 1 / 4 := by
    have h1 : tb ≤ 6 * (M + 2) * tb := le_mul_of_one_le_left htb0 h6
    linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) heb0]
  have heb1 : eb ≤ 1 := by
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 6 * (M + 2)) htb0]
  have hΔX4 : 4 * Δ ≤ X := by
    have : X * tb ≤ X * (1 / 4) := mul_le_mul_of_nonneg_left htb4 hX0.le
    linarith
  have hEtb := energy_total_le hεF0 hεF hεΦ0 hεΦ hTρ hTFρ hm0 ha1 hP0 hXpos hκl0 hκ0low
  rw [← heb] at hEtb
  obtain ⟨Et, hEt⟩ : ∃ Et, Et = εF ^ 2 * P + 2 * a ^ 2 * (T ^ 2 * P) +
      2 * (a * εΦ + εF) ^ 2 * P := ⟨_, rfl⟩
  rw [← hEt] at hEtb
  have hT0 : 0 ≤ T := hεΦ0.trans hεΦ
  have hEt0 : 0 ≤ Et := by rw [hEt]; positivity
  have hEX : Et ≤ X ^ 2 := by
    calc Et ≤ eb * X ^ 2 := hEtb
      _ ≤ 1 * X ^ 2 := mul_le_mul_of_nonneg_right heb1 (sq_nonneg _)
      _ = X ^ 2 := one_mul _
  have hE1 : E₁ ≤ Et := by
    rw [hE₁, hEt]
    have : 0 ≤ 2 * a ^ 2 * (T ^ 2 * P) := by positivity
    have : 0 ≤ 2 * (a * εΦ + εF) ^ 2 * P := by positivity
    linarith
  have hup3 : νB * (X - Δ) ^ 2 ≤ m * X ^ 2 + Et := by linarith
  have hlow3 : m * X ^ 2 - Et ≤ νB * (X + Δ) ^ 2 := by
    have e : E₁ + 2 * a ^ 2 * Eg + 2 * (a * εΦ + εF) ^ 2 * Ek = Et := by
      rw [hE₁, hEg, hEk, hEt]
    rw [e] at hlow; exact hlow
  have hmass := mass_close_of_two_sided hν0 hm0' hmM hX0 hΔ0 hΔX4 hEt0 hEX hup3 hlow3
  have hΔXr : Δ / X ≤ tb := by rw [div_le_iff₀ hX0]; linarith
  have hEXr : Et / X ^ 2 ≤ eb := by rw [div_le_iff₀ (by positivity)]; exact hEtb
  calc |νB - m| ≤ 6 * (M + 2) * (Δ / X) + 3 * (Et / X ^ 2) := hmass
    _ ≤ 6 * (M + 2) * tb + 3 * eb := by
        have h1 : 6 * (M + 2) * (Δ / X) ≤ 6 * (M + 2) * tb :=
          mul_le_mul_of_nonneg_left hΔXr (by linarith)
        have h2 : 3 * (Et / X ^ 2) ≤ 3 * eb := mul_le_mul_of_nonneg_left hEXr (by norm_num)
        linarith
    _ ≤ ϑ := hsmall.trans (min_le_right _ _)

/-- **The mass law, analytic core.**  Given the tail, floor and variation bounds for the
resolvent test at an on-line zero, the mass of any representing measure on the ball
`[γ₀ - r, γ₀ + r]` is the multiplicity up to `ϑ`. -/
theorem krein_mass_core {L : ℝ} {ν : Measure ℝ} (hν : RepresentsHodgeForm L ν)
    {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hline : ρ₀.re = 1 / 2) (hγ7 : 7 ≤ ρ₀.im) {F : ℝ → ℂ} (hF : SuperExpDecay F)
    (hprod : ∀ z : ℂ, (z - (ρ₀.im : ℂ)) ^ (zetaZeroConfig.mult ρ₀) * paperFT F z =
      paperFT (tiltedPhi θ) z)
    {U w r M T TF ρT mlow β ϑ : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) (hUL : U + w ≤ L)
    (hwL : w ≤ L) (hr0 : 0 < r) (hr1 : r ≤ 1) (hmM : (zetaZeroConfig.mult ρ₀ : ℝ) ≤ M)
    (hβ0 : 0 ≤ β)
    (hvar : ∀ τ : ℝ, |τ - ρ₀.im| ≤ r →
      ‖paperFT F (τ : ℂ) - paperFT F (ρ₀.im : ℂ)‖ ≤ β * ‖paperFT F (ρ₀.im : ℂ)‖)
    (htail : ∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|) ≤ T)
    (hεΦ : expTail (tiltedPhi θ) (1 / 2) U ≤ T) (hεF : expTail F (1 / 2) U ≤ TF)
    (hm0 : 0 < mlow) (hΦ₀ : mlow ≤ ‖paperFT F (ρ₀.im : ℂ)‖)
    (hTρ : T ≤ ρT * mlow) (hTFρ : TF ≤ ρT * mlow) (hρT : ρT ≤ 1 / 2)
    (hLr : bumpLipConst w ρ₀.im * r ≤ 4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u)))
    (hsmall : 6 * (M + 2) * (4 * β + 8 * ρT + 4 * (bumpLipConst w ρ₀.im * r /
        (4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u))))) +
      3 * (44 * ((r ^ (zetaZeroConfig.mult ρ₀))⁻¹) ^ 2 * ρT ^ 2 *
        (scaledBumpConst w ^ 2 * (1 + ρ₀.im) ^ 4 * (24 * A₀ * Real.log (ρ₀.im + 3)) /
          ((ρ₀.im ^ 2 + 1 / 4) * (4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u)))) ^ 2)) ≤
        min (1 / 4) ϑ) :
    ν (Icc (ρ₀.im - r) (ρ₀.im + r)) ≠ ⊤ ∧
      |(ν (Icc (ρ₀.im - r) (ρ₀.im + r))).toReal - (zetaZeroConfig.mult ρ₀ : ℝ)| ≤ ϑ := by
  have hc₀0 : 0 < Real.cos (1 / 8) * (∫ u, weilBump u) := by
    have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
    have hcos : 0 < Real.cos (1 / 8) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    positivity
  obtain ⟨hfH, hgH, hkH⟩ := resolvent_tests_hodge (γ₀ := ρ₀.im) hθ0 hθ hF hw hUL hwL
  obtain ⟨hXlow, hκ0low⟩ := resolvent_test_value_ge (U := U) (γ₀ := ρ₀.im) hF hw hw4
  obtain ⟨hWf, hWg, hWk⟩ := resolvent_tests_energy hA₀ hloc hθ0 hθ hρ₀ hline
    (by linarith only [hγ7]) hF hprod hw hw4 htail
  have hΔball : ∀ τ ∈ Icc (ρ₀.im - r) (ρ₀.im + r),
      ‖paperFT (bumpedTest (cutoffCore U F) w ρ₀.im) (τ : ℂ) -
        paperFT (bumpedTest (cutoffCore U F) w ρ₀.im) (ρ₀.im : ℂ)‖ ≤
      (β * ‖paperFT F (ρ₀.im : ℂ)‖ + 2 * expTail F (1 / 2) U) *
          (‖paperFT (scaledBumpPolarFree w ρ₀.im) (ρ₀.im : ℂ)‖ + bumpLipConst w ρ₀.im * r) +
        (‖paperFT F (ρ₀.im : ℂ)‖ + expTail F (1 / 2) U) * (bumpLipConst w ρ₀.im * r) :=
    fun τ hτ => norm_paperFT_resolventTest_sub_le hF hw hvar
      (abs_le.mpr ⟨by linarith only [hτ.1], by linarith only [hτ.2]⟩) hr1
  have hout : ∀ τ ∉ Icc (ρ₀.im - r) (ρ₀.im + r),
      ‖paperFT (bumpedTest (cutoffCore U F) w ρ₀.im) (τ : ℂ)‖ ≤
        (r ^ zetaZeroConfig.mult ρ₀)⁻¹ *
          ‖paperFT (bumpedTest (cutoffCore U (tiltedPhi θ)) w ρ₀.im) (τ : ℂ)‖ +
        ((r ^ zetaZeroConfig.mult ρ₀)⁻¹ * expTail (tiltedPhi θ) (1 / 2) U +
          expTail F (1 / 2) U) * ‖paperFT (scaledBumpPolarFree w ρ₀.im) (τ : ℂ)‖ := by
    intro τ hτ
    have hτr : r ≤ |τ - ρ₀.im| := by
      by_contra h; push Not at h
      exact hτ ⟨by linarith only [(abs_lt.mp h).1], by linarith only [(abs_lt.mp h).2]⟩
    exact norm_paperFT_resolventTest_le hθ0 hθ hF hprod hw hr0 hτr
  have hLr0 : 0 ≤ bumpLipConst w ρ₀.im * r := by unfold bumpLipConst; positivity
  have ha1 : 1 ≤ (r ^ zetaZeroConfig.mult ρ₀)⁻¹ :=
    (one_le_inv₀ (pow_pos hr0 _)).mpr (pow_le_one₀ hr0.le hr1)
  have hlog3 : 0 ≤ Real.log (ρ₀.im + 3) := Real.log_nonneg (by linarith only [hγ7])
  have hA0 : 0 ≤ A₀ := by linarith only [hA₀]
  have hP0 : 0 ≤ scaledBumpConst w ^ 2 * (1 + ρ₀.im) ^ 4 * (24 * A₀ * Real.log (ρ₀.im + 3)) := by
    have := scaledBumpConst_nonneg hw
    positivity
  have h1γ : 1 ≤ ρ₀.im ^ 2 + 1 / 4 := by nlinarith only [hγ7]
  have hκlc : 4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u)) ≤
      (ρ₀.im ^ 2 + 1 / 4) * (4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u))) := by
    calc 4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u))
        = 1 * (4 * w * (Real.cos (1 / 8) * (∫ u, weilBump u))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1γ (by positivity)
  have hmM0 : 0 ≤ M := le_trans (Nat.cast_nonneg _) hmM
  obtain ⟨hX0, hΔX4⟩ := delta_small_core hmM0 (by positivity) hκlc hκ0low hXlow
    (expTail_nonneg _ _ _) hm0 hΦ₀ (hεF.trans hTFρ) hρT hβ0 hLr0 hLr hP0
    (by positivity) (hsmall.trans (min_le_left _ _))
  obtain ⟨hνfin, hup, hlow⟩ := mass_two_sided_of_representation hν hfH hgH hkH rfl hΔX4 hX0
    hΔball hout hWf hWg hWk
  refine ⟨hνfin, ?_⟩
  exact mass_estimate_core ENNReal.toReal_nonneg (Nat.cast_nonneg _) hmM (by positivity)
    (by positivity) hκlc hκ0low hXlow (expTail_nonneg _ _ _) (expTail_nonneg _ _ _) hεF hεΦ
    hm0 hΦ₀ hTρ hTFρ hρT hβ0 hLr0 hLr ha1 hP0 rfl rfl rfl hsmall hup hlow

/-! ## Exponent bookkeeping -/

/-- The tails are small against the floor: `T, T_F ≤ ρ_T m_low`. -/
theorem tails_le_rho {M : ℕ} {Mθ cN KR L R G ε γ₀ : ℝ} (hMθ : 0 ≤ Mθ) (hcN : 0 < cN)
    (hKR : KR = 2 ^ (M + 1) * Mθ * Real.exp (3 / 2) / cN + 1) (hL : 0 ≤ L)
    (hε1 : ε ≤ 1) (hgain : G / 2 - ε / 2 ≤ R - ε * (γ₀ + 1 / 2)) :
    2 * Mθ * Real.exp (6 * L) * Real.exp (-R) ≤
      2 ^ (M + 1) * Mθ * Real.exp ((6 + 2 * M) * L) * Real.exp (-R) ∧
    2 ^ (M + 1) * Mθ * Real.exp ((6 + 2 * M) * L) * Real.exp (-R) ≤
      (KR * Real.exp ((6 + 2 * M) * L) * Real.exp (-(7 * G / 16))) *
        (cN / Real.exp 1 * Real.exp (-(ε * (γ₀ + 1 / 2))) * Real.exp (-(G / 16))) := by
  have h2 : (2 : ℝ) ≤ 2 ^ (M + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (M + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨?_, ?_⟩
  · have he : Real.exp (6 * L) ≤ Real.exp ((6 + 2 * M) * L) :=
      Real.exp_le_exp.mpr (by nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])
    have := Real.exp_pos (-R)
    gcongr
  · have hR : Real.exp (-R) ≤ Real.exp (1 / 2) * Real.exp (-(G / 2) - ε * (γ₀ + 1 / 2)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    have hKc : 2 ^ (M + 1) * Mθ * Real.exp (1 / 2) ≤ KR * (cN / Real.exp 1) := by
      rw [hKR]
      have e : (2 ^ (M + 1) * Mθ * Real.exp (3 / 2) / cN + 1) * (cN / Real.exp 1) =
          2 ^ (M + 1) * Mθ * Real.exp (1 / 2) + cN / Real.exp 1 := by
        have : Real.exp (3 / 2) = Real.exp (1 / 2) * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        rw [this]; field_simp
      rw [e]; have : 0 ≤ cN / Real.exp 1 := by positivity
      linarith
    have hexp : Real.exp (-(7 * G / 16)) * Real.exp (-(ε * (γ₀ + 1 / 2))) * Real.exp (-(G / 16)) =
        Real.exp (-(G / 2) - ε * (γ₀ + 1 / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    calc 2 ^ (M + 1) * Mθ * Real.exp ((6 + 2 * M) * L) * Real.exp (-R)
        ≤ 2 ^ (M + 1) * Mθ * Real.exp ((6 + 2 * M) * L) *
            (Real.exp (1 / 2) * Real.exp (-(G / 2) - ε * (γ₀ + 1 / 2))) := by gcongr
      _ = (2 ^ (M + 1) * Mθ * Real.exp (1 / 2)) * Real.exp ((6 + 2 * M) * L) *
            Real.exp (-(G / 2) - ε * (γ₀ + 1 / 2)) := by ring
      _ ≤ (KR * (cN / Real.exp 1)) * Real.exp ((6 + 2 * M) * L) *
            Real.exp (-(G / 2) - ε * (γ₀ + 1 / 2)) := by gcongr
      _ = _ := by rw [← hexp]; ring

/-- The `ρ_T` term. -/
theorem term_rho_le {M KR L Q B₀ : ℝ} (hM : 1 ≤ M) (hKR : 1 ≤ KR) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hB : Real.log (192 * (M + 2) * KR) ≤ B₀) (hmaster : B₀ + (14 + 4 * M) * L ≤ Q) :
    6 * (M + 2) * (8 * (KR * Real.exp ((6 + 2 * M) * L) * Real.exp (-(7 * (64 * M * Q) / 16)))) ≤
      Real.exp (-Q) / 4 := by
  have hK : 0 < 48 * (M + 2) * KR := by positivity
  have h := small_of_log_le (K := 48 * (M + 2) * KR) (c := 6 + 2 * M) (k := 28 * M) (Q := Q)
    (L := L) hK (by
      have e : 4 * (48 * (M + 2) * KR) = 192 * (M + 2) * KR := by ring
      rw [e]
      have h1 : (6 + 2 * M) * L ≤ (14 + 4 * M) * L := mul_le_mul_of_nonneg_right (by linarith) hL
      have h2 : Q ≤ (28 * M - 1) * Q := le_mul_of_one_le_left hQ (by linarith)
      linarith)
  calc 6 * (M + 2) * (8 * (KR * Real.exp ((6 + 2 * M) * L) * Real.exp (-(7 * (64 * M * Q) / 16))))
      = 48 * (M + 2) * KR * Real.exp ((6 + 2 * M) * L) * Real.exp (-(28 * M * Q)) := by
        ring_nf
    _ ≤ Real.exp (-Q) / 4 := h

/-- The Lipschitz term. -/
theorem term_lip_le {M w c₀ L Q B₀ Lk : ℝ} (hM : 1 ≤ M) (hw : 0 < w) (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hQ : 0 ≤ Q) (hLk : Lk ≤ 64 * Real.exp (4 * L))
    (hB : Real.log (1536 * (M + 2) / (w * c₀) + 1) ≤ B₀) (hmaster : B₀ + (14 + 4 * M) * L ≤ Q) :
    6 * (M + 2) * (4 * (Lk * Real.exp (-(8 * Q)) / (4 * w * c₀))) ≤ Real.exp (-Q) / 4 := by
  have hK : 0 < 384 * (M + 2) / (w * c₀) := by positivity
  have h := small_of_log_le (K := 384 * (M + 2) / (w * c₀)) (c := 4) (k := 8) (Q := Q) (L := L) hK
    (by
      have e : 4 * (384 * (M + 2) / (w * c₀)) = 1536 * (M + 2) / (w * c₀) := by ring
      rw [e]
      have h0 : Real.log (1536 * (M + 2) / (w * c₀)) ≤ Real.log (1536 * (M + 2) / (w * c₀) + 1) :=
        Real.log_le_log (by positivity) (by linarith)
      have h1 : 4 * L ≤ (14 + 4 * M) * L := mul_le_mul_of_nonneg_right (by linarith) hL
      linarith)
  have hr0 : 0 ≤ Real.exp (-(8 * Q)) := (Real.exp_pos _).le
  calc 6 * (M + 2) * (4 * (Lk * Real.exp (-(8 * Q)) / (4 * w * c₀)))
      = 6 * (M + 2) / (w * c₀) * Lk * Real.exp (-(8 * Q)) := by field_simp
    _ ≤ 6 * (M + 2) / (w * c₀) * (64 * Real.exp (4 * L)) * Real.exp (-(8 * Q)) := by gcongr
    _ = 384 * (M + 2) / (w * c₀) * Real.exp (4 * L) * Real.exp (-(8 * Q)) := by ring
    _ ≤ Real.exp (-Q) / 4 := h

/-- The squared-energy term. -/
theorem term_energy_le {M KR KP L Q B₀ a ρT PK : ℝ} (hM : 1 ≤ M) (hKR : 1 ≤ KR) (hKP : 1 ≤ KP)
    (hQ : 0 ≤ Q) (ha0 : 0 ≤ a) (ha : a ≤ Real.exp (8 * M * Q))
    (hρT : ρT = KR * Real.exp ((6 + 2 * M) * L) * Real.exp (-(7 * (64 * M * Q) / 16)))
    (hPK0 : 0 ≤ PK) (hPK : PK ≤ KP * Real.exp (2 * L))
    (hB : Real.log (12 * 44 * KP * KR ^ 2) ≤ B₀) (hmaster : B₀ + (14 + 4 * M) * L ≤ Q) :
    3 * (44 * a ^ 2 * ρT ^ 2 * PK) ≤ Real.exp (-Q) / 4 := by
  have hK : 0 < 132 * KP * KR ^ 2 := by positivity
  have h := small_of_log_le (K := 132 * KP * KR ^ 2) (c := 14 + 4 * M) (k := 40 * M) (Q := Q)
    (L := L) hK (by
      have e : 4 * (132 * KP * KR ^ 2) = 12 * 44 * KP * KR ^ 2 := by ring
      rw [e]
      have h2 : Q ≤ (40 * M - 1) * Q := le_mul_of_one_le_left hQ (by linarith)
      linarith)
  have ha2 : a ^ 2 ≤ Real.exp (16 * M * Q) := by
    calc a ^ 2 ≤ Real.exp (8 * M * Q) ^ 2 := pow_le_pow_left₀ ha0 ha 2
      _ = Real.exp (16 * M * Q) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hρ2 : ρT ^ 2 = KR ^ 2 * Real.exp ((12 + 4 * M) * L) * Real.exp (-(56 * M * Q)) := by
    rw [hρT, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 2 <;> push_cast <;> ring_nf
  calc 3 * (44 * a ^ 2 * ρT ^ 2 * PK)
      ≤ 3 * (44 * Real.exp (16 * M * Q) * ρT ^ 2 * (KP * Real.exp (2 * L))) := by gcongr
    _ = 132 * KP * KR ^ 2 * Real.exp ((14 + 4 * M) * L) * Real.exp (-(40 * M * Q)) := by
        rw [hρ2]
        have e1 : Real.exp (16 * M * Q) * Real.exp (-(56 * M * Q)) = Real.exp (-(40 * M * Q)) := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp ((12 + 4 * M) * L) * Real.exp (2 * L) = Real.exp ((14 + 4 * M) * L) := by
          rw [← Real.exp_add]; ring_nf
        calc 3 * (44 * Real.exp (16 * M * Q) *
              (KR ^ 2 * Real.exp ((12 + 4 * M) * L) * Real.exp (-(56 * M * Q))) *
              (KP * Real.exp (2 * L)))
            = 132 * KP * KR ^ 2 * (Real.exp ((12 + 4 * M) * L) * Real.exp (2 * L)) *
                (Real.exp (16 * M * Q) * Real.exp (-(56 * M * Q))) := by ring
          _ = _ := by rw [e1, e2]
    _ ≤ Real.exp (-Q) / 4 := h

/-- The Borel–Carathéodory term. -/
theorem term_beta_le {M KΛ L Q B₀ δ r lg : ℝ} (hM : 1 ≤ M) (hKΛM : 16 * M ≤ KΛ) (hL : 0 ≤ L)
    (hQ : 0 ≤ Q) (hr : r = Real.exp (-(8 * Q))) (hrδ : r ≤ δ / 4) (hδQ : 1 / δ ≤ 2 * Q)
    (hδ : 0 < δ) (hlg0 : 0 ≤ lg + 1) (hlg : lg + 1 ≤ KΛ + 6 * L + 8 * M * Q)
    (hB : Real.log (6144 * (M + 2) * KΛ) ≤ B₀) (hmaster : B₀ + (14 + 4 * M) * L ≤ Q) :
    6 * (M + 2) * (4 * (2 * (2 * (lg + 1) * r / (δ / 2 - r)))) ≤ Real.exp (-Q) / 4 := by
  have hr0 : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hKΛ : 0 < KΛ := by linarith
  have hden : δ / 4 ≤ δ / 2 - r := by linarith
  have hden0 : 0 < δ / 4 := by positivity
  have h1 : 2 * (lg + 1) * r / (δ / 2 - r) ≤ 2 * (lg + 1) * r / (δ / 4) :=
    div_le_div_of_nonneg_left (by positivity) hden0 hden
  have h2 : 2 * (lg + 1) * r / (δ / 4) = 8 * (lg + 1) * r * (1 / δ) := by field_simp; ring
  have h3 : 8 * (lg + 1) * r * (1 / δ) ≤ 8 * (lg + 1) * r * (2 * Q) :=
    mul_le_mul_of_nonneg_left hδQ (by positivity)
  have hQe : Q ≤ Real.exp (2 * Q) :=
    (self_le_exp Q).trans (Real.exp_le_exp.mpr (by linarith))
  have hQ2 : Q ^ 2 ≤ Real.exp (2 * Q) := by
    have := pow_le_pow_left₀ hQ (self_le_exp Q) 2
    calc Q ^ 2 ≤ Real.exp Q ^ 2 := this
      _ = Real.exp (2 * Q) := by rw [← Real.exp_nat_mul]; norm_num
  have h4 : Q * (lg + 1) ≤ (KΛ + 6 * L + 8 * M) * Real.exp (2 * Q) := by
    calc Q * (lg + 1) ≤ Q * (KΛ + 6 * L + 8 * M * Q) := mul_le_mul_of_nonneg_left hlg hQ
      _ = (KΛ + 6 * L) * Q + 8 * M * Q ^ 2 := by ring
      _ ≤ (KΛ + 6 * L) * Real.exp (2 * Q) + 8 * M * Real.exp (2 * Q) := by
          gcongr
      _ = (KΛ + 6 * L + 8 * M) * Real.exp (2 * Q) := by ring
  have h5 : KΛ + 6 * L + 8 * M ≤ 2 * KΛ * Real.exp (6 * L) := by
    have he := Real.add_one_le_exp (6 * L)
    have h6 : 2 * KΛ + 6 * L ≤ 2 * KΛ * (6 * L + 1) := by nlinarith
    calc KΛ + 6 * L + 8 * M ≤ 2 * KΛ + 6 * L := by linarith
      _ ≤ 2 * KΛ * (6 * L + 1) := h6
      _ ≤ 2 * KΛ * Real.exp (6 * L) := mul_le_mul_of_nonneg_left he (by positivity)
  have hK : 0 < 1536 * (M + 2) * KΛ := by positivity
  have hsmall := small_of_log_le (K := 1536 * (M + 2) * KΛ) (c := 6) (k := 6) (Q := Q) (L := L) hK
    (by
      have e : 4 * (1536 * (M + 2) * KΛ) = 6144 * (M + 2) * KΛ := by ring
      rw [e]
      have h7 : 6 * L ≤ (14 + 4 * M) * L := mul_le_mul_of_nonneg_right (by linarith) hL
      linarith)
  have hexp : Real.exp (2 * Q) * Real.exp (-(8 * Q)) = Real.exp (-(6 * Q)) := by
    rw [← Real.exp_add]; ring_nf
  calc 6 * (M + 2) * (4 * (2 * (2 * (lg + 1) * r / (δ / 2 - r))))
      ≤ 6 * (M + 2) * (4 * (2 * (8 * (lg + 1) * r * (2 * Q)))) := by
        have : 2 * (lg + 1) * r / (δ / 2 - r) ≤ 8 * (lg + 1) * r * (2 * Q) := by
          rw [h2] at h1; exact h1.trans h3
        gcongr
    _ = 768 * (M + 2) * (Q * (lg + 1)) * r := by ring
    _ ≤ 768 * (M + 2) * ((KΛ + 6 * L + 8 * M) * Real.exp (2 * Q)) * r := by gcongr
    _ ≤ 768 * (M + 2) * ((2 * KΛ * Real.exp (6 * L)) * Real.exp (2 * Q)) * r := by gcongr
    _ = 1536 * (M + 2) * KΛ * Real.exp (6 * L) * (Real.exp (2 * Q) * Real.exp (-(8 * Q))) := by
        rw [hr]; ring
    _ = 1536 * (M + 2) * KΛ * Real.exp (6 * L) * Real.exp (-(6 * Q)) := by rw [hexp]
    _ ≤ Real.exp (-Q) / 4 := hsmall

/-- The three tails of the resolvent test below the Landau height. -/
theorem landau_tail_package {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hline : ρ₀.re = 1 / 2) {M : ℕ}
    (hmM : zetaZeroConfig.mult ρ₀ ≤ M) {U L R : ℝ} (hU0 : 0 ≤ U) (hUL : U ≤ L)
    (hR : R = π * Real.cos (2 * θ) * Real.exp (2 * U)) (hR3 : 3 + (M : ℝ) ≤ R) :
    (∫ u : ℝ, ‖tiltedTail U θ u‖ * Real.exp (1 / 2 * |u|)) ≤
        2 * tiltedPhiTailConst * Real.exp (6 * L) * Real.exp (-R) ∧
    expTail (tiltedPhi θ) (1 / 2) U ≤ 2 * tiltedPhiTailConst * Real.exp (6 * L) * Real.exp (-R) ∧
    expTail (iterResolvent (ρ₀.im : ℂ) (zetaZeroConfig.mult ρ₀) (tiltedPhi θ)) (1 / 2) U ≤
      2 ^ (M + 1) * tiltedPhiTailConst * Real.exp ((6 + 2 * M) * L) * Real.exp (-R) := by
  obtain ⟨v, hv, hv0, hlocv⟩ := exists_tiltedPhi_local_factor hθ0 hθ hρ₀ hline
  have hdecay := superExpDecay_tiltedRiemannKernel hθ0 hθ
  have hM0 : 0 ≤ tiltedPhiTailConst := tiltedPhiTailConst_nonneg
  have hMr : (zetaZeroConfig.mult ρ₀ : ℝ) ≤ M := by exact_mod_cast hmM
  have hm0 : (0 : ℝ) ≤ zetaZeroConfig.mult ρ₀ := Nat.cast_nonneg _
  have hU6 : Real.exp (6 * U) ≤ Real.exp (6 * L) := Real.exp_le_exp.mpr (by linarith)
  have hRe : 3 ≤ π * Real.cos (2 * θ) * Real.exp (2 * U) := by rw [← hR]; linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := integral_norm_tiltedTail_mul_exp_le (U := U) hθ0 hθ hRe
    rw [← hR] at h
    refine h.trans ?_
    have := Real.exp_pos (-R); gcongr
  · have h := expTail_tiltedPhi_le_of_rate (b := 1 / 2) (X := U) hθ0 hθ (by linarith)
      (by rw [← mul_assoc]; linarith)
    rw [← hR] at h
    refine h.trans ?_
    have e : (11 / 2 + 1 / 2 : ℝ) * U = 6 * U := by ring
    rw [e]; have := Real.exp_pos (-R); gcongr
  · have h1 := expTail_iterResolvent_le hdecay (by simp) hv.continuousAt hlocv
      (zetaZeroConfig.mult ρ₀) le_rfl (1 / 2) U (by norm_num)
    have h2 := expTail_tiltedPhi_le_of_rate (b := 1 / 2 + 3 / 2 * ((zetaZeroConfig.mult ρ₀ : ℕ) : ℝ))
      (X := U) hθ0 hθ (by linarith) (by rw [← mul_assoc]; linarith)
    rw [← hR] at h2
    refine h1.trans ?_
    have hpow : (2 : ℝ) ^ (zetaZeroConfig.mult ρ₀) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hmM
    have hexpU : Real.exp ((11 / 2 + (1 / 2 + 3 / 2 * ((zetaZeroConfig.mult ρ₀ : ℕ) : ℝ))) * U) ≤
        Real.exp ((6 + 2 * M) * L) := by
      apply Real.exp_le_exp.mpr
      have h3 : 11 / 2 + (1 / 2 + 3 / 2 * ((zetaZeroConfig.mult ρ₀ : ℕ) : ℝ)) ≤ 6 + 2 * M := by
        linarith
      calc (11 / 2 + (1 / 2 + 3 / 2 * ((zetaZeroConfig.mult ρ₀ : ℕ) : ℝ))) * U
          ≤ (6 + 2 * M) * U := mul_le_mul_of_nonneg_right h3 hU0
        _ ≤ (6 + 2 * M) * L := mul_le_mul_of_nonneg_left hUL (by positivity)
    calc (2 : ℝ) ^ (zetaZeroConfig.mult ρ₀) * expTail (tiltedPhi θ)
          (1 / 2 + 3 / 2 * ((zetaZeroConfig.mult ρ₀ : ℕ) : ℝ)) U
        ≤ 2 ^ M * (2 * tiltedPhiTailConst *
            Real.exp ((11 / 2 + (1 / 2 + 3 / 2 * ((zetaZeroConfig.mult ρ₀ : ℕ) : ℝ))) * U) *
            Real.exp (-R)) := mul_le_mul hpow h2 (expTail_nonneg _ _ _) (by positivity)
      _ ≤ 2 ^ M * (2 * tiltedPhiTailConst * Real.exp ((6 + 2 * M) * L) * Real.exp (-R)) := by
          gcongr
      _ = 2 ^ (M + 1) * tiltedPhiTailConst * Real.exp ((6 + 2 * M) * L) * Real.exp (-R) := by
          rw [pow_succ]; ring

/-- The energy ratio `P/κ_l² ≤ K_P e^{2L}`. -/
theorem energy_ratio_le {Bw A₀ w c₀ γ₀ L KP : ℝ} (hA₀ : 1 ≤ A₀) (hw : 0 < w)
    (hc₀ : 0 < c₀) (hγ : 7 ≤ γ₀) (hγE : γ₀ + 3 ≤ 8 * Real.exp (2 * L))
    (hKP : KP = 24 * (Bw ^ 2 * A₀ / (w ^ 2 * c₀ ^ 2)) + 1) :
    Bw ^ 2 * (1 + γ₀) ^ 4 * (24 * A₀ * Real.log (γ₀ + 3)) / ((γ₀ ^ 2 + 1 / 4) * (4 * w * c₀)) ^ 2 ≤
      KP * Real.exp (2 * L) := by
  have hq : 0 < γ₀ ^ 2 + 1 / 4 := by positivity
  have h1 : (1 + γ₀) ^ 2 ≤ 7 / 5 * (γ₀ ^ 2 + 1 / 4) := by nlinarith
  have h2 : (1 + γ₀) ^ 4 ≤ 2 * (γ₀ ^ 2 + 1 / 4) ^ 2 := by
    have := pow_le_pow_left₀ (sq_nonneg (1 + γ₀)) h1 2
    nlinarith [sq_nonneg (γ₀ ^ 2 + 1 / 4)]
  have hlog : Real.log (γ₀ + 3) ≤ 8 * Real.exp (2 * L) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < γ₀ + 3); linarith
  have hlog0 : 0 ≤ Real.log (γ₀ + 3) := Real.log_nonneg (by linarith)
  have hA0 : 0 ≤ A₀ := by linarith
  rw [div_le_iff₀ (by positivity)]
  have hE0 : 0 < Real.exp (2 * L) := Real.exp_pos _
  calc Bw ^ 2 * (1 + γ₀) ^ 4 * (24 * A₀ * Real.log (γ₀ + 3))
      ≤ Bw ^ 2 * (2 * (γ₀ ^ 2 + 1 / 4) ^ 2) * (24 * A₀ * (8 * Real.exp (2 * L))) := by gcongr
    _ = 24 * (Bw ^ 2 * A₀ / (w ^ 2 * c₀ ^ 2)) * Real.exp (2 * L) *
          ((γ₀ ^ 2 + 1 / 4) * (4 * w * c₀)) ^ 2 := by field_simp; ring
    _ ≤ KP * Real.exp (2 * L) * ((γ₀ ^ 2 + 1 / 4) * (4 * w * c₀)) ^ 2 := by
        rw [hKP]; gcongr; linarith

/-- `L_κ ≤ 64 e^{4L}`. -/
theorem bumpLipConst_le {w γ₀ L : ℝ} (hw : 0 < w) (hw16 : w ≤ 1 / 16) (hγ : 7 ≤ γ₀)
    (hγE : γ₀ + 3 ≤ 8 * Real.exp (2 * L)) : bumpLipConst w γ₀ ≤ 64 * Real.exp (4 * L) := by
  unfold bumpLipConst
  rw [abs_of_nonneg (by linarith)]
  have h1 : 2 * w ^ 2 * (γ₀ + 2) ^ 2 + 2 * w * (2 * γ₀ + 1) ≤ (γ₀ + 2) ^ 2 := by
    have hw2 : 2 * w ^ 2 ≤ 1 / 2 := by nlinarith
    have hw1 : 2 * w ≤ 1 / 8 := by linarith
    have : 2 * w ^ 2 * (γ₀ + 2) ^ 2 ≤ 1 / 2 * (γ₀ + 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)
    have : 2 * w * (2 * γ₀ + 1) ≤ 1 / 8 * (2 * γ₀ + 1) :=
      mul_le_mul_of_nonneg_right hw1 (by linarith)
    nlinarith
  have h2 : (γ₀ + 2) ^ 2 ≤ (8 * Real.exp (2 * L)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h3 : (8 * Real.exp (2 * L)) ^ 2 = 64 * Real.exp (4 * L) := by
    rw [mul_pow, ← Real.exp_nat_mul]; norm_num; ring_nf
  linarith

/-- **The smallness package.**  From the master level inequality, all four error terms of the
mass estimate are below `e^{-Q}/4`, and the side conditions of the analytic core hold. -/
theorem landau_small_package {Mr KR KΛ KP B₀ L Q δ r lg w c₀ Lk PK : ℝ} {m : ℕ}
    (hM : 1 ≤ Mr) (hKR : 1 ≤ KR) (hKΛM : 16 * Mr ≤ KΛ) (hKP : 1 ≤ KP) (hL : 0 ≤ L)
    (hQ2 : 2 ≤ Q) (hmaster : B₀ + (14 + 4 * Mr) * L ≤ Q)
    (hB1 : Real.log (192 * (Mr + 2) * KR) ≤ B₀) (hB2 : Real.log (6144 * (Mr + 2) * KΛ) ≤ B₀)
    (hB3 : Real.log (1536 * (Mr + 2) / (w * c₀) + 1) ≤ B₀)
    (hB4 : Real.log (12 * 44 * KP * KR ^ 2) ≤ B₀) (hw : 0 < w) (hc₀ : 0 < c₀)
    (hr : r = Real.exp (-(8 * Q))) (hrδ : r ≤ δ / 4) (hδQ : 1 / δ ≤ 2 * Q) (hδ : 0 < δ)
    (hlg0 : 0 ≤ lg + 1) (hlg : lg + 1 ≤ KΛ + 6 * L + 8 * Mr * Q) (hLk0 : 0 ≤ Lk)
    (hLk : Lk ≤ 64 * Real.exp (4 * L)) (hPK0 : 0 ≤ PK) (hPK : PK ≤ KP * Real.exp (2 * L))
    (hmM : (m : ℝ) ≤ Mr) :
    0 ≤ 2 * (2 * (lg + 1) * r / (δ / 2 - r)) ∧
    2 * (lg + 1) * r / (δ / 2 - r) ≤ 1 ∧
    KR * Real.exp ((6 + 2 * Mr) * L) * Real.exp (-(7 * (64 * Mr * Q) / 16)) ≤ 1 / 2 ∧
    Lk * r ≤ 4 * w * c₀ ∧
    6 * (Mr + 2) * (4 * (2 * (2 * (lg + 1) * r / (δ / 2 - r))) +
        8 * (KR * Real.exp ((6 + 2 * Mr) * L) * Real.exp (-(7 * (64 * Mr * Q) / 16))) +
        4 * (Lk * r / (4 * w * c₀))) +
      3 * (44 * ((r ^ m)⁻¹) ^ 2 *
        (KR * Real.exp ((6 + 2 * Mr) * L) * Real.exp (-(7 * (64 * Mr * Q) / 16))) ^ 2 * PK) ≤
      min (1 / 4) (Real.exp (-Q)) := by
  have hQ0 : 0 ≤ Q := by linarith
  have hr0 : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hden : 0 < δ / 2 - r := by linarith
  have hβ0 : 0 ≤ 2 * (2 * (lg + 1) * r / (δ / 2 - r)) := by positivity
  have t1 := term_beta_le hM hKΛM hL hQ0 hr hrδ hδQ hδ hlg0 hlg hB2 hmaster
  have t2 := term_rho_le hM hKR hL hQ0 hB1 hmaster
  have t3 := term_lip_le (Lk := Lk) hM hw hc₀ hL hQ0 hLk hB3 hmaster
  rw [← hr] at t3
  have ha0 : 0 ≤ (r ^ m)⁻¹ := by positivity
  have ha : (r ^ m)⁻¹ ≤ Real.exp (8 * Mr * Q) := by
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have : (m : ℝ) * (8 * Q) ≤ Mr * (8 * Q) := mul_le_mul_of_nonneg_right hmM (by linarith)
    linarith
  have t4 := term_energy_le hM hKR hKP hQ0 ha0 ha rfl hPK0 hPK hB4 hmaster
  have hsum : 6 * (Mr + 2) * (4 * (2 * (2 * (lg + 1) * r / (δ / 2 - r))) +
        8 * (KR * Real.exp ((6 + 2 * Mr) * L) * Real.exp (-(7 * (64 * Mr * Q) / 16))) +
        4 * (Lk * r / (4 * w * c₀))) +
      3 * (44 * ((r ^ m)⁻¹) ^ 2 *
        (KR * Real.exp ((6 + 2 * Mr) * L) * Real.exp (-(7 * (64 * Mr * Q) / 16))) ^ 2 * PK) ≤
      Real.exp (-Q) := by
    have e : 6 * (Mr + 2) * (4 * (2 * (2 * (lg + 1) * r / (δ / 2 - r))) +
        8 * (KR * Real.exp ((6 + 2 * Mr) * L) * Real.exp (-(7 * (64 * Mr * Q) / 16))) +
        4 * (Lk * r / (4 * w * c₀))) =
        6 * (Mr + 2) * (4 * (2 * (2 * (lg + 1) * r / (δ / 2 - r)))) +
        6 * (Mr + 2) * (8 * (KR * Real.exp ((6 + 2 * Mr) * L) *
          Real.exp (-(7 * (64 * Mr * Q) / 16)))) +
        6 * (Mr + 2) * (4 * (Lk * r / (4 * w * c₀))) := by ring
    rw [e]; linarith
  have hexpQ : Real.exp (-Q) ≤ 1 / 4 := by
    have h1 : Real.exp (-Q) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-2) < 1 / 4 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h4 : (27 / 10 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      rw [h3]; norm_num; nlinarith
    linarith
  have h6 : 1 ≤ 6 * (Mr + 2) := by linarith
  have hexp1 : Real.exp (-Q) / 4 ≤ 1 / 16 := by linarith
  refine ⟨hβ0, ?_, ?_, ?_, le_min (hsum.trans hexpQ) hsum⟩
  · have hB0 : 0 ≤ 2 * (lg + 1) * r / (δ / 2 - r) := by positivity
    have h1 := le_mul_of_one_le_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hB0) h6
    have e : 6 * (Mr + 2) * (4 * (2 * (2 * (lg + 1) * r / (δ / 2 - r)))) =
        6 * (Mr + 2) * (8 * (2 * (lg + 1) * r / (δ / 2 - r))) := by ring
    linarith
  · have hρ0 : 0 ≤ KR * Real.exp ((6 + 2 * Mr) * L) * Real.exp (-(7 * (64 * Mr * Q) / 16)) := by
      positivity
    have h1 := le_mul_of_one_le_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hρ0) h6
    linarith
  · have hq0 : 0 ≤ 4 * (Lk * r / (4 * w * c₀)) := by positivity
    have h1 := le_mul_of_one_le_left hq0 h6
    have h2 : 4 * (Lk * r / (4 * w * c₀)) ≤ 1 := by linarith
    have h3 : Lk * r / (4 * w * c₀) ≤ 1 := by linarith
    rwa [div_le_one (by positivity)] at h3

/-- The logarithmic ceiling-to-floor ratio below the Landau height. -/
theorem log_ceil_floor_le {ε γ₀ δ L Q Mr KΛ : ℝ} {m : ℕ} (hε : 0 ≤ ε) (hγ : 7 ≤ γ₀) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hmM : (m : ℝ) ≤ Mr)
    (hγE : γ₀ + 2 ≤ 8 * Real.exp (2 * L))
    (hKΛ : KΛ = 14 + |Real.log (xiNearLineUpperConst / xiNearLineLowerConst)| + 16 * Mr)
    (hZ : 3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ ≤ 4 * Mr * Q)
    (hMδ : 2 * Mr / δ ≤ 4 * Mr * Q)
    {Φ₀ : ℝ} (hfl : dividedKernelFloor (π / 4 - ε) γ₀ δ ≤ Φ₀)
    (hce : Φ₀ ≤ dividedKernelCeil (π / 4 - ε) γ₀ δ m) :
    0 ≤ Real.log (dividedKernelCeil (π / 4 - ε) γ₀ δ m / dividedKernelFloor (π / 4 - ε) γ₀ δ) + 1 ∧
    Real.log (dividedKernelCeil (π / 4 - ε) γ₀ δ m / dividedKernelFloor (π / 4 - ε) γ₀ δ) + 1 ≤
      KΛ + 6 * L + 8 * Mr * Q := by
  have hf0 := dividedKernelFloor_pos (θ := π / 4 - ε) (δ := δ) hγ
  have hcf : dividedKernelFloor (π / 4 - ε) γ₀ δ ≤ dividedKernelCeil (π / 4 - ε) γ₀ δ m :=
    hfl.trans hce
  have hc0 : 0 < dividedKernelCeil (π / 4 - ε) γ₀ δ m := lt_of_lt_of_le hf0 hcf
  have hratio1 : 1 ≤ dividedKernelCeil (π / 4 - ε) γ₀ δ m / dividedKernelFloor (π / 4 - ε) γ₀ δ :=
    (one_le_div hf0).mpr hcf
  refine ⟨by linarith [Real.log_nonneg hratio1], ?_⟩
  have hmul := dividedKernelCeil_le_floor_mul (m := m) hε hγ hδ
  have hlog : Real.log (dividedKernelCeil (π / 4 - ε) γ₀ δ m / dividedKernelFloor (π / 4 - ε) γ₀ δ)
      ≤ 3 + Real.log (xiNearLineUpperConst / xiNearLineLowerConst) + 3 * Real.log (γ₀ + 2) +
        m * Real.log (4 / (3 * δ)) + 3 * logDerivZetaConstant * Real.log (γ₀ + 1) / δ := by
    rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hf0, mul_comm]
    exact hmul
  have h1 : Real.log (xiNearLineUpperConst / xiNearLineLowerConst) ≤
      |Real.log (xiNearLineUpperConst / xiNearLineLowerConst)| := le_abs_self _
  have h2 : Real.log (γ₀ + 2) ≤ 3 + 2 * L := by
    have h8 : Real.log (γ₀ + 2) ≤ Real.log (8 * Real.exp (2 * L)) :=
      Real.log_le_log (by linarith) hγE
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h8
    have : Real.log 8 < 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      have h4 : (27 / 10 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      rw [h3]; nlinarith
    linarith
  have h3 : (m : ℝ) * Real.log (4 / (3 * δ)) ≤ 2 * Mr / δ := by
    have hl0 : 0 ≤ Real.log (4 / (3 * δ)) := Real.log_nonneg (by
      rw [le_div_iff₀ (by positivity)]; linarith)
    have hl : Real.log (4 / (3 * δ)) ≤ 4 / (3 * δ) := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 4 / (3 * δ)); linarith
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    calc (m : ℝ) * Real.log (4 / (3 * δ)) ≤ Mr * (4 / (3 * δ)) :=
          mul_le_mul hmM hl hl0 (hm0.trans hmM)
      _ ≤ Mr * (2 / δ) := by
          apply mul_le_mul_of_nonneg_left _ (hm0.trans hmM)
          rw [div_le_div_iff₀ (by positivity) hδ]; nlinarith
      _ = 2 * Mr / δ := by ring
  rw [hKΛ]
  linarith

/-- **The mass law at a fixed level.** -/
theorem landau_mass_at_level {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) {M : ℕ} (hM1 : 1 ≤ M)
    {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {KR KΛ KP B₀ L Q : ℝ}
    (hKR : KR = 2 ^ (M + 1) * tiltedPhiTailConst * Real.exp (3 / 2) / xiNearLineLowerConst + 1)
    (hKΛ : KΛ = 14 + |Real.log (xiNearLineUpperConst / xiNearLineLowerConst)| + 16 * M)
    (hKP : KP = 24 * (scaledBumpConst (η / 8) ^ 2 * A₀ /
      ((η / 8) ^ 2 * (Real.cos (1 / 8) * (∫ u, weilBump u)) ^ 2)) + 1)
    (hB1 : Real.log (192 * (M + 2) * KR) ≤ B₀) (hB2 : Real.log (6144 * (M + 2) * KΛ) ≤ B₀)
    (hB3 : Real.log (1536 * (M + 2) / (η / 8 * (Real.cos (1 / 8) * (∫ u, weilBump u))) + 1) ≤ B₀)
    (hB4 : Real.log (12 * 44 * KP * KR ^ 2) ≤ B₀) (hB₀1 : 1 ≤ B₀)
    (hL1 : 1 ≤ L) (hQdef : Q = π * (η * Real.sqrt η) * Real.exp (2 * L) / (64 * M))
    (hmaster : B₀ + (14 + 4 * M) * L ≤ Q)
    {ν : Measure ℝ} (hν : RepresentsHodgeForm L ν) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hline : ρ₀.re = 1 / 2) (hmM : zetaZeroConfig.mult ρ₀ ≤ M) (hγ7 : 7 ≤ ρ₀.im)
    (hτ : ρ₀.im ≤ (1 - η) * (2 * π * Real.exp (2 * L))) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → δ ≤ |ρ.im - ρ₀.im|)
    (hH : (48 * logDerivZetaConstant * Real.log (ρ₀.im + 1) + 32 * M) / δ ≤ 64 * M * Q) :
    ν (Icc (ρ₀.im - Real.exp (-(8 * Q))) (ρ₀.im + Real.exp (-(8 * Q)))) ≠ ⊤ ∧
      |(ν (Icc (ρ₀.im - Real.exp (-(8 * Q))) (ρ₀.im + Real.exp (-(8 * Q))))).toReal -
        (zetaZeroConfig.mult ρ₀ : ℝ)| ≤ Real.exp (-Q) := by
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = Real.sqrt η / 2 := ⟨_, rfl⟩
  have hs1 : Real.sqrt η ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have hε0 : 0 < ε := by rw [hεdef]; have := Real.sqrt_pos.mpr hη; positivity
  have hε1 : ε ≤ 1 / 2 := by rw [hεdef]; linarith
  have hθ0 : 0 ≤ π / 4 - ε := by linarith [Real.pi_gt_three]
  have hθ : 2 * (π / 4 - ε) < π / 2 := by linarith
  have hw : 0 < η / 8 := by positivity
  have hw4 : 4 * (η / 8) ≤ 1 := by linarith
  have hw16 : η / 8 ≤ 1 / 16 := by linarith
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hmR : (zetaZeroConfig.mult ρ₀ : ℝ) ≤ M := by exact_mod_cast hmM
  have hL0 : 0 ≤ L := by linarith
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hmaster
  have hQ2 : 2 ≤ Q := by nlinarith
  have hc₀ : 0 < Real.cos (1 / 8) * (∫ u, weilBump u) := by
    have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
    have hcos : 0 < Real.cos (1 / 8) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    positivity
  -- the height
  have hγE : ρ₀.im + 3 ≤ 8 * Real.exp (2 * L) := by
    have hE : 2 ≤ Real.exp (2 * L) := by
      have := Real.add_one_le_exp (2 * L); linarith
    have h1 : ρ₀.im ≤ 2 * π * Real.exp (2 * L) := by
      have : 0 ≤ η * (2 * π * Real.exp (2 * L)) := by positivity
      linarith
    have hπ : π < 3.15 := Real.pi_lt_d2
    have h2 : π * Real.exp (2 * L) ≤ 3.15 * Real.exp (2 * L) :=
      mul_le_mul_of_nonneg_right hπ.le (Real.exp_pos _).le
    linarith
  -- separation consequences
  have hC := logDerivZetaConstant_nonneg
  have hlogγ : 0 ≤ Real.log (ρ₀.im + 1) := Real.log_nonneg (by linarith)
  have hsplit : (48 * logDerivZetaConstant * Real.log (ρ₀.im + 1) + 32 * M) / δ =
      48 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ + 32 * M / δ := by ring
  rw [hsplit] at hH
  have hA : 0 ≤ 48 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ := by positivity
  have hB : 0 ≤ 32 * (M : ℝ) / δ := by positivity
  have hδQ : 1 / δ ≤ 2 * Q := by
    have h : 32 * (M : ℝ) * (1 / δ) ≤ 32 * M * (2 * Q) := by
      have e : 32 * (M : ℝ) / δ = 32 * M * (1 / δ) := by ring
      rw [← e]; linarith
    exact le_of_mul_le_mul_left h (by positivity)
  have hZ : 3 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ ≤ 4 * M * Q := by
    have e : 3 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ =
        48 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ / 16 := by ring
    rw [e]; linarith
  have hMδ : 2 * (M : ℝ) / δ ≤ 4 * M * Q := by
    have e : 2 * (M : ℝ) / δ = 32 * M / δ / 16 := by ring
    rw [e]; linarith
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.exp (-(8 * Q)) := ⟨_, rfl⟩
  rw [← hrdef]
  have hr0 : 0 < r := by rw [hrdef]; exact Real.exp_pos _
  have hr1 : r ≤ 1 := by rw [hrdef]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hrδ : r ≤ δ / 4 := by
    have h8 : 8 * Q ≤ Real.exp (8 * Q) := self_le_exp _
    have h1 : r ≤ 1 / (8 * Q) := by
      rw [hrdef, Real.exp_neg, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (Real.exp_pos _)]
      linarith
    have h2 : 1 / (8 * Q) ≤ δ / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := (div_le_iff₀ hδ).mp hδQ
      linarith
    linarith
  -- the divided kernel
  obtain ⟨hF, hprod, hfloor, hceil, hvar⟩ := divided_tilted_kernel_near_zero hθ0 hθ hρ₀ hline hγ7
    hδ hδ2 hsep
  obtain ⟨hlg0, hlg⟩ := log_ceil_floor_le (L := L) (Q := Q) (KΛ := KΛ) hε0.le hγ7 hδ hδ2 hmR
    (by linarith) hKΛ hZ hMδ hfloor hceil
  -- the rate
  have hgain0 := landau_gain (L := L) hη hη2 hτ
  rw [← hεdef] at hgain0
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = π * Real.cos (2 * (π / 4 - ε)) * Real.exp (2 * (L - η / 8)) :=
    ⟨_, rfl⟩
  rw [← hRdef] at hgain0
  have hGQ : π * (η * Real.sqrt η) * Real.exp (2 * L) = 64 * M * Q := by rw [hQdef]; field_simp
  have hgain : 64 * M * Q / 2 - ε / 2 ≤ R - ε * (ρ₀.im + 1 / 2) := by
    rw [← hGQ]; linarith
  have hεγ : 0 ≤ ε * (ρ₀.im + 1 / 2) := by
    have : 0 ≤ ρ₀.im + 1 / 2 := by linarith
    positivity
  have hMQ : (M : ℝ) * 2 ≤ M * Q := mul_le_mul_of_nonneg_left hQ2 (by positivity)
  have hR3 : 3 + (M : ℝ) ≤ R := by linarith only [hgain, hεγ, hε1, hMQ, hMr]
  obtain ⟨hTtail, hεΦ, hεF⟩ := landau_tail_package hθ0 hθ hρ₀ hline hmM
    (U := L - η / 8) (L := L) (by linarith only [hL1, hw16]) (by linarith only [hw]) hRdef hR3
  have hZ16 : 3 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ ≤ 64 * M * Q / 16 := by
    linarith only [hZ]
  have hmlowF := (dividedKernelFloor_ge_exp hε0.le hγ7 hZ16).trans hfloor
  obtain ⟨hTTF, hTFρ⟩ := tails_le_rho (M := M) tiltedPhiTailConst_nonneg xiNearLineLowerConst_pos
    hKR hL0 (by linarith only [hε1]) hgain
  have hTρ := hTTF.trans hTFρ
  have hKR1 : 1 ≤ KR := by
    rw [hKR]
    have : 0 ≤ 2 ^ (M + 1) * tiltedPhiTailConst * Real.exp (3 / 2) / xiNearLineLowerConst := by
      have := tiltedPhiTailConst_nonneg; have := xiNearLineLowerConst_pos; positivity
    linarith only [this]
  have hKΛM : 16 * (M : ℝ) ≤ KΛ := by
    rw [hKΛ]
    linarith only [abs_nonneg (Real.log (xiNearLineUpperConst / xiNearLineLowerConst))]
  have hA0 : 0 ≤ A₀ := by linarith only [hA₀]
  have hKP1 : 1 ≤ KP := by
    rw [hKP]
    have : 0 ≤ scaledBumpConst (η / 8) ^ 2 * A₀ /
        ((η / 8) ^ 2 * (Real.cos (1 / 8) * (∫ u, weilBump u)) ^ 2) := by
      have := scaledBumpConst_nonneg hw
      positivity
    linarith only [this]
  have hPK := energy_ratio_le hA₀ hw hc₀ hγ7 hγE hKP
  have hlog3 : 0 ≤ Real.log (ρ₀.im + 3) := Real.log_nonneg (by linarith only [hγ7])
  have hPK0 : 0 ≤ scaledBumpConst (η / 8) ^ 2 * (1 + ρ₀.im) ^ 4 *
      (24 * A₀ * Real.log (ρ₀.im + 3)) /
      ((ρ₀.im ^ 2 + 1 / 4) * (4 * (η / 8) * (Real.cos (1 / 8) * (∫ u, weilBump u)))) ^ 2 := by
    have := scaledBumpConst_nonneg hw
    positivity
  have hLk := bumpLipConst_le hw hw16 hγ7 (by linarith only [hγE])
  have hLk0 : 0 ≤ bumpLipConst (η / 8) ρ₀.im := by unfold bumpLipConst; positivity
  obtain ⟨hβ0, hB1', hρT, hLr, hsmall⟩ := landau_small_package (m := zetaZeroConfig.mult ρ₀) hMr
    hKR1 hKΛM hKP1 hL0 hQ2 hmaster hB1 hB2 hB3 hB4 hw hc₀ hrdef hrδ hδQ hδ hlg0 hlg hLk0 hLk hPK0
    hPK hmR
  have hm0 : 0 < xiNearLineLowerConst / Real.exp 1 * Real.exp (-(ε * (ρ₀.im + 1 / 2))) *
      Real.exp (-(64 * M * Q / 16)) := by
    have := xiNearLineLowerConst_pos; positivity
  exact krein_mass_core hν hA₀ hloc hθ0 hθ hρ₀ hline hγ7 hF hprod hw hw4
    (U := L - η / 8) (by linarith only) (by linarith only [hL1, hw16]) hr0 hr1 hmR hβ0
    (hvar r hr0.le (by linarith only [hrδ, hδ]) hB1') hTtail hεΦ hεF hm0 hmlowF hTρ hTFρ hρT
    hLr hsmall

theorem le_sum_four_add_one {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a ≤ a + b + c + d + 1 ∧ b ≤ a + b + c + d + 1 ∧ c ≤ a + b + c + d + 1 ∧
      d ≤ a + b + c + d + 1 ∧ 1 ≤ a + b + c + d + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Masses equal multiplicities below the Landau height.**  For `0 < η ≤ 1/2` and every bound
`M ≥ 1` on multiplicities there is `L₀` such that for `L ≥ L₀`, every positive measure `ν`
representing the level-`L` Hodge form of `ζ` and every on-line zero `ρ₀ = 1/2 + iγ₀` of
multiplicity `m₀ ≤ M` with `7 ≤ γ₀ ≤ (1-η) 2π e^{2L}`, `δ`-separated in ordinate from all other
zeros (`0 < δ ≤ 1/2`, `(48 C log(γ₀+1) + 32 M)/δ ≤ π η^{3/2} e^{2L}`), satisfy
`|ν([γ₀ - r_L, γ₀ + r_L]) - m₀| ≤ exp(-π η^{3/2} e^{2L}/(64 M))`,
`r_L = exp(-π η^{3/2} e^{2L}/(8M))`. -/
theorem zeta_krein_representation_masses_below_landau_height :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∀ M : ℕ, 1 ≤ M → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ ν : Measure ℝ, RepresentsHodgeForm L ν →
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, ρ₀.re = 1 / 2 → zetaZeroConfig.mult ρ₀ ≤ M →
      7 ≤ ρ₀.im → ρ₀.im ≤ (1 - η) * (2 * π * Real.exp (2 * L)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      (∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → δ ≤ |ρ.im - ρ₀.im|) →
      (48 * logDerivZetaConstant * Real.log (ρ₀.im + 1) + 32 * M) / δ ≤
        π * (η * Real.sqrt η) * Real.exp (2 * L) →
      ν (Icc (ρ₀.im - Real.exp (-(π * (η * Real.sqrt η) * Real.exp (2 * L) / (8 * M))))
          (ρ₀.im + Real.exp (-(π * (η * Real.sqrt η) * Real.exp (2 * L) / (8 * M))))) ≠ ⊤ ∧
      |(ν (Icc (ρ₀.im - Real.exp (-(π * (η * Real.sqrt η) * Real.exp (2 * L) / (8 * M))))
          (ρ₀.im + Real.exp (-(π * (η * Real.sqrt η) * Real.exp (2 * L) / (8 * M)))))).toReal -
        (zetaZeroConfig.mult ρ₀ : ℝ)| ≤
        Real.exp (-(π * (η * Real.sqrt η) * Real.exp (2 * L) / (64 * M))) := by
  intro η hη hη2 M hM1
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hw : 0 < η / 8 := by positivity
  have hc₀ : 0 < Real.cos (1 / 8) * (∫ u, weilBump u) := by
    have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
    have hcos : 0 < Real.cos (1 / 8) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    positivity
  obtain ⟨KR, hKR⟩ : ∃ KR : ℝ, KR =
      2 ^ (M + 1) * tiltedPhiTailConst * Real.exp (3 / 2) / xiNearLineLowerConst + 1 := ⟨_, rfl⟩
  obtain ⟨KΛ, hKΛ⟩ : ∃ KΛ : ℝ, KΛ =
      14 + |Real.log (xiNearLineUpperConst / xiNearLineLowerConst)| + 16 * M := ⟨_, rfl⟩
  obtain ⟨KP, hKP⟩ : ∃ KP : ℝ, KP = 24 * (scaledBumpConst (η / 8) ^ 2 * A₀ /
      ((η / 8) ^ 2 * (Real.cos (1 / 8) * (∫ u, weilBump u)) ^ 2)) + 1 := ⟨_, rfl⟩
  have hKR1 : 1 ≤ KR := by
    rw [hKR]
    have : 0 ≤ 2 ^ (M + 1) * tiltedPhiTailConst * Real.exp (3 / 2) / xiNearLineLowerConst := by
      have := tiltedPhiTailConst_nonneg; have := xiNearLineLowerConst_pos; positivity
    linarith
  have hKΛ1 : 1 ≤ KΛ := by
    rw [hKΛ]; have := abs_nonneg (Real.log (xiNearLineUpperConst / xiNearLineLowerConst))
    linarith
  have hKP1 : 1 ≤ KP := by
    rw [hKP]
    have : 0 ≤ scaledBumpConst (η / 8) ^ 2 * A₀ /
        ((η / 8) ^ 2 * (Real.cos (1 / 8) * (∫ u, weilBump u)) ^ 2) := by
      have := scaledBumpConst_nonneg hw
      have : 0 ≤ A₀ := by linarith
      positivity
    linarith
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, B₀ = Real.log (192 * (M + 2) * KR) +
      Real.log (6144 * (M + 2) * KΛ) +
      Real.log (1536 * (M + 2) / (η / 8 * (Real.cos (1 / 8) * (∫ u, weilBump u))) + 1) +
      Real.log (12 * 44 * KP * KR ^ 2) + 1 := ⟨_, rfl⟩
  have hl1 : 0 ≤ Real.log (192 * (M + 2) * KR) := Real.log_nonneg (by nlinarith)
  have hl2 : 0 ≤ Real.log (6144 * (M + 2) * KΛ) := Real.log_nonneg (by nlinarith)
  have hl3 : 0 ≤ Real.log (1536 * (M + 2) / (η / 8 * (Real.cos (1 / 8) * (∫ u, weilBump u))) + 1) :=
    Real.log_nonneg (by
      have : 0 ≤ 1536 * ((M : ℝ) + 2) / (η / 8 * (Real.cos (1 / 8) * (∫ u, weilBump u))) := by
        positivity
      linarith)
  have hl4 : 0 ≤ Real.log (12 * 44 * KP * KR ^ 2) := Real.log_nonneg (by nlinarith)
  obtain ⟨hB1, hB2, hB3, hB4, hB₀1⟩ := le_sum_four_add_one hl1 hl2 hl3 hl4
  rw [← hB₀] at hB1 hB2 hB3 hB4 hB₀1
  have hκpos : 0 < π * (η * Real.sqrt η) / (64 * M) := by
    have := Real.pi_pos; have := Real.sqrt_pos.mpr hη; positivity
  obtain ⟨L₀, hL₀1, hL₀⟩ := exists_level_affine_le_exp (B := B₀) (a := 14 + 4 * M)
    (by linarith only [hB₀1]) hκpos
  refine ⟨L₀, fun L hL ν hν ρ₀ hρ₀ hline hmM hγ7 hτ δ hδ hδ2 hsep hH => ?_⟩
  have hL1 : 1 ≤ L := le_trans hL₀1 hL
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = π * (η * Real.sqrt η) * Real.exp (2 * L) / (64 * M) :=
    ⟨_, rfl⟩
  have hmaster : B₀ + (14 + 4 * M) * L ≤ Q := by
    rw [hQdef]
    calc B₀ + (14 + 4 * M) * L ≤ π * (η * Real.sqrt η) / (64 * M) * Real.exp (2 * L) := hL₀ L hL
      _ = π * (η * Real.sqrt η) * Real.exp (2 * L) / (64 * M) := by ring
  have hGQ : π * (η * Real.sqrt η) * Real.exp (2 * L) = 64 * M * Q := by rw [hQdef]; field_simp
  have hr : Real.exp (-(π * (η * Real.sqrt η) * Real.exp (2 * L) / (8 * M))) =
      Real.exp (-(8 * Q)) := by
    rw [hGQ]; congr 1; field_simp; ring
  have hϑ : Real.exp (-(π * (η * Real.sqrt η) * Real.exp (2 * L) / (64 * M))) = Real.exp (-Q) := by
    rw [← hQdef]
  rw [hr, hϑ]
  rw [hGQ] at hH
  exact landau_mass_at_level hη hη2 hM1 hA₀ hloc hKR hKΛ hKP hB1 hB2 hB3 hB4 hB₀1 hL1 hQdef
    hmaster hν hρ₀ hline hmM hγ7 hτ hδ hδ2 hsep hH

end

end RHTower
