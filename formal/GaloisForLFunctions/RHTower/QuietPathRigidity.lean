/-
Path-quiet rigidity: the quiet-crossing hypothesis weakened from straight horizontal
segments to arbitrary C¹ paths through the closed critical strip.

Let `F` be entire, agree with an absolutely convergent Dirichlet series `L(s) = Σ aₘ m^{−s}` on
`Re s ≥ c` (with `½ ≤ c`), and satisfy the exact reflection symmetry `F(s) = F(1−s)`.  Suppose
there is a sequence of heights `T_k → ∞` and, for each `k`, two C¹ paths `γt_k, γb_k : ℝ → ℂ`
crossing the strip `1−c ≤ σ ≤ c` at heights `≈ +T_k` and `≈ −T_k`, along which `F` is *quiet*
(`‖F ∘ γ‖ ≤ q_k`), of arc length `≤ L_k`, with budget `(q_k·L_k + 1)/T_k² → 0`.  Then `aₙ = 0`
for every `n ≥ 2`.

The engine is the Mellin representation `½·aₙ = (1/2π)∫ F(c+it)·E(c+it) dt` from
`QuietCrossingRigidity`, with `E = N/(s(s+1))` the entire regularization of the Perron kink.  Since
`H := F·E` is entire, it has a global primitive `P` (Morera on `ℂ`), so every contour integral of
`H` telescopes to a difference of `P`-values.  For a fixed left depth `−M ≤ −1` and each `k` we run
a closed hexagonal loop: right vertical at `Re = c`, top path `γt_k`, a straight top flank from
`Re = 1−c` to `Re = −M`, left vertical at `Re = −M`, a straight bottom flank, and bottom path
`γb_k`.  Telescoping `P` around the loop gives sum `= 0`.  As `k → ∞`: the two path pieces vanish
(`‖H∘γ‖ ≤ E_kernel · q_k`, so `≤ 4(n+½)^{c+1}·q_k·L_k/T_k² → 0`); the two flank pieces vanish
(`‖F‖ ≤ B` on the flank by reflection, kernel `≤ T_k^{-2}`, cost `≤ 4(n+½)^{c+1}·B·(M+1)/T_k² → 0` —
this is the rôle of the `+1` in the budget); the right and left verticals converge to the full-line
integrals `∫_{Re=c} H` and `∫_{Re=−M} H`.  Hence `∫_{Re=c} H = ∫_{Re=−M} H`, whose modulus is
`≤ 4πB(n−½)^{1−M}` by the right-flank bound carried left by reflection.  Sending `M → ∞` forces
`∫_{Re=c} H = 0`, i.e. `aₙ = 0`.

* `quiet_path_rigidity` — the theorem above.
-/
import GaloisForLFunctions.RHTower.QuietCrossingRigidity

open Complex MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

namespace RHTower

/-- The reciprocal quadratic `t ↦ (c²+t²)⁻¹` is Lebesgue integrable for `c > 0`; it is the
`c`-scaled Cauchy profile `c⁻²·(1+(t/c)²)⁻¹`. -/
private theorem inv_quad_int {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) := by
  have hc0 : c⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hc)
  have h1 : Integrable (fun t : ℝ => (1 + (c⁻¹ * t) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq).comp_mul_left' hc0
  have heq : (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) = fun t => (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹ := by
    funext t; rw [← mul_inv]; congr 1; field_simp
  rw [heq]; exact h1.const_mul _

/-- Kernel decay from the imaginary part alone: if `T ≤ |Im s|` with `T > 0`, then
`‖1/(s(s+1))‖ ≤ T^{-2}`, because `‖s‖ ≥ |Im s| ≥ T` and `‖s+1‖ ≥ |Im(s+1)| = |Im s| ≥ T`. -/
private theorem kernel_im_bound {s : ℂ} {T : ℝ} (hT : 0 < T) (hs : T ≤ |s.im|) :
    ‖(s * (s + 1))⁻¹‖ ≤ (T ^ 2)⁻¹ := by
  have hA : T ≤ ‖s‖ := le_trans hs (Complex.abs_im_le_norm s)
  have him1 : (s + 1).im = s.im := by rw [Complex.add_im, Complex.one_im, add_zero]
  have hB : T ≤ ‖s + 1‖ := by
    have h := Complex.abs_im_le_norm (s + 1); rw [him1] at h; exact le_trans hs h
  have hge : T ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, sq]; exact mul_le_mul hA hB hT.le (le_trans hT.le hA)
  rw [norm_inv]; exact inv_anti₀ (by positivity) hge

/-- Kernel decay on the vertical line `Re s = c > 0`: `‖1/(s(s+1))‖ ≤ (c²+t²)⁻¹`, since
`‖c+it‖ = √(c²+t²)` and `‖c+it+1‖ ≥ ‖c+it‖`. -/
private theorem kernel_c_bound {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖((↑c + ↑t * I) * (↑c + ↑t * I + 1))⁻¹‖ ≤ (c ^ 2 + t ^ 2)⁻¹ := by
  set A : ℂ := (↑c + ↑t * I) with hA
  set B : ℂ := (↑c + ↑t * I + 1) with hB
  have hAnorm : ‖A‖ = Real.sqrt (c ^ 2 + t ^ 2) := by rw [hA, Complex.norm_add_mul_I]
  have hApos : 0 < ‖A‖ := by rw [hAnorm]; apply Real.sqrt_pos.mpr; positivity
  have hBge : ‖A‖ ≤ ‖B‖ := by
    have hBnorm : ‖B‖ = Real.sqrt ((c + 1) ^ 2 + t ^ 2) := by
      rw [hB]
      have h : (↑c + ↑t * I + 1 : ℂ) = ↑(c + 1) + ↑t * I := by push_cast; ring
      rw [h, Complex.norm_add_mul_I]
    rw [hAnorm, hBnorm]; apply Real.sqrt_le_sqrt; nlinarith
  have hBpos : 0 < ‖B‖ := lt_of_lt_of_le hApos hBge
  rw [norm_inv, norm_mul, inv_le_inv₀ (mul_pos hApos hBpos) (by positivity)]
  calc c ^ 2 + t ^ 2 = ‖A‖ * ‖A‖ := by rw [hAnorm, Real.mul_self_sqrt (by positivity)]
    _ ≤ ‖A‖ * ‖B‖ := mul_le_mul_of_nonneg_left hBge (le_of_lt hApos)

/-- Kernel decay on the vertical line `Re s = −M` (with `M > 1`): `‖1/(s(s+1))‖ ≤ ((M−1)²+y²)⁻¹`,
since `‖s‖ = √(M²+y²) ≥ √((M−1)²+y²)` and `‖s+1‖ = √((M−1)²+y²)`. -/
private theorem kernel_negM_bound {M y : ℝ} (hM : 1 < M) :
    ‖((↑(-M) + ↑y * I) * (↑(-M) + ↑y * I + 1))⁻¹‖ ≤ ((M - 1) ^ 2 + y ^ 2)⁻¹ := by
  have hAnorm : ‖(↑(-M) + ↑y * I : ℂ)‖ = Real.sqrt ((-M) ^ 2 + y ^ 2) := Complex.norm_add_mul_I _ _
  have hBeq : (↑(-M) + ↑y * I + 1 : ℂ) = ↑(1 - M) + ↑y * I := by push_cast; ring
  have hBnorm : ‖(↑(-M) + ↑y * I + 1 : ℂ)‖ = Real.sqrt ((1 - M) ^ 2 + y ^ 2) := by
    rw [hBeq, Complex.norm_add_mul_I]
  have hden : (0 : ℝ) < (M - 1) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg y, sq_nonneg (M - 1)]
  have hAge : Real.sqrt ((M - 1) ^ 2 + y ^ 2) ≤ ‖(↑(-M) + ↑y * I : ℂ)‖ := by
    rw [hAnorm]; apply Real.sqrt_le_sqrt; nlinarith
  have hBge : Real.sqrt ((M - 1) ^ 2 + y ^ 2) ≤ ‖(↑(-M) + ↑y * I + 1 : ℂ)‖ := by
    rw [hBnorm]; apply Real.sqrt_le_sqrt; nlinarith
  have hge : (M - 1) ^ 2 + y ^ 2 ≤ ‖(↑(-M) + ↑y * I) * (↑(-M) + ↑y * I + 1)‖ := by
    rw [norm_mul]
    calc (M - 1) ^ 2 + y ^ 2
        = Real.sqrt ((M - 1) ^ 2 + y ^ 2) * Real.sqrt ((M - 1) ^ 2 + y ^ 2) := by
          rw [Real.mul_self_sqrt hden.le]
      _ ≤ ‖(↑(-M) + ↑y * I : ℂ)‖ * ‖(↑(-M) + ↑y * I + 1 : ℂ)‖ :=
          mul_le_mul hAge hBge (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) hAge)
  rw [norm_inv]; exact inv_anti₀ hden hge

/-- Derivative of the straight vertical parametrization `y ↦ σ + i·y`: constant `I`. -/
private theorem hasDerivAt_vert (σ y : ℝ) :
    HasDerivAt (fun t : ℝ => (↑σ : ℂ) + ↑t * I) I y := by
  have h1 : HasDerivAt (fun t : ℝ => (↑t : ℂ) * I) I y := by
    simpa using (Complex.ofRealCLM.hasDerivAt).mul_const I
  have h2 : HasDerivAt (fun t : ℝ => (↑σ : ℂ) + ↑t * I) (0 + I) y :=
    (hasDerivAt_const y (↑σ : ℂ)).add h1
  simpa using h2

/-- Derivative of the straight horizontal parametrization `x ↦ x + i·h`: constant `1`. -/
private theorem hasDerivAt_horiz (h x : ℝ) :
    HasDerivAt (fun t : ℝ => (↑t : ℂ) + ↑h * I) 1 x := by
  have h1 : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 x := by simpa using Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (↑t : ℂ) + ↑h * I) (1 + 0) x :=
    h1.add (hasDerivAt_const x (↑h * I : ℂ))
  simpa using h2

/-- **Fundamental theorem of calculus along a C¹ path.**  If `P` is a complex primitive of `H`
everywhere (`HasDerivAt P (H z) z` for all `z`) and `δ` is a path with derivative `δ'` on `[a,b]`
whose pullback integrand `H(δ t)·δ'(t)` is interval-integrable, then
`∫_a^b H(δ t)·δ'(t) dt = P(δ b) − P(δ a)`.  The chain rule gives
`d/dt P(δ t) = P'(δ t)·δ'(t) = H(δ t)·δ'(t)`, and the FTC integrates it. -/
private theorem path_ftc {Hf P : ℂ → ℂ} (hP : ∀ z, HasDerivAt P (Hf z) z)
    {δ δ' : ℝ → ℂ} {a b : ℝ}
    (hδ : ∀ t ∈ Set.uIcc a b, HasDerivAt δ (δ' t) t)
    (hint : IntervalIntegrable (fun t => Hf (δ t) * δ' t) MeasureTheory.volume a b) :
    ∫ t in a..b, Hf (δ t) * δ' t = P (δ b) - P (δ a) := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun s => P (δ s)) (Hf (δ t) * δ' t) t := by
    intro t ht
    simpa [Function.comp, smul_eq_mul, mul_comm] using (hP (δ t)).scomp t (hδ t ht)
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

set_option maxHeartbeats 800000 in
/-- **Path-quiet rigidity.**  A reflection-symmetric Dirichlet carrier `F` that is quiet along a
sequence of arbitrary C¹ paths crossing the closed critical strip `1−c ≤ σ ≤ c` at heights `≈ ±T_k`
(with `‖F ∘ γ‖ ≤ q_k`, arc length `≤ L_k`, and budget `(q_k·L_k + 1)/T_k² → 0`) has all
coefficients `aₙ = 0` for `n ≥ 2`.  See the module docstring for the hexagonal-loop mechanism. -/
theorem quiet_path_rigidity {F : ℂ → ℂ} {a : ℕ → ℂ} {c : ℝ}
    (hc : (1 : ℝ) / 2 ≤ c) (hc0 : 0 < c)
    (hF : Differentiable ℂ F) (hsum : LSeriesSummable a c)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hsym : ∀ s : ℂ, F s = F (1 - s))
    (hquiet : ∃ (T q L : ℕ → ℝ) (γt γb : ℕ → ℝ → ℂ),
      Filter.Tendsto T Filter.atTop Filter.atTop ∧ (∀ k, 1 ≤ T k) ∧ (∀ k, 0 ≤ q k) ∧
      Filter.Tendsto (fun k => (q k * L k + 1) / (T k) ^ 2) Filter.atTop (nhds 0) ∧
      ∀ k, (∀ t ∈ Set.Icc (0 : ℝ) 1,
              1 - c ≤ (γt k t).re ∧ (γt k t).re ≤ c ∧ T k ≤ (γt k t).im ∧
                (γt k t).im ≤ 2 * T k ∧ ‖F (γt k t)‖ ≤ q k) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1,
              1 - c ≤ (γb k t).re ∧ (γb k t).re ≤ c ∧ -(2 * T k) ≤ (γb k t).im ∧
                (γb k t).im ≤ -(T k) ∧ ‖F (γb k t)‖ ≤ q k) ∧
            (γt k 0).re = c ∧ (γt k 1).re = 1 - c ∧ (γb k 0).re = 1 - c ∧ (γb k 1).re = c ∧
            (∀ t, HasDerivAt (γt k) (deriv (γt k) t) t) ∧
            (∀ t, HasDerivAt (γb k) (deriv (γb k) t) t) ∧
            Continuous (deriv (γt k)) ∧ Continuous (deriv (γb k)) ∧
            (∫ t in (0 : ℝ)..1, ‖deriv (γt k) t‖) ≤ L k ∧
            (∫ t in (0 : ℝ)..1, ‖deriv (γb k) t‖) ≤ L k) :
    ∀ n : ℕ, 2 ≤ n → a n = 0 := by
  intro n hn2
  have hn1 : 1 ≤ n := by omega
  obtain ⟨T, q, L, γt, γb, hTtop, hT1, hq0, hbudget, hk⟩ := hquiet
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num [Set.mem_Icc]
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num [Set.mem_Icc]
  -- Accessors into the per-`k` conjunction.
  have hγtc : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 - c ≤ (γt k t).re ∧ (γt k t).re ≤ c ∧
      T k ≤ (γt k t).im ∧ (γt k t).im ≤ 2 * T k ∧ ‖F (γt k t)‖ ≤ q k := fun k => (hk k).1
  have hγbc : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 - c ≤ (γb k t).re ∧ (γb k t).re ≤ c ∧
      -(2 * T k) ≤ (γb k t).im ∧ (γb k t).im ≤ -(T k) ∧ ‖F (γb k t)‖ ≤ q k := fun k => (hk k).2.1
  have hγt0re : ∀ k, (γt k 0).re = c := fun k => (hk k).2.2.1
  have hγt1re : ∀ k, (γt k 1).re = 1 - c := fun k => (hk k).2.2.2.1
  have hγb0re : ∀ k, (γb k 0).re = 1 - c := fun k => (hk k).2.2.2.2.1
  have hγb1re : ∀ k, (γb k 1).re = c := fun k => (hk k).2.2.2.2.2.1
  have hγtHD : ∀ k, ∀ t, HasDerivAt (γt k) (deriv (γt k) t) t := fun k => (hk k).2.2.2.2.2.2.1
  have hγbHD : ∀ k, ∀ t, HasDerivAt (γb k) (deriv (γb k) t) t := fun k => (hk k).2.2.2.2.2.2.2.1
  have hγtdC : ∀ k, Continuous (deriv (γt k)) := fun k => (hk k).2.2.2.2.2.2.2.2.1
  have hγbdC : ∀ k, Continuous (deriv (γb k)) := fun k => (hk k).2.2.2.2.2.2.2.2.2.1
  have hγtL : ∀ k, (∫ t in (0 : ℝ)..1, ‖deriv (γt k) t‖) ≤ L k :=
    fun k => (hk k).2.2.2.2.2.2.2.2.2.2.1
  have hγbL : ∀ k, (∫ t in (0 : ℝ)..1, ‖deriv (γb k) t‖) ≤ L k :=
    fun k => (hk k).2.2.2.2.2.2.2.2.2.2.2
  have hTpos : ∀ k, 0 < T k := fun k => lt_of_lt_of_le one_pos (hT1 k)
  have hγtCont : ∀ k, Continuous (γt k) := by
    intro k; have hd : Differentiable ℝ (γt k) := fun t => (hγtHD k t).differentiableAt
    exact hd.continuous
  have hγbCont : ∀ k, Continuous (γb k) := by
    intro k; have hd : Differentiable ℝ (γb k) := fun t => (hγbHD k t).differentiableAt
    exact hd.continuous
  -- Uniform bound on the carrier across the strip and its reflection.
  obtain ⟨B, hB⟩ := lseries_bounded_on_halfplane hsum
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB ↑c (by rw [Complex.ofReal_re]))
  have hFB : ∀ s : ℂ, c ≤ s.re → ‖F s‖ ≤ B := fun s hs => by rw [hFeq s hs]; exact hB s hs
  have hFleft : ∀ s : ℂ, s.re ≤ 1 - c → ‖F s‖ ≤ B := by
    intro s hs; rw [hsym s]; exact hFB _ (by rw [Complex.sub_re, Complex.one_re]; linarith)
  -- The entire integrand `Hf = F·E`.
  set Hf : ℂ → ℂ := fun s => F s * perronE n s with hHfdef
  have hHfp : ∀ p, Hf p = F p * perronE n p := fun _ => rfl
  have hEdiff : Differentiable ℂ (perronE n) := perronE_differentiable hn1
  have hHfdiff : Differentiable ℂ Hf := hF.mul hEdiff
  have hHfcont : Continuous Hf := hHfdiff.continuous
  -- Freeze `Hf` opaque: prevents its definition from being unfolded during the (large)
  -- definitional-equality checks in the limit-uniqueness step below.
  clear_value Hf
  -- Real facts about the three knots.
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hxppos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hxmpos : (0 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hxm1 : (1 : ℝ) ≤ (n : ℝ) - 1 / 2 := by linarith
  have hxmgt1 : (1 : ℝ) < (n : ℝ) - 1 / 2 := by linarith
  have hbase1p : (1 : ℝ) ≤ (n : ℝ) + 1 / 2 := by linarith
  set Cn : ℝ := 4 * ((n : ℝ) + 1 / 2) ^ (c + 1) with hCndef
  have hCn0 : (0 : ℝ) ≤ Cn := by rw [hCndef]; positivity
  -- Kink numerator bounds (positive- and negative-exponent regimes).
  have hKink_c : ∀ s : ℂ, s.re ≤ c → ‖perronKink n s‖ ≤ Cn := by
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
    rw [hCndef]; linarith [hb, t1, t2, t3]
  have hKink_M : ∀ (Mr : ℝ) (p : ℂ), 1 ≤ Mr → p.re = -Mr →
      ‖perronKink n p‖ ≤ 4 * ((n : ℝ) - 1 / 2) ^ (1 - Mr) := by
    intro Mr p hM hpre
    have hb := perronKink_norm_le hn1 p
    rw [hpre, show (-Mr + 1) = 1 - Mr by ring] at hb
    have hnp : (1 - Mr) ≤ 0 := by linarith
    have t1 : ((n : ℝ) + 1 / 2) ^ (1 - Mr) ≤ ((n : ℝ) - 1 / 2) ^ (1 - Mr) :=
      Real.rpow_le_rpow_of_nonpos hxmpos (by linarith) hnp
    have t3 : ((n : ℝ)) ^ (1 - Mr) ≤ ((n : ℝ) - 1 / 2) ^ (1 - Mr) :=
      Real.rpow_le_rpow_of_nonpos hxmpos (by linarith) hnp
    linarith [hb, t1, t3]
  -- Regularized-kernel bound: on any point with `|Im| ≥ τ` and `Re ≤ c`, `‖E‖ ≤ Cn·τ^{-2}`.
  have hEim : ∀ (s : ℂ) (τ : ℝ), 0 < τ → τ ≤ |s.im| → s.re ≤ c →
      ‖perronE n s‖ ≤ Cn * (τ ^ 2)⁻¹ := by
    intro s τ hτ hsim hsre
    have hsim0 : s.im ≠ 0 := by rintro h; rw [h, abs_zero] at hsim; linarith
    have h0 : s ≠ 0 := fun hh => hsim0 (by rw [hh]; simp)
    have h1 : s ≠ -1 := fun hh => hsim0 (by rw [hh]; simp)
    rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
    exact mul_le_mul (hKink_c s hsre) (kernel_im_bound hτ hsim) (norm_nonneg _) hCn0
  -- The contour-depth bound (proved below by the hexagonal loop).
  have keyM : ∀ M : ℕ, 2 ≤ M → (c : ℝ) ≤ (M : ℝ) →
      ‖∫ t : ℝ, Hf (↑c + ↑t * I)‖ ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
    intro M hM2 hMc
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hM1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
    have hMR2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    have hMle1c : -(M : ℝ) ≤ 1 - c := by linarith
    set Jc : ℂ := ∫ t : ℝ, Hf (↑c + ↑t * I) with hJcdef
    set JM : ℂ := ∫ t : ℝ, Hf (↑(-(M : ℝ)) + ↑t * I) with hJMdef
    -- Integrability on the two vertical lines Re = c and Re = −M.
    have hRint : Integrable (fun t : ℝ => Hf (↑c + ↑t * I)) := by
      have hcont : Continuous (fun t : ℝ => Hf (↑c + ↑t * I)) := hHfcont.comp (by fun_prop)
      have hbd : ∀ t : ℝ, ‖Hf (↑c + ↑t * I)‖ ≤ (Cn * B) * (c ^ 2 + t ^ 2)⁻¹ := by
        intro t
        have hre : (↑c + ↑t * I : ℂ).re = c := by simp
        rw [hHfp, norm_mul]
        have hF' : ‖F (↑c + ↑t * I)‖ ≤ B := hFB _ (le_of_eq hre.symm)
        have h0 : (↑c + ↑t * I : ℂ) ≠ 0 := by
          intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
        have h1 : (↑c + ↑t * I : ℂ) ≠ -1 := by
          intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
        have hE' : ‖perronE n (↑c + ↑t * I)‖ ≤ Cn * (c ^ 2 + t ^ 2)⁻¹ := by
          rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
          exact mul_le_mul (hKink_c _ (le_of_eq hre)) (kernel_c_bound hc0 t) (norm_nonneg _) hCn0
        calc ‖F (↑c + ↑t * I)‖ * ‖perronE n (↑c + ↑t * I)‖
            ≤ B * (Cn * (c ^ 2 + t ^ 2)⁻¹) := mul_le_mul hF' hE' (norm_nonneg _) hB0
          _ = (Cn * B) * (c ^ 2 + t ^ 2)⁻¹ := by ring
      exact ((inv_quad_int hc0).const_mul _).mono' hcont.aestronglyMeasurable
        (Eventually.of_forall hbd)
    have hleftint : Integrable (fun y : ℝ => Hf (↑(-(M : ℝ)) + ↑y * I)) := by
      have hcont : Continuous (fun y : ℝ => Hf (↑(-(M : ℝ)) + ↑y * I)) :=
        hHfcont.comp (by fun_prop)
      have hbd : ∀ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
          ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
        intro y
        have hre : (↑(-(M : ℝ)) + ↑y * I : ℂ).re = -(M : ℝ) := by simp
        rw [hHfp, norm_mul]
        have hF' : ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ≤ B := hFleft _ (by rw [hre]; exact hMle1c)
        have h0 : (↑(-(M : ℝ)) + ↑y * I : ℂ) ≠ 0 := by
          intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
        have h1 : (↑(-(M : ℝ)) + ↑y * I : ℂ) ≠ -1 := by
          intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
        have hE' : ‖perronE n (↑(-(M : ℝ)) + ↑y * I)‖
            ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
          rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
          exact mul_le_mul (hKink_M (M : ℝ) _ hM1.le hre)
            (kernel_negM_bound (M := (M : ℝ)) (y := y) hM1) (norm_nonneg _) (by positivity)
        calc ‖F (↑(-(M : ℝ)) + ↑y * I)‖ * ‖perronE n (↑(-(M : ℝ)) + ↑y * I)‖
            ≤ B * ((4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹) :=
              mul_le_mul hF' hE' (norm_nonneg _) hB0
          _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
              ring
      exact ((inv_quad_int (show (0 : ℝ) < (M : ℝ) - 1 from by linarith)).const_mul _).mono'
        hcont.aestronglyMeasurable (Eventually.of_forall hbd)
    -- The contour shift Jc = JM (hexagonal loop).
    have hshift : Jc = JM := by
      -- Global primitive of the entire integrand.
      obtain ⟨P, hP⟩ := hHfdiff.isExactOn_univ
      have hPz : ∀ z, HasDerivAt P (Hf z) z := fun z => hP z (mem_univ z)
      -- Decaying dominators.
      have hinvsq : Tendsto (fun k => ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
        have hTsq : Tendsto (fun k => (T k) ^ 2) atTop atTop := by
          simpa [pow_two] using hTtop.atTop_mul_atTop₀ hTtop
        exact hTsq.inv_tendsto_atTop
      have hgpath : Tendsto (fun k => Cn * (q k * L k + 1) * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
        have heq : (fun k => Cn * (q k * L k + 1) * ((T k) ^ 2)⁻¹)
            = fun k => Cn * ((q k * L k + 1) / (T k) ^ 2) := by
          funext k; rw [div_eq_mul_inv]; ring
        rw [heq]; simpa using hbudget.const_mul Cn
      have hgflank : Tendsto (fun k => B * Cn * ((M : ℝ) + 1 - c) * ((T k) ^ 2)⁻¹) atTop (nhds 0) := by
        simpa using hinvsq.const_mul (B * Cn * ((M : ℝ) + 1 - c))
      -- Height divergence of the path endpoints.
      have hbA : Tendsto (fun k => (γt k 0).im) atTop atTop :=
        tendsto_atTop_mono (fun k => (hγtc k 0 h0mem).2.2.1) hTtop
      have haBp : Tendsto (fun k => (γb k 1).im) atTop atBot :=
        tendsto_atBot_mono (fun k => (hγbc k 1 h1mem).2.2.2.1) (tendsto_neg_atBot_iff.mpr hTtop)
      have hbC : Tendsto (fun k => (γt k 1).im) atTop atTop :=
        tendsto_atTop_mono (fun k => (hγtc k 1 h1mem).2.2.1) hTtop
      have haG : Tendsto (fun k => (γb k 0).im) atTop atBot :=
        tendsto_atBot_mono (fun k => (hγbc k 0 h0mem).2.2.2.1) (tendsto_neg_atBot_iff.mpr hTtop)
      -- Right vertical (Re = c) converges to Jc·I.
      have hRc : Tendsto (fun k => ∫ y in (γb k 1).im..(γt k 0).im, Hf (↑c + ↑y * I)) atTop
          (nhds Jc) := intervalIntegral_tendsto_integral hRint haBp hbA
      have tP1 : Tendsto (fun k => ∫ y in (γb k 1).im..(γt k 0).im, Hf (↑c + ↑y * I) * I) atTop
          (nhds (Jc * I)) := by
        simpa only [intervalIntegral.integral_mul_const] using hRc.mul_const I
      -- Left vertical (Re = −M) converges to −(JM·I).
      have hInner4 : Tendsto (fun k => ∫ y in (γb k 0).im..(γt k 1).im, Hf (↑(-(M : ℝ)) + ↑y * I))
          atTop (nhds JM) := intervalIntegral_tendsto_integral hleftint haG hbC
      have heq4 : ∀ k, (∫ y in (γt k 1).im..(γb k 0).im, Hf (↑(-(M : ℝ)) + ↑y * I) * I)
          = -((∫ y in (γb k 0).im..(γt k 1).im, Hf (↑(-(M : ℝ)) + ↑y * I)) * I) := by
        intro k
        rw [intervalIntegral.integral_mul_const,
          intervalIntegral.integral_symm (γb k 0).im (γt k 1).im]
        ring
      have tP4 : Tendsto (fun k => ∫ y in (γt k 1).im..(γb k 0).im, Hf (↑(-(M : ℝ)) + ↑y * I) * I)
          atTop (nhds (-(JM * I))) := ((hInner4.mul_const I).neg).congr (fun k => (heq4 k).symm)
      -- Top path vanishes.
      have tP2 : Tendsto (fun k => ∫ t in (0 : ℝ)..1, Hf (γt k t) * deriv (γt k) t) atTop
          (nhds 0) := by
        refine squeeze_zero_norm (fun k => ?_) hgpath
        have hbound_pt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
            ‖Hf (γt k t) * deriv (γt k) t‖ ≤ (Cn * q k * ((T k) ^ 2)⁻¹) * ‖deriv (γt k) t‖ := by
          intro t ht
          rw [norm_mul]
          have hcl := hγtc k t ht
          have hFb : ‖F (γt k t)‖ ≤ q k := hcl.2.2.2.2
          have hRe : (γt k t).re ≤ c := hcl.2.1
          have hImabs : T k ≤ |(γt k t).im| := le_trans hcl.2.2.1 (le_abs_self _)
          have hE : ‖perronE n (γt k t)‖ ≤ Cn * ((T k) ^ 2)⁻¹ :=
            hEim (γt k t) (T k) (hTpos k) hImabs hRe
          have hHb : ‖Hf (γt k t)‖ ≤ Cn * q k * ((T k) ^ 2)⁻¹ := by
            rw [hHfp, norm_mul]
            calc ‖F (γt k t)‖ * ‖perronE n (γt k t)‖
                ≤ q k * (Cn * ((T k) ^ 2)⁻¹) :=
                  mul_le_mul hFb hE (norm_nonneg _) (le_trans (norm_nonneg _) hFb)
              _ = Cn * q k * ((T k) ^ 2)⁻¹ := by ring
          exact mul_le_mul_of_nonneg_right hHb (norm_nonneg _)
        have hnn : (0 : ℝ) ≤ Cn * q k * ((T k) ^ 2)⁻¹ :=
          mul_nonneg (mul_nonneg hCn0 (hq0 k)) (by positivity)
        have hcont_int : Continuous (fun t => Hf (γt k t) * deriv (γt k) t) :=
          (hHfcont.comp (hγtCont k)).mul (hγtdC k)
        calc ‖∫ t in (0 : ℝ)..1, Hf (γt k t) * deriv (γt k) t‖
            ≤ ∫ t in (0 : ℝ)..1, ‖Hf (γt k t) * deriv (γt k) t‖ :=
              intervalIntegral.norm_integral_le_integral_norm (by norm_num)
          _ ≤ ∫ t in (0 : ℝ)..1, (Cn * q k * ((T k) ^ 2)⁻¹) * ‖deriv (γt k) t‖ :=
              intervalIntegral.integral_mono_on (by norm_num)
                (hcont_int.norm.intervalIntegrable 0 1)
                ((continuous_const.mul (hγtdC k).norm).intervalIntegrable 0 1) hbound_pt
          _ = (Cn * q k * ((T k) ^ 2)⁻¹) * ∫ t in (0 : ℝ)..1, ‖deriv (γt k) t‖ :=
              intervalIntegral.integral_const_mul _ _
          _ ≤ (Cn * q k * ((T k) ^ 2)⁻¹) * L k := mul_le_mul_of_nonneg_left (hγtL k) hnn
          _ ≤ Cn * (q k * L k + 1) * ((T k) ^ 2)⁻¹ := by
              have e : Cn * (q k * L k + 1) * ((T k) ^ 2)⁻¹
                  = (Cn * q k * ((T k) ^ 2)⁻¹) * L k + Cn * ((T k) ^ 2)⁻¹ := by ring
              rw [e]; linarith [mul_nonneg hCn0 (show (0 : ℝ) ≤ ((T k) ^ 2)⁻¹ by positivity)]
      -- Bottom path vanishes.
      have tP6 : Tendsto (fun k => ∫ t in (0 : ℝ)..1, Hf (γb k t) * deriv (γb k) t) atTop
          (nhds 0) := by
        refine squeeze_zero_norm (fun k => ?_) hgpath
        have hbound_pt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
            ‖Hf (γb k t) * deriv (γb k) t‖ ≤ (Cn * q k * ((T k) ^ 2)⁻¹) * ‖deriv (γb k) t‖ := by
          intro t ht
          rw [norm_mul]
          have hcl := hγbc k t ht
          have hFb : ‖F (γb k t)‖ ≤ q k := hcl.2.2.2.2
          have hRe : (γb k t).re ≤ c := hcl.2.1
          have hImle : (γb k t).im ≤ -(T k) := hcl.2.2.2.1
          have hImabs : T k ≤ |(γb k t).im| := by
            rw [abs_of_nonpos (by linarith [hTpos k] : (γb k t).im ≤ 0)]; linarith
          have hE : ‖perronE n (γb k t)‖ ≤ Cn * ((T k) ^ 2)⁻¹ :=
            hEim (γb k t) (T k) (hTpos k) hImabs hRe
          have hHb : ‖Hf (γb k t)‖ ≤ Cn * q k * ((T k) ^ 2)⁻¹ := by
            rw [hHfp, norm_mul]
            calc ‖F (γb k t)‖ * ‖perronE n (γb k t)‖
                ≤ q k * (Cn * ((T k) ^ 2)⁻¹) :=
                  mul_le_mul hFb hE (norm_nonneg _) (le_trans (norm_nonneg _) hFb)
              _ = Cn * q k * ((T k) ^ 2)⁻¹ := by ring
          exact mul_le_mul_of_nonneg_right hHb (norm_nonneg _)
        have hnn : (0 : ℝ) ≤ Cn * q k * ((T k) ^ 2)⁻¹ :=
          mul_nonneg (mul_nonneg hCn0 (hq0 k)) (by positivity)
        have hcont_int : Continuous (fun t => Hf (γb k t) * deriv (γb k) t) :=
          (hHfcont.comp (hγbCont k)).mul (hγbdC k)
        calc ‖∫ t in (0 : ℝ)..1, Hf (γb k t) * deriv (γb k) t‖
            ≤ ∫ t in (0 : ℝ)..1, ‖Hf (γb k t) * deriv (γb k) t‖ :=
              intervalIntegral.norm_integral_le_integral_norm (by norm_num)
          _ ≤ ∫ t in (0 : ℝ)..1, (Cn * q k * ((T k) ^ 2)⁻¹) * ‖deriv (γb k) t‖ :=
              intervalIntegral.integral_mono_on (by norm_num)
                (hcont_int.norm.intervalIntegrable 0 1)
                ((continuous_const.mul (hγbdC k).norm).intervalIntegrable 0 1) hbound_pt
          _ = (Cn * q k * ((T k) ^ 2)⁻¹) * ∫ t in (0 : ℝ)..1, ‖deriv (γb k) t‖ :=
              intervalIntegral.integral_const_mul _ _
          _ ≤ (Cn * q k * ((T k) ^ 2)⁻¹) * L k := mul_le_mul_of_nonneg_left (hγbL k) hnn
          _ ≤ Cn * (q k * L k + 1) * ((T k) ^ 2)⁻¹ := by
              have e : Cn * (q k * L k + 1) * ((T k) ^ 2)⁻¹
                  = (Cn * q k * ((T k) ^ 2)⁻¹) * L k + Cn * ((T k) ^ 2)⁻¹ := by ring
              rw [e]; linarith [mul_nonneg hCn0 (show (0 : ℝ) ≤ ((T k) ^ 2)⁻¹ by positivity)]
      -- Top flank vanishes.
      have tP3 : Tendsto (fun k => ∫ x in (1 - c)..(-(M : ℝ)), Hf (↑x + ↑((γt k 1).im) * I) * 1)
          atTop (nhds 0) := by
        refine squeeze_zero_norm (fun k => ?_) hgflank
        have hbnd : ∀ x ∈ Set.uIoc (1 - c) (-(M : ℝ)),
            ‖Hf (↑x + ↑((γt k 1).im) * I) * 1‖ ≤ B * Cn * ((T k) ^ 2)⁻¹ := by
          intro x hx
          have hxle : x ≤ 1 - c := by
            rcases Set.mem_uIoc.mp hx with ⟨_, h2⟩ | ⟨_, h2⟩
            · linarith [hMle1c]
            · exact h2
          rw [mul_one, hHfp (↑x + ↑((γt k 1).im) * I), norm_mul]
          have hsre : (↑x + ↑((γt k 1).im) * I : ℂ).re = x := by simp
          have hsim : (↑x + ↑((γt k 1).im) * I : ℂ).im = (γt k 1).im := by simp
          have hFb : ‖F (↑x + ↑((γt k 1).im) * I)‖ ≤ B := hFleft _ (by rw [hsre]; exact hxle)
          have hImabs : T k ≤ |(↑x + ↑((γt k 1).im) * I : ℂ).im| := by
            rw [hsim]; exact le_trans (hγtc k 1 h1mem).2.2.1 (le_abs_self _)
          have hRec : (↑x + ↑((γt k 1).im) * I : ℂ).re ≤ c := by rw [hsre]; linarith
          have hE : ‖perronE n (↑x + ↑((γt k 1).im) * I)‖ ≤ Cn * ((T k) ^ 2)⁻¹ :=
            hEim _ (T k) (hTpos k) hImabs hRec
          calc ‖F (↑x + ↑((γt k 1).im) * I)‖ * ‖perronE n (↑x + ↑((γt k 1).im) * I)‖
              ≤ B * (Cn * ((T k) ^ 2)⁻¹) := mul_le_mul hFb hE (norm_nonneg _) hB0
            _ = B * Cn * ((T k) ^ 2)⁻¹ := by ring
        calc ‖∫ x in (1 - c)..(-(M : ℝ)), Hf (↑x + ↑((γt k 1).im) * I) * 1‖
            ≤ (B * Cn * ((T k) ^ 2)⁻¹) * |(-(M : ℝ)) - (1 - c)| :=
              intervalIntegral.norm_integral_le_of_norm_le_const hbnd
          _ = B * Cn * ((M : ℝ) + 1 - c) * ((T k) ^ 2)⁻¹ := by
              rw [abs_of_nonpos (show (-(M : ℝ)) - (1 - c) ≤ 0 by linarith)]; ring
      -- Bottom flank vanishes.
      have tP5 : Tendsto (fun k => ∫ x in (-(M : ℝ))..(1 - c), Hf (↑x + ↑((γb k 0).im) * I) * 1)
          atTop (nhds 0) := by
        refine squeeze_zero_norm (fun k => ?_) hgflank
        have hbnd : ∀ x ∈ Set.uIoc (-(M : ℝ)) (1 - c),
            ‖Hf (↑x + ↑((γb k 0).im) * I) * 1‖ ≤ B * Cn * ((T k) ^ 2)⁻¹ := by
          intro x hx
          have hxle : x ≤ 1 - c := by
            rcases Set.mem_uIoc.mp hx with ⟨_, h2⟩ | ⟨_, h2⟩
            · exact h2
            · linarith [hMle1c]
          rw [mul_one, hHfp (↑x + ↑((γb k 0).im) * I), norm_mul]
          have hsre : (↑x + ↑((γb k 0).im) * I : ℂ).re = x := by simp
          have hsim : (↑x + ↑((γb k 0).im) * I : ℂ).im = (γb k 0).im := by simp
          have hFb : ‖F (↑x + ↑((γb k 0).im) * I)‖ ≤ B := hFleft _ (by rw [hsre]; exact hxle)
          have hImle : (γb k 0).im ≤ -(T k) := (hγbc k 0 h0mem).2.2.2.1
          have hImabs : T k ≤ |(↑x + ↑((γb k 0).im) * I : ℂ).im| := by
            rw [hsim, abs_of_nonpos (by linarith [hTpos k] : (γb k 0).im ≤ 0)]; linarith
          have hRec : (↑x + ↑((γb k 0).im) * I : ℂ).re ≤ c := by rw [hsre]; linarith
          have hE : ‖perronE n (↑x + ↑((γb k 0).im) * I)‖ ≤ Cn * ((T k) ^ 2)⁻¹ :=
            hEim _ (T k) (hTpos k) hImabs hRec
          calc ‖F (↑x + ↑((γb k 0).im) * I)‖ * ‖perronE n (↑x + ↑((γb k 0).im) * I)‖
              ≤ B * (Cn * ((T k) ^ 2)⁻¹) := mul_le_mul hFb hE (norm_nonneg _) hB0
            _ = B * Cn * ((T k) ^ 2)⁻¹ := by ring
        calc ‖∫ x in (-(M : ℝ))..(1 - c), Hf (↑x + ↑((γb k 0).im) * I) * 1‖
            ≤ (B * Cn * ((T k) ^ 2)⁻¹) * |(1 - c) - (-(M : ℝ))| :=
              intervalIntegral.norm_integral_le_of_norm_le_const hbnd
          _ = B * Cn * ((M : ℝ) + 1 - c) * ((T k) ^ 2)⁻¹ := by
              rw [abs_of_nonneg (show (0 : ℝ) ≤ (1 - c) - (-(M : ℝ)) by linarith)]; ring
      -- Hexagonal loop telescopes to 0 for each k.
      have hsum6 : ∀ k,
          (∫ y in (γb k 1).im..(γt k 0).im, Hf (↑c + ↑y * I) * I)
            + (∫ t in (0 : ℝ)..1, Hf (γt k t) * deriv (γt k) t)
            + (∫ x in (1 - c)..(-(M : ℝ)), Hf (↑x + ↑((γt k 1).im) * I) * 1)
            + (∫ y in (γt k 1).im..(γb k 0).im, Hf (↑(-(M : ℝ)) + ↑y * I) * I)
            + (∫ x in (-(M : ℝ))..(1 - c), Hf (↑x + ↑((γb k 0).im) * I) * 1)
            + (∫ t in (0 : ℝ)..1, Hf (γb k t) * deriv (γb k) t) = 0 := by
        intro k
        have eA : (↑c : ℂ) + ↑((γt k 0).im) * I = γt k 0 := by
          rw [← hγt0re k, Complex.re_add_im]
        have eBp : (↑c : ℂ) + ↑((γb k 1).im) * I = γb k 1 := by
          rw [← hγb1re k, Complex.re_add_im]
        have eC : (↑(1 - c) : ℂ) + ↑((γt k 1).im) * I = γt k 1 := by
          rw [← hγt1re k, Complex.re_add_im]
        have eG : (↑(1 - c) : ℂ) + ↑((γb k 0).im) * I = γb k 0 := by
          rw [← hγb0re k, Complex.re_add_im]
        have hP1 : (∫ y in (γb k 1).im..(γt k 0).im, Hf (↑c + ↑y * I) * I)
            = P (↑c + ↑((γt k 0).im) * I) - P (↑c + ↑((γb k 1).im) * I) := by
          refine path_ftc hPz (δ := fun y => (↑c : ℂ) + ↑y * I) (δ' := fun _ => I)
            (fun y _ => hasDerivAt_vert c y) ?_
          exact ((hHfcont.comp (by fun_prop)).mul continuous_const).intervalIntegrable _ _
        have hP2 : (∫ t in (0 : ℝ)..1, Hf (γt k t) * deriv (γt k) t)
            = P (γt k 1) - P (γt k 0) := by
          refine path_ftc hPz (δ := γt k) (δ' := deriv (γt k)) (fun t _ => hγtHD k t) ?_
          exact ((hHfcont.comp (hγtCont k)).mul (hγtdC k)).intervalIntegrable _ _
        have hP3 : (∫ x in (1 - c)..(-(M : ℝ)), Hf (↑x + ↑((γt k 1).im) * I) * 1)
            = P (↑(-(M : ℝ)) + ↑((γt k 1).im) * I) - P (↑(1 - c) + ↑((γt k 1).im) * I) := by
          refine path_ftc hPz (δ := fun x => (↑x : ℂ) + ↑((γt k 1).im) * I) (δ' := fun _ => 1)
            (fun x _ => hasDerivAt_horiz ((γt k 1).im) x) ?_
          exact ((hHfcont.comp (by fun_prop)).mul continuous_const).intervalIntegrable _ _
        have hP4 : (∫ y in (γt k 1).im..(γb k 0).im, Hf (↑(-(M : ℝ)) + ↑y * I) * I)
            = P (↑(-(M : ℝ)) + ↑((γb k 0).im) * I) - P (↑(-(M : ℝ)) + ↑((γt k 1).im) * I) := by
          refine path_ftc hPz (δ := fun y => (↑(-(M : ℝ)) : ℂ) + ↑y * I) (δ' := fun _ => I)
            (fun y _ => hasDerivAt_vert (-(M : ℝ)) y) ?_
          exact ((hHfcont.comp (by fun_prop)).mul continuous_const).intervalIntegrable _ _
        have hP5 : (∫ x in (-(M : ℝ))..(1 - c), Hf (↑x + ↑((γb k 0).im) * I) * 1)
            = P (↑(1 - c) + ↑((γb k 0).im) * I) - P (↑(-(M : ℝ)) + ↑((γb k 0).im) * I) := by
          refine path_ftc hPz (δ := fun x => (↑x : ℂ) + ↑((γb k 0).im) * I) (δ' := fun _ => 1)
            (fun x _ => hasDerivAt_horiz ((γb k 0).im) x) ?_
          exact ((hHfcont.comp (by fun_prop)).mul continuous_const).intervalIntegrable _ _
        have hP6 : (∫ t in (0 : ℝ)..1, Hf (γb k t) * deriv (γb k) t)
            = P (γb k 1) - P (γb k 0) := by
          refine path_ftc hPz (δ := γb k) (δ' := deriv (γb k)) (fun t _ => hγbHD k t) ?_
          exact ((hHfcont.comp (hγbCont k)).mul (hγbdC k)).intervalIntegrable _ _
        rw [hP1, hP2, hP3, hP4, hP5, hP6, eA, eBp, eC, eG]
        ring
      -- Uniqueness of the limit forces (Jc − JM)·I = 0.
      have key0 : (Jc - JM) * I = 0 := by
        have h := ((((tP1.add tP2).add tP3).add tP4).add tP5).add tP6
        rw [show (Jc * I + 0 + 0 + -(JM * I) + 0 + 0) = (Jc - JM) * I by ring] at h
        have h0 : Tendsto (fun k =>
            (∫ y in (γb k 1).im..(γt k 0).im, Hf (↑c + ↑y * I) * I)
              + (∫ t in (0 : ℝ)..1, Hf (γt k t) * deriv (γt k) t)
              + (∫ x in (1 - c)..(-(M : ℝ)), Hf (↑x + ↑((γt k 1).im) * I) * 1)
              + (∫ y in (γt k 1).im..(γb k 0).im, Hf (↑(-(M : ℝ)) + ↑y * I) * I)
              + (∫ x in (-(M : ℝ))..(1 - c), Hf (↑x + ↑((γb k 0).im) * I) * 1)
              + (∫ t in (0 : ℝ)..1, Hf (γb k t) * deriv (γb k) t)) atTop (nhds 0) := by
          have he : (fun k =>
              (∫ y in (γb k 1).im..(γt k 0).im, Hf (↑c + ↑y * I) * I)
                + (∫ t in (0 : ℝ)..1, Hf (γt k t) * deriv (γt k) t)
                + (∫ x in (1 - c)..(-(M : ℝ)), Hf (↑x + ↑((γt k 1).im) * I) * 1)
                + (∫ y in (γt k 1).im..(γb k 0).im, Hf (↑(-(M : ℝ)) + ↑y * I) * I)
                + (∫ x in (-(M : ℝ))..(1 - c), Hf (↑x + ↑((γb k 0).im) * I) * 1)
                + (∫ t in (0 : ℝ)..1, Hf (γb k t) * deriv (γb k) t)) = fun _ => (0 : ℂ) :=
            funext hsum6
          rw [he]; exact tendsto_const_nhds
        exact (tendsto_nhds_unique h0 h).symm
      rcases mul_eq_zero.mp key0 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h Complex.I_ne_zero
    -- Left-flank modulus bound on the full line Re = −M.
    have hJMbd : ‖JM‖ ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
      have hleftbd : ∀ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
          ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
        intro y
        have hre : (↑(-(M : ℝ)) + ↑y * I : ℂ).re = -(M : ℝ) := by simp
        rw [hHfp, norm_mul]
        have hF' : ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ≤ B := hFleft _ (by rw [hre]; exact hMle1c)
        have h0 : (↑(-(M : ℝ)) + ↑y * I : ℂ) ≠ 0 := by
          intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
        have h1 : (↑(-(M : ℝ)) + ↑y * I : ℂ) ≠ -1 := by
          intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
        have hE' : ‖perronE n (↑(-(M : ℝ)) + ↑y * I)‖
            ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
          rw [perronE_eq n h0 h1, div_eq_mul_inv, norm_mul]
          exact mul_le_mul (hKink_M (M : ℝ) _ hM1.le hre)
            (kernel_negM_bound (M := (M : ℝ)) (y := y) hM1) (norm_nonneg _) (by positivity)
        calc ‖F (↑(-(M : ℝ)) + ↑y * I)‖ * ‖perronE n (↑(-(M : ℝ)) + ↑y * I)‖
            ≤ B * ((4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹) :=
              mul_le_mul hF' hE' (norm_nonneg _) hB0
          _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := by
              ring
      have hqle : ∫ y : ℝ, (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ ≤ Real.pi := by
        rw [← integral_univ_inv_one_add_sq]
        refine integral_mono (inv_quad_int (show (0 : ℝ) < (M : ℝ) - 1 from by linarith))
          integrable_inv_one_add_sq (fun y => ?_)
        refine inv_anti₀ (by positivity) ?_
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ (M : ℝ) from hMnn)
          (show (0 : ℝ) ≤ (M : ℝ) - 2 from by linarith), sq_nonneg y]
      have hdomint : Integrable (fun y : ℝ =>
          (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹) :=
        (inv_quad_int (show (0 : ℝ) < (M : ℝ) - 1 from by linarith)).const_mul _
      have hCnn : (0 : ℝ) ≤ 4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B :=
        mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hxmpos.le _)) hB0
      have hleftfull : ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
          ≤ 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by
        calc ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖
            ≤ ∫ y : ℝ, (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) *
                (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := integral_mono hleftint.norm hdomint hleftbd
          _ = (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) *
                ∫ y : ℝ, (((M : ℝ) - 1) ^ 2 + y ^ 2)⁻¹ := integral_const_mul _ _
          _ ≤ (4 * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) * B) * Real.pi :=
              mul_le_mul_of_nonneg_left hqle hCnn
          _ = 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)) := by ring
      calc ‖JM‖ ≤ ∫ y : ℝ, ‖Hf (↑(-(M : ℝ)) + ↑y * I)‖ := by
            rw [hJMdef]; exact norm_integral_le_integral_norm _
        _ ≤ _ := hleftfull
    rw [hshift]; exact hJMbd
  -- Send the contour to infinity.
  have hMtendsto : Tendsto (fun M : ℕ => 4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
      atTop (nhds 0) := by
    have hbase : Tendsto (fun M : ℕ => ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) atTop (nhds 0) := by
      have h1 : (fun M : ℕ => ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))
          = fun M : ℕ => ((n : ℝ) - 1 / 2) * (((n : ℝ) - 1 / 2)⁻¹) ^ M := by
        funext M
        rw [Real.rpow_sub hxmpos, Real.rpow_one, Real.rpow_natCast, div_eq_mul_inv, inv_pow]
      rw [h1]
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ ((n : ℝ) - 1 / 2)⁻¹)
        (by rw [inv_lt_one_iff₀]; right; exact hxmgt1)
      simpa using this.const_mul ((n : ℝ) - 1 / 2)
    simpa using hbase.const_mul (4 * Real.pi * B)
  have hbound_an : ‖a n * (1 / 2)‖ ≤ 0 := by
    have hR : a n * (1 / 2) = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, Hf (↑c + ↑t * I) := by
      rw [hHfdef]; exact perronSecondDiff_integral hc0 hsum hF hFeq hn1
    have hev : ∀ᶠ M : ℕ in atTop, ‖a n * (1 / 2)‖
        ≤ (1 / (2 * Real.pi)) * (4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ))) := by
      filter_upwards [eventually_ge_atTop (max 2 ⌈c⌉₊)] with M hM
      have hM2 : 2 ≤ M := le_trans (le_max_left _ _) hM
      have hMc : (c : ℝ) ≤ (M : ℝ) :=
        le_trans (Nat.le_ceil c) (by exact_mod_cast le_trans (le_max_right _ _) hM)
      rw [hR, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (keyM M hM2 hMc) (by positivity)
    have hlim : Tendsto (fun M : ℕ => (1 / (2 * Real.pi)) *
        (4 * Real.pi * B * ((n : ℝ) - 1 / 2) ^ (1 - (M : ℝ)))) atTop (nhds 0) := by
      simpa using hMtendsto.const_mul (1 / (2 * Real.pi))
    exact ge_of_tendsto hlim hev
  have han2 : a n * (1 / 2) = 0 := norm_eq_zero.mp (le_antisymm hbound_an (norm_nonneg _))
  exact (mul_eq_zero.mp han2).resolve_right (by norm_num)

end RHTower
