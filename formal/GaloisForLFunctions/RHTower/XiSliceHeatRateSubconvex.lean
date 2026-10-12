import GaloisForLFunctions.RHTower.XiSliceHeatRateOnePlusDelta
import GaloisForLFunctions.RHTower.XiSliceEulerDerivativeLowerBoundNearEdge
import GaloisForLFunctions.RHTower.ZetaSubconvexStripBound

/-!
# Subconvexity lowers the heat rate of the WD slice below `1/log t`

Let `S(t, x) = ξ(½+x+it) ξ(½−x+it)` and let `T_n(λ, 0, t)` be the Taylor coefficients at `0` of the
heated slice `e^{(λ/2)∂_x²} S(t, ·)`.

**Theorem** (`DeBruijn.exists_xiSliceHeatTransfer_pos_heat_subconvex`).  There is `t₀` such that
for `|t| ≥ t₀`, every heat `λ ≥ (19/25)/log |t|` and every `m`, `T_{2m}(λ, 0, t) > 0`.

The convexity bound gives the rate `(1+δ)/log t` (`exists_xiSliceHeatTransfer_pos_heat_one_add_over_log`).
With a critical-line exponent `μ` the slice inside the strip satisfies
`|S(t, x)| ≲ S(t, ½+2η) t^{−η − c(½+η−|x|)}`, `c = 1 − 2(μ+η)/(½+η)`
(`exists_norm_xiSliceProduct_le_strip_subconvex`, from Weyl's bound
`norm_riemannZeta_half_le_sixth`, `μ = 1/6`).  The Gaussian of variance `κ/log t` has its saddle against `t^x` at `x = κ`, and the
heat `κ/log t` is admissible as soon as `κ(1 − c²)/2 > ½ − c/2 + η`, i.e. `κ > 1/(2 − 4μ)` in the
limit `η → 0`.  At `μ = 1/6` this is `κ > 3/4`; `κ = 19/25` with `η = 1/1000` is
`exists_xiSliceHeatTransfer_pos_low_order_saddle` with `subconvex_gap_pos`.

Proof of the low orders `1 ≤ N = 2m ≤ log t`, with `L = log t`, `λ = κ/L`, `x = √λ w` and
`√(2π) T_N = ∫ e^{−w²/2} S^{(N)}(x)/N! dw`:

* `|x| ≥ ½`: the integrand is `≥ 0` (absolute monotonicity of the slice from `½`);
* `x ∈ [κ, κ + 1/100]`: the Euler-point lower bound from `x₀ = 3/4`
  (`exists_iteratedDeriv_xiSliceProduct_ge_euler_near_edge`) and `x − x²/(2κ) = κ/2 − (x−κ)²/(2κ)`
  give the integrand `≥ S(½+2η) e^{aL − O(1)} L′ᴺ/N! (log t)^{−1/2}`, `a = κ/2 − ½ − 2η − 1/15000`;
* `|x| < ½`: Cauchy's estimate on the circle of radius `N/(L + 2C)` and the subconvex strip bound give
  `|S^{(N)}(x)|/N! ≤ C S(½+2η) e^{N − ηL − cL(½−|x|)} ((L+2C)/N)ᴺ`, and
  `e^{−w²/2 + cL√λ|w|} ≤ e^{c²κL/2}`; so the inner integrand is `≥ −C S(½+2η) e^{N − bL} ((L+2C)/N)ᴺ`
  with `b = η + c/2 − c²κ/2`.

When `a + b > 0` the window wins (`heat_window_comparison_gen`).  Below `κ = ½` the saddle leaves the
Euler region: no bound on the size of `ζ` alone can push the rate under `½/log t`.
-/

open Complex MeasureTheory Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The gain exponent of the subconvex strip bound: `1 − 2(1/6 + η)/(1/2 + η)`. -/
def subconvexGain (η : ℝ) : ℝ := 1 - 2 * (1 / 6 + η) / (1 / 2 + η)

theorem subconvexGain_nonneg {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 10) : 0 ≤ subconvexGain η := by
  unfold subconvexGain
  rw [sub_nonneg, div_le_one (by linarith)]
  linarith

theorem subconvexGain_le_one {η : ℝ} (hη : 0 < η) : subconvexGain η ≤ 1 := by
  unfold subconvexGain
  have : 0 ≤ 2 * (1 / 6 + η) / (1 / 2 + η) := by positivity
  linarith

/-- **The slice inside the strip, subconvex form.**  For `|a| < ½ + η`,
`|S(t, a + ic)| ≤ C S(t, ½+2η) t^{−η − c(½+η−|a|)}`, `c = subconvexGain η`. -/
theorem exists_norm_xiSliceProduct_le_strip_subconvex {η R₁ : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 10) (hR₁ : 1 ≤ R₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ t a c : ℝ, 32 * R₁ + 16 ≤ t → |c| ≤ R₁ → |a| < 1 / 2 + η →
      ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
        ≤ C * xiSliceReal t (1 / 2 + 2 * η)
          * t ^ (-(η + subconvexGain η * (1 / 2 + η - |a|))) := by
  obtain ⟨Cs, hCs, hsub⟩ := exists_norm_riemannZeta_le_subconvex hη (by linarith)
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = 1 / (1 + 1 / (2 * η)) := ⟨_, rfl⟩
  have hm₀0 : 0 < m₀ := by rw [hm₀]; positivity
  refine ⟨Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (Cs / m₀) ^ 2, by positivity, ?_⟩
  intro t a c ht hc ha
  have ht0 : 0 < t := by linarith
  have hct : |c| ≤ t / 2 := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 1 / 2 + 2 * η := ⟨_, rfl⟩
  have haR : |a| ≤ R := by rw [hR]; linarith
  have hz₀ := inv_le_norm_riemannZeta_saddle t hη (le_refl (1 / 2 + 2 * η))
  rw [← hm₀, ← hR] at hz₀
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (1 / 6 + η) * (1 + η - (1 / 2 + |a|)) / (1 / 2 + η) := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by
    rw [he]; exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hBc : ∀ c' : ℝ, |c'| ≤ R₁ →
      ‖riemannZeta (((1 / 2 + |a| : ℝ) : ℂ) + ((t + c' : ℝ) : ℂ) * I)‖ ≤ Cs * (2 * t) ^ e := by
    intro c' hc'
    have hc'' := abs_le.mp hc'
    refine (hsub _ _ (by linarith [abs_nonneg a]) (by linarith) (by linarith)).trans ?_
    rw [← he]
    gcongr
    · linarith
    · linarith
  have hB2 : ‖riemannZeta (((1 / 2 + |a| : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖
      ≤ Cs * (2 * t) ^ e := by
    have := hBc (-c) (by rwa [abs_neg]); rwa [← sub_eq_add_neg] at this
  have h := norm_xiSliceProduct_le_of_ref (by linarith) haR hct hm₀0 hz₀ (hBc c hc) hB2
  have hpow : (Cs * (2 * t) ^ e / m₀) ^ 2 = (Cs / m₀) ^ 2 * (2 * t) ^ (2 * e) := by
    rw [div_pow, mul_pow, ← Real.rpow_natCast ((2 * t) ^ e), ← Real.rpow_mul (by positivity)]
    push_cast
    ring_nf
  have hexpX := exp_shift_decay_le (d := R - |a|) (c := c) (a := |a|) ht le_rfl
    (by linarith) (by rw [hR]; linarith [abs_nonneg a]) hc (by linarith)
  have h2e : 2 * e ≤ 1 := by
    rw [he]
    have h1 : (1 + η - (1 / 2 + |a|)) / (1 / 2 + η) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith [abs_nonneg a]
    have h2 : 0 ≤ (1 + η - (1 / 2 + |a|)) / (1 / 2 + η) := div_nonneg (by linarith) (by linarith)
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * (1 / 6 + η))
    rw [mul_div_assoc]; linarith
  have hexpeq : 2 * e + -(R - |a|) = -(η + subconvexGain η * (1 / 2 + η - |a|)) := by
    rw [he, hR, subconvexGain]; field_simp; ring
  have hkey : (2 * t) ^ (2 * e) * t ^ (-(R - |a|))
      ≤ 2 * t ^ (-(η + subconvexGain η * (1 / 2 + η - |a|))) := by
    rw [Real.mul_rpow (by norm_num) ht0.le, mul_assoc, ← Real.rpow_add ht0, hexpeq]
    have h2 : (2 : ℝ) ^ (2 * e) ≤ 2 := by
      calc (2 : ℝ) ^ (2 * e) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h2e
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hS := xiSliceReal_nonneg t R
  rw [hpow] at h
  calc ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
      ≤ xiSliceReal t R * ((Cs / m₀) ^ 2 * (2 * t) ^ (2 * e))
        * Real.exp (-(R - |a|) * Real.log (t / (2 * Real.pi))
          + 12 * (R - |a| + |c|) / t + 4 * (1 / 2 + |a|) / t) := h
    _ ≤ xiSliceReal t R * ((Cs / m₀) ^ 2 * (2 * t) ^ (2 * e))
        * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(R - |a|)))) :=
        mul_le_mul_of_nonneg_left hexpX (by positivity)
    _ = xiSliceReal t R * (Cs / m₀) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
        * ((2 * t) ^ (2 * e) * t ^ (-(R - |a|))) := by ring
    _ ≤ xiSliceReal t R * (Cs / m₀) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
        * (2 * t ^ (-(η + subconvexGain η * (1 / 2 + η - |a|)))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (Cs / m₀) ^ 2 * xiSliceReal t (1 / 2 + 2 * η)
        * t ^ (-(η + subconvexGain η * (1 / 2 + η - |a|))) := by rw [hR]; ring

/-- **Inner Cauchy bound, subconvex form.**  For `|x| < ½` and `1 ≤ N ≤ log t`, with
`c = subconvexGain η` and `E = C_η`,
`|S^{(N)}(x)|/N! ≤ C S(½+2η) e^{N − η log t − c log t (½ − |x|)} ((log t + 2E)/N)ᴺ`. -/
theorem exists_norm_iteratedDeriv_xiSliceProduct_le_inner_subconvex {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 10) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 80 ≤ t → ∀ x : ℝ, |x| < 1 / 2 → ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ≤ Real.log t →
      ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖ / N.factorial ≤
        C * xiSliceReal t (1 / 2 + 2 * η) * (Real.exp (N - η * Real.log t
          - subconvexGain η * Real.log t * (1 / 2 - |x|))
          * ((Real.log t + 2 * xiEulerConstant η) / N) ^ N) := by
  obtain ⟨C₁, hC₁, hS₁⟩ := exists_norm_xiSliceProduct_le_strip_subconvex (R₁ := 2) hη hη1
    (by norm_num)
  obtain ⟨C₂, hC₂, hS₂⟩ := exists_norm_xiSliceProduct_le_strip (R₁ := 2) hη (by linarith)
    (by norm_num)
  have hc0 := subconvexGain_nonneg hη hη1
  have hc1 := subconvexGain_le_one hη
  refine ⟨C₁ + C₂, by linarith, fun t ht x hx N hN1 hNu => ?_⟩
  have ht0 : 0 < t := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = subconvexGain η := ⟨_, rfl⟩
  rw [← hudef] at hNu ⊢
  rw [← hEdef, ← hcdef]
  rw [← hcdef] at hc0 hc1
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hu0 : 0 < u := by linarith
  have hu2E : 0 < u + 2 * E := by linarith
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = xiSliceReal t (1 / 2 + 2 * η) := ⟨_, rfl⟩
  have hS₀0 : 0 ≤ S₀ := hS₀ ▸ xiSliceReal_nonneg t _
  obtain ⟨r, hrdef⟩ : ∃ r, r = N / (u + 2 * E) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hu2E]; linarith
  have hrN : (u + 2 * E) * r = N := by rw [hrdef]; field_simp
  have hxa : 0 < 1 / 2 - |x| := by linarith
  set M := (C₁ + C₂) * S₀ * Real.exp ((u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|)) with hM
  have hMb : ∀ z ∈ sphere (x : ℂ) r, ‖xiSliceProduct t z‖ ≤ M := by
    intro z hz
    have hzr : ‖z - x‖ = r := mem_sphere_iff_norm.mp hz
    have hza : |z.re - x| ≤ r := by
      have := Complex.abs_re_le_norm (z - x)
      rw [Complex.sub_re, Complex.ofReal_re] at this
      linarith
    have hzc : |z.im| ≤ r := by
      have := Complex.abs_im_le_norm (z - x)
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      linarith
    have hz' : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    have habs : |z.re| ≤ |x| + r := by
      have := abs_add_le (z.re - x) x
      rw [sub_add_cancel] at this
      linarith
    rw [hz']
    by_cases ha : |z.re| < 1 / 2 + η
    · have h := hS₁ t z.re z.im (by linarith) (by linarith) ha
      rw [← hS₀, ← hcdef] at h
      refine h.trans ?_
      rw [Real.rpow_def_of_pos ht0, ← hudef, hM]
      have hexp : u * -(η + c * (1 / 2 + η - |z.re|))
          ≤ (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|) := by
        have h2 : |z.re| - |x| - η ≤ r := by linarith only [habs, hη]
        have h3 : c * u * (|z.re| - |x| - η) ≤ c * u * r :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have h4 : c * (u * r) ≤ 1 * (u * r) :=
          mul_le_mul_of_nonneg_right hc1 (by positivity)
        have h5 : 0 ≤ 2 * E * r := by positivity
        have e1 : c * u * r = c * (u * r) := by ring
        have e2 : (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|) - u * -(η + c * (1 / 2 + η - |z.re|))
            = (u + 2 * E) * r - c * u * (|z.re| - |x| - η) := by ring
        have e3 : (u + 2 * E) * r = 1 * (u * r) + 2 * E * r := by ring
        linarith only [h3, h4, h5, e1, e2, e3]
      calc C₁ * S₀ * Real.exp (u * -(η + c * (1 / 2 + η - |z.re|)))
          ≤ (C₁ + C₂) * S₀ * Real.exp (u * -(η + c * (1 / 2 + η - |z.re|))) := by
            gcongr; linarith
        _ ≤ (C₁ + C₂) * S₀ * Real.exp ((u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|)) := by
            gcongr
    · push Not at ha
      obtain ⟨-, hout⟩ := hS₂ t z.re z.im (by linarith) (by linarith)
      refine le_trans (hout ha (by linarith)) ?_
      set y := max |z.re| (1 / 2 + 2 * η) with hy
      have hy1 : 1 / 2 + 2 * η ≤ y := le_max_right _ _
      have hy2 : y ≤ t / 2 := max_le (by linarith) (by linarith)
      have hgrow := (xiSliceReal_growth_euler (t := t) hη (by linarith) (y₁ := 1 / 2 + 2 * η)
        (y₂ := y) (by linarith) hy1 hy2).2
      rw [← hudef, ← hEdef, ← hS₀] at hgrow
      have hexp : (u + 2 * E) * (y - (1 / 2 + 2 * η))
          ≤ (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|) := by
        have hcu : c * u * (1 / 2 - |x|) ≤ u * (1 / 2 - |x|) := by
          have := mul_le_mul_of_nonneg_right hc1 (by positivity : (0 : ℝ) ≤ u * (1 / 2 - |x|))
          linarith
        have e0 : u * (1 / 2 - |x|) - c * u * (1 / 2 - |x|) = (1 - c) * (u * (1 / 2 - |x|)) := by
          ring
        have hcu' : 0 ≤ (1 - c) * (u * (1 / 2 - |x|)) :=
          mul_nonneg (by linarith only [hc1]) (by positivity)
        rcases le_total |z.re| (1 / 2 + 2 * η) with h | h
        · rw [hy, max_eq_right h, sub_self, mul_zero]
          have h1 : 1 / 2 + η - |x| ≤ r := by linarith only [ha, habs]
          have h2 : u * (1 / 2 + η - |x|) ≤ u * r := mul_le_mul_of_nonneg_left h1 hu0.le
          have h3 : 0 ≤ E * r := mul_nonneg hE0.le hr0.le
          have e1 : (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|)
              = (u * r - u * (1 / 2 + η - |x|)) + 2 * (E * r)
                + (u * (1 / 2 - |x|) - c * u * (1 / 2 - |x|)) := by ring
          linarith only [h2, h3, e0, e1, hcu']
        · rw [hy, max_eq_left h]
          have h1 : |z.re| - (1 / 2 + 2 * η) ≤ r + |x| - 1 / 2 - 2 * η := by linarith only [habs]
          have h2 := mul_le_mul_of_nonneg_left h1 hu2E.le
          have hneg : |x| - 1 / 2 - 2 * η ≤ 0 := by linarith only [hx, hη]
          have h3 : 2 * E * (|x| - 1 / 2 - 2 * η) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
          have e1 : (u + 2 * E) * (r + |x| - 1 / 2 - 2 * η)
              = (u + 2 * E) * r + u * (|x| - 1 / 2 - 2 * η) + 2 * E * (|x| - 1 / 2 - 2 * η) := by
            ring
          have e2 : u * (|x| - 1 / 2 - 2 * η) = -(u * (1 / 2 - |x|)) - 2 * (η * u) := by ring
          have hηu : 0 ≤ η * u := by positivity
          linarith only [h2, h3, e0, e1, e2, hcu', hηu]
      calc C₂ * xiSliceReal t y
          ≤ C₂ * (S₀ * Real.exp ((u + 2 * E) * (y - (1 / 2 + 2 * η)))) :=
            mul_le_mul_of_nonneg_left hgrow hC₂.le
        _ ≤ (C₁ + C₂) * (S₀ * Real.exp ((u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|))) := by
            gcongr; linarith
        _ = M := by rw [hM]; ring
  have hcauchy := norm_iteratedDeriv_xiSliceProduct_le t N hr0 hMb
  have hfact : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [div_le_iff₀ hfact, ← hS₀]
  calc ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖ ≤ N.factorial * M / r ^ N := hcauchy
    _ = (C₁ + C₂) * S₀ * (Real.exp (N - η * u - c * u * (1 / 2 - |x|))
          * ((u + 2 * E) / N) ^ N) * N.factorial := by
        rw [hM, hrN, hrdef, div_pow, div_pow]
        field_simp

/-- **Weighted window bound at the saddle.**  For `3/4 ≤ κ ≤ 1`, `x ∈ [κ, κ + 1/100]`, `u = log t`
and `E = C_η`, `S(½+2η) e^{u(κ/2 − ½ − 2η − 1/15000) − 2(log 2 + 2E)} ≤ S(x) e^{−x²u/(2κ)}`. -/
theorem xiSliceReal_mul_gauss_ge_window_saddle {η κ t x : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 10)
    (hκ : 3 / 4 ≤ κ) (hκ1 : κ ≤ 1) (ht : 8 ≤ t) (hx1 : κ ≤ x) (hx2 : x ≤ κ + 1 / 100)
    (hxt : x ≤ t / 2) :
    xiSliceReal t (1 / 2 + 2 * η) * Real.exp (Real.log t * (κ / 2 - 1 / 2 - 2 * η - 1 / 15000)
        - 2 * (Real.log 2 + 2 * xiEulerConstant η))
      ≤ xiSliceReal t x * Real.exp (-(x ^ 2 * Real.log t / (2 * κ))) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  rw [← hudef, ← hEdef]
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  have hu0 : 0 ≤ u := by rw [hudef]; exact Real.log_nonneg (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ0 : 0 < κ := by linarith
  have hgrow := (xiSliceReal_growth_euler (t := t) (η := η) hη ht
    (y₁ := 1 / 2 + 2 * η) (y₂ := x) (by linarith) (by linarith) hxt).1
  rw [Real.log_div ht0.ne' (by norm_num), ← hudef, ← hEdef] at hgrow
  have hQ : κ / 2 - 1 / 2 - 2 * η - 1 / 15000 ≤ x - (1 / 2 + 2 * η) - x ^ 2 / (2 * κ) := by
    have e : x - x ^ 2 / (2 * κ) = κ / 2 - (x - κ) ^ 2 / (2 * κ) := by field_simp; ring
    have h1 : (x - κ) ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : (x - κ) ^ 2 / (2 * κ) ≤ 1 / 15000 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hexp : u * (κ / 2 - 1 / 2 - 2 * η - 1 / 15000) - 2 * (Real.log 2 + 2 * E)
      ≤ (u - Real.log 2 - 2 * E) * (x - (1 / 2 + 2 * η)) - x ^ 2 * u / (2 * κ) := by
    have h1 := mul_le_mul_of_nonneg_left hQ hu0
    have h2 : x - (1 / 2 + 2 * η) ≤ 2 := by linarith
    have h3 : 0 ≤ x - (1 / 2 + 2 * η) := by linarith
    have hc : 0 ≤ Real.log 2 + 2 * E := by linarith
    have h4 := mul_le_mul_of_nonneg_left h2 hc
    have e : x ^ 2 * u / (2 * κ) = u * (x ^ 2 / (2 * κ)) := by ring
    rw [e]
    nlinarith
  have hS := xiSliceReal_nonneg t (1 / 2 + 2 * η)
  calc xiSliceReal t (1 / 2 + 2 * η)
        * Real.exp (u * (κ / 2 - 1 / 2 - 2 * η - 1 / 15000) - 2 * (Real.log 2 + 2 * E))
      ≤ xiSliceReal t (1 / 2 + 2 * η) * Real.exp ((u - Real.log 2 - 2 * E) * (x - (1 / 2 + 2 * η))
          - x ^ 2 * u / (2 * κ)) := by gcongr
    _ = xiSliceReal t (1 / 2 + 2 * η)
          * Real.exp ((u - Real.log 2 - 2 * E) * (x - (1 / 2 + 2 * η)))
          * Real.exp (-(x ^ 2 * u / (2 * κ))) := by
        rw [mul_assoc (xiSliceReal t (1 / 2 + 2 * η)), ← Real.exp_add]; ring_nf
    _ ≤ xiSliceReal t x * Real.exp (-(x ^ 2 * u / (2 * κ))) := by gcongr

/-- **The window beats the inner region**, with a window exponent `a`, an inner exponent `b`,
`a + b > 0`, and window length factor `w`.  With `L′ = u − log 2 − 2E₈`, `1 ≤ N ≤ u` and
`u K < e^{(a+b)u}`:
`2C e^{N − bu} ((u + 2E)/N)ᴺ < w e^{au − 2(log 2 + 2E)} L′ᴺ/N! /(40π√(2u))`. -/
theorem heat_window_comparison_gen {a b w C E E₈ u : ℝ} (hw : 0 < w) (hC : 0 < C)
    (hE : 0 ≤ E) (hE₈ : 0 ≤ E₈) (hu : 0 < u) (hu2 : 2 * (Real.log 2 + 2 * E₈) ≤ u)
    (hK : u * (80 * Real.pi * Real.sqrt 2 * C
        * Real.exp (2 * (2 * E + Real.log 2 + 2 * E₈) + (2 * (Real.log 2 + 2 * E) + 1)) / w)
      < Real.exp ((a + b) * u))
    {N : ℕ} (hN1 : 1 ≤ N) (hNu : (N : ℝ) ≤ u) :
    2 * (C * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N)) <
      w * (Real.exp (u * a - 2 * (Real.log 2 + 2 * E))
        * ((u - Real.log 2 - 2 * E₈) ^ N / N.factorial
          * (1 / (40 * Real.pi * Real.sqrt (2 * u))))) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨L', hL'⟩ : ∃ L', L' = u - Real.log 2 - 2 * E₈ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Real.log 2 + 2 * E := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = 2 * E + Real.log 2 + 2 * E₈ := ⟨_, rfl⟩
  rw [← hL', ← hc]
  rw [← hc, ← hc'] at hK
  have hL'2 : u / 2 ≤ L' := by rw [hL']; linarith
  have hL'0 : 0 < L' := by linarith
  have hc'0 : 0 ≤ c' := by rw [hc']; linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpi := Real.pi_pos
  have hρ : (u + 2 * E) ^ N ≤ Real.exp (2 * c') * L' ^ N := by
    have hsum : u + 2 * E = L' * (1 + c' / L') := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hL'0.ne', hL', hc']; ring
    have h1 : (1 + c' / L') ^ N ≤ Real.exp (2 * c') := by
      calc (1 + c' / L') ^ N ≤ Real.exp (c' / L') ^ N :=
            pow_le_pow_left₀ (by have := div_nonneg hc'0 hL'0.le; linarith)
              (by linarith [Real.add_one_le_exp (c' / L')]) N
        _ = Real.exp (N * (c' / L')) := by rw [Real.exp_nat_mul]
        _ ≤ Real.exp (2 * c') := by
            refine Real.exp_le_exp.mpr ?_
            rw [← mul_div_assoc, div_le_iff₀ hL'0]
            have := mul_le_mul_of_nonneg_right (by linarith : (N : ℝ) ≤ 2 * L') hc'0
            linarith
    rw [hsum, mul_pow, mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_left h1 (pow_pos hL'0 N).le
  obtain ⟨W, hW⟩ : ∃ W, W = L' ^ N / ((N : ℝ) / Real.exp 1) ^ N := ⟨_, rfl⟩
  have hNe : 0 < ((N : ℝ) / Real.exp 1) ^ N := pow_pos (div_pos hN0 (Real.exp_pos 1)) N
  have hW0 : 0 < W := by rw [hW]; exact div_pos (pow_pos hL'0 N) hNe
  obtain ⟨eA, heA⟩ : ∃ eA, eA = Real.exp (b * u) := ⟨_, rfl⟩
  obtain ⟨eB, heB⟩ : ∃ eB, eB = Real.exp (u * a) := ⟨_, rfl⟩
  obtain ⟨e1, he1⟩ : ∃ e1, e1 = Real.exp (2 * c') := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e2, e2 = Real.exp (2 * c + 1) := ⟨_, rfl⟩
  have heA0 : 0 < eA := heA ▸ Real.exp_pos _
  have heB0 : 0 < eB := heB ▸ Real.exp_pos _
  have he10 : 0 < e1 := he1 ▸ Real.exp_pos _
  have he20 : 0 < e2 := he2 ▸ Real.exp_pos _
  have hX : Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N ≤ e1 * W / eA := by
    have e : Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N
        = (u + 2 * E) ^ N / ((N : ℝ) / Real.exp 1) ^ N / eA := by
      rw [heA, Real.exp_sub, div_pow, div_pow, ← Real.exp_nat_mul, mul_one]
      field_simp
    rw [e, hW, he1]
    apply div_le_div_of_nonneg_right _ heA0.le
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hNe]
    exact hρ
  have hfact := RHTower.factorial_le_exp_one_mul_sqrt_mul_pow hN1
  have hfact0 : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hsN : Real.sqrt N ≤ Real.sqrt u := Real.sqrt_le_sqrt hNu
  have hsN0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hs2u : Real.sqrt (2 * u) = Real.sqrt 2 * Real.sqrt u := Real.sqrt_mul (by norm_num) u
  have hsuu : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  have hY : Real.exp (u * a - 2 * c) = Real.exp 1 * (eB / e2) := by
    rw [heB, he2, ← Real.exp_sub, ← Real.exp_add]; ring_nf
  have hR : W / (40 * Real.pi * Real.sqrt 2 * Real.exp 1 * u)
      ≤ L' ^ N / N.factorial * (1 / (40 * Real.pi * Real.sqrt (2 * u))) := by
    have h1 : L' ^ N / (Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N)
        ≤ L' ^ N / N.factorial := div_le_div_of_nonneg_left (pow_pos hL'0 N).le hfact0 hfact
    have h2 : W / (40 * Real.pi * Real.sqrt 2 * Real.exp 1 * u)
        ≤ L' ^ N / (Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N)
          * (1 / (40 * Real.pi * Real.sqrt (2 * u))) := by
      have hden : Real.sqrt N * Real.sqrt u ≤ u :=
        le_of_le_of_eq (mul_le_mul_of_nonneg_right hsN (Real.sqrt_nonneg u)) hsuu
      rw [hW, hs2u, div_div, div_mul_div_comm, mul_one]
      apply div_le_div_of_nonneg_left (pow_pos hL'0 N).le
        (mul_pos (mul_pos (mul_pos (Real.exp_pos 1) hsN0) hNe)
          (mul_pos (by positivity) (mul_pos (Real.sqrt_pos.mpr (by norm_num))
            (Real.sqrt_pos.mpr hu))))
      calc Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N
            * (40 * Real.pi * (Real.sqrt 2 * Real.sqrt u))
          = 40 * Real.pi * Real.sqrt 2 * Real.exp 1 * (Real.sqrt N * Real.sqrt u)
            * ((N : ℝ) / Real.exp 1) ^ N := by ring
        _ ≤ 40 * Real.pi * Real.sqrt 2 * Real.exp 1 * u * ((N : ℝ) / Real.exp 1) ^ N := by
            gcongr
        _ = ((N : ℝ) / Real.exp 1) ^ N * (40 * Real.pi * Real.sqrt 2 * Real.exp 1 * u) := by ring
    exact le_trans h2 (mul_le_mul_of_nonneg_right h1 (by positivity))
  have hK' : u * (80 * Real.pi * Real.sqrt 2 * C * (e1 * e2) / w) < eA * eB := by
    have e : Real.exp (2 * c' + (2 * c + 1)) = e1 * e2 := by rw [he1, he2, Real.exp_add]
    rw [← e]
    calc _ < Real.exp ((a + b) * u) := hK
      _ = eA * eB := by rw [heA, heB, ← Real.exp_add]; ring_nf
  have hcore : 2 * C * e1 / eA < w * (eB / e2) / (40 * Real.pi * Real.sqrt 2 * u) := by
    have hd : 0 < 40 * Real.pi * Real.sqrt 2 * u :=
      mul_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr (by norm_num))) hu
    rw [div_lt_div_iff₀ heA0 hd]
    calc 2 * C * e1 * (40 * Real.pi * Real.sqrt 2 * u)
        = w / e2 * (u * (80 * Real.pi * Real.sqrt 2 * C * (e1 * e2) / w)) := by
          field_simp; ring
      _ < w / e2 * (eA * eB) := mul_lt_mul_of_pos_left hK' (div_pos hw he20)
      _ = w * (eB / e2) * eA := by ring
  rw [hY]
  calc 2 * (C * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N))
      ≤ 2 * (C * (e1 * W / eA)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hC.le) (by norm_num)
    _ = 2 * C * e1 / eA * W := by ring
    _ < w * (eB / e2) / (40 * Real.pi * Real.sqrt 2 * u) * W :=
        mul_lt_mul_of_pos_right hcore hW0
    _ = w * (Real.exp 1 * (eB / e2)) * (W / (40 * Real.pi * Real.sqrt 2 * Real.exp 1 * u)) := by
        field_simp
    _ ≤ w * (Real.exp 1 * (eB / e2)) * (L' ^ N / N.factorial
          * (1 / (40 * Real.pi * Real.sqrt (2 * u)))) :=
        mul_le_mul_of_nonneg_left hR
          (mul_pos hw (mul_pos (Real.exp_pos 1) (div_pos heB0 he20))).le
    _ = _ := by ring

/-- The inner exponent at heat `κ/log t`: `b = η + c/2 − c²κ/2`. -/
def subconvexInnerRate (η κ : ℝ) : ℝ :=
  η + subconvexGain η / 2 - subconvexGain η ^ 2 * κ / 2

/-- At `η = 1/1000` and `κ = 19/25` the window exponent `κ/2 − ½ − 2η − 1/15000` and the inner
exponent leave a positive gap. -/
theorem subconvex_gap_pos :
    0 < ((19 / 25 : ℝ) / 2 - 1 / 2 - 2 * (1 / 1000) - 1 / 15000)
      + subconvexInnerRate (1 / 1000) (19 / 25) := by
  unfold subconvexInnerRate subconvexGain; norm_num

/-- **Low orders at heat `κ/log t`.**  If `3/4 ≤ κ ≤ 1` and the gap
`κ/2 − ½ − 2η − 1/15000 + b(η, κ)` is positive at `η = 1/1000`, then for `1 ≤ m` and `2m ≤ log t`,
`T_{2m}(κ/log t, 0, t)` is positive once `t` is large. -/
theorem exists_xiSliceHeatTransfer_pos_low_order_saddle {κ : ℝ} (hκ : 3 / 4 ≤ κ) (hκ1 : κ ≤ 1)
    (hgap : 0 < (κ / 2 - 1 / 2 - 2 * (1 / 1000) - 1 / 15000)
      + subconvexInnerRate (1 / 1000) κ) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ, 1 ≤ m → (2 * m : ℝ) ≤ Real.log t →
      0 < DeBruijn.xiSliceHeatTransfer (κ / Real.log t) 0 t (2 * m) := by
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 1 / 1000 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; norm_num
  have hη1 : η ≤ 1 / 10 := by rw [hηdef]; norm_num
  obtain ⟨C, hC, hinner⟩ := exists_norm_iteratedDeriv_xiSliceProduct_le_inner_subconvex hη hη1
  obtain ⟨t₄, -, hM4⟩ := RHTower.exists_iteratedDeriv_xiSliceProduct_ge_euler_near_edge
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  obtain ⟨E₈, hE₈def⟩ : ∃ E₈, E₈ = xiEulerConstant (1 / 8) := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  have hE₈0 : 0 < E₈ := hE₈def ▸ xiEulerConstant_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ0 : 0 < κ := by linarith
  obtain ⟨c, hcdef⟩ : ∃ c, c = subconvexGain η := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hcdef ▸ subconvexGain_nonneg hη hη1
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = κ / 2 - 1 / 2 - 2 * η - 1 / 15000 := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = subconvexInnerRate η κ := ⟨_, rfl⟩
  have hbc : b = η + c / 2 - c ^ 2 * κ / 2 := by rw [hbdef, hcdef]; rfl
  have hgap : 0 < a + b := by rw [hadef, hbdef, hηdef]; exact hgap
  obtain ⟨K, hKdef⟩ : ∃ K, K = 80 * Real.pi * Real.sqrt 2 * C
      * Real.exp (2 * (2 * E + Real.log 2 + 2 * E₈) + (2 * (Real.log 2 + 2 * E) + 1)) / (1 / 100) :=
    ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (a + b)
    hgap)).2 (1 / K) (by positivity)
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp e5
  obtain ⟨L₀, hL₀⟩ : ∃ L₀, L₀ = max (max (Real.log 80) (Real.log t₄))
      (max (2 * (Real.log 2 + 2 * E₈)) (max U 1)) := ⟨_, rfl⟩
  refine ⟨max 80 (max t₄ (Real.exp L₀)), le_max_left _ _, ?_⟩
  intro t ht m hm1 hmu
  have ht80 : 80 ≤ t := le_trans (le_max_left _ _) ht
  have ht4 : t₄ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htL : Real.exp L₀ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : 0 < t := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  have hLu : L₀ ≤ u := by
    rw [hudef, ← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) htL
  rw [hL₀] at hLu
  have hu2 : 2 * (Real.log 2 + 2 * E₈) ≤ u :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLu
  have huU : U ≤ u :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hLu
  have hu1 : 1 ≤ u :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hLu
  have hu0 : 0 < u := by linarith
  have hKu : u * K < Real.exp ((a + b) * u) := by
    have h := hU u huU
    rw [Real.rpow_one, show -(a + b) * u = -((a + b) * u) by ring, Real.exp_neg] at h
    have hx := Real.exp_pos ((a + b) * u)
    rw [lt_div_iff₀ hK0] at h
    calc u * K = u * (Real.exp ((a + b) * u))⁻¹ * K * Real.exp ((a + b) * u) := by field_simp
      _ < 1 * Real.exp ((a + b) * u) := mul_lt_mul_of_pos_right h hx
      _ = Real.exp ((a + b) * u) := one_mul _
  -- the order and the heat
  obtain ⟨N, hNdef⟩ : ∃ N, N = 2 * m := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by omega
  have hNu : (N : ℝ) ≤ u := by rw [hNdef, hudef]; push_cast; exact hmu
  rw [← hudef]
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = κ / u := ⟨_, rfl⟩
  rw [← hlamdef, ← hNdef]
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt lam := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hlam0
  have hs2 : s ^ 2 = lam := by rw [hsdef]; exact Real.sq_sqrt hlam0.le
  -- the representation and its real part
  have hrep := DeBruijn.xiSliceHeatTransfer_eq_integral_iteratedDeriv hlam0.le t N
  have hint := DeBruijn.integrable_gauss_mul_iteratedDeriv_xiSliceProduct hlam0.le t N
  rw [← hsdef] at hrep hint
  set F : ℝ → ℂ := fun w => ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
    * (iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ) / N.factorial) with hF
  have hre : ∫ w, (F w).re = (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
      * DeBruijn.xiSliceHeatTransfer lam 0 t N).re := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [hrep]; exact this
  have hfact0 : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hFre : ∀ w, (F w).re = Real.exp (-(w ^ 2 / 2))
      * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial) := by
    intro w
    simp only [hF]
    rw [Complex.re_ofReal_mul, Complex.div_natCast_re]
  -- constants of the window argument
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = xiSliceReal t (1 / 2 + 2 * η) := ⟨_, rfl⟩
  have hS₀0 : 0 < S₀ := by rw [hS₀]; exact xiSliceReal_pos t (by linarith)
  have hlogt2 : Real.log (t / 2) = u - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num), hudef]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (u - Real.log 2 - 2 * E₈) ^ N / N.factorial
      * (1 / (40 * Real.pi * Real.sqrt (2 * u))) := ⟨_, rfl⟩
  have hL'0 : 0 < u - Real.log 2 - 2 * E₈ := by linarith
  have hQ0 : 0 ≤ Q := by
    rw [hQ]; exact mul_nonneg (div_nonneg (pow_pos hL'0 N).le hfact0.le) (by positivity)
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, P₀ = S₀ * Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = C * S₀ * (Real.exp (N - b * u)
      * ((u + 2 * E) / N) ^ N) := ⟨_, rfl⟩
  have hwin := DeBruijn.integral_ge_of_window (h := fun w => (F w).re) hint.re
    (a := κ / s) (b := (κ + 1 / 100) / s) (c := 1 / 2 / s) (P := P₀) (B := B₀)
    (div_le_div_of_nonneg_right (by linarith) hs0.le) (by positivity)
    (div_le_div_of_nonneg_right (by linarith) hs0.le) ?_ ?_ ?_
  rotate_left
  · -- the window
    intro w hw
    have hx1 : κ ≤ s * w := by
      have := hw.1; rw [div_le_iff₀ hs0] at this; linarith
    have hx2 : s * w ≤ κ + 1 / 100 := by
      have := hw.2; rw [le_div_iff₀ hs0] at this; linarith
    have hM := hM4 t ht4 (s * w) (by linarith) (by linarith) N hN1 (by rw [← hudef]; exact hNu)
    rw [← div_eq_inv_mul, Complex.div_natCast_re, hlogt2, ← hE₈def, ← hudef] at hM
    have hF' := xiSliceReal_mul_gauss_ge_window_saddle (t := t) hη hη1 hκ hκ1 (by linarith)
      hx1 hx2 (by linarith)
    rw [← hudef, ← hEdef, ← hS₀,
      show u * (κ / 2 - 1 / 2 - 2 * η - 1 / 15000) = u * a by rw [hadef]] at hF'
    have hg : Real.exp (-(w ^ 2 / 2)) = Real.exp (-((s * w) ^ 2 * u / (2 * κ))) := by
      congr 2
      rw [mul_pow, hs2, hlamdef]
      field_simp
    rw [hFre, hg, hP₀]
    calc S₀ * Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q
        ≤ xiSliceReal t (s * w) * Real.exp (-((s * w) ^ 2 * u / (2 * κ))) * Q :=
          mul_le_mul_of_nonneg_right hF' hQ0
      _ = Real.exp (-((s * w) ^ 2 * u / (2 * κ)))
          * (xiSliceReal t (s * w) * (u - Real.log 2 - 2 * E₈) ^ N / N.factorial
            * (1 / (40 * Real.pi * Real.sqrt (2 * u)))) := by rw [hQ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
  · -- the inner region
    intro w hw
    have hx : |s * w| < 1 / 2 := by
      rw [abs_mul, abs_of_pos hs0, ← lt_div_iff₀' hs0]
      exact abs_lt.mpr ⟨hw.1, hw.2⟩
    have hb := hinner t ht80 (s * w) hx N hN1 (by rw [← hudef]; exact hNu)
    rw [← hudef, ← hEdef, ← hS₀, ← hcdef] at hb
    rw [hFre]
    have hg0 := Real.exp_pos (-(w ^ 2 / 2))
    have hsq : -(w ^ 2 / 2) + (N - η * u - c * u * (1 / 2 - |s * w|)) ≤ N - b * u := by
      have hsw : |s * w| = s * |w| := by rw [abs_mul, abs_of_pos hs0]
      have hus : u ^ 2 * s ^ 2 = κ * u := by
        rw [hs2, hlamdef]; field_simp
      have h1 : 0 ≤ (|w| - c * u * s) ^ 2 := sq_nonneg _
      have h2 : |w| ^ 2 = w ^ 2 := sq_abs w
      have key : -(w ^ 2 / 2) + c * u * s * |w| ≤ c ^ 2 * κ * u / 2 := by
        nlinarith only [h1, h2, hus]
      rw [hsw, hbc]
      linarith only [key]
    have hre1 : |(iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re| / N.factorial
        ≤ C * S₀ * (Real.exp (N - η * u - c * u * (1 / 2 - |s * w|)) * ((u + 2 * E) / N) ^ N) :=
      le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hfact0.le) hb
    have habs : |Real.exp (-(w ^ 2 / 2))
        * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial)| ≤ B₀ := by
      rw [abs_mul, abs_of_pos hg0, abs_div, abs_of_pos hfact0]
      calc Real.exp (-(w ^ 2 / 2)) * (|(iteratedDeriv N (xiSliceProduct t)
            ((s * w : ℝ) : ℂ)).re| / N.factorial)
          ≤ Real.exp (-(w ^ 2 / 2)) * (C * S₀ * (Real.exp (N - η * u - c * u * (1 / 2 - |s * w|))
            * ((u + 2 * E) / N) ^ N)) := mul_le_mul_of_nonneg_left hre1 hg0.le
        _ = C * S₀ * (Real.exp (-(w ^ 2 / 2) + (N - η * u - c * u * (1 / 2 - |s * w|)))
            * ((u + 2 * E) / N) ^ N) := by rw [Real.exp_add]; ring
        _ ≤ B₀ := by
            rw [hB₀]
            have hX0 : 0 ≤ ((u + 2 * E) / N) ^ N := by positivity
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsq) hX0)
              (mul_nonneg hC.le hS₀0.le)
    linarith [neg_abs_le (Real.exp (-(w ^ 2 / 2))
      * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial))]
  · -- outside the inner region
    intro w hw
    have hx : 1 / 2 ≤ |s * w| := by
      rw [abs_mul, abs_of_pos hs0, ← div_le_iff₀' hs0]
      by_contra hcon
      push Not at hcon
      exact hw (abs_lt.mp hcon)
    rw [hFre]
    have h0 := DeBruijn.re_iteratedDeriv_xiSliceProduct_even_nonneg t m hx
    rw [← hNdef] at h0
    exact mul_nonneg (Real.exp_pos _).le (div_nonneg h0 hfact0.le)
  -- the comparison
  have hcmp := heat_window_comparison_gen (a := a) (b := b) (w := 1 / 100) (by norm_num) hC
    hE0.le hE₈0.le hu0 hu2 (by rw [← hKdef]; exact hKu) hN1 hNu
  have hpos : 0 < ((κ + 1 / 100) / s - κ / s) * P₀ - 2 * (1 / 2 / s) * B₀ := by
    have e : ((κ + 1 / 100) / s - κ / s) * P₀ - 2 * (1 / 2 / s) * B₀
        = (1 / 100 * P₀ - B₀) / s := by field_simp; ring
    rw [e]
    refine div_pos ?_ hs0
    rw [hP₀, hB₀]
    rw [← hQ] at hcmp
    have h := mul_lt_mul_of_pos_left hcmp hS₀0
    rw [sub_pos]
    calc C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N)
        < 2 * (C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N)) := by
          have : 0 < C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N) := by positivity
          linarith
      _ = S₀ * (2 * (C * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N))) := by ring
      _ < S₀ * (1 / 100 * (Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q)) := h
      _ = 1 / 100 * (S₀ * Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q) := by ring
  have hT := lt_of_lt_of_le hpos (le_of_le_of_eq hwin hre)
  rw [Complex.re_ofReal_mul] at hT
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hTre : 0 < (DeBruijn.xiSliceHeatTransfer lam 0 t N).re := pos_of_mul_pos_right hT hsq.le
  exact Complex.lt_def.mpr ⟨hTre, (DeBruijn.xiSliceHeatTransfer_im_eq_zero hlam0.le t N).symm⟩

namespace DeBruijn

/-- **Every even order at heat `(19/25)/log t`.** -/
theorem exists_xiSliceHeatTransfer_pos_at_heat_subconvex :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ,
      0 < xiSliceHeatTransfer ((19 / 25) / Real.log t) 0 t (2 * m) := by
  obtain ⟨t₁, ht₁, hlow⟩ := exists_xiSliceHeatTransfer_pos_low_order_saddle (by norm_num) (by norm_num) subconvex_gap_pos
  obtain ⟨K₁, hK₁⟩ := exists_xiSliceCoeff_pos_above_quarter_log (ε := 1 / 4) (by norm_num)
  refine ⟨max t₁ (Real.exp (2 * |K₁| + 2)), le_trans ht₁ (le_max_left _ _), fun t ht m => ?_⟩
  have ht1 : t₁ ≤ t := le_trans (le_max_left _ _) ht
  have htK : Real.exp (2 * |K₁| + 2) ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log t := ⟨_, rfl⟩
  have hℓK : 2 * |K₁| + 2 ≤ ℓ := by
    rw [hℓ, ← Real.log_exp (2 * |K₁| + 2)]; exact Real.log_le_log (Real.exp_pos _) htK
  have hℓ0 : 0 < ℓ := by linarith [abs_nonneg K₁]
  rw [← hℓ]
  have hlam0 : 0 < (19 / 25) / ℓ := by positivity
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    rw [mul_zero]
    exact xiSliceHeatTransfer_zero_order_pos hlam0 t
  by_cases hm : (2 * m : ℝ) ≤ ℓ
  · rw [hℓ] at hm ⊢
    exact hlow t ht1 m hm0 hm
  push Not at hm
  -- high orders: every slice coefficient involved is positive
  have hcoef : ∀ k : ℕ, m ≤ k → 0 < xiSliceCoeff t (2 * k) := by
    intro k hk
    have hk' : (m : ℝ) ≤ k := by exact_mod_cast hk
    refine hK₁ t ht0.le k (max_le ?_ ?_)
    · have : (K₁ : ℝ) ≤ |K₁| := le_abs_self K₁
      linarith
    · rw [← hℓ]; linarith
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam0.le 0 t (2 * m)
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  have hterm : ∀ k : ℕ, 0 ≤ ((((((19 / 25) / ℓ) / 2) ^ k / k.factorial *
      ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) *
        xiSliceCoeff t (2 * m + 2 * k)) := by
    intro k
    refine mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
    rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
    exact (hcoef (m + k) (by omega)).le
  have h0 := le_hasSum hT 0 fun j _ => hterm j
  have hfac : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero,
    div_self hfac, one_mul, Complex.ofReal_one] at h0
  exact lt_of_lt_of_le (hcoef m le_rfl) h0

/-- **Heat `(19/25)/log |t|` makes every heated slice coefficient positive.**  There is `t₀` such that
for `|t| ≥ t₀`, every heat `λ ≥ (19/25)/log |t|` and every `m`, `T_{2m}(λ, 0, t) > 0`. -/
theorem exists_xiSliceHeatTransfer_pos_heat_subconvex :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ |t| → ∀ lam : ℝ, (19 / 25) / Real.log |t| ≤ lam →
      ∀ m : ℕ, 0 < xiSliceHeatTransfer lam 0 t (2 * m) := by
  obtain ⟨t₀, ht₀, h⟩ := exists_xiSliceHeatTransfer_pos_at_heat_subconvex
  refine ⟨t₀, ht₀, fun t ht lam hlam m => ?_⟩
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  have key : 0 < xiSliceHeatTransfer lam 0 |t| (2 * m) := by
    have hshift := hasSum_xiSliceHeatTransfer_shift hlam 0 |t| (2 * m)
    have hterm : ∀ k : ℕ, 0 ≤ ((((lam - (19 / 25) / Real.log |t|) / 2) ^ k / k.factorial *
        ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) *
          xiSliceHeatTransfer ((19 / 25) / Real.log |t|) 0 |t| (2 * m + 2 * k) := by
      intro k
      have hd : 0 ≤ (lam - (19 / 25) / Real.log |t|) / 2 := by linarith
      refine mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
      rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
      exact (h |t| ht (m + k)).le
    have h0 := le_hasSum hshift 0 fun j _ => hterm j
    have hfac : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero,
      div_self hfac, one_mul, Complex.ofReal_one] at h0
    exact lt_of_lt_of_le (h |t| ht m) h0
  rcases le_total 0 t with htn | htn
  · rwa [abs_of_nonneg htn] at key
  · rw [abs_of_nonpos htn] at key
    rw [← neg_neg t, xiSliceHeatTransfer_neg_height hlam0]
    exact key

end DeBruijn

end

end RHTower
