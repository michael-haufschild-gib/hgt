import GaloisForLFunctions.RHTower.ZetaElevenEighteenthsProfiles

/-!
# Size-only repair reaches the Weyl floor `2/3`

Let `S(t, x) = ξ(½+x+it) ξ(½−x+it)` and let `T_n(λ, 0, t)` be the Taylor coefficients at `0` of the
heated slice.

**Theorem** (`DeBruijn.exists_xiSliceHeatTransfer_pos_heat_two_thirds_add`).  For every `ε > 0`
there
is `t₀` such that for `|t| ≥ t₀`, every heat `λ ≥ (2/3 + ε)/log |t|` and every `m`,
`T_{2m}(λ, 0, t) > 0`.  The instance `ε = 1/300` with fixed constants is
`DeBruijn.exists_xiSliceHeatTransfer_pos_heat_weylFloor` (rate `67/100`).

The interior-Lindelöf rate `17/25` (`exists_xiSliceHeatTransfer_pos_heat_interior`) uses the two
pieces `μ(½) ≤ 1/6`, `μ(5/7) ≤ 1/14` of the size profile.  Its first piece gives the slice the
relative profile `t^{−(1/9 + (1/9)(½ − |a|))}`, of slope `1/9`, and the gap
`κ/2 − ½ − 2η − 1/12000 + 1/9 + 1/18 − κ/162 > 0`, i.e. `κ > 27/40` as `η → 0`.  The signed Weyl
bump (`ASignedWeylBumpAttainsTheMethodFloor`) shows that this gap is sharp for those inputs.

Inserting `μ(11/18) ≤ 1/9` (`exists_norm_riemannZeta_le_profile_ee_one`, `_ee_two`) gives three
pieces
(`exists_norm_xiSliceProduct_le_three_profiles`):

* `|a| ≤ 1/9`: `ζ` exponent `1/6 + η − |a|/2`; slice profile `t^{−1/6}`, flat in `a`;
* `1/9 ≤ |a| ≤ 3/14`: `ζ` exponent `1/9 + η − (5/13)(|a| − 1/9)`; slice profile
  `t^{−(1/13 + (3/13)(½ − |a|))}`;
* `|a| ≥ 3/14`: the second interior profile `t^{−(η + c₂(½ + η − |a|))}`.

With window width `ω` (`xiSliceReal_mul_gauss_ge_window_width`) the flat piece has slope `0` and gap
`κ/2 − ⅓ − 2η − 5ω²/6 > 0`; the middle piece needs `(80/169)κ > 4/13 + 2η + 5ω²/6`; the third is the
corpus one.  At `η = 1/2000`, `ω = 1/100`, `κ = 67/100` all three gaps are positive
(`weylFloor_gap_pos_one`, `_two`, `_three`); at `κ = 2/3 + ε`, `η = ε/16`, `ω = min(1/100, ε)` they
are
positive for every `0 < ε ≤ 1/3` (`weylFloor_gaps_of_eps`).  So the size-only rate reaches
`2/3 = 4μ(½)`, the floor that the Weyl bump (`AWeylBumpBreaksSizeOnlyRepair`) shows no size-only
argument can beat.
-/

open Complex MeasureTheory Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The slice with three size profiles -/

theorem mul_le_sum_three {K S P K₁ K₂ K₃ P₁ P₂ P₃ : ℝ} (hS : 0 ≤ S) (hP : 0 ≤ P)
    (hK : 0 ≤ K) (hKs : K ≤ K₁ + K₂ + K₃) (hPs : P ≤ P₁ + P₂ + P₃) :
    K * S * P ≤ (K₁ + K₂ + K₃) * S * (P₁ + P₂ + P₃) :=
  mul_le_mul (mul_le_mul_of_nonneg_right hKs hS) hPs hP (mul_nonneg (hK.trans hKs) hS)

/-- **The slice inside the strip, three profiles.**  For `|a| < ½ + η`,
`|S(t, a + ic)| ≤ C S(t, ½+2η) (t^{−1/6} + t^{−(1/13 + (3/13)(½ − |a|))} + t^{−(η + c₂(½ + η −
|a|))})`. -/
theorem exists_norm_xiSliceProduct_le_three_profiles {η R₁ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 10)
    (hR₁ : 1 ≤ R₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ t a c : ℝ, 32 * R₁ + 16 ≤ t → |c| ≤ R₁ → |a| < 1 / 2 + η →
      ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
        ≤ C * xiSliceReal t (1 / 2 + 2 * η)
          * (t ^ (-(1 / 6 : ℝ)) + t ^ (-(1 / 13 + 3 / 13 * (1 / 2 - |a|)))
            + t ^ (-(η + interiorGain η * (1 / 2 + η - |a|)))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_riemannZeta_le_profile_ee_one hη (by linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_riemannZeta_le_profile_ee_two hη (by linarith)
  obtain ⟨C₃, hC₃, h₃⟩ := exists_norm_riemannZeta_le_profile_two hη (by linarith)
  obtain ⟨K₁, hK₁⟩ : ∃ K₁,
      K₁ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (C₁ * (1 + 1 / (2 * η))) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂,
      K₂ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (C₂ * (1 + 1 / (2 * η))) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨K₃, hK₃⟩ : ∃ K₃,
      K₃ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (C₃ * (1 + 1 / (2 * η))) ^ 2 :=
    ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hK₃0 : 0 ≤ K₃ := by rw [hK₃]; positivity
  refine ⟨K₁ + K₂ + K₃, by rw [hK₁, hK₂, hK₃]; positivity, fun t a c ht hc ha => ?_⟩
  have ht0 : 0 < t := by linarith
  have hS := xiSliceReal_nonneg t (1 / 2 + 2 * η)
  have hp1 : 0 ≤ t ^ (-(1 / 6 : ℝ)) := by positivity
  have hp2 : 0 ≤ t ^ (-(1 / 13 + 3 / 13 * (1 / 2 - |a|))) := by positivity
  have hp3 : 0 ≤ t ^ (-(η + interiorGain η * (1 / 2 + η - |a|))) := by positivity
  have hzt : ∀ c' : ℝ, |c'| ≤ R₁ → 8 ≤ t + c' ∧ t + c' ≤ 2 * t := by
    intro c' hc'
    have := abs_le.mp hc'
    constructor <;> linarith
  rcases le_or_gt |a| (1 / 9) with hsmall | hmid
  · -- flat piece, `e = 1/6 + η − |a|/2`
    have he0 : 0 ≤ 1 / 6 + η - |a| / 2 := by linarith
    have hb := norm_xiSliceProduct_le_of_zeta_exponent (Cz := C₁) (e := 1 / 6 + η - |a| / 2)
      (t := t) (a := a) (c := c) hη (by linarith) hR₁ (by linarith [abs_nonneg a]) ht hc
      (by linarith) (fun c' hc' => by
        obtain ⟨h8, h2t⟩ := hzt c' hc'
        refine (h₁ _ _ (by linarith [abs_nonneg a]) (by linarith) h8).trans ?_
        rw [show 1 / 6 + η - (1 / 2 + |a| - 1 / 2) / 2 = 1 / 6 + η - |a| / 2 by ring]
        gcongr)
    rw [← hK₁] at hb
    have hex : 2 * (1 / 6 + η - |a| / 2) - (1 / 2 + 2 * η - |a|) = -(1 / 6 : ℝ) := by ring
    rw [hex] at hb
    exact hb.trans (mul_le_sum_three hS hp1 hK₁0 (by linarith) (by linarith))
  rcases le_or_gt |a| (3 / 14) with hsmall' | hbig
  · -- middle piece, `e = 1/9 + η − (5/13)(|a| − 1/9)`
    have he0 : 0 ≤ 1 / 9 + η - 5 / 13 * (|a| - 1 / 9) := by linarith
    have hb := norm_xiSliceProduct_le_of_zeta_exponent (Cz := C₂)
      (e := 1 / 9 + η - 5 / 13 * (|a| - 1 / 9)) (t := t) (a := a) (c := c) hη (by linarith) hR₁
      (by linarith) ht hc (by linarith) (fun c' hc' => by
        obtain ⟨h8, h2t⟩ := hzt c' hc'
        refine (h₂ _ _ (by linarith) (by linarith) h8).trans ?_
        rw [show 1 / 9 + η - 5 / 13 * (1 / 2 + |a| - 11 / 18) = 1 / 9 + η - 5 / 13 * (|a| - 1 / 9)
          by ring]
        gcongr)
    rw [← hK₂] at hb
    have hex : 2 * (1 / 9 + η - 5 / 13 * (|a| - 1 / 9)) - (1 / 2 + 2 * η - |a|)
        = -(1 / 13 + 3 / 13 * (1 / 2 - |a|)) := by ring
    rw [hex] at hb
    exact hb.trans (mul_le_sum_three hS hp2 hK₂0 (by linarith) (by linarith))
  · -- outer piece, `e = (1/14 + η)(½ + η − |a|)/(2/7 + η)`
    have h27 : (0 : ℝ) < 2 / 7 + η := by linarith
    have he0 : 0 ≤ (1 / 14 + η) * (1 / 2 + η - |a|) / (2 / 7 + η) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) h27.le
    have he1 : 2 * ((1 / 14 + η) * (1 / 2 + η - |a|) / (2 / 7 + η)) ≤ 1 := by
      rw [mul_div_assoc', div_le_one h27]
      nlinarith
    have hb := norm_xiSliceProduct_le_of_zeta_exponent (Cz := C₃)
      (e := (1 / 14 + η) * (1 / 2 + η - |a|) / (2 / 7 + η)) (t := t) (a := a) (c := c) hη
      (by linarith) hR₁ he1 ht hc
      (by linarith) (fun c' hc' => by
        obtain ⟨h8, h2t⟩ := hzt c' hc'
        refine (h₃ _ _ (by linarith) (by linarith) h8).trans ?_
        rw [show 1 + η - (1 / 2 + |a|) = 1 / 2 + η - |a| by ring]
        gcongr)
    rw [← hK₃] at hb
    have hex : 2 * ((1 / 14 + η) * (1 / 2 + η - |a|) / (2 / 7 + η)) - (1 / 2 + 2 * η - |a|)
        = -(η + interiorGain η * (1 / 2 + η - |a|)) := by
      unfold interiorGain; field_simp; ring
    rw [hex] at hb
    exact hb.trans (mul_le_sum_three hS hp3 hK₃0 (by linarith) (by linarith))

/-- **Inner Cauchy bound, three profiles.**  For `|x| < ½` and `1 ≤ N ≤ log t`, with
`c₂ = interiorGain η` and `E = C_η`, `|S^{(N)}(x)|/N!` is at most
`C S(½+2η) (e^{N − u/6} + e^{N − u/13 − (3u/13)(½−|x|)} + e^{N − ηu − c₂u(½−|x|)}) ((u + 2E)/N)ᴺ`,
`u = log t`. -/
theorem exists_norm_iteratedDeriv_xiSliceProduct_le_inner_three_profiles {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 10) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 80 ≤ t → ∀ x : ℝ, |x| < 1 / 2 → ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ≤ Real.log t →
      ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖ / N.factorial ≤
        C * xiSliceReal t (1 / 2 + 2 * η)
          * ((Real.exp (N - Real.log t / 6)
            + Real.exp (N - Real.log t / 13 - 3 / 13 * Real.log t * (1 / 2 - |x|))
            + Real.exp (N - η * Real.log t - interiorGain η * Real.log t * (1 / 2 - |x|)))
          * ((Real.log t + 2 * xiEulerConstant η) / N) ^ N) := by
  obtain ⟨C₁, hC₁, hS₁⟩ := exists_norm_xiSliceProduct_le_three_profiles (R₁ := 2) hη hη1
    (by norm_num)
  obtain ⟨C₂, hC₂, hS₂⟩ := exists_norm_xiSliceProduct_le_strip (R₁ := 2) hη (by linarith)
    (by norm_num)
  have hc0 := interiorGain_nonneg hη hη1
  have hc1 := interiorGain_le_one hη
  refine ⟨C₁ + C₂, by linarith, fun t ht x hx N hN1 hNu => ?_⟩
  have ht0 : 0 < t := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = interiorGain η := ⟨_, rfl⟩
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
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = (u + 2 * E) * r - u / 6 := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, A₂ = (u + 2 * E) * r - u / 13 - 3 / 13 * u * (1 / 2 - |x|) := ⟨_, rfl⟩
  obtain ⟨A₃, hA₃⟩ : ∃ A₃, A₃ = (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (C₁ + C₂) * S₀ * (Real.exp A₁ + Real.exp A₂ + Real.exp A₃) :=
    ⟨_, rfl⟩
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
    have hE1 : 0 ≤ Real.exp A₁ := (Real.exp_pos _).le
    have hE2 : 0 ≤ Real.exp A₂ := (Real.exp_pos _).le
    have hE3 : 0 ≤ Real.exp A₃ := (Real.exp_pos _).le
    rw [hz']
    by_cases ha : |z.re| < 1 / 2 + η
    · have h := hS₁ t z.re z.im (by linarith) (by linarith) ha
      rw [← hS₀, ← hcdef] at h
      refine h.trans ?_
      rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0, ← hudef, hM]
      have hur : 0 ≤ (u + 2 * E) * r := by positivity
      have hexp1 : u * -(1 / 6 : ℝ) ≤ A₁ := by rw [hA₁]; linarith
      have hexp2 : u * -(1 / 13 + 3 / 13 * (1 / 2 - |z.re|)) ≤ A₂ := by
        rw [hA₂]
        have h2 : |z.re| - |x| ≤ r := by linarith only [habs]
        have h3 : 3 / 13 * u * (|z.re| - |x|) ≤ 3 / 13 * u * r :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have h4 : 3 / 13 * u * r ≤ u * r := by nlinarith [hr0]
        have h5 : 0 ≤ 2 * E * r := by positivity
        nlinarith only [h3, h4, h5]
      have hexp3 : u * -(η + c * (1 / 2 + η - |z.re|)) ≤ A₃ := by
        rw [hA₃]
        have h2 : |z.re| - |x| - η ≤ r := by linarith only [habs, hη]
        have h3 : c * u * (|z.re| - |x| - η) ≤ c * u * r :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have h4 : c * (u * r) ≤ 1 * (u * r) :=
          mul_le_mul_of_nonneg_right hc1 (by positivity)
        have h5 : 0 ≤ 2 * E * r := by positivity
        have e1 : c * u * r = c * (u * r) := by ring
        have e2 : (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|)
            - u * -(η + c * (1 / 2 + η - |z.re|))
            = (u + 2 * E) * r - c * u * (|z.re| - |x| - η) := by ring
        have e3 : (u + 2 * E) * r = 1 * (u * r) + 2 * E * r := by ring
        linarith only [h3, h4, h5, e1, e2, e3]
      have hCC : C₁ * S₀ ≤ (C₁ + C₂) * S₀ := mul_le_mul_of_nonneg_right (by linarith) hS₀0
      exact mul_le_mul hCC (add_le_add (add_le_add (Real.exp_le_exp.mpr hexp1)
          (Real.exp_le_exp.mpr hexp2)) (Real.exp_le_exp.mpr hexp3))
        (by positivity) (mul_nonneg (by linarith) hS₀0)
    · push Not at ha
      obtain ⟨-, hout⟩ := hS₂ t z.re z.im (by linarith) (by linarith)
      refine le_trans (hout ha (by linarith)) ?_
      set y := max |z.re| (1 / 2 + 2 * η) with hy
      have hy1 : 1 / 2 + 2 * η ≤ y := le_max_right _ _
      have hy2 : y ≤ t / 2 := max_le (by linarith) (by linarith)
      have hgrow := (xiSliceReal_growth_euler (t := t) hη (by linarith) (y₁ := 1 / 2 + 2 * η)
        (y₂ := y) (by linarith) hy1 hy2).2
      rw [← hudef, ← hEdef, ← hS₀] at hgrow
      have hexp : (u + 2 * E) * (y - (1 / 2 + 2 * η)) ≤ A₃ := by
        rw [hA₃]
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
        _ ≤ (C₁ + C₂) * (S₀ * Real.exp A₃) := by
            gcongr; linarith
        _ ≤ (C₁ + C₂) * (S₀ * (Real.exp A₁ + Real.exp A₂ + Real.exp A₃)) := by
            gcongr; linarith [Real.exp_pos A₁, Real.exp_pos A₂]
        _ = M := by rw [hM]; ring
  have hcauchy := norm_iteratedDeriv_xiSliceProduct_le t N hr0 hMb
  have hfact : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [div_le_iff₀ hfact, ← hS₀]
  have hA₁' : A₁ = N - u / 6 := by rw [hA₁, hrN]
  have hA₂' : A₂ = N - u / 13 - 3 / 13 * u * (1 / 2 - |x|) := by rw [hA₂, hrN]
  have hA₃' : A₃ = N - η * u - c * u * (1 / 2 - |x|) := by rw [hA₃, hrN]
  calc ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖ ≤ N.factorial * M / r ^ N := hcauchy
    _ = (C₁ + C₂) * S₀ * ((Real.exp (N - u / 6)
          + Real.exp (N - u / 13 - 3 / 13 * u * (1 / 2 - |x|))
          + Real.exp (N - η * u - c * u * (1 / 2 - |x|))) * ((u + 2 * E) / N) ^ N)
          * N.factorial := by
        rw [hM, ← hA₁', ← hA₂', ← hA₃', hrdef, div_pow, div_pow]
        field_simp

/-! ## The gaps and the low orders -/

/-- The inner exponent of the middle profile, `b₂ = 1/13 + 3/26 − (3/13)²κ/2`. -/
def weylFloorRateTwo (κ : ℝ) : ℝ := 1 / 13 + 3 / 26 - (3 / 13) ^ 2 * κ / 2

/-- **Weighted window bound of width `ω`** for `max(½ + 2η, 3/5) ≤ κ ≤ 1`, `x ∈ [κ, κ + ω]`,
`ω ≤ 1`:
`S(½+2η) e^{u(κ/2 − ½ − 2η − 5ω²/6) − 2(log 2 + 2E)} ≤ S(x) e^{−x²u/(2κ)}`. -/
theorem xiSliceReal_mul_gauss_ge_window_width {η κ ω t x : ℝ} (hη : 0 < η)
    (hκη : 1 / 2 + 2 * η ≤ κ) (hκ6 : 3 / 5 ≤ κ) (hκ1 : κ ≤ 1) (hω1 : ω ≤ 1)
    (ht : 8 ≤ t) (hx1 : κ ≤ x) (hx2 : x ≤ κ + ω) (hxt : x ≤ t / 2) :
    xiSliceReal t (1 / 2 + 2 * η) * Real.exp (Real.log t * (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2)
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
  have hQ : κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2 ≤ x - (1 / 2 + 2 * η) - x ^ 2 / (2 * κ) := by
    have e : x - x ^ 2 / (2 * κ) = κ / 2 - (x - κ) ^ 2 / (2 * κ) := by field_simp; ring
    have h1 : (x - κ) ^ 2 ≤ ω ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : (x - κ) ^ 2 / (2 * κ) ≤ 5 / 6 * ω ^ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [sq_nonneg ω]
    linarith
  have hexp : u * (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) - 2 * (Real.log 2 + 2 * E)
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
        * Real.exp (u * (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) - 2 * (Real.log 2 + 2 * E))
      ≤ xiSliceReal t (1 / 2 + 2 * η) * Real.exp ((u - Real.log 2 - 2 * E) * (x - (1 / 2 + 2 * η))
          - x ^ 2 * u / (2 * κ)) := by gcongr
    _ = xiSliceReal t (1 / 2 + 2 * η)
          * Real.exp ((u - Real.log 2 - 2 * E) * (x - (1 / 2 + 2 * η)))
          * Real.exp (-(x ^ 2 * u / (2 * κ))) := by
        rw [mul_assoc (xiSliceReal t (1 / 2 + 2 * η)), ← Real.exp_add]; ring_nf
    _ ≤ xiSliceReal t x * Real.exp (-(x ^ 2 * u / (2 * κ))) := by gcongr

theorem weylFloor_gap_pos_one :
    0 < ((67 / 100 : ℝ) / 2 - 1 / 2 - 2 * (1 / 2000) - 5 / 6 * (1 / 100) ^ 2) + 1 / 6 := by norm_num

theorem weylFloor_gap_pos_two :
    0 < ((67 / 100 : ℝ) / 2 - 1 / 2 - 2 * (1 / 2000) - 5 / 6 * (1 / 100) ^ 2)
      + weylFloorRateTwo (67 / 100) := by
  unfold weylFloorRateTwo; norm_num

theorem weylFloor_gap_pos_three :
    0 < ((67 / 100 : ℝ) / 2 - 1 / 2 - 2 * (1 / 2000) - 5 / 6 * (1 / 100) ^ 2)
      + interiorRateTwo (1 / 2000) (67 / 100) := by
  unfold interiorRateTwo interiorGain; norm_num

/-- **Low orders at heat `κ/log t` with three size profiles.**  If `2/3 ≤ κ ≤ 1`, `0 < η ≤ 1/12`,
`0 < ω ≤ 1/100` and the three gaps `κ/2 − ½ − 2η − 5ω²/6 + bᵢ` are positive, then for `1 ≤ m` and
`2m ≤ log t`, `T_{2m}(κ/log t, 0, t)` is positive once `t` is large. -/
theorem exists_xiSliceHeatTransfer_pos_low_order_weylFloor {κ η ω : ℝ} (hκ : 2 / 3 ≤ κ)
    (hκ1 : κ ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1 / 12) (hω : 0 < ω) (hω1 : ω ≤ 1 / 100)
    (hgap₁ : 0 < (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) + 1 / 6)
    (hgap₂ : 0 < (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) + weylFloorRateTwo κ)
    (hgap₃ : 0 < (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) + interiorRateTwo η κ) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ, 1 ≤ m → (2 * m : ℝ) ≤ Real.log t →
      0 < DeBruijn.xiSliceHeatTransfer (κ / Real.log t) 0 t (2 * m) := by
  obtain ⟨C, hC, hinner⟩ := exists_norm_iteratedDeriv_xiSliceProduct_le_inner_three_profiles hη
    (by linarith)
  obtain ⟨t₄, -, hM4⟩ := exists_iteratedDeriv_xiSliceProduct_ge_euler_from (η := 1 / 12)
    (by norm_num) (by norm_num)
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  obtain ⟨E₈, hE₈def⟩ : ∃ E₈, E₈ = xiEulerConstant (1 / 12) := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  have hE₈0 : 0 < E₈ := hE₈def ▸ xiEulerConstant_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ0 : 0 < κ := by linarith
  obtain ⟨c, hcdef⟩ : ∃ c, c = interiorGain η := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = min (min (1 / 6) (weylFloorRateTwo κ)) (interiorRateTwo η κ) :=
    ⟨_, rfl⟩
  have hb₁ : b ≤ 1 / 6 := by rw [hbdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hb₂ : b ≤ 1 / 13 + 3 / 26 - (3 / 13) ^ 2 * κ / 2 := by
    rw [hbdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hb₃ : b ≤ η + c / 2 - c ^ 2 * κ / 2 := by
    rw [hbdef, hcdef]; exact min_le_right _ _
  have hgap : 0 < a + b := by
    rw [hadef, hbdef]
    rcases min_choice (min (1 / 6) (weylFloorRateTwo κ)) (interiorRateTwo η κ) with h | h <;>
      rw [h]
    · rcases min_choice (1 / 6 : ℝ) (weylFloorRateTwo κ) with h' | h' <;> rw [h']
      · exact hgap₁
      · exact hgap₂
    · exact hgap₃
  obtain ⟨K, hKdef⟩ : ∃ K, K = 80 * Real.pi * Real.sqrt 2 * (3 * C)
      * Real.exp (2 * (2 * E + Real.log 2 + 2 * E₈) + (2 * (Real.log 2 + 2 * E) + 1)) / ω :=
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
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = 3 * C * S₀ * (Real.exp (N - b * u)
      * ((u + 2 * E) / N) ^ N) := ⟨_, rfl⟩
  have hwin := DeBruijn.integral_ge_of_window (h := fun w => (F w).re) hint.re
    (a := κ / s) (b := (κ + ω) / s) (c := 1 / 2 / s) (P := P₀) (B := B₀)
    (div_le_div_of_nonneg_right (by linarith) hs0.le) (by positivity)
    (div_le_div_of_nonneg_right (by linarith) hs0.le) ?_ ?_ ?_
  rotate_left
  · -- the window
    intro w hw
    have hx1 : κ ≤ s * w := by
      have := hw.1; rw [div_le_iff₀ hs0] at this; linarith
    have hx2 : s * w ≤ κ + ω := by
      have := hw.2; rw [le_div_iff₀ hs0] at this; linarith
    have hM := hM4 t ht4 (s * w) (by linarith) (by linarith) N hN1 (by rw [← hudef]; exact hNu)
    rw [← div_eq_inv_mul, Complex.div_natCast_re, hlogt2, ← hE₈def, ← hudef] at hM
    have hF' := xiSliceReal_mul_gauss_ge_window_width (t := t) hη (by linarith) (by linarith)
      hκ1 (by linarith) (by linarith) hx1 hx2 (by linarith)
    rw [← hudef, ← hEdef, ← hS₀,
      show u * (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) = u * a by rw [hadef]] at hF'
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
    have hsw : |s * w| = s * |w| := by rw [abs_mul, abs_of_pos hs0]
    have hus : u ^ 2 * s ^ 2 = κ * u := by
      rw [hs2, hlamdef]; field_simp
    have h2 : |w| ^ 2 = w ^ 2 := sq_abs w
    have hsq₁ : -(w ^ 2 / 2) + (N - u / 6) ≤ N - b * u := by
      have hbu : b * u ≤ 1 / 6 * u := mul_le_mul_of_nonneg_right hb₁ hu0.le
      have : 0 ≤ w ^ 2 / 2 := by positivity
      linarith only [hbu, this]
    have hsq₂ : -(w ^ 2 / 2) + (N - u / 13 - 3 / 13 * u * (1 / 2 - |s * w|)) ≤ N - b * u := by
      have h1 : 0 ≤ (|w| - 3 / 13 * u * s) ^ 2 := sq_nonneg _
      have key : -(w ^ 2 / 2) + 3 / 13 * u * s * |w| ≤ (3 / 13) ^ 2 * κ * u / 2 := by
        nlinarith only [h1, h2, hus]
      have hbu : b * u ≤ (1 / 13 + 3 / 26 - (3 / 13) ^ 2 * κ / 2) * u :=
        mul_le_mul_of_nonneg_right hb₂ hu0.le
      rw [hsw]
      linarith only [key, hbu]
    have hsq₃ : -(w ^ 2 / 2) + (N - η * u - c * u * (1 / 2 - |s * w|)) ≤ N - b * u := by
      have h1 : 0 ≤ (|w| - c * u * s) ^ 2 := sq_nonneg _
      have key : -(w ^ 2 / 2) + c * u * s * |w| ≤ c ^ 2 * κ * u / 2 := by
        nlinarith only [h1, h2, hus]
      have hbu : b * u ≤ (η + c / 2 - c ^ 2 * κ / 2) * u :=
        mul_le_mul_of_nonneg_right hb₃ hu0.le
      rw [hsw]
      linarith only [key, hbu]
    have hre1 : |(iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re| / N.factorial
        ≤ C * S₀ * ((Real.exp (N - u / 6)
          + Real.exp (N - u / 13 - 3 / 13 * u * (1 / 2 - |s * w|))
          + Real.exp (N - η * u - c * u * (1 / 2 - |s * w|))) * ((u + 2 * E) / N) ^ N) :=
      le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hfact0.le) hb
    have hX0 : 0 ≤ ((u + 2 * E) / N) ^ N := by positivity
    have habs : |Real.exp (-(w ^ 2 / 2))
        * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial)| ≤ B₀ := by
      rw [abs_mul, abs_of_pos hg0, abs_div, abs_of_pos hfact0]
      calc Real.exp (-(w ^ 2 / 2)) * (|(iteratedDeriv N (xiSliceProduct t)
            ((s * w : ℝ) : ℂ)).re| / N.factorial)
          ≤ Real.exp (-(w ^ 2 / 2)) * (C * S₀ * ((Real.exp (N - u / 6)
            + Real.exp (N - u / 13 - 3 / 13 * u * (1 / 2 - |s * w|))
            + Real.exp (N - η * u - c * u * (1 / 2 - |s * w|))) * ((u + 2 * E) / N) ^ N)) :=
            mul_le_mul_of_nonneg_left hre1 hg0.le
        _ = C * S₀ * ((Real.exp (-(w ^ 2 / 2) + (N - u / 6))
            + Real.exp (-(w ^ 2 / 2) + (N - u / 13 - 3 / 13 * u * (1 / 2 - |s * w|)))
            + Real.exp (-(w ^ 2 / 2) + (N - η * u - c * u * (1 / 2 - |s * w|))))
            * ((u + 2 * E) / N) ^ N) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
        _ ≤ C * S₀ * ((Real.exp (N - b * u) + Real.exp (N - b * u) + Real.exp (N - b * u))
            * ((u + 2 * E) / N) ^ N) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (add_le_add (add_le_add (Real.exp_le_exp.mpr hsq₁) (Real.exp_le_exp.mpr hsq₂))
                (Real.exp_le_exp.mpr hsq₃)) hX0)
              (mul_nonneg hC.le hS₀0.le)
        _ = B₀ := by rw [hB₀]; ring
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
  have hcmp := heat_window_comparison_gen (a := a) (b := b) (w := ω) (C := 3 * C)
    hω (by linarith) hE0.le hE₈0.le hu0 hu2 (by rw [← hKdef]; exact hKu) hN1 hNu
  have hpos : 0 < ((κ + ω) / s - κ / s) * P₀ - 2 * (1 / 2 / s) * B₀ := by
    have e : ((κ + ω) / s - κ / s) * P₀ - 2 * (1 / 2 / s) * B₀
        = (ω * P₀ - B₀) / s := by field_simp; ring
    rw [e]
    refine div_pos ?_ hs0
    rw [hP₀, hB₀]
    rw [← hQ] at hcmp
    have h := mul_lt_mul_of_pos_left hcmp hS₀0
    rw [sub_pos]
    calc 3 * C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N)
        < 2 * (3 * C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N)) := by
          have : 0 < 3 * C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N) := by positivity
          linarith
      _ = S₀ * (2 * (3 * C * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N))) := by ring
      _ < S₀ * (ω * (Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q)) := h
      _ = ω * (S₀ * Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q) := by ring
  have hT := lt_of_lt_of_le hpos (le_of_le_of_eq hwin hre)
  rw [Complex.re_ofReal_mul] at hT
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hTre : 0 < (DeBruijn.xiSliceHeatTransfer lam 0 t N).re := pos_of_mul_pos_right hT hsq.le
  exact Complex.lt_def.mpr ⟨hTre, (DeBruijn.xiSliceHeatTransfer_im_eq_zero hlam0.le t N).symm⟩

/-! ## The gaps at `2/3 + ε` -/

theorem sq_min_hundredth_le {ε : ℝ} (hε : 0 < ε) :
    5 / 6 * min (1 / 100) ε ^ 2 ≤ ε / 120 := by
  have h1 : min (1 / 100) ε ≤ 1 / 100 := min_le_left _ _
  have h2 : min (1 / 100) ε ≤ ε := min_le_right _ _
  have h0 : 0 ≤ min (1 / 100) ε := le_min (by norm_num) hε.le
  nlinarith

/-- The three gaps at `κ = 2/3 + ε`, `η = ε/16`, `ω = min(1/100, ε)`, `0 < ε ≤ 1/3`. -/
theorem weylFloor_gaps_of_eps {ε : ℝ} (hε : 0 < ε) (hε3 : ε ≤ 1 / 3) :
    0 < ((2 / 3 + ε) / 2 - 1 / 2 - 2 * (ε / 16) - 5 / 6 * min (1 / 100) ε ^ 2) + 1 / 6 ∧
    0 < ((2 / 3 + ε) / 2 - 1 / 2 - 2 * (ε / 16) - 5 / 6 * min (1 / 100) ε ^ 2)
      + weylFloorRateTwo (2 / 3 + ε) ∧
    0 < ((2 / 3 + ε) / 2 - 1 / 2 - 2 * (ε / 16) - 5 / 6 * min (1 / 100) ε ^ 2)
      + interiorRateTwo (ε / 16) (2 / 3 + ε) := by
  have hω := sq_min_hundredth_le hε
  refine ⟨by linarith, by unfold weylFloorRateTwo; linarith, ?_⟩
  have hd : 0 < 2 / 7 + ε / 16 := by positivity
  have hc : interiorGain (ε / 16) = (1 / 7 - ε / 16) / (2 / 7 + ε / 16) := by
    unfold interiorGain; field_simp; ring
  have hG : (2 / 3 + ε) / 2 - 1 / 2 - 2 * (ε / 16) + interiorRateTwo (ε / 16) (2 / 3 + ε) - ε / 8
      = (51 / 2352 * ε + 29 / 896 * ε ^ 2 - 3 / 2048 * ε ^ 3) / (2 * (2 / 7 + ε / 16) ^ 2) := by
    unfold interiorRateTwo; rw [hc]; field_simp; ring
  have hP : 0 < 51 / 2352 * ε + 29 / 896 * ε ^ 2 - 3 / 2048 * ε ^ 3 := by
    have h1 : ε ^ 3 ≤ ε / 9 := by nlinarith [mul_pos hε hε]
    nlinarith [mul_pos hε hε]
  have hq : 0 < (51 / 2352 * ε + 29 / 896 * ε ^ 2 - 3 / 2048 * ε ^ 3)
      / (2 * (2 / 7 + ε / 16) ^ 2) :=
    div_pos hP (by positivity)
  linarith

namespace DeBruijn

/-- **From the low orders to every even order.**  Orders above `log t` are positive by the
quarter-log coefficient theorem, and order `0` by positivity of the slice. -/
theorem exists_xiSliceHeatTransfer_pos_at_heat_of_low_order {κ : ℝ} (hκ : 0 < κ)
    (hlow : ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ, 1 ≤ m → (2 * m : ℝ) ≤ Real.log t →
      0 < xiSliceHeatTransfer (κ / Real.log t) 0 t (2 * m)) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ,
      0 < xiSliceHeatTransfer (κ / Real.log t) 0 t (2 * m) := by
  obtain ⟨t₁, ht₁, hlow⟩ := hlow
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
  have hlam0 : 0 < κ / ℓ := by positivity
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    rw [mul_zero]
    exact xiSliceHeatTransfer_zero_order_pos hlam0 t
  by_cases hm : (2 * m : ℝ) ≤ ℓ
  · rw [hℓ] at hm ⊢
    exact hlow t ht1 m hm0 hm
  push Not at hm
  have hcoef : ∀ k : ℕ, m ≤ k → 0 < xiSliceCoeff t (2 * k) := by
    intro k hk
    have hk' : (m : ℝ) ≤ k := by exact_mod_cast hk
    refine hK₁ t ht0.le k (max_le ?_ ?_)
    · have : (K₁ : ℝ) ≤ |K₁| := le_abs_self K₁
      linarith
    · rw [← hℓ]; linarith
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam0.le 0 t (2 * m)
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  have hterm : ∀ k : ℕ, 0 ≤ (((((κ / ℓ) / 2) ^ k / k.factorial *
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

/-- **From heat `κ/log t` at `t ≥ t₀` to every heat `λ ≥ κ/log |t|`**: positivity is closed upward
in the heat and symmetric in the height. -/
theorem exists_xiSliceHeatTransfer_pos_heat_of_at_heat {κ : ℝ} (hκ : 0 < κ)
    (h : ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ,
      0 < xiSliceHeatTransfer (κ / Real.log t) 0 t (2 * m)) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ |t| → ∀ lam : ℝ, κ / Real.log |t| ≤ lam →
      ∀ m : ℕ, 0 < xiSliceHeatTransfer lam 0 t (2 * m) := by
  obtain ⟨t₀, ht₀, h⟩ := h
  refine ⟨t₀, ht₀, fun t ht lam hlam m => ?_⟩
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  have key : 0 < xiSliceHeatTransfer lam 0 |t| (2 * m) := by
    have hshift := hasSum_xiSliceHeatTransfer_shift hlam 0 |t| (2 * m)
    have hterm : ∀ k : ℕ, 0 ≤ ((((lam - κ / Real.log |t|) / 2) ^ k / k.factorial *
        ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) *
          xiSliceHeatTransfer (κ / Real.log |t|) 0 |t| (2 * m + 2 * k) := by
      intro k
      have hd : 0 ≤ (lam - κ / Real.log |t|) / 2 := by linarith
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

/-- **Heat `(67/100)/log |t|` makes every heated slice coefficient positive.**  There is `t₀` such
that for `|t| ≥ t₀`, every heat `λ ≥ (67/100)/log |t|` and every `m`, `T_{2m}(λ, 0, t) > 0`. -/
theorem exists_xiSliceHeatTransfer_pos_heat_weylFloor :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ |t| → ∀ lam : ℝ, (67 / 100) / Real.log |t| ≤ lam →
      ∀ m : ℕ, 0 < xiSliceHeatTransfer lam 0 t (2 * m) :=
  exists_xiSliceHeatTransfer_pos_heat_of_at_heat (by norm_num)
    (exists_xiSliceHeatTransfer_pos_at_heat_of_low_order (by norm_num)
      (exists_xiSliceHeatTransfer_pos_low_order_weylFloor (η := 1 / 2000) (ω := 1 / 100)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
        weylFloor_gap_pos_one weylFloor_gap_pos_two weylFloor_gap_pos_three))

/-- **Size-only repair reaches the Weyl floor.**  For every `ε > 0` there is `t₀` such that for
`|t| ≥ t₀`, every heat `λ ≥ (2/3 + ε)/log |t|` and every `m`, `T_{2m}(λ, 0, t) > 0`. -/
theorem exists_xiSliceHeatTransfer_pos_heat_two_thirds_add {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ |t| → ∀ lam : ℝ, (2 / 3 + ε) / Real.log |t| ≤ lam →
      ∀ m : ℕ, 0 < xiSliceHeatTransfer lam 0 t (2 * m) := by
  set ε' := min ε (1 / 3) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'3 : ε' ≤ 1 / 3 := min_le_right _ _
  obtain ⟨g₁, g₂, g₃⟩ := weylFloor_gaps_of_eps hε'0 hε'3
  have hω0 : 0 < min (1 / 100) ε' := lt_min (by norm_num) hε'0
  obtain ⟨t₀, ht₀, h⟩ := exists_xiSliceHeatTransfer_pos_heat_of_at_heat (by positivity)
    (exists_xiSliceHeatTransfer_pos_at_heat_of_low_order (by positivity)
      (exists_xiSliceHeatTransfer_pos_low_order_weylFloor (η := ε' / 16) (ω := min (1 / 100) ε')
        (by linarith) (by linarith) (by positivity) (by linarith) hω0 (min_le_left _ _)
        g₁ g₂ g₃))
  refine ⟨t₀, ht₀, fun t ht lam hlam m => h t ht lam (le_trans ?_ hlam) m⟩
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  exact div_le_div_of_nonneg_right (by linarith [min_le_left ε (1 / 3 : ℝ)]) hlog.le

end DeBruijn

end

end RHTower
