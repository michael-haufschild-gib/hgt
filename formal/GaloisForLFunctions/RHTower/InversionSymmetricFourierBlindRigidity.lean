import GaloisForLFunctions.RHTower.CosDilationBlindFiveThirdsSupportVanishing

/-!
# Inversion-symmetric Fourier-blind functions of short support vanish

Let `G : ℝ → ℝ` be continuous and even, with the inversion symmetry `G(1/x) = x G(x)` for
`x > 0`, vanishing on `[0, c)` for some `c > 0` (so by inversion it is supported in
`c ≤ |x| ≤ 1/c`), and whose Fourier transform vanishes at every integer `n` with `|n| ≥ 2`.

**Theorems.**
* `eq_zero_of_inversionSymmetric_fourierBlind_of_golden`: if `c² + c > 1` (`1/c < φ`), `G = 0`.
* `eq_zero_of_inversionSymmetric_fourierBlind_of_five_thirds`: if `5c > 3` (`1/c < 5/3`), `G = 0`.

These are the linear forms of `eq_zero_of_cosDilationKernel_blind_of_golden` and
`eq_zero_of_cosDilationKernel_blind_of_lt_five_thirds_mul`: no positive definiteness is used.  By
inversion, `∫ G(x) e^{2πinx} dx = ∫ G(t) e^{2πin/t} dt/|t|`, so the hypotheses ask for
annihilation of the lattice cross `{e^{2πinx}} ∪ {e^{2πin/t}}` on the hyperbola (a
Heisenberg-uniqueness problem in the sense of Hedenmalm–Montes-Rodríguez) by a pair of measures
tied by the symmetry, with the three exceptional modes `n = 0, ±1` and compact support.

**Proof.**  Put `a₀ = Re Ĝ(0)`, `a₁ = Re Ĝ(1)`, `H(v) = G(1 − 1/v)/v`, `τ(v) = 2 + 1/(v − 1)`.
* *Poisson periodization* (`tsum_add_eq_of_fourierBlind`): `Σ_k G(x + k) = a₀ + 2a₁ cos 2πx`.
  For `c > ½` and `v ≥ 2` only the translates `1 − 1/v`, `1 + 1/v`, `2 − 1/v` of `x = 1 − 1/v`
  meet the support, and inversion turns the periodization into the Gauss–Farey equation
  `H(v) + H(v + 1) + H(τ(v))/(v − 1) = (a₀ + 2a₁ cos(2π/v))/v`
  (`inversionSymmetric_gauss_farey_equation`).
* *Profile*: for `v ≥ v* = max(2, c/(2c − 1))` the last term vanishes, so `H` equals the explicit
  series `fareySeriesR (a₀ + 2a₁) (2a₁)`, holomorphic on `Re z > ½`
  (`inversionSymmetric_profile_eq_fareySeriesR`); and `H = 0` on `[2, w₂]`, `w₂ = 1/(1 − c)`.
* *Golden case*: `v* < w₂`, so the series vanishes on an interval, hence identically, and the
  recursion at `v = 2, 4` gives `a₀ = a₁ = 0`.
* *`5/3` case* (`3/5 < c`, `c² + c ≤ 1`): `2 < v* < 3`, and on `(2, min(w₂, 1 + 1/(v* − 2)))` the
  equation becomes the Lewis identity `(v − 1)F(v) = F(τ(v))`, which forces `a₀ = a₁ = 0`
  (`eq_zero_of_fareySeriesR_lewis_identity`).  On the remaining window `[w₂, v*]` the equation
  reads `H(v) = −H(τ(v))/(v − 1)`.  The Gauss branch maps the window into itself (`τ(v*) = w₂`,
  and `τ(w₂) = 1 + 1/c ≤ v*` because `c² + c ≤ 1`) and `v − 1 ≥ c/(1 − c) > 1` there, so
  iterating the contraction gives `H = 0` on the window.
* *Conclusion*: `H = 0` on `[2, ∞)`, so `G = 0` on `[½, 1]`, on `[0, ½)` by support, on `(1, ∞)`
  by inversion and on `(−∞, 0)` by evenness.
-/

open MeasureTheory Set Real Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ### Poisson periodization of an even Fourier-blind function -/

/-- **Poisson periodization.**  For a continuous, compactly supported, even real `G` whose Fourier
transform vanishes at every integer `|n| ≥ 2`,
`Σ_k G(x + k) = Re Ĝ(0) + 2 Re Ĝ(1) cos 2πx`. -/
theorem tsum_add_eq_of_fourierBlind {G : ℝ → ℝ} (hG : Continuous G) (hcpt : HasCompactSupport G)
    (heven : ∀ x, G (-x) = G x)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0) (x : ℝ) :
    ∑' k : ℤ, G (x + k) = (𝓕 (fun x => (G x : ℂ)) 0).re +
      2 * (𝓕 (fun x => (G x : ℂ)) 1).re * Real.cos (2 * π * x) := by
  set ρ : C(ℝ, ℂ) := ⟨fun x => (G x : ℂ), Complex.continuous_ofReal.comp hG⟩ with hρ
  have hρc : (ρ : ℝ → ℂ) = fun x => (G x : ℂ) := rfl
  obtain ⟨B, hB⟩ : ∃ B, ∀ y, G y ≠ 0 → |y| ≤ B := by
    obtain ⟨B, hB⟩ := hcpt.isCompact.isBounded.subset_closedBall 0
    refine ⟨B, fun y hy => ?_⟩
    have := hB (subset_tsupport _ hy)
    rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  have hout : ∀ n : ℤ, n ∉ Finset.Icc (-1 : ℤ) 1 → 2 ≤ |n| := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [le_abs']
    omega
  have h_sum : Summable fun n : ℤ => 𝓕 (ρ : ℝ → ℂ) n := by
    refine summable_of_ne_finset_zero (s := Finset.Icc (-1 : ℤ) 1) fun n hn => ?_
    rw [hρc, hblind n (hout n hn)]
  have h_norm : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(ρ.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ := by
    intro K
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
    obtain ⟨N, hN⟩ := exists_int_gt (R + B)
    refine summable_of_ne_finset_zero (s := Finset.Icc (-N) N) fun n hn => ?_
    rw [norm_eq_zero]
    ext ⟨y, hy⟩
    have hyR : |y| ≤ R := by
      have := hR hy
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    have hn' : (N : ℝ) < |(n : ℝ)| := by
      rw [Finset.mem_Icc] at hn
      have : N < |n| := by rw [lt_abs]; omega
      exact_mod_cast this
    have hbig : B < |y + n| := by
      have h3 := abs_add_le (y + n) (-y)
      have e1 : y + n + -y = (n : ℝ) := by ring
      rw [e1, abs_neg] at h3
      linarith
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight, ContinuousMap.zero_apply, hρ, ContinuousMap.coe_mk]
    by_contra hne
    have hne' : G (y + n) ≠ 0 := fun h => hne (by rw [h, Complex.ofReal_zero])
    linarith [hB _ hne']
  have hP := Real.tsum_eq_tsum_fourier h_norm h_sum x
  have hL : (∑' k : ℤ, ρ (x + k)) = ((∑' k : ℤ, G (x + k) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; rfl
  rw [hL] at hP
  conv_rhs at hP => rw [tsum_eq_sum (s := Finset.Icc (-1 : ℤ) 1) fun n hn => by
    rw [hρc, hblind n (hout n hn), zero_mul]]
  have hI : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by decide
  rw [hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hP
  -- the transform is even
  have hneg : 𝓕 (fun x => (G x : ℂ)) ((-1 : ℤ) : ℝ) = 𝓕 (fun x => (G x : ℂ)) 1 := by
    have h1 := integral_neg_eq_self
      (fun v : ℝ => Complex.exp (↑(-2 * π * v * 1) * Complex.I) • ((G v : ℝ) : ℂ)) volume
    rw [fourier_real_eq_integral_exp_smul, fourier_real_eq_integral_exp_smul, ← h1]
    congr 1
    funext v
    simp only [heven]
    congr 2
    push_cast
    ring
  have hre := congrArg Complex.re hP
  rw [Complex.ofReal_re] at hre
  rw [hre]
  simp only [hρc, fourier_coe_apply]
  have hexp : ∀ c : ℂ, Complex.exp (2 * ↑π * Complex.I * c * ↑x / ((1 : ℝ) : ℂ)) =
      Complex.exp (c * ((2 * π * x : ℝ) : ℂ) * Complex.I) := by
    intro c; congr 1; push_cast; ring
  simp only [hexp]
  rw [hneg]
  simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, neg_mul, one_mul, zero_mul,
    Complex.exp_zero, mul_one]
  rw [← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.mul_im, Complex.add_im]
  ring

/-! ### The rigidity theorem -/

/-- A continuous even inversion-symmetric function vanishing on `[0, 1)` vanishes. -/
theorem eq_zero_of_inversionSymmetric_of_zero_on_Ico {G : ℝ → ℝ} (hG : Continuous G)
    (heven : ∀ x, G (-x) = G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x)
    (h01 : ∀ x, 0 ≤ x → x < 1 → G x = 0) (y : ℝ) : G y = 0 := by
  have hcl : IsClosed {x | G x = 0} := isClosed_eq hG continuous_const
  have h1 : G 1 = 0 := by
    have hsub : Ico (0 : ℝ) 1 ⊆ {x | G x = 0} := fun x hx => h01 x hx.1 hx.2
    have := hcl.closure_subset_iff.mpr hsub
    rw [closure_Ico (by norm_num)] at this
    exact this ⟨by norm_num, le_rfl⟩
  have hpos : ∀ x, 0 ≤ x → G x = 0 := by
    intro x hx
    rcases lt_trichotomy x 1 with h | h | h
    · exact h01 x hx h
    · rw [h]; exact h1
    · have hx0 : 0 < x := by linarith
      have hi := hinv x hx0
      rw [h01 x⁻¹ (inv_nonneg.mpr hx) (inv_lt_one_of_one_lt₀ h)] at hi
      exact (mul_eq_zero.mp hi.symm).resolve_left hx0.ne'
  rcases le_or_gt 0 y with hy | hy
  · exact hpos y hy
  · rw [← heven]; exact hpos _ (by linarith)

/-- A continuous even inversion-symmetric `G` vanishing on `[0, ½)` and at `1 − 1/v` for every
`v ≥ 2` vanishes. -/
theorem eq_zero_of_inversionSymmetric_of_profile_zero {G : ℝ → ℝ} (hG : Continuous G)
    (heven : ∀ x, G (-x) = G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x)
    (hhalf : ∀ x, 0 ≤ x → x < 1 / 2 → G x = 0) (hprof : ∀ v, 2 ≤ v → G (1 - 1 / v) = 0)
    (y : ℝ) : G y = 0 := by
  refine eq_zero_of_inversionSymmetric_of_zero_on_Ico hG heven hinv (fun x hx hx1 => ?_) y
  rcases lt_or_ge x (1 / 2) with hx2 | hx2
  · exact hhalf x hx hx2
  · have hx1' : 0 < 1 - x := by linarith
    have hv2 : 2 ≤ 1 / (1 - x) := by rw [le_div_iff₀ hx1']; linarith
    have hx' : 1 - 1 / (1 / (1 - x)) = x := by rw [one_div_one_div]; ring
    have := hprof _ hv2
    rwa [hx'] at this

/-! ### Support -/

section Support

variable {G : ℝ → ℝ} {c : ℝ}

/-- The vanishing on `[0, c)` extends to `[0, c]`. -/
theorem inversionSymmetric_eq_zero_of_le (hG : Continuous G) (hc0 : 0 < c)
    (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0) : ∀ x, 0 ≤ x → x ≤ c → G x = 0 := by
  have hGc : G c = 0 := by
    have hcl : IsClosed {x | G x = 0} := isClosed_eq hG continuous_const
    have hsub : Ico (0 : ℝ) c ⊆ {x | G x = 0} := fun x hx => hsupp x hx.1 hx.2
    have := hcl.closure_subset_iff.mpr hsub
    rw [closure_Ico hc0.ne] at this
    exact this ⟨hc0.le, le_rfl⟩
  intro x hx hxc
  rcases eq_or_lt_of_le hxc with h | h
  · rw [h]; exact hGc
  · exact hsupp x hx h

/-- By inversion, `G` vanishes on `[1/c, ∞)`. -/
theorem inversionSymmetric_eq_zero_of_inv_le (hG : Continuous G)
    (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x) (hc0 : 0 < c)
    (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0) : ∀ x, c⁻¹ ≤ x → G x = 0 := by
  have hsupp' := inversionSymmetric_eq_zero_of_le hG hc0 hsupp
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (inv_pos.mpr hc0) hx
  have h := hinv x hx0
  have hxi : x⁻¹ ≤ c := by rw [inv_le_comm₀ hx0 hc0]; exact hx
  rw [hsupp' x⁻¹ (inv_nonneg.mpr hx0.le) hxi] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hx0.ne'

theorem hasCompactSupport_of_inversionSymmetric (hG : Continuous G)
    (heven : ∀ x, G (-x) = G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x) (hc0 : 0 < c)
    (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0) : HasCompactSupport G := by
  have hbig := inversionSymmetric_eq_zero_of_inv_le hG hinv hc0 hsupp
  refine HasCompactSupport.intro (isCompact_Icc (a := -c⁻¹) (b := c⁻¹)) fun x hx => ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · rw [← heven]; exact hbig _ (by linarith)
  · exact hbig _ hx.le

end Support

/-! ### The Gauss–Farey equation and the Farey profile -/

section Farey

variable {G : ℝ → ℝ} (hG : Continuous G) (heven : ∀ x, G (-x) = G x)
  (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x) {c : ℝ} (hc : 1 / 2 < c)
  (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0)
  (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0)
include hG heven hinv hc hsupp hblind

/-- **Three-term periodization.**  For `c > ½` and `v ≥ 2`,
`G(1 − 1/v) + G(1 + 1/v) + G(2 − 1/v) = a₀ + 2a₁ cos(2π/v)`. -/
theorem inversionSymmetric_three_term_periodization {v : ℝ} (hv2 : 2 ≤ v) :
    G (1 - 1 / v) + G (1 + 1 / v) + G (2 - 1 / v) = (𝓕 (fun x => (G x : ℂ)) 0).re +
      2 * (𝓕 (fun x => (G x : ℂ)) 1).re * Real.cos (2 * π / v) := by
  have hc0 : 0 < c := by linarith
  have hbig := inversionSymmetric_eq_zero_of_inv_le hG hinv hc0 hsupp
  have hcpt := hasCompactSupport_of_inversionSymmetric hG heven hinv hc0 hsupp
  have hci2 : c⁻¹ < 2 := by rw [inv_lt_comm₀ hc0 (by norm_num)]; linarith
  have hv0 : 0 < v := by linarith
  have hinvv : 1 / v ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hv2
  have hinvv0 : 0 < 1 / v := by positivity
  have h := tsum_add_eq_of_fourierBlind hG hcpt heven hblind (1 - 1 / v)
  rw [tsum_eq_sum (s := {0, -2, 1}) fun k hk => ?_] at h
  · rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
      Finset.sum_singleton] at h
    have e0 : 1 - 1 / v + ((0 : ℤ) : ℝ) = 1 - 1 / v := by simp
    have e2 : G (1 - 1 / v + ((-2 : ℤ) : ℝ)) = G (1 + 1 / v) := by
      rw [← heven]; congr 1; push_cast; ring
    have e1 : 1 - 1 / v + ((1 : ℤ) : ℝ) = 2 - 1 / v := by push_cast; ring
    have hcos : Real.cos (2 * π * (1 - 1 / v)) = Real.cos (2 * π / v) := by
      rw [show 2 * π * (1 - 1 / v) = 2 * π - 2 * π / v by ring, Real.cos_two_pi_sub]
    rw [e0, e2, e1, hcos] at h
    linarith
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rcases le_or_gt 2 k with hk2 | hk2
    · have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      exact hbig _ (by linarith)
    rcases le_or_gt (-1) k with hkm | hkm
    · have : k = -1 := by omega
      subst this
      rw [← heven]
      exact hsupp _ (by push_cast; linarith) (by push_cast; linarith)
    · have hk3 : k ≤ -3 := by omega
      have : (k : ℝ) ≤ -3 := by exact_mod_cast hk3
      rw [← heven]
      exact hbig _ (by linarith)

/-- **The Gauss–Farey equation** `H(v) + H(v + 1) + H(τ(v))/(v − 1) = (a₀ + 2a₁ cos(2π/v))/v`
for `H(v) = G(1 − 1/v)/v`, `c > ½` and `v ≥ 2`. -/
theorem inversionSymmetric_gauss_farey_equation {v : ℝ} (hv2 : 2 ≤ v) :
    G (1 - 1 / v) / v + G (1 - 1 / (v + 1)) / (v + 1) +
        G (1 - 1 / gaussBranch v) / gaussBranch v / (v - 1) =
      ((𝓕 (fun x => (G x : ℂ)) 0).re +
        2 * (𝓕 (fun x => (G x : ℂ)) 1).re * Real.cos (2 * π / v)) / v := by
  have hv0 : 0 < v := by linarith
  have hv1 : 0 < v - 1 := by linarith
  have hv1' : v - 1 ≠ 0 := hv1.ne'
  have hv0' : v ≠ 0 := hv0.ne'
  have hvp : v + 1 ≠ 0 := by linarith
  have h2v : 2 * v - 1 ≠ 0 := ne_of_gt (by linarith)
  have hp := inversionSymmetric_three_term_periodization hG heven hinv hc hsupp hblind hv2
  have hs1 : 1 - 1 / (v + 1) = v / (v + 1) := by field_simp; ring
  have hr1 : 0 < 1 - 1 / (v + 1) := by rw [hs1]; positivity
  have hinv1 := hinv _ hr1
  have e1 : (1 - 1 / (v + 1))⁻¹ = 1 + 1 / v := by
    rw [hs1, inv_div]; field_simp
  rw [e1] at hinv1
  have hτ : gaussBranch v = (2 * v - 1) / (v - 1) := by unfold gaussBranch; field_simp; ring
  have hs2 : 1 - 1 / gaussBranch v = v / (2 * v - 1) := by rw [hτ]; field_simp; ring
  have hr2 : 0 < 1 - 1 / gaussBranch v := by rw [hs2]; exact div_pos hv0 (by linarith)
  have hinv2 := hinv _ hr2
  have e2 : (1 - 1 / gaussBranch v)⁻¹ = 2 - 1 / v := by
    rw [hs2, inv_div]; field_simp
  rw [e2] at hinv2
  rw [hinv1, hinv2] at hp
  set X := G (1 - 1 / v) with hX
  set Y := G (1 - 1 / (v + 1)) with hY
  set Z := G (1 - 1 / gaussBranch v) with hZ
  rw [hs1, hs2] at hp
  rw [← hp, hτ]
  field_simp

/-- **The Farey profile.**  For `c > ½`, `H(v) = G(1 − 1/v)/v` equals
`fareySeriesR (a₀ + 2a₁) (2a₁)` on `[max(2, c/(2c − 1)), ∞)`. -/
theorem inversionSymmetric_profile_eq_fareySeriesR {v : ℝ} (hv : max 2 (c / (2 * c - 1)) ≤ v) :
    G (1 - 1 / v) / v = fareySeriesR ((𝓕 (fun x => (G x : ℂ)) 0).re +
      2 * (𝓕 (fun x => (G x : ℂ)) 1).re) (2 * (𝓕 (fun x => (G x : ℂ)) 1).re) v := by
  have hc0 : 0 < c := by linarith
  have hbig := inversionSymmetric_eq_zero_of_inv_le hG hinv hc0 hsupp
  have hcpt := hasCompactSupport_of_inversionSymmetric hG heven hinv hc0 hsupp
  set a₀ := (𝓕 (fun x => (G x : ℂ)) 0).re with ha₀
  set a₁ := (𝓕 (fun x => (G x : ℂ)) 1).re with ha₁
  set a := a₀ + 2 * a₁ with ha
  set b := 2 * a₁ with hb
  have h2c : 0 < 2 * c - 1 := by linarith
  set vs := max 2 (c / (2 * c - 1)) with hvs
  -- the two-term periodization: the translate `2 − 1/v` leaves the support
  have htwo : ∀ v, vs ≤ v → G (1 - 1 / v) + G (1 + 1 / v) =
      a₀ + 2 * a₁ * Real.cos (2 * π / v) := by
    intro v hv
    have hv2 : 2 ≤ v := (le_max_left _ _).trans hv
    have hv0 : 0 < v := by linarith
    have hvw : c / (2 * c - 1) ≤ v := (le_max_right _ _).trans hv
    have hk1' : c⁻¹ ≤ 2 - 1 / v := by
      rw [div_le_iff₀ h2c] at hvw
      rw [inv_eq_one_div, div_le_iff₀ hc0]
      have : c / v ≤ 2 * c - 1 := by rw [div_le_iff₀ hv0]; linarith
      have e : (2 - 1 / v) * c = 2 * c - c / v := by ring
      linarith
    have h := inversionSymmetric_three_term_periodization hG heven hinv hc hsupp hblind hv2
    rw [hbig _ hk1', add_zero] at h
    exact h
  -- the Farey recursion for `H(v) = G(1 − 1/v)/v`
  set H : ℝ → ℝ := fun v => G (1 - 1 / v) / v with hH
  have hrec : ∀ v, vs ≤ v → H v + H (v + 1) = (a + b * (Real.cos (2 * π / v) - 1)) / v := by
    intro v hv
    have hv0 : 0 < v := by linarith [(le_max_left 2 (c / (2 * c - 1))).trans hv]
    have hvp : 0 < v + 1 := by linarith
    have hs1 : 1 - 1 / (v + 1) = v / (v + 1) := by field_simp; ring
    have hr : 0 < 1 - 1 / (v + 1) := by rw [hs1]; positivity
    have hi := hinv (1 - 1 / (v + 1)) hr
    have e1 : (1 - 1 / (v + 1))⁻¹ = 1 + 1 / v := by
      rw [hs1, inv_div]; field_simp
    rw [e1] at hi
    have h := htwo v hv
    rw [hi] at h
    simp only [hH]
    set X := G (1 - 1 / v)
    set Y := G (1 - 1 / (v + 1))
    rw [hs1] at h
    rw [show a + b * (Real.cos (2 * π / v) - 1) = a₀ + 2 * a₁ * Real.cos (2 * π / v) by
      rw [ha, hb]; ring, ← h]
    field_simp
  obtain ⟨CG, hCG⟩ : ∃ C, ∀ r, |G r| ≤ C := by
    obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuous hG
    exact ⟨C, fun r => by rw [← Real.norm_eq_abs]; exact hC r⟩
  exact eq_fareySeriesR_of_recursion (le_trans (by norm_num) (le_max_left _ _)) hrec
    (fun w hw => by
      have hw0 : 0 < w := by linarith
      simp only [hH]
      rw [abs_div, abs_of_pos hw0]
      exact div_le_div_of_nonneg_right (hCG _) hw0.le) v hv

end Farey

/-! ### The rigidity theorems -/

/-- **Inversion-symmetric Fourier-blind functions of support ratio below the golden ratio
vanish.** -/
theorem eq_zero_of_inversionSymmetric_fourierBlind_of_golden {G : ℝ → ℝ} (hG : Continuous G)
    (heven : ∀ x, G (-x) = G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x) {c : ℝ} (hc0 : 0 < c)
    (hgold : 1 < c ^ 2 + c) (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0) (y : ℝ) : G y = 0 := by
  rcases le_or_gt 1 c with hc1 | hc1
  · exact eq_zero_of_inversionSymmetric_of_zero_on_Ico hG heven hinv
      (fun x hx hx1 => hsupp x hx (lt_of_lt_of_le hx1 hc1)) y
  have hhalf : 1 / 2 < c := by nlinarith
  set a₀ := (𝓕 (fun x => (G x : ℂ)) 0).re with ha₀
  set a₁ := (𝓕 (fun x => (G x : ℂ)) 1).re with ha₁
  set a := a₀ + 2 * a₁ with ha
  set b := 2 * a₁ with hb
  have h2c : 0 < 2 * c - 1 := by linarith
  set vs := max 2 (c / (2 * c - 1)) with hvs
  set H : ℝ → ℝ := fun v => G (1 - 1 / v) / v with hH
  have hHF : ∀ v, vs ≤ v → H v = fareySeriesR a b v := fun v hv =>
    inversionSymmetric_profile_eq_fareySeriesR hG heven hinv hhalf hsupp hblind hv
  -- the zero range of `H`
  set w₂ := 1 / (1 - c) with hw₂
  have h1c : 0 < 1 - c := by linarith
  have hHzero : ∀ v, 2 ≤ v → v < w₂ → H v = 0 := by
    intro v hv2 hvw
    have hv0 : 0 < v := by linarith
    have hinvv : 1 / v ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hv2
    have hlt : 1 - 1 / v < c := by
      rw [hw₂, lt_div_iff₀ h1c] at hvw
      rw [show 1 - 1 / v = (v - 1) / v by field_simp, div_lt_iff₀ hv0]
      linarith
    simp only [hH]
    rw [hsupp _ (by linarith) hlt, zero_div]
  have hvsw : vs < w₂ := by
    rw [hvs, max_lt_iff]
    constructor
    · rw [hw₂, lt_div_iff₀ h1c]; linarith
    · rw [hw₂, div_lt_div_iff₀ h2c h1c]; nlinarith
  -- analytic continuation
  set q := (vs + w₂) / 2 with hq
  have hvsq : vs < q := by rw [hq]; linarith
  have hGa := (differentiableOn_fareySeries a b).analyticOnNhd isOpen_halfPlaneHalf
  have hvs2 : 2 ≤ vs := le_max_left _ _
  have hzero := eqOn_zero_of_real_interval hGa (convex_halfSpace_re_gt (1 / 2)).isPreconnected
    hvsq (by show 1 / 2 < (((vs + q) / 2 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith)
    fun x hx1 hx2 => by
      rw [fareySeries_ofReal, ← hHF x hx1.le, hHzero x (by linarith) (by linarith),
        Complex.ofReal_zero]
  have hFall : ∀ v : ℝ, 1 ≤ v → fareySeriesR a b v = 0 := by
    intro v hv
    have hvU : ((v : ℝ) : ℂ) ∈ halfPlaneHalf := by
      show 1 / 2 < ((v : ℝ) : ℂ).re
      rw [Complex.ofReal_re]; linarith
    have := hzero hvU
    rw [fareySeries_ofReal, Pi.zero_apply] at this
    exact_mod_cast this
  have e2 := fareySeriesR_add_one a b (v := 2) (by norm_num)
  have e4 := fareySeriesR_add_one a b (v := 4) (by norm_num)
  rw [hFall 2 (by norm_num), hFall (2 + 1) (by norm_num), add_zero] at e2
  rw [hFall 4 (by norm_num), hFall (4 + 1) (by norm_num), add_zero] at e4
  have c2 : Real.cos (2 * π / 2) = -1 := by rw [show 2 * π / 2 = π by ring, Real.cos_pi]
  have c4 : Real.cos (2 * π / 4) = 0 := by
    rw [show 2 * π / 4 = π / 2 by ring, Real.cos_pi_div_two]
  rw [c2] at e2
  rw [c4] at e4
  have hb0 : b = 0 := by
    have e2' : a + b * (-1 - 1) = 0 := by
      have := e2; rw [eq_comm, div_eq_zero_iff] at this
      rcases this with h | h
      · exact h
      · norm_num at h
    have e4' : a + b * (0 - 1) = 0 := by
      have := e4; rw [eq_comm, div_eq_zero_iff] at this
      rcases this with h | h
      · exact h
      · norm_num at h
    linarith
  have ha0 : a = 0 := by
    have := e4; rw [eq_comm, div_eq_zero_iff] at this
    rcases this with h | h
    · rw [hb0] at h; linarith
    · norm_num at h
  -- now `H = 0` on `[2, ∞)`
  have hHall : ∀ v, 2 ≤ v → H v = 0 := by
    intro v hv
    rcases lt_or_ge v w₂ with h | h
    · exact hHzero v hv h
    · rw [hHF v (by linarith), hFall v (by linarith)]
  refine eq_zero_of_inversionSymmetric_of_profile_zero hG heven hinv
    (fun x hx hx2 => hsupp x hx (by linarith)) (fun v hv => ?_) y
  have h := hHall v hv
  simp only [hH] at h
  exact (div_eq_zero_iff.mp h).resolve_right (by linarith)
/-- **Inversion-symmetric Fourier-blind functions of support ratio below `5/3` vanish.** -/
theorem eq_zero_of_inversionSymmetric_fourierBlind_of_five_thirds {G : ℝ → ℝ}
    (hG : Continuous G) (heven : ∀ x, G (-x) = G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x)
    {c : ℝ} (h53 : 3 < 5 * c) (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0) (y : ℝ) : G y = 0 := by
  have hc0 : 0 < c := by linarith
  rcases lt_or_ge 1 (c ^ 2 + c) with hg | hg
  · exact eq_zero_of_inversionSymmetric_fourierBlind_of_golden hG heven hinv hc0 hg hsupp
      hblind y
  have hc23 : c < 2 / 3 := by nlinarith
  have hhalf : 1 / 2 < c := by linarith
  have hsupp' := inversionSymmetric_eq_zero_of_le hG hc0 hsupp
  set a₀ := (𝓕 (fun x => (G x : ℂ)) 0).re with ha₀
  set a₁ := (𝓕 (fun x => (G x : ℂ)) 1).re with ha₁
  set a := a₀ + 2 * a₁ with ha
  set b := 2 * a₁ with hb
  set F := fareySeriesR a b with hF
  set H : ℝ → ℝ := fun v => G (1 - 1 / v) / v with hH
  have h2c : 0 < 2 * c - 1 := by linarith
  have h1c : 0 < 1 - c := by linarith
  set vs := c / (2 * c - 1) with hvs
  have hvs2 : 2 < vs := by rw [hvs, lt_div_iff₀ h2c]; linarith
  have hvs3 : vs < 3 := by rw [hvs, div_lt_iff₀ h2c]; linarith
  have hHF : ∀ v, vs ≤ v → H v = F v := fun v hv =>
    inversionSymmetric_profile_eq_fareySeriesR hG heven hinv hhalf hsupp hblind
      (max_le (by linarith) hv)
  set w₂ := 1 / (1 - c) with hw₂
  have hw₂2 : 2 < w₂ := by rw [hw₂, lt_div_iff₀ h1c]; linarith
  have hHzero : ∀ v, 2 ≤ v → v ≤ w₂ → H v = 0 := by
    intro v hv2 hvw
    have hv0 : 0 < v := by linarith
    have hinvv : 1 / v ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hv2
    have hle : 1 - 1 / v ≤ c := by
      rw [hw₂, le_div_iff₀ h1c] at hvw
      rw [show 1 - 1 / v = (v - 1) / v by field_simp, div_le_iff₀ hv0]
      linarith
    simp only [hH]
    rw [hsupp' _ (by linarith) hle, zero_div]
  -- the Lewis identity on an interval to the right of `2`
  set q := min w₂ (1 + 1 / (vs - 2)) with hq
  have hq2 : 2 < q := by
    rw [hq, lt_min_iff]
    refine ⟨hw₂2, ?_⟩
    have : 1 < 1 / (vs - 2) := by rw [lt_div_iff₀ (by linarith)]; linarith
    linarith
  have hlewis : ∀ v, 2 < v → v < q → (v - 1) * F v = F (gaussBranch v) := by
    intro v hv2 hvq
    have hvw : v ≤ w₂ := hvq.le.trans (min_le_left _ _)
    have hv1 : 0 < v - 1 := by linarith
    have hτ : vs ≤ gaussBranch v := by
      have hvq' : v ≤ 1 + 1 / (vs - 2) := hvq.le.trans (min_le_right _ _)
      unfold gaussBranch
      have : v - 1 ≤ 1 / (vs - 2) := by linarith
      rw [le_div_iff₀ (by linarith)] at this
      have : vs - 2 ≤ 1 / (v - 1) := by rw [le_div_iff₀ hv1]; linarith
      linarith
    have e : H v + H (v + 1) + H (gaussBranch v) / (v - 1) =
        (a₀ + 2 * a₁ * Real.cos (2 * π / v)) / v :=
      inversionSymmetric_gauss_farey_equation hG heven hinv hhalf hsupp hblind hv2.le
    rw [hHzero v hv2.le hvw, hHF (v + 1) (by linarith), hHF (gaussBranch v) hτ, zero_add] at e
    have hrec := fareySeriesR_add_one a b (v := v) (by linarith)
    rw [← hF] at hrec
    have hg : (a₀ + 2 * a₁ * Real.cos (2 * π / v)) / v =
        (a + b * (Real.cos (2 * π / v) - 1)) / v := by
      rw [ha, hb]; ring
    rw [hg, ← hrec] at e
    field_simp at e
    linarith
  obtain ⟨ha0, hb0⟩ := eq_zero_of_fareySeriesR_lewis_identity hq2 hlewis
  have hF0 : ∀ v, F v = 0 := fun v => by rw [hF, ha0, hb0]; simp [fareySeriesR]
  have hga₁ : a₁ = 0 := by rw [hb] at hb0; linarith
  have hga₀ : a₀ = 0 := by rw [ha, hb0] at ha0; linarith
  -- the window `[w₂, vs]`: a contraction along the Gauss branch
  have hwin : ∀ v, w₂ ≤ v → v ≤ vs → H v = -(H (gaussBranch v) / (v - 1)) := by
    intro v hvw hvs'
    have hv2 : 2 ≤ v := by linarith
    have e : H v + H (v + 1) + H (gaussBranch v) / (v - 1) =
        (a₀ + 2 * a₁ * Real.cos (2 * π / v)) / v :=
      inversionSymmetric_gauss_farey_equation hG heven hinv hhalf hsupp hblind hv2
    rw [hHF (v + 1) (by linarith), hF0, hga₀, hga₁] at e
    simp only [mul_zero, zero_mul, add_zero, zero_div] at e
    linarith
  have hτwin : ∀ v, w₂ ≤ v → v ≤ vs → w₂ ≤ gaussBranch v ∧ gaussBranch v ≤ vs := by
    intro v hvw hvs'
    have hv1 : 0 < v - 1 := by linarith
    have hA : 1 ≤ v * (1 - c) := by rw [hw₂, div_le_iff₀ h1c] at hvw; exact hvw
    have hB : v * (2 * c - 1) ≤ c := by rw [hvs, le_div_iff₀ h2c] at hvs'; exact hvs'
    unfold gaussBranch
    set t := 1 / (v - 1) with ht
    have htv : t * (v - 1) = 1 := by rw [ht]; field_simp
    have ht0 : 0 < t := by positivity
    constructor
    · rw [hw₂, div_le_iff₀ h1c]
      have hB' : (v - 1) * (2 * c - 1) ≤ 1 - c := by linarith
      have h1 := mul_le_mul_of_nonneg_left hB' ht0.le
      have e : t * ((v - 1) * (2 * c - 1)) = 2 * c - 1 := by rw [← mul_assoc, htv, one_mul]
      linarith
    · rw [hvs, le_div_iff₀ h2c]
      have hA' : c ≤ (v - 1) * (1 - c) := by linarith
      have h1 := mul_le_mul_of_nonneg_left hA' ht0.le
      have e : t * ((v - 1) * (1 - c)) = 1 - c := by rw [← mul_assoc, htv, one_mul]
      have htc : t * c ≤ 1 - c := by linarith
      have key : c * ((2 + t) * (2 * c - 1)) ≤ c * c := by
        nlinarith [mul_le_mul_of_nonneg_right htc h2c.le]
      exact le_of_mul_le_mul_left key hc0
  obtain ⟨CG, hCG⟩ : ∃ C, ∀ r, |G r| ≤ C := by
    obtain ⟨C, hC⟩ := (hasCompactSupport_of_inversionSymmetric hG heven hinv hc0
      hsupp).exists_bound_of_continuous hG
    exact ⟨C, fun r => by rw [← Real.norm_eq_abs]; exact hC r⟩
  have hw₂1 : 1 < w₂ - 1 := by rw [hw₂, lt_sub_iff_add_lt, lt_div_iff₀ h1c]; linarith
  set θ := 1 / (w₂ - 1) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by linarith)]; exact hw₂1
  have hiter : ∀ n : ℕ, ∀ v, w₂ ≤ v → v ≤ vs → |H v| ≤ CG * θ ^ n := by
    intro n
    induction n with
    | zero =>
      intro v hvw _
      have hv1 : 1 ≤ v := by linarith
      simp only [pow_zero, mul_one, hH]
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < v)]
      exact (div_le_self (abs_nonneg _) hv1).trans (hCG _)
    | succ n ih =>
      intro v hvw hvs'
      obtain ⟨h1, h2⟩ := hτwin v hvw hvs'
      have hv1 : w₂ - 1 ≤ v - 1 := by linarith
      rw [hwin v hvw hvs', abs_neg, abs_div, abs_of_pos (by linarith : (0 : ℝ) < v - 1)]
      calc |H (gaussBranch v)| / (v - 1) ≤ |H (gaussBranch v)| / (w₂ - 1) :=
            div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hv1
        _ ≤ CG * θ ^ n / (w₂ - 1) := div_le_div_of_nonneg_right (ih _ h1 h2) (by linarith)
        _ = CG * θ ^ (n + 1) := by rw [pow_succ, hθ]; ring
  have hwin0 : ∀ v, w₂ ≤ v → v ≤ vs → H v = 0 := by
    intro v hvw hvs'
    have hlim : Tendsto (fun n : ℕ => CG * θ ^ n) atTop (𝓝 (CG * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul CG
    have := ge_of_tendsto' hlim fun n => hiter n v hvw hvs'
    rw [mul_zero] at this
    exact abs_nonpos_iff.mp this
  have hHall : ∀ v, 2 ≤ v → H v = 0 := by
    intro v hv
    rcases le_or_gt v w₂ with h | h
    · exact hHzero v hv h
    rcases le_or_gt v vs with h' | h'
    · exact hwin0 v h.le h'
    · rw [hHF v h'.le, hF0]
  refine eq_zero_of_inversionSymmetric_of_profile_zero hG heven hinv
    (fun x hx hx2 => hsupp x hx (by linarith)) (fun v hv => ?_) y
  have h := hHall v hv
  simp only [hH] at h
  exact (div_eq_zero_iff.mp h).resolve_right (by linarith)

end

end RHTower
