import GaloisForLFunctions.RHTower.SoninBandSinc
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import Mathlib.Analysis.Fourier.Convolution
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheBlindSpotIsExactThroughThirdOrder

/-!
# The sine-kernel Gram moments match the blind spot through third order

The bandwidth-one evaluation Gram matrix of a unit-density sine process has entries
`S(x_i − x_j)`, `S(x) = sin(πx)/(πx) = 𝓕(1_{[−1/2,1/2]})(x)`, and the process has correlation
functions `ρ_n = det[S(x_i − x_j)]`. Splitting the sum `tr Ĝ^k = Σ_{i₁,…,i_k}` by index coincidences,
its per-point moments are
`κ₂ = 1 + ∫ S²ρ₂`, `κ₃ = 1 + 3∫ S²ρ₂ + ∬ S(x)S(y)S(x−y) ρ₃(0, x, y)`, with `ρ₂ = 1 − S²` and
`ρ₃(0, x, y) = 1 − S(x)² − S(y)² − S(x−y)² + 2S(x)S(y)S(x−y)` (`sineKappa₂`, `sineKappa₃`).

* **The values** (`sineKappa₂_eq`, `sineKappa₃_eq`): `κ₂ = 4/3` and `κ₃ = 2`. The fully
  distinct triple term vanishes (`sineTriple_eq_zero`).
* **The blind spot** (`sineMoments_eq_blindSpot`, `cubic_sineValue_le_two_thirds`): these are the
  moments of the coalescence blind spot `diag(1,1,1,1,2)`, so every cubic inertia certificate
  certifies at most `2/3` at sine-kernel statistics; `q⋆` reaches `3/4` iff `κ₄ ≤ 2503/768`
  (`qStarValue_sineKappa`).

All integrals are computed on the Fourier side. `S = 𝓕 1`, `S² = 𝓕 Δ` with the triangle
`Δ = 1 ⋆ 1 = (1 − |η|)₊` (`fourier_tri`, `tri_apply`), and `S³ = 𝓕 (Δ ⋆ 1)` by the
convolution theorem. Parseval for integrable square-integrable functions
(`integral_conj_fourier_mul_fourier`) and the modulation rule `𝓕(G e_x) = 𝓕G(· − x)` turn every
inner integral over `y` into an integral of compactly supported polynomials: `∫ S² = 1`,
`∫ S⁴ = ∫ Δ² = 2/3`, `∫ Δ³ = 1/2`.
-/

open MeasureTheory Complex FourierTransform
open scoped ComplexConjugate Convolution

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SineKernel

open _root_.RHTower

/-! ### The kernels -/

/-- The band indicator `1_{[−1/2, 1/2]}`. -/
def ind : ℝ → ℂ := (centralInterval (1 / 2)).indicator fun _ => 1

/-- The sine kernel `S(x) = sin(πx)/(πx)`, `S(0) = 1`. -/
def sk (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin (Real.pi * x) / (Real.pi * x)

/-- The triangle `Δ = 1 ⋆ 1`. -/
def tri : ℝ → ℂ := ind ⋆[ContinuousLinearMap.mul ℂ ℂ] ind

/-- The quadratic spline `Δ ⋆ 1`, the Fourier partner of `S³`. -/
def quad : ℝ → ℂ := tri ⋆[ContinuousLinearMap.mul ℂ ℂ] ind

theorem ind_apply (η : ℝ) : ind η = if η ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) then 1 else 0 := by
  simp only [ind, centralInterval, Set.indicator_apply]

theorem integrable_ind : Integrable ind := integrable_centralIndicator (1 / 2)

theorem norm_ind_le (η : ℝ) : ‖ind η‖ ≤ 1 := by
  rw [ind_apply]; split_ifs <;> simp

theorem memLp_two_ind : MemLp ind 2 := by
  refine (memLp_two_iff_integrable_sq_norm integrable_ind.aestronglyMeasurable).mpr ?_
  refine Integrable.mono' integrable_ind.norm (integrable_ind.aestronglyMeasurable.norm.pow 2) ?_
  refine Filter.Eventually.of_forall fun η => ?_
  have h := norm_ind_le η
  have h0 := norm_nonneg (ind η)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

theorem sk_neg (x : ℝ) : sk (-x) = sk x := by
  unfold sk
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (neg_ne_zero.mpr hx), if_neg hx, mul_neg, Real.sin_neg, neg_div_neg_eq]

/-- `S = 𝓕 1_{[−1/2,1/2]}`. -/
theorem fourier_ind (x : ℝ) : 𝓕 ind x = (sk x : ℂ) := by
  by_cases hx : x = 0
  · subst hx
    have h0 : 𝓕 ind 0 = ∫ v, ind v := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      congr 1; funext v; simp
    rw [h0, ind, integral_indicator (measurableSet_centralInterval _), centralInterval,
      MeasureTheory.setIntegral_const]
    simp [sk]
    norm_num
  · rw [ind, fourierIntegral_centralIndicator (by norm_num) hx, sk, if_neg hx,
      show 2 * Real.pi * (1 / 2) * x = Real.pi * x by ring]

/-! ### Parseval and modulation -/

/-- **Parseval for integrals**: for integrable square-integrable `F, G`,
`∫ conj(𝓕F) 𝓕G = ∫ conj(F) G`. -/
theorem integral_conj_fourier_mul_fourier {F G : ℝ → ℂ} (hF1 : Integrable F) (hF2 : MemLp F 2)
    (hG1 : Integrable G) (hG2 : MemLp G 2) :
    ∫ y, conj (𝓕 F y) * 𝓕 G y = ∫ η, conj (F η) * G η := by
  have h := MeasureTheory.Lp.inner_fourier_eq (hF2.toLp F) (hG2.toLp G)
  rw [L2.inner_def, L2.inner_def] at h
  have hl : (fun y => inner ℂ (((𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) y)
      (((𝓕 (hG2.toLp G) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) y)) =ᵐ[volume]
      fun y => conj (𝓕 F y) * 𝓕 G y := by
    filter_upwards [GaloisForLFunctions.RHTower.coeFn_fourier_toLp hF1 hF2,
      GaloisForLFunctions.RHTower.coeFn_fourier_toLp hG1 hG2] with y h1 h2
    rw [h1, h2, RCLike.inner_apply, mul_comm]
  have hr : (fun η => inner ℂ ((hF2.toLp F : Lp ℂ 2 (volume : Measure ℝ)) η)
      ((hG2.toLp G : Lp ℂ 2 (volume : Measure ℝ)) η)) =ᵐ[volume] fun η => conj (F η) * G η := by
    filter_upwards [hF2.coeFn_toLp, hG2.coeFn_toLp] with η h1 h2
    rw [h1, h2, RCLike.inner_apply, mul_comm]
  rw [integral_congr_ae hl, integral_congr_ae hr] at h
  exact h

/-- The character `η ↦ e^{2πiηx}`. -/
def ex (x η : ℝ) : ℂ := Complex.exp (((2 * Real.pi * η * x : ℝ) : ℂ) * Complex.I)

theorem norm_ex (x η : ℝ) : ‖ex x η‖ = 1 := by
  rw [ex, Complex.norm_exp_ofReal_mul_I]

/-- **Modulation**: `𝓕(G · e_x)(y) = 𝓕G(y − x)`. -/
theorem fourier_mul_ex (G : ℝ → ℂ) (x y : ℝ) :
    𝓕 (fun η => G η * ex x η) y = 𝓕 G (y - x) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  funext v
  rw [ex, smul_eq_mul, smul_eq_mul]
  rw [show ∀ a b : ℂ, Complex.exp a * (G v * Complex.exp b) = G v * Complex.exp (a + b) from
    fun a b => by rw [Complex.exp_add]; ring, mul_comm (Complex.exp _) (G v)]
  congr 2
  push_cast
  ring

theorem integrable_mul_ex {G : ℝ → ℂ} (hG : Integrable G) (x : ℝ) :
    Integrable fun η => G η * ex x η := by
  refine hG.mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun η => (norm_ex x η).le)
  exact (Continuous.aestronglyMeasurable (by unfold ex; fun_prop))

theorem memLp_two_mul_ex {G : ℝ → ℂ} (hG : MemLp G 2) (x : ℝ) :
    MemLp (fun η => G η * ex x η) 2 := by
  refine hG.of_le_mul (c := 1) ?_ (Filter.Eventually.of_forall fun η => ?_)
  · exact hG.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by unfold ex; fun_prop))
  · rw [norm_mul, norm_ex, mul_one, one_mul]

/-! ### The triangle and the spline -/

/-- The real triangle `(1 − |η|)₊`. -/
def triR (η : ℝ) : ℝ := max (1 - |η|) 0

theorem triR_nonneg (η : ℝ) : 0 ≤ triR η := le_max_right _ _

theorem triR_le_one (η : ℝ) : triR η ≤ 1 :=
  max_le (by linarith [abs_nonneg η]) zero_le_one

/-- `∫ (1 − |η|)₊^{k+1} = 2/(k + 2)`. -/
theorem integral_triR_pow_succ (k : ℕ) : ∫ η, triR η ^ (k + 1) = 2 / (k + 2) := by
  have h := integral_comp_abs (f := fun t => (max (1 - t) 0) ^ (k + 1))
  have e : (fun η : ℝ => triR η ^ (k + 1)) = fun η => (max (1 - |η|) 0) ^ (k + 1) := rfl
  rw [e, h]
  have hcont : Continuous fun t : ℝ => (max (1 - t) 0) ^ (k + 1) := by fun_prop
  have hsplit : ∫ t in Set.Ioi (0 : ℝ), (max (1 - t) 0) ^ (k + 1) =
      ∫ t in (0 : ℝ)..1, (1 - t) ^ (k + 1) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    have hU : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
      (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    have hz : ∀ t ∈ Set.Ioi (1 : ℝ), (max (1 - t) 0) ^ (k + 1) = 0 := fun t ht => by
      rw [max_eq_right (by linarith [Set.mem_Ioi.mp ht])]
      exact zero_pow (Nat.succ_ne_zero k)
    rw [hU, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      (integrableOn_zero.congr_fun (fun t ht => (hz t ht).symm) measurableSet_Ioi),
      setIntegral_eq_zero_of_forall_eq_zero hz, add_zero]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    show (max (1 - t) 0) ^ (k + 1) = (1 - t) ^ (k + 1)
    rw [max_eq_left (by linarith [ht.2])]
  rw [hsplit, intervalIntegral.integral_comp_sub_left (fun t => t ^ (k + 1)), sub_self, sub_zero,
    integral_pow]
  push_cast
  ring

/-- **The triangle**: `1 ⋆ 1 = (1 − |η|)₊`. -/
theorem tri_apply (η : ℝ) : tri η = (triR η : ℂ) := by
  set a : ℝ := max (-(1 / 2)) (η - 1 / 2)
  set b : ℝ := min (1 / 2) (η + 1 / 2)
  have key : ∀ t : ℝ, (t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) ∧
      η - t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) ↔ t ∈ Set.Icc a b := fun t => by
    simp only [Set.mem_Icc, a, b, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, by linarith, by linarith⟩
  have hpt : (fun t => (ContinuousLinearMap.mul ℂ ℂ) (ind t) (ind (η - t))) =
      (Set.Icc a b).indicator fun _ => (1 : ℂ) := by
    funext t
    rw [ContinuousLinearMap.mul_apply', ind_apply, ind_apply, Set.indicator_apply]
    by_cases hm : t ∈ Set.Icc a b
    · obtain ⟨h1, h2⟩ := (key t).mpr hm
      rw [if_pos h1, if_pos h2, if_pos hm, one_mul]
    · rw [if_neg hm]
      by_cases h1 : t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
      · rw [if_pos h1, if_neg (fun h2 => hm ((key t).mp ⟨h1, h2⟩)), mul_zero]
      · rw [if_neg h1, zero_mul]
  rw [tri, convolution_def, hpt, integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc, Complex.real_smul, mul_one]
  congr 1
  rw [triR]
  rcases le_or_gt 0 η with hη | hη
  · rw [abs_of_nonneg hη]
    have ha : a = η - 1 / 2 := max_eq_right (by linarith)
    have hb : b = 1 / 2 := min_eq_left (by linarith)
    rw [ha, hb]; ring_nf
  · rw [abs_of_neg hη]
    have ha : a = -(1 / 2) := max_eq_left (by linarith)
    have hb : b = η + 1 / 2 := min_eq_right (by linarith)
    rw [ha, hb]; ring_nf

theorem integrable_tri : Integrable tri := integrable_ind.integrable_convolution _ integrable_ind

theorem integrable_quad : Integrable quad := integrable_tri.integrable_convolution _ integrable_ind

/-- `S² = 𝓕 Δ`. -/
theorem fourier_tri (x : ℝ) : 𝓕 tri x = (sk x : ℂ) ^ 2 := by
  rw [tri, Real.fourier_mul_convolution_eq integrable_ind integrable_ind, fourier_ind, sq]

/-- `S³ = 𝓕 (Δ ⋆ 1)`. -/
theorem fourier_quad (x : ℝ) : 𝓕 quad x = (sk x : ℂ) ^ 3 := by
  rw [quad, Real.fourier_mul_convolution_eq integrable_tri integrable_ind, fourier_tri,
    fourier_ind]; ring

theorem norm_tri_le (η : ℝ) : ‖tri η‖ ≤ 1 := by
  rw [tri_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (triR_nonneg η)]
  exact triR_le_one η

theorem norm_quad_le (x : ℝ) : ‖quad x‖ ≤ 1 := by
  rw [quad, convolution_def]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ t, ‖(ContinuousLinearMap.mul ℂ ℂ) (tri t) (ind (x - t))‖
      ≤ ∫ t, triR t := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          ?_ (Filter.Eventually.of_forall fun t => ?_)
        · have := integral_triR_pow_succ 0
          by_contra hni
          rw [integral_undef (by simpa using hni)] at this
          norm_num at this
        · simp only [ContinuousLinearMap.mul_apply', norm_mul]
          rw [tri_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (triR_nonneg t)]
          exact mul_le_of_le_one_right (triR_nonneg t) (norm_ind_le _)
    _ = 1 := by simpa using integral_triR_pow_succ 0

/-- An integrable function bounded by `1` is square integrable. -/
theorem memLp_two_of_norm_le_one {f : ℝ → ℂ} (hf : Integrable f) (hb : ∀ x, ‖f x‖ ≤ 1) :
    MemLp f 2 := by
  refine (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr ?_
  refine Integrable.mono' hf.norm (hf.aestronglyMeasurable.norm.pow 2) ?_
  refine Filter.Eventually.of_forall fun η => ?_
  have h := hb η
  have h0 := norm_nonneg (f η)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

theorem memLp_two_tri : MemLp tri 2 := memLp_two_of_norm_le_one integrable_tri norm_tri_le

theorem memLp_two_quad : MemLp quad 2 := memLp_two_of_norm_le_one integrable_quad norm_quad_le

/-! ### Real pairings through Parseval -/

/-- The pairing `conj(𝓕F) 𝓕G` of two `L¹ ∩ L²` transforms is integrable (`|ab| ≤ (|a|² + |b|²)/2`). -/
theorem integrable_conj_fourier_mul_fourier {F G : ℝ → ℂ} (hF1 : Integrable F) (hF2 : MemLp F 2)
    (hG1 : Integrable G) (hG2 : MemLp G 2) :
    Integrable fun y => conj (𝓕 F y) * 𝓕 G y := by
  have hb : Integrable (fun y => (‖𝓕 F y‖ ^ (2 : ℕ) + ‖𝓕 G y‖ ^ (2 : ℕ)) / 2) :=
    ((GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hF1 hF2).add
      (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hG1 hG2)).div_const 2
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((Complex.continuous_conj.comp
      (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hF1)).mul
      (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hG1)).aestronglyMeasurable
  · rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖𝓕 F y‖ - ‖𝓕 G y‖)]

/-- **Real Parseval pairing**: if `𝓕F = f` and `𝓕G = g` are real, then `fg` is integrable and
`∫ fg = ∫ conj(F) G`. -/
theorem integral_mul_eq_of_fourier {F G : ℝ → ℂ} {f g : ℝ → ℝ} (hF1 : Integrable F)
    (hF2 : MemLp F 2) (hG1 : Integrable G) (hG2 : MemLp G 2) (hf : ∀ y, 𝓕 F y = f y)
    (hg : ∀ y, 𝓕 G y = g y) :
    Integrable (fun y => f y * g y) ∧ ((∫ y, f y * g y : ℝ) : ℂ) = ∫ η, conj (F η) * G η := by
  have e : (fun y => conj (𝓕 F y) * 𝓕 G y) = fun y => ((f y * g y : ℝ) : ℂ) := by
    funext y; rw [hf, hg, Complex.conj_ofReal]; push_cast; ring
  have hi := integrable_conj_fourier_mul_fourier hF1 hF2 hG1 hG2
  rw [e] at hi
  refine ⟨by simpa using hi.re, ?_⟩
  rw [← integral_complex_ofReal, ← integral_conj_fourier_mul_fourier hF1 hF2 hG1 hG2, e]

/-- Pairing against a modulated function is a Fourier transform:
`∫ conj(G e_x) F = 𝓕(conj(G) F)(x)`. -/
theorem integral_conj_mul_ex (G F : ℝ → ℂ) (x : ℝ) :
    ∫ η, conj (G η * ex x η) * F η = 𝓕 (fun η => conj (G η) * F η) x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1
  funext η
  rw [map_mul, ex, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, smul_eq_mul,
    show ((2 * Real.pi * η * x : ℝ) : ℂ) * -Complex.I =
      ((-2 * Real.pi * η * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  ring

theorem conj_ind (η : ℝ) : conj (ind η) = ind η := by
  rw [ind_apply]; split_ifs <;> simp

theorem ind_mul_ind (η : ℝ) : ind η * ind η = ind η := by
  rw [ind_apply]; split_ifs <;> simp

theorem conj_tri (η : ℝ) : conj (tri η) = tri η := by
  rw [tri_apply, Complex.conj_ofReal]

theorem integral_ind : ∫ η, ind η = 1 := by
  have h := fourier_ind 0
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  simpa [sk] using h

theorem integral_tri_pow_succ (k : ℕ) : ∫ η, tri η ^ (k + 1) = ((2 / (k + 2) : ℝ) : ℂ) := by
  simp_rw [tri_apply, ← Complex.ofReal_pow]
  rw [integral_complex_ofReal, integral_triR_pow_succ]

theorem fourier_tri' (y : ℝ) : 𝓕 tri y = ((sk y ^ 2 : ℝ) : ℂ) := by
  rw [fourier_tri]; push_cast; rfl

theorem fourier_quad' (y : ℝ) : 𝓕 quad y = ((sk y ^ 3 : ℝ) : ℂ) := by
  rw [fourier_quad]; push_cast; rfl

theorem fourier_ind_mul_ex (x y : ℝ) : 𝓕 (fun η => ind η * ex x η) y = (sk (x - y) : ℂ) := by
  rw [fourier_mul_ex, fourier_ind, ← sk_neg, neg_sub]

theorem fourier_tri_mul_ex (x y : ℝ) :
    𝓕 (fun η => tri η * ex x η) y = ((sk (x - y) ^ 2 : ℝ) : ℂ) := by
  rw [fourier_mul_ex, fourier_tri', ← sk_neg, neg_sub]

theorem integrable_ind_mul_quad : Integrable fun η => ind η * quad η :=
  integrable_ind.mul_bdd (c := 1) integrable_quad.aestronglyMeasurable
    (Filter.Eventually.of_forall norm_quad_le)

theorem integrable_tri_mul_tri : Integrable fun η => tri η * tri η :=
  integrable_tri.mul_bdd (c := 1) integrable_tri.aestronglyMeasurable
    (Filter.Eventually.of_forall norm_tri_le)

theorem memLp_two_ind_mul_quad : MemLp (fun η => ind η * quad η) 2 :=
  memLp_two_of_norm_le_one integrable_ind_mul_quad fun η => by
    rw [norm_mul]; exact mul_le_one₀ (norm_ind_le η) (norm_nonneg _) (norm_quad_le η)

theorem memLp_two_tri_mul_tri : MemLp (fun η => tri η * tri η) 2 :=
  memLp_two_of_norm_le_one integrable_tri_mul_tri fun η => by
    rw [norm_mul]; exact mul_le_one₀ (norm_tri_le η) (norm_nonneg _) (norm_tri_le η)

/-! ### The one- and two-variable integrals -/

/-- `∫ S² = 1`. -/
theorem integral_sk_sq : Integrable (fun x => sk x ^ 2) ∧ ∫ x, sk x ^ 2 = 1 := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier integrable_ind memLp_two_ind integrable_ind
    memLp_two_ind fourier_ind fourier_ind
  simp_rw [conj_ind, ind_mul_ind, integral_ind] at he
  simp_rw [sq]
  exact ⟨hi, by exact_mod_cast he⟩

/-- `∫ S⁴ = ∫ Δ² = 2/3`. -/
theorem integral_sk_pow_four : Integrable (fun x => sk x ^ 4) ∧ ∫ x, sk x ^ 4 = 2 / 3 := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier integrable_tri memLp_two_tri integrable_tri
    memLp_two_tri fourier_tri' fourier_tri'
  simp_rw [conj_tri, ← sq, integral_tri_pow_succ 1] at he
  have e : (fun x => sk x ^ 4) = fun x => sk x ^ 2 * sk x ^ 2 := funext fun x => by ring
  rw [e]
  refine ⟨hi, ?_⟩
  have := Complex.ofReal_inj.mp he
  simp_rw [← sq]
  rw [this]; norm_num

/-- `∫ 1·(Δ ⋆ 1) = ∫ S · S³ = 2/3`. -/
theorem integral_ind_mul_quad : ∫ η, ind η * quad η = ((2 / 3 : ℝ) : ℂ) := by
  obtain ⟨-, he⟩ := integral_mul_eq_of_fourier integrable_ind memLp_two_ind integrable_quad
    memLp_two_quad fourier_ind fourier_quad'
  simp_rw [conj_ind] at he
  rw [← he, ← integral_sk_pow_four.2]
  congr 2
  funext x; ring

/-- **The projection identity** `∫ S(x − y) S(y) dy = S(x)`. -/
theorem integral_sk_sub_mul_sk (x : ℝ) :
    Integrable (fun y => sk (x - y) * sk y) ∧ ∫ y, sk (x - y) * sk y = sk x := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier (integrable_mul_ex integrable_ind x)
    (memLp_two_mul_ex memLp_two_ind x) integrable_ind memLp_two_ind (fourier_ind_mul_ex x)
    fourier_ind
  rw [integral_conj_mul_ex] at he
  simp_rw [conj_ind, ind_mul_ind, fourier_ind] at he
  exact ⟨hi, by exact_mod_cast he⟩

/-- `A(x) = ∫ S(x − y) S(y)³ dy`, the transform of `1·(Δ ⋆ 1)`. -/
def sA (x : ℝ) : ℝ := ∫ y, sk (x - y) * sk y ^ 3

/-- `B(x) = ∫ S(x − y)² S(y)² dy`, the transform of `Δ²`. -/
def sB (x : ℝ) : ℝ := ∫ y, sk (x - y) ^ 2 * sk y ^ 2

theorem integrable_sA_integrand (x : ℝ) : Integrable fun y => sk (x - y) * sk y ^ 3 :=
  (integral_mul_eq_of_fourier (integrable_mul_ex integrable_ind x)
    (memLp_two_mul_ex memLp_two_ind x) integrable_quad memLp_two_quad (fourier_ind_mul_ex x)
    fourier_quad').1

theorem fourier_ind_mul_quad (x : ℝ) : 𝓕 (fun η => ind η * quad η) x = (sA x : ℂ) := by
  obtain ⟨-, he⟩ := integral_mul_eq_of_fourier (integrable_mul_ex integrable_ind x)
    (memLp_two_mul_ex memLp_two_ind x) integrable_quad memLp_two_quad (fourier_ind_mul_ex x)
    fourier_quad'
  rw [integral_conj_mul_ex] at he
  simp_rw [conj_ind] at he
  rw [sA, he]

theorem integrable_sB_integrand (x : ℝ) : Integrable fun y => sk (x - y) ^ 2 * sk y ^ 2 :=
  (integral_mul_eq_of_fourier (integrable_mul_ex integrable_tri x)
    (memLp_two_mul_ex memLp_two_tri x) integrable_tri memLp_two_tri (fourier_tri_mul_ex x)
    fourier_tri').1

theorem fourier_tri_mul_tri (x : ℝ) : 𝓕 (fun η => tri η * tri η) x = (sB x : ℂ) := by
  obtain ⟨-, he⟩ := integral_mul_eq_of_fourier (integrable_mul_ex integrable_tri x)
    (memLp_two_mul_ex memLp_two_tri x) integrable_tri memLp_two_tri (fourier_tri_mul_ex x)
    fourier_tri'
  rw [integral_conj_mul_ex] at he
  simp_rw [conj_tri] at he
  rw [sB, he]

/-- The reflected cubic term equals `A`: substitute `y ↦ x − y`. -/
theorem integral_sk_mul_sk_sub_cube (x : ℝ) :
    Integrable (fun y => sk y * sk (x - y) ^ 3) ∧ ∫ y, sk y * sk (x - y) ^ 3 = sA x := by
  have e : (fun y => sk y * sk (x - y) ^ 3) = fun y => sk (x - (x - y)) * sk (x - y) ^ 3 :=
    funext fun y => by rw [sub_sub_cancel]
  rw [e]
  exact ⟨(integrable_sA_integrand x).comp_sub_left x,
    integral_sub_left_eq_self (fun y => sk (x - y) * sk y ^ 3) volume x⟩

/-- `∫ S · A = ∫ 1·(Δ ⋆ 1) = 2/3`. -/
theorem integral_sk_mul_sA : Integrable (fun x => sk x * sA x) ∧ ∫ x, sk x * sA x = 2 / 3 := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier integrable_ind memLp_two_ind
    integrable_ind_mul_quad memLp_two_ind_mul_quad fourier_ind fourier_ind_mul_quad
  simp_rw [conj_ind, ← mul_assoc, ind_mul_ind, integral_ind_mul_quad] at he
  exact ⟨hi, by exact_mod_cast he⟩

/-- `∫ S² · B = ∫ Δ³ = 1/2`. -/
theorem integral_sk_sq_mul_sB :
    Integrable (fun x => sk x ^ 2 * sB x) ∧ ∫ x, sk x ^ 2 * sB x = 1 / 2 := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier integrable_tri memLp_two_tri
    integrable_tri_mul_tri memLp_two_tri_mul_tri fourier_tri' fourier_tri_mul_tri
  simp_rw [conj_tri, ← mul_assoc, show ∀ η, tri η * tri η * tri η = tri η ^ (2 + 1) from
    fun η => by ring, integral_tri_pow_succ 2] at he
  refine ⟨hi, ?_⟩
  rw [Complex.ofReal_inj.mp he]; norm_num

/-! ### The moments -/

/-- The pair term `∫ S² ρ₂`, `ρ₂ = 1 − S²`. -/
def sinePair : ℝ := ∫ x, sk x ^ 2 * (1 - sk x ^ 2)

/-- The fully distinct triple term `∬ S(x) S(y) S(x − y) ρ₃(0, x, y)`. -/
def sineTriple : ℝ :=
  ∫ x, ∫ y, sk x * sk y * sk (x - y) *
    (1 - sk x ^ 2 - sk y ^ 2 - sk (x - y) ^ 2 + 2 * sk x * sk y * sk (x - y))

/-- The second sine-kernel Gram moment per point. -/
def sineKappa₂ : ℝ := 1 + sinePair

/-- The third sine-kernel Gram moment per point: diagonal, three pair coincidences, triples. -/
def sineKappa₃ : ℝ := 1 + 3 * sinePair + sineTriple

theorem sinePair_eq : sinePair = 1 / 3 := by
  have e : (fun x => sk x ^ 2 * (1 - sk x ^ 2)) = fun x => sk x ^ 2 - sk x ^ 4 :=
    funext fun x => by ring
  rw [sinePair, e, integral_sub integral_sk_sq.1 integral_sk_pow_four.1, integral_sk_sq.2,
    integral_sk_pow_four.2]
  norm_num

/-- The inner triple integral is `S²(1 − S²) − 2 S A + 2 S² B`. -/
theorem integral_triple_inner (x : ℝ) :
    ∫ y, sk x * sk y * sk (x - y) *
      (1 - sk x ^ 2 - sk y ^ 2 - sk (x - y) ^ 2 + 2 * sk x * sk y * sk (x - y)) =
    sk x ^ 2 * (1 - sk x ^ 2) - 2 * (sk x * sA x) + 2 * (sk x ^ 2 * sB x) := by
  have e : (fun y => sk x * sk y * sk (x - y) *
      (1 - sk x ^ 2 - sk y ^ 2 - sk (x - y) ^ 2 + 2 * sk x * sk y * sk (x - y))) =
      fun y => sk x * (1 - sk x ^ 2) * (sk (x - y) * sk y) - sk x * (sk (x - y) * sk y ^ 3) -
        sk x * (sk y * sk (x - y) ^ 3) + 2 * sk x ^ 2 * (sk (x - y) ^ 2 * sk y ^ 2) :=
    funext fun y => by ring
  obtain ⟨h1, e1⟩ := integral_sk_sub_mul_sk x
  obtain ⟨h3, e3⟩ := integral_sk_mul_sk_sub_cube x
  have h2 := integrable_sA_integrand x
  have h4 := integrable_sB_integrand x
  rw [e, integral_add ?_ (h4.const_mul _), integral_sub ?_ (h3.const_mul _),
    integral_sub (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, e1, e3,
    show ∫ y, sk (x - y) * sk y ^ 3 = sA x from rfl,
    show ∫ y, sk (x - y) ^ 2 * sk y ^ 2 = sB x from rfl]
  · ring
  all_goals first
    | exact (h1.const_mul _).sub (h2.const_mul _)
    | exact ((h1.const_mul _).sub (h2.const_mul _)).sub (h3.const_mul _)

/-- **The fully distinct triple term vanishes.** -/
theorem sineTriple_eq_zero : sineTriple = 0 := by
  have hp : Integrable fun x => sk x ^ 2 * (1 - sk x ^ 2) := by
    have e : (fun x => sk x ^ 2 * (1 - sk x ^ 2)) = fun x => sk x ^ 2 - sk x ^ 4 :=
      funext fun x => by ring
    rw [e]; exact integral_sk_sq.1.sub integral_sk_pow_four.1
  obtain ⟨hA, eA⟩ := integral_sk_mul_sA
  obtain ⟨hB, eB⟩ := integral_sk_sq_mul_sB
  rw [sineTriple]
  simp_rw [integral_triple_inner]
  rw [integral_add ?_ (hB.const_mul _), integral_sub hp (hA.const_mul _),
    integral_const_mul, integral_const_mul, eA, eB, ← sinePair, sinePair_eq]
  · norm_num
  · exact hp.sub (hA.const_mul _)

/-- **`κ₂ = 4/3`.** -/
theorem sineKappa₂_eq : sineKappa₂ = 4 / 3 := by
  rw [sineKappa₂, sinePair_eq]; norm_num

/-- **`κ₃ = 2`.** -/
theorem sineKappa₃_eq : sineKappa₃ = 2 := by
  rw [sineKappa₃, sinePair_eq, sineTriple_eq_zero]; norm_num

/-! ### The blind spot -/

open Matrix in
/-- **The sine-kernel moments are the blind-spot moments.** Per counted zero, `diag(1,1,1,1,2)`
(six zeros) has `tr Ĥ² / 6 = κ₂` and `tr Ĥ³ / 6 = κ₃`. -/
theorem sineMoments_eq_blindSpot :
    sineKappa₂ * 6 =
      (((diagonal fun i : HigherInertia.BlindIdx => (HigherInertia.blindVal i : ℂ)) ^ 2).trace).re ∧
    sineKappa₃ * 6 =
      (((diagonal fun i : HigherInertia.BlindIdx => (HigherInertia.blindVal i : ℂ)) ^ 3).trace).re := by
  rw [HigherInertia.blindSpot_moments, HigherInertia.blindSpot_moments, sineKappa₂_eq,
    sineKappa₃_eq]
  norm_num

/-- **Sine-kernel statistics through third order certify at most `2/3`.** Every cubic inertia
certificate valid on the blind spot has value at most `2/3` at the sine-kernel moments `(κ₂, κ₃)`. -/
theorem cubic_sineValue_le_two_thirds (c₁ c₂ c₃ : ℝ)
    (hvalid : ∑ i, (c₁ * HigherInertia.blindSpot_isHermitian.eigenvalues₀ i +
      c₂ * HigherInertia.blindSpot_isHermitian.eigenvalues₀ i ^ 2 +
        c₃ * HigherInertia.blindSpot_isHermitian.eigenvalues₀ i ^ 3) ≤ Fintype.card (Fin 4)) :
    c₁ + c₂ * sineKappa₂ + c₃ * sineKappa₃ ≤ 2 / 3 := by
  rw [sineKappa₂_eq, sineKappa₃_eq]
  exact HigherInertia.cubic_value_le_two_thirds c₁ c₂ c₃ hvalid

/-- At the sine-kernel `(κ₂, κ₃)` the certificate `q⋆` has value `(64/49)(23/6 − κ₄)`, and reaches
`3/4` exactly when `κ₄ ≤ 2503/768`. -/
theorem qStarValue_sineKappa (κ₄ : ℝ) :
    HigherInertia.qStarValue sineKappa₂ sineKappa₃ κ₄ = 64 / 49 * (23 / 6 - κ₄) ∧
      (3 / 4 ≤ HigherInertia.qStarValue sineKappa₂ sineKappa₃ κ₄ ↔ κ₄ ≤ 2503 / 768) := by
  rw [sineKappa₂_eq, sineKappa₃_eq]
  exact ⟨HigherInertia.qStarValue_sine_two κ₄, HigherInertia.three_quarters_le_qStarValue_iff κ₄⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SineKernel
