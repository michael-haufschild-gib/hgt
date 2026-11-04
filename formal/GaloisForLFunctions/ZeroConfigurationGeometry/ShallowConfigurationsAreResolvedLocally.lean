import GaloisForLFunctions.ZeroConfigurationGeometry.ShallowConfigurationsAreResolvedAtTheInghamScale

/-!
# Shallow configurations are resolved locally

`ShallowConfigurationsAreResolvedAtTheInghamScale` resolves configurations that are shallow and
separated at the Ingham scale `g > π/(2a)` everywhere. For `ζ` such hypotheses can only hold near
one height at a time. This module localizes the resolution at a height `X`. Only the cluster within
distance `R` of `X` has to be shallow and separated, and the rest enters as an explicit error.

* **Nearly vanishing pair sums** (`inghamConst_mul_normSq_le_of_small`). If a pair sum over
  separated shallow sites has modulus `≤ ε` on `[−V, V]`, every centre satisfies
  `θ |p_k + q_k|² ≤ 2K Σ_j (|p_j| + |q_j|)² + 4Vε²`. The case `ε = 0` is
  `inghamConst_mul_normSq_le`.
* **The camera at a site** (`norm_siteP_add_norm_siteQ_le`,
  `norm_multDiff_mul_shallowFloor_sq_le`). Modulated to height `γ₀`, the bump `κ_w` sees a site of
  depth `≤ ½` at height `γ` with weight `≤ 2|c| C_w²/(1 + |γ − γ₀|)⁸`. It sees its own site of
  depth `≤ s` with centre `≥ |c| r(w, s)²`.
* **Local resolution** (`norm_multDiff_sq_le_of_locally_shallow`). Let `Z, Z'` be tempered mimics at
  aperture `a ≥ V/2 + w` whose points lie in the strip. Suppose their points with height in
  `[X − R, X + R]` are `s`-shallow and `g`-separated apart from FE partners, with `g > π/V` and
  `2K T_loc < θ r⁴`. Then every `z` with `|Im z − X| ≤ R` satisfies
  `|m_Z(z) − m_{Z'}(z)|² ≤ C (1 + |Im z − X|)^{14} (1 + |X|)⁴ S² / (1 + R/2)^{10}`,
  where `S = Σ_ρ |m_Z(ρ) − m_{Z'}(ρ)|/(1 + |γ_ρ|²)` and `C = localShallowConst V w g s`.
* **The Ingham scale, locally** (`exists_local_resolution_at_ingham_scale`,
  `eq_of_locally_shallow_at_ingham_scale`). For every `g > π/(2a)` there are a depth `s₀ > 0` and a
  constant `C` with the bound above for all such mimics, heights and radii. In particular the
  multiplicities agree at `z` once `(1 + R/2)^{10} > C (1 + |Im z − X|)^{14} (1 + |X|)⁴ S²`.

Proof. Maximize `|c_k|/(1 + |γ_k − X|)⁷` over the sites within `R` of `X`. At a maximal site `k₀`
the camera modulated to `γ₀ = Im k₀` makes the full pair sum vanish, so the near pair sum equals
minus the far one. The far one is at most `e^{V/2} W_far`. The near sites are dominated:
`|c_k| ≤ |c₀| (1 + |γ_k − γ₀|)⁷`, and against the bump decay `(1 + |γ_k − γ₀|)^{−8}` their squared
weights sum to `T_loc |c₀|²` over the separated heights. This gives `(θ r⁴ − 2K T_loc) |c₀|² ≤
4V e^V W_far²`. A far site is at height distance `≥ R − d₀` from `γ₀`, `d₀ = |γ₀ − X|`, so
`W_far ≤ (5/2) C_w² (1 + |X|)² (1 + d₀)² S/(1 + R − d₀)⁶`. Maximality transfers the bound to `z` at
the cost `((1 + |Im z − X|)/(1 + d₀))^{14}`, and `(1 + d₀)^{10} (1 + R − d₀)^{12} ≥ (1 + R/2)^{10}`
for every `d₀ ∈ [0, R]`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open SquareRootThreshold Zeta23

/-! ### Nearly vanishing pair sums -/

/-- **Centres of a nearly vanishing pair sum.** If a summable pair sum has modulus `≤ ε` on
`[−V, V]`, with `g`-separated heights, depths `≤ s` and `g > π/V`, every centre satisfies
`θ |p_k + q_k|² ≤ 2K(V, g, s) Σ_j (|p_j| + |q_j|)² + 4Vε²`. -/
theorem inghamConst_mul_normSq_le_of_small {κ : Type*} (γ δ : κ → ℝ) (p q : κ → ℂ)
    {g V s ε : ℝ} (hg : 0 < g) (hV : 0 < V) (hs : 0 ≤ s) (hδ : ∀ k, |δ k| ≤ s)
    (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) (hgap : π / V < g)
    (hsum : Summable fun k => ‖p k‖ + ‖q k‖)
    (hsmall : ∀ v ∈ Icc (-V) V, ‖∑' k, cexp (I * γ k * v) *
      (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v))‖ ≤ ε) (k₀ : κ) :
    tiltedInghamConst V g 0 * ‖p k₀ + q k₀‖ ^ 2 ≤
      2 * remConst V g s * ∑' k, (‖p k‖ + ‖q k‖) ^ 2 + 4 * V * ε ^ 2 := by
  classical
  set w : κ → ℝ := fun k => ‖p k‖ + ‖q k‖ with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by positivity
  have hw2 : Summable fun k => w k ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
      (hsum.mul_left (∑' j, w j))
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hsum.le_tsum k fun j _ => hw0 j) (hw0 k)
  have hθ0 := (inghamConst_pos hV hgap).le
  have hK0 := remConst_nonneg (g := g) hV hs
  set E := Real.exp (s * V) with hE
  -- the term of a site and its bound
  set T : κ → ℝ → ℂ := fun k v => cexp (I * γ k * v) *
    (p k * cexp ((δ k : ℂ) * v) + q k * cexp (-(δ k : ℂ) * v)) with hT
  have hTb : ∀ k, ∀ v ∈ Icc (-V) V, ‖T k v‖ ≤ E * w k := by
    intro k v hv
    have hvV : |v| ≤ V := abs_le.mpr hv
    have hδv : ∀ σ : ℝ, |σ| ≤ s → ‖cexp ((σ : ℂ) * v)‖ ≤ E := fun σ hσ => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
        rw [abs_mul]; exact mul_le_mul hσ hvV (abs_nonneg _) hs))
    have h1 : ‖cexp (I * γ k * v)‖ = 1 := by
      rw [show I * (γ k : ℂ) * v = ((γ k * v : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hneg : -(δ k : ℂ) * v = ((-δ k : ℝ) : ℂ) * v := by push_cast; ring
    simp only [hT]
    rw [norm_mul, h1, one_mul, hneg]
    calc ‖p k * cexp ((δ k : ℂ) * v) + q k * cexp (((-δ k : ℝ) : ℂ) * v)‖ ≤
        ‖p k‖ * E + ‖q k‖ * E := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
          · exact mul_le_mul_of_nonneg_left (hδv _ (hδ k)) (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hδv _ (by rw [abs_neg]; exact hδ k)) (norm_nonneg _)
      _ = E * w k := by rw [hw]; ring
  -- the tail of the sum
  set τ : Finset κ → ℝ := fun S => ∑' k : {k // k ∉ S}, w k with hτ
  have hτlim : Tendsto τ atTop (𝓝 0) := tendsto_tsum_compl_atTop_zero w
  have hfin : ∀ S : Finset κ, k₀ ∈ S → tiltedInghamConst V g 0 * ‖p k₀ + q k₀‖ ^ 2 ≤
      2 * remConst V g s * ∑' k, w k ^ 2 + 2 * (2 * V * (ε + E * τ S) ^ 2) := by
    intro S hk₀
    set M : ℝ → ℂ := fun v => ∑ k : S, (p k + q k) * cexp (I * γ k * v) with hM
    set R : ℝ → ℂ := fun v => ∑ k : S, cexp (I * γ k * v) *
      (p k * (remProfile (δ k) true v : ℂ) + q k * (remProfile (δ k) false v : ℂ)) with hR
    set F : ℝ → ℂ := fun v => ∑ k : S, T k v with hF
    have hMRF : ∀ v, M v = F v - R v := by
      intro v
      simp only [hM, hR, hF, hT]
      rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pair_eq_centre_add_rem]
      ring
    have hMc : Continuous M := by rw [hM]; fun_prop
    have hRc : Continuous R := by
      rw [hR]
      have : ∀ k : S, ∀ b, Continuous (remProfile (δ k) b) := fun k b => continuous_remProfile _ _
      fun_prop
    have hFc : Continuous F := by rw [hF, hT]; fun_prop
    have hsepS : ∀ j l : S, j ≠ l → g ≤ |γ j - γ l| := fun j l hjl =>
      hsep j l fun h => hjl (Subtype.ext h)
    have hlow := ingham_lower (fun k : S => γ k) (fun k : S => p k + q k) hg hV hsepS hgap
    have hδS : ∀ k : S, |δ k| ≤ s := fun k => hδ k
    have hup := remainder_upper (fun k : S => γ k) (fun k : S => δ k) (fun k : S => p k)
      (fun k : S => q k) hg hV hs hδS hsepS
    -- the truncated pair sum is the full sum minus the tail
    have hFb : ∀ v ∈ Icc (-V) V, ‖F v‖ ≤ ε + E * τ S := by
      intro v hv
      have hTs : Summable fun k => T k v :=
        Summable.of_norm_bounded (hsum.mul_left E) fun k => hTb k v hv
      have hsplit := hTs.sum_add_tsum_subtype_compl S
      have hFeq : F v = (∑' k, T k v) - ∑' k : {k // k ∉ S}, T k v := by
        simp only [hF]
        rw [Finset.sum_coe_sort S (fun k => T k v)]
        linear_combination hsplit
      rw [hFeq]
      refine (norm_sub_le _ _).trans (add_le_add (hsmall v hv) ?_)
      have hws : Summable fun k : {k // k ∉ S} => w k := hsum.subtype _
      refine (norm_tsum_le_tsum_norm ((hws.mul_left E).of_norm_bounded fun k => ?_)).trans ?_
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hTb k v hv
      · rw [hτ, ← tsum_mul_left]
        exact (Summable.of_norm_bounded (hws.mul_left E) fun k => hTb k v hv).norm.tsum_le_tsum
          (fun k => hTb k v hv) (hws.mul_left E)
    have hFint : ∫ v in -V..V, ‖F v‖ ^ 2 ≤ 2 * V * (ε + E * τ S) ^ 2 := by
      calc ∫ v in -V..V, ‖F v‖ ^ 2 ≤ ∫ v in -V..V, (ε + E * τ S) ^ 2 :=
            intervalIntegral.integral_mono_on (by linarith)
              ((hFc.norm.pow 2).intervalIntegrable _ _) intervalIntegrable_const fun v hv =>
                pow_le_pow_left₀ (norm_nonneg _) (hFb v hv) 2
        _ = 2 * V * (ε + E * τ S) ^ 2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hpt : ∀ v, ‖M v‖ ^ 2 ≤ 2 * ‖R v‖ ^ 2 + 2 * ‖F v‖ ^ 2 := by
      intro v
      rw [hMRF v]
      have h := norm_sub_le (F v) (R v)
      nlinarith [norm_nonneg (F v - R v), norm_nonneg (F v), norm_nonneg (R v),
        sq_nonneg (‖F v‖ - ‖R v‖)]
    have hMint : ∫ v in -V..V, ‖M v‖ ^ 2 ≤
        2 * (∫ v in -V..V, ‖R v‖ ^ 2) + 2 * ∫ v in -V..V, ‖F v‖ ^ 2 := by
      calc ∫ v in -V..V, ‖M v‖ ^ 2 ≤ ∫ v in -V..V, (2 * ‖R v‖ ^ 2 + 2 * ‖F v‖ ^ 2) :=
            intervalIntegral.integral_mono_on (by linarith)
              ((hMc.norm.pow 2).intervalIntegrable _ _)
              ((((hRc.norm.pow 2).const_mul 2).add
                ((hFc.norm.pow 2).const_mul 2)).intervalIntegrable _ _) fun v _ => hpt v
        _ = 2 * (∫ v in -V..V, ‖R v‖ ^ 2) + 2 * ∫ v in -V..V, ‖F v‖ ^ 2 := by
            have hR2 : Continuous fun v => 2 * ‖R v‖ ^ 2 := continuous_const.mul (hRc.norm.pow 2)
            have hF2 : Continuous fun v => 2 * ‖F v‖ ^ 2 := continuous_const.mul (hFc.norm.pow 2)
            rw [intervalIntegral.integral_add (hR2.intervalIntegrable _ _)
              (hF2.intervalIntegrable _ _),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hsumS : ∑ k : S, (‖p k‖ + ‖q k‖) ^ 2 ≤ ∑' k, w k ^ 2 := by
      rw [Finset.sum_coe_sort S (fun k => (‖p k‖ + ‖q k‖) ^ 2)]
      exact hw2.sum_le_tsum S fun k _ => sq_nonneg _
    have hk : ‖p k₀ + q k₀‖ ^ 2 ≤ ∑ k : S, ‖p k + q k‖ ^ 2 := by
      rw [Finset.sum_coe_sort S (fun k => ‖p k + q k‖ ^ 2)]
      exact Finset.single_le_sum (f := fun k => ‖p k + q k‖ ^ 2) (fun _ _ => by positivity) hk₀
    calc tiltedInghamConst V g 0 * ‖p k₀ + q k₀‖ ^ 2 ≤
        tiltedInghamConst V g 0 * ∑ k : S, ‖p k + q k‖ ^ 2 := mul_le_mul_of_nonneg_left hk hθ0
      _ ≤ ∫ v in -V..V, ‖M v‖ ^ 2 := hlow
      _ ≤ 2 * (∫ v in -V..V, ‖R v‖ ^ 2) + 2 * ∫ v in -V..V, ‖F v‖ ^ 2 := hMint
      _ ≤ 2 * (remConst V g s * ∑' k, w k ^ 2) + 2 * (2 * V * (ε + E * τ S) ^ 2) := by
          have hup' : ∫ v in -V..V, ‖R v‖ ^ 2 ≤ remConst V g s * ∑' k, w k ^ 2 :=
            (hup : ∫ v in -V..V, ‖R v‖ ^ 2 ≤ _).trans (mul_le_mul_of_nonneg_left hsumS hK0)
          linarith
      _ = 2 * remConst V g s * ∑' k, w k ^ 2 + 2 * (2 * V * (ε + E * τ S) ^ 2) := by ring
  have hlim : Tendsto (fun S => 2 * remConst V g s * ∑' k, w k ^ 2 +
      2 * (2 * V * (ε + E * τ S) ^ 2)) atTop
      (𝓝 (2 * remConst V g s * ∑' k, w k ^ 2 + 4 * V * ε ^ 2)) := by
    have h := (((((hτlim.const_mul E).const_add ε).pow 2).const_mul (2 * V)).const_mul 2).const_add
      (2 * remConst V g s * ∑' k, w k ^ 2)
    convert h using 2
    ring
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨{k₀}, fun S hS =>
    hfin S (hS (Finset.mem_singleton_self k₀))⟩)

/-! ### The camera at a site -/

/-- The decay constant `C_w = C_κ/(4w)³` of the scaled bump. -/
def localBumpConst (w : ℝ) : ℝ := _root_.RHTower.bumpDecayConst / (4 * w) ^ 3

theorem localBumpConst_nonneg {w : ℝ} (hw0 : 0 < w) : 0 ≤ localBumpConst w :=
  div_nonneg _root_.RHTower.bumpDecayConst_nonneg (by positivity)

/-- **The camera sees a far site faintly.** Modulated to `γ₀`, the bump sees a site of depth `≤ ½`
at height `γ` with weight `|p| + |q| ≤ 2|c| (C_w/(1 + |γ − γ₀|)⁴)²`. -/
theorem norm_siteP_add_norm_siteQ_le (Z Z' : ZeroConfig) {w : ℝ} (hw0 : 0 < w) (hw4 : 4 * w ≤ 1)
    (γ₀ : ℝ) (k : ℂ) (hk : |k.re - 1 / 2| ≤ 1 / 2) :
    ‖siteP Z Z' w γ₀ k‖ + ‖siteQ Z Z' w γ₀ k‖ ≤
      2 * ‖multDiff Z Z' k‖ * (localBumpConst w / (1 + |k.im - γ₀|) ^ 4) ^ 2 := by
  set κh := paperFT (_root_.RHTower.scaledBump w)
    (((k.im - γ₀ : ℝ) : ℂ) - I * ((k.re - 1 / 2 : ℝ) : ℂ)) with hκh
  have hp : siteP Z Z' w γ₀ k = multDiff Z Z' k * κh ^ 2 := by
    rw [siteP, pairWeight_modScaledBump_eq_sq]
  have hq : ‖siteQ Z Z' w γ₀ k‖ ≤ ‖multDiff Z Z' k‖ * ‖κh‖ ^ 2 := by
    unfold siteQ
    split_ifs
    · rw [norm_zero]; positivity
    · rw [norm_mul, Complex.norm_conj, multDiff_reflect, pairWeight_modScaledBump_eq_sq, norm_pow]
  have hκ : ‖κh‖ ≤ localBumpConst w / (1 + |k.im - γ₀|) ^ 4 := by
    have hz : |((((k.im - γ₀ : ℝ) : ℂ) - I * ((k.re - 1 / 2 : ℝ) : ℂ))).im| ≤ 1 / 2 := by
      have e : ((((k.im - γ₀ : ℝ) : ℂ) - I * ((k.re - 1 / 2 : ℝ) : ℂ))).im = -(k.re - 1 / 2) := by
        simp
      rw [e, abs_neg]
      exact hk
    have h := _root_.RHTower.norm_paperFT_scaledBump_le hw0 hw4 hz
    have hre : ((((k.im - γ₀ : ℝ) : ℂ) - I * ((k.re - 1 / 2 : ℝ) : ℂ))).re = k.im - γ₀ := by simp
    rw [hre] at h
    exact h.trans (le_of_eq (div_div _ _ _).symm)
  calc ‖siteP Z Z' w γ₀ k‖ + ‖siteQ Z Z' w γ₀ k‖ ≤ 2 * ‖multDiff Z Z' k‖ * ‖κh‖ ^ 2 := by
        rw [hp, norm_mul, norm_pow]; linarith
    _ ≤ 2 * ‖multDiff Z Z' k‖ * (localBumpConst w / (1 + |k.im - γ₀|) ^ 4) ^ 2 := by
        gcongr

/-- **The camera sees its own site.** Modulated to the height of a site of depth `≤ s`, the bump
sees it with centre `|p + q| ≥ |c| r(w, s)²`. -/
theorem norm_multDiff_mul_shallowFloor_sq_le (Z Z' : ZeroConfig) {w s : ℝ} (hw0 : 0 < w) (k : ℂ)
    (hk : |k.re - 1 / 2| ≤ s) :
    ‖multDiff Z Z' k‖ * shallowFloor w s ^ 2 ≤ ‖siteP Z Z' w k.im k + siteQ Z Z' w k.im k‖ := by
  set κ₀ := paperFT (_root_.RHTower.scaledBump w) (-(I * ((k.re - 1 / 2 : ℝ) : ℂ))) with hκ₀
  have hpw : _root_.RHTower.pairWeight (_root_.RHTower.modScaledBump w k.im) (k.re - 1 / 2) k.im =
      κ₀ ^ 2 := by
    rw [pairWeight_modScaledBump_eq_sq, sub_self, Complex.ofReal_zero, zero_sub]
  have hconj : conj κ₀ = κ₀ := by
    rw [hκ₀, conj_paperFT_scaledBump]
    rw [show conj (-(I * ((k.re - 1 / 2 : ℝ) : ℂ))) = I * ((k.re - 1 / 2 : ℝ) : ℂ) by
      rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring]
    rw [← paperFT_scaledBump_neg w (I * ((k.re - 1 / 2 : ℝ) : ℂ))]
  have hfloor : shallowFloor w s ≤ ‖κ₀‖ := by
    have h := _root_.RHTower.norm_paperFT_scaledBump_I_mul_ge hw0 (-(k.re - 1 / 2))
    rw [show ((-(k.re - 1 / 2) : ℝ) : ℂ) * I = -(I * ((k.re - 1 / 2 : ℝ) : ℂ)) by
      push_cast; ring, ← hκ₀, abs_neg] at h
    refine le_trans ?_ h
    have hint := _root_.RHTower.weilBump.integral_pos (μ := volume)
    unfold shallowFloor
    have : Real.exp (-(w * s)) ≤ Real.exp (-(w * |k.re - 1 / 2|)) :=
      Real.exp_le_exp.mpr (by nlinarith [hk])
    gcongr
  have hfl0 := (shallowFloor_pos hw0 s).le
  have hκn : ‖multDiff Z Z' k‖ * shallowFloor w s ^ 2 ≤ ‖multDiff Z Z' k‖ * ‖κ₀‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfl0 hfloor 2) (norm_nonneg _)
  refine hκn.trans ?_
  have hp : siteP Z Z' w k.im k = multDiff Z Z' k * κ₀ ^ 2 := by rw [siteP, hpw]
  rw [hp]
  unfold siteQ
  split_ifs
  · rw [add_zero, norm_mul, norm_pow]
  · rw [multDiff_reflect, hpw, map_pow, hconj, ← two_mul, norm_mul, norm_mul, norm_pow,
      Complex.norm_two]
    have := mul_nonneg (norm_nonneg (multDiff Z Z' k)) (sq_nonneg ‖κ₀‖)
    nlinarith

/-! ### Elementary comparisons -/

/-- `1 + |a − c| ≤ (1 + |b − c|)(1 + |a − b|)`. -/
theorem one_add_abs_sub_le_mul (a b c : ℝ) : 1 + |a - c| ≤ (1 + |b - c|) * (1 + |a - b|) := by
  have h : |a - c| ≤ |a - b| + |b - c| := by
    rw [show a - c = (a - b) + (b - c) by ring]
    exact abs_add_le _ _
  nlinarith [abs_nonneg (a - b), abs_nonneg (b - c),
    mul_nonneg (abs_nonneg (b - c)) (abs_nonneg (a - b))]

/-- In the strip, `1 + |γ_ρ|² ≤ (5/4)(1 + |X|)²(1 + |Im ρ − X|)²`. -/
theorem one_add_normSq_gammaOf_le {ρ : ℂ} (hρ : |ρ.re - 1 / 2| ≤ 1 / 2) (X : ℝ) :
    1 + Complex.normSq (gammaOf ρ) ≤ 5 / 4 * (1 + |X|) ^ 2 * (1 + |ρ.im - X|) ^ 2 := by
  rw [normSq_gammaOf]
  have h1 : (ρ.re - 1 / 2) ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hρ
    nlinarith
  have h2 := one_add_abs_sub_le_mul ρ.im X 0
  rw [sub_zero, sub_zero] at h2
  have h3 : (1 + |ρ.im|) ^ 2 ≤ ((1 + |X|) * (1 + |ρ.im - X|)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  have h4 : 1 + (ρ.re - 1 / 2) ^ 2 + ρ.im ^ 2 ≤ 5 / 4 * (1 + |ρ.im|) ^ 2 := by
    nlinarith [sq_abs ρ.im, abs_nonneg ρ.im]
  nlinarith

/-- `(1 + R/2)^{10} ≤ (1 + d)^{10} (1 + (R − d))^{12}` for `0 ≤ d ≤ R`. -/
theorem one_add_half_pow_le {d R : ℝ} (hd : 0 ≤ d) (hdR : d ≤ R) :
    (1 + R / 2) ^ 10 ≤ (1 + d) ^ 10 * (1 + (R - d)) ^ 12 := by
  have hRd : 0 ≤ R - d := by linarith
  rcases le_total (R / 2) d with h | h
  · have h1 : (1 + R / 2) ^ 10 ≤ (1 + d) ^ 10 := pow_le_pow_left₀ (by linarith) (by linarith) 10
    have h2 : 1 ≤ (1 + (R - d)) ^ 12 := one_le_pow₀ (by linarith)
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + d) 10]
  · have h1 : (1 + R / 2) ^ 10 ≤ (1 + (R - d)) ^ 10 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 10
    have h2 : (1 + (R - d)) ^ 10 ≤ (1 + (R - d)) ^ 12 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have h3 : 1 ≤ (1 + d) ^ 10 := one_le_pow₀ (by linarith)
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + (R - d)) 12]

/-- A nonnegative family decaying like `(1 + |γ_k − γ_j|)^{−2}` around one of `g`-separated
heights sums to at most `c(1 + π²/(3g²))`. -/
theorem tsum_le_of_decay_two {κ : Type*} (F : κ → ℝ) (hF0 : ∀ k, 0 ≤ F k) (γ : κ → ℝ) {g c : ℝ}
    (hg : 0 < g) (hc : 0 ≤ c) (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) (j : κ)
    (hF : ∀ k, F k ≤ c / (1 + |γ k - γ j|) ^ 2) :
    ∑' k, F k ≤ c * (1 + π ^ 2 / 3 / g ^ 2) := by
  classical
  refine Real.tsum_le_of_sum_le (fun k => hF0 k) fun S => ?_
  set S' := insert j S with hS'
  have hjS' : j ∈ S' := Finset.mem_insert_self j S
  set j₀ : S' := ⟨j, hjS'⟩ with hj₀
  set γS : S' → ℝ := fun x => γ x with hγS
  have hsepS : ∀ x y : S', x ≠ y → g ≤ |γS x - γS y| := fun x y hxy =>
    hsep x y fun h => hxy (Subtype.ext h)
  have hFj : F j ≤ c := by
    have h := hF j
    rwa [sub_self, abs_zero, add_zero, one_pow, div_one] at h
  have hFx : ∀ x ∈ Finset.univ.erase j₀, F x ≤ c * (1 / |γS j₀ - γS x| ^ 2) := by
    intro x hx
    have hne : x ≠ j₀ := Finset.ne_of_mem_erase hx
    have hd : |γS j₀ - γS x| = |γ x - γ j| := abs_sub_comm _ _
    have hpos : 0 < |γ x - γ j| := hd ▸ lt_of_lt_of_le hg (hsepS j₀ x (Ne.symm hne))
    have h2 : |γ x - γ j| ^ 2 ≤ (1 + |γ x - γ j|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
    calc F x ≤ c / (1 + |γ x - γ j|) ^ 2 := hF x
      _ ≤ c / |γ x - γ j| ^ 2 := div_le_div_of_nonneg_left hc (by positivity) h2
      _ = c * (1 / |γS j₀ - γS x| ^ 2) := by rw [hd, mul_one_div]
  have hrow := sum_inv_sq_sep_le_erase γS hg hsepS j₀
  calc ∑ k ∈ S, F k ≤ ∑ k ∈ S', F k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) (fun k _ _ => hF0 k)
    _ = ∑ x : S', F x := (Finset.sum_coe_sort S' F).symm
    _ = F j₀ + ∑ x ∈ Finset.univ.erase j₀, F x :=
        (Finset.add_sum_erase _ (fun x : S' => F x) (Finset.mem_univ j₀)).symm
    _ ≤ c + ∑ x ∈ Finset.univ.erase j₀, c * (1 / |γS j₀ - γS x| ^ 2) :=
        add_le_add hFj (Finset.sum_le_sum hFx)
    _ ≤ c + c * (π ^ 2 / 3 / g ^ 2) := by
        rw [← Finset.mul_sum]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hrow hc)
    _ = c * (1 + π ^ 2 / 3 / g ^ 2) := by ring

/-! ### Local resolution -/

/-- The local tail constant `T_loc(w, g) = 4 C_w⁴ (1 + π²/(3g²))`. -/
def localShallowTail (w g : ℝ) : ℝ := 4 * localBumpConst w ^ 4 * (1 + π ^ 2 / 3 / g ^ 2)

/-- The local constant `C = 25 V e^V C_w⁴/(θ r⁴ − 2K T_loc)`. -/
def localShallowConst (V w g s : ℝ) : ℝ :=
  25 * V * Real.exp V * localBumpConst w ^ 4 /
    (tiltedInghamConst V g 0 * shallowFloor w s ^ 4 - 2 * remConst V g s * localShallowTail w g)

theorem localShallowTail_le_shallowTail {w : ℝ} (hw0 : 0 < w) (g s : ℝ) :
    localShallowTail w g ≤ shallowTail w g s := by
  have hC := localBumpConst_nonneg hw0
  have h1 : 1 ≤ (1 + s ^ 2) ^ 2 := one_le_pow₀ (by nlinarith [sq_nonneg s])
  have h2 : 0 ≤ 1 + π ^ 2 / 3 / g ^ 2 := by positivity
  unfold localShallowTail shallowTail
  rw [← localBumpConst]
  have h3 : 0 ≤ localBumpConst w ^ 4 * (1 + π ^ 2 / 3 / g ^ 2) := by positivity
  nlinarith

/-- **Local resolution.** Let `Z, Z'` be tempered configurations in the strip with equal Weil forms
on `C²` tests supported in `[−a, a]`, `a ≥ V/2 + w`. Suppose their points with height in
`[X − R, X + R]` have depth `≤ s` and `g`-separated heights apart from FE partners, `g > π/V`, and
`2K T_loc < θ r⁴`. Then every `z` with `|Im z − X| ≤ R` satisfies
`|m_Z(z) − m_{Z'}(z)|² ≤ C (1 + |Im z − X|)^{14} (1 + |X|)⁴ S²/(1 + R/2)^{10}`. -/
theorem norm_multDiff_sq_le_of_locally_shallow (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {g V w s a X R : ℝ} (hg : 0 < g) (hV : 0 < V) (hw0 : 0 < w)
    (hw4 : 4 * w ≤ 1) (hVa : V / 2 + w ≤ a) (hs : 0 ≤ s)
    (hstrip : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, |ρ.re - 1 / 2| ≤ 1 / 2)
    (hdepth : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, |ρ.im - X| ≤ R → |ρ.re - 1 / 2| ≤ s)
    (hsep : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, |ρ.im - X| ≤ R →
      |ρ'.im - X| ≤ R → ρ' ≠ ρ → ρ' ≠ reflect ρ → g ≤ |ρ.im - ρ'.im|)
    (hgap : π / V < g)
    (hcond : 2 * remConst V g s * localShallowTail w g <
      tiltedInghamConst V g 0 * shallowFloor w s ^ 4)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f)
    {z : ℂ} (hz : |z.im - X| ≤ R) :
    ‖multDiff Z Z' z‖ ^ 2 ≤ localShallowConst V w g s * (1 + |z.im - X|) ^ 14 * (1 + |X|) ^ 4 *
      (∑' ρ, ‖multDiff Z Z' ρ‖ / (1 + Complex.normSq (gammaOf ρ))) ^ 2 / (1 + R / 2) ^ 10 := by
  classical
  set c := multDiff Z Z' with hcdef
  set Cw := localBumpConst w with hCw
  have hCw0 : 0 ≤ Cw := localBumpConst_nonneg hw0
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = tiltedInghamConst V g 0 * shallowFloor w s ^ 4 -
      2 * remConst V g s * localShallowTail w g := ⟨_, rfl⟩
  have hΔ0 : 0 < Δ := by rw [hΔ]; linarith
  have hconst : localShallowConst V w g s = 25 * V * Real.exp V * Cw ^ 4 / Δ := by
    rw [localShallowConst, hΔ]
  have hconst0 : 0 ≤ localShallowConst V w g s := by
    rw [hconst]; exact div_nonneg (by positivity) hΔ0.le
  have hN1 : ∀ ρ : ℂ, 0 < 1 + Complex.normSq (gammaOf ρ) := fun ρ => by
    linarith [Complex.normSq_nonneg (gammaOf ρ)]
  -- the weighted multiplicities are summable
  set ω : ℂ → ℝ := fun ρ => ‖c ρ‖ / (1 + Complex.normSq (gammaOf ρ)) with hω
  have hωs : Summable ω := by
    refine Summable.of_nonneg_of_le (fun ρ => div_nonneg (norm_nonneg _) (hN1 ρ).le)
      (fun ρ => ?_) ((summable_indicator_tempered Z hZ).add (summable_indicator_tempered Z' hZ'))
    rw [← add_div]
    exact div_le_div_of_nonneg_right (norm_multDiff_le_add Z Z' ρ) (hN1 ρ).le
  set S := ∑' ρ, ω ρ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun ρ => div_nonneg (norm_nonneg _) (hN1 ρ).le
  by_cases hcz : c z = 0
  · rw [hcz, norm_zero]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this]
    exact div_nonneg (by positivity) (by positivity)
  -- a site with the multiplicity of `z`
  obtain ⟨t₁, ht₁re, ht₁im, ht₁c⟩ : ∃ t₁ : ℂ, 1 / 2 ≤ t₁.re ∧ t₁.im = z.im ∧ c t₁ = c z := by
    by_cases h : 1 / 2 ≤ z.re
    · exact ⟨z, h, rfl, rfl⟩
    · exact ⟨reflect z, by rw [reflect_re']; linarith, reflect_im' z, multDiff_reflect Z Z' z⟩
  have hct₁ : c t₁ ≠ 0 := by rw [ht₁c]; exact hcz
  set K := pairSites Z Z' with hK
  set N : Set K := {k | |(k : ℂ).im - X| ≤ R} with hN
  have hdepthK : ∀ k : K, |(k : ℂ).re - 1 / 2| ≤ 1 / 2 := fun k => hstrip k k.2.1
  -- maximize `|c_k|/(1 + |γ_k − X|)⁷` over the sites near `X`
  set ψ : N → ℝ := fun k => ‖c ((k : K) : ℂ)‖ / (1 + |((k : K) : ℂ).im - X|) ^ 7 with hψ
  have hψs : Summable ψ := by
    have hinj : Function.Injective fun k : N => ((k : K) : ℂ) :=
      Subtype.val_injective.comp Subtype.val_injective
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((hωs.comp_injective hinj).mul_left (5 / 4 * (1 + |X|) ^ 2 * (1 + R) ^ 2))
    show ψ k ≤ 5 / 4 * (1 + |X|) ^ 2 * (1 + R) ^ 2 * ω ((k : K) : ℂ)
    have hk := one_add_normSq_gammaOf_le (hdepthK k) X
    have hkR : (1 + |((k : K) : ℂ).im - X|) ^ 2 ≤ (1 + R) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith [k.2]) 2
    have hn : 1 + Complex.normSq (gammaOf ((k : K) : ℂ)) ≤ 5 / 4 * (1 + |X|) ^ 2 * (1 + R) ^ 2 :=
      hk.trans (mul_le_mul_of_nonneg_left hkR (by positivity))
    have hψc : ψ k ≤ ‖c ((k : K) : ℂ)‖ :=
      div_le_self (norm_nonneg _) (one_le_pow₀ (by linarith [abs_nonneg (((k : K) : ℂ).im - X)]))
    refine hψc.trans ?_
    simp only [hω]
    rw [mul_div_assoc', le_div_iff₀ (hN1 _)]
    exact mul_le_mul_of_nonneg_left hn (norm_nonneg _) |>.trans_eq' (by ring)
  set t₁N : N := ⟨⟨t₁, mem_carrier_of_multDiff_ne_zero hct₁, ht₁re⟩, by
    show |t₁.im - X| ≤ R; rw [ht₁im]; exact hz⟩ with ht₁N
  have hψt : 0 < ψ t₁N := div_pos (norm_pos_iff.mpr hct₁) (by positivity)
  have hfin : (ψ ⁻¹' Iio (ψ t₁N))ᶜ.Finite :=
    Filter.mem_cofinite.mp (hψs.tendsto_cofinite_zero (Iio_mem_nhds hψt))
  obtain ⟨k₀, -, hk₀max⟩ := hfin.toFinset.exists_max_image ψ ⟨t₁N, by simp⟩
  have hmax : ∀ k, ψ k ≤ ψ k₀ := by
    intro k
    by_cases hk : ψ k < ψ t₁N
    · exact hk.le.trans (hk₀max t₁N (by simp))
    · exact hk₀max k (by simpa using hk)
  set z₀ : ℂ := ((k₀ : K) : ℂ) with hz₀
  set γ₀ := z₀.im with hγ₀
  set d₀ := |γ₀ - X| with hd₀
  have hd₀R : d₀ ≤ R := k₀.2
  have hd₀0 : 0 ≤ d₀ := abs_nonneg _
  -- domination of the near sites
  have hdom : ∀ k : N, ‖c ((k : K) : ℂ)‖ ≤ ‖c z₀‖ * (1 + |((k : K) : ℂ).im - γ₀|) ^ 7 := by
    intro k
    have h := hmax k
    simp only [hψ] at h
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
    have htri := one_add_abs_sub_le_mul (((k : K) : ℂ).im) γ₀ X
    have hpow : (1 + |((k : K) : ℂ).im - X|) ^ 7 ≤
        (1 + d₀) ^ 7 * (1 + |((k : K) : ℂ).im - γ₀|) ^ 7 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) htri 7
    refine le_of_mul_le_mul_right ?_ (by positivity : 0 < (1 + d₀) ^ 7)
    calc ‖c ((k : K) : ℂ)‖ * (1 + d₀) ^ 7 ≤ ‖c z₀‖ * (1 + |((k : K) : ℂ).im - X|) ^ 7 := h
      _ ≤ ‖c z₀‖ * ((1 + d₀) ^ 7 * (1 + |((k : K) : ℂ).im - γ₀|) ^ 7) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = ‖c z₀‖ * (1 + |((k : K) : ℂ).im - γ₀|) ^ 7 * (1 + d₀) ^ 7 := by ring
  -- the pair sum at the maximal site vanishes
  have hzero := pairSum_vanishes_of_weil_eq Z Z' hZ hZ' hw0 hVa γ₀ hW
  have hsumK := summable_site Z Z' hZ hZ' hw0 γ₀
  set TK : K → ℝ → ℂ := fun k v => cexp (I * (k : ℂ).im * v) *
    (siteP Z Z' w γ₀ k * cexp ((((k : ℂ).re - 1 / 2 : ℝ) : ℂ) * v) +
      siteQ Z Z' w γ₀ k * cexp (-(((k : ℂ).re - 1 / 2 : ℝ) : ℂ) * v)) with hTK
  have hzero' : ∀ v ∈ Icc (-V) V, ∑' k : K, TK k v = 0 := hzero
  set E := Real.exp (1 / 2 * V) with hE
  have hTb : ∀ k : K, ∀ v ∈ Icc (-V) V,
      ‖TK k v‖ ≤ E * (‖siteP Z Z' w γ₀ k‖ + ‖siteQ Z Z' w γ₀ k‖) := by
    intro k v hv
    have hvV : |v| ≤ V := abs_le.mpr hv
    have hδv : ∀ σ : ℝ, |σ| ≤ 1 / 2 → ‖cexp ((σ : ℂ) * v)‖ ≤ E := fun σ hσ => by
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
        rw [abs_mul]; exact mul_le_mul hσ hvV (abs_nonneg _) (by norm_num)))
    have h1 : ‖cexp (I * (k : ℂ).im * v)‖ = 1 := by
      rw [show I * ((k : ℂ).im : ℂ) * v = (((k : ℂ).im * v : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hneg : -((((k : ℂ).re - 1 / 2 : ℝ)) : ℂ) * v = ((-((k : ℂ).re - 1 / 2) : ℝ) : ℂ) * v := by
      push_cast; ring
    simp only [hTK]
    rw [norm_mul, h1, one_mul, hneg]
    calc _ ≤ ‖siteP Z Z' w γ₀ k‖ * E + ‖siteQ Z Z' w γ₀ k‖ * E := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
          · exact mul_le_mul_of_nonneg_left (hδv _ (hdepthK k)) (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hδv _ (by rw [abs_neg]; exact hdepthK k))
              (norm_nonneg _)
      _ = E * (‖siteP Z Z' w γ₀ k‖ + ‖siteQ Z Z' w γ₀ k‖) := by ring
  -- the near pair sum is minus the far one
  set WF := ∑' k : ↑Nᶜ, (‖siteP Z Z' w γ₀ ((k : K) : ℂ)‖ + ‖siteQ Z Z' w γ₀ ((k : K) : ℂ)‖)
    with hWF
  have hWF0 : 0 ≤ WF := tsum_nonneg fun k => by positivity
  have hsmallN : ∀ v ∈ Icc (-V) V, ‖∑' k : N, TK k v‖ ≤ E * WF := by
    intro v hv
    have hTs : Summable fun k : K => TK k v :=
      Summable.of_norm_bounded (hsumK.mul_left E) fun k => hTb k v hv
    have hsplit := hTs.tsum_subtype_add_tsum_subtype_compl N
    rw [hzero' v hv] at hsplit
    have heq : ∑' k : N, TK k v = -∑' k : ↑Nᶜ, TK k v := by linear_combination hsplit
    rw [heq, norm_neg]
    have hws : Summable fun k : ↑Nᶜ =>
        ‖siteP Z Z' w γ₀ ((k : K) : ℂ)‖ + ‖siteQ Z Z' w γ₀ ((k : K) : ℂ)‖ := hsumK.subtype _
    refine (norm_tsum_le_tsum_norm ((hws.mul_left E).of_norm_bounded fun k => ?_)).trans ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hTb k v hv
    · rw [hWF, ← tsum_mul_left]
      exact (Summable.of_norm_bounded (hws.mul_left E) fun k => hTb k v hv).norm.tsum_le_tsum
        (fun k => hTb k v hv) (hws.mul_left E)
  -- Ingham on the near sites
  have hδN : ∀ k : N, |((k : K) : ℂ).re - 1 / 2| ≤ s := fun k => hdepth _ (k : K).2.1 k.2
  have hsepN : ∀ j l : N, j ≠ l → g ≤ |((j : K) : ℂ).im - ((l : K) : ℂ).im| := by
    intro j l hjl
    have hjl' : (j : K) ≠ l := fun h => hjl (Subtype.ext h)
    refine hsep _ (j : K).2.1 _ (l : K).2.1 j.2 l.2 (fun h => hjl' (Subtype.ext h.symm))
      fun h => hjl' ?_
    apply Subtype.ext
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    rw [reflect_re'] at hre
    rw [reflect_im'] at him
    have h1 := (j : K).2.2
    have h2 := (l : K).2.2
    apply Complex.ext <;> linarith
  have hsumN : Summable fun k : N =>
      ‖siteP Z Z' w γ₀ ((k : K) : ℂ)‖ + ‖siteQ Z Z' w γ₀ ((k : K) : ℂ)‖ := hsumK.subtype _
  have hcore := inghamConst_mul_normSq_le_of_small (κ := N) (fun k => ((k : K) : ℂ).im)
    (fun k => ((k : K) : ℂ).re - 1 / 2) (fun k => siteP Z Z' w γ₀ ((k : K) : ℂ))
    (fun k => siteQ Z Z' w γ₀ ((k : K) : ℂ)) hg hV hs hδN hsepN hgap hsumN hsmallN k₀
  -- the near sites sum to `T_loc |c₀|²`
  have hnear : ∑' k : N, (‖siteP Z Z' w γ₀ ((k : K) : ℂ)‖ + ‖siteQ Z Z' w γ₀ ((k : K) : ℂ)‖) ^ 2 ≤
      localShallowTail w g * ‖c z₀‖ ^ 2 := by
    refine (tsum_le_of_decay_two
      (fun k : N => (‖siteP Z Z' w γ₀ ((k : K) : ℂ)‖ + ‖siteQ Z Z' w γ₀ ((k : K) : ℂ)‖) ^ 2)
      (fun k => sq_nonneg _) (fun k : N => ((k : K) : ℂ).im) hg
      (c := 4 * Cw ^ 4 * ‖c z₀‖ ^ 2) (by positivity) hsepN k₀ (fun k => ?_)).trans
      (le_of_eq ?_)
    · have hk1 := norm_siteP_add_norm_siteQ_le Z Z' hw0 hw4 γ₀ ((k : K) : ℂ) (hdepthK k)
      have hx1 : (0 : ℝ) < 1 + |((k : K) : ℂ).im - γ₀| := by positivity
      have hwk : ‖siteP Z Z' w γ₀ ((k : K) : ℂ)‖ + ‖siteQ Z Z' w γ₀ ((k : K) : ℂ)‖ ≤
          2 * Cw ^ 2 * ‖c z₀‖ / (1 + |((k : K) : ℂ).im - γ₀|) := by
        calc _ ≤ 2 * ‖c ((k : K) : ℂ)‖ * (Cw / (1 + |((k : K) : ℂ).im - γ₀|) ^ 4) ^ 2 := hk1
          _ ≤ 2 * (‖c z₀‖ * (1 + |((k : K) : ℂ).im - γ₀|) ^ 7) *
              (Cw / (1 + |((k : K) : ℂ).im - γ₀|) ^ 4) ^ 2 := by
            gcongr; exact hdom k
          _ = 2 * Cw ^ 2 * ‖c z₀‖ / (1 + |((k : K) : ℂ).im - γ₀|) := by
            field_simp
      calc (‖siteP Z Z' w γ₀ ((k : K) : ℂ)‖ + ‖siteQ Z Z' w γ₀ ((k : K) : ℂ)‖) ^ 2 ≤
          (2 * Cw ^ 2 * ‖c z₀‖ / (1 + |((k : K) : ℂ).im - γ₀|)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hwk 2
        _ = 4 * Cw ^ 4 * ‖c z₀‖ ^ 2 / (1 + |((k : K) : ℂ).im - γ₀|) ^ 2 := by
            field_simp; ring
    · rw [localShallowTail, ← hCw]; ring
  -- the far sites weigh at most `G S`
  set G := 5 / 2 * Cw ^ 2 * (1 + |X|) ^ 2 * (1 + d₀) ^ 2 / (1 + (R - d₀)) ^ 6 with hG
  have hG0 : 0 ≤ G := by
    rw [hG]; exact div_nonneg (by positivity) (pow_nonneg (by linarith) 6)
  have hfar : WF ≤ G * S := by
    have hper : ∀ k : ↑Nᶜ, ‖siteP Z Z' w γ₀ ((k : K) : ℂ)‖ + ‖siteQ Z Z' w γ₀ ((k : K) : ℂ)‖ ≤
        G * ω ((k : K) : ℂ) := by
      intro k
      set ρ : ℂ := ((k : K) : ℂ) with hρ
      have hfarρ : R < |ρ.im - X| := not_le.mp k.2
      have hk1 := norm_siteP_add_norm_siteQ_le Z Z' hw0 hw4 γ₀ ρ (hdepthK k)
      have hn := one_add_normSq_gammaOf_le (hdepthK k) X
      have htri := one_add_abs_sub_le_mul ρ.im γ₀ X
      have hx : R - d₀ ≤ |ρ.im - γ₀| := by
        have := abs_sub_abs_le_abs_sub (ρ.im - X) (γ₀ - X)
        rw [show ρ.im - X - (γ₀ - X) = ρ.im - γ₀ by ring] at this
        linarith
      have hx1 : (0 : ℝ) < 1 + |ρ.im - γ₀| := by positivity
      have hR1 : (0 : ℝ) < 1 + (R - d₀) := by linarith
      have hcρ : ‖c ρ‖ = ω ρ * (1 + Complex.normSq (gammaOf ρ)) := by
        simp only [hω]; field_simp [(hN1 ρ).ne']
      have hc_le : ‖c ρ‖ ≤ 5 / 4 * (1 + |X|) ^ 2 * (1 + d₀) ^ 2 * (1 + |ρ.im - γ₀|) ^ 2 * ω ρ := by
        have hω0 : 0 ≤ ω ρ := div_nonneg (norm_nonneg _) (hN1 ρ).le
        have h2 : (1 + |ρ.im - X|) ^ 2 ≤ ((1 + d₀) * (1 + |ρ.im - γ₀|)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) htri 2
        rw [hcρ]
        calc ω ρ * (1 + Complex.normSq (gammaOf ρ)) ≤
            ω ρ * (5 / 4 * (1 + |X|) ^ 2 * (1 + |ρ.im - X|) ^ 2) :=
              mul_le_mul_of_nonneg_left hn hω0
          _ ≤ ω ρ * (5 / 4 * (1 + |X|) ^ 2 * ((1 + d₀) * (1 + |ρ.im - γ₀|)) ^ 2) := by gcongr
          _ = _ := by ring
      have hω0 : 0 ≤ ω ρ := div_nonneg (norm_nonneg _) (hN1 ρ).le
      calc _ ≤ 2 * ‖c ρ‖ * (Cw / (1 + |ρ.im - γ₀|) ^ 4) ^ 2 := hk1
        _ ≤ 2 * (5 / 4 * (1 + |X|) ^ 2 * (1 + d₀) ^ 2 * (1 + |ρ.im - γ₀|) ^ 2 * ω ρ) *
            (Cw / (1 + |ρ.im - γ₀|) ^ 4) ^ 2 := by gcongr
        _ = 5 / 2 * Cw ^ 2 * (1 + |X|) ^ 2 * (1 + d₀) ^ 2 * ω ρ / (1 + |ρ.im - γ₀|) ^ 6 := by
            field_simp; ring
        _ ≤ 5 / 2 * Cw ^ 2 * (1 + |X|) ^ 2 * (1 + d₀) ^ 2 * ω ρ / (1 + (R - d₀)) ^ 6 :=
            div_le_div_of_nonneg_left (by positivity) (pow_pos hR1 6)
              (pow_le_pow_left₀ hR1.le (by linarith) 6)
        _ = G * ω ρ := by rw [hG]; ring
    have hinj : Function.Injective fun k : ↑Nᶜ => ((k : K) : ℂ) :=
      Subtype.val_injective.comp Subtype.val_injective
    have hωNc : Summable fun k : ↑Nᶜ => ω ((k : K) : ℂ) := hωs.comp_injective hinj
    have h1 : WF ≤ ∑' k : ↑Nᶜ, G * ω ((k : K) : ℂ) :=
      Summable.tsum_le_tsum hper (hsumK.subtype _) (hωNc.mul_left G)
    rw [tsum_mul_left] at h1
    have h2 : ∑' k : ↑Nᶜ, ω ((k : K) : ℂ) ≤ S :=
      Summable.tsum_le_tsum_of_inj (fun k : ↑Nᶜ => ((k : K) : ℂ)) hinj
        (fun ρ _ => div_nonneg (norm_nonneg _) (hN1 ρ).le) (fun k => le_rfl) hωNc hωs
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hG0)
  -- the maximal coefficient is bounded by the far weight
  have hcentre := norm_multDiff_mul_shallowFloor_sq_le Z Z' (s := s) hw0 z₀
    (hdepth z₀ (k₀ : K).2.1 k₀.2)
  have hθ := inghamConst_pos hV hgap
  have hK0 := remConst_nonneg (g := g) hV hs
  have hE2 : E ^ 2 = Real.exp V := by
    rw [hE, sq, ← Real.exp_add]; ring_nf
  have hP : ‖c z₀‖ ^ 2 ≤ 4 * V * Real.exp V * (G * S) ^ 2 / Δ := by
    rw [le_div_iff₀ hΔ0]
    have h1 : tiltedInghamConst V g 0 * (‖c z₀‖ * shallowFloor w s ^ 2) ^ 2 ≤
        tiltedInghamConst V g 0 * ‖siteP Z Z' w γ₀ z₀ + siteQ Z Z' w γ₀ z₀‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (sq_nonneg _))
        hcentre 2) hθ.le
    have h2 := mul_le_mul_of_nonneg_left hnear (mul_nonneg zero_le_two hK0)
    have h3 : (E * WF) ^ 2 ≤ Real.exp V * (G * S) ^ 2 := by
      rw [mul_pow, hE2]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hWF0 hfar 2) (Real.exp_pos V).le
    have h3' := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * V)
    have hcore' : tiltedInghamConst V g 0 * ‖siteP Z Z' w γ₀ z₀ + siteQ Z Z' w γ₀ z₀‖ ^ 2 ≤
        2 * remConst V g s * ∑' k : N,
          (‖siteP Z Z' w γ₀ ((k : K) : ℂ)‖ + ‖siteQ Z Z' w γ₀ ((k : K) : ℂ)‖) ^ 2 +
        4 * V * (E * WF) ^ 2 := hcore
    have e1 : tiltedInghamConst V g 0 * (‖c z₀‖ * shallowFloor w s ^ 2) ^ 2 =
        tiltedInghamConst V g 0 * shallowFloor w s ^ 4 * ‖c z₀‖ ^ 2 := by ring
    have e2 : 2 * remConst V g s * (localShallowTail w g * ‖c z₀‖ ^ 2) =
        2 * remConst V g s * localShallowTail w g * ‖c z₀‖ ^ 2 := by ring
    have e3 : ‖c z₀‖ ^ 2 * Δ = tiltedInghamConst V g 0 * shallowFloor w s ^ 4 * ‖c z₀‖ ^ 2 -
        2 * remConst V g s * localShallowTail w g * ‖c z₀‖ ^ 2 := by rw [hΔ]; ring
    rw [e3]
    linarith only [hcore', h1, h2, h3', e1, e2]
  -- transfer to `z` by maximality
  set d₁ := |z.im - X| with hd₁
  have h14 : ‖c t₁‖ ^ 2 * (1 + d₀) ^ 14 ≤ ‖c z₀‖ ^ 2 * (1 + d₁) ^ 14 := by
    have h := hmax t₁N
    simp only [hψ] at h
    have ht : ((t₁N : K) : ℂ) = t₁ := rfl
    rw [ht, ht₁im, div_le_div_iff₀ (by positivity) (by positivity)] at h
    have h2 := pow_le_pow_left₀ (by positivity) h 2
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul] at h2
    exact h2
  have hd1 : (0 : ℝ) < 1 + d₀ := by linarith
  have hR1 : (0 : ℝ) < 1 + (R - d₀) := by linarith
  have hfinal : ‖c t₁‖ ^ 2 ≤ 4 * V * Real.exp V * (G * S) ^ 2 / Δ * (1 + d₁) ^ 14 /
      (1 + d₀) ^ 14 := by
    rw [le_div_iff₀ (by positivity)]
    exact h14.trans (mul_le_mul_of_nonneg_right hP (by positivity))
  have heq : 4 * V * Real.exp V * (G * S) ^ 2 / Δ * (1 + d₁) ^ 14 / (1 + d₀) ^ 14 =
      localShallowConst V w g s * (1 + d₁) ^ 14 * (1 + |X|) ^ 4 * S ^ 2 /
        ((1 + d₀) ^ 10 * (1 + (R - d₀)) ^ 12) := by
    rw [hconst, hG]
    field_simp
    ring
  rw [heq] at hfinal
  rw [← ht₁c]
  refine hfinal.trans (div_le_div_of_nonneg_left ?_ (by positivity)
    (one_add_half_pow_le hd₀0 hd₀R))
  exact mul_nonneg (mul_nonneg (mul_nonneg hconst0 (by positivity)) (by positivity)) (sq_nonneg _)

/-! ### The Ingham scale, locally -/

/-- **The Ingham scale, locally.** For every aperture `a > 0` and every `g > π/(2a)` there are a
depth `s₀ > 0` and a constant `C ≥ 0` such that for tempered mimics at aperture `a` in the strip,
every height `X` and radius `R`: if the points with height in `[X − R, X + R]` have depth `≤ s₀` and
`g`-separated heights apart from FE partners, then every `z` with `|Im z − X| ≤ R` satisfies
`|m_Z(z) − m_{Z'}(z)|² ≤ C (1 + |Im z − X|)^{14} (1 + |X|)⁴ S²/(1 + R/2)^{10}`. -/
theorem exists_local_resolution_at_ingham_scale {a g : ℝ} (ha : 0 < a) (hg : π / (2 * a) < g) :
    ∃ s₀ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) →
      (∀ ρ ∈ Z.carrier ∪ Z'.carrier, |ρ.re - 1 / 2| ≤ 1 / 2) → ∀ X R : ℝ,
      (∀ ρ ∈ Z.carrier ∪ Z'.carrier, |ρ.im - X| ≤ R → |ρ.re - 1 / 2| ≤ s₀) →
      (∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, |ρ.im - X| ≤ R →
        |ρ'.im - X| ≤ R → ρ' ≠ ρ → ρ' ≠ reflect ρ → g ≤ |ρ.im - ρ'.im|) →
      ∀ z : ℂ, |z.im - X| ≤ R →
        ‖multDiff Z Z' z‖ ^ 2 ≤ C * (1 + |z.im - X|) ^ 14 * (1 + |X|) ^ 4 *
          (∑' ρ, ‖multDiff Z Z' ρ‖ / (1 + Complex.normSq (gammaOf ρ))) ^ 2 / (1 + R / 2) ^ 10 := by
  have hg0 : 0 < g := lt_trans (by positivity) hg
  have hπg : π / g < 2 * a := by
    rw [div_lt_iff₀ hg0]
    rw [div_lt_iff₀ (by positivity)] at hg
    linarith
  set V := (π / g + 2 * a) / 2 with hVdef
  have hπg0 : 0 < π / g := by positivity
  have hV : 0 < V := by rw [hVdef]; linarith
  have hgap : π / V < g := by
    rw [div_lt_iff₀ hV]
    have : π / g < V := by rw [hVdef]; linarith
    rw [div_lt_iff₀ hg0] at this
    linarith
  set w := min (a - V / 2) (1 / 4) with hwdef
  have hw0 : 0 < w := lt_min (by rw [hVdef]; linarith) (by norm_num)
  have hw4 : 4 * w ≤ 1 := by have := min_le_right (a - V / 2) (1 / 4); linarith
  have hVa : V / 2 + w ≤ a := by have := min_le_left (a - V / 2) (1 / 4); linarith
  obtain ⟨s₀, hs₀, hcond⟩ := exists_shallow_depth hV hw0 hgap
  have hcond' : 2 * remConst V g s₀ * localShallowTail w g <
      tiltedInghamConst V g 0 * shallowFloor w s₀ ^ 4 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (localShallowTail_le_shallowTail hw0 g s₀)
      (mul_nonneg zero_le_two (remConst_nonneg hV hs₀.le))) (hcond s₀ ⟨hs₀.le, le_rfl⟩)
  have hC0 : 0 ≤ localShallowConst V w g s₀ :=
    div_nonneg (by have := localBumpConst_nonneg hw0; positivity) (by linarith)
  refine ⟨s₀, hs₀, localShallowConst V w g s₀, hC0,
    fun Z Z' hZ hZ' hW hstrip X R hdepth hsep z hz => ?_⟩
  exact norm_multDiff_sq_le_of_locally_shallow Z Z' hZ hZ' hg0 hV hw0 hw4 hVa hs₀.le hstrip hdepth
    hsep hgap hcond' hW hz

/-- **Local identification at the Ingham scale.** In the setting of
`exists_local_resolution_at_ingham_scale`, the multiplicities of the two mimics agree at every `z`
within `R` of `X` once `C (1 + |Im z − X|)^{14} (1 + |X|)⁴ S² < (1 + R/2)^{10}`. -/
theorem eq_of_locally_shallow_at_ingham_scale {a g : ℝ} (ha : 0 < a) (hg : π / (2 * a) < g) :
    ∃ s₀ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) →
      (∀ ρ ∈ Z.carrier ∪ Z'.carrier, |ρ.re - 1 / 2| ≤ 1 / 2) → ∀ X R : ℝ,
      (∀ ρ ∈ Z.carrier ∪ Z'.carrier, |ρ.im - X| ≤ R → |ρ.re - 1 / 2| ≤ s₀) →
      (∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, |ρ.im - X| ≤ R →
        |ρ'.im - X| ≤ R → ρ' ≠ ρ → ρ' ≠ reflect ρ → g ≤ |ρ.im - ρ'.im|) →
      ∀ z : ℂ, |z.im - X| ≤ R →
        C * (1 + |z.im - X|) ^ 14 * (1 + |X|) ^ 4 *
          (∑' ρ, ‖multDiff Z Z' ρ‖ / (1 + Complex.normSq (gammaOf ρ))) ^ 2 < (1 + R / 2) ^ 10 →
        multDiff Z Z' z = 0 := by
  obtain ⟨s₀, hs₀, C, hC, hres⟩ := exists_local_resolution_at_ingham_scale ha hg
  refine ⟨s₀, hs₀, C, hC, fun Z Z' hZ hZ' hW hstrip X R hdepth hsep z hz hlt => ?_⟩
  by_contra hne
  have h1 : 1 ≤ ‖multDiff Z Z' z‖ := by
    classical
    obtain ⟨m, hm⟩ : ∃ m : ℤ, multDiff Z Z' z = m := by
      refine ⟨(if z ∈ Z.carrier then (Z.mult z : ℤ) else 0) -
        (if z ∈ Z'.carrier then (Z'.mult z : ℤ) else 0), ?_⟩
      simp only [multDiff, Set.indicator_apply]
      split_ifs <;> push_cast <;> ring
    rw [hm] at hne ⊢
    have hm0 : m ≠ 0 := fun e => hne (by rw [e, Int.cast_zero])
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hm0
  have h := hres Z Z' hZ hZ' hW hstrip X R hdepth hsep z hz
  have hpos : (0 : ℝ) < (1 + R / 2) ^ 10 := lt_of_le_of_lt (by
    have : 0 ≤ ∑' ρ, ‖multDiff Z Z' ρ‖ / (1 + Complex.normSq (gammaOf ρ)) :=
      tsum_nonneg fun ρ => div_nonneg (norm_nonneg _) (by positivity)
    positivity) hlt
  rw [le_div_iff₀ hpos] at h
  have h2 : 1 ≤ ‖multDiff Z Z' z‖ ^ 2 := one_le_pow₀ h1
  nlinarith

end GaloisForLFunctions.ZeroConfigurationGeometry
