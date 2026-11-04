import GaloisForLFunctions.WindowVisibilityLaw.CoherentClusterAndTiltAmplificationLaw
import GaloisForLFunctions.SquareRootThreshold.PositivityCertifiesColumnConfigurations

/-!
# Split-Column Visibility Threshold and Off-Line Column Fragility

This module resolves Test (3) of the window visibility law (`Γ40`, `Γ36`, `Π29`):

* **Finite-multiplicity division & one-sided isolation (`exists_iter_divWindow_paperFT_ne_zero`,
  `exists_window_re_W_neg_of_one_side_isolation`).** Iterated division at `w_- = γ_{1 − ρ̄₀}`
  terminates in finitely many steps by a factorial bound on `[−r, r]`, removing any accidental root
  at `w_-` without enlarging support. Since `pointImage f f z = f̂(γ_z) conj f̂(γ_{1 − z̄})`, blinding
  only the closed right half-plane `{z ∈ Z | ½ ≤ Re z} \ {ρ₀}` annihilates `pointImage f f` on all
  of `Z \ {ρ₀, 1 − ρ̄₀}` without ever blinding the left-half-plane columns.
* **Exact split-column threshold law (`re_eq_half_of_re_W_nonneg_of_one_side_columns`,
  `re_eq_half_of_re_W_nonneg_of_split_columns`,
  `onsetAperture_le_half_pi_density_of_all_offLine_columns`,
  `re_eq_half_of_re_W_nonneg_of_curve_columns_improved`).** For `D_on = ∑_{j ∈ T_on} 1/h_j` on-line
  column density and `D_off = 2 ∑_{j ∈ T_off} 1/h'_j` two-sided off-line column density, positivity
  at any `a > π D_on + (π/2) D_off` certifies `Re ρ = ½`. In particular, pure off-line column
  configurations (`T_on = ∅`) satisfy `onsetAperture Z ≤ (π/2) D`, and any `2g`-column curve
  configuration (`g ≥ 1`) is certified at `a > (g − ½) log q`, strictly improving `g log q`.
* **Sharp mixed `2g`-column counterexample (`mixedGenusColumnConfig`,
  `onsetAperture_mixedGenusColumnConfig_eq`).** For every `g ≥ 2` and shallow depth `δ > 0`, `2g − 2`
  on-line columns plus `1` off-line column pair of spacing `2π/ℓ` (`D = gℓ/π`) has exact onset
  aperture `onsetAperture = (g − ½)ℓ > (g/2)ℓ = πD/2`, refuting `πD/2` for mixed column geometries
  and proving `(g − ½) log q` sharp for every `g ≥ 2`.
* **Two-sided perturbation law for off-line columns (`onsetAperture_singleDefectOffLineLattice_lt`,
  `windowPositiveAt_perturbedOffLineLatticeConfig`).** Moving a single pair of the off-line lattice
  by `0 < ε ≤ π/L` collapses `onsetAperture` from `L/2` down to `O((1/(2δ)) log(δL/ε²))`, whereas
  exponentially small `ℓ¹` jitter `8 a² e^{2δa} ∑_k |ε_k| ≤ L` preserves `WindowPositiveAt` at
  `a ≤ L/2`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate Convolution

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.SquareRootThreshold

/-! ### 1. Finite-multiplicity division at a partner frequency -/

/-- Iterated quotient window `(divWindow r κ)^[n] f` at frequency `κ`. -/
def iterDivWindow (r : ℝ) (κ : ℂ) : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, f => f
  | n + 1, f => divWindow r κ (iterDivWindow r κ n f)

private theorem iterDivWindow_props_of_lt {r : ℝ} (hr : 0 ≤ r) {f : ℝ → ℂ}
    (hf : ApertureWindow r f) {κ : ℂ} :
    ∀ n : ℕ, (∀ k < n, paperFT (iterDivWindow r κ k f) κ = 0) →
      ApertureWindow r (iterDivWindow r κ n f) ∧
        ∀ w : ℂ, paperFT f w = (-I * (w - κ)) ^ n * paperFT (iterDivWindow r κ n f) w
  | 0, _ => ⟨hf, fun w => by simp [iterDivWindow]⟩
  | n + 1, hz => by
    obtain ⟨hgn, hft⟩ := iterDivWindow_props_of_lt hr hf n
      (fun k hk => hz k (Nat.lt_succ_of_lt hk))
    have hzn : paperFT (iterDivWindow r κ n f) κ = 0 := hz n (Nat.lt_succ_self n)
    have hg_succ : ApertureWindow r (iterDivWindow r κ (n + 1) f) :=
      ⟨by exact_mod_cast contDiff_divWindow r κ 2 hgn.1,
        tsupport_divWindow_subset hgn.1.continuous hgn.2 hr hzn⟩
    refine ⟨hg_succ, fun w => ?_⟩
    rw [hft w, paperFT_divWindow (hgn.1.of_le (by norm_num)) hgn.2 hr hzn w, pow_succ]
    dsimp [iterDivWindow]
    ring

private theorem norm_cexp_mul_iterDivWindow_le {r M : ℝ} (hr : 0 ≤ r) (hM0 : 0 ≤ M) {κ : ℂ}
    {f : ℝ → ℂ} (hM : ∀ u ∈ Icc (-r) r, ‖cexp (I * κ * u) * f u‖ ≤ M) :
    ∀ n : ℕ, (∀ k ≤ n, Continuous (iterDivWindow r κ k f)) →
      ∀ u ∈ Icc (-r) r,
        ‖cexp (I * κ * u) * iterDivWindow r κ n f u‖ ≤ M * (u + r) ^ n / (n.factorial : ℝ)
  | 0, _, u, hu => by
    simp only [iterDivWindow, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
    exact hM u hu
  | n + 1, hcont, u, hu => by
    have ih := norm_cexp_mul_iterDivWindow_le hr hM0 hM n
      (fun k hk => hcont k (Nat.le_succ_of_le hk))
    have hGn_cont : Continuous fun s : ℝ => cexp (I * κ * s) * iterDivWindow r κ n f s :=
      (contDiff_cexp_mul (I * κ)).continuous.mul (hcont n (Nat.le_succ n))
    have hstep : cexp (I * κ * u) * iterDivWindow r κ (n + 1) f u =
        ∫ s in (-r)..u, cexp (I * κ * s) * iterDivWindow r κ n f s := by
      dsimp only [iterDivWindow, divWindow]
      rw [← mul_assoc, ← Complex.exp_add,
        show I * κ * (u : ℂ) + -(I * κ * (u : ℂ)) = 0 by ring, Complex.exp_zero, one_mul]
    have hmaj_cont : Continuous fun s : ℝ => M * (s + r) ^ n / (n.factorial : ℝ) := by fun_prop
    have hantideriv : ∀ s : ℝ, HasDerivAt
        (fun t : ℝ => M * (t + r) ^ (n + 1) / ((n + 1).factorial : ℝ))
        (M * (s + r) ^ n / (n.factorial : ℝ)) s := fun s => by
      have hd := (((hasDerivAt_id s).add_const r).pow (n + 1) |>.const_mul M).div_const
        ((n + 1).factorial : ℝ)
      refine hd.congr_deriv ?_
      have hnf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [Nat.factorial_succ, Nat.cast_mul]
      push_cast
      field_simp
      ring
    rw [hstep, intervalIntegral.integral_of_le hu.1]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ s in Ioc (-r) u, ‖cexp (I * κ * s) * iterDivWindow r κ n f s‖
        ≤ ∫ s in Ioc (-r) u, M * (s + r) ^ n / (n.factorial : ℝ) :=
          setIntegral_mono_on hGn_cont.norm.integrableOn_Ioc hmaj_cont.integrableOn_Ioc
            measurableSet_Ioc fun s hs => ih s ⟨hs.1.le, hs.2.trans hu.2⟩
      _ = ∫ s in (-r)..u, M * (s + r) ^ n / (n.factorial : ℝ) :=
          (intervalIntegral.integral_of_le hu.1).symm
      _ = M * (u + r) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hantideriv s)
            (hmaj_cont.intervalIntegrable _ _)]
          simp [add_neg_cancel, zero_pow (Nat.succ_ne_zero n)]

/-- **Finite-multiplicity division.** If a window `f` of aperture `r ≥ 0` satisfies
`paperFT f w₁ ≠ 0`, iterated division at any frequency `w₂` terminates in finitely many steps at a
window `g` of the same aperture `r` that sees **both** `w₁` and `w₂` while preserving every zero of
`paperFT f` away from `w₂`. -/
theorem exists_iter_divWindow_paperFT_ne_zero {r : ℝ} (hr : 0 ≤ r) {f : ℝ → ℂ}
    (hf : ApertureWindow r f) {w₁ : ℂ} (hw₁ : paperFT f w₁ ≠ 0) (w₂ : ℂ) :
    ∃ g : ℝ → ℂ, ApertureWindow r g ∧ paperFT g w₁ ≠ 0 ∧ paperFT g w₂ ≠ 0 ∧
      ∀ w : ℂ, w ≠ w₂ → paperFT f w = 0 → paperFT g w = 0 := by
  classical
  have hex : ∃ n : ℕ, paperFT (iterDivWindow r w₂ n f) w₂ ≠ 0 := by
    by_contra hall_not
    push Not at hall_not
    have hall : ∀ n : ℕ, ApertureWindow r (iterDivWindow r w₂ n f) ∧
        ∀ w : ℂ, paperFT f w = (-I * (w - w₂)) ^ n * paperFT (iterDivWindow r w₂ n f) w :=
      fun n => iterDivWindow_props_of_lt hr hf n (fun k _ => hall_not k)
    have hG0_cont : Continuous fun u : ℝ => cexp (I * w₂ * u) * f u :=
      (contDiff_cexp_mul (I * w₂)).continuous.mul hf.1.continuous
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := -r) (b := r)).bddAbove_image hG0_cont.norm.continuousOn
    set M := max B 0
    have hM0 : 0 ≤ M := le_max_right B 0
    have hM : ∀ u ∈ Icc (-r) r, ‖cexp (I * w₂ * u) * f u‖ ≤ M := fun u hu =>
      (hB ⟨u, hu, rfl⟩).trans (le_max_left B 0)
    set C := M * Real.exp (|w₂.im| * r) * Real.exp (r * |w₁.im|) * (2 * r)
    set X := 2 * r * ‖w₁ - w₂‖
    have hbound : ∀ n : ℕ, ‖paperFT f w₁‖ ≤ C * (X ^ n / (n.factorial : ℝ)) := fun n => by
      have hgn := (hall n).1
      have hft := (hall n).2 w₁
      have hGn := norm_cexp_mul_iterDivWindow_le hr hM0 hM n
        (fun k _ => (hall k).1.1.continuous)
      have hpt_gn : ∀ u : ℝ, ‖iterDivWindow r w₂ n f u‖ ≤
          M * Real.exp (|w₂.im| * r) * (2 * r) ^ n / (n.factorial : ℝ) := fun u => by
        by_cases hu : u ∈ Icc (-r) r
        · have heq : iterDivWindow r w₂ n f u =
              cexp (-(I * w₂ * u)) * (cexp (I * w₂ * u) * iterDivWindow r w₂ n f u) := by
            rw [← mul_assoc, ← Complex.exp_add,
              show -(I * w₂ * (u : ℂ)) + I * w₂ * (u : ℂ) = 0 by ring, Complex.exp_zero, one_mul]
          have hexp : ‖cexp (-(I * w₂ * u))‖ ≤ Real.exp (|w₂.im| * r) := by
            rw [Complex.norm_exp]
            have hre : (-(I * w₂ * (u : ℂ))).re = w₂.im * u := by
              simp [Complex.mul_re, Complex.mul_im]
            rw [hre]
            refine Real.exp_le_exp.mpr ?_
            calc w₂.im * u ≤ |w₂.im * u| := le_abs_self _
              _ = |w₂.im| * |u| := abs_mul _ _
              _ ≤ |w₂.im| * r := mul_le_mul_of_nonneg_left (abs_le.mpr hu) (abs_nonneg _)
          have hur : (u + r) ^ n ≤ (2 * r) ^ n :=
            pow_le_pow_left₀ (by linarith [hu.1]) (by linarith [hu.2]) n
          rw [heq, norm_mul]
          calc ‖cexp (-(I * w₂ * u))‖ * ‖cexp (I * w₂ * u) * iterDivWindow r w₂ n f u‖
              ≤ Real.exp (|w₂.im| * r) * (M * (u + r) ^ n / (n.factorial : ℝ)) :=
                mul_le_mul hexp (hGn u hu) (norm_nonneg _) (Real.exp_pos _).le
            _ ≤ Real.exp (|w₂.im| * r) * (M * (2 * r) ^ n / (n.factorial : ℝ)) := by gcongr
            _ = M * Real.exp (|w₂.im| * r) * (2 * r) ^ n / (n.factorial : ℝ) := by ring
        · rw [eq_zero_of_not_mem_Icc_of_tsupport hgn.2 hu, norm_zero]
          positivity
      have hft_le := norm_paperFT_le_of_tsupport hr hgn.2 hpt_gn w₁
      have hpow_norm : ‖(-I * (w₁ - w₂)) ^ n‖ = ‖w₁ - w₂‖ ^ n := by
        rw [norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul]
      rw [hft, norm_mul, hpow_norm]
      calc ‖w₁ - w₂‖ ^ n * ‖paperFT (iterDivWindow r w₂ n f) w₁‖
          ≤ ‖w₁ - w₂‖ ^ n *
              ((M * Real.exp (|w₂.im| * r) * (2 * r) ^ n / (n.factorial : ℝ)) *
                Real.exp (r * |w₁.im|) * (2 * r)) :=
            mul_le_mul_of_nonneg_left hft_le (by positivity)
        _ = C * (X ^ n / (n.factorial : ℝ)) := by
            dsimp [C, X]; rw [mul_pow]; ring
    have hlim : Tendsto (fun n : ℕ => C * (X ^ n / (n.factorial : ℝ))) atTop (𝓝 0) := by
      simpa using (Real.summable_pow_div_factorial X).tendsto_atTop_zero.const_mul C
    have h0 : ‖paperFT f w₁‖ ≤ 0 := le_of_tendsto' hlim hbound
    exact hw₁ (norm_le_zero_iff.mp h0)
  set m := Nat.find hex
  have hm_ne : paperFT (iterDivWindow r w₂ m f) w₂ ≠ 0 := Nat.find_spec hex
  have hm_lt : ∀ k < m, paperFT (iterDivWindow r w₂ k f) w₂ = 0 :=
    fun k hk => Decidable.byContradiction (Nat.find_min hex hk)
  obtain ⟨hgm, hftm⟩ := iterDivWindow_props_of_lt hr hf m hm_lt
  refine ⟨iterDivWindow r w₂ m f, hgm, ?_, hm_ne, fun w hw hfw => ?_⟩
  · intro hg0
    have := hftm w₁
    rw [hg0, mul_zero] at this
    exact hw₁ this
  · have h := hftm w
    rw [hfw] at h
    have hfac : (-I * (w - w₂)) ^ m ≠ 0 :=
      pow_ne_zero m (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (sub_ne_zero.mpr hw))
    exact (mul_eq_zero.mp h.symm).resolve_left hfac

/-! ### 2. One-sided right-half-plane isolation makes `Re W < 0` -/

private theorem reflect_involutive (z : ℂ) : reflect (reflect z) = z := by
  apply Complex.ext <;> simp [reflect]

private theorem gammaOf_im_eq (z : ℂ) : (gammaOf z).im = 1 / 2 - z.re := by
  simp [gammaOf]

/-- **One-sided isolation makes `Re W_Z < 0`.** If `ρ₀ ∈ Z.carrier` lies strictly in the right half
plane (`½ < Re ρ₀`) and a window `f₁` of aperture `a' ≥ 0` sees `γ_{ρ₀}` while vanishing at `γ_z`
for every other `z ∈ Z.carrier` with `½ ≤ Re z`, then for every `ε > 0` there is a window `f` of
aperture `a' + ε` with `(Z.W f f).re < 0`. No left-half-plane zero ever has to be blinded directly,
because `pointImage f f z = f̂(γ_z) conj f̂(γ_{1 − z̄})` vanishes on `{Re z < ½} \ {1 − ρ̄₀}` via its
second factor. -/
theorem exists_window_re_W_neg_of_one_side_isolation {Z : ZeroConfig} {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hgt : 1 / 2 < ρ₀.re) {a' ε : ℝ} (ha' : 0 ≤ a') (hε : 0 < ε)
    {f₁ : ℝ → ℂ} (hf₁ : ApertureWindow a' f₁)
    (hblind : ∀ z ∈ Z.carrier, 1 / 2 ≤ z.re → z ≠ ρ₀ → paperFT f₁ (gammaOf z) = 0)
    (hsee : paperFT f₁ (gammaOf ρ₀) ≠ 0) :
    ∃ f : ℝ → ℂ, ApertureWindow (a' + ε) f ∧ (Z.W f f).re < 0 := by
  classical
  set w_pos := gammaOf ρ₀
  set w_neg := gammaOf (reflect ρ₀)
  have hw_im_pos : w_pos.im < 0 := by
    dsimp [w_pos]; rw [gammaOf_im_eq]; linarith
  have hw_im_neg : 0 < w_neg.im := by
    dsimp [w_neg]; rw [gammaOf_im_eq]
    have : (reflect ρ₀).re = 1 - ρ₀.re := by simp [reflect]
    linarith
  have hw_ne : w_pos ≠ w_neg := fun h => by
    have := congrArg Complex.im h; linarith
  obtain ⟨g, hg, hg_pos, hg_neg, hg_van⟩ :=
    exists_iter_divWindow_paperFT_ne_zero ha' hf₁ hsee w_neg
  have hg_right : ∀ z ∈ Z.carrier, 1 / 2 ≤ z.re → z ≠ ρ₀ → paperFT g (gammaOf z) = 0 := by
    intro z hz hre hne
    have hne_w : gammaOf z ≠ w_neg := fun h => by
      have := congrArg Complex.im h
      rw [gammaOf_im_eq] at this
      linarith
    exact hg_van (gammaOf z) hne_w (hblind z hz hre hne)
  obtain ⟨β₁, hβ₁, hβ₁_van, hβ₁_see⟩ := exists_window_vanishing_on_finset hε ({w_neg} : Finset ℂ)
    (Finset.notMem_singleton.mpr hw_ne)
  obtain ⟨β₂, hβ₂, hβ₂_van, hβ₂_see⟩ := exists_window_vanishing_on_finset hε ({w_pos} : Finset ℂ)
    (Finset.notMem_singleton.mpr hw_ne.symm)
  set u := paperFT g w_pos
  set v := paperFT g w_neg
  set b₁ := paperFT β₁ w_pos
  set b₂ := paperFT β₂ w_neg
  set c : ℂ := -(u * b₁) / (v * b₂)
  set β : ℝ → ℂ := fun t => β₁ t + c * β₂ t
  have hβ : ApertureWindow ε β := hβ₁.add_smul hβ₂ c
  have hβ_ft : ∀ w, paperFT β w = paperFT β₁ w + c * paperFT β₂ w :=
    paperFT_add_smul hβ₁.1.continuous hβ₁.hasCompactSupport hβ₂.1.continuous
      hβ₂.hasCompactSupport c
  obtain ⟨hf, hf_ft⟩ := apertureWindow_convolution hg hβ
  set f := convolution g β (ContinuousLinearMap.mul ℝ ℂ) volume
  set U := u * b₁
  have hU_ne : U ≠ 0 := mul_ne_zero hg_pos hβ₁_see
  have hf_pos : paperFT f w_pos = U := by
    rw [hf_ft, hβ_ft, hβ₂_van w_pos (Finset.mem_singleton_self _), mul_zero, add_zero]
  have hf_neg : paperFT f w_neg = -U := by
    rw [hf_ft, hβ_ft, hβ₁_van w_neg (Finset.mem_singleton_self _), zero_add]
    have hvb : v * b₂ ≠ 0 := mul_ne_zero hg_neg hβ₂_see
    dsimp [U, c, v, b₂]
    calc v * (-(u * b₁) / (v * b₂) * b₂)
        = (v * b₂) * (-(u * b₁) / (v * b₂)) := by ring
      _ = -(u * b₁) := mul_div_cancel₀ _ hvb
  have hρ₁ : reflect ρ₀ ∈ Z.carrier := Z.reflect_mem ρ₀ hρ₀
  have hrefl_ne : reflect ρ₀ ≠ ρ₀ := fun h => by
    have := congrArg Complex.re h
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    linarith
  have hS : ∀ z ∈ Z.carrier, z ∉ ({ρ₀, reflect ρ₀} : Finset ℂ) → pointImage f f z = 0 := by
    intro z hz hzS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzS
    rcases le_or_gt (1 / 2) z.re with hre | hre
    · rw [pointImage, hf_ft, hg_right z hz hre hzS.1, zero_mul, zero_mul]
    · have hz' : reflect z ∈ Z.carrier := Z.reflect_mem z hz
      have hre' : 1 / 2 ≤ (reflect z).re := by
        have : (reflect z).re = 1 - z.re := by simp [reflect]
        linarith
      have hne' : reflect z ≠ ρ₀ := fun h => hzS.2 (by rw [← h, reflect_involutive])
      rw [pointImage, ← gammaOf_reflect_eq_conj, hf_ft (gammaOf (reflect z)),
        hg_right (reflect z) hz' hre' hne', zero_mul, map_zero, mul_zero]
  have p0 : pointImage f f ρ₀ = -(U * conj U) := by
    rw [pointImage, show gammaOf ρ₀ = w_pos from rfl, ← gammaOf_reflect_eq_conj,
      show gammaOf (reflect ρ₀) = w_neg from rfl, hf_pos, hf_neg, map_neg, mul_neg]
  have p1 : pointImage f f (reflect ρ₀) = -(U * conj U) := by
    rw [pointImage, show gammaOf (reflect ρ₀) = w_neg from rfl, gammaOf_reflect_eq_conj,
      Complex.conj_conj, show gammaOf ρ₀ = w_pos from rfl, hf_neg, hf_pos]
    ring
  refine ⟨f, hf, ?_⟩
  rw [W_eq_sum_of_support Z ({ρ₀, reflect ρ₀} : Finset ℂ) hS, Finset.sum_pair hrefl_ne.symm,
    Set.indicator_of_mem hρ₀, Set.indicator_of_mem hρ₁, Z.mult_reflect ρ₀ hρ₀, p0, p1,
    Complex.mul_conj]
  have hnorm_pos : 0 < Complex.normSq U := Complex.normSq_pos.mpr hU_ne
  have hm : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  have heq : ((Z.mult ρ₀ : ℂ) * -((Complex.normSq U : ℝ) : ℂ) +
      (Z.mult ρ₀ : ℂ) * -((Complex.normSq U : ℝ) : ℂ)) =
      ((-(2 * (Z.mult ρ₀ : ℝ) * Complex.normSq U) : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.ofReal_re]
  nlinarith

/-! ### 3. The exact split-column threshold law (`Γ40`, `Γ36`) -/

/-- **One-sided column positivity criterion.** If the closed right-half-plane carrier
`{z ∈ Z.carrier | ½ ≤ Re z}` lies on finitely many perturbed columns `T` of total density
`D_+ = ∑_{j ∈ T} 1/h_j`, apart from a finite set `F`, then positivity at a single aperture
`a > π D_+` puts every point of `Z` on the critical line. -/
theorem re_eq_half_of_re_W_nonneg_of_one_side_columns {ι : Type*} [DecidableEq ι]
    {Z : ZeroConfig} (T : Finset ι) (h L : ι → ℝ) (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℂ)
    (hν : ∀ j ∈ T, ∀ k : ℤ, ‖ν j k - k * h j‖ ≤ L j)
    (him : ∀ j ∈ T, ∀ k, |(ν j k).im| ≤ 1 / 2) {a : ℝ} (ha : π * ∑ j ∈ T, (h j)⁻¹ < a)
    (F : Finset ℂ)
    (hS : ∀ z ∈ Z.carrier, 1 / 2 ≤ z.re → (∃ j ∈ T, ∃ k : ℤ, gammaOf z = ν j k) ∨ z ∈ F)
    (hpos : WindowPositiveAt Z a) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hoff
  set ρ₀ := if 1 / 2 < ρ.re then ρ else reflect ρ
  have hρ₀ : ρ₀ ∈ Z.carrier := by
    dsimp [ρ₀]; split_ifs; exacts [hρ, Z.reflect_mem ρ hρ]
  have hgt : 1 / 2 < ρ₀.re := by
    dsimp [ρ₀]
    split_ifs with hlt
    · exact hlt
    · have href : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
      have hle : ρ.re < 1 / 2 := lt_of_le_of_ne (not_lt.mp hlt) hoff
      linarith
  have hD0 : 0 ≤ π * ∑ j ∈ T, (h j)⁻¹ :=
    mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun j hj => (inv_pos.mpr (hh j hj)).le)
  set a' := (a + π * ∑ j ∈ T, (h j)⁻¹) / 2
  set ε := (a - π * ∑ j ∈ T, (h j)⁻¹) / 2
  have ha'0 : 0 ≤ a' := by dsimp [a']; linarith
  have hε0 : 0 < ε := by dsimp [ε]; linarith
  have ha'_gt : π * ∑ j ∈ T, (h j)⁻¹ < a' := by dsimp [a']; linarith
  obtain ⟨f₁, hf₁, hf₁_blind, hf₁_see⟩ := exists_isolating_window_of_columns_and_finset T h L hh ν
    hν him ha'_gt F (S := {z ∈ Z.carrier | 1 / 2 ≤ z.re}) (fun z hz => hS z hz.1 hz.2) ρ₀
  obtain ⟨f, hf, hneg⟩ := exists_window_re_W_neg_of_one_side_isolation hρ₀ hgt ha'0 hε0 hf₁
    (fun z hz hre hne => hf₁_blind z ⟨hz, hre⟩ hne) hf₁_see
  have hsum_a : a' + ε = a := by dsimp [a', ε]; ring
  rw [hsum_a] at hf
  exact absurd (hpos f hf.1 hf.2) (not_le.mpr hneg)

/-- **Exact split-column threshold law (`Γ40`).** Suppose `Z` decomposes into:
* `T_on` perturbed on-line columns of spacing `h_on j` (total on-line density
  `D_on = ∑_{j ∈ T_on} 1/h_on j`),
* `T_off` reflected pairs of perturbed off-line columns `{ν_off j k, conj (ν_off j k)}` of spacing
  `h_off j` (total two-sided off-line density `D_off = 2 ∑_{j ∈ T_off} 1/h_off j`), and
* a finite set `F`.

Then `WindowPositiveAt Z a` at any single aperture
`a > π D_on + (π / 2) D_off = π (∑_{T_on} 1/h_on j + ∑_{T_off} 1/h_off j)` certifies that every
zero of `Z` lies on the critical line. On-line columns cost `π` per unit density because they sit on
`Re ρ = ½`, whereas off-line column pairs split across `Re ρ ≷ ½` and cost `π/2` per unit total
density. -/
theorem re_eq_half_of_re_W_nonneg_of_split_columns {ι₁ ι₂ : Type*} [DecidableEq ι₁]
    [DecidableEq ι₂] {Z : ZeroConfig}
    (T_on : Finset ι₁) (h_on L_on : ι₁ → ℝ) (hh_on : ∀ i ∈ T_on, 0 < h_on i)
    (ν_on : ι₁ → ℤ → ℝ) (hν_on : ∀ i ∈ T_on, ∀ k : ℤ, |ν_on i k - k * h_on i| ≤ L_on i)
    (T_off : Finset ι₂) (h_off L_off : ι₂ → ℝ) (hh_off : ∀ j ∈ T_off, 0 < h_off j)
    (ν_off : ι₂ → ℤ → ℂ) (hν_off : ∀ j ∈ T_off, ∀ k : ℤ, ‖ν_off j k - k * h_off j‖ ≤ L_off j)
    (him_off : ∀ j ∈ T_off, ∀ k : ℤ, |(ν_off j k).im| ≤ 1 / 2)
    (F : Finset ℂ)
    (hS : ∀ z ∈ Z.carrier,
      (∃ i ∈ T_on, ∃ k : ℤ, gammaOf z = (ν_on i k : ℂ)) ∨
        (∃ j ∈ T_off, ∃ k : ℤ, gammaOf z = ν_off j k ∨ gammaOf z = conj (ν_off j k)) ∨
        z ∈ F)
    {a : ℝ} (ha : π * (∑ i ∈ T_on, (h_on i)⁻¹ + ∑ j ∈ T_off, (h_off j)⁻¹) < a)
    (hpos : WindowPositiveAt Z a) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  classical
  -- Fold each off-line pair `{ν_off j k, conj (ν_off j k)}` into the lower half-plane `Im ≤ 0`
  -- corresponding to `½ ≤ Re z`.
  set ν_right : ι₂ → ℤ → ℂ := fun j k =>
    if 0 < (ν_off j k).im then conj (ν_off j k) else ν_off j k
  have hν_right_b : ∀ j ∈ T_off, ∀ k : ℤ, ‖ν_right j k - k * h_off j‖ ≤ L_off j := by
    intro j hj k
    dsimp [ν_right]
    split_ifs with hpos_im
    · have hreal : conj ((k : ℂ) * (h_off j : ℂ)) = (k : ℂ) * (h_off j : ℂ) := by
        simp [Complex.conj_ofReal]
      rw [← hreal, ← map_sub, Complex.norm_conj]
      exact hν_off j hj k
    · exact hν_off j hj k
  have hν_right_im : ∀ j ∈ T_off, ∀ k : ℤ, |(ν_right j k).im| ≤ 1 / 2 := by
    intro j hj k
    dsimp [ν_right]
    split_ifs
    · rw [Complex.conj_im, abs_neg]; exact him_off j hj k
    · exact him_off j hj k
  set T : Finset (ι₁ ⊕ ι₂) := (T_on.image Sum.inl) ∪ (T_off.image Sum.inr)
  have hdisj : Disjoint (T_on.image (Sum.inl : ι₁ → ι₁ ⊕ ι₂))
      (T_off.image (Sum.inr : ι₂ → ι₁ ⊕ ι₂)) := by
    rw [Finset.disjoint_left]
    rintro _ h1 h2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨j, _, h⟩ := Finset.mem_image.mp h2
    exact Sum.noConfusion h
  set h_sum : ι₁ ⊕ ι₂ → ℝ := Sum.elim h_on h_off
  set L_sum : ι₁ ⊕ ι₂ → ℝ := Sum.elim L_on L_off
  set ν_sum : ι₁ ⊕ ι₂ → ℤ → ℂ := Sum.elim (fun i k => (ν_on i k : ℂ)) ν_right
  have hh_sum : ∀ x ∈ T, 0 < h_sum x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx; exact hh_on i hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx; exact hh_off j hj
  have hν_sum : ∀ x ∈ T, ∀ k : ℤ, ‖ν_sum x k - k * h_sum x‖ ≤ L_sum x := by
    intro x hx k
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      dsimp [ν_sum, h_sum, L_sum]
      rw [show (ν_on i k : ℂ) - (k : ℂ) * (h_on i : ℂ) =
          ((ν_on i k - k * h_on i : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact hν_on i hi k
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact hν_right_b j hj k
  have him_sum : ∀ x ∈ T, ∀ k : ℤ, |(ν_sum x k).im| ≤ 1 / 2 := by
    intro x hx k
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; simp [ν_sum]
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx; exact hν_right_im j hj k
  have hsum_eq : ∑ x ∈ T, (h_sum x)⁻¹ = ∑ i ∈ T_on, (h_on i)⁻¹ + ∑ j ∈ T_off, (h_off j)⁻¹ := by
    rw [Finset.sum_union hdisj,
      Finset.sum_image (fun _ _ _ _ h => Sum.inl.inj h),
      Finset.sum_image (fun _ _ _ _ h => Sum.inr.inj h)]
    rfl
  refine re_eq_half_of_re_W_nonneg_of_one_side_columns T h_sum L_sum hh_sum ν_sum hν_sum him_sum
    (by rwa [hsum_eq]) F (fun z hz hre => ?_) hpos
  have him_z : (gammaOf z).im ≤ 0 := by rw [gammaOf_im_eq]; linarith
  rcases hS z hz with ⟨i, hi, k, hk⟩ | ⟨j, hj, k, hk⟩ | hzF
  · exact Or.inl ⟨Sum.inl i, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi), k, hk⟩
  · refine Or.inl ⟨Sum.inr j, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj), k, ?_⟩
    dsimp [ν_sum, ν_right]
    rcases hk with hk | hk
    · split_ifs with hpos_im
      · exfalso; rw [hk] at him_z; linarith
      · exact hk
    · split_ifs with hpos_im
      · exact hk
      · have him0 : (ν_off j k).im = 0 := by
          have : (conj (ν_off j k)).im = -(ν_off j k).im := Complex.conj_im _
          rw [hk, this] at him_z
          linarith
        rw [hk, Complex.conj_eq_iff_im.mpr him0]
  · exact Or.inr hzF

/-- **Pure off-line column configurations obey the `πD/2` onset bound (`Γ40` affirmative branch).**
If `Z` consists solely of `T_off` pairs of perturbed off-line columns of total two-sided density
`D = 2 ∑_{j ∈ T_off} 1/h_off j` (plus at most finitely many on-line points `F_on`), then either
`Z` lies on the critical line or `onsetAperture Z ≤ ((π * ∑_{j ∈ T_off} (h_off j)⁻¹ : ℝ) : EReal)`
(`= π D / 2`). In particular, if `Z` contains any off-line zero, its onset aperture is at most
`π D / 2`. -/
theorem onsetAperture_le_half_pi_density_of_all_offLine_columns {ι : Type*} [DecidableEq ι]
    {Z : ZeroConfig} (hZ : TemperedConfig Z) (T_off : Finset ι) (h_off L_off : ι → ℝ)
    (hh_off : ∀ j ∈ T_off, 0 < h_off j) (ν_off : ι → ℤ → ℂ)
    (hν_off : ∀ j ∈ T_off, ∀ k : ℤ, ‖ν_off j k - k * h_off j‖ ≤ L_off j)
    (him_off : ∀ j ∈ T_off, ∀ k : ℤ, |(ν_off j k).im| ≤ 1 / 2) (F : Finset ℂ)
    (hS : ∀ z ∈ Z.carrier,
      (∃ j ∈ T_off, ∃ k : ℤ, gammaOf z = ν_off j k ∨ gammaOf z = conj (ν_off j k)) ∨ z ∈ F)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hoff : ρ₀.re ≠ 1 / 2) :
    onsetAperture Z ≤ ((π * ∑ j ∈ T_off, (h_off j)⁻¹ : ℝ) : EReal) := by
  set B : ℝ := π * ∑ j ∈ T_off, (h_off j)⁻¹
  have hB0 : 0 ≤ B :=
    mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun j hj => (inv_pos.mpr (hh_off j hj)).le)
  by_contra hgt
  push Not at hgt
  cases hstar : onsetAperture Z with
  | bot =>
    have h0 := zero_le_onsetAperture Z
    rw [hstar] at h0
    exact absurd h0 (by decide)
  | top =>
    have hon := (onsetAperture_eq_top_iff_onLine hZ).mp hstar
    exact hoff (hon ρ₀ hρ₀)
  | coe b =>
    rw [hstar, EReal.coe_lt_coe_iff] at hgt
    have hb0 : 0 ≤ b := le_trans hB0 hgt.le
    have hpos : WindowPositiveAt Z b := (windowPositiveAt_iff_le_onsetAperture hZ hb0).mpr
      (by rw [hstar])
    have hon := re_eq_half_of_re_W_nonneg_of_split_columns
      (∅ : Finset Unit) (fun _ => 1) (fun _ => 0) (by simp) (fun _ _ => 0) (by simp)
      T_off h_off L_off hh_off ν_off hν_off him_off F
      (fun z hz => Or.inr (hS z hz)) (by simpa [B] using hgt) hpos
    exact hoff (hon ρ₀ hρ₀)

/-- **Universal `(g − ½) log q` threshold for `2g` curve columns (`Γ36` / `Γ40`).** Under the exact
hypotheses of `PositivityCertifiesColumnConfigurations.re_eq_half_of_re_W_nonneg_of_curve_columns`
(`g ≥ 1`, `q > 1`, `2g` columns of spacing `2π / log q` and depths `|δ_j| ≤ ½`), window positivity
at any single aperture `a > (g − ½) log q` (lag `2a > (2g − 1) log q`) already puts every zero on
the critical line: any off-line zero forces its partner into `Re ρ < ½`, removing at least one
column from `{½ ≤ Re ρ}` and dropping the right-half-plane column count to at most `2g − 1`. -/
theorem re_eq_half_of_re_W_nonneg_of_curve_columns_improved {Z : ZeroConfig} {g : ℕ} (hg : 1 ≤ g)
    {q : ℝ} (hq : 1 < q) (θ δ : Fin (2 * g) → ℝ) (hδ : ∀ j, |δ j| ≤ 1 / 2)
    (hS : ∀ z ∈ Z.carrier, ∃ j : Fin (2 * g), ∃ k : ℤ,
      gammaOf z = (((θ j + 2 * π * k) / Real.log q : ℝ) : ℂ) - I * δ j)
    {a : ℝ} (ha : ((g : ℝ) - 1 / 2) * Real.log q < a) (hpos : WindowPositiveAt Z a) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  classical
  intro ρ hρ
  by_contra hoff
  have hl : 0 < Real.log q := Real.log_pos hq
  -- Exhibit a point strictly in the open left half-plane `Re < ½`, forcing some `δ j₀ < 0`.
  set ρ_left := if ρ.re < 1 / 2 then ρ else reflect ρ
  have hρ_left : ρ_left ∈ Z.carrier := by
    dsimp [ρ_left]; split_ifs; exacts [hρ, Z.reflect_mem ρ hρ]
  have hre_left : ρ_left.re < 1 / 2 := by
    dsimp [ρ_left]
    split_ifs with hlt
    · exact hlt
    · have href : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
      have hgt : 1 / 2 < ρ.re := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hoff)
      linarith
  obtain ⟨j₀, k₀, hk₀⟩ := hS ρ_left hρ_left
  have hδ_neg : δ j₀ < 0 := by
    have him := congrArg Complex.im hk₀
    rw [gammaOf_im_eq] at him
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_sub, zero_add] at him
    linarith
  set T_pos : Finset (Fin (2 * g)) := Finset.univ.filter fun j => 0 ≤ δ j
  have hj₀_not : j₀ ∉ T_pos := by
    simp only [T_pos, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact hδ_neg
  have hcard_lt : T_pos.card < 2 * g := by
    calc T_pos.card < (Finset.univ : Finset (Fin (2 * g))).card :=
          Finset.card_lt_card ⟨Finset.subset_univ _, fun hsub => hj₀_not (hsub (Finset.mem_univ j₀))⟩
      _ = 2 * g := Fintype.card_fin (2 * g)
  have hcard_le : (T_pos.card : ℝ) ≤ 2 * (g : ℝ) - 1 := by
    have hnat : T_pos.card ≤ 2 * g - 1 := by omega
    have hcast : ((2 * g - 1 : ℕ) : ℝ) = 2 * (g : ℝ) - 1 := by
      have : 1 ≤ 2 * g := by omega
      rw [Nat.cast_sub this, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    exact hcast ▸ (Nat.cast_le.mpr hnat)
  set ν : Fin (2 * g) → ℤ → ℂ := fun j k =>
    (((θ j + 2 * π * k) / Real.log q : ℝ) : ℂ) - I * δ j
  have hν : ∀ j ∈ T_pos, ∀ k : ℤ,
      ‖ν j k - k * ((2 * π / Real.log q : ℝ) : ℂ)‖ ≤ |θ j| / Real.log q + 1 / 2 := by
    intro j _ k
    have e : ν j k - k * ((2 * π / Real.log q : ℝ) : ℂ) =
        ((θ j / Real.log q : ℝ) : ℂ) - I * δ j := by
      dsimp [ν]; push_cast; field_simp; ring
    rw [e]
    calc ‖((θ j / Real.log q : ℝ) : ℂ) - I * δ j‖
        ≤ ‖((θ j / Real.log q : ℝ) : ℂ)‖ + ‖I * δ j‖ := norm_sub_le _ _
      _ = |θ j| / Real.log q + |δ j| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hl, norm_mul,
            Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |θ j| / Real.log q + 1 / 2 := by linarith [hδ j]
  have him : ∀ j ∈ T_pos, ∀ k, |(ν j k).im| ≤ 1 / 2 := by
    intro j _ k
    dsimp [ν]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_sub, zero_add, abs_neg]
    exact hδ j
  have hsum_le : π * ∑ _j ∈ T_pos, (2 * π / Real.log q)⁻¹ ≤ ((g : ℝ) - 1 / 2) * Real.log q := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hval : π * ((T_pos.card : ℝ) * (2 * π / Real.log q)⁻¹) =
        (T_pos.card : ℝ) * (Real.log q / 2) := by field_simp
    rw [hval]
    calc (T_pos.card : ℝ) * (Real.log q / 2)
        ≤ (2 * (g : ℝ) - 1) * (Real.log q / 2) :=
          mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = ((g : ℝ) - 1 / 2) * Real.log q := by ring
  have hon := re_eq_half_of_re_W_nonneg_of_one_side_columns T_pos
    (fun _ => 2 * π / Real.log q) (fun j => |θ j| / Real.log q + 1 / 2)
    (fun _ _ => by positivity) ν hν him (lt_of_le_of_lt hsum_le ha) ∅
    (fun z hz hre => by
      obtain ⟨j, k, hk⟩ := hS z hz
      have hδ_nonneg : 0 ≤ δ j := by
        have him_z := congrArg Complex.im hk
        rw [gammaOf_im_eq] at him_z
        simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, zero_mul, one_mul, zero_sub, zero_add] at him_z
        linarith
      exact Or.inl ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hδ_nonneg⟩, k, hk⟩) hpos
  exact hoff (hon ρ hρ)

/-! ### 4. Sharpness: mixed `2g`-column counterexample with `onsetAperture = (g − ½)ℓ > πD/2` -/

private theorem norm_weilTest_diag_le {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : ℝ) : ‖EF.weilTest f f x‖ ≤ ∫ t, ‖f t‖ ^ 2 := by
  have hn_supp : HasCompactSupport (fun t : ℝ => ‖f t‖ ^ 2) :=
    hfc.mono fun t ht => by contrapose! ht; simp [ht]
  have hn_int : Integrable (fun t : ℝ => ‖f t‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport hn_supp
  have hn_shift : Integrable (fun t : ℝ => ‖f (t - x)‖ ^ 2) := hn_int.comp_sub_right x
  have hprod_int : Integrable (fun t : ℝ => ‖f t * conj (f (t - x))‖) :=
    ((hf.mul (Complex.continuous_conj.comp (hf.comp (continuous_id.sub continuous_const)))).norm
      ).integrable_of_hasCompactSupport (hfc.mono fun t ht => by contrapose! ht; simp [ht])
  rw [weilTest_apply]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ t, ‖f t * conj (f (t - x))‖
      ≤ ∫ t, (‖f t‖ ^ 2 + ‖f (t - x)‖ ^ 2) / 2 := by
        refine integral_mono hprod_int ((hn_int.add hn_shift).div_const 2) fun t => ?_
        rw [norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖f t‖ - ‖f (t - x)‖)]
    _ = ((∫ t, ‖f t‖ ^ 2) + ∫ t, ‖f (t - x)‖ ^ 2) / 2 := by
        rw [integral_div, integral_add hn_int hn_shift]
    _ = ∫ t, ‖f t‖ ^ 2 := by
        rw [integral_sub_right_eq_self (fun t : ℝ => ‖f t‖ ^ 2) x]; ring

private theorem re_integral_mul_conj_self_eq_norm_sq (f : ℝ → ℂ) :
    (∫ t, f t * conj (f t)).re = ∫ t, ‖f t‖ ^ 2 := by
  have hpt : (fun t => f t * conj (f t)) = fun t => ((‖f t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hpt, integral_complex_ofReal, Complex.ofReal_re]

/-- **Mixed `2g`-column configuration (`g ≥ 2`).** Let `N = 2g − 1` and `L = Nℓ`. The points
`verticalLatticePoint L 0 m` with `N ∤ m` form `N − 1 = 2g − 2` simple on-line columns of spacing
`2π/ℓ`, and `offLineLatticeConfig hℓ hδ hδ'` adds `2` simple off-line columns of spacing `2π/ℓ` at
`Re ρ = ½ ± δ`, giving `2g` simple columns of total density `D = gℓ/π` (`πD/2 = (g/2)ℓ`). -/
def mixedGenusColumnConfig {g : ℕ} (hg : 2 ≤ g) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) : ZeroConfig where
  carrier := {ρ : ℂ | ∃ m : ℤ, ¬ (((2 * g - 1 : ℕ) : ℤ) ∣ m) ∧
      ρ = verticalLatticePoint (((2 * g - 1 : ℕ) : ℝ) * ℓ) 0 m} ∪
    (offLineLatticeConfig hℓ hδ hδ').carrier
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro _ (⟨m, _, rfl⟩ | h)
    · simp only [verticalLatticePoint]; norm_num
    · exact (offLineLatticeConfig hℓ hδ hδ').strip _ h
  reflect_mem := by
    rintro _ (⟨m, hm, rfl⟩ | h)
    · exact Or.inl ⟨m, hm, by rw [reflect_verticalLatticePoint, neg_zero]⟩
    · exact Or.inr ((offLineLatticeConfig hℓ hδ hδ').reflect_mem _ h)
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    have hN : (0 : ℝ) < ((2 * g - 1 : ℕ) : ℝ) := by
      have : 0 < 2 * g - 1 := by omega
      exact_mod_cast this
    have hL : 0 < ((2 * g - 1 : ℕ) : ℝ) * ℓ := mul_pos hN hℓ
    have hF1 := (finite_latticeWindow (h := 2 * π / (((2 * g - 1 : ℕ) : ℝ) * ℓ))
      (by positivity) T₁ T₂).image (verticalLatticePoint (((2 * g - 1 : ℕ) : ℝ) * ℓ) 0)
    have hF2 := (offLineLatticeConfig hℓ hδ hδ').finite_window T₁ T₂
    refine (hF1.union hF2).subset ?_
    rintro ρ ⟨⟨m, _, rfl⟩ | h, h1, h2⟩
    · exact Or.inl ⟨m, ⟨h1, h2⟩, rfl⟩
    · exact Or.inr ⟨h, h1, h2⟩

/-- Phase shifts of the `2g` columns of `mixedGenusColumnConfig`. -/
def mixedGenusTheta (g : ℕ) (j : Fin (2 * g)) : ℝ :=
  if j.1 = 0 ∨ j.1 = 1 then 0 else 2 * π * ((j.1 - 1 : ℕ) : ℝ) / ((2 * g - 1 : ℕ) : ℝ)

/-- Signed depths of the `2g` columns of `mixedGenusColumnConfig`. -/
def mixedGenusDelta (g : ℕ) (δ : ℝ) (j : Fin (2 * g)) : ℝ :=
  if j.1 = 0 then δ else if j.1 = 1 then -δ else 0

theorem abs_mixedGenusDelta_le {g : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (j : Fin (2 * g)) : |mixedGenusDelta g δ j| ≤ 1 / 2 := by
  dsimp [mixedGenusDelta]
  split_ifs
  · rw [abs_of_pos hδ]; exact hδ'
  · rw [abs_neg, abs_of_pos hδ]; exact hδ'
  · simp

/-- `mixedGenusColumnConfig` is a `2g`-column configuration of spacing `2π/ℓ` (`ℓ = log(e^ℓ)`). -/
theorem mixedGenusColumnConfig_mem_curve_columns {g : ℕ} (hg : 2 ≤ g) {ℓ δ : ℝ} (hℓ : 0 < ℓ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∀ z ∈ (mixedGenusColumnConfig hg hℓ hδ hδ').carrier, ∃ j : Fin (2 * g), ∃ k : ℤ,
      gammaOf z = (((mixedGenusTheta g j + 2 * π * k) / ℓ : ℝ) : ℂ) -
        I * mixedGenusDelta g δ j := by
  set N : ℕ := 2 * g - 1
  have hN_pos : 0 < N := by omega
  have hN_int : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN_pos
  have hN_real : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  rintro z (⟨m, hm_ndvd, rfl⟩ | (⟨k, rfl⟩ | ⟨k, rfl⟩))
  · set r : ℤ := m % (N : ℤ)
    set k : ℤ := m / (N : ℤ)
    have hr0 : 0 ≤ r := Int.emod_nonneg m hN_int.ne'
    have hr_lt : r < (N : ℤ) := Int.emod_lt_of_pos m hN_int
    have hdiv : (N : ℤ) * k + r = m := Int.ediv_add_emod m (N : ℤ)
    have hr_ne : r ≠ 0 := fun hr_zero => hm_ndvd ⟨k, by linarith⟩
    have hr1 : 1 ≤ r := by omega
    set idx : ℕ := r.toNat + 1
    have hidx_ge : 2 ≤ idx := by omega
    have hidx_lt : idx < 2 * g := by omega
    refine ⟨⟨idx, hidx_lt⟩, k, ?_⟩
    have hj01 : ¬ (idx = 0 ∨ idx = 1) := by omega
    have hj0 : idx ≠ 0 := by omega
    have hj1 : idx ≠ 1 := by omega
    have hsub1 : (idx - 1 : ℕ) = r.toNat := by omega
    have hr_cast : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by
      have : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
      exact_mod_cast this
    have hm_real : (m : ℝ) = (N : ℝ) * (k : ℝ) + (r : ℝ) := by exact_mod_cast hdiv.symm
    rw [gammaOf_verticalLatticePoint]
    dsimp [mixedGenusTheta, mixedGenusDelta]
    rw [if_neg hj01, if_neg hj0, if_neg hj1, hsub1, hr_cast]
    have hℓ_ne : ℓ ≠ 0 := hℓ.ne'
    have hN_ne : (N : ℝ) ≠ 0 := hN_real.ne'
    have hord : (m : ℝ) * (2 * π / ((N : ℝ) * ℓ)) =
        (2 * π * (r : ℝ) / (N : ℝ) + 2 * π * (k : ℝ)) / ℓ := by
      rw [hm_real]; field_simp; ring
    change ((((m : ℝ) * (2 * π / ((N : ℝ) * ℓ)) : ℝ) : ℂ) - I * (0 : ℝ)) =
      ((((2 * π * (r : ℝ) / (N : ℝ) + 2 * π * (k : ℝ)) / ℓ : ℝ) : ℂ) - I * (0 : ℝ))
    rw [hord]
  · refine ⟨⟨0, by omega⟩, k, ?_⟩
    rw [gammaOf_verticalLatticePoint]
    dsimp [mixedGenusTheta, mixedGenusDelta]
    rw [if_pos (Or.inl rfl), if_pos rfl, zero_add]
    have hord : (k : ℝ) * (2 * π / ℓ) = 2 * π * (k : ℝ) / ℓ := by ring
    rw [hord]
  · refine ⟨⟨1, by omega⟩, k, ?_⟩
    rw [gammaOf_verticalLatticePoint]
    dsimp [mixedGenusTheta, mixedGenusDelta]
    rw [if_pos (Or.inr rfl), if_neg (by decide), if_pos rfl, zero_add]
    have hord : (k : ℝ) * (2 * π / ℓ) = 2 * π * (k : ℝ) / ℓ := by ring
    rw [hord]

/-- `mixedGenusColumnConfig` is tempered. -/
theorem temperedConfig_mixedGenusColumnConfig {g : ℕ} (hg : 2 ≤ g) {ℓ δ : ℝ} (hℓ : 0 < ℓ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    TemperedConfig (mixedGenusColumnConfig hg hℓ hδ hδ') := by
  set Z := mixedGenusColumnConfig hg hℓ hδ hδ'
  set N : ℕ := 2 * g - 1
  have hN : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hL : 0 < (N : ℝ) * ℓ := mul_pos hN hℓ
  set Z_L := onLineLatticeConfig hL
  set Z_off := offLineLatticeConfig hℓ hδ hδ'
  have h1 : Summable (Z_L.carrier.indicator fun ρ =>
      (Z_L.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
    summable_subtype_iff_indicator.mp (temperedConfig_onLineLatticeConfig hL)
  have h2 : Summable (Z_off.carrier.indicator fun ρ =>
      (Z_off.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
    summable_subtype_iff_indicator.mp (temperedConfig_offLineLatticeConfig hℓ hδ hδ')
  rw [TemperedConfig, ← summable_subtype_iff_indicator]
  refine Summable.of_nonneg_of_le (fun z => Set.indicator_nonneg (fun ρ _ => ?_) z)
    (fun z => ?_) (h1.add h2)
  · have := Complex.normSq_nonneg (gammaOf ρ); positivity
  · have hden : 0 < 1 + Complex.normSq (gammaOf z) := by
      linarith [Complex.normSq_nonneg (gammaOf z)]
    have h1_nonneg : 0 ≤ Z_L.carrier.indicator
        (fun ρ => (Z_L.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) z :=
      Set.indicator_nonneg (fun _ _ => by positivity) z
    have h2_nonneg : 0 ≤ Z_off.carrier.indicator
        (fun ρ => (Z_off.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) z :=
      Set.indicator_nonneg (fun _ _ => by positivity) z
    by_cases hz : z ∈ Z.carrier
    · rw [Set.indicator_of_mem hz]
      rcases hz with ⟨m, _, rfl⟩ | hz_off
      · have hzL : verticalLatticePoint ((N : ℝ) * ℓ) 0 m ∈ Z_L.carrier := ⟨m, rfl⟩
        rw [Set.indicator_of_mem hzL]
        have hmZ : (Z.mult (verticalLatticePoint ((N : ℝ) * ℓ) 0 m) : ℝ) = 1 := rfl
        have hmL : (Z_L.mult (verticalLatticePoint ((N : ℝ) * ℓ) 0 m) : ℝ) = 2 := rfl
        rw [hmZ, hmL]
        have : 1 / (1 + Complex.normSq (gammaOf (verticalLatticePoint ((N : ℝ) * ℓ) 0 m))) ≤
            2 / (1 + Complex.normSq (gammaOf (verticalLatticePoint ((N : ℝ) * ℓ) 0 m))) := by
          gcongr; norm_num
        linarith
      · rw [Set.indicator_of_mem hz_off]
        have hmZ : (Z.mult z : ℝ) = 1 := rfl
        have hmO : (Z_off.mult z : ℝ) = 1 := rfl
        rw [hmZ, hmO]
        linarith
    · rw [Set.indicator_of_notMem hz]; linarith

/-- **Exact Weil-form decomposition of `mixedGenusColumnConfig`.** For every `C²` compactly
supported window `f`,
`2 * Z.W f f + Z_ℓ.W f f = Z_L.W f f + 2 * Z_off.W f f`,
where `L = (2g − 1)ℓ`, `Z_L = onLineLatticeConfig hL`, `Z_ℓ = onLineLatticeConfig hℓ`, and
`Z_off = offLineLatticeConfig hℓ hδ hδ'`. -/
theorem two_mul_W_mixedGenusColumnConfig_add {g : ℕ} (hg : 2 ≤ g) {ℓ δ : ℝ} (hℓ : 0 < ℓ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    2 * (mixedGenusColumnConfig hg hℓ hδ hδ').W f f + (onLineLatticeConfig hℓ).W f f =
      (onLineLatticeConfig (show 0 < ((2 * g - 1 : ℕ) : ℝ) * ℓ by
          have : 0 < 2 * g - 1 := by omega
          exact mul_pos (by exact_mod_cast this) hℓ)).W f f +
        2 * (offLineLatticeConfig hℓ hδ hδ').W f f := by
  set N : ℕ := 2 * g - 1
  have hN_pos : 0 < N := by omega
  have hN_real : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hL : 0 < (N : ℝ) * ℓ := mul_pos hN_real hℓ
  set Z := mixedGenusColumnConfig hg hℓ hδ hδ'
  set Z_ℓ := onLineLatticeConfig hℓ
  set Z_L := onLineLatticeConfig hL
  set Z_off := offLineLatticeConfig hℓ hδ hδ'
  have hsZ := summable_indicator_pointImage Z (temperedConfig_mixedGenusColumnConfig hg hℓ hδ hδ')
    hf hfc hf hfc
  have hsℓ := summable_indicator_pointImage Z_ℓ (temperedConfig_onLineLatticeConfig hℓ)
    hf hfc hf hfc
  have hsL := summable_indicator_pointImage Z_L (temperedConfig_onLineLatticeConfig hL)
    hf hfc hf hfc
  have hsO := summable_indicator_pointImage Z_off (temperedConfig_offLineLatticeConfig hℓ hδ hδ')
    hf hfc hf hfc
  have hsublat : ∀ m : ℤ, verticalLatticePoint ((N : ℝ) * ℓ) 0 m ∈ Z_ℓ.carrier ↔ (N : ℤ) ∣ m := by
    intro m
    constructor
    · rintro ⟨k, hk⟩
      have him := congrArg Complex.im hk
      simp only [verticalLatticePoint] at him
      have hℓ_ne : ℓ ≠ 0 := hℓ.ne'
      have hN_ne : (N : ℝ) ≠ 0 := hN_real.ne'
      have hπ_ne : π ≠ 0 := Real.pi_ne_zero
      have hmr : (m : ℝ) = (N : ℝ) * (k : ℝ) := by
        field_simp at him; linear_combination him / (2 * π)
      exact ⟨k, by exact_mod_cast hmr⟩
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      apply Complex.ext
      · simp [verticalLatticePoint]
      · simp only [verticalLatticePoint]
        have hℓ_ne : ℓ ≠ 0 := hℓ.ne'
        have hN_ne : (N : ℝ) ≠ 0 := hN_real.ne'
        push_cast; field_simp
  have hdisj_re : ∀ z ∈ Z_off.carrier, z.re ≠ 1 / 2 := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) h <;> simp only [verticalLatticePoint] at h <;> linarith
  have hpt_ind : ∀ z : ℂ,
      2 * Z.carrier.indicator (fun z => (Z.mult z : ℂ)) z +
          Z_ℓ.carrier.indicator (fun z => (Z_ℓ.mult z : ℂ)) z =
        Z_L.carrier.indicator (fun z => (Z_L.mult z : ℂ)) z +
          2 * Z_off.carrier.indicator (fun z => (Z_off.mult z : ℂ)) z := by
    intro z
    by_cases hzO : z ∈ Z_off.carrier
    · have hz_re := hdisj_re z hzO
      have hzL : z ∉ Z_L.carrier := by rintro ⟨m, rfl⟩; exact hz_re (by simp [verticalLatticePoint])
      have hzℓ : z ∉ Z_ℓ.carrier := by rintro ⟨k, rfl⟩; exact hz_re (by simp [verticalLatticePoint])
      have hzZ : z ∈ Z.carrier := Or.inr hzO
      rw [Set.indicator_of_mem hzZ, Set.indicator_of_notMem hzℓ,
        Set.indicator_of_notMem hzL, Set.indicator_of_mem hzO]
      change (2 : ℂ) * 1 + 0 = 0 + 2 * 1; ring
    · by_cases hzL : z ∈ Z_L.carrier
      · obtain ⟨m, rfl⟩ := hzL
        have hmL : verticalLatticePoint ((N : ℝ) * ℓ) 0 m ∈ Z_L.carrier := ⟨m, rfl⟩
        by_cases hdvd : (N : ℤ) ∣ m
        · have hmℓ : verticalLatticePoint ((N : ℝ) * ℓ) 0 m ∈ Z_ℓ.carrier :=
            (hsublat m).mpr hdvd
          have hmZ : verticalLatticePoint ((N : ℝ) * ℓ) 0 m ∉ Z.carrier := by
            rintro (⟨m', hm', heq⟩ | hO)
            · exact hm' ((verticalLatticePoint_injective hL 0 heq) ▸ hdvd)
            · exact hzO hO
          rw [Set.indicator_of_notMem hmZ, Set.indicator_of_mem hmℓ,
            Set.indicator_of_mem hmL, Set.indicator_of_notMem hzO]
          change (2 : ℂ) * 0 + 2 = 2 + 2 * 0; ring
        · have hmℓ : verticalLatticePoint ((N : ℝ) * ℓ) 0 m ∉ Z_ℓ.carrier :=
            fun h => hdvd ((hsublat m).mp h)
          have hmZ : verticalLatticePoint ((N : ℝ) * ℓ) 0 m ∈ Z.carrier :=
            Or.inl ⟨m, hdvd, rfl⟩
          rw [Set.indicator_of_mem hmZ, Set.indicator_of_notMem hmℓ,
            Set.indicator_of_mem hmL, Set.indicator_of_notMem hzO]
          change (2 : ℂ) * 1 + 0 = 2 + 2 * 0; ring
      · have hzℓ : z ∉ Z_ℓ.carrier := by
          rintro ⟨k, rfl⟩
          apply hzL
          have hk : verticalLatticePoint ((N : ℝ) * ℓ) 0 ((N : ℤ) * k) ∈ Z_ℓ.carrier :=
            (hsublat ((N : ℤ) * k)).mpr ⟨k, rfl⟩
          obtain ⟨k', hk'⟩ := hk
          have heq : verticalLatticePoint ((N : ℝ) * ℓ) 0 ((N : ℤ) * k) =
              verticalLatticePoint ℓ 0 k := by
            apply Complex.ext
            · simp [verticalLatticePoint]
            · simp only [verticalLatticePoint]
              have hℓ_ne : ℓ ≠ 0 := hℓ.ne'
              have hN_ne : (N : ℝ) ≠ 0 := hN_real.ne'
              push_cast; field_simp
          exact ⟨(N : ℤ) * k, heq⟩
        have hzZ : z ∉ Z.carrier := by
          rintro (⟨m, _, rfl⟩ | hO)
          · exact hzL ⟨m, rfl⟩
          · exact hzO hO
        rw [Set.indicator_of_notMem hzZ, Set.indicator_of_notMem hzℓ,
          Set.indicator_of_notMem hzL, Set.indicator_of_notMem hzO]
        ring
  rw [W_eq_tsum_indicator Z, W_eq_tsum_indicator Z_ℓ, W_eq_tsum_indicator Z_L,
    W_eq_tsum_indicator Z_off, ← tsum_mul_left, ← tsum_mul_left,
    ← (hsZ.mul_left 2).tsum_add hsℓ, ← hsL.tsum_add (hsO.mul_left 2)]
  refine tsum_congr fun z => ?_
  have h := congrArg (fun c : ℂ => c * pointImage f f z) (hpt_ind z)
  dsimp only at h
  linear_combination h

/-- **Positivity up to `(g − ½)ℓ` for shallow `mixedGenusColumnConfig`.** Whenever
`4 * (2g − 2) * (cosh(δ (2g − 1) ℓ) − 1) ≤ 2g − 1`, the `2g`-column configuration
`mixedGenusColumnConfig` is window-positive at half-width `(g − ½)ℓ`! -/
theorem windowPositiveAt_mixedGenusColumnConfig {g : ℕ} (hg : 2 ≤ g) {ℓ δ : ℝ} (hℓ : 0 < ℓ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hsmall : 4 * (((2 * g - 1 : ℕ) : ℝ) - 1) *
      (Real.cosh (δ * (((2 * g - 1 : ℕ) : ℝ) * ℓ)) - 1) ≤ ((2 * g - 1 : ℕ) : ℝ)) :
    WindowPositiveAt (mixedGenusColumnConfig hg hℓ hδ hδ') (((g : ℝ) - 1 / 2) * ℓ) := by
  set N : ℕ := 2 * g - 1
  have hN_pos : 0 < N := by omega
  have hN_real : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  set L : ℝ := (N : ℝ) * ℓ
  have hL : 0 < L := mul_pos hN_real hℓ
  have ha_eq : ((g : ℝ) - 1 / 2) * ℓ = L / 2 := by
    have hN_eq : (N : ℝ) = 2 * (g : ℝ) - 1 := by
      have : 1 ≤ 2 * g := by omega
      dsimp [N]; rw [Nat.cast_sub this, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    dsimp [L]; rw [hN_eq]; ring
  rw [ha_eq]
  intro f hf hfs
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hrel := two_mul_W_mixedGenusColumnConfig_add hg hℓ hδ hδ' hf hfc
  set Z := mixedGenusColumnConfig hg hℓ hδ hδ'
  set Z_ℓ := onLineLatticeConfig hℓ
  set Z_L := onLineLatticeConfig hL
  set Z_off := offLineLatticeConfig hℓ hδ hδ'
  have hWL : (Z_L.W f f).re = 2 * L * ∫ t, ‖f t‖ ^ 2 := by
    rw [W_onLineLatticeConfig_of_le_nyquist hL hf hf.continuous hfs hfs,
      show (2 : ℂ) * (L : ℂ) * ∫ t, f t * conj (f t) =
        ((2 * L : ℝ) : ℂ) * ∫ t, f t * conj (f t) by push_cast; ring,
      Complex.re_ofReal_mul, re_integral_mul_conj_self_eq_norm_sq]
  have hWℓ : 0 ≤ (Z_ℓ.W f f).re := re_W_onLineLatticeConfig_nonneg hℓ f
  -- Bound `‖Z_off.W f f - Z_ℓ.W f f‖` by summing the `2 * (N - 1)` nonzero lags `m * ℓ` (`|m| < N`).
  have hKc : Continuous (EF.weilTest f f) := (EF.weilTest_contDiff hf hf.continuous hfc).continuous
  have hKs : tsupport (EF.weilTest f f) ⊆ Icc (-L) L := EF.tsupport_weilTest_subset hfs hfs
  set S_lags : Finset ℤ := (Finset.Ioo (-(N : ℤ)) (N : ℤ)).erase 0
  have hvan : ∀ (φ : ℤ → ℂ), φ 0 = 0 → ∀ m ∉ S_lags, EF.weilTest f f (m * ℓ) * φ m = 0 := by
    intro φ hφ0 m hm
    by_cases hm0 : m = 0
    · rw [hm0, hφ0, mul_zero]
    · have hnotIoo : m ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ) :=
        fun hmem => hm (Finset.mem_erase.mpr ⟨hm0, hmem⟩)
      have habs_m : (N : ℝ) ≤ |(m : ℝ)| := by
        rw [Finset.mem_Ioo, not_and_or, not_lt, not_lt] at hnotIoo
        rcases hnotIoo with hle | hge
        · exact le_abs.mpr (Or.inr (by have : (m : ℝ) ≤ -(N : ℝ) := by exact_mod_cast hle
                                       linarith))
        · exact le_abs.mpr (Or.inl (by exact_mod_cast hge))
      have habs_L : L ≤ |(m : ℝ) * ℓ| := by
        rw [abs_mul, abs_of_pos hℓ]
        exact mul_le_mul_of_nonneg_right habs_m hℓ.le
      rw [eq_zero_of_tsupport_subset_Icc hKc hKs habs_L, zero_mul]
  have hW_diff : Z_off.W f f - Z_ℓ.W f f =
      (ℓ : ℂ) * ∑ m ∈ S_lags, EF.weilTest f f (m * ℓ) *
        (((2 * (Real.cosh (δ * (m * ℓ)) - 1) : ℝ)) : ℂ) := by
    rw [W_offLineLatticeConfig hℓ hδ hδ' (A := L) hf hf.continuous hfs hfs,
      W_onLineLatticeConfig hℓ (A := L) hf hf.continuous hfs hfs]
    have hs1 : ∑' m : ℤ, EF.weilTest f f (m * ℓ) * (Real.exp (δ * (m * ℓ)) : ℂ) =
        EF.weilTest f f 0 + ∑ m ∈ S_lags,
          EF.weilTest f f (m * ℓ) * (Real.exp (δ * (m * ℓ)) : ℂ) := by
      have hv : ∀ m ∉ insert (0 : ℤ) S_lags,
          EF.weilTest f f (m * ℓ) * (Real.exp (δ * (m * ℓ)) : ℂ) = 0 := by
        intro m hm
        have hm0 : m ≠ 0 := fun h => hm (h ▸ Finset.mem_insert_self 0 S_lags)
        have hmS : m ∉ S_lags := fun h => hm (Finset.mem_insert_of_mem h)
        have hnotIoo : m ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ) :=
          fun hmem => hmS (Finset.mem_erase.mpr ⟨hm0, hmem⟩)
        have habs_m : (N : ℝ) ≤ |(m : ℝ)| := by
          rw [Finset.mem_Ioo, not_and_or, not_lt, not_lt] at hnotIoo
          rcases hnotIoo with hle | hge
          · exact le_abs.mpr (Or.inr (by have : (m : ℝ) ≤ -(N : ℝ) := by exact_mod_cast hle
                                         linarith))
          · exact le_abs.mpr (Or.inl (by exact_mod_cast hge))
        rw [eq_zero_of_tsupport_subset_Icc hKc hKs
          (by rw [abs_mul, abs_of_pos hℓ]; exact mul_le_mul_of_nonneg_right habs_m hℓ.le),
          zero_mul]
      rw [tsum_eq_sum hv, Finset.sum_insert (Finset.notMem_erase 0 _)]
      simp
    have hs2 : ∑' m : ℤ, EF.weilTest f f (m * ℓ) * (Real.exp (-δ * (m * ℓ)) : ℂ) =
        EF.weilTest f f 0 + ∑ m ∈ S_lags,
          EF.weilTest f f (m * ℓ) * (Real.exp (-δ * (m * ℓ)) : ℂ) := by
      have hv : ∀ m ∉ insert (0 : ℤ) S_lags,
          EF.weilTest f f (m * ℓ) * (Real.exp (-δ * (m * ℓ)) : ℂ) = 0 := by
        intro m hm
        have hm0 : m ≠ 0 := fun h => hm (h ▸ Finset.mem_insert_self 0 S_lags)
        have hmS : m ∉ S_lags := fun h => hm (Finset.mem_insert_of_mem h)
        have hnotIoo : m ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ) :=
          fun hmem => hmS (Finset.mem_erase.mpr ⟨hm0, hmem⟩)
        have habs_m : (N : ℝ) ≤ |(m : ℝ)| := by
          rw [Finset.mem_Ioo, not_and_or, not_lt, not_lt] at hnotIoo
          rcases hnotIoo with hle | hge
          · exact le_abs.mpr (Or.inr (by have : (m : ℝ) ≤ -(N : ℝ) := by exact_mod_cast hle
                                         linarith))
          · exact le_abs.mpr (Or.inl (by exact_mod_cast hge))
        rw [eq_zero_of_tsupport_subset_Icc hKc hKs
          (by rw [abs_mul, abs_of_pos hℓ]; exact mul_le_mul_of_nonneg_right habs_m hℓ.le),
          zero_mul]
      rw [tsum_eq_sum hv, Finset.sum_insert (Finset.notMem_erase 0 _)]
      simp
    have hs0 : ∑' m : ℤ, EF.weilTest f f (m * ℓ) =
        EF.weilTest f f 0 + ∑ m ∈ S_lags, EF.weilTest f f (m * ℓ) := by
      have hv : ∀ m ∉ insert (0 : ℤ) S_lags, EF.weilTest f f (m * ℓ) = 0 := by
        intro m hm
        have hm0 : m ≠ 0 := fun h => hm (h ▸ Finset.mem_insert_self 0 S_lags)
        have hmS : m ∉ S_lags := fun h => hm (Finset.mem_insert_of_mem h)
        have hnotIoo : m ∉ Finset.Ioo (-(N : ℤ)) (N : ℤ) :=
          fun hmem => hmS (Finset.mem_erase.mpr ⟨hm0, hmem⟩)
        have habs_m : (N : ℝ) ≤ |(m : ℝ)| := by
          rw [Finset.mem_Ioo, not_and_or, not_lt, not_lt] at hnotIoo
          rcases hnotIoo with hle | hge
          · exact le_abs.mpr (Or.inr (by have : (m : ℝ) ≤ -(N : ℝ) := by exact_mod_cast hle
                                         linarith))
          · exact le_abs.mpr (Or.inl (by exact_mod_cast hge))
        exact eq_zero_of_tsupport_subset_Icc hKc hKs
          (by rw [abs_mul, abs_of_pos hℓ]; exact mul_le_mul_of_nonneg_right habs_m hℓ.le)
      rw [tsum_eq_sum hv, Finset.sum_insert (Finset.notMem_erase 0 _)]
      simp
    rw [hs1, hs2, hs0]
    have hsum_combine :
        (∑ m ∈ S_lags, EF.weilTest f f (m * ℓ) * (Real.exp (δ * (m * ℓ)) : ℂ)) +
          (∑ m ∈ S_lags, EF.weilTest f f (m * ℓ) * (Real.exp (-δ * (m * ℓ)) : ℂ)) -
          2 * ∑ m ∈ S_lags, EF.weilTest f f (m * ℓ) =
        ∑ m ∈ S_lags, EF.weilTest f f (m * ℓ) *
          (((2 * (Real.cosh (δ * (m * ℓ)) - 1) : ℝ)) : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Real.cosh_eq, show -δ * ((m : ℝ) * ℓ) = -(δ * ((m : ℝ) * ℓ)) by ring]
      push_cast; ring
    linear_combination (ℓ : ℂ) * hsum_combine
  have hcard_S : (S_lags.card : ℝ) ≤ 2 * ((N : ℝ) - 1) := by
    have hsub : Finset.Ioo (-(N : ℤ)) (N : ℤ) ⊆
        (Finset.range (2 * N - 1)).image (fun i : ℕ => (i : ℤ) - ((N : ℤ) - 1)) := by
      intro m hm
      rw [Finset.mem_Ioo] at hm
      rw [Finset.mem_image]
      refine ⟨(m + ((N : ℤ) - 1)).toNat, Finset.mem_range.mpr (by omega), by omega⟩
    have hcard_Ioo : (Finset.Ioo (-(N : ℤ)) (N : ℤ)).card ≤ 2 * N - 1 :=
      (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_range]))
    have h0_mem : (0 : ℤ) ∈ Finset.Ioo (-(N : ℤ)) (N : ℤ) :=
      Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
    have hcard_nat : S_lags.card ≤ 2 * (N - 1) := by
      dsimp [S_lags]
      rw [Finset.card_erase_of_mem h0_mem]
      omega
    have hcast : ((2 * (N - 1) : ℕ) : ℝ) = 2 * ((N : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hN_pos, Nat.cast_one]
    exact hcast ▸ (Nat.cast_le.mpr hcard_nat)
  have hI_nonneg : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hcoshL : 0 ≤ Real.cosh (δ * L) - 1 := by linarith [Real.one_le_cosh (δ * L)]
  have hdiff_norm : ‖Z_off.W f f - Z_ℓ.W f f‖ ≤
      4 * ((N : ℝ) - 1) * ℓ * (Real.cosh (δ * L) - 1) * ∫ t, ‖f t‖ ^ 2 := by
    rw [hW_diff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le S_lags _) hℓ.le).trans ?_
    have hterm : ∀ m ∈ S_lags,
        ‖EF.weilTest f f (m * ℓ) * (((2 * (Real.cosh (δ * (m * ℓ)) - 1) : ℝ)) : ℂ)‖ ≤
          2 * (Real.cosh (δ * L) - 1) * ∫ t, ‖f t‖ ^ 2 := by
      intro m hm
      have hmIoo := (Finset.mem_erase.mp hm).2
      rw [Finset.mem_Ioo] at hmIoo
      have habs_m : |(m : ℝ)| ≤ (N : ℝ) := abs_le.mpr
        ⟨by exact_mod_cast hmIoo.1.le, by exact_mod_cast hmIoo.2.le⟩
      have hch_m : Real.cosh (δ * ((m : ℝ) * ℓ)) ≤ Real.cosh (δ * L) := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : 0 ≤ δ * L),
          abs_mul, abs_mul, abs_of_pos hδ, abs_of_pos hℓ]
        dsimp [L]
        calc δ * (|(m : ℝ)| * ℓ) ≤ δ * ((N : ℝ) * ℓ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right habs_m hℓ.le) hδ.le
      have hch0 : 0 ≤ 2 * (Real.cosh (δ * ((m : ℝ) * ℓ)) - 1) := by
        linarith [Real.one_le_cosh (δ * ((m : ℝ) * ℓ))]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hch0, mul_comm]
      exact mul_le_mul (by linarith) (norm_weilTest_diag_le hf.continuous hfc _)
        (norm_nonneg _) (by positivity)
    calc ℓ * ∑ m ∈ S_lags,
          ‖EF.weilTest f f (m * ℓ) * (((2 * (Real.cosh (δ * (m * ℓ)) - 1) : ℝ)) : ℂ)‖
        ≤ ℓ * ∑ _m ∈ S_lags, (2 * (Real.cosh (δ * L) - 1) * ∫ t, ‖f t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hℓ.le
      _ = ℓ * ((S_lags.card : ℝ) * (2 * (Real.cosh (δ * L) - 1) * ∫ t, ‖f t‖ ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ℓ * ((2 * ((N : ℝ) - 1)) * (2 * (Real.cosh (δ * L) - 1) * ∫ t, ‖f t‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcard_S (by positivity)) hℓ.le
      _ = 4 * ((N : ℝ) - 1) * ℓ * (Real.cosh (δ * L) - 1) * ∫ t, ‖f t‖ ^ 2 := by ring
  -- Rewrite `2 * Z.W f f = Z_L.W f f + Z_ℓ.W f f + 2 * (Z_off.W f f - Z_ℓ.W f f)` and take `.re`.
  have hident : 2 * Z.W f f = Z_L.W f f + Z_ℓ.W f f + 2 * (Z_off.W f f - Z_ℓ.W f f) := by
    linear_combination hrel
  have hre_ident : 2 * (Z.W f f).re =
      (Z_L.W f f).re + (Z_ℓ.W f f).re + 2 * (Z_off.W f f - Z_ℓ.W f f).re := by
    have := congrArg Complex.re hident
    simpa [Complex.add_re, Complex.sub_re] using this
  have hre_diff : -(4 * ((N : ℝ) - 1) * ℓ * (Real.cosh (δ * L) - 1) * ∫ t, ‖f t‖ ^ 2) ≤
      (Z_off.W f f - Z_ℓ.W f f).re := by
    have := neg_abs_le (Z_off.W f f - Z_ℓ.W f f).re
    have habs := (Complex.abs_re_le_norm (Z_off.W f f - Z_ℓ.W f f)).trans hdiff_norm
    linarith
  have hfactor : 0 ≤ 2 * ℓ * ((N : ℝ) - 4 * ((N : ℝ) - 1) * (Real.cosh (δ * L) - 1)) :=
    mul_nonneg (by positivity) (by dsimp [N, L]; linarith)
  have hlb : 2 * ℓ * ((N : ℝ) - 4 * ((N : ℝ) - 1) * (Real.cosh (δ * L) - 1)) * ∫ t, ‖f t‖ ^ 2 ≤
      2 * (Z.W f f).re := by
    rw [hre_ident, hWL]
    have hring : 2 * L * (∫ t, ‖f t‖ ^ 2) -
        2 * (4 * ((N : ℝ) - 1) * ℓ * (Real.cosh (δ * L) - 1) * ∫ t, ‖f t‖ ^ 2) =
        2 * ℓ * ((N : ℝ) - 4 * ((N : ℝ) - 1) * (Real.cosh (δ * L) - 1)) * ∫ t, ‖f t‖ ^ 2 := by
      dsimp [L]; ring
    linarith
  nlinarith [mul_nonneg hfactor hI_nonneg]

/-- **Exact onset aperture of `mixedGenusColumnConfig` (`Γ40` mixed-column counterexample & `Γ36`
sharpness).** For every `g ≥ 2`, `ℓ > 0`, and `0 < δ ≤ ½` satisfying the shallow condition
`4 * (2g − 2) * (cosh(δ (2g − 1) ℓ) − 1) ≤ 2g − 1`, the `2g`-column configuration of total density
`D = gℓ/π` satisfies
`onsetAperture (mixedGenusColumnConfig ...) = ((g − ½)ℓ : EReal) > ((g/2)ℓ : EReal) = (πD/2 : EReal)`.
Thus `πD/2` is **false** for mixed on-line/off-line column configurations, and the universal
`(g − ½) log q` law of `re_eq_half_of_re_W_nonneg_of_curve_columns_improved` is **exact** for every
`g ≥ 2`. -/
theorem onsetAperture_mixedGenusColumnConfig_eq {g : ℕ} (hg : 2 ≤ g) {ℓ δ : ℝ} (hℓ : 0 < ℓ)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hsmall : 4 * (((2 * g - 1 : ℕ) : ℝ) - 1) *
      (Real.cosh (δ * (((2 * g - 1 : ℕ) : ℝ) * ℓ)) - 1) ≤ ((2 * g - 1 : ℕ) : ℝ)) :
    onsetAperture (mixedGenusColumnConfig hg hℓ hδ hδ') = (((g : ℝ) - 1 / 2) * ℓ : EReal) ∧
      (((g : ℝ) / 2) * ℓ : EReal) < onsetAperture (mixedGenusColumnConfig hg hℓ hδ hδ') := by
  set Z := mixedGenusColumnConfig hg hℓ hδ hδ'
  have hg_real : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have ha0 : 0 ≤ ((g : ℝ) - 1 / 2) * ℓ := mul_nonneg (by linarith) hℓ.le
  have hge : (((g : ℝ) - 1 / 2) * ℓ : EReal) ≤ onsetAperture Z :=
    le_onsetAperture_of_windowPositiveAt ha0 (windowPositiveAt_mixedGenusColumnConfig hg hℓ hδ hδ'
      hsmall)
  have hle : onsetAperture Z ≤ (((g : ℝ) - 1 / 2) * ℓ : EReal) := by
    refine sSup_le ?_
    rintro _ ⟨a, _, rfl, hpos⟩
    rw [EReal.coe_le_coe_iff]
    by_contra hgt
    push Not at hgt
    have hq : 1 < Real.exp ℓ := Real.one_lt_exp_iff.mpr hℓ
    have hS : ∀ z ∈ Z.carrier, ∃ j : Fin (2 * g), ∃ k : ℤ,
        gammaOf z = (((mixedGenusTheta g j + 2 * π * k) / Real.log (Real.exp ℓ) : ℝ) : ℂ) -
          I * mixedGenusDelta g δ j := by
      simpa only [Real.log_exp] using mixedGenusColumnConfig_mem_curve_columns hg hℓ hδ hδ'
    have hon := re_eq_half_of_re_W_nonneg_of_curve_columns_improved (by omega : 1 ≤ g) hq
      (mixedGenusTheta g) (mixedGenusDelta g δ) (abs_mixedGenusDelta_le hδ hδ') hS
      (by rwa [Real.log_exp]) hpos
    have hmem : verticalLatticePoint ℓ δ 0 ∈ Z.carrier := Or.inr (Or.inl ⟨0, rfl⟩)
    have hre := hon _ hmem
    simp only [verticalLatticePoint] at hre
    linarith
  have heq : onsetAperture Z = (((g : ℝ) - 1 / 2) * ℓ : EReal) := le_antisymm hle hge
  refine ⟨heq, ?_⟩
  rw [heq, EReal.coe_lt_coe_iff]
  nlinarith
