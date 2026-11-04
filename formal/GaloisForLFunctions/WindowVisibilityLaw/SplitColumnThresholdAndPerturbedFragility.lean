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

/-! ### 5. Two-sided perturbation law for off-line columns (`Π29`) -/

/-- **Single-defect off-line column configuration.** Replaces the `k = 0` pair `½ ± δ` of
`offLineLatticeConfig hL hδ hδ'` by the `ε`-shifted pair `½ ± δ + iε` (`0 < ε ≤ π/L`). -/
def singleDefectOffLineLattice {L δ ε : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (_hε : 0 < ε) (_hεL : ε ≤ π / L) : ZeroConfig where
  carrier := {ρ : ℂ | ∃ k : ℤ, k ≠ 0 ∧
      (ρ = verticalLatticePoint L δ k ∨ ρ = verticalLatticePoint L (-δ) k)} ∪
    ({offLinePoint δ ε, offLinePoint (-δ) ε} : Set ℂ)
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro _ (⟨k, _, rfl | rfl⟩ | h)
    · simp only [verticalLatticePoint]; constructor <;> linarith
    · simp only [verticalLatticePoint]; constructor <;> linarith
    · rcases h with rfl | h'
      · simp only [offLinePoint]; constructor <;> linarith
      · rw [Set.mem_singleton_iff] at h'; subst h'
        simp only [offLinePoint]; constructor <;> linarith
  reflect_mem := by
    rintro _ (⟨k, hk, rfl | rfl⟩ | h)
    · exact Or.inl ⟨k, hk, Or.inr (reflect_verticalLatticePoint L δ k)⟩
    · exact Or.inl ⟨k, hk, Or.inl (by rw [reflect_verticalLatticePoint, neg_neg])⟩
    · rcases h with rfl | h'
      · exact Or.inr (Or.inr (by rw [reflect_offLinePoint]; rfl))
      · rw [Set.mem_singleton_iff] at h'; subst h'
        exact Or.inr (Or.inl (by rw [reflect_offLinePoint, neg_neg]))
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    have hF1 := (offLineLatticeConfig hL hδ hδ').finite_window T₁ T₂
    have hF2 : ({offLinePoint δ ε, offLinePoint (-δ) ε} : Set ℂ).Finite :=
      (Set.finite_singleton _).insert _
    refine (hF1.union hF2).subset ?_
    rintro ρ ⟨⟨k, _, rfl | rfl⟩ | h, h1, h2⟩
    · exact Or.inl ⟨Or.inl ⟨k, rfl⟩, h1, h2⟩
    · exact Or.inl ⟨Or.inr ⟨k, rfl⟩, h1, h2⟩
    · exact Or.inr h

theorem temperedConfig_singleDefectOffLineLattice {L δ ε : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hε : 0 < ε) (hεL : ε ≤ π / L) :
    TemperedConfig (singleDefectOffLineLattice hL hδ hδ' hε hεL) := by
  set Z := singleDefectOffLineLattice hL hδ hδ' hε hεL
  set Z_lat := offLineLatticeConfig hL hδ hδ'
  set Z_iso := isolatedPairConfig hL hδ hδ' ε
  have h1 : Summable (Z_lat.carrier.indicator fun ρ =>
      (Z_lat.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
    summable_subtype_iff_indicator.mp (temperedConfig_offLineLatticeConfig hL hδ hδ')
  have h2 : Summable (Z_iso.carrier.indicator fun ρ =>
      (Z_iso.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
    summable_subtype_iff_indicator.mp (temperedConfig_isolatedPairConfig hL hδ hδ' ε)
  rw [TemperedConfig, ← summable_subtype_iff_indicator]
  refine Summable.of_nonneg_of_le (fun z => Set.indicator_nonneg (fun ρ _ => ?_) z)
    (fun z => ?_) (h1.add h2)
  · have := Complex.normSq_nonneg (gammaOf ρ); positivity
  · have hden : 0 < 1 + Complex.normSq (gammaOf z) := by
      linarith [Complex.normSq_nonneg (gammaOf z)]
    have h1_nonneg : 0 ≤ Z_lat.carrier.indicator
        (fun ρ => (Z_lat.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) z :=
      Set.indicator_nonneg (fun _ _ => by positivity) z
    have h2_nonneg : 0 ≤ Z_iso.carrier.indicator
        (fun ρ => (Z_iso.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) z :=
      Set.indicator_nonneg (fun _ _ => by positivity) z
    by_cases hz : z ∈ Z.carrier
    · rw [Set.indicator_of_mem hz]
      rcases hz with ⟨k, _, rfl | rfl⟩ | (rfl | hneg)
      · have hz1 : verticalLatticePoint L δ k ∈ Z_lat.carrier := Or.inl ⟨k, rfl⟩
        rw [Set.indicator_of_mem hz1]
        have hmZ : (Z.mult (verticalLatticePoint L δ k) : ℝ) = 1 := rfl
        have hm1 : (Z_lat.mult (verticalLatticePoint L δ k) : ℝ) = 1 := rfl
        rw [hmZ, hm1]; linarith
      · have hz1 : verticalLatticePoint L (-δ) k ∈ Z_lat.carrier := Or.inr ⟨k, rfl⟩
        rw [Set.indicator_of_mem hz1]
        have hmZ : (Z.mult (verticalLatticePoint L (-δ) k) : ℝ) = 1 := rfl
        have hm1 : (Z_lat.mult (verticalLatticePoint L (-δ) k) : ℝ) = 1 := rfl
        rw [hmZ, hm1]; linarith
      · have hz2 : offLinePoint δ ε ∈ Z_iso.carrier := Or.inl (Or.inr rfl)
        rw [Set.indicator_of_mem hz2]
        have hmZ : (Z.mult (offLinePoint δ ε) : ℝ) = 1 := rfl
        have hm2 : (Z_iso.mult (offLinePoint δ ε) : ℝ) = 1 := by
          change ((if (offLinePoint δ ε).re = 1 / 2 then (2 : ℕ) else 1) : ℝ) = 1
          rw [if_neg (by simp only [offLinePoint]; linarith)]; norm_num
        rw [hmZ, hm2]; linarith
      · rw [Set.mem_singleton_iff] at hneg; subst hneg
        have hz2 : offLinePoint (-δ) ε ∈ Z_iso.carrier := Or.inr rfl
        rw [Set.indicator_of_mem hz2]
        have hmZ : (Z.mult (offLinePoint (-δ) ε) : ℝ) = 1 := rfl
        have hm2 : (Z_iso.mult (offLinePoint (-δ) ε) : ℝ) = 1 := by
          change ((if (offLinePoint (-δ) ε).re = 1 / 2 then (2 : ℕ) else 1) : ℝ) = 1
          rw [if_neg (by simp only [offLinePoint]; linarith)]; norm_num
        rw [hmZ, hm2]; linarith
    · rw [Set.indicator_of_notMem hz]; linarith

private theorem sq_div_eight_le_one_sub_cos {θ : ℝ} (h0 : 0 ≤ θ) (h2 : θ ≤ 2) :
    θ ^ 2 / 8 ≤ 1 - Real.cos θ := by
  have hsin_cubic : ∀ φ : ℝ, 0 ≤ φ → φ - φ ^ 3 / 6 ≤ Real.sin φ := fun φ hφ => by
    rcases eq_or_lt_of_le hφ with rfl | hpos
    · simp
    · set g : ℝ → ℝ := fun t => Real.sin t - (t - t ^ 3 / 6)
      have hgd : ∀ t : ℝ, HasDerivAt g (Real.cos t - (1 - t ^ 2 / 2)) t := fun t => by
        have d1 := Real.hasDerivAt_sin t
        have d2 := (hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)
        exact (d1.sub d2).congr_deriv (by ring)
      obtain ⟨c, _, hcd⟩ := exists_hasDerivAt_eq_slope g
        (fun t => Real.cos t - (1 - t ^ 2 / 2)) hpos (by fun_prop) fun t _ => hgd t
      have hg0 : g 0 = 0 := by simp [g]
      rw [hg0, sub_zero, sub_zero, eq_div_iff hpos.ne'] at hcd
      have hcos_c : 0 ≤ Real.cos c - (1 - c ^ 2 / 2) := by
        linarith [Real.one_sub_sq_div_two_le_cos (x := c)]
      have hgφ : 0 ≤ g φ := by nlinarith
      dsimp [g] at hgφ
      linarith
  have hφ0 : 0 ≤ θ / 2 := by linarith
  have hφ1 : θ / 2 ≤ 1 := by linarith
  have hsin_lb : θ / 4 ≤ Real.sin (θ / 2) := by
    have h1 := hsin_cubic (θ / 2) hφ0
    have h2' : (θ / 2) ^ 3 ≤ θ / 2 := by nlinarith
    linarith
  have hcos_id : 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
    have hc := Real.cos_two_mul (θ / 2)
    have hs := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hc
    linarith
  rw [hcos_id]
  have hsq : (θ / 4) ^ 2 ≤ Real.sin (θ / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hsin_lb 2
  linarith

private theorem sinhTest_window_lb_sq_ge {a δ : ℝ} (hδ : 0 < δ) (hδa : 2 ≤ δ * a) :
    a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7) ≤
      ((1 / (4 * δ)) * ((1 / (4 * δ)) * a) ^ (5 / 2 : ℝ) *
        Real.sinh (δ * (a - 2 * (1 / (4 * δ)))) ^ 2) ^ 2 := by
  have ha : 0 < a := by by_contra hle; push Not at hle; nlinarith
  set w := 1 / (4 * δ)
  set x := δ * (a - 2 * w)
  have hx_eq : x = δ * a - 1 / 2 := by dsimp [x, w]; field_simp [hδ.ne']; ring
  have hexp_2x : 2 ≤ Real.exp (2 * x) := by
    have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : Real.exp 1 ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hexp_neg_x : Real.exp (-x) ≤ Real.exp x / 2 := by
    have hprod : Real.exp (2 * x) * Real.exp (-x) = Real.exp x := by
      rw [← Real.exp_add]; congr 1; ring
    have := mul_le_mul_of_nonneg_right hexp_2x (Real.exp_pos (-x)).le
    rw [hprod] at this; linarith
  have hsinh_x : Real.exp x / 4 ≤ Real.sinh x := by rw [Real.sinh_eq]; linarith
  have hexp_half : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have hsq : Real.exp (1 / 2 : ℝ) ^ 2 < 2 ^ 2 := by
      rw [sq, ← Real.exp_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
      linarith [Real.exp_one_lt_d9]
    have hlt2 : Real.exp (1 / 2 : ℝ) < 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    linarith [hlt2]
  have hexp_x : Real.exp (δ * a) / 2 ≤ Real.exp x := by
    rw [hx_eq, show δ * a - (1 / 2 : ℝ) = δ * a + -(1 / 2 : ℝ) by ring, Real.exp_add]
    have := mul_le_mul_of_nonneg_left hexp_half (Real.exp_pos (δ * a)).le
    linarith
  have hsinh_lb : Real.exp (δ * a) / 8 ≤ Real.sinh x := by linarith
  have hsh_sq : (Real.exp (δ * a) / 8) ^ 2 ≤ Real.sinh x ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsinh_lb 2
  have hwa_sq : ((w * a) ^ (5 / 2 : ℝ)) ^ 2 = (w * a) ^ 5 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity),
      show (5 / 2 : ℝ) * (2 : ℕ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)
      = w ^ 2 * (w * a) ^ 5 * ((Real.exp (δ * a) / 8) ^ 2) ^ 2 := by
        dsimp [w]
        have he4 : Real.exp (4 * δ * a) = Real.exp (δ * a) ^ 4 := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [he4]; field_simp [hδ.ne']; ring
    _ = (w * (w * a) ^ (5 / 2 : ℝ) * (Real.exp (δ * a) / 8) ^ 2) ^ 2 := by
        symm; rw [mul_pow, mul_pow, hwa_sq]
    _ ≤ (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh x ^ 2) ^ 2 := by gcongr

/-- **Off-line column fragility under a single defect (`Π29` collapse side).** Whereas the exact
off-line lattice `offLineLatticeConfig hL hδ hδ'` has `onsetAperture = L/2`, shifting just its
`k = 0` pair by `0 < ε ≤ π/L` collapses `onsetAperture` below every `a ≤ L/2` (`2 ≤ δa`) with
`960 * 2 ^ 26 * δ * L < ε ^ 2 * a ^ 2 * exp(2 * δ * a)`, i.e. down to the logarithmic scale
`a ≍ (1/(2δ)) log(δL / ε²) ≪ L/2`! -/
theorem onsetAperture_singleDefectOffLineLattice_lt {L δ ε a : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hε : 0 < ε) (hεL : ε ≤ π / L) (haL : a ≤ L / 2) (hδa : 2 ≤ δ * a)
    (hdet : 960 * 2 ^ 26 * δ * L < ε ^ 2 * a ^ 2 * Real.exp (2 * δ * a)) :
    onsetAperture (singleDefectOffLineLattice hL hδ hδ' hε hεL) < (a : EReal) := by
  classical
  have ha : 0 < a := by by_contra hle; push Not at hle; nlinarith
  set Z_def := singleDefectOffLineLattice hL hδ hδ' hε hεL
  set Z_lat := offLineLatticeConfig hL hδ hδ'
  have htemp_def := temperedConfig_singleDefectOffLineLattice hL hδ hδ' hε hεL
  have htemp_lat := temperedConfig_offLineLatticeConfig hL hδ hδ'
  rw [← exists_re_W_neg_iff_onsetAperture_lt htemp_def ha.le]
  set s := sinhTest a δ
  set f := modulatedTest ε s
  have hf_cd : ContDiff ℝ 2 f := modulatedTest_contDiff ε (sinhTest_contDiff a δ)
  have hs_supp : ∀ u, s u ≠ 0 → |u| ≤ a := sinhTest_supp ha.le
  have hf_supp : tsupport f ⊆ Icc (-a) a := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have hsu : s u ≠ 0 := fun h0 => hu (by simp [f, modulatedTest, h0])
    exact abs_le.mp (hs_supp u hsu)
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_Icc hf_supp
  refine ⟨f, hf_cd, hf_supp, ?_⟩
  -- Identify the 4-point difference `Z_def.W f f - Z_lat.W f f`.
  set p₁ := offLinePoint δ ε
  set p₂ := offLinePoint (-δ) ε
  set q₁ := offLinePoint δ 0
  set q₂ := offLinePoint (-δ) 0
  have hq₁_lat : verticalLatticePoint L δ 0 = q₁ := by
    apply Complex.ext <;> simp [verticalLatticePoint, q₁, offLinePoint]
  have hq₂_lat : verticalLatticePoint L (-δ) 0 = q₂ := by
    apply Complex.ext <;> simp [verticalLatticePoint, q₂, offLinePoint]
  have hnot_lat : ∀ (k : ℤ) (d : ℝ), k ≠ 0 → verticalLatticePoint L d k ≠ offLinePoint d ε ∧
      verticalLatticePoint L d k ≠ offLinePoint (-d) ε := by
    intro k d hk
    have hk_abs : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
    have him_ge : 2 * π / L ≤ |(k : ℝ) * (2 * π / L)| := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)]
      nlinarith [Real.pi_pos]
    have hlt_2pi : ε < 2 * π / L := by
      have : π / L < 2 * π / L := by
        rw [div_lt_div_iff_of_pos_right hL]; linarith [Real.pi_pos]
      linarith
    constructor <;> intro heq <;>
      { have him := congrArg Complex.im heq
        simp only [verticalLatticePoint, offLinePoint] at him
        rw [him, abs_of_pos hε] at him_ge
        linarith }
  have hp₁_not_lat : p₁ ∉ Z_lat.carrier := by
    rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · by_cases hk0 : k = 0
      · subst hk0; rw [hq₁_lat] at hk
        have := congrArg Complex.im hk; simp [p₁, q₁, offLinePoint] at this; linarith
      · exact (hnot_lat k δ hk0).1 hk
    · have := congrArg Complex.re hk; simp [verticalLatticePoint, p₁, offLinePoint] at this; linarith
  have hp₂_not_lat : p₂ ∉ Z_lat.carrier := by
    rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · have := congrArg Complex.re hk; simp [verticalLatticePoint, p₂, offLinePoint] at this; linarith
    · by_cases hk0 : k = 0
      · subst hk0; rw [hq₂_lat] at hk
        have := congrArg Complex.im hk; simp [p₂, q₂, offLinePoint] at this; linarith
      · exact (hnot_lat k (-δ) hk0).1 hk
  have hq₁_not_def : q₁ ∉ Z_def.carrier := by
    rintro (⟨k, hk0, h | h⟩ | (h | h))
    · have := verticalLatticePoint_injective hL δ (h.symm.trans hq₁_lat.symm); exact hk0 this
    · have := congrArg Complex.re h; simp [verticalLatticePoint, q₁, offLinePoint] at this; linarith
    · have := congrArg Complex.im h; simp [q₁, offLinePoint] at this; linarith
    · rw [Set.mem_singleton_iff] at h
      have := congrArg Complex.im h; simp [q₁, offLinePoint] at this; linarith
  have hq₂_not_def : q₂ ∉ Z_def.carrier := by
    rintro (⟨k, hk0, h | h⟩ | (h | h))
    · have := congrArg Complex.re h; simp [verticalLatticePoint, q₂, offLinePoint] at this; linarith
    · have := verticalLatticePoint_injective hL (-δ) (h.symm.trans hq₂_lat.symm); exact hk0 this
    · have := congrArg Complex.im h; simp [q₂, offLinePoint] at this; linarith
    · rw [Set.mem_singleton_iff] at h
      have := congrArg Complex.im h; simp [q₂, offLinePoint] at this; linarith
  set S₄ : Finset ℂ := {p₁, p₂, q₁, q₂}
  have hmultDiff_van : ∀ z ∉ S₄, multDiff Z_def Z_lat z = 0 := by
    intro z hz
    simp only [S₄, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    have hiff : z ∈ Z_def.carrier ↔ z ∈ Z_lat.carrier := by
      constructor
      · rintro (⟨k, _, rfl | rfl⟩ | (rfl | h))
        · exact Or.inl ⟨k, rfl⟩
        · exact Or.inr ⟨k, rfl⟩
        · exact absurd rfl hz1
        · rw [Set.mem_singleton_iff] at h; exact absurd h hz2
      · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
        · by_cases hk0 : k = 0
          · subst hk0; exact absurd hq₁_lat hz3
          · exact Or.inl ⟨k, hk0, Or.inl rfl⟩
        · by_cases hk0 : k = 0
          · subst hk0; exact absurd hq₂_lat hz4
          · exact Or.inl ⟨k, hk0, Or.inr rfl⟩
    by_cases hmem : z ∈ Z_def.carrier
    · have hmem' : z ∈ Z_lat.carrier := hiff.mp hmem
      simp [multDiff, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem', Z_def, Z_lat]
    · have hmem' : z ∉ Z_lat.carrier := fun h => hmem (hiff.mpr h)
      simp [multDiff, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']
  have hW_sub := W_sub_W_eq_sum htemp_def htemp_lat hmultDiff_van hf_cd hfc hf_cd hfc
  have hp12 : p₁ ≠ p₂ := fun h => by
    have := congrArg Complex.re h; simp [p₁, p₂, offLinePoint] at this; linarith
  have hp1q1 : p₁ ≠ q₁ := fun h => by
    have := congrArg Complex.im h; simp [p₁, q₁, offLinePoint] at this; linarith
  have hp1q2 : p₁ ≠ q₂ := fun h => by
    have := congrArg Complex.im h; simp [p₁, q₂, offLinePoint] at this; linarith
  have hp2q1 : p₂ ≠ q₁ := fun h => by
    have := congrArg Complex.im h; simp [p₂, q₁, offLinePoint] at this; linarith
  have hp2q2 : p₂ ≠ q₂ := fun h => by
    have := congrArg Complex.im h; simp [p₂, q₂, offLinePoint] at this; linarith
  have hq12 : q₁ ≠ q₂ := fun h => by
    have := congrArg Complex.re h; simp [q₁, q₂, offLinePoint] at this; linarith
  have hp₁_def : p₁ ∈ Z_def.carrier := Or.inr (Or.inl rfl)
  have hp₂_def : p₂ ∈ Z_def.carrier := Or.inr (Or.inr (Set.mem_singleton _))
  have hq₁_mem : q₁ ∈ Z_lat.carrier := Or.inl ⟨0, hq₁_lat⟩
  have hq₂_mem : q₂ ∈ Z_lat.carrier := Or.inr ⟨0, hq₂_lat⟩
  have md_p₁ : multDiff Z_def Z_lat p₁ = 1 := by
    simp [multDiff, Set.indicator_of_mem hp₁_def, Set.indicator_of_notMem hp₁_not_lat, Z_def]
  have md_p₂ : multDiff Z_def Z_lat p₂ = 1 := by
    simp [multDiff, Set.indicator_of_mem hp₂_def, Set.indicator_of_notMem hp₂_not_lat, Z_def]
  have md_q₁ : multDiff Z_def Z_lat q₁ = -1 := by
    simp [multDiff, Set.indicator_of_notMem hq₁_not_def, Set.indicator_of_mem hq₁_mem, Z_lat]
  have md_q₂ : multDiff Z_def Z_lat q₂ = -1 := by
    simp [multDiff, Set.indicator_of_notMem hq₂_not_def, Set.indicator_of_mem hq₂_mem, Z_lat]
  have hsum4 : ∑ z ∈ S₄, multDiff Z_def Z_lat z * pointImage f f z =
      pointImage f f p₁ + pointImage f f p₂ - pointImage f f q₁ - pointImage f f q₂ := by
    dsimp [S₄]
    rw [Finset.sum_insert (by simp [hp12, hp1q1, hp1q2]),
      Finset.sum_insert (by simp [hp2q1, hp2q2]),
      Finset.sum_pair hq12, md_p₁, md_p₂, md_q₁, md_q₂]
    ring
  rw [hsum4] at hW_sub
  -- Evaluate the real parts via `re_Wsummand_modulatedTest_odd`.
  have hp_odd := re_Wsummand_modulatedTest_odd Z_def ε hp₁_def (ε := δ)
    (by simp [p₁, offLinePoint]) (sinhTest_contDiff a δ).continuous hs_supp (sinhTest_odd a δ)
  have hq_odd := re_Wsummand_modulatedTest_odd Z_lat ε hq₁_mem (ε := δ)
    (by simp [q₁, offLinePoint]) (sinhTest_contDiff a δ).continuous hs_supp (sinhTest_odd a δ)
  have hrefl_p₁ : reflect p₁ = p₂ := reflect_offLinePoint δ ε
  have hrefl_q₁ : reflect q₁ = q₂ := reflect_offLinePoint δ 0
  have hp_im : p₁.im - ε = 0 := by simp [p₁, offLinePoint]
  have hq_im : q₁.im - ε = -ε := by simp [q₁, offLinePoint]
  rw [hrefl_p₁, hp_im] at hp_odd
  rw [hrefl_q₁, hq_im] at hq_odd
  have hp_pt1 : pointImage f f p₁ = Z_def.Wsummand f f p₁ := by
    rw [Wsummand_eq_mul]; change _ = (1 : ℂ) * _; ring
  have hp_pt2 : pointImage f f p₂ = Z_def.Wsummand f f p₂ := by
    rw [Wsummand_eq_mul]; change _ = (1 : ℂ) * _; ring
  have hq_pt1 : pointImage f f q₁ = Z_lat.Wsummand f f q₁ := by
    rw [Wsummand_eq_mul]; change _ = (1 : ℂ) * _; ring
  have hq_pt2 : pointImage f f q₂ = Z_lat.Wsummand f f q₂ := by
    rw [Wsummand_eq_mul]; change _ = (1 : ℂ) * _; ring
  set P := ∫ u, s u * Real.sinh (δ * u)
  set A := ∫ u, s u * Real.sinh (δ * u) * Real.cos (ε * u)
  set B := ∫ u, s u * Real.cosh (δ * u) * Real.sin (-ε * u)
  have hA_eq : (∫ u, s u * Real.sinh (δ * u) * Real.cos (-ε * u)) = A := by
    dsimp [A]; congr 1 with u; rw [neg_mul, Real.cos_neg]
  have hp_re : (pointImage f f p₁).re + (pointImage f f p₂).re = -2 * P ^ 2 := by
    rw [hp_pt1, hp_pt2, hp_odd.1, hp_odd.2]
    have hm1 : (Z_def.mult p₁ : ℝ) = 1 := rfl
    have hsin0 : (∫ u, s u * Real.cosh (δ * u) * Real.sin (0 * u)) = 0 := by simp
    have hcos0 : (∫ u, s u * Real.sinh (δ * u) * Real.cos (0 * u)) = P := by simp [P]
    rw [hm1, hsin0, hcos0]; ring
  have hq_re : (pointImage f f q₁).re + (pointImage f f q₂).re = 2 * (B ^ 2 - A ^ 2) := by
    rw [hq_pt1, hq_pt2, hq_odd.1, hq_odd.2, hA_eq]
    have hm1 : (Z_lat.mult q₁ : ℝ) = 1 := rfl
    rw [hm1]; ring
  -- Lattice background bound at `a ≤ L/2`.
  have hf_supp_L : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hf_supp.trans (Icc_subset_Icc (by linarith) haL)
  have hW_lat_re : (Z_lat.W f f).re ≤ 60 * L * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6 := by
    rw [W_offLineLatticeConfig_of_le_nyquist hL hδ hδ' hf_cd hf_cd.continuous hf_supp_L hf_supp_L,
      show (2 : ℂ) * (L : ℂ) * ∫ t, f t * conj (f t) =
        ((2 * L : ℝ) : ℂ) * ∫ t, f t * conj (f t) by push_cast; ring,
      Complex.re_ofReal_mul, re_integral_mul_conj_self_eq_norm_sq]
    have hnorm_le := integral_norm_sq_modulatedTest_sinhTest_le ε ha.le hδ
    calc 2 * L * ∫ t, ‖f t‖ ^ 2
        ≤ 2 * L * (30 * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6) :=
          mul_le_mul_of_nonneg_left hnorm_le (by positivity)
      _ = 60 * L * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6 := by ring
  -- Lower bound `P^2 - A^2 ≥ (ε^2 * a^2 / 32) * (a^5 * exp(4δa) / (2^26 * δ^7))`.
  set w := 1 / (4 * δ)
  have hw : 0 < w := by dsimp [w]; positivity
  have hwa : w ≤ a / 4 := by
    dsimp [w]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set Q := w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hQ_le_P : Q ≤ P := sinhTest_energy_ge hδ hw hwa
  have hsh_nonneg : ∀ u, 0 ≤ s u * Real.sinh (δ * u) := fun u => by
    have : s u * Real.sinh (δ * u) = Real.sinh (δ * u) ^ 2 * sinhTestWeight a u := by
      dsimp [s, sinhTest]; ring
    rw [this]; exact mul_nonneg (sq_nonneg _) (sinhTestWeight_nonneg a u)
  have hint_P : Integrable (fun u => s u * Real.sinh (δ * u)) :=
    ((sinhTest_contDiff a δ).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs hs_supp).mul_right
  have hint_A : Integrable (fun u => s u * Real.sinh (δ * u) * Real.cos (ε * u)) :=
    (((sinhTest_contDiff a δ).continuous.mul (by fun_prop)).mul (by fun_prop)
      ).integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs hs_supp).mul_right.mul_right
  have hA_nonneg : 0 ≤ A := by
    refine integral_nonneg fun u => ?_
    by_cases h0 : s u = 0
    · simp [h0]
    · have hua : |u| ≤ L / 2 := (hs_supp u h0).trans haL
      have hεu : |ε * u| ≤ π / 2 := by
        rw [abs_mul, abs_of_pos hε]
        calc ε * |u| ≤ (π / L) * (L / 2) := mul_le_mul hεL hua (abs_nonneg _) (by positivity)
          _ = π / 2 := by field_simp [hL.ne']
      exact mul_nonneg (hsh_nonneg u) (Real.cos_nonneg_of_mem_Icc (abs_le.mp hεu))
  have hPA_ge : (ε ^ 2 * a ^ 2 / 32) * Q ≤ P - A := by
    have hdiff_eq : P - A = ∫ u, s u * Real.sinh (δ * u) * (1 - Real.cos (ε * u)) := by
      dsimp [P, A]
      rw [← integral_sub hint_P hint_A]
      congr 1 with u; ring
    rw [hdiff_eq]
    have hcont_d : Continuous (fun u => s u * Real.sinh (δ * u) * (1 - Real.cos (ε * u))) :=
      ((sinhTest_contDiff a δ).continuous.mul (by fun_prop)).mul (by fun_prop)
    have hint_d : Integrable (fun u => s u * Real.sinh (δ * u) * (1 - Real.cos (ε * u))) := by
      refine (hint_P.sub hint_A).congr (Eventually.of_forall fun u => by ring)
    have hd_nonneg : ∀ u, 0 ≤ s u * Real.sinh (δ * u) * (1 - Real.cos (ε * u)) := fun u =>
      mul_nonneg (hsh_nonneg u) (by linarith [Real.cos_le_one (ε * u)])
    set c0 := (ε ^ 2 * a ^ 2 / 32) * ((w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2)
    have hsub : ∫ _u in Icc (a - 2 * w) (a - w), c0 ≤
        ∫ u in Icc (a - 2 * w) (a - w), s u * Real.sinh (δ * u) * (1 - Real.cos (ε * u)) := by
      refine setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne (by simp))
        hcont_d.integrableOn_Icc measurableSet_Icc fun u hu => ?_
      obtain ⟨hu1, hu2⟩ := hu
      have hu_half : a / 2 ≤ u := by linarith
      have huL : u ≤ L / 2 := by linarith
      have hp : w * a ≤ a ^ 2 - u ^ 2 := by nlinarith
      have hψ : (w * a) ^ (5 / 2 : ℝ) ≤ sinhTestWeight a u :=
        Real.rpow_le_rpow (by positivity) hp (by norm_num)
      have hsh0 : 0 ≤ Real.sinh (δ * (a - 2 * w)) :=
        Real.sinh_nonneg_iff.mpr (mul_nonneg hδ.le (by linarith))
      have hsh : Real.sinh (δ * (a - 2 * w)) ^ 2 ≤ Real.sinh (δ * u) ^ 2 :=
        pow_le_pow_left₀ hsh0 (Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hu1 hδ.le)) 2
      have h1 : (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2 ≤
          s u * Real.sinh (δ * u) := by
        rw [show s u * Real.sinh (δ * u) = sinhTestWeight a u * Real.sinh (δ * u) ^ 2 by
          dsimp [s, sinhTest]; ring]
        exact mul_le_mul hψ hsh (sq_nonneg _) (sinhTestWeight_nonneg a u)
      have hθ0 : 0 ≤ ε * u := mul_nonneg hε.le (by linarith)
      have hθ2 : ε * u ≤ 2 := by
        calc ε * u ≤ (π / L) * (L / 2) := mul_le_mul hεL huL (by linarith) (by positivity)
          _ = π / 2 := by field_simp [hL.ne']
          _ ≤ 2 := by linarith [Real.pi_lt_four]
      have hcos_lb : ε ^ 2 * a ^ 2 / 32 ≤ 1 - Real.cos (ε * u) := by
        have hsq : ε ^ 2 * a ^ 2 / 32 ≤ (ε * u) ^ 2 / 8 := by
          have : (ε * (a / 2)) ^ 2 ≤ (ε * u) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hu_half hε.le) 2
          linarith
        exact hsq.trans (sq_div_eight_le_one_sub_cos hθ0 hθ2)
      dsimp [c0]
      rw [mul_comm (ε ^ 2 * a ^ 2 / 32)]
      exact mul_le_mul h1 hcos_lb (by positivity) (hsh_nonneg u)
    have hle_all := setIntegral_le_integral hint_d (Eventually.of_forall hd_nonneg)
    rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul, max_eq_left (by linarith),
      show a - w - (a - 2 * w) = w by ring] at hsub
    calc (ε ^ 2 * a ^ 2 / 32) * Q = w * c0 := by dsimp [Q, c0]; ring
      _ ≤ _ := hsub.trans hle_all
  have hP2_sub_A2 :
      (ε ^ 2 * a ^ 2 / 32) * (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)) ≤
        P ^ 2 - A ^ 2 := by
    have hQ2 := sinhTest_window_lb_sq_ge hδ hδa
    have hPA_sum : Q ≤ P + A := by linarith
    calc (ε ^ 2 * a ^ 2 / 32) * (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7))
        ≤ (ε ^ 2 * a ^ 2 / 32) * Q ^ 2 :=
          mul_le_mul_of_nonneg_left hQ2 (by positivity)
      _ = Q * ((ε ^ 2 * a ^ 2 / 32) * Q) := by ring
      _ ≤ (P + A) * (P - A) :=
          mul_le_mul hPA_sum hPA_ge (by positivity) (by linarith)
      _ = P ^ 2 - A ^ 2 := by ring
  -- Combine all terms in `(Z_def.W f f).re`.
  have hW_re_eq : (Z_def.W f f).re = (Z_lat.W f f).re - 2 * P ^ 2 - 2 * (B ^ 2 - A ^ 2) := by
    have hre := congrArg Complex.re hW_sub
    simp only [Complex.sub_re, Complex.add_re] at hre
    linarith [hp_re, hq_re]
  have hW_def_le : (Z_def.W f f).re ≤
      60 * L * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6 -
        (ε ^ 2 * a ^ 2 / 16) * (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)) := by
    nlinarith [sq_nonneg B]
  have hscale : 0 < a ^ 5 * Real.exp (2 * δ * a) / (16 * 2 ^ 26 * δ ^ 7) := by positivity
  have hdiff_neg :
      60 * L * a ^ 5 * Real.exp (2 * δ * a) / δ ^ 6 -
        (ε ^ 2 * a ^ 2 / 16) * (a ^ 5 * Real.exp (4 * δ * a) / (2 ^ 26 * δ ^ 7)) =
      (960 * 2 ^ 26 * δ * L - ε ^ 2 * a ^ 2 * Real.exp (2 * δ * a)) *
        (a ^ 5 * Real.exp (2 * δ * a) / (16 * 2 ^ 26 * δ ^ 7)) := by
    have he4 : Real.exp (4 * δ * a) = Real.exp (2 * δ * a) * Real.exp (2 * δ * a) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he4]; field_simp [hδ.ne']; ring
  nlinarith

/-- **Perturbed off-line lattice configuration (`Π29` stability side).** Shifts each `k`-th pair
of `offLineLatticeConfig` from `2πk/L` to `2πk/L + ε_k` with `|ε_k| ≤ π/(2L)`. -/
def perturbedOffLineLatticeConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (ε : ℤ → ℝ) (hε : ∀ k : ℤ, |ε k| ≤ π / (2 * L)) : ZeroConfig where
  carrier := Set.range (fun k : ℤ => offLinePoint δ ((k : ℝ) * (2 * π / L) + ε k)) ∪
    Set.range (fun k : ℤ => offLinePoint (-δ) ((k : ℝ) * (2 * π / L) + ε k))
  mult := fun _ => 1
  one_le_mult := fun _ _ => le_rfl
  strip := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> simp only [offLinePoint] <;> constructor <;> linarith
  reflect_mem := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact Or.inr ⟨k, (reflect_offLinePoint δ _).symm⟩
    · exact Or.inl ⟨k, by rw [reflect_offLinePoint, neg_neg]⟩
  mult_reflect := fun _ _ => rfl
  finite_window := by
    intro T₁ T₂
    have hF := finite_latticeWindow (h := 2 * π / L) (by positivity)
      (T₁ - π / (2 * L)) (T₂ + π / (2 * L))
    set p_pos : ℤ → ℂ := fun k => offLinePoint δ ((k : ℝ) * (2 * π / L) + ε k)
    set p_neg : ℤ → ℂ := fun k => offLinePoint (-δ) ((k : ℝ) * (2 * π / L) + ε k)
    refine ((hF.image p_pos).union (hF.image p_neg)).subset ?_
    rintro _ ⟨⟨k, rfl⟩ | ⟨k, rfl⟩, h1, h2⟩
    · simp only [offLinePoint] at h1 h2
      have hb := abs_le.mp (hε k)
      exact Or.inl ⟨k, ⟨by linarith, by linarith⟩, rfl⟩
    · simp only [offLinePoint] at h1 h2
      have hb := abs_le.mp (hε k)
      exact Or.inr ⟨k, ⟨by linarith, by linarith⟩, rfl⟩

private theorem perturbedOrdinate_injective {L : ℝ} (hL : 0 < L) {ε : ℤ → ℝ}
    (hε : ∀ k : ℤ, |ε k| ≤ π / (2 * L)) (d : ℝ) :
    Function.Injective (fun k : ℤ => offLinePoint d ((k : ℝ) * (2 * π / L) + ε k)) := by
  intro k₁ k₂ heq
  by_contra hne
  have him := congrArg Complex.im heq
  simp only [offLinePoint] at him
  have hdiff : ((k₁ : ℝ) - (k₂ : ℝ)) * (2 * π / L) = ε k₂ - ε k₁ := by linarith
  have hk_ge : (1 : ℝ) ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by
    have hsub_ne : k₁ - k₂ ≠ 0 := sub_ne_zero.mpr hne
    have := Int.one_le_abs hsub_ne
    have hcast : (((|k₁ - k₂| : ℤ) : ℝ)) = |(k₁ : ℝ) - (k₂ : ℝ)| := by
      rw [Int.cast_abs, Int.cast_sub]
    linarith
  have hlhs : 2 * π / L ≤ |((k₁ : ℝ) - (k₂ : ℝ)) * (2 * π / L)| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)]
    nlinarith [Real.pi_pos]
  have hrhs : |ε k₂ - ε k₁| ≤ π / L := by
    calc |ε k₂ - ε k₁| ≤ |ε k₂| + |ε k₁| := abs_sub _ _
      _ ≤ π / (2 * L) + π / (2 * L) := add_le_add (hε k₂) (hε k₁)
      _ = π / L := by field_simp [hL.ne']; ring
  have hlt : π / L < 2 * π / L := by
    rw [div_lt_div_iff_of_pos_right hL]; linarith [Real.pi_pos]
  rw [hdiff] at hlhs
  linarith

private theorem norm_cexp_I_mul_sub_le (x₁ x₂ u : ℝ) :
    ‖cexp (((x₁ * u : ℝ) : ℂ) * I) - cexp (((x₂ * u : ℝ) : ℂ) * I)‖ ≤ |x₁ - x₂| * |u| := by
  set φ := (x₁ - x₂) * u
  have hfac : cexp (((x₁ * u : ℝ) : ℂ) * I) - cexp (((x₂ * u : ℝ) : ℂ) * I) =
      cexp (((x₂ * u : ℝ) : ℂ) * I) * (cexp ((φ : ℂ) * I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2; dsimp [φ]; push_cast; ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsq : ‖cexp ((φ : ℂ) * I) - 1‖ ^ 2 ≤ |φ| ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.exp_mul_I, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re]
    have hre_im : (((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * I - 1) =
        ⟨Real.cos φ - 1, Real.sin φ⟩ := by
      apply Complex.ext <;> simp
    rw [hre_im, Complex.normSq_mk]
    have hc := Real.cos_two_mul (φ / 2)
    have hs := Real.sin_sq_add_cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at hc
    have hid : (Real.cos φ - 1) * (Real.cos φ - 1) + Real.sin φ * Real.sin φ =
        4 * Real.sin (φ / 2) ^ 2 := by nlinarith
    rw [hid]
    have hsin : |Real.sin (φ / 2)| ≤ |φ / 2| := Real.abs_sin_le_abs
    have hsin_sq : Real.sin (φ / 2) ^ 2 ≤ (φ / 2) ^ 2 := by
      rw [← sq_abs (Real.sin (φ / 2)), ← sq_abs (φ / 2)]
      exact pow_le_pow_left₀ (abs_nonneg _) hsin 2
    rw [sq_abs]; linarith
  have habs_nonneg : 0 ≤ |φ| := abs_nonneg φ
  have hle : ‖cexp ((φ : ℂ) * I) - 1‖ ≤ |φ| := by nlinarith [norm_nonneg (cexp ((φ : ℂ) * I) - 1)]
  simpa [φ, abs_mul] using hle

private theorem norm_paperFT_sub_I_mul_lip {K : ℝ → ℂ} {a M δ : ℝ} (hKc : Continuous K)
    (ha : 0 ≤ a) (hM0 : 0 ≤ M) (hδ : 0 ≤ δ) (hKs : tsupport K ⊆ Icc (-(2 * a)) (2 * a))
    (hKM : ∀ u, ‖K u‖ ≤ M) (x₁ x₂ s : ℝ) (hs : |s| ≤ δ) :
    ‖paperFT K ((x₁ : ℂ) - I * s) - paperFT K ((x₂ : ℂ) - I * s)‖ ≤
      8 * a ^ 2 * Real.exp (2 * δ * a) * |x₁ - x₂| * M := by
  have hK_cs : HasCompactSupport K := isCompact_Icc.of_isClosed_subset (isClosed_tsupport K) hKs
  have hK_out : ∀ u ∉ Icc (-(2 * a)) (2 * a), K u = 0 :=
    fun u hu => image_eq_zero_of_notMem_tsupport fun hm => hu (hKs hm)
  have hint1 : Integrable (fun u : ℝ => K u * cexp (I * ((x₁ : ℂ) - I * s) * u)) :=
    (hKc.mul (by fun_prop)).integrable_of_hasCompactSupport hK_cs.mul_right
  have hint2 : Integrable (fun u : ℝ => K u * cexp (I * ((x₂ : ℂ) - I * s) * u)) :=
    (hKc.mul (by fun_prop)).integrable_of_hasCompactSupport hK_cs.mul_right
  have hsub_int : paperFT K ((x₁ : ℂ) - I * s) - paperFT K ((x₂ : ℂ) - I * s) =
      ∫ u in Icc (-(2 * a)) (2 * a),
        K u * (cexp (I * ((x₁ : ℂ) - I * s) * u) - cexp (I * ((x₂ : ℂ) - I * s) * u)) := by
    rw [paperFT_def, paperFT_def, ← integral_sub hint1 hint2,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun u hu => by rw [hK_out u hu, zero_mul, zero_mul, sub_zero])]
    congr 1 with u; ring
  rw [hsub_int]
  set C := M * Real.exp (2 * δ * a) * (|x₁ - x₂| * (2 * a))
  have hvol : (volume : Measure ℝ).real (Icc (-(2 * a)) (2 * a)) = 4 * a := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  calc ‖∫ u in Icc (-(2 * a)) (2 * a),
          K u * (cexp (I * ((x₁ : ℂ) - I * s) * u) - cexp (I * ((x₂ : ℂ) - I * s) * u))‖
      ≤ C * (volume : Measure ℝ).real (Icc (-(2 * a)) (2 * a)) := by
        refine norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun u hu => ?_
        have hu_abs : |u| ≤ 2 * a := abs_le.mpr hu
        have hexp_fac : ∀ x : ℝ, cexp (I * ((x : ℂ) - I * s) * u) =
            (Real.exp (s * u) : ℂ) * cexp (((x * u : ℝ) : ℂ) * I) := fun x => by
          have hI : I * I = -1 := Complex.I_mul_I
          rw [Complex.ofReal_exp, ← Complex.exp_add]
          congr 1; push_cast; linear_combination (-(s : ℂ) * u) * hI
        rw [hexp_fac x₁, hexp_fac x₂, ← mul_sub, norm_mul, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have hexp_le : Real.exp (s * u) ≤ Real.exp (2 * δ * a) := by
          refine Real.exp_le_exp.mpr ?_
          calc s * u ≤ |s * u| := le_abs_self _
            _ = |s| * |u| := abs_mul _ _
            _ ≤ δ * (2 * a) := mul_le_mul hs hu_abs (abs_nonneg _) hδ
            _ = 2 * δ * a := by ring
        have hosc : ‖cexp (((x₁ * u : ℝ) : ℂ) * I) - cexp (((x₂ * u : ℝ) : ℂ) * I)‖ ≤
            |x₁ - x₂| * (2 * a) :=
          (norm_cexp_I_mul_sub_le x₁ x₂ u).trans
            (mul_le_mul_of_nonneg_left hu_abs (abs_nonneg _))
        dsimp [C]
        exact mul_le_mul (mul_le_mul (hKM u) hexp_le (Real.exp_pos _).le hM0) hosc
          (norm_nonneg _) (mul_nonneg hM0 (Real.exp_pos _).le)
    _ = 8 * a ^ 2 * Real.exp (2 * δ * a) * |x₁ - x₂| * M := by
        rw [hvol]; dsimp [C]; ring

theorem temperedConfig_perturbedOffLineLatticeConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (ε : ℤ → ℝ) (hε : ∀ k : ℤ, |ε k| ≤ π / (2 * L)) :
    TemperedConfig (perturbedOffLineLatticeConfig hL hδ hδ' ε hε) := by
  set Z := perturbedOffLineLatticeConfig hL hδ hδ' ε hε
  set G : ℂ → ℝ := fun ρ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  have h2L : 0 < 2 * L := by positivity
  have hmaj := summable_lattice_weight h2L 0
  have hbranch : ∀ d : ℝ, ∃ S : ℝ,
      HasSum (fun ρ : Set.range (fun k : ℤ => offLinePoint d ((k : ℝ) * (2 * π / L) + ε k)) =>
        G ρ) S := fun d => by
    have hsum_k : Summable (fun k : ℤ => G (offLinePoint d ((k : ℝ) * (2 * π / L) + ε k))) := by
      refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hmaj
      · dsimp [G]; have := Complex.normSq_nonneg (gammaOf (offLinePoint d _)); positivity
      · dsimp [G]
        have hm1 : (Z.mult (offLinePoint d ((k : ℝ) * (2 * π / L) + ε k)) : ℝ) = 1 := rfl
        rw [hm1, gammaOf_offLinePoint, normSq_gammaOf_verticalLatticePoint]
        by_cases hk0 : k = 0
        · subst hk0
          simp only [Int.cast_zero, zero_mul, sq, add_zero, div_one]
          exact div_le_one_of_le₀
            (by linarith [Complex.normSq_nonneg ((0 + ε 0 : ℝ) - I * d)])
            (by linarith [Complex.normSq_nonneg ((0 + ε 0 : ℝ) - I * d)])
        · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
            rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
          have hε_le : |ε k| ≤ |(k : ℝ)| * (π / L) := by
            calc |ε k| ≤ π / (2 * L) := hε k
              _ ≤ |(k : ℝ)| * (π / L) := by
                  have : π / (2 * L) ≤ 1 * (π / L) := by
                    rw [one_mul, div_le_div_iff_of_pos_left Real.pi_pos (by positivity) hL]
                    linarith
                  exact this.trans (mul_le_mul_of_nonneg_right hk1 (by positivity))
          have hord_ge : |(k : ℝ) * (2 * π / (2 * L))| ≤ |(k : ℝ) * (2 * π / L) + ε k| := by
            have h1 : |(k : ℝ) * (2 * π / (2 * L))| = |(k : ℝ)| * (π / L) := by
              rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π / (2 * L))]
              field_simp [hL.ne']
            have h2 : |(k : ℝ) * (2 * π / L)| - |ε k| ≤ |(k : ℝ) * (2 * π / L) + ε k| := by
              have := abs_sub_abs_le_abs_sub ((k : ℝ) * (2 * π / L)) (-ε k)
              simpa [sub_neg_eq_add] using this
            have h3 : |(k : ℝ) * (2 * π / L)| = 2 * (|(k : ℝ)| * (π / L)) := by
              rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)]; ring
            linarith
          have hsq : ((k : ℝ) * (2 * π / (2 * L))) ^ 2 + (0 : ℝ) ^ 2 ≤
              Complex.normSq ((((k : ℝ) * (2 * π / L) + ε k : ℝ) : ℂ) - I * d) := by
            have hnsq : Complex.normSq ((((k : ℝ) * (2 * π / L) + ε k : ℝ) : ℂ) - I * d) =
                ((k : ℝ) * (2 * π / L) + ε k) ^ 2 + d ^ 2 := by
              rw [Complex.normSq_apply]
              simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.mul_im]
              ring
            rw [hnsq]
            have hpow := pow_le_pow_left₀ (abs_nonneg _) hord_ge 2
            rw [sq_abs, sq_abs] at hpow
            nlinarith [sq_nonneg d]
          exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
    obtain ⟨S, hS⟩ := hsum_k
    exact ⟨S, ((perturbedOrdinate_injective hL hε d).hasSum_range_iff).mpr hS⟩
  obtain ⟨S_pos, h_pos⟩ := hbranch δ
  obtain ⟨S_neg, h_neg⟩ := hbranch (-δ)
  have hdisj : Disjoint
      (Set.range fun k : ℤ => offLinePoint δ ((k : ℝ) * (2 * π / L) + ε k))
      (Set.range fun k : ℤ => offLinePoint (-δ) ((k : ℝ) * (2 * π / L) + ε k)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [offLinePoint] at this
    linarith
  exact ⟨S_pos + S_neg, HasSum.add_disjoint (f := G) hdisj h_pos h_neg⟩

/-- **Exponentially small `ℓ¹` jitter preserves off-line column positivity (`Π29` stability
side).** If `|ε_k| ≤ π/(2L)` and `Summable (fun k => |ε_k|)`, then at any half-width
`0 ≤ a ≤ L/2` satisfying `8 * a ^ 2 * exp(2 * δ * a) * (∑' k, |ε_k|) ≤ L`, the perturbed off-line
column pair `perturbedOffLineLatticeConfig` remains window-positive at `a`! Together with
`onsetAperture_singleDefectOffLineLattice_lt`, this fixes the exact `e^{−2δa}` exponential
perturbation scale of off-line column mimicry (`Π29`). -/
theorem windowPositiveAt_perturbedOffLineLatticeConfig {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {ε : ℤ → ℝ} (hε : ∀ k : ℤ, |ε k| ≤ π / (2 * L))
    (hε_sum : Summable fun k : ℤ => |ε k|) (ha0 : 0 ≤ a) (haL : a ≤ L / 2)
    (hstab : 8 * a ^ 2 * Real.exp (2 * δ * a) * (∑' k : ℤ, |ε k|) ≤ L) :
    WindowPositiveAt (perturbedOffLineLatticeConfig hL hδ hδ' ε hε) a := by
  intro f hf hfs
  set Z_pert := perturbedOffLineLatticeConfig hL hδ hδ' ε hε
  set Z_lat := offLineLatticeConfig hL hδ hδ'
  have hfs_L : tsupport f ⊆ Icc (-(L / 2)) (L / 2) := hfs.trans (Icc_subset_Icc (by linarith) haL)
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_Icc hfs
  set K := EF.weilTest f f
  have hK : ContDiff ℝ 2 K := EF.weilTest_contDiff hf hf.continuous hfc
  have hKs : tsupport K ⊆ Icc (-(2 * a)) (2 * a) := by
    simpa [two_mul] using EF.tsupport_weilTest_subset hfs hfs
  set M := ∫ t, ‖f t‖ ^ 2
  have hM0 : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  have hKM : ∀ u, ‖K u‖ ≤ M := norm_weilTest_diag_le hf.continuous hfc
  set C_lip := 8 * a ^ 2 * Real.exp (2 * δ * a) * M
  -- Compare each branch `d ∈ {δ, -δ}` against the unperturbed lattice sum.
  have hbranch_diff : ∀ d : ℝ, |d| ≤ δ →
      ∃ (S_pert S_lat : ℂ),
        HasSum (fun ρ : Set.range (fun k : ℤ => offLinePoint d ((k : ℝ) * (2 * π / L) + ε k)) =>
          Z_pert.Wsummand f f ρ) S_pert ∧
        HasSum (fun ρ : Set.range (verticalLatticePoint L d) =>
          Z_lat.Wsummand f f ρ) S_lat ∧
        ‖S_pert - S_lat‖ ≤ C_lip * ∑' k : ℤ, |ε k| := by
    intro d hd
    set g_lat : ℤ → ℂ := fun k => paperFT K ((((k : ℝ) * (2 * π / L) : ℝ) : ℂ) - I * d)
    set g_pert : ℤ → ℂ := fun k => paperFT K ((((k : ℝ) * (2 * π / L) + ε k : ℝ) : ℂ) - I * d)
    have hs_lat : HasSum g_lat (L * ∑' m : ℤ, K (m * L) * (Real.exp (d * (m * L)) : ℂ)) :=
      hasSum_paperFT_lattice_sub_I_mul hL hK (weilTest_abs_le hfs_L hfs_L) d
    have hnorm_diff : ∀ k : ℤ, ‖g_pert k - g_lat k‖ ≤ C_lip * |ε k| := fun k => by
      have h := norm_paperFT_sub_I_mul_lip hK.continuous ha0 hM0 hδ.le hKs hKM
        ((k : ℝ) * (2 * π / L) + ε k) ((k : ℝ) * (2 * π / L)) d hd
      rw [show (k : ℝ) * (2 * π / L) + ε k - (k : ℝ) * (2 * π / L) = ε k by ring] at h
      calc ‖g_pert k - g_lat k‖ ≤ 8 * a ^ 2 * Real.exp (2 * δ * a) * |ε k| * M := h
        _ = C_lip * |ε k| := by dsimp [C_lip]; ring
    have hsum_diff : Summable (fun k : ℤ => g_pert k - g_lat k) :=
      Summable.of_norm_bounded (hε_sum.mul_left C_lip) hnorm_diff
    have hsum_pert : Summable g_pert := by
      have := hs_lat.summable.add hsum_diff
      exact this.congr fun k => by ring
    set S_pert := ∑' k : ℤ, g_pert k
    set S_lat := ∑' k : ℤ, g_lat k
    refine ⟨S_pert, S_lat, ?_, ?_, ?_⟩
    · rw [(perturbedOrdinate_injective hL hε d).hasSum_range_iff]
      refine hsum_pert.hasSum.congr_fun fun k => ?_
      rw [Function.comp_apply, ZeroConfig.Wsummand,
        EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, gammaOf_offLinePoint]
      change g_pert k = (1 : ℂ) * g_pert k; ring
    · rw [(verticalLatticePoint_injective hL d).hasSum_range_iff]
      refine hs_lat.summable.hasSum.congr_fun fun k => ?_
      rw [Function.comp_apply, Wsummand_verticalLatticePoint _ hf.continuous hf.continuous hfc hfc]
      change g_lat k = (1 : ℂ) * g_lat k; ring
    · dsimp [S_pert, S_lat]
      rw [← hsum_pert.tsum_sub hs_lat.summable]
      calc ‖∑' k : ℤ, (g_pert k - g_lat k)‖
          ≤ ∑' k : ℤ, ‖g_pert k - g_lat k‖ := norm_tsum_le_tsum_norm hsum_diff.norm
        _ ≤ ∑' k : ℤ, C_lip * |ε k| :=
            Summable.tsum_le_tsum hnorm_diff hsum_diff.norm (hε_sum.mul_left C_lip)
        _ = C_lip * ∑' k : ℤ, |ε k| := tsum_mul_left
  obtain ⟨Sp₁, Sl₁, hp₁, hl₁, hb₁⟩ := hbranch_diff δ (by rw [abs_of_pos hδ])
  obtain ⟨Sp₂, Sl₂, hp₂, hl₂, hb₂⟩ := hbranch_diff (-δ) (by rw [abs_neg, abs_of_pos hδ])
  have hdisj_pert : Disjoint
      (Set.range fun k : ℤ => offLinePoint δ ((k : ℝ) * (2 * π / L) + ε k))
      (Set.range fun k : ℤ => offLinePoint (-δ) ((k : ℝ) * (2 * π / L) + ε k)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [offLinePoint] at this; linarith
  have hdisj_lat : Disjoint (Set.range (verticalLatticePoint L δ))
      (Set.range (verticalLatticePoint L (-δ))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [verticalLatticePoint] at this; linarith
  have hW_pert_eq : Z_pert.W f f = Sp₁ + Sp₂ :=
    (HasSum.add_disjoint (f := Z_pert.Wsummand f f) hdisj_pert hp₁ hp₂).tsum_eq
  have hW_lat_eq : Z_lat.W f f = Sl₁ + Sl₂ :=
    (HasSum.add_disjoint (f := Z_lat.Wsummand f f) hdisj_lat hl₁ hl₂).tsum_eq
  have hW_lat_re : (Z_lat.W f f).re = 2 * L * M := by
    rw [W_offLineLatticeConfig_of_le_nyquist hL hδ hδ' hf hf.continuous hfs_L hfs_L,
      show (2 : ℂ) * (L : ℂ) * ∫ t, f t * conj (f t) =
        ((2 * L : ℝ) : ℂ) * ∫ t, f t * conj (f t) by push_cast; ring,
      Complex.re_ofReal_mul, re_integral_mul_conj_self_eq_norm_sq]
  have hdiff_le : ‖Z_pert.W f f - Z_lat.W f f‖ ≤
      16 * a ^ 2 * Real.exp (2 * δ * a) * (∑' k : ℤ, |ε k|) * M := by
    rw [hW_pert_eq, hW_lat_eq, show Sp₁ + Sp₂ - (Sl₁ + Sl₂) = (Sp₁ - Sl₁) + (Sp₂ - Sl₂) by ring]
    calc ‖(Sp₁ - Sl₁) + (Sp₂ - Sl₂)‖
        ≤ ‖Sp₁ - Sl₁‖ + ‖Sp₂ - Sl₂‖ := norm_add_le _ _
      _ ≤ C_lip * (∑' k : ℤ, |ε k|) + C_lip * (∑' k : ℤ, |ε k|) := add_le_add hb₁ hb₂
      _ = 16 * a ^ 2 * Real.exp (2 * δ * a) * (∑' k : ℤ, |ε k|) * M := by dsimp [C_lip]; ring
  have hre_sub : -(16 * a ^ 2 * Real.exp (2 * δ * a) * (∑' k : ℤ, |ε k|) * M) ≤
      (Z_pert.W f f).re - (Z_lat.W f f).re := by
    rw [← Complex.sub_re]
    have h1 := neg_abs_le (Z_pert.W f f - Z_lat.W f f).re
    have h2 := (Complex.abs_re_le_norm (Z_pert.W f f - Z_lat.W f f)).trans hdiff_le
    linarith
  have hfactor : 0 ≤ 2 * (L - 8 * a ^ 2 * Real.exp (2 * δ * a) * (∑' k : ℤ, |ε k|)) * M :=
    mul_nonneg (by linarith) hM0
  linarith

end GaloisForLFunctions.WindowVisibilityLaw
