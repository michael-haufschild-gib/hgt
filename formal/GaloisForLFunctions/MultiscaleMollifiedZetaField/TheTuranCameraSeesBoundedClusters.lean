import GaloisForLFunctions.MultiscaleMollifiedZetaField.ThePrimeCameraSeesDominantZeros
import GaloisForLFunctions.HTGeometry.PowerSumTuranWeightedLowerBound

/-!
# The Turán camera sees bounded clusters

For a fixed width the camera is a power sum in its centre: at `y = νh`,

`Z_{νh}(t) = Σ_ρ B_ρ z_ρ^ν`, `B_ρ = m_ρ v̂(δ(γ_ρ − t − i b_ρ))`, `z_ρ = e^{(b_ρ + i(γ_ρ − t))h}`

(`term_eq_weight_mul_node_pow`). On the window `|γ_ρ − t| ≤ 1/(10δ)` the weights have positive real part, however
deep the zero and on whichever side of the line it lies (`re_paperFT_profile_ge`), so the top groups of Turán's second
main theorem cannot cancel. A cluster of at most `N` zeros in the window, of any shape and with no separation,
therefore cannot hide from all `N` centres `(M+1)h, …, (M+N)h`: at one of them the field has at least
`κ(N, M)` times the amplitude of the deepest zero of the cluster (`exists_nu_norm_zeroField_ge`).

With `δ = cL`, `h = cL/N` and `M` depending only on `c, N`, the loss `κ(N, M)` is a constant, and the centres satisfy
`(1−3c)L ≤ νh ≤ (1−2c)L`. The union of the `N` Chebyshev bounds gives: separated zeros of depth `≥ α/L` sitting in
clusters of at most `N` zeros number `≪_{c,N} T L e^{−2(1−4c)α}` (`exists_card_clustered_zeros_le`).

**What this removes.** Dominance asked that the window contain no competing zero. Here the window may contain up to `N`
arbitrary zeros, deeper ones included. What stays is the condition `ClusterAt`: the zeros outside the cluster carry
weighted mass below the Turán constant times the amplitude. The average window holds `≍ 1/c` zeros, so the bounded
count holds at most heights, and the obstruction left to a rate-two density theorem is the outside mass: comparably
deep zeros just outside the sector, or windows much denser than the average.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

variable {v : ℝ → ℝ}

/-! ### The Turán constant -/

/-- The loss of the weighted Turán theorem with `N` points and starting exponent `M`. -/
def turanConstant (N M : ℕ) : ℝ :=
  1 / (2 * (Real.exp 1 * N * (6 * ((N : ℝ) + 1) * ((M : ℝ) + 2 * N + 2)) ^ N))

theorem turanConstant_pos {N : ℕ} (hN : 1 ≤ N) (M : ℕ) : 0 < turanConstant N M := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold turanConstant
  positivity

/-- The loss only grows with the number of points. -/
theorem turanConstant_le {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (M : ℕ) :
    turanConstant N M ≤ turanConstant n M := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hb1 : 1 ≤ 6 * ((n : ℝ) + 1) * ((M : ℝ) + 2 * n + 2) := by nlinarith
  have hb2 : 6 * ((n : ℝ) + 1) * ((M : ℝ) + 2 * n + 2) ≤
      6 * ((N : ℝ) + 1) * ((M : ℝ) + 2 * N + 2) := by
    apply mul_le_mul <;> nlinarith
  have hb3 : 1 ≤ 6 * ((N : ℝ) + 1) * ((M : ℝ) + 2 * N + 2) := hb1.trans hb2
  have hp : (6 * ((n : ℝ) + 1) * ((M : ℝ) + 2 * n + 2)) ^ n ≤
      (6 * ((N : ℝ) + 1) * ((M : ℝ) + 2 * N + 2)) ^ N :=
    (pow_le_pow_left₀ (by linarith) hb2 n).trans (pow_le_pow_right₀ hb3 hnN)
  unfold turanConstant
  refine one_div_le_one_div_of_le (by positivity) ?_
  have he := Real.exp_pos 1
  gcongr

/-! ### The power sum structure -/

/-- **The camera is a power sum in its centre.** -/
theorem term_eq_weight_mul_node_pow {δ : ℝ} (hδ : 0 < δ) (h t : ℝ) (ν : ℕ) (ρ m : ℂ) :
    m * paperFT (cameraTest v δ ((ν : ℝ) * h)) (gammaOf ρ - t) =
      (m * paperFT (cplx v) ((gammaOf ρ - t) * δ)) * cexp (I * (gammaOf ρ - t) * h) ^ ν := by
  rw [paperFT_cameraTest hδ, ← Complex.exp_nat_mul]
  have e : I * (gammaOf ρ - t) * (((ν : ℝ) * h : ℝ) : ℂ) = (ν : ℂ) * (I * (gammaOf ρ - t) * h) := by
    push_cast
    ring
  rw [e]
  ring

/-- `|z_ρ| = e^{b_ρ h}`. -/
theorem norm_node_eq (ρ : ℂ) (h t : ℝ) :
    ‖cexp (I * (gammaOf ρ - t) * h)‖ = Real.exp ((ρ.re - 1 / 2) * h) := by
  rw [norm_cexp_I_mul, gammaOf_sub_im]
  congr 1
  ring

/-- **The sector of the window.** If `|Re z| δ ≤ 1/10`, then `Re v̂(zδ) ≥ ½ e^{−|Im z| δ} ∫v`: the phase of `v̂` turns
by at most `1/10`, whatever the sign and the size of `Im z`. -/
theorem re_paperFT_profile_ge (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : |z.re| * δ ≤ 1 / 10) :
    1 / 2 * Real.exp (-(|z.im| * δ)) * (∫ u, v u) ≤ (paperFT (cplx v) (z * δ)).re := by
  set w : ℂ := z * (δ : ℂ) with hw
  have hwre : w.re = z.re * δ := by simp [hw]
  have hwim : w.im = z.im * δ := by simp [hw]
  set f : ℝ → ℂ := fun u => cplx v u * cexp (I * w * u) with hf
  have hscs : HasCompactSupport (cplx v) :=
    hasCompactSupport_of_support_subset_abs (cplx_support hsupp)
  have hfc : Continuous f := (contDiff_cplx hv).continuous.mul (by fun_prop)
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hscs.mul_right
  have hvi : Integrable v :=
    hv.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_support_subset_abs hsupp)
  have hre : ∀ u : ℝ, (f u).re =
      v u * (Real.exp (-(z.im * δ * u)) * Real.cos (z.re * δ * u)) := by
    intro u
    simp only [hf, cplx]
    rw [Complex.re_ofReal_mul, Complex.exp_re]
    have h1 : (I * w * (u : ℂ)).re = -(z.im * δ * u) := by
      simp [hwim]
    have h2 : (I * w * (u : ℂ)).im = z.re * δ * u := by
      simp [hwre]
    rw [h1, h2]
  have hlow : ∀ u : ℝ, 1 / 2 * Real.exp (-(|z.im| * δ)) * v u ≤ (f u).re := by
    intro u
    rw [hre]
    by_cases hu : v u = 0
    · simp [hu]
    have hu1 := hsupp u hu
    have hexp : Real.exp (-(|z.im| * δ)) ≤ Real.exp (-(z.im * δ * u)) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : |z.im * δ * u| ≤ |z.im| * δ := by
        rw [abs_mul, abs_mul, abs_of_pos hδ]
        calc |z.im| * δ * |u| ≤ |z.im| * δ * 1 :=
              mul_le_mul_of_nonneg_left hu1 (by positivity)
          _ = _ := mul_one _
      linarith [neg_abs_le (z.im * δ * u), le_abs_self (z.im * δ * u)]
    set x := z.re * δ * u with hx
    have hx1 : |x| ≤ 1 / 10 := by
      rw [hx, abs_mul, abs_mul, abs_of_pos hδ]
      calc |z.re| * δ * |u| ≤ 1 / 10 * 1 := mul_le_mul hz hu1 (abs_nonneg _) (by norm_num)
        _ = 1 / 10 := by norm_num
    have hx2 : x ^ 2 ≤ 1 / 100 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg x]
    have hcos : 1 / 2 ≤ Real.cos x := by
      have := Real.one_sub_sq_div_two_le_cos (x := x)
      linarith
    calc 1 / 2 * Real.exp (-(|z.im| * δ)) * v u = v u * (Real.exp (-(|z.im| * δ)) * (1 / 2)) := by
          ring
      _ ≤ v u * (Real.exp (-(z.im * δ * u)) * Real.cos x) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hexp hcos (by norm_num) (Real.exp_pos _).le) (hv0 u)
  have hreI : (∫ u, (f u).re) = (paperFT (cplx v) w).re :=
    Complex.reCLM.integral_comp_comm hfi
  rw [← hreI, ← integral_const_mul]
  exact integral_mono (hvi.const_mul _) hfi.re hlow

/-! ### The tail of the field -/

/-- The field minus a finite part is bounded by the finite sums of the rest. -/
theorem norm_tsum_sub_sum_le {ι : Type*} [DecidableEq ι] {f : ι → ℂ} (hf : Summable f) (s : Finset ι)
    {c : ℝ} (h : ∀ F : Finset ι, Disjoint F s → ∑ i ∈ F, ‖f i‖ ≤ c) :
    ‖(∑' i, f i) - ∑ i ∈ s, f i‖ ≤ c := by
  set g : ι → ℂ := fun i => if i ∈ s then 0 else f i with hg
  set k : ι → ℂ := fun i => if i ∈ s then f i else 0 with hk
  have hgn : Summable fun i => ‖g i‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hf.norm
    by_cases hi : i ∈ s
    · have h0 : g i = 0 := if_pos hi
      rw [h0, norm_zero]
      exact norm_nonneg _
    · have h0 : g i = f i := if_neg hi
      rw [h0]
  have hgs : Summable g := hgn.of_norm
  have hks : (∑' i, k i) = ∑ i ∈ s, f i := by
    rw [tsum_eq_sum (s := s) fun i hi => if_neg hi]
    exact Finset.sum_congr rfl fun i hi => if_pos hi
  have hksum : Summable k := by
    refine summable_of_ne_finset_zero (s := s) fun i hi => if_neg hi
  have hadd : f = fun i => g i + k i := by
    funext i
    by_cases hi : i ∈ s
    · simp [hg, hk, hi]
    · simp [hg, hk, hi]
  have hts : (∑' i, f i) = (∑' i, g i) + ∑ i ∈ s, f i := by
    conv_lhs => rw [hadd]
    rw [hgs.tsum_add hksum, hks]
  rw [hts, add_sub_cancel_right]
  refine (norm_tsum_le_tsum_norm hgn).trans ?_
  refine Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) fun F => ?_
  have hfilter : ∑ i ∈ F, ‖g i‖ = ∑ i ∈ F.filter (fun i => i ∉ s), ‖f i‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ s
    · have h0 : g i = 0 := if_pos hi
      rw [h0, norm_zero, if_neg (not_not.mpr hi)]
    · have h0 : g i = f i := if_neg hi
      rw [h0, if_pos hi]
  rw [hfilter]
  refine h _ (Finset.disjoint_left.2 fun i hi hi' => ?_)
  exact (Finset.mem_filter.mp hi).2 hi'

/-! ### One height -/

/-- **A bounded cluster cannot hide from all centres.** If the cluster `s ∋ ρ` lies in the sector of the window at
height `t` and the rest of the field has mass `≤ Λ` at all `N` centres, then at one of them the field is at least
`½ κ(N, M) (∫v) e^{b_ρ((M+1)h − δ)} − Λ`. -/
theorem exists_nu_norm_zeroField_ge (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {δ h t Λ : ℝ} (hδ : 0 < δ) (hh : 0 < h) {M N : ℕ}
    (hN : 1 ≤ N) (hy : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → δ < (ν : ℝ) * h)
    {s : Finset zetaZeroConfig.carrier} (hcard : s.card ≤ N)
    (hsec : ∀ ρ' ∈ s, |(ρ' : ℂ).im - t| * δ ≤ 1 / 10) {ρ : zetaZeroConfig.carrier} (hρ : ρ ∈ s)
    (hb : 1 / 2 ≤ (ρ : ℂ).re)
    (houter : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → ∀ F : Finset zetaZeroConfig.carrier, Disjoint F s →
      profileMass v * ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) *
        companionWeight δ ((ν : ℝ) * h) t ρ' ≤ Λ) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧
      1 / 2 * (∫ u, v u) * turanConstant N M *
          Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - δ)) - Λ ≤
        ‖zeroField v δ ((ν : ℝ) * h) t‖ := by
  classical
  have hs1 : s.Nonempty := ⟨ρ, hρ⟩
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image s (fun ρ' => ((ρ' : ℂ)).re) hs1
  set w : zetaZeroConfig.carrier → ℂ := fun ρ' => (zetaZeroConfig.mult ρ' : ℂ) *
    paperFT (cplx v) ((gammaOf (ρ' : ℂ) - t) * δ) with hw
  set z : zetaZeroConfig.carrier → ℂ := fun ρ' => cexp (I * (gammaOf (ρ' : ℂ) - t) * h) with hz
  set b₀ := ((i₀ : ℂ)).re - 1 / 2 with hb₀
  have hb₀ρ : (ρ : ℂ).re - 1 / 2 ≤ b₀ := by
    have := hmax ρ hρ
    rw [hb₀]
    linarith
  have hbρ0 : 0 ≤ (ρ : ℂ).re - 1 / 2 := by linarith
  have hb₀0 : 0 ≤ b₀ := by linarith
  set Z := Real.exp (b₀ * h) with hZ
  have hZ0 : 0 < Z := Real.exp_pos _
  have hzi₀ : ‖z i₀‖ = Z := norm_node_eq (i₀ : ℂ) h t
  -- the weights lie in the right half plane on the window
  have hrew : ∀ ρ' ∈ s, 1 / 2 * Real.exp (-(|(gammaOf (ρ' : ℂ) - t).im| * δ)) * (∫ u, v u) ≤
      (w ρ').re := by
    intro ρ' hρ'
    have hre : |(gammaOf (ρ' : ℂ) - t).re| * δ ≤ 1 / 10 := by
      rw [gammaOf_sub_re]
      exact hsec ρ' hρ'
    have h1 := re_paperFT_profile_ge hv hsupp hv0 hδ hre
    have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ' := by
      exact_mod_cast zetaZeroConfig.one_le_mult ρ' ρ'.2
    have e : (w ρ').re = (zetaZeroConfig.mult ρ' : ℝ) *
        (paperFT (cplx v) ((gammaOf (ρ' : ℂ) - t) * δ)).re := by
      simp only [hw]
      have e2 : ((zetaZeroConfig.mult ρ' : ℕ) : ℂ) = (((zetaZeroConfig.mult ρ' : ℕ) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [e2, Complex.re_ofReal_mul]
    rw [e]
    have h0 : 0 ≤ 1 / 2 * Real.exp (-(|(gammaOf (ρ' : ℂ) - t).im| * δ)) * (∫ u, v u) := by
      positivity
    exact h1.trans (le_mul_of_one_le_left (h0.trans h1) hm1)
  have hrew0 : ∀ ρ' ∈ s, 0 ≤ (w ρ').re := fun ρ' hρ' =>
    le_trans (by positivity) (hrew ρ' hρ')
  set β := 1 / 2 * Real.exp (-(b₀ * δ)) * (∫ u, v u) with hβdef
  have hβ0 : 0 < β := by positivity
  have hβi₀ : β ≤ (w i₀).re := by
    have h1 := hrew i₀ hi₀
    have him : |(gammaOf (i₀ : ℂ) - t).im| = b₀ := by
      rw [gammaOf_sub_im, abs_neg, abs_of_nonneg hb₀0]
    rwa [him] at h1
  -- Turán
  have htop : ∀ t' : ℝ, 1 - 1 / ((M : ℝ) + 2 * s.card + 2) ≤ t' → t' ≤ 1 →
      β ≤ ‖∑ i ∈ s.filter (fun i => t' * Z ≤ ‖z i‖), w i‖ := by
    intro t' _ ht'
    have hmem : i₀ ∈ s.filter (fun i => t' * Z ≤ ‖z i‖) := by
      refine Finset.mem_filter.mpr ⟨hi₀, ?_⟩
      rw [hzi₀]
      nlinarith
    have hsum : (w i₀).re ≤ ∑ i ∈ s.filter (fun i => t' * Z ≤ ‖z i‖), (w i).re :=
      Finset.single_le_sum (f := fun i => (w i).re)
        (fun i hi => hrew0 i (Finset.mem_filter.mp hi).1) hmem
    calc β ≤ (w i₀).re := hβi₀
      _ ≤ ∑ i ∈ s.filter (fun i => t' * Z ≤ ‖z i‖), (w i).re := hsum
      _ = (∑ i ∈ s.filter (fun i => t' * Z ≤ ‖z i‖), w i).re := (Complex.re_sum _ _).symm
      _ ≤ _ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  obtain ⟨ν, hν1, hν2, hν⟩ := HTGeometry.exists_norm_weightedPowerSum_ge_scaled s z w hZ0
    ⟨i₀, hi₀, hzi₀.ge⟩ M hβ0 htop
  have hνN : ν ≤ M + N := by omega
  refine ⟨ν, hν1, hνN, ?_⟩
  have hcard1 : 1 ≤ s.card := Finset.card_pos.2 hs1
  have hyν := hy ν hν1 hνN
  -- the Turán loss at the true size of the cluster
  have hκ : β * Z ^ ν * turanConstant N M ≤ ‖∑ i ∈ s, w i * z i ^ ν‖ := by
    refine le_trans ?_ hν
    have hle := turanConstant_le hcard1 hcard M
    have e : β * Z ^ ν / (2 * (Real.exp 1 * s.card *
        (6 * ((s.card : ℝ) + 1) * ((M : ℝ) + 2 * s.card + 2)) ^ s.card)) =
        β * Z ^ ν * turanConstant s.card M := by
      unfold turanConstant
      rw [mul_one_div]
    rw [e]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  -- the amplitude
  have hamp : Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - δ)) ≤
      Real.exp (-(b₀ * δ)) * Z ^ ν := by
    rw [hZ, ← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hM1 : ((M : ℝ) + 1) * h ≤ (ν : ℝ) * h := by
      refine mul_le_mul_of_nonneg_right ?_ hh.le
      exact_mod_cast hν1
    have hgap : 0 ≤ ((M : ℝ) + 1) * h - δ := by
      have := hy (M + 1) le_rfl (by omega)
      push_cast at this
      linarith
    have h1 : ((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - δ) ≤ b₀ * (((M : ℝ) + 1) * h - δ) :=
      mul_le_mul_of_nonneg_right hb₀ρ hgap
    have h2 : b₀ * (((M : ℝ) + 1) * h - δ) ≤ b₀ * ((ν : ℝ) * h - δ) :=
      mul_le_mul_of_nonneg_left (by linarith) hb₀0
    have e : -(b₀ * δ) + (ν : ℝ) * (b₀ * h) = b₀ * ((ν : ℝ) * h - δ) := by ring
    rw [e]
    linarith
  have hκ0 := turanConstant_pos hN M
  have hmain : 1 / 2 * (∫ u, v u) * turanConstant N M *
      Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - δ)) ≤
      ‖∑ i ∈ s, w i * z i ^ ν‖ := by
    refine le_trans ?_ hκ
    have h3 := mul_le_mul_of_nonneg_left hamp
      (by positivity : (0 : ℝ) ≤ 1 / 2 * (∫ u, v u) * turanConstant N M)
    calc _ ≤ 1 / 2 * (∫ u, v u) * turanConstant N M * (Real.exp (-(b₀ * δ)) * Z ^ ν) := h3
      _ = _ := by
          rw [hβdef]
          ring
  -- the rest of the field
  obtain ⟨hsum, -⟩ := camera_explicit_formula hv hsupp hδ hyν t
  have htail := norm_tsum_sub_sum_le hsum s (c := Λ) (fun F hF => by
    refine le_trans ?_ (houter ν hν1 hνN F hF)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ' _ => ?_
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ' := Nat.cast_nonneg _
    have hk := norm_paperFT_companion_le hv hsupp hδ ((ν : ℝ) * h) t (ρ' : ℂ)
    rw [norm_mul, Complex.norm_natCast]
    calc (zetaZeroConfig.mult ρ' : ℝ) * ‖paperFT (cameraTest v δ ((ν : ℝ) * h)) (gammaOf (ρ' : ℂ) - t)‖
        ≤ (zetaZeroConfig.mult ρ' : ℝ) * (profileMass v * companionWeight δ ((ν : ℝ) * h) t (ρ' : ℂ)) :=
          mul_le_mul_of_nonneg_left hk hm
      _ = _ := by ring)
  have hfinite : ∑ ρ' ∈ s, (zetaZeroConfig.mult ρ' : ℂ) *
      paperFT (cameraTest v δ ((ν : ℝ) * h)) (gammaOf (ρ' : ℂ) - t) = ∑ i ∈ s, w i * z i ^ ν :=
    Finset.sum_congr rfl fun ρ' _ => term_eq_weight_mul_node_pow hδ h t ν (ρ' : ℂ) _
  rw [hfinite] at htail
  have htri : ‖∑ i ∈ s, w i * z i ^ ν‖ ≤ ‖zeroField v δ ((ν : ℝ) * h) t‖ + Λ := by
    have h4 := norm_sub_norm_le (∑ i ∈ s, w i * z i ^ ν) (zeroField v δ ((ν : ℝ) * h) t)
    rw [norm_sub_rev] at h4
    have : ‖zeroField v δ ((ν : ℝ) * h) t - ∑ i ∈ s, w i * z i ^ ν‖ ≤ Λ := htail
    linarith
  linarith

/-! ### The count -/

/-- The starting exponent `⌊(1−2c)N/c⌋ − N`, so that the `N` centres lie in `[(1−3c)L, (1−2c)L]`. -/
def turanStart (c : ℝ) (N : ℕ) : ℕ := ⌊(1 - 2 * c) * N / c⌋₊ - N

theorem turanStart_bounds {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 4) {N : ℕ} (hN : 1 ≤ N) :
    ((turanStart c N : ℝ) + N) * (c / N) ≤ 1 - 2 * c ∧
      1 - 3 * c ≤ ((turanStart c N : ℝ) + 1) * (c / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set x := (1 - 2 * c) * N / c with hx
  have hx0 : 0 ≤ x := by
    have : 0 ≤ 1 - 2 * c := by linarith
    positivity
  have hxN : (N : ℝ) ≤ x := by
    rw [hx, le_div_iff₀ hc0]
    nlinarith
  have hfloor1 : N ≤ ⌊x⌋₊ := Nat.le_floor hxN
  have hcast : ((turanStart c N : ℕ) : ℝ) + N = (⌊x⌋₊ : ℝ) := by
    unfold turanStart
    rw [Nat.cast_sub hfloor1]
    ring
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hxc : x * (c / N) = 1 - 2 * c := by
    rw [hx]
    field_simp
  have hcN : 0 < c / N := by positivity
  constructor
  · rw [hcast, ← hxc]
    exact mul_le_mul_of_nonneg_right hle hcN.le
  · have h1 : x - N ≤ (turanStart c N : ℝ) + 1 := by
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hcN.le
    have e : (x - N) * (c / N) = 1 - 3 * c := by
      rw [sub_mul, hxc]
      field_simp
      ring
    rw [e] at h2
    exact h2

/-- `ρ` sits in a cluster of at most `N` zeros at the camera `(δ, h, M)`: at every height of its window, some family
`s ∋ ρ` of at most `N` zeros lies in the sector, and the other zeros carry weighted mass at most a quarter of the Turán
constant times the amplitude of `ρ`, at all `N` centres. -/
def ClusterAt (v : ℝ → ℝ) (δ h : ℝ) (M N : ℕ) (ρ : zetaZeroConfig.carrier) : Prop :=
  ∀ t : ℝ, |t - (ρ : ℂ).im| ≤ 1 / (10 * δ) → ∃ s : Finset zetaZeroConfig.carrier, ρ ∈ s ∧ s.card ≤ N ∧
    (∀ ρ' ∈ s, |(ρ' : ℂ).im - t| * δ ≤ 1 / 10) ∧
    ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → ∀ F : Finset zetaZeroConfig.carrier, Disjoint F s →
      profileMass v * ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) *
        companionWeight δ ((ν : ℝ) * h) t ρ' ≤
      1 / 4 * (∫ u, v u) * turanConstant N M *
        Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - δ))

/-- **The Turán camera bounds separated clustered zeros.** With `δ = cL`, `h = cL/N`, separated zeros of depth
`≥ α/L` in `[T+1, 2T−1]` sitting in clusters of at most `N` zeros number `≪_{c,N} T L e^{−2(1−4c)α}`. -/
theorem exists_card_clustered_zeros_le (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 4) {N : ℕ}
    (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α : ℝ, 0 ≤ α → ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, 1 / 2 + α / Real.log T ≤ (ρ : ℂ).re ∧ T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧
        ClusterAt v (c * Real.log T) (c / N * Real.log T) (turanStart c N) N ρ) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      (S.card : ℝ) ≤ C * T * Real.log T * Real.exp (-(2 * (1 - 4 * c) * α)) := by
  classical
  obtain ⟨C₀, L₁, hC₀0, hvol⟩ := exists_volume_zeroField_ge_le_uniform hv hsupp
  set Iv := ∫ u, v u with hIvdef
  set M := turanStart c N with hMdef
  set κ := turanConstant N M with hκdef
  have hκ0 : 0 < κ := turanConstant_pos hN M
  obtain ⟨hMup, hMlow⟩ := turanStart_bounds hc0 hc hN
  rw [← hMdef] at hMup hMlow
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨80 * N * C₀ / (c * Iv ^ 2 * κ ^ 2), by positivity, ?_⟩
  have hL : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop 3, hL.eventually_ge_atTop (max 1 L₁),
    hL.eventually_ge_atTop (1 / c), hL.eventually_ge_atTop (64 / c ^ 2)]
    with T hT3 hL₀ hLc hLd α hα S hS hsep
  have hL1 : 1 ≤ Real.log T := (le_max_left _ _).trans hL₀
  have hL₁ : L₁ ≤ Real.log T := (le_max_right _ _).trans hL₀
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  set L := Real.log T with hLdef
  have hδ1 : 1 ≤ c * L := by
    rw [div_le_iff₀ hc0] at hLc
    linarith
  have hδ0 : 0 < c * L := by linarith
  set h := c / N * L with hhdef
  have hh0 : 0 < h := by positivity
  set r := 1 / (10 * (c * L)) with hrdef
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one (by positivity)]
    linarith
  have h14 : 0 < 1 - 4 * c := by linarith
  -- the centres
  have hcentre : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N →
      (1 - 3 * c) * L ≤ (ν : ℝ) * h ∧ (ν : ℝ) * h ≤ (1 - 2 * c) * L := by
    intro ν h1 h2
    have h1' : (M : ℝ) + 1 ≤ ν := by exact_mod_cast h1
    have h2' : (ν : ℝ) ≤ (M : ℝ) + N := by exact_mod_cast h2
    have hcN : 0 < c / N := by positivity
    constructor
    · calc (1 - 3 * c) * L ≤ (((M : ℝ) + 1) * (c / N)) * L :=
            mul_le_mul_of_nonneg_right hMlow hL0.le
        _ ≤ ((ν : ℝ) * (c / N)) * L :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1' hcN.le) hL0.le
        _ = (ν : ℝ) * h := by
            rw [hhdef]
            ring
    · calc (ν : ℝ) * h = ((ν : ℝ) * (c / N)) * L := by
            rw [hhdef]
            ring
        _ ≤ (((M : ℝ) + N) * (c / N)) * L :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2' hcN.le) hL0.le
        _ ≤ (1 - 2 * c) * L := mul_le_mul_of_nonneg_right hMup hL0.le
  have hyδ : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → c * L < (ν : ℝ) * h := by
    intro ν h1 h2
    have := (hcentre ν h1 h2).1
    nlinarith
  have hyL : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → (ν : ℝ) * h + c * L ≤ (1 - c) * L := by
    intro ν h1 h2
    have := (hcentre ν h1 h2).2
    nlinarith
  set lam := 1 / 4 * Iv * κ * Real.exp ((1 - 4 * c) * α) with hlamdef
  have hlam : 0 < lam := by positivity
  set D : ℕ → Set ℝ := fun ν => {t | t ∈ Ioc T (2 * T) ∧
    lam ≤ ‖zeroField v (c * L) ((ν : ℝ) * h) t‖} with hD
  have hsubset : ∀ ρ ∈ S, Ioo ((ρ : ℂ).im - r) ((ρ : ℂ).im + r) ⊆
      ⋃ ν ∈ Finset.Icc (M + 1) (M + N), D ν := by
    intro ρ hρ t ht
    obtain ⟨hdepth, hlow, hhigh, hcl⟩ := hS ρ hρ
    have habs : |t - (ρ : ℂ).im| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    obtain ⟨s, hρs, hcard, hsec, houter⟩ := hcl t habs
    have hαL : 0 ≤ α / L := by positivity
    have hb : 1 / 2 ≤ (ρ : ℂ).re := by linarith
    obtain ⟨ν, hν1, hν2, hν⟩ := exists_nu_norm_zeroField_ge hv hsupp hv0 hI hδ0 hh0 hN hyδ hcard hsec
      hρs hb houter
    refine Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hν1, hν2⟩)) ?_
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    have hexp : (1 - 4 * c) * α ≤ ((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - c * L) := by
      have h1 : α / L ≤ (ρ : ℂ).re - 1 / 2 := by linarith
      have h2 : (1 - 4 * c) * L ≤ ((M : ℝ) + 1) * h - c * L := by
        have := (hcentre (M + 1) le_rfl (by omega)).1
        push_cast at this
        linarith
      have h3 : 0 ≤ (1 - 4 * c) * L := by positivity
      have h4 : α / L * ((1 - 4 * c) * L) = (1 - 4 * c) * α := by
        field_simp
      have h5 : α / L * ((1 - 4 * c) * L) ≤
          ((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - c * L) :=
        mul_le_mul h1 h2 h3 (by linarith)
      linarith
    have hexp' := Real.exp_le_exp.2 hexp
    have hcoef : 0 ≤ 1 / 4 * Iv * κ := by positivity
    have h6 := mul_le_mul_of_nonneg_left hexp' hcoef
    rw [hlamdef]
    have e : 1 / 2 * Iv * κ * Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - c * L)) -
        1 / 4 * Iv * κ * Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - c * L)) =
        1 / 4 * Iv * κ * Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - c * L)) := by
      ring
    linarith
  have hsep' : ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 2 * r ≤ |(ρ : ℂ).im - (ρ' : ℂ).im| := by
    intro ρ hρ ρ' hρ' hne
    have e : 2 * r = 1 / (5 * (c * L)) := by
      rw [hrdef]
      field_simp
      norm_num
    rw [e]
    exact hsep ρ hρ ρ' hρ' hne
  have hunion := volume_biUnion_windows_eq S (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im) hsep'
  have hDν : ∀ ν ∈ Finset.Icc (M + 1) (M + N), volume (D ν) ≤
      ENNReal.ofReal (C₀ / c ^ 2 * T / lam ^ 2) := by
    intro ν hν
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hν
    exact hvol T c ((ν : ℝ) * h) lam hT3 hL₁ hc0 (by linarith) hLc hLd (hyδ ν h1 h2) (hyL ν h1 h2)
      hlam
  have hle : volume (⋃ ρ ∈ S, Ioo ((ρ : ℂ).im - r) ((ρ : ℂ).im + r)) ≤
      ENNReal.ofReal ((N : ℝ) * (C₀ / c ^ 2 * T / lam ^ 2)) := by
    refine (measure_mono (Set.iUnion₂_subset hsubset)).trans ?_
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum hDν).trans ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
    have e : M + N + 1 - (M + 1) = N := by omega
    rw [e]
  rw [hunion] at hle
  have hreal : (S.card : ℝ) * (2 * r) ≤ (N : ℝ) * (C₀ / c ^ 2 * T / lam ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
  have hlamsq : lam ^ 2 = Iv ^ 2 * κ ^ 2 / 16 * Real.exp (2 * (1 - 4 * c) * α) := by
    rw [hlamdef, mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have he : Real.exp (-(2 * (1 - 4 * c) * α)) = (Real.exp (2 * (1 - 4 * c) * α))⁻¹ :=
    Real.exp_neg _
  have h2r : (2 * r)⁻¹ = 5 * (c * L) := by
    rw [hrdef]
    field_simp
    norm_num
  have h2r0 : 0 < 2 * r := by positivity
  calc (S.card : ℝ) = (S.card : ℝ) * (2 * r) * (2 * r)⁻¹ := by field_simp
    _ ≤ (N : ℝ) * (C₀ / c ^ 2 * T / lam ^ 2) * (2 * r)⁻¹ :=
        mul_le_mul_of_nonneg_right hreal (by positivity)
    _ = 80 * N * C₀ / (c * Iv ^ 2 * κ ^ 2) * T * L * Real.exp (-(2 * (1 - 4 * c) * α)) := by
        rw [hlamsq, h2r, he]
        field_simp
        ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
