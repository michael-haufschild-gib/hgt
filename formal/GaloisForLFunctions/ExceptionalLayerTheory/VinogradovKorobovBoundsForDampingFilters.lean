import GaloisForLFunctions.ExceptionalLayerTheory.ZeroFreeBoundsForDampingFilters
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovLogDeriv

/-!
# Vinogradov–Korobov bounds for the complete prime filter

A local Mellin shift keeps the entire divisor filter and its spacing power.
The actual zero-free width supplies a saving beyond every fixed inverse-log
saving, with no exceptional-layer assumption.
-/

open Complex Filter Set Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A coarse lower bound for the actual width suffices to absorb every fixed
polynomial in height into the saving. -/
theorem inv_vkHadamardWidth_le_log_cube {T : ℝ}
    (hT : Real.exp (Real.exp 1) ≤ T) :
    (vkHadamardWidth T)⁻¹ ≤ 10 ^ 8 * Real.log T ^ 3 := by
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hT
  have hL : Real.exp 1 ≤ Real.log T := (Real.le_log_iff_exp_le hT0).mpr hT
  have hL1 : 1 ≤ Real.log T := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < Real.log T := (Real.exp_pos _).trans_le hL
  have hLL : 1 ≤ Real.log (Real.log T) := (Real.le_log_iff_exp_le hL0).mpr hL
  have he : (vkHadamardWidth T)⁻¹ =
      10 ^ 8 * Real.log T ^ ((2 : ℝ) / 3) *
        Real.log (Real.log T) ^ ((5 : ℝ) / 3) := by
    rw [vkHadamardWidth, inv_div, div_eq_mul_inv, mul_inv,
      show -(2 : ℝ) / 3 = -((2 : ℝ) / 3) by ring,
      show -(5 : ℝ) / 3 = -((5 : ℝ) / 3) by ring,
      Real.rpow_neg hL0.le, Real.rpow_neg (by linarith only [hLL] : 0 ≤ Real.log (Real.log T)),
      inv_inv, inv_inv]
    ring
  have hp1 : Real.log T ^ ((2 : ℝ) / 3) ≤ Real.log T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL1
      (by norm_num : (2 : ℝ) / 3 ≤ 1)
  have hp2 : Real.log (Real.log T) ^ ((5 : ℝ) / 3) ≤ Real.log T ^ (2 : ℕ) := by
    calc
      _ ≤ Real.log (Real.log T) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLL (by norm_num)
      _ = Real.log (Real.log T) ^ (2 : ℕ) := by norm_num
      _ ≤ Real.log T ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by linarith only [hLL]) (Real.log_le_self hL0.le) 2
  rw [he]
  calc
    _ ≤ 10 ^ 8 * Real.log T * Real.log T ^ (2 : ℕ) := by gcongr
    _ = _ := by ring

theorem tendsto_vkHadamardWidth_zero : Tendsto vkHadamardWidth atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1))] with T hT
    exact hε.trans (vkHadamardWidth_pos hT)
  · intro ε hε
    filter_upwards [eventually_ge_atTop
      (Real.exp (max (Real.exp 1) ((10 ^ 8 * (ε / 2)) ^ (-(3 : ℝ) / 2))))] with T hT
    exact (vkHadamardWidth_le (by linarith only [hε] : 0 < ε / 2) hT).trans_lt
      (by linarith only [hε])

/-- All total zeta heights in the local Mellin rectangle share the actual
Vinogradov–Korobov width and a polynomial logarithmic-derivative bound. -/
theorem eventually_zeta_vk_local_rectangle :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ x v : ℝ,
      1 - vkHadamardWidth (2 * t + 1) / 2 ≤ x → x ≤ 9 / 8 → |v| ≤ t / 2 →
      riemannZeta ((x : ℂ) + ((t + v : ℝ) : ℂ) * I) ≠ 0 ∧
      ‖logDeriv riemannZeta ((x : ℂ) + ((t + v : ℝ) : ℂ) * I)‖ ≤ D * (1 + t) ^ 4 := by
  obtain ⟨T₀, C, hT₀, hC, hz, hd⟩ := Sieve.exists_logDeriv_zeta_bound_vk
  let H := Sieve.vkLogDerivThreshold T₀ + 1
  have hHT : T₀ ≤ H := by
    dsimp only [H, Sieve.vkLogDerivThreshold]
    have hh : T₀ ≤ max (max T₀ 4)
        (Real.exp (max (Real.exp 1) ((10 ^ 8 * (1 / 80 : ℝ)) ^ (-(3 : ℝ) / 2)))) :=
      (le_max_left _ _).trans (le_max_left _ _)
    linarith only [hh]
  refine ⟨C * 10 ^ 8 * 81, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * H), eventually_ge_atTop (2 : ℝ)] with t htH ht2
  intro x v hx hx1 hv
  have hv' := abs_le.mp hv
  have hγH : H ≤ t + v := by linarith only [htH, hv'.1]
  have hγE : Real.exp (Real.exp 1) ≤ t + v := hT₀.trans (hHT.trans hγH)
  have hγ0 : 0 < t + v := (Real.exp_pos _).trans_le hγE
  have hγ2 : t + v + 1 ≤ 2 * t + 1 := by linarith only [hv'.2, ht2]
  have h2E : Real.exp (Real.exp 1) ≤ 2 * t + 1 :=
    hγE.trans (by linarith only [hγ2])
  have hwp := vkHadamardWidth_pos h2E
  have hmono := vkHadamardWidth_anti (T := t + v + 1)
    (hγE.trans (by linarith)) hγ2
  have hmono0 := vkHadamardWidth_anti hγE (by linarith only [hγ2] : t + v ≤ 2 * t + 1)
  have hlow : 1 - vkHadamardWidth (t + v + 1) / 2 ≤ x := by linarith only [hx, hmono]
  have hzero : riemannZeta ((x : ℂ) + ((t + v : ℝ) : ℂ) * I) ≠ 0 := by
    by_cases hx2 : x ≤ 1
    · apply hz x (t + v) (by rw [abs_of_pos hγ0]; exact hHT.trans hγH) hx2
      rw [abs_of_pos hγ0]
      linarith only [hx, hmono0, hwp]
    · exact riemannZeta_ne_zero_of_one_lt_re (by simpa using lt_of_not_ge hx2)
  refine ⟨hzero, ?_⟩
  have hb := hd x (t + v) (by rw [abs_of_pos hγ0]; exact hγH)
    (by simpa only [abs_of_pos hγ0] using hlow) hx1
  rw [abs_of_pos hγ0] at hb
  have hlog0 : 0 ≤ Real.log (t + v) := Real.log_nonneg
    ((Real.one_le_exp (by positivity)).trans hγE)
  have hlog : Real.log (t + v) ≤ Real.log (2 * t + 1) :=
    Real.log_le_log hγ0 (by linarith only [hγ2])
  have hL0 : 0 ≤ Real.log (2 * t + 1) := hlog0.trans hlog
  have hL : Real.log (2 * t + 1) ≤ 3 * (1 + t) := by
    have hh := Real.log_le_self (by linarith only [ht2] : 0 ≤ 2 * t + 1)
    linarith only [hh, ht2]
  calc
    _ ≤ C * Real.log (t + v) / vkHadamardWidth (t + v + 1) := hb
    _ ≤ C * Real.log (2 * t + 1) / vkHadamardWidth (2 * t + 1) := by
      exact (div_le_div_of_nonneg_left (by positivity) hwp hmono).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC.le) hwp.le)
    _ ≤ C * Real.log (2 * t + 1) * (10 ^ 8 * Real.log (2 * t + 1) ^ 3) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_vkHadamardWidth_le_log_cube h2E) (by positivity)
    _ = C * 10 ^ 8 * Real.log (2 * t + 1) ^ 4 := by ring
    _ ≤ C * 10 ^ 8 * (3 * (1 + t)) ^ 4 := by gcongr
    _ = _ := by ring

private def filteredMellinIntegrand (P : Polynomial ℂ) (s : ℂ)
    (β h y : ℝ) (w : ℂ) : ℂ :=
  P.eval (Complex.exp ((h : ℂ) * (s + w - β))) *
    gaussianMBKernel y w * (-logDeriv riemannZeta (s + w))

private theorem differentiableAt_filteredMellinIntegrand (P : Polynomial ℂ)
    (s : ℂ) (β h : ℝ) {y : ℝ} (hy : 0 < y) {w : ℂ}
    (hw : 0 < w.re) (hs : s + w ≠ 1) (hz : riemannZeta (s + w) ≠ 0) :
    DifferentiableAt ℂ (filteredMellinIntegrand P s β h y) w := by
  have hG : DifferentiableAt ℂ Complex.Gamma (w / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have he := congrArg Complex.re hm
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at he
    linarith only [hw, he, Nat.cast_nonneg (α := ℝ) m]
  have hK : DifferentiableAt ℂ (gaussianMBKernel y) w := by
    unfold gaussianMBKernel
    exact ((hG.comp w (differentiableAt_id.div_const 2)).const_mul (1 / 2)).mul
      ((differentiableAt_id.div_const 2).neg.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne')))
  have hza : AnalyticAt ℂ riemannZeta (s + w) := by
    have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ :=
      fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)
  have hld : DifferentiableAt ℂ (logDeriv riemannZeta) (s + w) := by
    rw [show logDeriv riemannZeta = (fun z => deriv riemannZeta z / riemannZeta z) by
      funext z; rw [logDeriv_apply]]
    exact hza.deriv.differentiableAt.div hza.differentiableAt hz
  have hP : DifferentiableAt ℂ
      (fun z : ℂ => P.eval (Complex.exp ((h : ℂ) * (s + z - β)))) w := by
    exact P.differentiable.differentiableAt.comp w
      (((differentiableAt_id.const_add s).sub_const (β : ℂ)).const_mul (h : ℂ)).cexp
  exact (hP.mul hK).mul ((hld.comp w (differentiableAt_id.const_add s)).neg)

private theorem norm_vertical_integral_le_rect {G : ℂ → ℂ} {c r K : ℝ}
    (hG : DifferentiableOn ℂ G (uIcc c r ×ℂ uIcc (-K) K)) :
    ‖∫ v in (-K)..K, G ((r : ℂ) + v * I)‖ ≤
      ‖∫ v in (-K)..K, G ((c : ℂ) + v * I)‖ +
      ‖∫ x in c..r, G ((x : ℂ) + (-K : ℝ) * I)‖ +
      ‖∫ x in c..r, G ((x : ℂ) + K * I)‖ := by
  have h := Sieve.integral_vertical_sub_eq_horizontal_rect K hG
  set R := ∫ v in (-K)..K, G ((r : ℂ) + v * I)
  set L := ∫ v in (-K)..K, G ((c : ℂ) + v * I)
  set Bt := ∫ x in c..r, G ((x : ℂ) + (-K : ℝ) * I)
  set Tp := ∫ x in c..r, G ((x : ℂ) + K * I)
  have he : I • R = I • L - Bt + Tp := by
    change I • R - I • L = Tp - Bt at h
    linear_combination h
  have hn : ‖R‖ = ‖I • R‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [hn, he]
  calc
    _ ≤ ‖I • L - Bt‖ + ‖Tp‖ := norm_add_le _ _
    _ ≤ ‖I • L‖ + ‖Bt‖ + ‖Tp‖ := by gcongr; exact norm_sub_le _ _
    _ = _ := by rw [norm_smul, Complex.norm_I, one_mul]

private theorem norm_integral_le_shifted_rectangle {G : ℂ → ℂ}
    {A b c r K V E : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) (hcr : c ≤ r)
    (hK : 0 ≤ K) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hGi : Integrable (fun v : ℝ => G ((r : ℂ) + v * I)))
    (hGd : DifferentiableOn ℂ G (uIcc c r ×ℂ uIcc (-K) K))
    (hline : ∀ v : ℝ, ‖G ((r : ℂ) + v * I)‖ ≤
      A * Real.exp (b * r) * E * Real.exp (-(|v| / 2)))
    (hrect : ∀ x v : ℝ, c ≤ x → x ≤ r → |v| ≤ K →
      ‖G ((x : ℂ) + v * I)‖ ≤
        A * Real.exp (b * x) * V * Real.exp (-(|v| / 2))) :
    ‖∫ v : ℝ, G ((r : ℂ) + v * I)‖ ≤ A *
      (Real.exp (b * c) * V * (2 * K) +
        Real.exp (b * r) * V * Real.exp (-(K / 2)) * (2 * (r - c)) +
        Real.exp (b * r) * E * Real.exp (-(K / 4)) *
          ∫ v : ℝ, Real.exp (-((1 / 4 : ℝ) * |v|))) := by
  have hleft : ‖∫ v in (-K)..K, G ((c : ℂ) + v * I)‖ ≤
      A * Real.exp (b * c) * V * (2 * K) := by
    have hpt : ∀ v ∈ uIoc (-K) K,
        ‖G ((c : ℂ) + v * I)‖ ≤ A * Real.exp (b * c) * V := by
      intro v hv
      rw [uIoc_of_le (by linarith only [hK])] at hv
      have hvK : |v| ≤ K := abs_le.mpr ⟨hv.1.le, hv.2⟩
      exact (hrect c v le_rfl hcr hvK).trans
        (mul_le_of_le_one_right (by positivity)
          (Real.exp_le_one_iff.mpr (by linarith only [abs_nonneg v])))
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans_eq ?_
    rw [show K - -K = 2 * K by ring, abs_of_nonneg (by positivity)]
  have hedge (v : ℝ) (hv : |v| = K) :
      ‖∫ x in c..r, G ((x : ℂ) + v * I)‖ ≤
        A * Real.exp (b * r) * V * Real.exp (-(K / 2)) * (r - c) := by
    have hpt : ∀ x ∈ uIoc c r, ‖G ((x : ℂ) + v * I)‖ ≤
        A * Real.exp (b * r) * V * Real.exp (-(K / 2)) := by
      intro x hx
      rw [uIoc_of_le hcr] at hx
      have hh := hrect x v hx.1.le hx.2 hv.le
      rw [hv] at hh
      exact hh.trans (by gcongr; exact hx.2)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans_eq ?_
    rw [abs_of_nonneg (sub_nonneg.mpr hcr)]
  have htail := MoebiusAbel.norm_integral_sub_intervalIntegral_le hGi hK
    (by positivity : 0 ≤ A * Real.exp (b * r) * E) hline
  have hmid := (norm_vertical_integral_le_rect hGd).trans
    (add_le_add (add_le_add hleft (hedge (-K) (by rw [abs_neg, abs_of_nonneg hK])))
      (hedge K (abs_of_nonneg hK)))
  calc
    _ ≤ ‖∫ v in (-K)..K, G ((r : ℂ) + v * I)‖ +
        ‖(∫ v : ℝ, G ((r : ℂ) + v * I)) -
          ∫ v in (-K)..K, G ((r : ℂ) + v * I)‖ := by
      convert norm_add_le
        (∫ v in (-K)..K, G ((r : ℂ) + v * I))
        ((∫ v : ℝ, G ((r : ℂ) + v * I)) -
          ∫ v in (-K)..K, G ((r : ℂ) + v * I)) using 1
      congr 1
      abel
    _ ≤ _ := (add_le_add hmid htail).trans_eq (by ring)


/-- A local contour shift separates the zero-free saving from the exponentially
smaller truncation error, uniformly in the damping spacing. -/
theorem exists_primeDampingFilter_vk_local_shift_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β a r : ℝ) (hσ : σ < 1) (ha : 0 < a)
    (hr : 1 < r) (hr1 : r ≤ 9 / 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      ‖primeDampingFilter (divisorDampingFilter F ρ β h) σ β a h t‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + t) ^ ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card) + 5) *
          (Real.exp (a * t * (1 - σ - vkHadamardWidth (2 * t + 1) / 2) / 2) +
            Real.exp (a * t * (r - σ) / 2 - t / 8)) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let l := (1 - σ) / 2
  let u := r - σ
  have hl : 0 < l := by dsimp only [l]; linarith only [hσ]
  have hu : 0 < u := by dsimp only [u]; linarith only [hσ, hr]
  obtain ⟨A, hA, hkernel⟩ := exists_divisorFilter_kernel_strip_envelope F ρ σ β l u hl
  obtain ⟨D, hD, hrectangle⟩ := eventually_zeta_vk_local_rectangle
  let E := (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ r) + 1
  have hE : 0 < E := by
    have hs : 0 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ r :=
      tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    dsimp only [E]
    linarith only [hs]
  let J := ∫ v : ℝ, Real.exp (-((1 / 4 : ℝ) * |v|))
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  let B := D + 2 * u * D + E * J + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  let k := 1 / (2 * Real.pi)
  have hk : 0 < k := by dsimp only [k]; positivity
  refine ⟨k * A * B, by positivity, ?_⟩
  have hwidthlim : Tendsto (fun t : ℝ => vkHadamardWidth (2 * t + 1)) atTop (𝓝 0) :=
    tendsto_vkHadamardWidth_zero.comp
      (tendsto_atTop_add_const_right atTop 1
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have hsmall : ∀ᶠ t : ℝ in atTop, vkHadamardWidth (2 * t + 1) / 2 < l := by
    filter_upwards [hwidthlim.eventually (gt_mem_nhds (show 0 < 2 * l by positivity))] with t ht
    linarith only [ht]
  filter_upwards [hrectangle, hsmall, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (Real.exp (Real.exp 1))] with t htR htη ht2 htE
  intro h hh hh1
  have ht : 0 < t := by linarith only [ht2]
  have hw : 0 < vkHadamardWidth (2 * t + 1) :=
    vkHadamardWidth_pos (by linarith only [htE, ht2])
  let c := 1 - σ - vkHadamardWidth (2 * t + 1) / 2
  have hcl : l ≤ c := by dsimp only [c, l] at *; linarith only [htη]
  have hc : 0 < c := hl.trans_le hcl
  have hcu : c ≤ u := by
    dsimp only [c, u]
    linarith only [hw, hr]
  let s : ℂ := (σ : ℂ) + t * I
  let P := divisorDampingFilter F ρ β h
  let G := filteredMellinIntegrand P s β h (Real.exp (-a * t))
  let M := A * h ^ d * (1 + t) ^ d
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hcoord (x v : ℝ) : s + ((x : ℂ) + v * I) =
      ((σ + x : ℝ) : ℂ) + ((t + v : ℝ) : ℂ) * I := by dsimp only [s]; push_cast; ring
  have hre (v : ℝ) : (s + ((u : ℂ) + v * I)).re = r := by
    rw [hcoord]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    dsimp only [u]
    ring
  have heuler (v : ℝ) :
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (s + ((u : ℂ) + v * I)) = -logDeriv riemannZeta (s + ((u : ℂ) + v * I)) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (by rw [hre]; exact hr), logDeriv_apply, neg_div]
  have hL (v : ℝ) : ‖logDeriv riemannZeta (s + ((u : ℂ) + v * I))‖ ≤ E := by
    have hn := norm_LSeries_vonMangoldt_le
      (s := s + ((u : ℂ) + v * I)) (by rw [hre]; exact hr)
    rw [heuler, norm_neg, hre] at hn
    exact hn.trans (by dsimp only [E]; linarith)
  have hK (x v : ℝ) (hx : l ≤ x) (hx1 : x ≤ u) :
      ‖P.eval (Complex.exp ((h : ℂ) * (s + ((x : ℂ) + v * I) - β))) *
        gaussianMBKernel (Real.exp (-a * t)) ((x : ℂ) + v * I)‖ ≤
      M * Real.exp (a * t * x / 2) * Real.exp (-(|v| / 2)) := by
    have he : (Real.exp (-a * t)) ^ (-(x / 2)) = Real.exp (a * t * x / 2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    simpa only [P, s, M, d, abs_of_pos ht, he] using
      hkernel (Real.exp (-a * t)) h t x v (Real.exp_pos _) hh hh1 hx hx1
  have hline (v : ℝ) : ‖G ((u : ℂ) + v * I)‖ ≤
      M * Real.exp (a * t * u / 2) * E * Real.exp (-(|v| / 2)) := by
    change ‖(_ * _) * (-logDeriv riemannZeta (s + ((u : ℂ) + v * I)))‖ ≤ _
    rw [norm_mul, norm_neg]
    calc
      _ ≤ (M * Real.exp (a * t * u / 2) * Real.exp (-(|v| / 2))) * E :=
        mul_le_mul (hK u v (hcl.trans hcu) le_rfl) (hL v) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hGc : Continuous (fun v : ℝ => G ((u : ℂ) + v * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hs1 : s + ((u : ℂ) + v * I) ≠ 1 := by
      intro he
      have h := congrArg Complex.re he
      rw [hre, Complex.one_re] at h
      linarith only [h, hr]
    have hg : ContinuousAt G ((u : ℂ) + v * I) :=
      (differentiableAt_filteredMellinIntegrand P s β h
      (y := Real.exp (-a * t)) (Real.exp_pos _)
      (by simpa using hu) hs1
      (riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; exact hr))).continuousAt
    exact hg.comp (f := fun v : ℝ => (u : ℂ) + v * I) (by fun_prop)
  have hGi : Integrable (fun v : ℝ => G ((u : ℂ) + v * I)) := by
    have hi : Integrable (fun v : ℝ =>
        M * Real.exp (a * t * u / 2) * E * Real.exp (-(|v| / 2))) := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using
        (integrable_exp_neg_mul_abs' (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
          (M * Real.exp (a * t * u / 2) * E)
    exact hi.mono' hGc.aestronglyMeasurable (Eventually.of_forall hline)
  have hrect (x v : ℝ) (hx : c ≤ x) (hx1 : x ≤ u) (hv : |v| ≤ t / 2) :
      ‖G ((x : ℂ) + v * I)‖ ≤
        M * Real.exp (a * t * x / 2) * (D * (1 + t) ^ 4) *
          Real.exp (-(|v| / 2)) := by
    have hb := (htR (σ + x) v
      (by dsimp only [c] at hx; linarith only [hx])
      (by dsimp only [u] at hx1; linarith only [hx1, hr1]) hv).2
    rw [← hcoord] at hb
    change ‖(_ * _) * (-logDeriv riemannZeta (s + ((x : ℂ) + v * I)))‖ ≤ _
    rw [norm_mul, norm_neg]
    calc
      _ ≤ (M * Real.exp (a * t * x / 2) * Real.exp (-(|v| / 2))) *
          (D * (1 + t) ^ 4) :=
        mul_le_mul (hK x v (hcl.trans hx) hx1) hb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hGd : DifferentiableOn ℂ G (uIcc c u ×ℂ uIcc (-(t / 2)) (t / 2)) := by
    intro w hw
    obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hw
    rw [uIcc_of_le hcu] at hwre
    rw [uIcc_of_le (by linarith only [ht])] at hwim
    have hv : |w.im| ≤ t / 2 := abs_le.mpr hwim
    have he : s + w = ((σ + w.re : ℝ) : ℂ) + ((t + w.im : ℝ) : ℂ) * I := by
      rw [← hcoord]
      congr 1
      exact (Complex.re_add_im w).symm
    have hzw := (htR (σ + w.re) w.im
      (by dsimp only [c] at hwre; linarith only [hwre.1])
      (by dsimp only [u] at hwre; linarith only [hwre.2, hr1]) hv).1
    rw [← he] at hzw
    have hs1 : s + w ≠ 1 := by
      intro hh
      have him := congrArg Complex.im hh
      simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
        add_zero, zero_add, Complex.one_im] at him
      linarith only [him, hwim.1, ht]
    exact (differentiableAt_filteredMellinIntegrand P s β h (Real.exp_pos _)
      (hc.trans_le hwre.1) hs1 hzw).differentiableWithinAt
  have hscale (x : ℝ) : a * t / 2 * x = a * t * x / 2 := by ring
  have hbound := norm_integral_le_shifted_rectangle hM
    (by positivity : 0 ≤ a * t / 2) hcu (by positivity : 0 ≤ t / 2)
    (by positivity : 0 ≤ D * (1 + t) ^ 4) hE.le hGi hGd
    (by intro v; rw [hscale]; exact hline v)
    (by intro x v hx hx1 hv; rw [hscale]; exact hrect x v hx hx1 hv)
  have hid : primeDampingFilter P σ β a h t = (k : ℂ) * ∫ v : ℝ, G ((u : ℂ) + v * I) := by
    rw [primeDampingFilter_eq_euler_integral P σ β a h t u hu
      (by dsimp only [u]; linarith only [hr])]
    congr 1
    apply integral_congr_ae
    refine Eventually.of_forall fun v => ?_
    change _ = filteredMellinIntegrand P s β h (Real.exp (-a * t)) ((u : ℂ) + v * I)
    rw [filteredMellinIntegrand, ← heuler]
  let L := Real.exp (a * t * c / 2)
  let R := Real.exp (a * t * u / 2 - t / 8)
  have hL0 : 0 ≤ L := (Real.exp_pos _).le
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hp45 : (1 + t) ^ 4 ≤ (1 + t) ^ 5 :=
    pow_le_pow_right₀ (by linarith only [ht]) (by norm_num)
  have hp5 : 1 ≤ (1 + t) ^ 5 := one_le_pow₀ (by linarith only [ht])
  have hleft : Real.exp (a * t / 2 * c) * (D * (1 + t) ^ 4) * (2 * (t / 2)) ≤
      D * (1 + t) ^ 5 * L := by
    have he : a * t / 2 * c = a * t * c / 2 := by ring
    rw [he]
    change L * (D * (1 + t) ^ 4) * (2 * (t / 2)) ≤ _
    have hp : (1 + t) ^ 4 * t ≤ (1 + t) ^ 5 := by
      have hp : 0 ≤ (1 + t) ^ 4 := by positivity
      have he : (1 + t) ^ 5 = (1 + t) ^ 4 * (1 + t) := by rw [pow_succ]
      rw [he]
      nlinarith only [hp]
    nlinarith only [mul_le_mul_of_nonneg_left hp (mul_nonneg hD.le hL0)]
  have hedge : Real.exp (a * t / 2 * u) * (D * (1 + t) ^ 4) *
        Real.exp (-(t / 2 / 2)) * (2 * (u - c)) ≤
      2 * u * D * (1 + t) ^ 5 * R := by
    calc
      _ ≤ Real.exp (a * t / 2 * u) * (D * (1 + t) ^ 5) *
          Real.exp (-(t / 8)) * (2 * u) := by
        have he : Real.exp (-(t / 2 / 2)) ≤ Real.exp (-(t / 8)) :=
          Real.exp_le_exp.mpr (by linarith only [ht])
        have hp := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hp45 hD.le) (Real.exp_pos (a * t / 2 * u)).le
        exact mul_le_mul (mul_le_mul hp he (by positivity) (by positivity))
          (by linarith only [hc]) (by linarith only [hcu]) (by positivity)
      _ = _ := by
        dsimp only [R]
        rw [show a * t * u / 2 - t / 8 = a * t / 2 * u + -(t / 8) by ring,
          Real.exp_add]
        ring
  have htail : Real.exp (a * t / 2 * u) * E * Real.exp (-(t / 2 / 4)) * J ≤
      E * J * (1 + t) ^ 5 * R := by
    calc
      _ = E * J * R := by
        dsimp only [R]
        rw [show a * t * u / 2 - t / 8 = a * t / 2 * u + -(t / 2 / 4) by ring,
          Real.exp_add]
        ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hp5 (by positivity : 0 ≤ E * J * R)]
  have hDB : D ≤ B := by
    have hh : 0 ≤ 2 * u * D + E * J + 1 := by positivity
    dsimp only [B]
    linarith only [hh]
  have hEB : 2 * u * D + E * J ≤ B := by dsimp only [B]; linarith only [hD]
  have hsum := add_le_add (add_le_add hleft hedge) htail
  have hsum' :
      Real.exp (a * t / 2 * c) * (D * (1 + t) ^ 4) * (2 * (t / 2)) +
      Real.exp (a * t / 2 * u) * (D * (1 + t) ^ 4) * Real.exp (-(t / 2 / 2)) * (2 * (u - c)) +
      Real.exp (a * t / 2 * u) * E * Real.exp (-(t / 2 / 4)) * J ≤
        B * (1 + t) ^ 5 * (L + R) := by
    refine hsum.trans ?_
    calc
      _ = (1 + t) ^ 5 * (D * L + (2 * u * D + E * J) * R) := by ring
      _ ≤ (1 + t) ^ 5 * (B * L + B * R) := by gcongr
      _ = _ := by ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  calc
    _ ≤ k * (M * (B * (1 + t) ^ 5 * (L + R))) :=
      mul_le_mul_of_nonneg_left (hbound.trans
        (mul_le_mul_of_nonneg_left hsum' hM)) hk.le
    _ = _ := by
      change k * (M * (B * (1 + t) ^ 5 * (L + R))) =
        (k * A * B) * h ^ d * (1 + t) ^ (d + 5) * (L + R)
      dsimp only [M]
      rw [pow_add]
      ring


/-- The complete arithmetic filter has the actual Vinogradov–Korobov saving,
uniformly in its spacing and without a finite-layer assumption. -/
theorem exists_primeDampingFilter_vinogradovKorobov_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β a : ℝ) (hσ : σ < 1) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      ‖primeDampingFilter (divisorDampingFilter F ρ β h) σ β a h t‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + t) ^ ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card) + 5) *
            Real.exp (a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (2 * t + 1) / 4) := by
  classical
  let ε := min (1 / 16 : ℝ) (1 / (16 * a))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 16 := min_le_left _ _
  have hεa : a * ε / 2 ≤ 1 / 32 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * a)).mp
      (min_le_right (1 / 16) (1 / (16 * a)))
    change ε * (16 * a) ≤ 1 at hh
    nlinarith only [hh]
  obtain ⟨C, hC, hbound⟩ := exists_primeDampingFilter_vk_local_shift_bound
    F ρ σ β a (1 + ε) hσ ha (by linarith only [hε]) (by linarith only [hε1])
  refine ⟨2 * C, by positivity, ?_⟩
  have hwidthlim : Tendsto (fun t : ℝ => vkHadamardWidth (2 * t + 1)) atTop (𝓝 0) :=
    tendsto_vkHadamardWidth_zero.comp
      (tendsto_atTop_add_const_right atTop 1
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have hsmall : ∀ᶠ t : ℝ in atTop, a * vkHadamardWidth (2 * t + 1) / 4 ≤ 1 / 16 := by
    filter_upwards [hwidthlim.eventually (gt_mem_nhds (show 0 < 1 / (4 * a) by positivity))]
      with t ht
    have hh := (lt_div_iff₀ (by positivity : 0 < 4 * a)).mp ht
    nlinarith only [hh]
  filter_upwards [hbound, hsmall, eventually_ge_atTop (2 : ℝ)] with t ht htw ht2
  intro h hh hh1
  have ht0 : 0 ≤ t := by linarith only [ht2]
  have hleft : a * t * (1 - σ - vkHadamardWidth (2 * t + 1) / 2) / 2 =
      a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (2 * t + 1) / 4 := by ring
  have hright : a * t * (1 + ε - σ) / 2 - t / 8 ≤
      a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (2 * t + 1) / 4 := by
    have he := mul_le_mul_of_nonneg_right hεa ht0
    have hw := mul_le_mul_of_nonneg_right htw ht0
    nlinarith only [he, hw, ht0]
  have ht' := ht h hh hh1
  rw [hleft] at ht'
  refine ht'.trans ?_
  calc
    _ ≤ C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
        (1 + t) ^ ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card) + 5) *
          (Real.exp (a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (2 * t + 1) / 4) +
            Real.exp (a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (2 * t + 1) / 4)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (Real.exp_le_exp.mpr hright)) (by positivity)
    _ = _ := by ring

/-- The width saving dominates every polynomial prefactor. -/
theorem tendsto_polynomial_mul_exp_neg_vk_width (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => (1 + t) ^ n *
      Real.exp (-(b * t * vkHadamardWidth (2 * t + 1)))) atTop (𝓝 0) := by
  have hT : Tendsto (fun t : ℝ => 2 * t + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hL := Real.tendsto_log_atTop.comp hT
  have hlim := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hL
  have hsmall : ∀ᶠ t : ℝ in atTop,
      Real.log (2 * t + 1) ^ 4 * Real.exp (-Real.log (2 * t + 1)) <
        b / (3 * 10 ^ 8 * ((n : ℝ) + 1)) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  refine squeeze_zero' ?_ ?_ (Real.tendsto_exp_neg_atTop_nhds_zero.comp hL)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  · filter_upwards [hsmall, eventually_ge_atTop (Real.exp (Real.exp 1)),
      eventually_ge_atTop (2 : ℝ)] with t ht htE ht2
    have ht0 : 0 < 2 * t + 1 := by linarith only [ht2]
    have hTE : Real.exp (Real.exp 1) ≤ 2 * t + 1 := by linarith only [htE, ht2]
    have hlog : 0 < Real.log (2 * t + 1) := Real.log_pos (by linarith only [ht2])
    have hw := vkHadamardWidth_pos hTE
    have hrecip := inv_vkHadamardWidth_le_log_cube hTE
    have hh := ht.le
    rw [Real.exp_neg, Real.exp_log ht0, ← div_eq_mul_inv,
      div_le_div_iff₀ ht0 (by positivity : 0 < 3 * 10 ^ 8 * ((n : ℝ) + 1))] at hh
    have hbudget : 10 ^ 8 * ((n : ℝ) + 1) * Real.log (2 * t + 1) ^ 4 ≤ b * t := by
      nlinarith only [hh, hb, ht2]
    have hq : ((n : ℝ) + 1) * Real.log (2 * t + 1) ≤
        b * t * vkHadamardWidth (2 * t + 1) := by
      apply (div_le_iff₀ hw).mp
      calc
        _ ≤ (((n : ℝ) + 1) * Real.log (2 * t + 1)) *
            (10 ^ 8 * Real.log (2 * t + 1) ^ 3) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left hrecip (by positivity)
        _ = 10 ^ 8 * ((n : ℝ) + 1) * Real.log (2 * t + 1) ^ 4 := by ring
        _ ≤ b * t := hbudget
    calc
      _ ≤ (2 * t + 1) ^ n * Real.exp (-(b * t * vkHadamardWidth (2 * t + 1))) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by linarith only [ht2]) (by linarith only [ht2]) n)
          (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ) * Real.log (2 * t + 1) -
          b * t * vkHadamardWidth (2 * t + 1)) := by
        rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log ht0, Real.exp_neg]
        rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by
        change (n : ℝ) * Real.log (2 * t + 1) - b * t * vkHadamardWidth (2 * t + 1) ≤
          -Real.log (2 * t + 1)
        linarith only [hq])

/-- A width-sized relaxation of critical exponential contraction still forces
the literal prime filter to zero, independently of any exceptional divisor. -/
theorem tendsto_primeDampingFilter_zero_of_vk_relaxed_contraction
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a : ℝ) (hσ : σ < 1) (ha : 0 < a)
    {h : ℝ → ℝ} (hpos : ∀ᶠ t : ℝ in atTop, 0 ≤ h t ∧ h t ≤ 1)
    (hcontract : ∀ᶠ t : ℝ in atTop,
      (h t) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) ≤
        Real.exp (-(a * (1 - σ) * t / 2) + a * t * vkHadamardWidth (2 * t + 1) / 8)) :
    Tendsto (fun t : ℝ =>
      primeDampingFilter (divisorDampingFilter F ρ β (h t)) σ β a (h t) t) atTop (𝓝 0) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  obtain ⟨C, hC, hb⟩ := exists_primeDampingFilter_vinogradovKorobov_bound F ρ σ β a hσ ha
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim := (tendsto_polynomial_mul_exp_neg_vk_width (d + 5)
    (by positivity : 0 < a / 8)).const_mul C
  simp only [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hb, hpos, hcontract, eventually_ge_atTop (0 : ℝ)] with t ht hh hct ht0
  calc
    _ ≤ C * (h t) ^ d * (1 + t) ^ (d + 5) *
        Real.exp (a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (2 * t + 1) / 4) :=
      ht (h t) hh.1 hh.2
    _ ≤ C * Real.exp (-(a * (1 - σ) * t / 2) +
          a * t * vkHadamardWidth (2 * t + 1) / 8) * (1 + t) ^ (d + 5) *
        Real.exp (a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (2 * t + 1) / 4) := by
      gcongr
    _ = C * ((1 + t) ^ (d + 5) *
        (Real.exp (-(a * (1 - σ) * t / 2) + a * t * vkHadamardWidth (2 * t + 1) / 8) *
          Real.exp (a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (2 * t + 1) / 4))) := by
      ring
    _ = C * ((1 + t) ^ (d + 5) *
        Real.exp (-(a / 8 * t * vkHadamardWidth (2 * t + 1)))) := by
      rw [← Real.exp_add]
      congr 3
      ring

/-- Critical exponential spacing enlarged by the proved zero-free saving. -/
def vkRelaxedDampingStep (d : ℕ) (σ a t : ℝ) : ℝ :=
  Real.exp ((-(a * (1 - σ) / 2) + a * vkHadamardWidth (2 * t + 1) / 8) * t / d)

/-- An explicit spacing below the old critical contraction rate still makes
the complete prime filter tend to zero. -/
theorem tendsto_primeDampingFilter_zero_of_vk_schedule
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a : ℝ) (hσ : σ < 1) (ha : 0 < a) :
    let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
    Tendsto (fun t : ℝ => primeDampingFilter
      (divisorDampingFilter F ρ β (vkRelaxedDampingStep d σ a t))
        σ β a (vkRelaxedDampingStep d σ a t) t) atTop (𝓝 0) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  have hd : 0 < (d : ℝ) := by dsimp only [d]; positivity
  apply tendsto_primeDampingFilter_zero_of_vk_relaxed_contraction F ρ σ β a hσ ha
  · have hwidthlim : Tendsto (fun t : ℝ => vkHadamardWidth (2 * t + 1)) atTop (𝓝 0) :=
      tendsto_vkHadamardWidth_zero.comp
        (tendsto_atTop_add_const_right atTop 1
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
    filter_upwards [hwidthlim.eventually
      (gt_mem_nhds (show 0 < 2 * (1 - σ) by linarith only [hσ])),
      eventually_ge_atTop (0 : ℝ)] with t ht ht0
    refine ⟨(Real.exp_pos _).le, ?_⟩
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ hd.le
    apply mul_nonpos_of_nonpos_of_nonneg _ ht0
    nlinarith only [ht, ha, mul_pos ha (sub_pos.mpr hσ)]
  · refine Eventually.of_forall fun t => ?_
    change (vkRelaxedDampingStep d σ a t) ^ d ≤ _
    rw [vkRelaxedDampingStep, ← Real.exp_nat_mul]
    apply le_of_eq
    congr 1
    field_simp [hd.ne']

#print axioms eventually_zeta_vk_local_rectangle
#print axioms exists_primeDampingFilter_vinogradovKorobov_bound
#print axioms tendsto_polynomial_mul_exp_neg_vk_width
#print axioms tendsto_primeDampingFilter_zero_of_vk_relaxed_contraction
#print axioms tendsto_primeDampingFilter_zero_of_vk_schedule

end GaloisForLFunctions.ExceptionalLayerTheory
