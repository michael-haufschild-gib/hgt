import GaloisForLFunctions.RHTower.RiemannKernelStripFirstOrderBounds
import GaloisForLFunctions.RHTower.XiStrongFirstOrderFilterNoGo
import GaloisForLFunctions.RHTower.ZeroGapLargeGapTail

/-!
# First-order Laguerre–Pólya preimages of `Ξ`: identification and zero data

Let `a ≠ 0`, let `f` be Laguerre–Pólya with `f − f′/a = Ξ`, and let `ψ = Re f` on `ℝ`, so
`ψ′ = a(ψ − Ξ)`.

**Identification.**  For `m(z) = 1/(1 − iz/a)` the transform `ψ_m(x) = ∫ Φ(u)m(u)e^{ixu} du` solves
`ψ_m − ψ_m′/a = Ξ`, because `(1 − iu/a)m(u) = 1` (`kernelPsi_lorentzOne_ode`).  Any real solution
of `ψ′ = a(ψ − Ξ)` differs from `ψ_m` by `Ae^{ax}`.  At zeros of `ψ`, `|Ae^{ax}| = |ψ_m| ≤ ∫|Φm|`.
For `a > 0` zeros arbitrarily far to the right force `A = 0`
(`ofReal_eq_kernelPsi_lorentzOne_of_ode`).

**Zero data.**  RH holds (`riemannHypothesis_of_XiC_eq_sub_smul_deriv`).  Under RH a window
`(x − r, x]` carrying two zeros of `ξ` with multiplicity carries two real zeros of `Ξ` or a
double one (`exists_XiC_zeros_of_two_le_N`).  Interlacing then places a zero of `ψ` in
`[x − r, x]`.  Littlewood's windows give such a zero in `[x − 1, x]` for every large `x`
(`riemannHypothesis_and_zero_data_of_firstOrder_preimage`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower.KernelStrip

noncomputable section

/-! ## The first-order multiplier on the real line -/

theorem norm_lorentzOne_ofReal_le (a u : ℝ) : ‖lorentzOne a u‖ ≤ 1 := by
  have h := one_le_norm_one_sub_I_mul_div a u
  rw [lorentzOne, norm_div, norm_one, div_le_one (by linarith)]
  exact h

theorem continuous_lorentzOne_ofReal (a : ℝ) : Continuous fun u : ℝ => lorentzOne a u := by
  unfold lorentzOne
  exact continuous_const.div (by fun_prop) (fun u => one_sub_I_mul_div_ne_zero a u)

theorem lorentzOne_mul (a u : ℝ) : (1 - I * (u : ℂ) / a) * lorentzOne a u = 1 := by
  rw [lorentzOne, mul_one_div, div_self (one_sub_I_mul_div_ne_zero a u)]

/-- The profiles `h = Φm` and `uh` are integrable. -/
theorem lorentzOne_profiles_integrable (a : ℝ) :
    Integrable (fun u : ℝ => riemannPhiKernel u * lorentzOne a u) ∧
      Integrable (fun u : ℝ => (u : ℂ) * (riemannPhiKernel u * lorentzOne a u)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le
  have hc : Continuous fun u : ℝ => riemannPhiKernel u * lorentzOne a u :=
    continuous_riemannPhiKernel.mul (continuous_lorentzOne_ofReal a)
  have hh : ∀ u : ℝ, ‖riemannPhiKernel u * lorentzOne a u‖ ≤ C * Real.exp (-(3 * |u|)) := by
    intro u
    rw [norm_mul]
    calc ‖riemannPhiKernel u‖ * ‖lorentzOne a u‖ ≤ (C * Real.exp (-(3 * |u|))) * 1 :=
          mul_le_mul (hC u) (norm_lorentzOne_ofReal_le a u) (norm_nonneg _) (by positivity)
      _ = C * Real.exp (-(3 * |u|)) := mul_one _
  have hexp : ∀ u : ℝ, Real.exp (-(3 * |u|)) ≤ Real.exp (-(1 * |u|)) := fun u =>
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u])
  refine ⟨integrable_of_norm_le_exp hc (C := C) fun u =>
    (hh u).trans (mul_le_mul_of_nonneg_left (hexp u) hC0), ?_⟩
  refine integrable_of_norm_le_exp (Complex.continuous_ofReal.mul hc) (C := C) fun u => ?_
  have hu := abs_nonneg u
  have h1 : |u| ≤ Real.exp (2 * |u|) := by linarith [Real.add_one_le_exp (2 * |u|)]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |u| * ‖riemannPhiKernel u * lorentzOne a u‖
      ≤ Real.exp (2 * |u|) * (C * Real.exp (-(3 * |u|))) :=
        mul_le_mul h1 (hh u) (norm_nonneg _) (by positivity)
    _ = C * (Real.exp (2 * |u|) * Real.exp (-(3 * |u|))) := by ring
    _ = C * Real.exp (-(1 * |u|)) := by rw [← Real.exp_add]; ring_nf

/-- **`ψ_m` solves the first-order Ξ-equation**: `ψ_m′ = ∫ iuΦm e^{ixu}` and
`ψ_m − ψ_m′/a = Ξ`. -/
theorem kernelPsi_lorentzOne_ode {a : ℝ} (ha : a ≠ 0) :
    (∀ x : ℝ, HasDerivAt (fun x : ℝ => kernelPsi (lorentzOne a) x)
        (paperFT (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzOne a u)) x) x) ∧
      ∀ x : ℝ, kernelPsi (lorentzOne a) x -
          ((1 / a : ℝ) : ℂ) * paperFT (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzOne a u)) x =
        paperFT riemannPhiKernel x := by
  obtain ⟨i0, i1⟩ := lorentzOne_profiles_integrable a
  set h : ℝ → ℂ := fun u => riemannPhiKernel u * lorentzOne a u with hh
  have i2 : Integrable (fun u : ℝ => I * u * h u) := by
    have := i1.const_mul I
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [hh]; ring
  have hk : (fun x : ℝ => kernelPsi (lorentzOne a) x) = fun x : ℝ => paperFT h x := rfl
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [hk]; exact hasDerivAt_paperFT i0 i1 x
  · have e0 : kernelPsi (lorentzOne a) x = paperFT h x := rfl
    set s₁ : ℂ := ((1 / a : ℝ) : ℂ)
    have I0 : Integrable (fun u : ℝ => h u * cexp (I * x * u)) := integrable_mul_cexp_I_mul i0 x
    have I2 : Integrable (fun u : ℝ => s₁ * (I * u * h u * cexp (I * x * u))) :=
      (integrable_mul_cexp_I_mul i2 x).const_mul s₁
    have hsplit : paperFT h x - s₁ * paperFT (fun u : ℝ => I * u * h u) x =
        ∫ u : ℝ, (h u * cexp (I * x * u) - s₁ * (I * u * h u * cexp (I * x * u))) := by
      rw [integral_sub I0 I2, integral_const_mul]
      rfl
    rw [e0, hsplit]
    show _ = ∫ u : ℝ, riemannPhiKernel u * cexp (I * x * u)
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    have hm := lorentzOne_mul a u
    have hc : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have key : h u - s₁ * (I * u * h u) =
        riemannPhiKernel u * ((1 - I * (u : ℂ) / a) * lorentzOne a u) := by
      simp only [hh, s₁]
      push_cast
      field_simp
    rw [hm, mul_one] at key
    simp only
    linear_combination cexp (I * x * u) * key

theorem norm_kernelPsi_lorentzOne_le (a x : ℝ) :
    ‖kernelPsi (lorentzOne a) x‖ ≤ ∫ u : ℝ, ‖riemannPhiKernel u * lorentzOne a u‖ := by
  unfold kernelPsi
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (Eventually.of_forall fun u => ?_)))
  simp only
  rw [norm_mul, show I * (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Identification of first-order solutions.**  Let `a > 0` and let a real `ψ` satisfy
`ψ′ = a(ψ − F)` with `F(x) = ∫ Φ(u)e^{ixu} du`.  If `ψ` has zeros arbitrarily far to the right,
then `ψ(x) = ∫ Φ(u)m(u)e^{ixu} du` with `m(u) = 1/(1 − iu/a)`. -/
theorem ofReal_eq_kernelPsi_lorentzOne_of_ode {a : ℝ} (ha : 0 < a) {ψ F : ℝ → ℝ}
    (hode : ∀ t, HasDerivAt ψ (a * (ψ t - F t)) t)
    (hF : ∀ x, (F x : ℂ) = paperFT riemannPhiKernel x) (hz : ∀ T, ∃ x > T, ψ x = 0) :
    ∀ x, (ψ x : ℂ) = kernelPsi (lorentzOne a) x := by
  obtain ⟨hk1, hk2⟩ := kernelPsi_lorentzOne_ode ha.ne'
  set K := ∫ u : ℝ, ‖riemannPhiKernel u * lorentzOne a u‖
  set k : ℝ → ℂ := fun x => kernelPsi (lorentzOne a) x with hkdef
  set d : ℝ → ℂ := fun x => (ψ x : ℂ) - k x with hd
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  -- `d′ = a d`
  have hdd : ∀ x, HasDerivAt d ((a : ℂ) * d x) x := by
    intro x
    have h3 := hk2 x
    rw [← hF x] at h3
    have e : paperFT (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzOne a u)) x =
        (a : ℂ) * (k x - F x) := by
      calc paperFT (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzOne a u)) x
          = (a : ℂ) * (((1 / a : ℝ) : ℂ) *
              paperFT (fun u : ℝ => I * u * (riemannPhiKernel u * lorentzOne a u)) x) := by
            push_cast; field_simp
        _ = (a : ℂ) * (k x - F x) := by rw [← h3]; ring
    refine ((hode x).ofReal_comp.sub (hk1 x)).congr_deriv ?_
    rw [e]; simp only [hd]; push_cast; ring
  -- `d e^{−ax}` is constant
  have hed : ∀ x : ℝ, HasDerivAt (fun y : ℝ => d y * cexp (-(a : ℂ) * y)) 0 x := by
    intro x
    have hexp : HasDerivAt (fun y : ℝ => cexp (-(a : ℂ) * y))
        (cexp (-(a : ℂ) * x) * (-(a : ℂ))) x := by
      have := ((hasDerivAt_id (x : ℂ)).const_mul (-(a : ℂ))).cexp
      simpa using this.comp_ofReal
    exact ((hdd x).mul hexp).congr_deriv (by ring)
  have hconst : ∀ x : ℝ, d x * cexp (-(a : ℂ) * x) = d 0 := by
    intro x
    have h := is_const_of_deriv_eq_zero (f := fun y : ℝ => d y * cexp (-(a : ℂ) * y))
      (fun y => (hed y).differentiableAt) (fun y => (hed y).deriv) x 0
    simpa using h
  have hdx : ∀ x : ℝ, d x = d 0 * cexp ((a : ℂ) * x) := by
    intro x
    rw [← hconst x, mul_assoc, ← Complex.exp_add]
    simp
  -- the constant vanishes
  have hd0 : d 0 = 0 := by
    by_contra hne
    have hδ : 0 < ‖d 0‖ := norm_pos_iff.mpr hne
    refine KernelStrip.false_of_growth (f := fun x => ‖d x‖) (K := K) ha hδ
      (Eventually.of_forall fun x => ?_) (fun T => ?_)
    · show ‖d 0‖ * Real.exp (a * x) ≤ ‖d x‖
      refine le_of_eq ?_
      rw [hdx x, norm_mul, show (a : ℂ) * (x : ℂ) = ((a * x : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_exp_ofReal]
    · obtain ⟨x, hx, hψx⟩ := hz T
      refine ⟨x, hx, ?_⟩
      show ‖d x‖ ≤ K
      simp only [hd, hψx, Complex.ofReal_zero, zero_sub, norm_neg, hkdef]
      exact norm_kernelPsi_lorentzOne_le a x
  intro x
  have h := hdx x
  rw [hd0, zero_mul] at h
  exact sub_eq_zero.mp h

end

end RHTower.KernelStrip

namespace RHTower.Littlewood

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## Zero data -/

/-- **Two zeros with multiplicity give two real zeros or a double real zero.**  Under RH, if the
window `(a, b]` carries at least two zeros counted with multiplicity, then `Ξ` has two distinct
real zeros in `(a, b]` or a zero `γ ∈ (a, b]` with `Ξ(γ) = Ξ′(γ) = 0`. -/
theorem exists_XiC_zeros_of_two_le_N (hRH : RiemannHypothesis) {a b : ℝ}
    (hN : 2 ≤ zetaZeroConfig.N a b) :
    (∃ γ₁ γ₂ : ℝ, a < γ₁ ∧ γ₁ < γ₂ ∧ γ₂ ≤ b ∧ XiC γ₁ = 0 ∧ XiC γ₂ = 0) ∨
      (∃ γ : ℝ, a < γ ∧ γ ≤ b ∧ XiC γ = 0 ∧ deriv XiC γ = 0) := by
  classical
  have hfin : (zetaZeroConfig.window a b).Finite := zetaZeroConfig.finite_window a b
  set Wf := hfin.toFinset with hWf
  have hmemW : ∀ ρ, ρ ∈ Wf ↔ ρ ∈ zetaZeroConfig.carrier ∧ a < ρ.im ∧ ρ.im ≤ b := by
    intro ρ
    simp only [hWf, Set.Finite.mem_toFinset, ZeroConfig.window, Set.mem_inter_iff,
      Set.mem_setOf_eq]
  set T : Finset ℝ := Wf.image (fun ρ => ρ.im) with hT
  have hinj : Set.InjOn (fun ρ : ℂ => ρ.im) (Wf : Set ℂ) := by
    intro ρ₁ h₁ ρ₂ h₂ himeq
    have e₁ := (XiC_im_eq_zero_of_RH hRH ((hmemW ρ₁).mp h₁).1).1
    have e₂ := (XiC_im_eq_zero_of_RH hRH ((hmemW ρ₂).mp h₂).1).1
    simp only at himeq
    rw [e₁, e₂, himeq]
  have hcard : T.card = Wf.card := Finset.card_image_of_injOn hinj
  have hmemT : ∀ γ ∈ T, a < γ ∧ γ ≤ b ∧ XiC γ = 0 := by
    intro γ hγ
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨hc, h1, h2⟩ := (hmemW ρ).mp hρ
    exact ⟨h1, h2, (XiC_im_eq_zero_of_RH hRH hc).2⟩
  have hNsum : zetaZeroConfig.N a b = ∑ ρ ∈ Wf, zetaZeroConfig.mult ρ := by
    unfold ZeroConfig.N
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  by_cases h2 : 2 ≤ T.card
  · left
    set e := T.orderEmbOfFin rfl
    have i0 : (0 : ℕ) < T.card := by omega
    have i1 : (1 : ℕ) < T.card := by omega
    obtain ⟨ha0, hb0, hz0⟩ := hmemT _ (T.orderEmbOfFin_mem rfl ⟨0, i0⟩)
    obtain ⟨ha1, hb1, hz1⟩ := hmemT _ (T.orderEmbOfFin_mem rfl ⟨1, i1⟩)
    exact ⟨e ⟨0, i0⟩, e ⟨1, i1⟩, ha0, e.strictMono (by simp [Fin.lt_def]), hb1, hz0, hz1⟩
  · right
    by_contra hno
    push Not at hno
    have hle : ∀ ρ ∈ Wf, zetaZeroConfig.mult ρ ≤ 1 := by
      intro ρ hρ
      by_contra h
      push Not at h
      obtain ⟨hc, h1, h2⟩ := (hmemW ρ).mp hρ
      obtain ⟨-, hz⟩ := XiC_im_eq_zero_of_RH hRH hc
      exact hno ρ.im h1 h2 hz (deriv_XiC_im_eq_zero_of_RH hRH hc h)
    have hsum : ∑ ρ ∈ Wf, zetaZeroConfig.mult ρ ≤ Wf.card := by
      calc ∑ ρ ∈ Wf, zetaZeroConfig.mult ρ ≤ ∑ _ρ ∈ Wf, 1 := Finset.sum_le_sum hle
        _ = Wf.card := by simp
    omega

/-- **First-order Laguerre–Pólya preimages: RH and zero data.**  Let `a ≠ 0` and let `f` be
Laguerre–Pólya with `f − f′/a = Ξ`.  Then RH holds, `ψ = Re f` is `f` on `ℝ` and solves
`ψ′ = a(ψ − Ξ)`, and for some `x₀` and all `x ≥ x₀`:
* `ψ` vanishes in `[x − 1, x]`;
* if `N_ξ(x) − N_ξ(x − r) ≥ 2` with `r > 0`, then `ψ` vanishes in `[x − r, x]`. -/
theorem riemannHypothesis_and_zero_data_of_firstOrder_preimage {a : ℝ} (ha : a ≠ 0)
    {f : ℂ → ℂ} (hf : GaloisForLFunctions.HTGeometry.LaguerrePolya f)
    (hode : ∀ z, f z - ((1 / a : ℝ) : ℂ) * deriv f z = XiC z) :
    RiemannHypothesis ∧ (∀ x : ℝ, (((f x).re : ℝ) : ℂ) = f x) ∧
      (∀ t : ℝ, HasDerivAt (fun x : ℝ => (f x).re) (a * ((f t).re - Xi t)) t) ∧
      ∃ x₀ : ℝ, (∀ x ≥ x₀, ∃ q ∈ Icc (x - 1) x, (f q).re = 0) ∧
        ∀ x ≥ x₀, ∀ r > 0, 2 ≤ xiZeroCount x - xiZeroCount (x - r) →
          ∃ q ∈ Icc (x - r) x, (f q).re = 0 := by
  have hc : (1 / a : ℝ) ≠ 0 := one_div_ne_zero ha
  have hXi : ∀ z, XiC z = f z - ((1 / a : ℝ) : ℂ) * deriv f z := fun z => (hode z).symm
  have hXifun : XiC = fun z => f z - ((1 / a : ℝ) : ℂ) * deriv f z := funext hXi
  have hRH : RiemannHypothesis := riemannHypothesis_of_XiC_eq_sub_smul_deriv hf (1 / a) hXi
  have hnz : ∃ z₀, f z₀ - ((1 / a : ℝ) : ℂ) * deriv f z₀ ≠ 0 :=
    ⟨-I / 2, by rw [← hXi]; exact XiC_neg_I_div_two_ne_zero⟩
  obtain ⟨hzp, -⟩ := laguerrePolya_preimage_zeros hf (1 / a) hXi
  obtain ⟨x₁, -, hx₁⟩ := hzp 0
  have hreal : ∀ x : ℝ, (((f x).re : ℝ) : ℂ) = f x := fun x =>
    ofReal_re_of_im_eq_zero (by simpa using im_iterate_deriv_eq_zero_of_laguerrePolya hf 0 x)
  have hzero : ∀ q : ℝ, f q = 0 → (f q).re = 0 := fun q h => by rw [h, Complex.zero_re]
  refine ⟨hRH, hreal, fun t => ?_, ?_⟩
  · -- the ODE
    have hd := ((GaloisForLFunctions.HTGeometry.LaguerrePolya.differentiable hf)
      (t : ℂ)).hasDerivAt.real_of_complex
    convert hd using 1
    have h1 := hode t
    rw [XiC_ofReal] at h1
    have hda : deriv f t = (a : ℂ) * (f t - (Xi t : ℂ)) := by
      have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
      rw [← h1]; push_cast; field_simp; ring
    rw [hda]
    simp
  -- Littlewood windows
  obtain ⟨C, t₀, hC, hwin⟩ := riemannHypothesis_XiC_window_zeros hRH
  set x₀ : ℝ := max (t₀ + 1) (Real.exp (Real.exp C) + 1) with hx₀
  have htwo : ∀ α β : ℝ, TwoZeros (fun z => f z - ((1 / a : ℝ) : ℂ) * deriv f z) α β →
      ∃ q ∈ Icc α β, (f q).re = 0 := by
    intro α β h
    obtain ⟨q, hq, hfq⟩ := exists_zero_of_twoZeros hf hx₁ hc hnz h
    exact ⟨q, hq, hzero q hfq⟩
  have hlong : ∀ x ≥ x₀, ∃ q ∈ Icc (x - 1) x, (f q).re = 0 := by
    intro x hx
    have ht0 : t₀ ≤ x - 1 := by linarith [le_max_left (t₀ + 1) (Real.exp (Real.exp C) + 1)]
    have hte : Real.exp (Real.exp C) ≤ x - 1 := by
      linarith [le_max_right (t₀ + 1) (Real.exp (Real.exp C) + 1)]
    have htpos : 0 < x - 1 := lt_of_lt_of_le (Real.exp_pos _) hte
    have hlog : Real.exp C ≤ Real.log (x - 1) := (Real.le_log_iff_exp_le htpos).mpr hte
    have hlogpos : 0 < Real.log (x - 1) := lt_of_lt_of_le (Real.exp_pos _) hlog
    have hll : C ≤ Real.log (Real.log (x - 1)) := (Real.le_log_iff_exp_le hlogpos).mpr hlog
    have hllpos : 0 < Real.log (Real.log (x - 1)) := lt_of_lt_of_le hC hll
    have hw : C / Real.log (Real.log (x - 1)) ≤ 1 := by rw [div_le_one hllpos]; exact hll
    have hz := hwin (x - 1) ht0
    rw [← hXifun] at htwo
    obtain ⟨q, hq, hfq⟩ := htwo (x - 1) (x - 1 + C / Real.log (Real.log (x - 1))) (by
      rcases hz with ⟨γ₁, γ₂, γ₃, h1, h12, h23, h3, z1, z2, -⟩ | ⟨γ, h1, h2, z, dz⟩
      · exact Or.inl ⟨γ₁, γ₂, h1.le, h12, by linarith, z1, z2⟩
      · exact Or.inr ⟨γ, h1.le, h2, z, dz⟩)
    exact ⟨q, ⟨hq.1, by linarith [hq.2]⟩, hfq⟩
  refine ⟨x₀, hlong, fun x hx r hr hN => ?_⟩
  rcases le_or_gt 1 r with hr1 | hr1
  · obtain ⟨q, hq, hfq⟩ := hlong x hx
    exact ⟨q, ⟨by linarith [hq.1], hq.2⟩, hfq⟩
  · have hx1 : 1 ≤ x := by
      have : 1 ≤ x₀ := by
        have := Real.exp_pos (Real.exp C)
        linarith [le_max_right (t₀ + 1) (Real.exp (Real.exp C) + 1)]
      linarith
    have hxr : 0 ≤ x - r := by linarith
    have hcount := xiZeroCount_sub_eq hxr (by linarith : x - r ≤ x)
    have h2N : 2 ≤ zetaZeroConfig.N (x - r) x := by
      have : (2 : ℤ) ≤ (zetaZeroConfig.N (x - r) x : ℤ) := by rw [← hcount]; exact hN
      exact_mod_cast this
    rw [← hXifun] at htwo
    refine htwo (x - r) x ?_
    rcases exists_XiC_zeros_of_two_le_N hRH h2N with ⟨γ₁, γ₂, h1, h12, h2, z1, z2⟩ |
      ⟨γ, h1, h2, z, dz⟩
    · exact Or.inl ⟨γ₁, γ₂, h1.le, h12, h2, z1, z2⟩
    · exact Or.inr ⟨γ, h1.le, h2, z, dz⟩

end

end RHTower.Littlewood
