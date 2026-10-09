import GaloisForLFunctions.RHTower.RiemannKernelStripHomogeneous
import GaloisForLFunctions.RHTower.XiRealZeroWindowsRH
import GaloisForLFunctions.RHTower.LaguerrePolyaDoubleZeroBridge
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion

/-!
# Second-order Laguerre–Pólya preimages of `Ξ`

Let `a₁, a₂ ≠ 0` and let `ψ` be in the Laguerre–Pólya class with

  `ψ − (1/a₁ + 1/a₂)ψ′ + ψ″/(a₁a₂) = Ξ`,   i.e.  `(1 − D/a₁)(1 − D/a₂)ψ = Ξ`.

Then RH holds, and `ψ` vanishes in every window `[t, t + h]` with `t` large, for every `h > 0`.
On the real line `ψ` equals `ψ₀ = ∫Φ(u)m(u)e^{ixu}du`, `m(u) = 1/((1 − iu/a₁)(1 − iu/a₂))`
(`riemannHypothesis_and_kernelPsi_zeros_of_secondOrder_preimage`).

**Proof.**
* `g = ψ − ψ′/a₂` is Laguerre–Pólya with `Ξ = g − g′/a₁`, so RH holds.
* Under RH every Littlewood window carries three zeros of `Ξ`, counted with multiplicity
  (`riemannHypothesis_XiC_window_zeros_neg`).
* First-order interlacing passes two zeros of `F = f − cf′` (distinct, or one double) to a zero of
  `f`, and three zeros of `F` to two zeros of `f` (`exists_zero_of_twoZeros`, `twoZeros_of_threeZeros`).
  The double-zero case is `eq_zero_and_deriv_eq_zero_of_sub_smul_deriv`.  Applied to `Ξ = g − g′/a₁`
  and then to `g = ψ − ψ′/a₂`, this puts a zero of `ψ` in every window at both ends.
* `ψ` is real on `ℝ`, so the bounded-solution theorem `ofReal_eq_kernelPsi_of_ode` identifies it
  with `ψ₀`.
-/

open Complex Filter Topology Set
open Zeta23
open GaloisForLFunctions.HTGeometry

namespace RHTower.Littlewood

noncomputable section

/-- `F` has two zeros in `[α, β]` counted with multiplicity: two distinct real zeros, or one
real zero with `F′ = 0`. -/
def TwoZeros (F : ℂ → ℂ) (α β : ℝ) : Prop :=
  (∃ γ γ' : ℝ, α ≤ γ ∧ γ < γ' ∧ γ' ≤ β ∧ F γ = 0 ∧ F γ' = 0) ∨
    (∃ γ : ℝ, α ≤ γ ∧ γ ≤ β ∧ F γ = 0 ∧ deriv F γ = 0)

/-- `F` has three zeros in `[α, β]`: three distinct real zeros, or one real zero with `F′ = 0`. -/
def ThreeZeros (F : ℂ → ℂ) (α β : ℝ) : Prop :=
  (∃ γ₁ γ₂ γ₃ : ℝ, α ≤ γ₁ ∧ γ₁ < γ₂ ∧ γ₂ < γ₃ ∧ γ₃ ≤ β ∧ F γ₁ = 0 ∧ F γ₂ = 0 ∧ F γ₃ = 0) ∨
    (∃ γ : ℝ, α ≤ γ ∧ γ ≤ β ∧ F γ = 0 ∧ deriv F γ = 0)

theorem twoZeros_of_threeZeros_self {F : ℂ → ℂ} {α β : ℝ} (h : ThreeZeros F α β) :
    TwoZeros F α β := by
  rcases h with ⟨γ₁, γ₂, γ₃, h1, h12, h23, h3, z1, z2, -⟩ | h
  · exact Or.inl ⟨γ₁, γ₂, h1, h12, by linarith, z1, z2⟩
  · exact Or.inr h

/-- One zero of `F` in `[α, β]` from two. -/
theorem exists_zero_of_twoZeros_self {F : ℂ → ℂ} {α β : ℝ} (h : TwoZeros F α β) :
    ∃ x ∈ Icc α β, F x = 0 := by
  rcases h with ⟨γ, γ', h1, h12, h2, z, -⟩ | ⟨γ, h1, h2, z, -⟩
  · exact ⟨γ, ⟨h1, by linarith⟩, z⟩
  · exact ⟨γ, ⟨h1, h2⟩, z⟩

/-- **Two zeros of `f − cf′` give a zero of `f`.** -/
theorem exists_zero_of_twoZeros {f : ℂ → ℂ} (hf : GaloisForLFunctions.HTGeometry.LaguerrePolya f) {x₀ : ℝ} (hx₀ : f x₀ = 0)
    {c : ℝ} (hc : c ≠ 0) (hnz : ∃ z₀, f z₀ - (c : ℂ) * deriv f z₀ ≠ 0) {α β : ℝ}
    (h : TwoZeros (fun z => f z - (c : ℂ) * deriv f z) α β) : ∃ x ∈ Icc α β, f x = 0 := by
  rcases h with ⟨γ, γ', h1, h12, h2, z, z'⟩ | ⟨γ, h1, h2, z, dz⟩
  · obtain ⟨x, hx, hfx⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hf c hnz h12 z z'
    exact ⟨x, ⟨h1.trans hx.1, hx.2.trans h2⟩, hfx⟩
  · exact ⟨γ, ⟨h1, h2⟩, (eq_zero_and_deriv_eq_zero_of_sub_smul_deriv hf hx₀ hc z dz).1⟩

/-- **Three zeros of `f − cf′` give two zeros of `f`.** -/
theorem twoZeros_of_threeZeros {f : ℂ → ℂ} (hf : GaloisForLFunctions.HTGeometry.LaguerrePolya f) {x₀ : ℝ} (hx₀ : f x₀ = 0)
    {c : ℝ} (hc : c ≠ 0) (hnz : ∃ z₀, f z₀ - (c : ℂ) * deriv f z₀ ≠ 0) {α β : ℝ}
    (h : ThreeZeros (fun z => f z - (c : ℂ) * deriv f z) α β) : TwoZeros f α β := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rcases h with ⟨γ₁, γ₂, γ₃, h1, h12, h23, h3, z1, z2, z3⟩ | ⟨γ, h1, h2, z, dz⟩
  · obtain ⟨x₁, hx₁, f₁⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hf c hnz h12 z1 z2
    obtain ⟨x₂, hx₂, f₂⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hf c hnz h23 z2 z3
    rcases lt_or_eq_of_le (hx₁.2.trans hx₂.1) with hlt | heq
    · exact Or.inl ⟨x₁, x₂, h1.trans hx₁.1, hlt, hx₂.2.trans h3, f₁, f₂⟩
    · -- both zeros sit at `γ₂`
      have hx1 : x₁ = γ₂ := le_antisymm hx₁.2 (heq ▸ hx₂.1)
      rw [hx1] at f₁
      have hd : deriv f γ₂ = 0 := by
        have h' : f γ₂ - (c : ℂ) * deriv f γ₂ = 0 := z2
        rw [f₁, zero_sub, neg_eq_zero] at h'
        exact (mul_eq_zero.mp h').resolve_left hcC
      exact Or.inr ⟨γ₂, by linarith, by linarith, f₁, hd⟩
  · obtain ⟨hf0, hd0⟩ := eq_zero_and_deriv_eq_zero_of_sub_smul_deriv hf hx₀ hc z dz
    exact Or.inr ⟨γ, h1, h2, hf0, hd0⟩

/-- A Laguerre–Pólya function and its derivatives are real on `ℝ`. -/
theorem im_iterate_deriv_eq_zero_of_laguerrePolya {ψ : ℂ → ℂ} (hψ : GaloisForLFunctions.HTGeometry.LaguerrePolya ψ) (j : ℕ)
    (x : ℝ) : (deriv^[j] ψ x).im = 0 := by
  obtain ⟨P, -, hconv⟩ := hψ
  have hder := tendstoLocallyUniformly_iterate_deriv hconv (fun m => differentiable_polyEvalC (P m)) j
  have h := (tendstoLocallyUniformlyOn_univ.mpr hder).tendsto_at (mem_univ (x : ℂ))
  have him := (Complex.continuous_im.tendsto _).comp h
  have h0 : (fun m => (deriv^[j] (polyEvalC (P m)) (x : ℂ)).im) = fun _ => (0 : ℝ) := by
    funext m
    rw [iterate_deriv_polyEvalC, polyEvalC_ofReal, Complex.ofReal_im]
  simp only [Function.comp_def] at him
  rw [h0] at him
  exact (tendsto_nhds_unique tendsto_const_nhds him).symm

theorem ofReal_re_of_im_eq_zero {w : ℂ} (h : w.im = 0) : ((w.re : ℝ) : ℂ) = w :=
  Complex.ext (by simp) (by simp [h])

/-- The paper transform of Riemann's kernel is `Ξ`. -/
theorem paperFT_riemannPhiKernel_eq_XiC (z : ℂ) : paperFT riemannPhiKernel z = XiC z := by
  rw [paperFT_riemannPhiKernel, riemannPhiTransform_eq_xi, XiC, mul_comm]

/-- **Second-order Laguerre–Pólya preimages of `Ξ`.**  If `ψ` is Laguerre–Pólya and
`ψ − (1/a₁ + 1/a₂)ψ′ + ψ″/(a₁a₂) = Ξ` with `a₁, a₂ ≠ 0`, then RH holds and
`ψ₀ = kernelPsi (lorentzPair a₁ a₂)` vanishes in every window `[t, t + h]`, `h > 0`, `t` large. -/
theorem riemannHypothesis_and_kernelPsi_zeros_of_secondOrder_preimage {a₁ a₂ : ℝ}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) {ψ : ℂ → ℂ} (hψ : GaloisForLFunctions.HTGeometry.LaguerrePolya ψ)
    (hode : ∀ z, ψ z - ((1 / a₁ + 1 / a₂ : ℝ) : ℂ) * deriv ψ z +
      deriv (deriv ψ) z / ((a₁ * a₂ : ℝ) : ℂ) = XiC z) :
    RiemannHypothesis ∧ ∀ h : ℝ, 0 < h → ∃ X : ℝ, ∀ t : ℝ, X ≤ t →
      ∃ x ∈ Icc t (t + h), KernelStrip.kernelPsi (KernelStrip.lorentzPair a₁ a₂) x = 0 := by
  have hc₁ : (1 / a₁ : ℝ) ≠ 0 := one_div_ne_zero ha₁
  have hc₂ : (1 / a₂ : ℝ) ≠ 0 := one_div_ne_zero ha₂
  have hψd : Differentiable ℂ ψ := GaloisForLFunctions.HTGeometry.LaguerrePolya.differentiable hψ
  have hψd' : Differentiable ℂ (deriv ψ) := fun z => ((hψd.analyticAt z).deriv).differentiableAt
  -- the first factor
  set g : ℂ → ℂ := fun z => ψ z - ((1 / a₂ : ℝ) : ℂ) * deriv ψ z with hg
  have hgLP : GaloisForLFunctions.HTGeometry.LaguerrePolya g := laguerrePolya_sub_smul_deriv hψ (1 / a₂)
  have hgd : ∀ z, deriv g z = deriv ψ z - ((1 / a₂ : ℝ) : ℂ) * deriv (deriv ψ) z := fun z =>
    ((hψd z).hasDerivAt.sub ((hψd' z).hasDerivAt.const_mul ((1 / a₂ : ℝ) : ℂ))).deriv
  have hXi : ∀ z, XiC z = g z - ((1 / a₁ : ℝ) : ℂ) * deriv g z := by
    intro z
    rw [← hode z, hgd z]
    simp only [hg]
    have h1 : (a₁ : ℂ) ≠ 0 := by exact_mod_cast ha₁
    have h2 : (a₂ : ℂ) ≠ 0 := by exact_mod_cast ha₂
    push_cast
    field_simp
    ring
  have hXifun : XiC = fun z => g z - ((1 / a₁ : ℝ) : ℂ) * deriv g z := funext hXi
  have hRH : RiemannHypothesis := riemannHypothesis_of_XiC_eq_sub_smul_deriv hgLP (1 / a₁) hXi
  refine ⟨hRH, ?_⟩
  -- nonvanishing
  have hXi0 : XiC (-I / 2) ≠ 0 := by
    have e : (1 / 2 : ℂ) + -I / 2 * I = 1 := by ring_nf; rw [Complex.I_sq]; ring
    rw [XiC, e, xi_one]; norm_num
  have hnzXi : ∃ z₀, g z₀ - ((1 / a₁ : ℝ) : ℂ) * deriv g z₀ ≠ 0 :=
    ⟨-I / 2, by rw [← hXi]; exact hXi0⟩
  have hnzg : ∃ z₀, ψ z₀ - ((1 / a₂ : ℝ) : ℂ) * deriv ψ z₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hg0 : g = fun _ => 0 := funext hall
    apply hXi0
    rw [hXi, hg0]
    simp
  -- the windows
  obtain ⟨C, t₀, hC, hwin⟩ := riemannHypothesis_XiC_window_zeros_neg hRH
  set t₁ := max t₀ 1 with ht₁
  have hthree : ∀ t, t₁ ≤ t →
      ThreeZeros (fun z => g z - ((1 / a₁ : ℝ) : ℂ) * deriv g z) t
          (t + C / Real.log (Real.log t)) ∧
        ThreeZeros (fun z => g z - ((1 / a₁ : ℝ) : ℂ) * deriv g z)
          (-t - C / Real.log (Real.log t)) (-t) := by
    intro t ht
    obtain ⟨hp, hn⟩ := hwin t (le_trans (le_max_left _ _) ht)
    rw [← hXifun]
    constructor
    · rcases hp with ⟨γ₁, γ₂, γ₃, h1, h12, h23, h3, z1, z2, z3⟩ | ⟨γ, h1, h2, z, dz⟩
      · exact Or.inl ⟨γ₁, γ₂, γ₃, h1.le, h12, h23, h3, z1, z2, z3⟩
      · exact Or.inr ⟨γ, h1.le, h2, z, dz⟩
    · rcases hn with ⟨γ₁, γ₂, γ₃, h1, h12, h23, h3, z1, z2, z3⟩ | ⟨γ, h1, h2, z, dz⟩
      · exact Or.inl ⟨γ₁, γ₂, γ₃, h1, h12, h23, h3.le, z1, z2, z3⟩
      · exact Or.inr ⟨γ, h1, h2.le, z, dz⟩
  have ht₁1 : (1 : ℝ) ≤ t₁ := le_max_right _ _
  -- a real zero of `g`
  obtain ⟨xg, hxg⟩ : ∃ x : ℝ, g x = 0 := by
    obtain ⟨hp, hn⟩ := hthree t₁ le_rfl
    obtain ⟨γp, hγp, zp⟩ := exists_zero_of_twoZeros_self (twoZeros_of_threeZeros_self hp)
    obtain ⟨γn, hγn, zn⟩ := exists_zero_of_twoZeros_self (twoZeros_of_threeZeros_self hn)
    have hlt : γn < γp := by linarith [hγn.2, hγp.1]
    obtain ⟨x, -, hx⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hgLP (1 / a₁) hnzXi hlt
      zn zp
    exact ⟨x, hx⟩
  -- a zero of `g` in every window
  have hgwin : ∀ t, t₁ ≤ t →
      (∃ x ∈ Icc t (t + C / Real.log (Real.log t)), g x = 0) ∧
        (∃ x ∈ Icc (-t - C / Real.log (Real.log t)) (-t), g x = 0) := by
    intro t ht
    obtain ⟨hp, hn⟩ := hthree t ht
    exact ⟨exists_zero_of_twoZeros hgLP hxg hc₁ hnzXi (twoZeros_of_threeZeros_self hp),
      exists_zero_of_twoZeros hgLP hxg hc₁ hnzXi (twoZeros_of_threeZeros_self hn)⟩
  -- a real zero of `ψ`
  obtain ⟨xψ, hxψ⟩ : ∃ x : ℝ, ψ x = 0 := by
    obtain ⟨⟨xp, hxp, zp⟩, ⟨xn, hxn, zn⟩⟩ := hgwin t₁ le_rfl
    have hlt : xn < xp := by linarith [hxn.2, hxp.1]
    obtain ⟨x, -, hx⟩ := exists_zero_Icc_of_laguerrePolya_sub_smul_deriv hψ (1 / a₂) hnzg hlt
      zn zp
    exact ⟨x, hx⟩
  -- a zero of `ψ` in every window
  have hψwin : ∀ t, t₁ ≤ t →
      (∃ x ∈ Icc t (t + C / Real.log (Real.log t)), ψ x = 0) ∧
        (∃ x ∈ Icc (-t - C / Real.log (Real.log t)) (-t), ψ x = 0) := by
    intro t ht
    obtain ⟨hp, hn⟩ := hthree t ht
    exact ⟨exists_zero_of_twoZeros hψ hxψ hc₂ hnzg (twoZeros_of_threeZeros hgLP hxg hc₁ hnzXi hp),
      exists_zero_of_twoZeros hψ hxψ hc₂ hnzg (twoZeros_of_threeZeros hgLP hxg hc₁ hnzXi hn)⟩
  -- the real restriction of `ψ` and the bounded-solution theorem
  set ψr : ℝ → ℝ := fun x => (ψ x).re with hψr
  set ψ1 : ℝ → ℝ := fun x => (deriv ψ x).re with hψ1
  set ψ2 : ℝ → ℝ := fun x => (deriv (deriv ψ) x).re with hψ2
  have hreal : ∀ (j : ℕ) (x : ℝ), (((deriv^[j] ψ x).re : ℝ) : ℂ) = deriv^[j] ψ x :=
    fun j x => ofReal_re_of_im_eq_zero (im_iterate_deriv_eq_zero_of_laguerrePolya hψ j x)
  have hr0 : ∀ x : ℝ, (ψr x : ℂ) = ψ x := fun x => hreal 0 x
  have hr1 : ∀ x : ℝ, (ψ1 x : ℂ) = deriv ψ x := fun x => hreal 1 x
  have hr2 : ∀ x : ℝ, (ψ2 x : ℂ) = deriv (deriv ψ) x := fun x => hreal 2 x
  have hd0 : ∀ x, HasDerivAt ψr (ψ1 x) x := fun x => (hψd x).hasDerivAt.real_of_complex
  have hd1 : ∀ x, HasDerivAt ψ1 (ψ2 x) x := fun x => (hψd' x).hasDerivAt.real_of_complex
  have hodeR : ∀ x : ℝ, ((ψr x - (1 / a₁ + 1 / a₂) * ψ1 x + ψ2 x / (a₁ * a₂) : ℝ) : ℂ) =
      paperFT riemannPhiKernel x := by
    intro x
    rw [paperFT_riemannPhiKernel_eq_XiC, ← hode x]
    push_cast
    rw [hr0, hr1, hr2]
  have hzp : ∀ T, ∃ x > T, ψr x = 0 := by
    intro T
    obtain ⟨x, hx, hψx⟩ := (hψwin (max (T + 1) t₁) (le_max_right _ _)).1
    refine ⟨x, by linarith [hx.1, le_max_left (T + 1) t₁], ?_⟩
    simp only [hψr, hψx, Complex.zero_re]
  have hzn : ∀ T, ∃ x < -T, ψr x = 0 := by
    intro T
    obtain ⟨x, hx, hψx⟩ := (hψwin (max (T + 1) t₁) (le_max_right _ _)).2
    refine ⟨x, by linarith [hx.2, le_max_left (T + 1) t₁], ?_⟩
    simp only [hψr, hψx, Complex.zero_re]
  have hid := KernelStrip.ofReal_eq_kernelPsi_of_ode ha₁ ha₂ hd0 hd1 hodeR hzp hzn
  -- the windows of length `h`
  intro h hh
  refine ⟨max t₁ (Real.exp (Real.exp (C / h))), fun t ht => ?_⟩
  have ht1 : t₁ ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : Real.exp (Real.exp (C / h)) ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht2
  have hlog1 : Real.exp (C / h) ≤ Real.log t := by
    rw [← Real.log_exp (Real.exp (C / h))]; exact Real.log_le_log (Real.exp_pos _) ht2
  have hlog2 : C / h ≤ Real.log (Real.log t) := by
    rw [← Real.log_exp (C / h)]; exact Real.log_le_log (Real.exp_pos _) hlog1
  have hCh : 0 < C / h := by positivity
  have hwidth : C / Real.log (Real.log t) ≤ h := by
    rw [div_le_iff₀ (by linarith)]
    rw [div_le_iff₀ hh] at hlog2
    linarith
  obtain ⟨x, hx, hψx⟩ := (hψwin t ht1).1
  refine ⟨x, ⟨hx.1, by linarith [hx.2]⟩, ?_⟩
  rw [← hid x, hr0 x, hψx]

end

end RHTower.Littlewood
