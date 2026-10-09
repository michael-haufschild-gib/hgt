import GaloisForLFunctions.RHTower.LittlewoodShortWindowZeroCount
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.XiHeightAdaptiveHedenmalmCensusCollision
import GaloisForLFunctions.RHTower.SeamStripRamification

/-!
# Real zeros of `Ξ` in short windows under RH

Under RH the nontrivial zeros are `ρ = ½ + iγ` with `Ξ(γ) = 0`.  Zeros on the line are determined
by their ordinates, and the multiplicity of `ρ` is the analytic order of `Ξ` at `γ`.  A window whose
zero count with multiplicity is at least `3` therefore contains three distinct real zeros of `Ξ`, or
one zero of order at least two, i.e. `Ξ(γ) = Ξ′(γ) = 0` (`exists_XiC_zeros_of_three_le_N`).

With Littlewood's short windows (`riemannHypothesis_eventually_xiZeroCount_window_ge`), every window
`(t, t + C/log log t]` with `t` large has this property
(`riemannHypothesis_XiC_window_zeros`).  By evenness of `Ξ`, so does every window
`[−t − C/log log t, −t)` (`riemannHypothesis_XiC_window_zeros_neg`).
-/

open Complex Filter Topology Set
open Zeta23

namespace RHTower.Littlewood

noncomputable section

/-- Under RH every nontrivial zero lies on the critical line. -/
theorem re_eq_half_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    ρ.re = 1 / 2 := by
  rw [zetaZeroConfig_carrier] at hρ
  obtain ⟨hz, hre0, hre1⟩ := hρ
  refine hRH ρ hz ?_ ?_
  · rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re < 0 := by
      simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
        Complex.add_im, Complex.natCast_im, Complex.one_im]
      norm_num
      positivity
    linarith
  · intro h; rw [h] at hre1; simp at hre1

/-- A zero of order at least two is a critical point. -/
theorem deriv_eq_zero_of_two_le_analyticOrderAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (h : (2 : ℕ∞) ≤ analyticOrderAt f z) : deriv f z = 0 := by
  rcases eq_or_ne (analyticOrderAt f z) ⊤ with htop | htop
  · have hev : f =ᶠ[𝓝 z] fun _ => (0 : ℂ) := analyticOrderAt_eq_top.mp htop
    rw [hev.deriv_eq]
    simp
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    obtain ⟨g, hg, -, hev⟩ := hf.analyticOrderAt_eq_natCast.mp hn.symm
    have hn2 : 2 ≤ n := by rw [← hn] at h; exact_mod_cast h
    have hev' : f =ᶠ[𝓝 z] fun w => (w - z) ^ n * g w := hev.mono fun w hw => by
      rw [hw, smul_eq_mul]
    rw [hev'.deriv_eq]
    have hp : HasDerivAt (fun w : ℂ => (w - z) ^ n) ((n : ℂ) * (z - z) ^ (n - 1) * 1) z :=
      ((hasDerivAt_id z).sub_const z).pow n
    have hd : HasDerivAt (fun w : ℂ => (w - z) ^ n * g w)
        ((n : ℂ) * (z - z) ^ (n - 1) * 1 * g z + (z - z) ^ n * deriv g z) z :=
      hp.mul hg.differentiableAt.hasDerivAt
    rw [hd.deriv, sub_self, zero_pow (by omega), zero_pow (by omega)]
    ring

/-- Zeros on the line: for `ρ` a nontrivial zero under RH, `ρ = ½ + i·Im ρ` and `Ξ(Im ρ) = 0`. -/
theorem XiC_im_eq_zero_of_RH (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) :
    ρ = 1 / 2 + (ρ.im : ℂ) * I ∧ XiC (ρ.im : ℂ) = 0 := by
  have hre := re_eq_half_of_RH hRH hρ
  have heq : ρ = 1 / 2 + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  refine ⟨heq, ?_⟩
  have hρ' := hρ
  rw [zetaZeroConfig_carrier] at hρ'
  obtain ⟨hz, hre0, hre1⟩ := hρ'
  rw [XiC, ← heq]
  exact (xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).mpr hz

/-- Multiplicity two on the line gives a critical zero of `Ξ`. -/
theorem deriv_XiC_im_eq_zero_of_RH (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) (hm : 2 ≤ zetaZeroConfig.mult ρ) :
    deriv XiC (ρ.im : ℂ) = 0 := by
  obtain ⟨heq, -⟩ := XiC_im_eq_zero_of_RH hRH hρ
  have hρ' := hρ
  rw [zetaZeroConfig_carrier] at hρ'
  obtain ⟨-, hre0, hre1⟩ := hρ'
  have hmult : zetaZeroConfig.mult ρ = (analyticOrderAt riemannZeta ρ).toNat := rfl
  have hord : (2 : ℕ∞) ≤ analyticOrderAt riemannZeta ρ := by
    rcases eq_or_ne (analyticOrderAt riemannZeta ρ) ⊤ with htop | htop
    · rw [htop]; exact le_top
    · rw [← ENat.coe_toNat htop, ← hmult]
      exact_mod_cast hm
  have hcoord : ((ρ - 1 / 2) * -I) = (ρ.im : ℂ) := by
    conv_lhs => rw [heq]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hX : analyticOrderAt XiC (ρ.im : ℂ) = analyticOrderAt riemannZeta ρ := by
    rw [← hcoord, analyticOrderAt_XiC_centeredCoordinate,
      xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre0, hre1⟩]
  exact deriv_eq_zero_of_two_le_analyticOrderAt (XiC_differentiable.analyticAt _) (hX ▸ hord)

/-- **Three zeros with multiplicity give three real zeros or a double real zero.**  Under RH, if
the window `(a, b]` carries at least three zeros counted with multiplicity, then `Ξ` has three
distinct real zeros in `(a, b]` or a zero `γ ∈ (a, b]` with `Ξ(γ) = Ξ′(γ) = 0`. -/
theorem exists_XiC_zeros_of_three_le_N (hRH : RiemannHypothesis) {a b : ℝ}
    (hN : 3 ≤ zetaZeroConfig.N a b) :
    (∃ γ₁ γ₂ γ₃ : ℝ, a < γ₁ ∧ γ₁ < γ₂ ∧ γ₂ < γ₃ ∧ γ₃ ≤ b ∧
        XiC γ₁ = 0 ∧ XiC γ₂ = 0 ∧ XiC γ₃ = 0) ∨
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
  by_cases h3 : 3 ≤ T.card
  · left
    set e := T.orderEmbOfFin rfl
    have i0 : (0 : ℕ) < T.card := by omega
    have i1 : (1 : ℕ) < T.card := by omega
    have i2 : (2 : ℕ) < T.card := by omega
    obtain ⟨ha0, hb0, hz0⟩ := hmemT _ (T.orderEmbOfFin_mem rfl ⟨0, i0⟩)
    obtain ⟨ha1, hb1, hz1⟩ := hmemT _ (T.orderEmbOfFin_mem rfl ⟨1, i1⟩)
    obtain ⟨ha2, hb2, hz2⟩ := hmemT _ (T.orderEmbOfFin_mem rfl ⟨2, i2⟩)
    refine ⟨e ⟨0, i0⟩, e ⟨1, i1⟩, e ⟨2, i2⟩, ha0, ?_, ?_, hb2, hz0, hz1, hz2⟩
    · exact e.strictMono (by simp [Fin.lt_def])
    · exact e.strictMono (by simp [Fin.lt_def])
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

/-- **Real zeros of `Ξ` in Littlewood windows.**  Under RH there are `C > 0` and `t₀` such that for
every `t ≥ t₀` the window `(t, t + C/log log t]` contains three distinct real zeros of `Ξ` or a
real zero `γ` with `Ξ(γ) = Ξ′(γ) = 0`. -/
theorem riemannHypothesis_XiC_window_zeros (hRH : RiemannHypothesis) :
    ∃ C t₀ : ℝ, 0 < C ∧ ∀ t : ℝ, t₀ ≤ t →
      (∃ γ₁ γ₂ γ₃ : ℝ, t < γ₁ ∧ γ₁ < γ₂ ∧ γ₂ < γ₃ ∧ γ₃ ≤ t + C / Real.log (Real.log t) ∧
          XiC γ₁ = 0 ∧ XiC γ₂ = 0 ∧ XiC γ₃ = 0) ∨
        (∃ γ : ℝ, t < γ ∧ γ ≤ t + C / Real.log (Real.log t) ∧ XiC γ = 0 ∧ deriv XiC γ = 0) := by
  obtain ⟨C, hC, hall⟩ := riemannHypothesis_eventually_xiZeroCount_window_ge hRH
  obtain ⟨t₀, ht₀⟩ := hall 3
  refine ⟨C, max t₀ (Real.exp (Real.exp 1)), hC, fun t ht => ?_⟩
  have ht1 : t₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : Real.exp (Real.exp 1) ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht2
  have hlog : Real.exp 1 ≤ Real.log t := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) ht2
  have hloglog : 0 < Real.log (Real.log t) := by
    apply Real.log_pos
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hle : t ≤ t + C / Real.log (Real.log t) := by
    have : 0 ≤ C / Real.log (Real.log t) := by positivity
    linarith
  have hcount := ht₀ t ht1
  rw [xiZeroCount_sub_eq htpos.le hle] at hcount
  have hN : 3 ≤ zetaZeroConfig.N t (t + C / Real.log (Real.log t)) := by exact_mod_cast hcount
  exact exists_XiC_zeros_of_three_le_N hRH hN

/-- `Ξ′` is odd. -/
theorem deriv_XiC_neg (z : ℂ) : deriv XiC (-z) = -deriv XiC z := by
  have h : (fun w => XiC (-w)) = XiC := funext XiC_even
  have hd : HasDerivAt (fun w => XiC (-w)) (deriv XiC (-z) * (-1)) z :=
    (XiC_differentiable (-z)).hasDerivAt.comp z (hasDerivAt_neg z)
  rw [h] at hd
  have := hd.unique (XiC_differentiable z).hasDerivAt
  linear_combination -this

/-- **The mirror windows.**  Under RH, with the same `C` and `t₀`, every window
`[−t − C/log log t, −t)` contains three distinct real zeros of `Ξ` or a real zero `γ` with
`Ξ(γ) = Ξ′(γ) = 0`. -/
theorem riemannHypothesis_XiC_window_zeros_neg (hRH : RiemannHypothesis) :
    ∃ C t₀ : ℝ, 0 < C ∧ ∀ t : ℝ, t₀ ≤ t →
      ((∃ γ₁ γ₂ γ₃ : ℝ, t < γ₁ ∧ γ₁ < γ₂ ∧ γ₂ < γ₃ ∧ γ₃ ≤ t + C / Real.log (Real.log t) ∧
          XiC γ₁ = 0 ∧ XiC γ₂ = 0 ∧ XiC γ₃ = 0) ∨
        (∃ γ : ℝ, t < γ ∧ γ ≤ t + C / Real.log (Real.log t) ∧ XiC γ = 0 ∧ deriv XiC γ = 0)) ∧
      ((∃ γ₁ γ₂ γ₃ : ℝ, -t - C / Real.log (Real.log t) ≤ γ₁ ∧ γ₁ < γ₂ ∧ γ₂ < γ₃ ∧ γ₃ < -t ∧
          XiC γ₁ = 0 ∧ XiC γ₂ = 0 ∧ XiC γ₃ = 0) ∨
        (∃ γ : ℝ, -t - C / Real.log (Real.log t) ≤ γ ∧ γ < -t ∧ XiC γ = 0 ∧
          deriv XiC γ = 0)) := by
  obtain ⟨C, t₀, hC, h⟩ := riemannHypothesis_XiC_window_zeros hRH
  refine ⟨C, t₀, hC, fun t ht => ⟨h t ht, ?_⟩⟩
  rcases h t ht with ⟨γ₁, γ₂, γ₃, h1, h12, h23, h3, z1, z2, z3⟩ | ⟨γ, h1, h2, z, dz⟩
  · left
    refine ⟨-γ₃, -γ₂, -γ₁, by linarith, by linarith, by linarith, by linarith, ?_, ?_, ?_⟩ <;>
      rw [Complex.ofReal_neg, XiC_even] <;> assumption
  · right
    refine ⟨-γ, by linarith, by linarith, by rw [Complex.ofReal_neg, XiC_even]; exact z, ?_⟩
    rw [Complex.ofReal_neg, deriv_XiC_neg, dz, neg_zero]

end

end RHTower.Littlewood
