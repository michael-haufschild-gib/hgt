import GaloisForLFunctions.RHTower.Zeta23OffLineMultipleExclusion
import Zeta23.ThmD.Mult

/-!
# Off-line multiple zeros at the Montgomery–Taylor constant

The excess-retaining seam `RHTower.seamA_mult2_offLineMultiple` holds for every window parameter,
so it runs through Alpöge–Furman's Theorem-D endgame (the Montgomery–Taylor window realizing
`HD(1) = 2 − 1/c₁* = 0.6725…`).  Unconditionally, for `ζ`:

* `(HD(1) − ε)·N(T,2T) + M_off(T,2T) ≤ N₀ˢ(T,2T)`;
* `S_off + 2·M_off ≤ (1 − HD(1) + ε)N`;
* in every large dyadic window either `N₀ ≥ (3/4)N`, or `S_off ≥ (HD(1) − 1/2 − ε)N`
  (`HD(1) − 1/2 = 0.1725…`).

`M_off` counts off-line zeros of multiplicity `≥ 2` with multiplicity, `S_off` simple off-line
zeros and `N₀` critical zeros with multiplicity.
-/

open Filter Asymptotics Topology Real RHLinalg

noncomputable section

namespace RHTower

open Zeta23 Zeta23.ThmD Zeta23.Assembly

/-- **Multiplicity-refined Theorem D, abstract**: the `c = 2` Theorem-D endgame applied to the
lower count `N₀ˢ − M_off`. -/
theorem thmD_mult2_offLineMultiple_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params)
    (hP : P.Valid) (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) - (offLineMultipleMass Z T (2 * T) : ℝ) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  -- (1) the seam with the off-line multiple mass, eventually in `T`
  have hmain : ∀ᶠ T in atTop, (2 - c⁻¹) * N T - err T
      ≤ (Z.N0s T (2 * T) : ℝ) - (offLineMultipleMass Z T (2 * T) : ℝ) := by
    filter_upwards [hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
      with T hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (P.atD T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hA := seamA_mult2_offLineMultiple hT0 (fun z => GzGp.phiHat_conj _ T z)
      (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqD hP h8) hTl haposD hLpos
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
    have haL : (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA
    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]; simp only [hR₂]; linarith
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := N0star_lower_c hB₀ hA htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (2 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith
  -- (2) `err = o(N)`, exactly as in the Theorem-D endgame
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]; exact h.2
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have := hcinvO.mul (isBigO_refl N atTop)
      simpa using this
    have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (this.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr; exact ha2.1
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using this.abs
  have herr_o : err =o[atTop] N := o5.add o6
  exact eps_form_of_isLittleO hmain (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o

/-- Multiplicity-refined Theorem D at fixed `λ ∈ (0,1)`, abstract zero configuration. -/
theorem thmD_offLineMultiple_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params)
    (hP : P.Valid) (hlam : P.lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (HD P.lam - ε) * (Z.N T (2 * T) : ℝ)
      ≤ (Z.N0s T (2 * T) : ℝ) - (offLineMultipleMass Z T (2 * T) : ℝ) := by
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmD_mult2_offLineMultiple_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha θ₀ hTail
    hθ₀ hNII hGzGp hId hcalE
  simpa only [HD, one_div] using h

/-- Multiplicity-refined Theorem D for `ζ` at fixed `λ ∈ (0,1)`, unconditional. -/
theorem thmD_offLineMultiple_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD lam - ε) * (Ncount T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) - (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmD_offLineMultiple_lam_abstract zetaZeroConfig paperInputs_zeta
    (paramsOf stdProfile lam) hP h1

/-- **Off-line multiple zeros at the Montgomery–Taylor constant**, unconditional:
`(HD(1) − ε)·N(T,2T) + M_off(T,2T) ≤ N₀ˢ(T,2T)`. -/
theorem HD_one_add_offLineMultipleMass_le_N0simple :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD 1 - ε) * (Ncount T (2 * T) : ℝ) + (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ)
        ≤ N0simple T (2 * T) := by
  have h := eps_form_HD (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T =>
      (N0simple T (2 * T) : ℝ) - (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) fun lam hl1 hl2 => thmD_offLineMultiple_lam (by linarith) hl2
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h ε hε
  exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩

/-- **Simple off-line zeros plus twice the off-line multiple mass are at most
`(1 − HD(1) + ε)N`.** -/
theorem offLineSimple_add_two_offLineMultiple_le_one_sub_HD_one :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (offLineSimpleCount zetaZeroConfig T (2 * T) : ℝ)
          + 2 * (offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ)
        ≤ (1 - HD 1 + ε) * (Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := HD_one_add_offLineMultipleMass_le_N0simple ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hN := zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple T (2 * T)
  have hs : (N0simple T (2 * T) : ℝ) ≤ N0 T (2 * T) := by exact_mod_cast zeta_N0simple_le_N0 _ _
  linarith

/-- **The simple off-line core of three quarters at the Montgomery–Taylor constant**,
unconditional: in every large dyadic window either at least three quarters of the zero copies of
`ζ` lie on the critical line, or at least `(HD(1) − 1/2 − ε)N` of them are simple off-line zeros
(`HD(1) − 1/2 = 0.1725…`). -/
theorem three_quarters_or_simple_offLine_HD_one :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 4 * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T) ∨
        (HD 1 - 1 / 2 - ε) * (Ncount T (2 * T) : ℝ)
          ≤ offLineSimpleCount zetaZeroConfig T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := offLineSimple_add_two_offLineMultiple_le_one_sub_HD_one ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hN := zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple T (2 * T)
  by_cases h34 : 3 / 4 * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T)
  · exact Or.inl h34
  · right
    push Not at h34
    linarith

/-! ## Cumulative forms over `(0, T]` -/

/-- Off-line multiple mass is additive over adjacent windows. -/
theorem offLineMultipleMass_add (Z : ZeroConfig) {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    offLineMultipleMass Z a d = offLineMultipleMass Z a b + offLineMultipleMass Z b d := by
  classical
  have hunion : zeroWindowFinset Z a d = zeroWindowFinset Z a b ∪ zeroWindowFinset Z b d := by
    ext ρ
    simp only [Finset.mem_union, mem_zeroWindowFinset, Zeta23.Assembly.window_union Z hab hbd,
      Set.mem_union]
  have hdisj : Disjoint (zeroWindowFinset Z a b) (zeroWindowFinset Z b d) := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    exact Set.disjoint_left.mp (Zeta23.Assembly.window_disjoint Z a b d)
      ((mem_zeroWindowFinset Z).mp h1) ((mem_zeroWindowFinset Z).mp h2)
  unfold offLineMultipleMass
  rw [hunion, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hdisj)]

/-- **Cumulative form**: `(HD(1) − ε)·N(T) + M_off(0,T) ≤ N₀ˢ(0,T)` for all large `T`. -/
theorem HD_one_add_offLineMultipleMass_le_N0simple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD 1 - ε) * (Ncount 0 T : ℝ) + (offLineMultipleMass zetaZeroConfig 0 T : ℝ)
        ≤ N0simple 0 T := by
  -- run the dyadic-to-cumulative transfer on the nonnegative additive count `N₀ˢ − M_off + N`
  have hnn : ∀ a b : ℝ,
      0 ≤ (N0simple a b : ℝ) - (offLineMultipleMass zetaZeroConfig a b : ℝ) + (Ncount a b : ℝ) := by
    intro a b
    have hN := zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple a b
    have hS : (0 : ℝ) ≤ offLineSimpleCount zetaZeroConfig a b := Nat.cast_nonneg _
    have hN0 : (0 : ℝ) ≤ N0simple a b := Nat.cast_nonneg _
    have hN0' : (0 : ℝ) ≤ N0 a b := Nat.cast_nonneg _
    linarith
  have h := Zeta23.Assembly.dyadic
    (f := fun a b => (N0simple a b : ℝ) - (offLineMultipleMass zetaZeroConfig a b : ℝ)
      + (Ncount a b : ℝ))
    (g := fun a b => (Ncount a b : ℝ)) (c := HD 1 + 1)
    (fun a b d hab hbd => by
      rw [N0simple_add' zetaSeam hab hbd, offLineMultipleMass_add zetaZeroConfig hab hbd]
      have := Zeta23.Assembly.N_add zetaZeroConfig hab hbd
      rw [zetaZeroConfig_N, zetaZeroConfig_N, zetaZeroConfig_N] at this
      rw [this]
      push_cast
      ring)
    (fun a b d hab hbd => by
      have := Zeta23.Assembly.N_add zetaZeroConfig hab hbd
      rw [zetaZeroConfig_N, zetaZeroConfig_N, zetaZeroConfig_N] at this
      exact_mod_cast this)
    hnn (fun _ _ => Nat.cast_nonneg _) (tendsto_Ncount_zero_atTop zetaSeam paperInputs_zeta.RvM)
    (fun ε hε => by
      obtain ⟨T₀, hT₀⟩ := HD_one_add_offLineMultipleMass_le_N0simple ε hε
      exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩)
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h ε hε
  exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩

/-- **Cumulative form**: at least `(GD(1) − ε)N(T)` zero copies up to height `T` are simple or on the
critical line, `GD(1) = (1 + HD(1))/2 = 0.83625…`. -/
theorem simple_or_critical_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (GD 1 - ε) * (Ncount 0 T : ℝ)
        ≤ (Ncount 0 T : ℝ) - (offLineMultipleMass zetaZeroConfig 0 T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := HD_one_add_offLineMultipleMass_le_N0simple_cumulative (2 * ε) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hN := zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple 0 T
  have hs : (N0simple 0 T : ℝ) ≤ N0 0 T := by exact_mod_cast zeta_N0simple_le_N0 _ _
  have hS : (0 : ℝ) ≤ offLineSimpleCount zetaZeroConfig 0 T := Nat.cast_nonneg _
  rw [GD_eq]
  linarith

end RHTower

end
