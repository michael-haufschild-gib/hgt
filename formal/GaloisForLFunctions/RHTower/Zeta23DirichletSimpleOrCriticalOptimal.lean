import GaloisForLFunctions.RHTower.Zeta23SimpleOrCriticalOptimal
import GaloisForLFunctions.RHTower.Zeta23CriticalOrdinateCensus
import Zeta23.ThmDE.Mult

/-!
# Simple or critical zeros of Dirichlet `L`-functions at the optimal level `2 + √2`

The level-`2 + √2` budget `2c tr Â − ‖Â‖² ≤ (2c − 1)N − (3/2 + √2)M_off` (`sqrtTwo_budget_le`) is a
statement about an abstract zero configuration, and its seam (`seamA_sqrtTwo_offLineMultiple`) only
uses the hat-unit Gram.  Running it through Alpöge–Furman's Theorem D for `L(s, χ)` (`Zeta23.ThmDE`)
gives, for every primitive `χ` mod `q > 1`, unconditionally,

`(3/2 + √2)·M_off(χ; T, 2T) ≤ (1 − HD(1) + ε)·N(χ; T, 2T)`,

so at least `1 − (1 − HD(1))/(3/2 + √2) − ε = 0.8876…` of the zero copies of `L(s, χ)` in `(T, 2T]`
are simple or lie on the critical line (`simple_or_critical_optimal_dirichlet`).  The ordinate
census transfers verbatim: at least `2HD(1)/(1 + HD(1)) − ε` of the zero ordinates of `L(s, χ)` in
`(T, 2T]` carry a critical zero (`critical_ordinates_dirichlet`).
-/

open Filter Asymptotics Topology Real RHLinalg
open scoped BigOperators ComplexOrder

noncomputable section

namespace RHTower

open Zeta23 Zeta23.Assembly Zeta23.ThmD Zeta23.ThmE Zeta23.ThmDE

/-- **Level `2 + √2` through Theorem D for `L(s, χ)`, abstract**:
`(3/2 + √2)M_off ≤ (c⁻¹ − 1 + ε)N`. -/
theorem thmDChi_sqrtTwo_offLineMultiple_abstract (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q)
    (cf : ℕ → ℂ) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (hRvM : RiemannVonMangoldtChi q Z)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsDChi P q aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (lam1q P q T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = GpChi (P.atD T) κ q cf T)
    (hId : ∀ᶠ T in atTop, trGtildeChi (P.atD T) κ q cf T = trG T ∧
      trGtildeSqChi (P.atD T) κ q cf T = trG2 T ∧ (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 + Real.sqrt 2) * (offLineMultipleMass Z T (2 * T) : ℝ)
        ≤ (c⁻¹ - 1 + ε) * (Z.N T (2 * T) : ℝ) := by
  intro ε hε
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set κc := sqrtTwoLevel with hκdef
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (lam1q P q T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (2 * κc * R₁ T + R₂ T + (2 * κc - 1) * (NII Z T : ℝ)
      + B T * (2 * κc + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T
    with herr
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  -- (1) the seam with the off-line multiple mass, eventually in `T`
  have hmain : ∀ᶠ T in atTop,
      (3 / 2 + Real.sqrt 2) * (offLineMultipleMass Z T (2 * T) : ℝ) ≤ (c⁻¹ - 1) * N T + err T := by
    filter_upwards [hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
      with T hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (P.atD T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hA := seamA_sqrtTwo_offLineMultiple hT0 (fun z => GzGp.phiHat_conj _ T z)
      (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqD hP h8) hTl haposD hLpos
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_GpChi, hidtr, hida]; rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_GpChi, hidfr, hida]; rfl
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
    have h := sqrtTwo_lower hB₀ hA htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (cinv T - 1) * N T ≤ (c⁻¹ - 1) * N T + |cinv T - c⁻¹| * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith
  -- (2) `err = o(N)`
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop_chi q Z hq hRvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
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
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM isLittleO_sqrt_mul_l_Tl)
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
  have oB : B =o[atTop] N := by
    refine ((isLittleO_one_iff ℝ).2 o4).trans_isBigO (IsBigO.of_bound 1 ?_)
    filter_upwards [hNtop.eventually_ge_atTop 1] with T h1
    rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (by linarith), one_mul]; exact h1
  -- the level `2κ` exceeds Zeta23's `4` by `2κ − 4`
  have o5' : (fun T => 2 * κc * R₁ T + R₂ T + (2 * κc - 1) * (NII Z T : ℝ)
      + B T * (2 * κc + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) =o[atTop] N := by
    have := o5.add ((((o1.const_mul_left (2 * κc - 4)).add (o3.const_mul_left (2 * κc - 4))).add
      (oB.const_mul_left (2 * κc - 4))))
    exact this.congr_left fun T => by ring
  have herr_o : err =o[atTop] N := o5'.add o6
  -- (3) conclude
  have hfin : ∀ᶠ T in atTop, err T ≤ ε * N T := (herr_o.def hε).mono fun T h => by
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0] at h
    exact (le_abs_self _).trans h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hmain.and hfin)
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hT₀ T hT
  simp only [hNdef] at h1 h2
  nlinarith [h1, h2]

/-- Level `2 + √2` for `L(s, χ)` at fixed `λ ∈ (0,1)`, abstract zero configuration. -/
theorem thmDChi_sqrtTwo_lam_abstract (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q) (cf : ℕ → ℂ)
    (hcu : CoeffUnimodular q cf) (H : PaperInputsChi κ q cf Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 + Real.sqrt 2) * (offLineMultipleMass Z T (2 * T) : ℝ)
        ≤ (1 - HD P.lam + ε) * (Z.N T (2 * T) : ℝ) := by
  have hLoc : ThmD.LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsDChi_concrete (Z := Z) hP hq hcu H hLoc
  have hc := tendsto_cRatio_concreteChi hP hq _ _ _ (tendsto_aD hP) (tendsto_bD hP)
    (tendsto_JD hP)
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataDChi P κ q cf Z).aT T ∧
      (concreteDataDChi P κ q cf Z).aT T ≤ 1 :=
    (concreteFactsDChi hP hq hcu H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD_of_localCount Z hP hA₀ hloc
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpDChi Z hP H.EF
  have hId : ∀ᶠ T in atTop,
      trGtildeChi (P.atD T) κ q cf T = (concreteDataDChi P κ q cf Z).trG T ∧
      trGtildeSqChi (P.atD T) κ q cf T = (concreteDataDChi P κ q cf Z).trG2 T ∧
      (P.atD T).a T = (concreteDataDChi P κ q cf Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtildeChi hP κ q cf T, Params.atD_trGtildeSqChi hP κ q cf T,
        Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmDChi_sqrtTwo_offLineMultiple_abstract Z κ hq cf P hP hlam H.RvM _ _ _ _ _ hTr hc0 hc
    ha θ₀ hTail hθ₀ hNII hGzGp hId hcalE
  have hHD : 1 - HD P.lam = (cStar P.lam)⁻¹ - 1 := by simp only [HD, one_div]; ring
  simpa only [hHD] using h

/-- **Off-line multiple zeros through Theorem D for `L(s, χ)`, abstract**: the `c = 2` endgame of
`Zeta23.ThmDE` applied to the lower count `N₀ˢ − M_off`. -/
theorem thmDChi_mult2_offLineMultiple_abstract (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q)
    (cf : ℕ → ℂ) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (hRvM : RiemannVonMangoldtChi q Z)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsDChi P q aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (lam1q P q T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = GpChi (P.atD T) κ q cf T)
    (hId : ∀ᶠ T in atTop, trGtildeChi (P.atD T) κ q cf T = trG T ∧
      trGtildeSqChi (P.atD T) κ q cf T = trG2 T ∧
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
  set cinv : ℝ → ℝ := fun T => (cRatio (lam1q P q T) (aT T) (bT T) (JT T))⁻¹ with hcinv
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
      rw [rtrace_hat, hGG, rtrace_tilde_GpChi, hidtr, hida]; rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_GpChi, hidfr, hida]; rfl
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
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop_chi q Z hq hRvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
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
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM isLittleO_sqrt_mul_l_Tl)
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

/-- The same at fixed `λ ∈ (0,1)` for an abstract zero configuration with the `χ`-inputs. -/
theorem thmDChi_offLineMultiple_lam_abstract (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q)
    (cf : ℕ → ℂ) (hcu : CoeffUnimodular q cf) (H : PaperInputsChi κ q cf Z) (P : Params)
    (hP : P.Valid) (hlam : P.lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (HD P.lam - ε) * (Z.N T (2 * T) : ℝ)
      ≤ (Z.N0s T (2 * T) : ℝ) - (offLineMultipleMass Z T (2 * T) : ℝ) := by
  have hLoc : ThmD.LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsDChi_concrete (Z := Z) hP hq hcu H hLoc
  have hc := tendsto_cRatio_concreteChi hP hq _ _ _ (tendsto_aD hP) (tendsto_bD hP)
    (tendsto_JD hP)
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataDChi P κ q cf Z).aT T ∧
      (concreteDataDChi P κ q cf Z).aT T ≤ 1 :=
    (concreteFactsDChi hP hq hcu H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD_of_localCount Z hP hA₀ hloc
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpDChi Z hP H.EF
  have hId : ∀ᶠ T in atTop,
      trGtildeChi (P.atD T) κ q cf T = (concreteDataDChi P κ q cf Z).trG T ∧
      trGtildeSqChi (P.atD T) κ q cf T = (concreteDataDChi P κ q cf Z).trG2 T ∧
      (P.atD T).a T = (concreteDataDChi P κ q cf Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtildeChi hP κ q cf T, Params.atD_trGtildeSqChi hP κ q cf T,
        Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmDChi_mult2_offLineMultiple_abstract Z κ hq cf P hP hlam H.RvM _ _ _ _ _ hTr hc0 hc
    ha θ₀ hTail hθ₀ hNII hGzGp hId hcalE
  simpa only [HD, one_div] using h

section DirichletS1

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Off-line multiple zeros of `L(s, χ)` are charged twice**, unconditional: for every primitive `χ`
mod `q > 1`, `(HD(1) − ε)N_χ(T,2T) + M_off(χ; T,2T) ≤ N₀ˢ(χ; T,2T)` for all large `T`. -/
theorem HD_one_add_offLineMultipleMass_le_N0simple_dirichlet (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD 1 - ε) * (NcountL χ T (2 * T) : ℝ)
          + (offLineMultipleMass (LZeros (LSeam_of hq hprim)) T (2 * T) : ℝ)
        ≤ N0simpleL χ T (2 * T) := by
  have h := eps_form_HD (N := fun T => (NcountL χ T (2 * T) : ℝ))
    (lower := fun T => (N0simpleL χ T (2 * T) : ℝ)
      - (offLineMultipleMass (LZeros (LSeam_of hq hprim)) T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) (fun lam hl1 hl2 => by
      have hP := paramsOf_valid taperProfile_stdProfile (show 0 < lam by linarith) hl2.le
      simpa [paramsOf] using thmDChi_offLineMultiple_lam_abstract (LZeros (LSeam_of hq hprim))
        (parity χ) (by omega) (coeff χ) (coeffUnimodular_of_primitive hq hprim)
        (paperInputsChi_L hq hprim) (paramsOf stdProfile lam) hP hl2)
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h ε hε
  exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩

end DirichletS1

section Dirichlet

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- Level `2 + √2` for `L(s, χ)` at fixed `λ ∈ (0,1)`, unconditional. -/
theorem thmE_sqrtTwo_lam (hq : 1 < q) (hprim : χ.IsPrimitive) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 2 + Real.sqrt 2) * (offLineMultipleMass (LZeros (LSeam_of hq hprim)) T (2 * T) : ℝ)
        ≤ (1 - HD lam + ε) * (NcountL χ T (2 * T) : ℝ) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  simpa [paramsOf] using thmDChi_sqrtTwo_lam_abstract (LZeros (LSeam_of hq hprim)) (parity χ)
    (by omega) (coeff χ) (coeffUnimodular_of_primitive hq hprim) (paperInputsChi_L hq hprim)
    (paramsOf stdProfile lam) hP h1

/-- **At least `1 − (1 − HD(1))/(3/2 + √2) − ε = 0.8876…` of the zero copies of `L(s, χ)` in
`(T, 2T]` are simple or lie on the critical line**, for every primitive `χ` mod `q > 1`,
unconditional. -/
theorem simple_or_critical_optimal_dirichlet (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - (1 - HD 1) / (3 / 2 + Real.sqrt 2) - ε) * (NcountL χ T (2 * T) : ℝ)
        ≤ (NcountL χ T (2 * T) : ℝ)
          - (offLineMultipleMass (LZeros (LSeam_of hq hprim)) T (2 * T) : ℝ) := by
  have hM := eps_form_HD (N := fun T => (NcountL χ T (2 * T) : ℝ))
    (lower := fun T => (NcountL χ T (2 * T) : ℝ)
      - (3 / 2 + Real.sqrt 2) * (offLineMultipleMass (LZeros (LSeam_of hq hprim)) T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) (fun lam hl1 hl2 ε hε => by
      obtain ⟨T₀, hT₀⟩ := thmE_sqrtTwo_lam hq hprim (by linarith) hl2 ε hε
      exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩)
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hM ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hK : (1 : ℝ) ≤ 3 / 2 + Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2]
  have hKpos : (0 : ℝ) < 3 / 2 + Real.sqrt 2 := by linarith
  set K := 3 / 2 + Real.sqrt 2
  set M : ℝ := (offLineMultipleMass (LZeros (LSeam_of hq hprim)) T (2 * T) : ℝ)
  set N : ℝ := (NcountL χ T (2 * T) : ℝ)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h1 : M ≤ (1 - HD 1 + ε) * N / K := by rw [le_div_iff₀ hKpos]; linarith
  have h2 : (1 - HD 1 + ε) * N / K = (1 - HD 1) * N / K + ε * N / K := by ring
  have h3 : ε * N / K ≤ ε * N := div_le_self (mul_nonneg hε.le hN) hK
  have e : (1 - HD 1) / K * N = (1 - HD 1) * N / K := by ring
  nlinarith

/-- **Critical ordinates of `L(s, χ)`**: for every primitive `χ` mod `q > 1`, at least
`2HD(1)/(1 + HD(1)) − ε = 0.8042…` of the zero ordinates in `(T, 2T]` carry a critical zero. -/
theorem critical_ordinates_dirichlet (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * HD 1 / (1 + HD 1) - ε)
          * ((zeroOrdinates (LZeros (LSeam_of hq hprim)) T (2 * T)).card : ℝ) ≤
        (criticalOrdinates (LZeros (LSeam_of hq hprim)) T (2 * T)).card := by
  intro ε hε
  set Z := LZeros (LSeam_of hq hprim) with hZ
  obtain ⟨T₀, hT₀⟩ := thmE_D₀_simple_mult hq hprim (ε / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  set H := HD 1 with hHdef
  have hH := HD_one_ge
  have hH1 := HD_one_le_one
  rw [← hHdef] at hH hH1
  have hcensus := two_mul_card_ordinates_le Z T (2 * T)
  have hs := N0s_le_card_criticalOrdinates Z T (2 * T)
  have hsN0 := N0s_le_N0 Z T (2 * T)
  rw [hZ, LZeros_N] at hcensus
  rw [hZ, LZeros_N0s] at hs hsN0
  have hcensus' : 2 * ((zeroOrdinates Z T (2 * T)).card : ℝ) + (Z.N0 T (2 * T) : ℝ)
      ≤ 2 * ((criticalOrdinates Z T (2 * T)).card : ℝ) + (NcountL χ T (2 * T) : ℝ) := by
    exact_mod_cast hcensus
  have hs' : (N0simpleL χ T (2 * T) : ℝ) ≤ (criticalOrdinates Z T (2 * T)).card := by
    exact_mod_cast hs
  have hsN0' : (N0simpleL χ T (2 * T) : ℝ) ≤ Z.N0 T (2 * T) := by exact_mod_cast hsN0
  have hMT := hT₀ T hT
  set o : ℝ := ((zeroOrdinates Z T (2 * T)).card : ℝ)
  set c : ℝ := ((criticalOrdinates Z T (2 * T)).card : ℝ)
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have ho : 0 ≤ o := Nat.cast_nonneg _
  set qq := 2 * H / (1 + H) with hq'
  have hq1 : qq * (1 + H) = 2 * H := by rw [hq']; field_simp
  by_cases hneg : qq - ε ≤ 0
  · nlinarith
  set h : ℝ := H - ε / 2 with hdef
  have hhN : h * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by linarith
  have hqpos : 0 ≤ qq := by rw [hq']; exact div_nonneg (by linarith) (by linarith)
  have hq0 : qq ≤ 2 * H := by nlinarith [hq1, hqpos, hH]
  have hh : 0 < h := by rw [hdef]; nlinarith
  have hh1 : 0 ≤ 1 - h := by rw [hdef]; nlinarith
  have hkey : 2 * h * o ≤ (1 + h) * c := by
    nlinarith [mul_le_mul_of_nonneg_left hcensus' hh.le, mul_le_mul_of_nonneg_left hsN0' hh.le,
      mul_le_mul_of_nonneg_left hs' hh1]
  have hcoef : (qq - ε) * (1 + h) ≤ 2 * h := by rw [hdef]; nlinarith
  have h1h : 0 < 1 + h := by linarith
  have : (qq - ε) * o * (1 + h) ≤ c * (1 + h) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef ho]
  exact le_of_mul_le_mul_right this h1h

end Dirichlet

end RHTower

end
