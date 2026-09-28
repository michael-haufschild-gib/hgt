import GaloisForLFunctions.RHTower.ThetaSeamCouplingZeros

/-!
# Contacts of the coupled theta renewal family at the physical endpoint

The negative set `{y > 0 : Ξ(2y) < 0}` has infinitely many disjoint bounded components
`(α_j, β_j)`, `α_j → ∞`. With `m_j = min Ξ(2y) < 0` and the contact coupling
`r_j = C/(C - m_j) ∈ (0, 1)`, the affine law `X_r = C(1 - r) + r Ξ(2z)` gives: `X_r > 0` on the
component for `r < r_j`, `X_{r_j} ≥ 0` vanishing to even order `2k ≥ 2` at each minimizer, and two
real zeros for `r_j < r < 1`; moreover `0 < 1 - r_j ≤ C_κ e^{-κ α_j}`, so the positive real zero
count of `X_r` is unbounded as `r ↑ 1`. Just below each contact, Rouché's theorem gives exactly
`2k` zeros near the minimizer; all are nonreal, lie in `|Im z| < 1/4` and converge to the
minimizer. Hence every interval `(r₀, 1)` contains couplings with nonreal zeros in the natural
strip.
-/

open Complex Filter Topology Set Metric HurwitzZeta
open GaloisForLFunctions.HTGeometry (zeroMult)

namespace RHTower

noncomputable section

theorem continuous_Xi_two_mul : Continuous fun y : ℝ => Xi (2 * y) :=
  continuous_Xi'.comp (continuous_const.mul continuous_id)

/-! ## Negative components of the critical Xi signal -/

/-- `(α, β)` is a bounded component of `{y > 0 : Ξ(2y) < 0}`. -/
def IsXiNegativeComponent (α β : ℝ) : Prop :=
  0 < α ∧ α < β ∧ Xi (2 * α) = 0 ∧ Xi (2 * β) = 0 ∧ ∀ y ∈ Ioo α β, Xi (2 * y) < 0

/-- Negative components exist above every height. -/
theorem exists_isXiNegativeComponent (Y : ℝ) :
    ∃ α β : ℝ, Y < α ∧ IsXiNegativeComponent α β := by
  have hf := continuous_Xi_two_mul
  obtain ⟨γ, hγ, hXiγ, -⟩ := exists_simpleCrossing_above 1 (Or.inl rfl) (2 * max Y 0)
  obtain ⟨t, ht, hneg⟩ := exists_Xi_neg_gt γ
  obtain ⟨γ', hγ', hXiγ', -⟩ := exists_simpleCrossing_above 1 (Or.inl rfl) t
  set ζ := γ / 2
  set y₀ := t / 2
  set ζ' := γ' / 2
  have hζ : 2 * ζ = γ := by simp only [ζ]; ring
  have hy₀ : 2 * y₀ = t := by simp only [y₀]; ring
  have hζ' : 2 * ζ' = γ' := by simp only [ζ']; ring
  have hζy : ζ < y₀ := by simp only [ζ, y₀]; linarith
  have hyζ : y₀ < ζ' := by simp only [y₀, ζ']; linarith
  set Z : Set ℝ := {y | Xi (2 * y) = 0}
  have hZ : IsClosed Z := isClosed_eq hf continuous_const
  set S₁ := Icc ζ y₀ ∩ Z
  set S₂ := Icc y₀ ζ' ∩ Z
  have hS₁ : IsCompact S₁ := isCompact_Icc.inter_right hZ
  have hS₂ : IsCompact S₂ := isCompact_Icc.inter_right hZ
  have hζS : ζ ∈ S₁ := ⟨⟨le_rfl, hζy.le⟩, by simp only [Z, mem_setOf_eq, hζ, hXiγ]⟩
  have hζ'S : ζ' ∈ S₂ := ⟨⟨hyζ.le, le_rfl⟩, by simp only [Z, mem_setOf_eq, hζ', hXiγ']⟩
  set α := sSup S₁
  set β := sInf S₂
  have hα : α ∈ S₁ := hS₁.sSup_mem ⟨ζ, hζS⟩
  have hβ : β ∈ S₂ := hS₂.sInf_mem ⟨ζ', hζ'S⟩
  have hle₁ : ∀ y ∈ S₁, y ≤ α := fun y hy => le_csSup hS₁.bddAbove hy
  have hle₂ : ∀ y ∈ S₂, β ≤ y := fun y hy => csInf_le hS₂.bddBelow hy
  have hy₀Z : Xi (2 * y₀) ≠ 0 := by rw [hy₀]; exact hneg.ne
  have hαy : α < y₀ := lt_of_le_of_ne hα.1.2 fun h => hy₀Z (h ▸ hα.2)
  have hyβ : y₀ < β := lt_of_le_of_ne hβ.1.1 fun h => hy₀Z (h ▸ hβ.2)
  have hnz : ∀ y ∈ Ioo α β, Xi (2 * y) ≠ 0 := by
    intro y hy hy0
    rcases le_or_gt y y₀ with h | h
    · have := hle₁ y ⟨⟨hα.1.1.trans hy.1.le, h⟩, hy0⟩; linarith [hy.1]
    · have := hle₂ y ⟨⟨h.le, hy.2.le.trans hβ.1.2⟩, hy0⟩; linarith [hy.2]
  have hmax : max Y 0 < ζ := by simp only [ζ]; linarith
  refine ⟨α, β, by linarith [le_max_left Y 0, hα.1.1], ?_, hαy.trans hyβ, hα.2, hβ.2, ?_⟩
  · linarith [le_max_right Y 0, hα.1.1]
  · intro y hy
    by_contra hc
    push Not at hc
    have hpos : 0 < Xi (2 * y) := lt_of_le_of_ne hc (Ne.symm (hnz y hy))
    obtain ⟨x, hx, hx0⟩ := isPreconnected_Ioo.intermediate_value (⟨hαy, hyβ⟩ : y₀ ∈ Ioo α β) hy
      hf.continuousOn (⟨by rw [hy₀]; exact hneg.le, hpos.le⟩ : (0 : ℝ) ∈ Icc _ _)
    exact hnz x hx hx0

/-- Distinct negative components are disjoint. -/
theorem IsXiNegativeComponent.eq_of_mem {α β α' β' : ℝ} (h : IsXiNegativeComponent α β)
    (h' : IsXiNegativeComponent α' β') {y : ℝ} (hy : y ∈ Ioo α β) (hy' : y ∈ Ioo α' β') :
    α = α' ∧ β = β' := by
  obtain ⟨-, -, hα, hβ, hneg⟩ := h
  obtain ⟨-, -, hα', hβ', hneg'⟩ := h'
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · by_contra hc; push Not at hc
    exact (hneg' α ⟨hc, hy.1.trans hy'.2⟩).ne hα
  · by_contra hc; push Not at hc
    exact (hneg α' ⟨hc, hy'.1.trans hy.2⟩).ne hα'
  · by_contra hc; push Not at hc
    exact (hneg β' ⟨by linarith [hy'.1, hy'.2, hy.1], hc⟩).ne hβ'
  · by_contra hc; push Not at hc
    exact (hneg' β ⟨by linarith [hy.1, hy'.1, hy.2], hc⟩).ne hβ

/-- There are infinitely many negative components. -/
theorem infinite_isXiNegativeComponent :
    {p : ℝ × ℝ | IsXiNegativeComponent p.1 p.2}.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image Prod.fst).bddAbove
  obtain ⟨α, β, hα, h⟩ := exists_isXiNegativeComponent M
  have := hM ⟨(α, β), h, rfl⟩
  simp only at this
  linarith

/-! ## Contact couplings -/

/-- The minimum `m = min_{[α, β]} Ξ(2y)` of a negative component. -/
def xiComponentMin (α β : ℝ) : ℝ := sInf ((fun y => Xi (2 * y)) '' Icc α β)

theorem xiComponentMin_le {α β : ℝ} {y : ℝ} (hy : y ∈ Icc α β) :
    xiComponentMin α β ≤ Xi (2 * y) :=
  csInf_le (isCompact_Icc.image continuous_Xi_two_mul).bddBelow ⟨y, hy, rfl⟩

/-- The minimum is attained at an interior point. -/
theorem IsXiNegativeComponent.exists_minimizer {α β : ℝ} (h : IsXiNegativeComponent α β) :
    ∃ y ∈ Ioo α β, Xi (2 * y) = xiComponentMin α β := by
  obtain ⟨-, hαβ, hα, hβ, hneg⟩ := h
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hαβ.le)
    continuous_Xi_two_mul.continuousOn
  have heq : Xi (2 * y) = xiComponentMin α β :=
    le_antisymm (le_csInf ((nonempty_Icc.mpr hαβ.le).image _) (by
      rintro _ ⟨x, hx, rfl⟩; exact hmin hx)) (xiComponentMin_le hy)
  have hmid : Xi (2 * y) < 0 := by
    have := hmin (show (α + β) / 2 ∈ Icc α β by constructor <;> linarith)
    have h2 := hneg ((α + β) / 2) (by constructor <;> linarith)
    exact lt_of_le_of_lt this h2
  refine ⟨y, ⟨lt_of_le_of_ne hy.1 ?_, lt_of_le_of_ne hy.2 ?_⟩, heq⟩
  · intro he; rw [← he, hα] at hmid; exact lt_irrefl _ hmid
  · intro he; rw [he, hβ] at hmid; exact lt_irrefl _ hmid

theorem IsXiNegativeComponent.xiComponentMin_neg {α β : ℝ} (h : IsXiNegativeComponent α β) :
    xiComponentMin α β < 0 := by
  obtain ⟨y, hy, hm⟩ := h.exists_minimizer
  rw [← hm]; exact h.2.2.2.2 y hy

/-- **(5).** The contact coupling `r_j = C/(C - m_j)`. -/
def contactCoupling (α β : ℝ) : ℝ := thetaSeamConst / (thetaSeamConst - xiComponentMin α β)

theorem IsXiNegativeComponent.contactCoupling_pos {α β : ℝ} (h : IsXiNegativeComponent α β) :
    0 < contactCoupling α β := by
  have := h.xiComponentMin_neg; have := thetaSeamConst_pos
  exact div_pos this (by linarith)

theorem IsXiNegativeComponent.contactCoupling_lt_one {α β : ℝ} (h : IsXiNegativeComponent α β) :
    contactCoupling α β < 1 := by
  have := h.xiComponentMin_neg; have := thetaSeamConst_pos
  rw [contactCoupling, div_lt_one (by linarith)]; linarith

theorem IsXiNegativeComponent.one_sub_contactCoupling {α β : ℝ} (h : IsXiNegativeComponent α β) :
    1 - contactCoupling α β = |xiComponentMin α β| / (thetaSeamConst + |xiComponentMin α β|) := by
  have hm := h.xiComponentMin_neg; have hC := thetaSeamConst_pos
  rw [abs_of_neg hm, contactCoupling, ← sub_eq_add_neg]
  have : thetaSeamConst - xiComponentMin α β ≠ 0 := by linarith
  field_simp
  ring

/-- `C(1 - r_j) + r_j m_j = 0`. -/
theorem IsXiNegativeComponent.contact_identity {α β : ℝ} (h : IsXiNegativeComponent α β) :
    thetaSeamConst * (1 - contactCoupling α β) + contactCoupling α β * xiComponentMin α β = 0 := by
  have hm := h.xiComponentMin_neg; have hC := thetaSeamConst_pos
  have : thetaSeamConst - xiComponentMin α β ≠ 0 := by linarith
  rw [contactCoupling]; field_simp; ring

/-- **(6), below contact.** For `0 ≤ r < r_j`, `X_r > 0` on `[α, β]`. -/
theorem IsXiNegativeComponent.thetaCouplingXi_pos {α β : ℝ} (h : IsXiNegativeComponent α β)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < contactCoupling α β) {y : ℝ} (hy : y ∈ Icc α β) :
    0 < thetaSeamConst * (1 - r) + r * Xi (2 * y) := by
  have hm := h.xiComponentMin_neg; have hC := thetaSeamConst_pos
  have hle := xiComponentMin_le hy
  have hid := h.contact_identity
  have hrj : r * (thetaSeamConst - xiComponentMin α β) <
      contactCoupling α β * (thetaSeamConst - xiComponentMin α β) :=
    mul_lt_mul_of_pos_right hr (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hle hr0]

/-- **(6), at contact.** `X_{r_j} ≥ 0` on `[α, β]`, vanishing at every minimizer. -/
theorem IsXiNegativeComponent.thetaCouplingXi_contact_nonneg {α β : ℝ}
    (h : IsXiNegativeComponent α β) {y : ℝ} (hy : y ∈ Icc α β) :
    0 ≤ thetaSeamConst * (1 - contactCoupling α β) + contactCoupling α β * Xi (2 * y) := by
  have hid := h.contact_identity
  have hle := xiComponentMin_le hy
  nlinarith [mul_le_mul_of_nonneg_left hle h.contactCoupling_pos.le]

theorem IsXiNegativeComponent.thetaCouplingXi_contact_eq_zero {α β : ℝ}
    (h : IsXiNegativeComponent α β) {y : ℝ} (hy : Xi (2 * y) = xiComponentMin α β) :
    thetaCouplingXi (contactCoupling α β) y = 0 := by
  rw [thetaCouplingXi_ofReal, hy, h.contact_identity, Complex.ofReal_zero]

/-- **(6), above contact.** For `r_j < r < 1`, `X_r` has at least two real zeros in `(α, β)`. -/
theorem IsXiNegativeComponent.exists_two_zeros {α β : ℝ} (h : IsXiNegativeComponent α β)
    {r : ℝ} (hr : contactCoupling α β < r) (hr1 : r < 1) :
    ∃ y₁ y₂ : ℝ, α < y₁ ∧ y₁ < y₂ ∧ y₂ < β ∧ thetaCouplingXi r y₁ = 0 ∧
      thetaCouplingXi r y₂ = 0 := by
  have hm := h.xiComponentMin_neg; have hC := thetaSeamConst_pos
  have hid := h.contact_identity
  obtain ⟨y, hy, hmin⟩ := h.exists_minimizer
  set F : ℝ → ℝ := fun x => thetaSeamConst * (1 - r) + r * Xi (2 * x)
  have hF : Continuous F := continuous_const.add (continuous_const.mul continuous_Xi_two_mul)
  have hFy : F y < 0 := by
    simp only [F, hmin]
    have : contactCoupling α β * (thetaSeamConst - xiComponentMin α β) <
        r * (thetaSeamConst - xiComponentMin α β) := mul_lt_mul_of_pos_right hr (by linarith)
    nlinarith
  have hFα : 0 < F α := by simp only [F, h.2.2.1]; nlinarith
  have hFβ : 0 < F β := by simp only [F, h.2.2.2.1]; nlinarith
  obtain ⟨y₁, hy₁, hz₁⟩ := intermediate_value_Ioo' hy.1.le hF.continuousOn
    (⟨hFy, hFα⟩ : (0 : ℝ) ∈ Ioo (F y) (F α))
  obtain ⟨y₂, hy₂, hz₂⟩ := intermediate_value_Ioo hy.2.le hF.continuousOn
    (⟨hFy, hFβ⟩ : (0 : ℝ) ∈ Ioo (F y) (F β))
  refine ⟨y₁, y₂, hy₁.1, hy₁.2.trans hy₂.1, hy₂.2, ?_, ?_⟩
  · rw [thetaCouplingXi_ofReal]; exact_mod_cast hz₁
  · rw [thetaCouplingXi_ofReal]; exact_mod_cast hz₂

/-! ## Even contact and the local Taylor form -/

theorem IsXiNegativeComponent.eventually_mem_Icc {α β y : ℝ} (hy : y ∈ Ioo α β) :
    ∀ᶠ x : ℝ in 𝓝 y, x ∈ Icc α β :=
  Filter.mem_of_superset (Ioo_mem_nhds hy.1 hy.2) Ioo_subset_Icc_self

/-- **(8).** At a minimizer `y*` of a negative component,
`Ξ(2z) - m = (z - y*)^{2k} h(z)` with `k ≥ 1`, `h` entire, `h(y*) > 0`. -/
theorem IsXiNegativeComponent.exists_contact_taylor {α β : ℝ} (h : IsXiNegativeComponent α β)
    {y : ℝ} (hy : y ∈ Ioo α β) (hmin : Xi (2 * y) = xiComponentMin α β) :
    ∃ k : ℕ, 1 ≤ k ∧
      analyticOrderAt (fun z => XiC (2 * z) - xiComponentMin α β) y = ((2 * k : ℕ) : ℕ∞) ∧
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (g y).im = 0 ∧ 0 < (g y).re ∧
        ∀ z, XiC (2 * z) - xiComponentMin α β = (z - y) ^ (2 * k) * g z := by
  have hm := h.xiComponentMin_neg
  have hreal : ∀ x : ℝ, XiC (2 * (x : ℂ)) = ((Xi (2 * x) : ℝ) : ℂ) := fun x => by
    rw [show (2 : ℂ) * x = ((2 * x : ℝ) : ℂ) by push_cast; ring, XiC_ofReal]
  set f : ℂ → ℂ := fun z => XiC (2 * z) - xiComponentMin α β with hf
  have hfd : Differentiable ℂ f :=
    (XiC_differentiable.comp (differentiable_id.const_mul 2)).sub_const _
  refine GaloisForLFunctions.HTGeometry.exists_even_order_factor_of_real_nonneg (f := f)
    hfd (fun x => ?_) ?_ ?_ (z₁ := 0) ?_
  · simp [f, hreal]
  · simp [f, hreal, hmin]
  · filter_upwards [IsXiNegativeComponent.eventually_mem_Icc hy] with x hx
    simp only [f, hreal, sub_re, ofReal_re]
    linarith [xiComponentMin_le hx]
  · simp only [f, mul_zero]
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, XiC_ofReal]
    intro h0
    have := Xi_zero_pos
    have h1 : ((Xi 0 - xiComponentMin α β : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have h2 : Xi 0 - xiComponentMin α β = 0 := by exact_mod_cast h1
    linarith

/-- Every contact zero has even multiplicity `2k ≥ 2`. -/
theorem IsXiNegativeComponent.even_order_contact {α β : ℝ} (h : IsXiNegativeComponent α β)
    {y : ℝ} (hy : y ∈ Ioo α β) (hmin : Xi (2 * y) = xiComponentMin α β) :
    ∃ k : ℕ, 1 ≤ k ∧
      analyticOrderAt (thetaCouplingXi (contactCoupling α β)) y = ((2 * k : ℕ) : ℕ∞) := by
  obtain ⟨k, hk, hord, -⟩ := h.exists_contact_taylor hy hmin
  refine ⟨k, hk, ?_⟩
  have hid := h.contact_identity
  have hr := h.contactCoupling_pos
  have hfun : thetaCouplingXi (contactCoupling α β) =
      fun z => (contactCoupling α β : ℂ) * (XiC (2 * z) - xiComponentMin α β) := by
    funext z
    rw [thetaCouplingXi_eq]
    have hid' : (thetaSeamConst : ℂ) * (1 - contactCoupling α β) =
        -(contactCoupling α β * xiComponentMin α β) := by
      exact_mod_cast (eq_neg_of_add_eq_zero_left hid)
    rw [hid']; ring
  have hc : AnalyticAt ℂ (fun _ : ℂ => (contactCoupling α β : ℂ)) (y : ℂ) := analyticAt_const
  have hg : AnalyticAt ℂ (fun z => XiC (2 * z) - xiComponentMin α β) (y : ℂ) :=
    ((XiC_differentiable.comp (differentiable_id.const_mul 2)).sub_const _).analyticAt _
  rw [hfun, show (fun z => (contactCoupling α β : ℂ) * (XiC (2 * z) - xiComponentMin α β)) =
    (fun _ : ℂ => (contactCoupling α β : ℂ)) * (fun z => XiC (2 * z) - xiComponentMin α β) from rfl,
    analyticOrderAt_mul hc hg, hc.analyticOrderAt_eq_zero.mpr (by exact_mod_cast hr.ne'), zero_add,
    hord]

/-! ## Exponential accumulation of the contacts -/

/-- **(7).** `0 < 1 - r_j = |m_j|/(C + |m_j|) ≤ C_κ e^{-κ α_j}` for every `0 < κ < π/2`. -/
theorem exists_one_sub_contactCoupling_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < Real.pi / 2) :
    ∃ Cκ : ℝ, 0 ≤ Cκ ∧ ∀ α β : ℝ, IsXiNegativeComponent α β →
      |xiComponentMin α β| ≤ Cκ * thetaSeamConst * Real.exp (-(κ * α)) ∧
      0 < 1 - contactCoupling α β ∧ 1 - contactCoupling α β ≤ Cκ * Real.exp (-(κ * α)) := by
  have hC := thetaSeamConst_pos
  obtain ⟨C', hC', hXi⟩ := exists_abs_Xi_le (δ := κ / 2) (by linarith) (by linarith)
  refine ⟨C' / thetaSeamConst, by positivity, fun α β h => ?_⟩
  obtain ⟨y, hy, hmin⟩ := h.exists_minimizer
  have hα := h.1
  have hm := h.xiComponentMin_neg
  have habs : |xiComponentMin α β| ≤ C' * Real.exp (-(κ * α)) := by
    rw [← hmin]
    refine (hXi (2 * y)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC')
    rw [abs_of_pos (by linarith [hy.1])]
    nlinarith [hy.1]
  have hone := h.one_sub_contactCoupling
  refine ⟨by rw [div_mul_cancel₀ _ hC.ne']; exact habs, by linarith [h.contactCoupling_lt_one], ?_⟩
  rw [hone, div_le_iff₀ (by positivity)]
  have h1 : |xiComponentMin α β| ≤ C' / thetaSeamConst * Real.exp (-(κ * α)) * thetaSeamConst := by
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hC.ne']; exact habs
  have h2 : 0 ≤ C' / thetaSeamConst * Real.exp (-(κ * α)) * |xiComponentMin α β| := by positivity
  nlinarith

/-- The contact levels `m_j → 0` and couplings `r_j → 1` along the components. -/
theorem exists_contact_near_one {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ α β : ℝ, IsXiNegativeComponent α β → Y ≤ α →
      |xiComponentMin α β| < ε ∧ 1 - contactCoupling α β < ε := by
  have hC := thetaSeamConst_pos
  obtain ⟨Cκ, hCκ, hb⟩ := exists_one_sub_contactCoupling_le (κ := 1) one_pos
    (by linarith [Real.pi_gt_three])
  have hlim : Tendsto (fun α : ℝ => (Cκ * thetaSeamConst + Cκ) * Real.exp (-(1 * α))) atTop
      (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (Cκ * thetaSeamConst + Cκ)
    simpa using this
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨Y, fun α β h hα => ?_⟩
  obtain ⟨h1, -, h3⟩ := hb α β h
  have hY' := hY α hα
  have hE := Real.exp_pos (-(1 * α))
  constructor <;> nlinarith [mul_nonneg hCκ hC.le]

/-! ## The real zero count diverges as `r ↑ 1` -/

/-- An increasing chain of negative components. -/
theorem exists_isXiNegativeComponent_chain :
    ∃ α β : ℕ → ℝ, (∀ k, IsXiNegativeComponent (α k) (β k)) ∧ ∀ k, β k < α (k + 1) := by
  choose A B hAB using exists_isXiNegativeComponent
  let p : ℕ → ℝ × ℝ := fun k => Nat.rec (A 0, B 0) (fun _ q => (A q.2, B q.2)) k
  refine ⟨fun k => (p k).1, fun k => (p k).2, fun k => ?_, fun k => ?_⟩
  · cases k with
    | zero => exact (hAB 0).2
    | succ k => exact (hAB (p k).2).2
  · exact (hAB (p k).2).1

/-- **Real zero count.** For every `n` there is `r₀ < 1` such that `X_r` has at least `n`
positive real zeros for every `r₀ < r < 1` (while each such count is finite). -/
theorem exists_le_ncard_thetaCouplingXi_real_zeros (n : ℕ) :
    ∃ r₀ < 1, ∀ r ∈ Ioo r₀ 1, n ≤ {y : ℝ | 0 < y ∧ thetaCouplingXi r y = 0}.ncard := by
  obtain ⟨α, β, hc, hchain⟩ := exists_isXiNegativeComponent_chain
  have hmono : StrictMono α := strictMono_nat_of_lt_succ fun k =>
    ((hc k).2.1).trans (hchain k)
  have hsep : ∀ j k, j < k → β j < α k := fun j k hjk =>
    (hchain j).trans_le (hmono.monotone (Nat.succ_le_of_lt hjk))
  have P : ∀ n : ℕ, ∃ r₀ < 1, ∀ r ∈ Ioo r₀ 1, ∀ k < n,
      ∃ y ∈ Ioo (α k) (β k), thetaCouplingXi r y = 0 := by
    intro n
    induction n with
    | zero => exact ⟨0, one_pos, fun _ _ k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ n ih =>
      obtain ⟨r₀, hr₀, hr⟩ := ih
      refine ⟨max r₀ (contactCoupling (α n) (β n)),
        max_lt hr₀ (hc n).contactCoupling_lt_one, fun r hr' k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact hr r ⟨lt_of_le_of_lt (le_max_left _ _) hr'.1, hr'.2⟩ k hk
      · obtain ⟨y₁, y₂, hy₁, h12, hy₂, h₁, -⟩ := (hc k).exists_two_zeros
          (lt_of_le_of_lt (le_max_right _ _) hr'.1) hr'.2
        exact ⟨y₁, ⟨by linarith, by linarith⟩, h₁⟩
  obtain ⟨r₀, hr₀, hr⟩ := P n
  refine ⟨r₀, hr₀, fun r hr' => ?_⟩
  choose y hy hy0 using hr r hr'
  set f : Fin n → ℝ := fun k => y k k.2
  have hinj : Function.Injective f := by
    intro j k hjk
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · have h1 := (hy j j.2).2; have h2 := (hy k k.2).1; have h3 := hsep j k h
      simp only [f] at hjk; linarith
    · have h1 := (hy k k.2).2; have h2 := (hy j j.2).1; have h3 := hsep k j h
      simp only [f] at hjk; linarith
  have hfin : {y : ℝ | 0 < y ∧ thetaCouplingXi r y = 0}.Finite :=
    (finite_thetaCouplingXi_real_zeros hr'.2.ne).subset fun y hy => hy.2
  have hsub : (Finset.univ.image f : Set ℝ) ⊆ {y : ℝ | 0 < y ∧ thetaCouplingXi r y = 0} := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, image_univ, mem_range] at hx
    obtain ⟨k, rfl⟩ := hx
    exact ⟨((hc k).1).trans (hy k k.2).1, hy0 k k.2⟩
  calc n = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    _ = (Finset.univ.image f : Set ℝ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

/-! ## Nonreal clusters just below each contact -/

theorem zeroMult_const_mul {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c : ℂ} (hc : c ≠ 0) (z : ℂ) :
    zeroMult (fun u => c * g u) z = zeroMult g z := by
  have hca : AnalyticAt ℂ (fun _ : ℂ => c) z := analyticAt_const
  rw [zeroMult, zeroMult, show (fun u => c * g u) = (fun _ : ℂ => c) * g from rfl,
    analyticOrderAt_mul hca (hg.analyticAt z), hca.analyticOrderAt_eq_zero.mpr hc, zero_add]

/-- The gap `δ(r) = m - L(r)`, `L(r) = -C(1 - r)/r`, written as `(C - r(C - m))/r`. -/
def contactGap (α β r : ℝ) : ℝ := (thetaSeamConst - r * (thetaSeamConst - xiComponentMin α β)) / r

/-- **(9).** `δ(r) = m - L(r)` with the lower target level `L(r) = -C(1 - r)/r`. -/
theorem contactGap_eq (α β : ℝ) {r : ℝ} (hr : r ≠ 0) :
    contactGap α β r = xiComponentMin α β - (-(thetaSeamConst * (1 - r)) / r) := by
  rw [contactGap]; field_simp; ring

/-- **(9).** `X_r(z) = r [Ξ(2z) - m + δ(r)]`. -/
theorem thetaCouplingXi_eq_contactGap (α β : ℝ) {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    thetaCouplingXi r z = r * ((XiC (2 * z) - xiComponentMin α β) + contactGap α β r) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [thetaCouplingXi_eq, contactGap]
  push_cast
  field_simp
  ring

/-- For `r` in a left neighbourhood of `r_j`, the gap is positive and below any given `δ₁ > 0`. -/
theorem IsXiNegativeComponent.exists_contactGap_lt {α β : ℝ} (h : IsXiNegativeComponent α β)
    {δ₁ : ℝ} (hδ₁ : 0 < δ₁) :
    ∃ ε > 0, ∀ r ∈ Ioo (contactCoupling α β - ε) (contactCoupling α β),
      0 < r ∧ 0 < contactGap α β r ∧ contactGap α β r < δ₁ := by
  have hm := h.xiComponentMin_neg; have hC := thetaSeamConst_pos
  set m := xiComponentMin α β
  have hd : 0 < thetaSeamConst - m := by linarith
  set r₁ := thetaSeamConst / (thetaSeamConst - m + δ₁)
  have hr₁ : 0 < r₁ := by positivity
  have hr₁j : r₁ < contactCoupling α β :=
    div_lt_div_of_pos_left hC hd (by linarith)
  refine ⟨contactCoupling α β - r₁, by linarith, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith [hr.1]
  have hlt : r * (thetaSeamConst - m) < thetaSeamConst := by
    have := hr.2; rw [contactCoupling, lt_div_iff₀ hd] at this; exact this
  have hgt : thetaSeamConst < r * (thetaSeamConst - m + δ₁) := by
    have : r₁ < r := by linarith [hr.1]
    rwa [div_lt_iff₀ (by linarith)] at this
  refine ⟨hr0, div_pos (by linarith) hr0, ?_⟩
  rw [contactGap, div_lt_iff₀ hr0]; linarith

/-- **(9)–(10).** Just below each contact, `X_r` has exactly `2k` zeros (with multiplicity) in a
disc of radius `< a` around a minimizer `y*`; all are nonreal, lie in `|Im z| < a`, and converge
to `y*` as `r ↑ r_j`. -/
theorem IsXiNegativeComponent.exists_nonreal_cluster {α β : ℝ} (h : IsXiNegativeComponent α β)
    {y : ℝ} (hy : y ∈ Ioo α β) (hmin : Xi (2 * y) = xiComponentMin α β) :
    ∃ k : ℕ, 1 ≤ k ∧
      analyticOrderAt (fun z => XiC (2 * z) - xiComponentMin α β) y = ((2 * k : ℕ) : ℕ∞) ∧
      ∃ R ε : ℝ, 0 < R ∧ R < 1 / 4 ∧ 0 < ε ∧
        (∀ r ∈ Ioo (contactCoupling α β - ε) (contactCoupling α β),
          ∃ Z : Finset ℂ, Z.Nonempty ∧
            (∀ z ∈ Z, z ∈ ball (y : ℂ) R ∧ z.im ≠ 0 ∧ |z.im| < 1 / 4) ∧
            (∀ z ∈ ball (y : ℂ) R, thetaCouplingXi r z = 0 ↔ z ∈ Z) ∧
            ∑ z ∈ Z, zeroMult (thetaCouplingXi r) z = 2 * k) ∧
        ∀ ρ > 0, ∃ ε' > 0, ∀ r ∈ Ioo (contactCoupling α β - ε') (contactCoupling α β),
          ∀ z ∈ ball (y : ℂ) R, thetaCouplingXi r z = 0 → dist z y < ρ := by
  obtain ⟨k, hk, hord, -⟩ := h.exists_contact_taylor hy hmin
  set m := xiComponentMin α β with hm_def
  set f : ℂ → ℂ := fun z => XiC (2 * z) - m with hf
  have hfd : Differentiable ℂ f :=
    (XiC_differentiable.comp (differentiable_id.const_mul 2)).sub_const _
  have hρ₀ : 0 < min (1 / 4) (min (y - α) (β - y)) := by
    have := hy.1; have := hy.2
    exact lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  obtain ⟨R, δ₀, hR, hRρ, hδ₀, hcount⟩ := exists_zeroCount_add_const hfd hord hρ₀
  have hR4 : R < 1 / 4 := hRρ.trans_le (min_le_left _ _)
  have hRα : R ≤ y - α := hRρ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRβ : R ≤ β - y := hRρ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the zeros of `X_r` are those of the shifted function
  have hiff : ∀ r, r ≠ 0 → ∀ z, thetaCouplingXi r z = 0 ↔ f z + contactGap α β r = 0 := by
    intro r hr z
    rw [thetaCouplingXi_eq_contactGap α β hr]
    simp only [mul_eq_zero, Complex.ofReal_eq_zero, hr, false_or]
    exact Iff.rfl
  have hmult : ∀ r, r ≠ 0 → ∀ z, zeroMult (thetaCouplingXi r) z =
      zeroMult (fun u => f u + (contactGap α β r : ℂ)) z := by
    intro r hr z
    have : thetaCouplingXi r = fun u => (r : ℂ) * (f u + (contactGap α β r : ℂ)) :=
      funext (thetaCouplingXi_eq_contactGap α β hr)
    rw [this, zeroMult_const_mul (hfd.add_const _) (by exact_mod_cast hr)]
  -- no zero is real
  have hnonreal : ∀ r, 0 < contactGap α β r → ∀ z ∈ ball (y : ℂ) R,
      f z + contactGap α β r = 0 → z.im ≠ 0 := by
    intro r hδ z hz hz0 him
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hd : |z.re - y| < R := by
      have := Complex.abs_re_le_norm (z - y)
      rw [mem_ball, dist_eq_norm] at hz
      simp only [sub_re, ofReal_re] at this
      linarith
    have hx : z.re ∈ Icc α β := by
      rw [abs_lt] at hd; constructor <;> linarith
    rw [hzr] at hz0
    simp only [f] at hz0
    rw [show (2 : ℂ) * (z.re : ℂ) = ((2 * z.re : ℝ) : ℂ) by push_cast; ring, XiC_ofReal] at hz0
    have hle := xiComponentMin_le hx
    have : ((Xi (2 * z.re) - m + contactGap α β r : ℝ) : ℂ) = 0 := by push_cast; exact hz0
    have h0 : Xi (2 * z.re) - m + contactGap α β r = 0 := by exact_mod_cast this
    linarith
  obtain ⟨ε, hε, hgap⟩ := h.exists_contactGap_lt hδ₀
  refine ⟨k, hk, hord, R, ε, hR, hR4, hε, fun r hr => ?_, fun ρ hρ => ?_⟩
  · obtain ⟨hr0, hδ, hδ₀'⟩ := hgap r hr
    have hw : ‖(contactGap α β r : ℂ)‖ < δ₀ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hδ.le]; exact hδ₀'
    obtain ⟨Z, hZball, hZiff, -, hZsum⟩ := hcount _ hw
    refine ⟨Z, ?_, fun z hz => ⟨hZball z hz, ?_, ?_⟩, fun z hz => ?_, ?_⟩
    · rw [Finset.nonempty_iff_ne_empty]
      intro hZ
      rw [hZ, Finset.sum_empty] at hZsum
      omega
    · exact hnonreal r hδ z (hZball z hz) ((hZiff z (hZball z hz)).mpr hz)
    · have h1 := hZball z hz
      rw [mem_ball, dist_eq_norm] at h1
      have := Complex.abs_im_le_norm (z - y)
      simp only [sub_im, ofReal_im, sub_zero] at this
      linarith
    · rw [hiff r hr0.ne', hZiff z hz]
    · rw [← hZsum]
      exact Finset.sum_congr rfl fun z _ => hmult r hr0.ne' z
  · rcases le_or_gt R ρ with hRρ' | hρR
    · exact ⟨ε, hε, fun r _ z hz _ => lt_of_lt_of_le (mem_ball.mp hz) hRρ'⟩
    obtain ⟨R', δ₀', hR', hR'ρ, hδ₀', hcount'⟩ := exists_zeroCount_add_const hfd hord hρ
    obtain ⟨ε', hε', hgap'⟩ := h.exists_contactGap_lt (lt_min hδ₀ hδ₀')
    refine ⟨ε', hε', fun r hr z hz hz0 => ?_⟩
    obtain ⟨hr0, hδ, hδ₁⟩ := hgap' r hr
    have hw : ‖(contactGap α β r : ℂ)‖ < δ₀ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hδ.le]; exact hδ₁.trans_le (min_le_left _ _)
    have hw' : ‖(contactGap α β r : ℂ)‖ < δ₀' := by
      rw [Complex.norm_real, Real.norm_of_nonneg hδ.le]; exact hδ₁.trans_le (min_le_right _ _)
    obtain ⟨Z, hZball, hZiff, hZ1, hZsum⟩ := hcount _ hw
    obtain ⟨Z', hZball', hZiff', -, hZsum'⟩ := hcount' _ hw'
    have hR'R : R' < R := hR'ρ.trans hρR
    have hsub : Z' ⊆ Z := fun u hu => by
      have hu' := hZball' u hu
      exact (hZiff u (ball_subset_ball hR'R.le hu')).mp ((hZiff' u hu').mpr hu)
    have hdiff : Z \ Z' = ∅ := by
      have hsplit := Finset.sum_sdiff hsub (f := zeroMult (fun u => f u + (contactGap α β r : ℂ)))
      rw [hZsum, hZsum'] at hsplit
      have hzero : ∑ u ∈ Z \ Z', zeroMult (fun u => f u + (contactGap α β r : ℂ)) u = 0 := by
        omega
      by_contra hne
      obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h1 := hZ1 u (Finset.mem_sdiff.mp hu).1
      have h2 := Finset.single_le_sum (f := zeroMult (fun u => f u + (contactGap α β r : ℂ)))
        (fun _ _ => Nat.zero_le _) hu
      omega
    have hzZ : z ∈ Z := (hZiff z hz).mp ((hiff r hr0.ne' z).mp hz0)
    have hzZ' : z ∈ Z' := by
      by_contra hn
      have : z ∈ Z \ Z' := Finset.mem_sdiff.mpr ⟨hzZ, hn⟩
      rw [hdiff] at this
      exact Finset.notMem_empty z this
    exact (mem_ball.mp (hZball' z hzZ')).trans hR'ρ

/-- **No left neighbourhood of the physical coupling is off-axis zero-free:** every interval
`(r₀, 1)` contains couplings with nonreal zeros in the natural strip `|Im z| < a`. -/
theorem exists_thetaCouplingXi_nonreal_zero_in_strip {r₀ : ℝ} (hr₀ : r₀ < 1) :
    ∃ r ∈ Ioo r₀ 1, ∃ z : ℂ, thetaCouplingXi r z = 0 ∧ z.im ≠ 0 ∧ |z.im| < 1 / 4 := by
  obtain ⟨Y, hY⟩ := exists_contact_near_one (show 0 < 1 - r₀ by linarith)
  obtain ⟨α, β, hα, h⟩ := exists_isXiNegativeComponent Y
  obtain ⟨-, hrj⟩ := hY α β h hα.le
  obtain ⟨y, hy, hmin⟩ := h.exists_minimizer
  obtain ⟨k, hk, -, R, ε, -, -, hε, hcl, -⟩ := h.exists_nonreal_cluster hy hmin
  set r := (max r₀ (contactCoupling α β - ε) + contactCoupling α β) / 2
  have hmax : max r₀ (contactCoupling α β - ε) < contactCoupling α β :=
    max_lt (by linarith) (by linarith)
  have hr1 : r < contactCoupling α β := by simp only [r]; linarith
  have hr2 : max r₀ (contactCoupling α β - ε) < r := by simp only [r]; linarith
  obtain ⟨Z, ⟨z, hz⟩, hZ, hZiff, -⟩ := hcl r ⟨lt_of_le_of_lt (le_max_right _ _) hr2, hr1⟩
  exact ⟨r, ⟨lt_of_le_of_lt (le_max_left _ _) hr2, hr1.trans h.contactCoupling_lt_one⟩, z,
    (hZiff z (hZ z hz).1).mpr hz, (hZ z hz).2.1, (hZ z hz).2.2⟩

/-- Scaling the seam constant together with the input does not move the zero set. -/
theorem scaledSeam_two_ended_eq_zero_iff {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    (1 / 4 - I * z) * ((r : ℂ) * (evenKernel 0 1 : ℝ) - r * thetaRenewalLaplace (-(I * z))) +
      (1 / 4 + I * z) * ((r : ℂ) * (evenKernel 0 1 : ℝ) - r * thetaRenewalLaplace (I * z)) = 0 ↔
      XiC (2 * z) = 0 := by
  rw [scaledSeam_two_ended, mul_eq_zero]
  simp [hr]

end

end RHTower
