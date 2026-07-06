/-
A growing count of forced band-edge events on a lateral edge, from a pointwise incidence
phase-rate floor.

The incidence carrier `ι = −Λ₂/Λ₁` of a pencil anchored at a nonvanishing `Λ₁` has
logarithmic derivative `logDeriv Λ₂ − logDeriv Λ₁`.  Along a vertical edge its phase advances
at the rate `Re(logDeriv Λ₂ − logDeriv Λ₁)`.  When this rate is bounded below by a positive
constant `ρ₀`, the phase is strictly increasing, and every time it crosses an integer multiple
of `π` the imaginary part of `ι` vanishes — a point where a real-ratio pencil member vanishes,
a transversal band-edge event.  On an edge of length `ℓ` the phase advances by at least
`ℓ·ρ₀`, so the number of forced events is at least `ℓ·ρ₀/π`: the events are *supplied* by the
rate floor, not hypothesized, and their count grows with the edge length and — once `ρ₀` is the
archimedean winding floor net of a bounded Dirichlet budget — with the height.
-/
import GaloisForLFunctions.RHTower.LateralWindingFloor
import GaloisForLFunctions.RHTower.EulerTailWinding

open Complex MeasureTheory

namespace RHTower

/-! ### The monotone-phase multi-crossing engine -/

/-- **Strictly ordered crossings from a phase-rate floor.**  A carrier presented in polar
form along an edge, whose phase obeys a uniform positive lower rate `ρ₀` (the phase advances by
at least `ρ₀·(y−x)` across any subinterval), crosses the imaginary axis of the phase at every
multiple of `π` it passes; on an edge long enough to advance by `n·π` there are `n` strictly
ordered points where the imaginary part vanishes. -/
theorem exists_strictMono_events_of_rate_floor {F : ℝ → ℂ} {r θ : ℝ → ℝ} {a b ρ₀ : ℝ} {n : ℕ}
    (hab : a ≤ b) (hρ : 0 < ρ₀)
    (hpolar : ∀ τ ∈ Set.Icc a b, F τ = (r τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hθc : ContinuousOn θ (Set.Icc a b))
    (hfloor : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → ρ₀ * (y - x) ≤ θ y - θ x)
    (hn : (n : ℝ) * Real.pi ≤ (b - a) * ρ₀) :
    ∃ e : Fin n → ℝ, StrictMono e ∧ ∀ i, e i ∈ Set.Icc a b ∧ (F (e i)).im = 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hmono : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x < y → θ x < θ y := by
    intro x hx y hy hxy
    have := hfloor x hx y hy hxy.le
    nlinarith [this, hρ, sub_pos.mpr hxy]
  have haa : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hbb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
  have hspan : (b - a) * ρ₀ ≤ θ b - θ a := by
    have := hfloor a haa b hbb hab; nlinarith [this]
  set k₀ : ℤ := ⌈θ a / Real.pi⌉ with hk0
  set lvl : Fin n → ℝ := fun i => ((k₀ + i) : ℝ) * Real.pi with hlvl
  have hk0lo : θ a ≤ (k₀ : ℝ) * Real.pi := by
    rw [hk0]
    calc θ a = (θ a / Real.pi) * Real.pi := by field_simp
      _ ≤ (⌈θ a / Real.pi⌉ : ℝ) * Real.pi :=
          mul_le_mul_of_nonneg_right (Int.le_ceil _) hπ.le
  have hk0hi : (k₀ : ℝ) * Real.pi < θ a + Real.pi := by
    rw [hk0]
    have h := Int.ceil_lt_add_one (θ a / Real.pi)
    calc (⌈θ a / Real.pi⌉ : ℝ) * Real.pi < (θ a / Real.pi + 1) * Real.pi :=
          mul_lt_mul_of_pos_right h hπ
      _ = θ a + Real.pi := by field_simp
  have hlvl_mem : ∀ i : Fin n, θ a ≤ lvl i ∧ lvl i ≤ θ b := by
    intro i
    have hik : (0 : ℝ) ≤ (i : ℝ) := by positivity
    have hin : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    constructor
    · rw [hlvl]; push_cast
      have : (k₀ : ℝ) * Real.pi ≤ ((k₀ : ℝ) + i) * Real.pi :=
        mul_le_mul_of_nonneg_right (by linarith) hπ.le
      linarith [hk0lo]
    · rw [hlvl]; push_cast
      have hlt : ((k₀ : ℝ) + i) * Real.pi < θ a + Real.pi + (i : ℝ) * Real.pi := by
        have : ((k₀ : ℝ) + i) * Real.pi = (k₀ : ℝ) * Real.pi + (i : ℝ) * Real.pi := by ring
        rw [this]; linarith [hk0hi]
      have hi1 : θ a + Real.pi + (i : ℝ) * Real.pi ≤ θ a + (n : ℝ) * Real.pi := by
        have hprod : 0 ≤ ((n : ℝ) - ((i : ℝ) + 1)) * Real.pi :=
          mul_nonneg (by linarith [hin]) hπ.le
        nlinarith [hprod]
      have : θ a + (n : ℝ) * Real.pi ≤ θ b := by nlinarith [hspan, hn]
      linarith
  have hpre : ∀ i : Fin n, ∃ τ ∈ Set.Icc a b, θ τ = lvl i := by
    intro i
    obtain ⟨τ, hτ, hθτ⟩ :=
      intermediate_value_Icc hab hθc ⟨(hlvl_mem i).1, (hlvl_mem i).2⟩
    exact ⟨τ, hτ, hθτ⟩
  choose e he hθe using hpre
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    have hlvlij : lvl i < lvl j := by
      rw [hlvl]; apply mul_lt_mul_of_pos_right _ hπ
      have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
      linarith
    have hθij : θ (e i) < θ (e j) := by rw [hθe i, hθe j]; exact hlvlij
    rcases lt_trichotomy (e i) (e j) with h | h | h
    · exact h
    · rw [h] at hθij; exact absurd rfl (ne_of_lt hθij)
    · exact absurd (hmono (e j) (he j) (e i) (he i) h) (not_lt.mpr hθij.le)
  · intro i
    refine ⟨he i, ?_⟩
    have him : (F (e i)).im = r (e i) * Real.sin (θ (e i)) := by
      rw [hpolar (e i) (he i), Complex.mul_im]
      simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [him, hθe i]
    simp only [hlvl]
    rw [show ((k₀ : ℝ) + (i : ℝ)) * Real.pi = ((k₀ + i : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi, mul_zero]

/-! ### The rate floor from a phase-advance identity -/

/-- **A pointwise rate floor lifts to the difference rate floor.**  If the phase is the
primitive of a continuous rate `g` from the left endpoint, and `g` is bounded below by `ρ₀`,
then the phase advances by at least `ρ₀·(y−x)` across every subinterval. -/
theorem rate_floor_of_phase_advance {θ g : ℝ → ℝ} {a b ρ₀ : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (hadv : ∀ τ ∈ Set.Icc a b, θ τ - θ a = ∫ t in a..τ, g t)
    (hgfloor : ∀ τ ∈ Set.Icc a b, ρ₀ ≤ g τ) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → ρ₀ * (y - x) ≤ θ y - θ x := by
  intro x hx y hy hxy
  have hgint : IntervalIntegrable g volume x y :=
    (hg.mono (Set.uIcc_subset_Icc hx hy)).intervalIntegrable
  have hsub : (∫ t in a..y, g t) - (∫ t in a..x, g t) = ∫ t in x..y, g t := by
    have hax : IntervalIntegrable g volume a x :=
      (hg.mono (Set.uIcc_subset_Icc ⟨le_refl a, hx.1.trans hx.2⟩ hx)).intervalIntegrable
    have := intervalIntegral.integral_add_adjacent_intervals hax hgint
    linarith [this]
  have hθdiff : θ y - θ x = ∫ t in x..y, g t := by
    have h1 := hadv y hy
    have h2 := hadv x hx
    rw [← hsub]; linarith
  have hmono : (∫ t in x..y, (ρ₀ : ℝ)) ≤ ∫ t in x..y, g t :=
    intervalIntegral.integral_mono_on hxy intervalIntegrable_const hgint
      (fun t ht => hgfloor t ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  rw [hθdiff]
  linarith [hmono]

/-! ### The incidence carrier along the edge -/

/-- The logarithmic derivative of the incidence carrier is `logDeriv Λ₂ − logDeriv Λ₁`. -/
theorem logDeriv_incidence {Λ₁ Λ₂ : ℂ → ℂ} {z : ℂ}
    (h1 : Λ₁ z ≠ 0) (h2 : Λ₂ z ≠ 0)
    (hd1 : DifferentiableAt ℂ Λ₁ z) (hd2 : DifferentiableAt ℂ Λ₂ z) :
    logDeriv (incidence Λ₁ Λ₂) z = logDeriv Λ₂ z - logDeriv Λ₁ z := by
  calc logDeriv (incidence Λ₁ Λ₂) z
      = logDeriv (fun w => -Λ₂ w) z - logDeriv Λ₁ z := by
        unfold incidence; exact logDeriv_div z (by simpa using h2) h1 hd2.neg hd1
    _ = logDeriv Λ₂ z - logDeriv Λ₁ z := by
        congr 1
        rw [show (fun w => -Λ₂ w) = fun w => (-1 : ℂ) * Λ₂ w from by funext w; ring,
          logDeriv_const_mul z (-1) (by norm_num)]

/-- **The forced-event count on a lateral edge.**  Suppose the anchor `Λ₁` and target `Λ₂` are
analytic and nonvanishing on an open set covering a vertical edge, and the incidence phase rate
`Re(logDeriv Λ₂ − logDeriv Λ₁)` is bounded below by `ρ₀ > 0` along the edge.  Then on an edge
long enough to advance the phase by `n·π` there are `n` strictly ordered points where a
real-ratio pencil member vanishes: `n` transversal band-edge events, supplied by the rate
floor. -/
theorem exists_edge_events_of_incidence_rate_floor {Λ₁ Λ₂ : ℂ → ℂ} {U : Set ℂ}
    {σ a b ρ₀ : ℝ} {n : ℕ}
    (hab : a ≤ b) (hρ : 0 < ρ₀) (hU : IsOpen U)
    (hmapU : ∀ τ ∈ Set.Icc a b, stripPt σ τ ∈ U)
    (hΛ1 : AnalyticOnNhd ℂ Λ₁ U) (hΛ1ne : ∀ z ∈ U, Λ₁ z ≠ 0)
    (hΛ2 : AnalyticOnNhd ℂ Λ₂ U) (hΛ2ne : ∀ z ∈ U, Λ₂ z ≠ 0)
    (hfloor : ∀ τ ∈ Set.Icc a b,
      ρ₀ ≤ (logDeriv Λ₂ (stripPt σ τ) - logDeriv Λ₁ (stripPt σ τ)).re)
    (hn : (n : ℝ) * Real.pi ≤ (b - a) * ρ₀) :
    ∃ e : Fin n → ℝ, StrictMono e ∧ ∀ i, e i ∈ Set.Icc a b ∧
      pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ (stripPt σ (e i))).re : ℂ) 1 (stripPt σ (e i)) = 0 := by
  -- the incidence carrier is analytic and nonvanishing on `U`
  have hιan : AnalyticOnNhd ℂ (incidence Λ₁ Λ₂) U := by
    have : incidence Λ₁ Λ₂ = fun s => (-Λ₂ s) / Λ₁ s := by funext s; rw [incidence]
    rw [this]
    exact hΛ2.neg.div hΛ1 (fun z hz => hΛ1ne z hz)
  have hιne : ∀ z ∈ U, incidence Λ₁ Λ₂ z ≠ 0 := by
    intro z hz
    rw [incidence]
    exact div_ne_zero (by simpa using hΛ2ne z hz) (hΛ1ne z hz)
  -- the log-derivative equals the difference and is continuous on `U`
  have hld : ∀ z ∈ U, logDeriv (incidence Λ₁ Λ₂) z = logDeriv Λ₂ z - logDeriv Λ₁ z :=
    fun z hz => logDeriv_incidence (hΛ1ne z hz) (hΛ2ne z hz)
      (hΛ1 z hz).differentiableAt (hΛ2 z hz).differentiableAt
  have hldiffc : ContinuousOn (fun z => logDeriv Λ₂ z - logDeriv Λ₁ z) U := by
    have hc1 : ContinuousOn (fun z => logDeriv Λ₁ z) U := by
      have : (fun z => logDeriv Λ₁ z) = fun z => deriv Λ₁ z / Λ₁ z := by
        funext z; rw [logDeriv_apply]
      rw [this]
      exact (hΛ1.deriv.continuousOn).div hΛ1.continuousOn (fun z hz => hΛ1ne z hz)
    have hc2 : ContinuousOn (fun z => logDeriv Λ₂ z) U := by
      have : (fun z => logDeriv Λ₂ z) = fun z => deriv Λ₂ z / Λ₂ z := by
        funext z; rw [logDeriv_apply]
      rw [this]
      exact (hΛ2.deriv.continuousOn).div hΛ2.continuousOn (fun z hz => hΛ2ne z hz)
    exact hc2.sub hc1
  -- transport the polar data through the real preimage of `U`
  set V : Set ℝ := stripPt σ ⁻¹' U with hV
  have hstripc : Continuous (stripPt σ) := by
    unfold stripPt
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hVopen : IsOpen V := hU.preimage hstripc
  have hIccV : Set.Icc a b ⊆ V := fun τ hτ => hmapU τ hτ
  set ω : ℝ → ℂ := fun τ => logDeriv (incidence Λ₁ Λ₂) (stripPt σ τ) * Complex.I with hω
  have hωc : ContinuousOn ω V := by
    have hcomp : ContinuousOn (fun τ => logDeriv (incidence Λ₁ Λ₂) (stripPt σ τ)) V := by
      have hcongr : ContinuousOn (fun τ => (logDeriv Λ₂ (stripPt σ τ)
          - logDeriv Λ₁ (stripPt σ τ))) V :=
        hldiffc.comp hstripc.continuousOn (fun τ hτ => hτ)
      refine hcongr.congr (fun τ hτ => ?_)
      exact hld (stripPt σ τ) hτ
    exact hcomp.mul continuousOn_const
  have hG : ∀ τ ∈ Set.Icc a b,
      HasDerivAt (fun τ => incidence Λ₁ Λ₂ (stripPt σ τ))
        ((fun τ => incidence Λ₁ Λ₂ (stripPt σ τ)) τ * ω τ) τ := by
    intro τ hτ
    have hzU : stripPt σ τ ∈ U := hmapU τ hτ
    have hderiv : HasDerivAt (incidence Λ₁ Λ₂)
        (deriv (incidence Λ₁ Λ₂) (stripPt σ τ)) (stripPt σ τ) :=
      (hιan (stripPt σ τ) hzU).differentiableAt.hasDerivAt
    have hcomp := hderiv.comp τ (hasDerivAt_stripPt σ τ)
    have hne := hιne (stripPt σ τ) hzU
    have hval : deriv (incidence Λ₁ Λ₂) (stripPt σ τ) * Complex.I
        = incidence Λ₁ Λ₂ (stripPt σ τ) * ω τ := by
      have hkey : incidence Λ₁ Λ₂ (stripPt σ τ)
          * logDeriv (incidence Λ₁ Λ₂) (stripPt σ τ)
          = deriv (incidence Λ₁ Λ₂) (stripPt σ τ) := by
        rw [logDeriv_apply, mul_comm, div_mul_cancel₀ _ hne]
      rw [hω, ← mul_assoc, hkey]
    rw [hval] at hcomp
    exact hcomp
  have hGa : incidence Λ₁ Λ₂ (stripPt σ a) ≠ 0 :=
    hιne (stripPt σ a) (hmapU a ⟨le_refl a, hab⟩)
  obtain ⟨R, θ, hRne, hpolar, hθc, hθadv⟩ :=
    polar_data_of_logDeriv hVopen hIccV hG hωc hGa
  -- the pointwise rate floor
  have hImω : ∀ τ ∈ Set.Icc a b,
      (ω τ).im = (logDeriv Λ₂ (stripPt σ τ) - logDeriv Λ₁ (stripPt σ τ)).re := by
    intro τ hτ
    rw [hω, Complex.mul_I_im, hld (stripPt σ τ) (hmapU τ hτ)]
  have hgc : ContinuousOn (fun τ => (ω τ).im) (Set.Icc a b) :=
    (Complex.continuous_im.comp_continuousOn (hωc.mono hIccV))
  have hgfloor : ∀ τ ∈ Set.Icc a b, ρ₀ ≤ (ω τ).im := by
    intro τ hτ; rw [hImω τ hτ]; exact hfloor τ hτ
  have hratefloor := rate_floor_of_phase_advance hgc hθadv hgfloor
  -- apply the multi-crossing engine to the incidence carrier
  obtain ⟨e, hemono, hev⟩ :=
    exists_strictMono_events_of_rate_floor (F := fun τ => incidence Λ₁ Λ₂ (stripPt σ τ))
      hab hρ hpolar hθc hratefloor hn
  refine ⟨e, hemono, fun i => ⟨(hev i).1, ?_⟩⟩
  exact incidence_real_member_zero_of_im_zero
    (hΛ1ne (stripPt σ (e i)) (hmapU (e i) (hev i).1)) (hev i).2

end RHTower
