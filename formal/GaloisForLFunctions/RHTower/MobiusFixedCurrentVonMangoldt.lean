import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.MobiusCausalFlatLimit

/-!
# The fixed current of the moving Möbius multiplier

The exact moving-aperture signed Möbius multiplier

```text
τ_σ(u) = ζ(2σ)/[ζ(σ)ζ(σ+uε)]
```

has a logarithmic current that is entirely free of its `u`-independent gauge factors:

```text
∂_u log τ_σ(u) = ε·A(σ+uε),     A(s) = -ζ′(s)/ζ(s).
```

The same current is the normal derivative of the Suzuki packet Dirichlet series
`C(α,s) = ζ(s-α)/ζ(s+α)` at `α = 0`, whereas tying the normal shift to the thermal parameter
before differentiating destroys it: `C(α,1+2α) → 3`.  Finally the critical Euler clock has the
mean-one exponential Laplace transform and first moment.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The positive von Mangoldt current `A(s) = -ζ′(s)/ζ(s)`. -/
def vonMangoldtCurrent (s : ℂ) : ℂ := -deriv riemannZeta s / riemannZeta s

/-- The exact moving-aperture signed Möbius multiplier. -/
def mobiusMovingMultiplier (σ ε u : ℝ) : ℂ :=
  riemannZeta (2 * (σ : ℂ)) /
    (riemannZeta (σ : ℂ) * riemannZeta ((σ : ℂ) + (u : ℂ) * (ε : ℂ)))

theorem riemannZeta_ofReal_ne_zero {x : ℝ} (hx : 1 < x) : riemannZeta (x : ℂ) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  rw [Complex.ofReal_re]
  linarith

theorem ofReal_ne_one {x : ℝ} (hx : 1 < x) : (x : ℂ) ≠ 1 := by
  intro h
  have : (x : ℂ).re = (1 : ℂ).re := by rw [h]
  rw [Complex.ofReal_re, Complex.one_re] at this
  linarith

/-- The shifted aperture point stays inside the Euler half plane. -/
theorem movingAperture_re {σ ε u : ℝ} (hσ : 1 < σ) (hε : 0 < ε) (hu : 0 ≤ u) :
    ((σ : ℂ) + (u : ℂ) * (ε : ℂ)) = (((σ + u * ε : ℝ)) : ℂ) ∧ 1 < σ + u * ε := by
  refine ⟨by push_cast; ring, ?_⟩
  have : 0 ≤ u * ε := mul_nonneg hu (le_of_lt hε)
  linarith

/-- **The fixed-current theorem `(4)`.**  The parameter derivative of the moving multiplier is its
own von Mangoldt current: every `u`-independent gauge factor drops out. -/
theorem hasDerivAt_mobiusMovingMultiplier {σ ε : ℝ} (hσ : 1 < σ) (hε : 0 < ε) {u : ℝ}
    (hu : 0 ≤ u) :
    HasDerivAt (fun v : ℝ => mobiusMovingMultiplier σ ε v)
      ((ε : ℂ) * vonMangoldtCurrent ((σ : ℂ) + (u : ℂ) * (ε : ℂ)) *
        mobiusMovingMultiplier σ ε u) u := by
  obtain ⟨hcast, hre⟩ := movingAperture_re hσ hε hu
  have hne : ((σ : ℂ) + (u : ℂ) * (ε : ℂ)) ≠ 1 := by
    rw [hcast]
    exact ofReal_ne_one hre
  have hζne : riemannZeta ((σ : ℂ) + (u : ℂ) * (ε : ℂ)) ≠ 0 := by
    rw [hcast]
    exact riemannZeta_ofReal_ne_zero hre
  have hlin : HasDerivAt (fun v : ℝ => (σ : ℂ) + (v : ℂ) * (ε : ℂ)) (ε : ℂ) u := by
    have h : HasDerivAt (fun v : ℝ => ((v : ℝ) : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    simpa using (h.mul_const (ε : ℂ)).const_add (σ : ℂ)
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta ((σ : ℂ) + (u : ℂ) * (ε : ℂ)))
      ((σ : ℂ) + (u : ℂ) * (ε : ℂ)) := (differentiableAt_riemannZeta hne).hasDerivAt
  have hcomp : HasDerivAt (fun v : ℝ => riemannZeta ((σ : ℂ) + (v : ℂ) * (ε : ℂ)))
      ((ε : ℂ) * deriv riemannZeta ((σ : ℂ) + (u : ℂ) * (ε : ℂ))) u := by
    have h := hζ.scomp u hlin
    simpa [Function.comp, smul_eq_mul, mul_comm] using! h
  have hden : HasDerivAt (fun v : ℝ =>
      riemannZeta (σ : ℂ) * riemannZeta ((σ : ℂ) + (v : ℂ) * (ε : ℂ)))
      (riemannZeta (σ : ℂ) * ((ε : ℂ) * deriv riemannZeta ((σ : ℂ) + (u : ℂ) * (ε : ℂ)))) u := by
    have h := hcomp.const_mul (riemannZeta (σ : ℂ))
    exact h
  have hσne : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ofReal_ne_zero hσ
  have hdenne : riemannZeta (σ : ℂ) * riemannZeta ((σ : ℂ) + (u : ℂ) * (ε : ℂ)) ≠ 0 :=
    mul_ne_zero hσne hζne
  have h := (hasDerivAt_const u (riemannZeta (2 * (σ : ℂ)))).div hden hdenne
  refine h.congr_deriv ?_
  rw [mobiusMovingMultiplier, vonMangoldtCurrent]
  field_simp
  ring

/-- The logarithmic form of the fixed current. -/
theorem logDeriv_mobiusMovingMultiplier {σ ε : ℝ} (hσ : 1 < σ) (hε : 0 < ε) {u : ℝ} (hu : 0 ≤ u) :
    logDeriv (fun v : ℝ => mobiusMovingMultiplier σ ε v) u
      = (ε : ℂ) * vonMangoldtCurrent ((σ : ℂ) + (u : ℂ) * (ε : ℂ)) := by
  obtain ⟨hcast, hre⟩ := movingAperture_re hσ hε hu
  have hζne : riemannZeta ((σ : ℂ) + (u : ℂ) * (ε : ℂ)) ≠ 0 := by
    rw [hcast]
    exact riemannZeta_ofReal_ne_zero hre
  have hσne : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ofReal_ne_zero hσ
  have h2σ : riemannZeta (2 * (σ : ℂ)) ≠ 0 := by
    have hcast2 : (2 : ℂ) * (σ : ℂ) = ((2 * σ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast2]
    exact riemannZeta_ofReal_ne_zero (by linarith)
  have hτne : mobiusMovingMultiplier σ ε u ≠ 0 := by
    rw [mobiusMovingMultiplier]
    exact div_ne_zero h2σ (mul_ne_zero hσne hζne)
  rw [logDeriv_apply, (hasDerivAt_mobiusMovingMultiplier hσ hε hu).deriv]
  field_simp

/-! ### The Suzuki packet Dirichlet series -/

/-- The packet Dirichlet series `C(α,s) = ζ(s-α)/ζ(s+α)`. -/
def suzukiPacketDirichlet (a : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s - (a : ℂ)) / riemannZeta (s + (a : ℂ))

/-- **The normal current `(7)`.**  The `α`-derivative of the packet series at `α = 0` is twice the
von Mangoldt current. -/
theorem hasDerivAt_suzukiPacketDirichlet {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (fun a : ℝ => suzukiPacketDirichlet a s) (2 * vonMangoldtCurrent s) 0 := by
  have hsne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    linarith
  have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)
  have hlin1 : HasDerivAt (fun a : ℝ => s - (a : ℂ)) (-1) 0 := by
    have h : HasDerivAt (fun a : ℝ => ((a : ℝ) : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    simpa using h.const_sub s
  have hlin2 : HasDerivAt (fun a : ℝ => s + (a : ℂ)) 1 0 := by
    have h : HasDerivAt (fun a : ℝ => ((a : ℝ) : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    simpa using h.const_add s
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hsne).hasDerivAt
  have hnum : HasDerivAt (fun a : ℝ => riemannZeta (s - (a : ℂ)))
      (-deriv riemannZeta s) 0 := by
    have hζ' : HasDerivAt riemannZeta (deriv riemannZeta (s - ((0 : ℝ) : ℂ)))
        (s - ((0 : ℝ) : ℂ)) := by
      have h0 : s - ((0 : ℝ) : ℂ) = s := by push_cast; ring
      rw [h0]
      exact hζ
    have h := HasDerivAt.scomp (h := fun a : ℝ => s - (a : ℂ)) 0 hζ' hlin1
    have h0 : s - ((0 : ℝ) : ℂ) = s := by push_cast; ring
    simpa [Function.comp, smul_eq_mul, h0] using! h
  have hden : HasDerivAt (fun a : ℝ => riemannZeta (s + (a : ℂ)))
      (deriv riemannZeta s) 0 := by
    have hζ' : HasDerivAt riemannZeta (deriv riemannZeta (s + ((0 : ℝ) : ℂ)))
        (s + ((0 : ℝ) : ℂ)) := by
      have h0 : s + ((0 : ℝ) : ℂ) = s := by push_cast; ring
      rw [h0]
      exact hζ
    have h := HasDerivAt.scomp (h := fun a : ℝ => s + (a : ℂ)) 0 hζ' hlin2
    have h0 : s + ((0 : ℝ) : ℂ) = s := by push_cast; ring
    simpa [Function.comp, smul_eq_mul, h0] using! h
  have hzero : riemannZeta (s + ((0 : ℝ) : ℂ)) ≠ 0 := by
    have h0 : s + ((0 : ℝ) : ℂ) = s := by push_cast; ring
    rw [h0]
    exact hζne
  have h := hnum.div hden hzero
  refine h.congr_deriv ?_
  have h0 : s + ((0 : ℝ) : ℂ) = s := by push_cast; ring
  have h0' : s - ((0 : ℝ) : ℂ) = s := by push_cast; ring
  rw [vonMangoldtCurrent, h0, h0']
  field_simp
  ring

/-! ### The diagonal collapse -/

theorem tendsto_ofReal_one_add_mul {c : ℝ} (hc : 0 < c) :
    Tendsto (fun a : ℝ => (1 : ℂ) + (c : ℂ) * (a : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : Continuous fun a : ℝ => (1 : ℂ) + (c : ℂ) * (a : ℂ) := by fun_prop
    have h0 : (1 : ℂ) + (c : ℂ) * ((0 : ℝ) : ℂ) = 1 := by push_cast; ring
    have h := hcont.tendsto (0 : ℝ)
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with a ha
    have hapos : (0 : ℝ) < a := ha
    intro hmem
    rw [Set.mem_singleton_iff] at hmem
    have hre : ((1 : ℂ) + (c : ℂ) * (a : ℂ)).re = 1 := by rw [hmem]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] at hre
    nlinarith

theorem tendsto_mul_riemannZeta_one_add_mul {c : ℝ} (hc : 0 < c) :
    Tendsto (fun a : ℝ => ((c : ℂ) * (a : ℂ)) * riemannZeta (1 + (c : ℂ) * (a : ℂ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have hcomp := riemannZeta_residue_one.comp (tendsto_ofReal_one_add_mul hc)
  refine hcomp.congr fun a => ?_
  simp only [Function.comp_apply]
  ring_nf

/-- **The diagonal collapse `(8)`.**  Tying the normal shift to the thermal parameter before
differentiating gives the limit `3`, not the von Mangoldt current. -/
theorem tendsto_suzukiPacketDirichlet_diagonal :
    Tendsto (fun a : ℝ => suzukiPacketDirichlet a (1 + 2 * (a : ℂ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 3) := by
  have h1 := tendsto_mul_riemannZeta_one_add_mul (c := 1) (by norm_num)
  have h3 := tendsto_mul_riemannZeta_one_add_mul (c := 3) (by norm_num)
  have hdiv := h1.div h3 (by norm_num)
  rw [div_one] at hdiv
  have hmul := hdiv.const_mul (3 : ℂ)
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have hapos : (0 : ℝ) < a := ha
  have hane : ((a : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hapos
  have hz1 : riemannZeta (1 + (a : ℂ)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hz3 : riemannZeta (1 + (a : ℂ) * 3) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
    nlinarith
  have hnum : (1 : ℂ) + 2 * (a : ℂ) - (a : ℂ) = 1 + (a : ℂ) := by ring
  have hden : (1 : ℂ) + 2 * (a : ℂ) + (a : ℂ) = 1 + (a : ℂ) * 3 := by ring
  simp only [Pi.div_apply]
  rw [suzukiPacketDirichlet, hnum, hden]
  push_cast
  field_simp

/-! ### The critical Euler clock -/

/-- **`(9)`/`(12)`: the Euler current has a simple pole of residue one.**  For every positive
scale `c`, `cε·A(1+cε) → 1` as `ε → 0+`. -/
theorem tendsto_mul_vonMangoldtCurrent_scaled {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε : ℝ => ((c : ℂ) * (ε : ℂ)) * vonMangoldtCurrent (1 + (c : ℂ) * (ε : ℂ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have hcomp := neg_logDeriv_zeta_residue.comp (tendsto_ofReal_one_add_mul hc)
  refine hcomp.congr fun a => ?_
  simp only [Function.comp_apply, vonMangoldtCurrent]
  ring_nf

/-- **`(11)`: the critical Euler clock has the mean-one exponential Laplace transform.** -/
theorem tendsto_eulerClockLaplace {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun ε : ℝ => vonMangoldtCurrent (1 + ((1 + u : ℝ) : ℂ) * (ε : ℂ)) /
        vonMangoldtCurrent (1 + ((1 : ℝ) : ℂ) * (ε : ℂ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 / (1 + (u : ℂ)))) := by
  have hu1 : (0 : ℝ) < 1 + u := by linarith
  have hnum := tendsto_mul_riemannZeta_one_add_mul (c := 1 + u) hu1
  have hnumA := tendsto_mul_vonMangoldtCurrent_scaled (c := 1 + u) hu1
  have hdenA := tendsto_mul_vonMangoldtCurrent_scaled (c := 1) (by norm_num)
  have hscale : Tendsto (fun ε : ℝ =>
      (((1 : ℝ) : ℂ) * (ε : ℂ)) * vonMangoldtCurrent (1 + ((1 : ℝ) : ℂ) * (ε : ℂ)) *
        (1 + (u : ℂ))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 + (u : ℂ))) := by
    have h := hdenA.mul_const (1 + (u : ℂ))
    simpa using h
  have hne : (1 : ℂ) + (u : ℂ) ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) + (u : ℂ)).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hre
    linarith
  have hdiv := hnumA.div hscale hne
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hεne : ((ε : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hεpos
  have hcne : (((1 + u : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hu1
  simp only [Pi.div_apply]
  push_cast
  field_simp

/-! ### The first moment of the critical Euler clock -/

/-- The Euler current is the pole plus the analytic unit's logarithmic derivative. -/
theorem vonMangoldtCurrent_eventuallyEq :
    vonMangoldtCurrent =ᶠ[nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ]
      fun z => (z - 1)⁻¹ - logDeriv zetaResidueUnit z := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds zetaResidueUnit_ne_zero_eventually]
    with s hs hG
  have hs1 : s ≠ 1 := hs
  have h : -deriv riemannZeta s / riemannZeta s = -logDeriv riemannZeta s := by
    rw [logDeriv_apply]; ring
  rw [vonMangoldtCurrent, h, logDeriv_zeta_eq hs1 hG]
  ring

/-- **The derivative residue of the Euler current.**  `(s-1)² A′(s) → -1`. -/
theorem tendsto_sub_one_sq_mul_deriv_vonMangoldtCurrent :
    Tendsto (fun s : ℂ => (s - 1) ^ (2 : ℕ) * deriv vonMangoldtCurrent s)
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds (-1)) := by
  have hG1 : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have hlogGeq : ∀ z : ℂ, logDeriv zetaResidueUnit z
      = deriv zetaResidueUnit z / zetaResidueUnit z := fun z => logDeriv_apply _ _
  have hlogG : ∀ z : ℂ, zetaResidueUnit z ≠ 0 → AnalyticAt ℂ (logDeriv zetaResidueUnit) z := by
    intro z hz
    have hGz : AnalyticAt ℂ zetaResidueUnit z := analyticAt_zetaResidueUnit z
    have h : AnalyticAt ℂ (fun w => deriv zetaResidueUnit w / zetaResidueUnit w) z :=
      hGz.deriv.div hGz hz
    refine h.congr ?_
    filter_upwards with w
    rw [hlogGeq w]
  have hderivcont : ContinuousAt (deriv (logDeriv zetaResidueUnit)) 1 :=
    (hlogG 1 hG1).deriv.continuousAt
  have hsub : Tendsto (fun s : ℂ => s - 1) (nhds (1 : ℂ)) (nhds 0) := by
    simpa using (continuous_sub_right (1 : ℂ)).tendsto (1 : ℂ)
  have hmain : Tendsto (fun s : ℂ => -1 - (s - 1) ^ (2 : ℕ) * deriv (logDeriv zetaResidueUnit) s)
      (nhds (1 : ℂ)) (nhds (-1)) := by
    have h := (hsub.pow 2).mul hderivcont.tendsto
    have h0 : Tendsto (fun s : ℂ => (s - 1) ^ (2 : ℕ) * deriv (logDeriv zetaResidueUnit) s)
        (nhds (1 : ℂ)) (nhds 0) := by simpa using h
    have h1 := (tendsto_const_nhds (x := (-1 : ℂ))).sub h0
    simpa using h1
  refine Tendsto.congr' ?_ (hmain.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds zetaResidueUnit_ne_zero_eventually] with s hs hG
  have hs1 : s ≠ 1 := hs
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hGne : ∀ᶠ z in nhds s, zetaResidueUnit z ≠ 0 :=
    ((analyticAt_zetaResidueUnit s).continuousAt).eventually_ne hG
  have hopen : IsOpen ({(1 : ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
  have heq : vonMangoldtCurrent =ᶠ[nhds s]
      fun z => (z - 1)⁻¹ - logDeriv zetaResidueUnit z := by
    filter_upwards [hopen.mem_nhds (show s ∈ ({(1 : ℂ)}ᶜ : Set ℂ) by simpa using hs1), hGne]
      with z hz hGz
    have hz1 : z ≠ 1 := by simpa using hz
    have h : -deriv riemannZeta z / riemannZeta z = -logDeriv riemannZeta z := by
      rw [logDeriv_apply]; ring
    rw [vonMangoldtCurrent, h, logDeriv_zeta_eq hz1 hGz]
    ring
  have hinv : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-1 / (s - 1) ^ (2 : ℕ)) s :=
    ((hasDerivAt_id s).sub_const 1).inv hs0
  have hsum : HasDerivAt (fun z : ℂ => (z - 1)⁻¹ - logDeriv zetaResidueUnit z)
      (-1 / (s - 1) ^ (2 : ℕ) - deriv (logDeriv zetaResidueUnit) s) s :=
    hinv.sub ((hlogG s hG).differentiableAt.hasDerivAt)
  have hderiv : deriv vonMangoldtCurrent s
      = -1 / (s - 1) ^ (2 : ℕ) - deriv (logDeriv zetaResidueUnit) s := by
    rw [heq.deriv_eq, hsum.deriv]
  rw [hderiv]
  field_simp

/-- **`(13)`: the first moment of the critical Euler clock tends to one.** -/
theorem tendsto_eulerClockFirstMoment :
    Tendsto (fun ε : ℝ => -(ε : ℂ) * deriv vonMangoldtCurrent (1 + (ε : ℂ)) /
        vonMangoldtCurrent (1 + (ε : ℂ))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
  have hmap : Tendsto (fun ε : ℝ => (1 : ℂ) + (ε : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
    have h := tendsto_ofReal_one_add_mul (c := 1) (by norm_num)
    refine h.congr fun a => ?_
    push_cast
    ring
  have hnum := tendsto_sub_one_sq_mul_deriv_vonMangoldtCurrent.comp hmap
  have hden := neg_logDeriv_zeta_residue.comp hmap
  have hdiv := hnum.div hden (by norm_num)
  have hval : (-1 : ℂ) / 1 = -1 := by norm_num
  rw [hval] at hdiv
  have hneg := hdiv.neg
  rw [neg_neg] at hneg
  refine hneg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hεne : ((ε : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hεpos
  simp only [Pi.div_apply, Function.comp_apply, vonMangoldtCurrent]
  have hcast : (1 : ℂ) + (ε : ℂ) - 1 = (ε : ℂ) := by ring
  rw [hcast]
  field_simp

/-! ### The second moment of the critical Euler clock -/

/-- The open set on which the Euler current equals its Laurent form. -/
def eulerCurrentLaurentSet : Set ℂ := {z : ℂ | z ≠ 1 ∧ zetaResidueUnit z ≠ 0}

theorem isOpen_eulerCurrentLaurentSet : IsOpen eulerCurrentLaurentSet := by
  have h1 : IsOpen ({(1 : ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hcont : Continuous zetaResidueUnit := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    exact (analyticAt_zetaResidueUnit z).continuousAt
  have h2 : IsOpen {z : ℂ | zetaResidueUnit z ≠ 0} := isOpen_ne_fun hcont continuous_const
  have hset : eulerCurrentLaurentSet = ({(1 : ℂ)}ᶜ : Set ℂ) ∩ {z : ℂ | zetaResidueUnit z ≠ 0} := by
    ext z
    simp only [eulerCurrentLaurentSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_singleton_iff]
  rw [hset]
  exact h1.inter h2

theorem analyticAt_logDeriv_zetaResidueUnit {z : ℂ} (hz : zetaResidueUnit z ≠ 0) :
    AnalyticAt ℂ (logDeriv zetaResidueUnit) z := by
  have hGz : AnalyticAt ℂ zetaResidueUnit z := analyticAt_zetaResidueUnit z
  have h : AnalyticAt ℂ (fun w => deriv zetaResidueUnit w / zetaResidueUnit w) z :=
    hGz.deriv.div hGz hz
  refine h.congr ?_
  filter_upwards with w
  rw [logDeriv_apply]

/-- **`(12)`: the simple pole of zeta.**  The Euler current minus its polar part has a limit at the
pole, namely minus the logarithmic derivative of the analytic residue unit.  This is the exact form
of `A(1+x) = 1/x + O(1)`. -/
theorem tendsto_vonMangoldtCurrent_sub_pole :
    Tendsto (fun s : ℂ => vonMangoldtCurrent s - (s - 1)⁻¹)
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds (-logDeriv zetaResidueUnit 1)) := by
  have hG1 : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have hcont : Tendsto (fun s : ℂ => -logDeriv zetaResidueUnit s) (nhds (1 : ℂ))
      (nhds (-logDeriv zetaResidueUnit 1)) :=
    ((analyticAt_logDeriv_zetaResidueUnit hG1).continuousAt.tendsto).neg
  refine (hcont.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [vonMangoldtCurrent_eventuallyEq] with s hs
  rw [hs]
  ring

/-- **The `O(1)` statement of `(12)`.**  The correction to the polar part is bounded near the
pole. -/
theorem exists_bound_vonMangoldtCurrent_sub_pole :
    ∃ C : ℝ, ∀ᶠ s : ℂ in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ,
      ‖vonMangoldtCurrent s - (s - 1)⁻¹‖ ≤ C := by
  refine ⟨‖(-logDeriv zetaResidueUnit 1)‖ + 1, ?_⟩
  have hball := tendsto_vonMangoldtCurrent_sub_pole
    (Metric.ball_mem_nhds (-logDeriv zetaResidueUnit 1) one_pos)
  filter_upwards [hball] with s hs
  have hdist : dist (vonMangoldtCurrent s - (s - 1)⁻¹) (-logDeriv zetaResidueUnit 1) < 1 :=
    Metric.mem_ball.mp hs
  have := norm_le_norm_add_norm_sub' (vonMangoldtCurrent s - (s - 1)⁻¹)
    (-logDeriv zetaResidueUnit 1)
  rw [dist_eq_norm] at hdist
  linarith [this]

/-- **`(12)` along the real critical scaling.**  For real escapes the correction to `1/x` stays
bounded. -/
theorem exists_bound_vonMangoldtCurrent_one_add_sub_inv :
    ∃ C : ℝ, ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖vonMangoldtCurrent (1 + (x : ℂ)) - ((x : ℂ))⁻¹‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_vonMangoldtCurrent_sub_pole
  refine ⟨C, ?_⟩
  have hmap := tendsto_ofReal_one_add_mul (c := 1) one_pos
  have hpull := hmap.eventually hC
  filter_upwards [hpull] with x hx
  have harg : (1 : ℂ) + ((1 : ℝ) : ℂ) * (x : ℂ) - 1 = (x : ℂ) := by push_cast; ring
  have hval : (1 : ℂ) + ((1 : ℝ) : ℂ) * (x : ℂ) = 1 + (x : ℂ) := by push_cast; ring
  rw [harg, hval] at hx
  exact hx

theorem deriv_vonMangoldtCurrent_of_mem {s : ℂ} (hs : s ∈ eulerCurrentLaurentSet) :
    deriv vonMangoldtCurrent s = -1 / (s - 1) ^ (2 : ℕ) - deriv (logDeriv zetaResidueUnit) s := by
  have hsmem : s ∈ eulerCurrentLaurentSet := hs
  obtain ⟨hs1, hG⟩ := hs
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have heq : vonMangoldtCurrent =ᶠ[nhds s]
      fun z => (z - 1)⁻¹ - logDeriv zetaResidueUnit z := by
    filter_upwards [isOpen_eulerCurrentLaurentSet.mem_nhds hsmem] with z hz
    obtain ⟨hz1, hGz⟩ := hz
    have h : -deriv riemannZeta z / riemannZeta z = -logDeriv riemannZeta z := by
      rw [logDeriv_apply]; ring
    rw [vonMangoldtCurrent, h, logDeriv_zeta_eq hz1 hGz]
    ring
  have hinv : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-1 / (s - 1) ^ (2 : ℕ)) s :=
    ((hasDerivAt_id s).sub_const 1).inv hs0
  have hsum : HasDerivAt (fun z : ℂ => (z - 1)⁻¹ - logDeriv zetaResidueUnit z)
      (-1 / (s - 1) ^ (2 : ℕ) - deriv (logDeriv zetaResidueUnit) s) s :=
    hinv.sub ((analyticAt_logDeriv_zetaResidueUnit hG).differentiableAt.hasDerivAt)
  rw [heq.deriv_eq, hsum.deriv]

/-- **The differentiated form of `(12)`.**  The derivative of the Euler current minus its double
polar part has a limit at the pole: `A′(1+x) = -x^{-2} + O(1)`. -/
theorem tendsto_deriv_vonMangoldtCurrent_add_pole :
    Tendsto (fun s : ℂ => deriv vonMangoldtCurrent s + 1 / (s - 1) ^ (2 : ℕ))
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds (-deriv (logDeriv zetaResidueUnit) 1)) := by
  have hG1 : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have hcont : Tendsto (fun s : ℂ => -deriv (logDeriv zetaResidueUnit) s) (nhds (1 : ℂ))
      (nhds (-deriv (logDeriv zetaResidueUnit) 1)) :=
    (((analyticAt_logDeriv_zetaResidueUnit hG1).deriv).continuousAt.tendsto).neg
  refine (hcont.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds zetaResidueUnit_ne_zero_eventually] with s hs hG
  have hmem : s ∈ eulerCurrentLaurentSet := ⟨hs, hG⟩
  rw [deriv_vonMangoldtCurrent_of_mem hmem]
  ring

/-- **The `O(1)` statement of the differentiated `(12)`.** -/
theorem exists_bound_deriv_vonMangoldtCurrent_add_pole :
    ∃ C : ℝ, ∀ᶠ s : ℂ in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ,
      ‖deriv vonMangoldtCurrent s + 1 / (s - 1) ^ (2 : ℕ)‖ ≤ C := by
  refine ⟨‖(-deriv (logDeriv zetaResidueUnit) 1)‖ + 1, ?_⟩
  have hball := tendsto_deriv_vonMangoldtCurrent_add_pole
    (Metric.ball_mem_nhds (-deriv (logDeriv zetaResidueUnit) 1) one_pos)
  filter_upwards [hball] with s hs
  have hdist : dist (deriv vonMangoldtCurrent s + 1 / (s - 1) ^ (2 : ℕ))
      (-deriv (logDeriv zetaResidueUnit) 1) < 1 := Metric.mem_ball.mp hs
  have hnorm := norm_le_norm_add_norm_sub' (deriv vonMangoldtCurrent s + 1 / (s - 1) ^ (2 : ℕ))
    (-deriv (logDeriv zetaResidueUnit) 1)
  rw [dist_eq_norm] at hdist
  linarith [hnorm]

/-- **The differentiated `(12)` along the real critical scaling.** -/
theorem exists_bound_deriv_vonMangoldtCurrent_one_add :
    ∃ C : ℝ, ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖deriv vonMangoldtCurrent (1 + (x : ℂ)) + 1 / (x : ℂ) ^ (2 : ℕ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_deriv_vonMangoldtCurrent_add_pole
  refine ⟨C, ?_⟩
  have hpull := (tendsto_ofReal_one_add_mul (c := 1) one_pos).eventually hC
  filter_upwards [hpull] with x hx
  have harg : (1 : ℂ) + ((1 : ℝ) : ℂ) * (x : ℂ) - 1 = (x : ℂ) := by push_cast; ring
  have hval : (1 : ℂ) + ((1 : ℝ) : ℂ) * (x : ℂ) = 1 + (x : ℂ) := by push_cast; ring
  rw [harg, hval] at hx
  exact hx

theorem hasDerivAt_neg_inv_sq {s : ℂ} (hs : s - 1 ≠ 0) :
    HasDerivAt (fun z : ℂ => -1 / (z - 1) ^ (2 : ℕ)) (2 / (s - 1) ^ (3 : ℕ)) s := by
  have hbase : HasDerivAt (fun z : ℂ => (z - 1) ^ (2 : ℕ)) (2 * (s - 1)) s := by
    have hlinear : HasDerivAt (fun z : ℂ => z - 1) 1 s :=
      (hasDerivAt_id s).sub_const 1
    exact (hlinear.pow 2).congr_deriv (by ring)
  have hne : ((s - 1) ^ (2 : ℕ)) ≠ 0 := pow_ne_zero 2 hs
  have hinv := hbase.inv hne
  have hneg := hinv.neg
  have hval : -(-(2 * (s - 1)) / ((s - 1) ^ (2 : ℕ)) ^ (2 : ℕ)) = 2 / (s - 1) ^ (3 : ℕ) := by
    field_simp
  rw [hval] at hneg
  refine hneg.congr_of_eventuallyEq ?_
  filter_upwards with z
  simp only [Pi.neg_apply, Pi.inv_apply]
  rw [neg_div, one_div]

/-- The Laurent form of the second derivative of the Euler current: a triple pole with an
analytic correction. -/
theorem deriv2_vonMangoldtCurrent_of_mem {s : ℂ} (hs : s ∈ eulerCurrentLaurentSet) :
    deriv (deriv vonMangoldtCurrent) s
      = 2 / (s - 1) ^ (3 : ℕ) - deriv (deriv (logDeriv zetaResidueUnit)) s := by
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.1
  have heq : deriv vonMangoldtCurrent =ᶠ[nhds s]
      fun z => -1 / (z - 1) ^ (2 : ℕ) - deriv (logDeriv zetaResidueUnit) z := by
    filter_upwards [isOpen_eulerCurrentLaurentSet.mem_nhds hs] with z hz
    exact deriv_vonMangoldtCurrent_of_mem hz
  have hsum : HasDerivAt (fun z : ℂ => -1 / (z - 1) ^ (2 : ℕ) - deriv (logDeriv zetaResidueUnit) z)
      (2 / (s - 1) ^ (3 : ℕ) - deriv (deriv (logDeriv zetaResidueUnit)) s) s :=
    (hasDerivAt_neg_inv_sq hs0).sub
      ((analyticAt_logDeriv_zetaResidueUnit hs.2).deriv.differentiableAt.hasDerivAt)
  rw [heq.deriv_eq, hsum.deriv]

/-- **The second-order residue expansion.**  The second derivative of the Euler current minus its
triple polar part has a limit at the pole: `A″(1+x) = 2x^{-3} + O(1)`. -/
theorem tendsto_deriv2_vonMangoldtCurrent_sub_pole :
    Tendsto (fun s : ℂ => deriv (deriv vonMangoldtCurrent) s - 2 / (s - 1) ^ (3 : ℕ))
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ)
      (nhds (-deriv (deriv (logDeriv zetaResidueUnit)) 1)) := by
  have hG1 : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have hcont : Tendsto (fun s : ℂ => -deriv (deriv (logDeriv zetaResidueUnit)) s) (nhds (1 : ℂ))
      (nhds (-deriv (deriv (logDeriv zetaResidueUnit)) 1)) :=
    (((analyticAt_logDeriv_zetaResidueUnit hG1).deriv.deriv).continuousAt.tendsto).neg
  refine (hcont.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds zetaResidueUnit_ne_zero_eventually] with s hs hG
  rw [deriv2_vonMangoldtCurrent_of_mem ⟨hs, hG⟩]
  ring

/-- **The `O(1)` statement of the second-order residue expansion.** -/
theorem exists_bound_deriv2_vonMangoldtCurrent_sub_pole :
    ∃ C : ℝ, ∀ᶠ s : ℂ in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ,
      ‖deriv (deriv vonMangoldtCurrent) s - 2 / (s - 1) ^ (3 : ℕ)‖ ≤ C := by
  refine ⟨‖(-deriv (deriv (logDeriv zetaResidueUnit)) 1)‖ + 1, ?_⟩
  have hball := tendsto_deriv2_vonMangoldtCurrent_sub_pole
    (Metric.ball_mem_nhds (-deriv (deriv (logDeriv zetaResidueUnit)) 1) one_pos)
  filter_upwards [hball] with s hs
  have hdist : dist (deriv (deriv vonMangoldtCurrent) s - 2 / (s - 1) ^ (3 : ℕ))
      (-deriv (deriv (logDeriv zetaResidueUnit)) 1) < 1 := Metric.mem_ball.mp hs
  have hnorm := norm_le_norm_add_norm_sub' (deriv (deriv vonMangoldtCurrent) s - 2 / (s - 1) ^ (3 : ℕ))
    (-deriv (deriv (logDeriv zetaResidueUnit)) 1)
  rw [dist_eq_norm] at hdist
  linarith [hnorm]

/-- **The second derivative residue of the Euler current.**  `(s-1)³ A″(s) → 2`. -/
theorem tendsto_sub_one_cube_mul_deriv2_vonMangoldtCurrent :
    Tendsto (fun s : ℂ => (s - 1) ^ (3 : ℕ) * deriv (deriv vonMangoldtCurrent) s)
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 2) := by
  have hG1 : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have hderiv2cont : ContinuousAt (deriv (deriv (logDeriv zetaResidueUnit))) 1 :=
    (analyticAt_logDeriv_zetaResidueUnit hG1).deriv.deriv.continuousAt
  have hsub : Tendsto (fun s : ℂ => s - 1) (nhds (1 : ℂ)) (nhds 0) := by
    simpa using (continuous_sub_right (1 : ℂ)).tendsto (1 : ℂ)
  have hmain : Tendsto
      (fun s : ℂ => 2 - (s - 1) ^ (3 : ℕ) * deriv (deriv (logDeriv zetaResidueUnit)) s)
      (nhds (1 : ℂ)) (nhds 2) := by
    have h := (hsub.pow 3).mul hderiv2cont.tendsto
    have h0 : Tendsto (fun s : ℂ => (s - 1) ^ (3 : ℕ) * deriv (deriv (logDeriv zetaResidueUnit)) s)
        (nhds (1 : ℂ)) (nhds 0) := by simpa using h
    have h1 := (tendsto_const_nhds (x := (2 : ℂ))).sub h0
    simpa using h1
  refine Tendsto.congr' ?_ (hmain.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds zetaResidueUnit_ne_zero_eventually] with s hs hG
  have hs1 : s ≠ 1 := hs
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [deriv2_vonMangoldtCurrent_of_mem ⟨hs1, hG⟩]
  field_simp

/-- **`(15a)`: the second moment of the critical Euler clock tends to two.** -/
theorem tendsto_eulerClockSecondMoment :
    Tendsto (fun ε : ℝ => (ε : ℂ) ^ (2 : ℕ) * deriv (deriv vonMangoldtCurrent) (1 + (ε : ℂ)) /
        vonMangoldtCurrent (1 + (ε : ℂ))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 2) := by
  have hmap : Tendsto (fun ε : ℝ => (1 : ℂ) + (ε : ℂ)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) := by
    have h := tendsto_ofReal_one_add_mul (c := 1) (by norm_num)
    refine h.congr fun a => ?_
    push_cast
    ring
  have hnum := tendsto_sub_one_cube_mul_deriv2_vonMangoldtCurrent.comp hmap
  have hden := neg_logDeriv_zeta_residue.comp hmap
  have hdiv := hnum.div hden (by norm_num)
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hεne : ((ε : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hεpos
  simp only [Pi.div_apply, Function.comp_apply, vonMangoldtCurrent]
  have hcast : (1 : ℂ) + (ε : ℂ) - 1 = (ε : ℂ) := by ring
  rw [hcast]
  field_simp

end

end RHTower
