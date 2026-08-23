import GaloisForLFunctions.RHTower.ExtendedMellinHeadHardy
import GaloisForLFunctions.RHTower.DivShiftRepresentative
import GaloisForLFunctions.RHTower.HeadTailMellinAnalytic
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyMul

/-!
# The canonical Hardy representative of a vector of `L_a`

The witness `H` produced by `IsMellinHeadHardy` is only pinned down on the open half-plane
`Re w > 0`, which is useless for dividing at a point of the critical line.  There is however a
canonical choice: substituting `M(v) = N/(s(1-s))` into `((w-1/2)/(w+1/2))·a^w·M(v)(w+1/2)`
collapses everything to

  `soninHardyRep a c d v w = -a^w · N(w+1/2)/(w+1/2)^2`,

visibly analytic on `w ≠ -1/2`.  It agrees with any Hardy witness on `Re w > 0`, hence is itself a
Hardy function, and it is analytic at `ρ - 1/2` for every `ρ` of the open critical strip — including
the critical line.  That is what makes Burnol's Proposition 4.3 available at *every* strip point.

## Main results

* `soninHardyRep`, `soninHardyRep_eq`, `analyticAt_soninHardyRep`
* `isHalfPlaneHardy_soninHardyRep`
* `isMellinHeadHardy_divShiftNF`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem hardyRep_algebra (A N x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    -(A * N / x ^ 2) = (y / x) * (A * (N / (x * -y))) := by
  field_simp

variable {a : ℝ} {v : SoninL2} {c d : ℂ}

/-- The canonical Hardy representative. -/
def soninHardyRep (a : ℝ) (c d : ℂ) (v : SoninL2) : ℂ → ℂ := fun w =>
  -(((a : ℝ) : ℂ) ^ w * extendedMellinNumerator a c d v (w + 1 / 2) / (w + 1 / 2) ^ 2)

theorem analyticAt_soninHardyRep (ha : 0 < a) (hev : v ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    {w : ℂ} (hw : w + 1 / 2 ≠ 0) : AnalyticAt ℂ (soninHardyRep a c d v) w := by
  have hnum : AnalyticAt ℂ (fun z : ℂ => extendedMellinNumerator a c d v (z + 1 / 2)) w := by
    have h1 : AnalyticAt ℂ (extendedMellinNumerator a c d v) (w + 1 / 2) :=
      analyticAt_extendedMellinNumerator ha hev hc hd _
    have h2 : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) w := analyticAt_id.add analyticAt_const
    exact AnalyticAt.comp (g := extendedMellinNumerator a c d v)
      (f := fun z : ℂ => z + 1 / 2) h1 h2
  have hcpow : AnalyticAt ℂ (fun z : ℂ => ((a : ℝ) : ℂ) ^ z) w :=
    (differentiable_const_cpow_ofReal ha (fun z : ℂ => z) differentiable_id).analyticAt w
  have hden : AnalyticAt ℂ (fun z : ℂ => (z + 1 / 2) ^ 2) w :=
    (analyticAt_id.add analyticAt_const).pow 2
  have hne : ((w : ℂ) + 1 / 2) ^ 2 ≠ 0 := pow_ne_zero _ hw
  exact ((hcpow.mul hnum).div hden hne).neg

/-- On `w ≠ ±1/2` the canonical representative is the renormalised transform. -/
theorem soninHardyRep_eq (a : ℝ) (c d : ℂ) (v : SoninL2) {w : ℂ} (h0 : w + 1 / 2 ≠ 0)
    (h1 : w - 1 / 2 ≠ 0) :
    soninHardyRep a c d v w
      = ((w - 1 / 2) / (w + 1 / 2)) * (((a : ℝ) : ℂ) ^ w
          * extendedMellinContinuation a c d v (w + 1 / 2)) := by
  have hs : (1 : ℂ) - (w + 1 / 2) = -(w - 1 / 2) := by ring
  rw [soninHardyRep, extendedMellinContinuation, hs]
  exact hardyRep_algebra _ _ _ _ h0 h1

/-- **The canonical representative is a Hardy function of the right half-plane.** -/
theorem isHalfPlaneHardy_soninHardyRep (ha : 0 < a) (hev : v ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d) :
    ∃ M : ℝ, IsHalfPlaneHardy (soninHardyRep a c d v) M := by
  obtain ⟨H, M, hH, hHeq⟩ := isMellinHeadHardy_extendedMellinContinuation ha hev hc hd
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hshift : ∀ w : ℂ, 0 < w.re → w + 1 / 2 ≠ 0 := by
    intro w hw hzero
    have := congrArg Complex.re hzero
    simp at this
    linarith
  have hoff : ∀ w : ℂ, 0 < w.re → w ≠ 1 / 2 → H w = soninHardyRep a c d v w := by
    intro w hw hne
    have h1 : w - 1 / 2 ≠ 0 := sub_ne_zero.2 hne
    rw [hHeq w hw hne, soninHardyRep_eq a c d v (hshift w hw) h1]
  refine ⟨M, hH.congr ?_⟩
  intro w hw
  by_cases hne : w = 1 / 2
  · subst hne
    have hcontH : ContinuousAt H ((1 : ℂ) / 2) :=
      (hH.holo.differentiableAt (hopen.mem_nhds hw)).continuousAt
    have hcontR : ContinuousAt (soninHardyRep a c d v) ((1 : ℂ) / 2) :=
      (analyticAt_soninHardyRep ha hev hc hd (hshift _ hw)).continuousAt
    refine eq_of_eventuallyEq_punctured hcontH hcontR ?_
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds hw)] with z hz hz'
    exact hoff z hz' hz
  · exact hoff w hw hne

/-- **Proposition 4.3, head-Hardy half.**  Dividing the continued Mellin transform of a vector of
`L_a` by `(s - ρ)` at a zero `ρ` of the open critical strip keeps it in `L̂_a`. -/
theorem isMellinHeadHardy_divShiftNF (ha : 0 < a) (hev : v ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hvan : extendedMellinContinuation a c d v ρ = 0) :
    IsMellinHeadHardy a (divShiftNF (extendedMellinContinuation a c d v) ρ) := by
  set F : ℂ → ℂ := extendedMellinContinuation a c d v with hF
  have hFmero : ∀ s : ℂ, MeromorphicAt F s := meromorphicAt_extendedMellinContinuation ha hev hc hd
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hFana : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → AnalyticAt ℂ F s := fun s hs0 hs1 =>
    analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hs0 hs1
  set w₀ : ℂ := ρ - 1 / 2 with hw₀
  have hw₀shift : w₀ + 1 / 2 = ρ := by rw [hw₀]; ring
  have hw₀ne0 : w₀ + 1 / 2 ≠ 0 := by rw [hw₀shift]; exact hρ0
  have hw₀ne1 : w₀ - 1 / 2 ≠ 0 := by
    rw [hw₀]
    intro h
    exact hρ1 (by linear_combination h)
  obtain ⟨M, hHardy⟩ := isHalfPlaneHardy_soninHardyRep ha hev hc hd
  have hanaRep : AnalyticAt ℂ (soninHardyRep a c d v) w₀ :=
    analyticAt_soninHardyRep ha hev hc hd hw₀ne0
  have hvanRep : soninHardyRep a c d v w₀ = 0 := by
    rw [soninHardyRep_eq a c d v hw₀ne0 hw₀ne1, hw₀shift, ← hF, hvan]
    ring
  have hord : ((1 : ℕ) : ℕ∞) ≤ analyticOrderAt (soninHardyRep a c d v) w₀ := by
    have hne : analyticOrderAt (soninHardyRep a c d v) w₀ ≠ 0 := by
      intro h
      exact (hanaRep.analyticOrderAt_eq_zero.1 h) hvanRep
    exact Order.one_le_iff_ne_zero.2 hne
  obtain ⟨HQ, N, hHQ, hHQeq⟩ := exists_isHalfPlaneHardy_div_pow hHardy hanaRep hord
  refine ⟨HQ, N, hHQ, ?_⟩
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hshift : ∀ w : ℂ, 0 < w.re → w + 1 / 2 ≠ 0 := by
    intro w hw hzero
    have := congrArg Complex.re hzero
    simp at this
    linarith
  have hoff : ∀ w : ℂ, 0 < w.re → w ≠ 1 / 2 → w ≠ w₀ →
      HQ w = ((w - 1 / 2) / (w + 1 / 2)) * (((a : ℝ) : ℂ) ^ w * divShiftNF F ρ (w + 1 / 2)) := by
    intro w hw hne hnew
    have hne0 : w + 1 / 2 ≠ 0 := hshift w hw
    have hne1 : w + 1 / 2 ≠ 1 := by
      intro h
      exact hne (by linear_combination h)
    have hneρ : w + 1 / 2 ≠ ρ := by
      intro h
      exact hnew (by rw [hw₀]; linear_combination h)
    have hQ : divShiftNF F ρ (w + 1 / 2) = F (w + 1 / 2) / ((w + 1 / 2) - ρ) :=
      divShiftNF_eq hFmero (hFana _ hne0 hne1) hneρ
    have hsub : (w + 1 / 2) - ρ = w - w₀ := by rw [hw₀]; ring
    have hdiff : w - w₀ ≠ 0 := sub_ne_zero.2 hnew
    have hkey := hHQeq w hw hnew
    rw [pow_one] at hkey
    rw [hQ, hsub, soninHardyRep_eq a c d v hne0 (sub_ne_zero.2 hne)] at *
    field_simp at hkey ⊢
    linear_combination hkey
  intro w hw hne
  by_cases hnew : w = w₀
  · have hcontL : ContinuousAt HQ w := (hHQ.holo.differentiableAt (hopen.mem_nhds hw)).continuousAt
    have hne0 : w + 1 / 2 ≠ 0 := hshift w hw
    have hne1 : w + 1 / 2 ≠ 1 := by
      intro h
      exact hne (by linear_combination h)
    have hQana : AnalyticAt ℂ (divShiftNF F ρ) (w + 1 / 2) :=
      analyticAt_divShiftNF hFmero (hFana _ hne0 hne1) (hFana ρ hρ0 hρ1) hvan
    have hcontR : ContinuousAt
        (fun z : ℂ => ((z - 1 / 2) / (z + 1 / 2)) * (((a : ℝ) : ℂ) ^ z * divShiftNF F ρ (z + 1 / 2)))
        w := by
      have hc1 : ContinuousAt (fun z : ℂ => (z - 1 / 2) / (z + 1 / 2)) w :=
        ContinuousAt.div (by fun_prop) (by fun_prop) hne0
      have hc2 : ContinuousAt (fun z : ℂ => ((a : ℝ) : ℂ) ^ z) w :=
        (continuous_const_cpow_ofReal ha).continuousAt
      have hc3 : ContinuousAt (fun z : ℂ => divShiftNF F ρ (z + 1 / 2)) w := by
        have hsh : ContinuousAt (fun z : ℂ => z + (1 : ℂ) / 2) w := by fun_prop
        exact ContinuousAt.comp (g := divShiftNF F ρ) (f := fun z : ℂ => z + (1 : ℂ) / 2)
          (x := w) hQana.continuousAt hsh
      exact hc1.mul (hc2.mul hc3)
    have hopen2 : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1 / 2} := by
      have hset : {z : ℂ | 0 < z.re ∧ z ≠ 1 / 2} = {z : ℂ | 0 < z.re} ∩ {(1 : ℂ) / 2}ᶜ := by
        ext z
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
      rw [hset]
      exact hopen.inter isOpen_compl_singleton
    refine eq_of_eventuallyEq_punctured (ρ := w) (F := HQ)
      (H := fun z : ℂ => ((z - 1 / 2) / (z + 1 / 2))
        * (((a : ℝ) : ℂ) ^ z * divShiftNF F ρ (z + 1 / 2))) hcontL hcontR ?_
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (hopen2.mem_nhds ⟨hw, hne⟩)] with z hz hz'
    exact hoff z hz'.1 hz'.2 (by rw [← hnew]; exact hz)
  · exact hoff w hw hne hnew

end

end RHTower
