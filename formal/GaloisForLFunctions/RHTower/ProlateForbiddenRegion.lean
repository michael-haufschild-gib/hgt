import GaloisForLFunctions.RHTower.ProlateWKBIntegral

/-!
# Zero-free forbidden region for endpoint-normalized prolate modes

Beyond the positive turning point, the Sturm flux has one sign.  A solution normalized to value
one at the singular endpoint therefore cannot have a last zero there: after such a zero it would
be nonnegative, hence antitone, forcing the zero value to dominate the endpoint value one.

The stronger start point `sqrt ((1+s)/2)` also puts the exact WKB profile in its Riccati
subsolution region.  The lemmas below package all algebraic side conditions for that point.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set

open _root_.RHTower

/-- Start of the outer region where the unscaled WKB profile is a Riccati subsolution. -/
def prolateOuterStart (s : ℝ) : ℝ := Real.sqrt ((1 + s) / 2)

/-- An endpoint-normalized smooth prolate solution is strictly positive throughout every right
forbidden interval on which `chi + c²x²` is nonnegative. -/
theorem prolate_pos_on_right_forbidden_region
    {c chi y₀ : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = chi * Φ y)
    (hΦ1 : Φ 1 = 1) (hy₀0 : 0 ≤ y₀)
    (hQ : ∀ y ∈ Icc y₀ 1, 0 ≤ chi + c ^ 2 * y ^ 2) :
    ∀ y ∈ Icc y₀ 1, 0 < Φ y := by
  intro x hx
  by_contra hnot
  push Not at hnot
  have hcont : Continuous Φ := hsm.continuous
  have hzeroExists : ∃ z ∈ Icc x 1, Φ z = 0 := by
    have hzeroMem : (0 : ℝ) ∈ uIcc (Φ x) (Φ 1) := by
      rw [hΦ1, uIcc_of_le (by linarith : Φ x ≤ (1 : ℝ))]
      exact ⟨hnot, zero_le_one⟩
    obtain ⟨z, hz, hzeq⟩ :=
      (intermediate_value_uIcc hcont.continuousOn) hzeroMem
    refine ⟨z, ?_, hzeq⟩
    simpa only [uIcc_of_le hx.2] using hz
  let H : Set ℝ := Icc x 1 ∩ {t : ℝ | Φ t = 0}
  have hHcompact : IsCompact H :=
    isCompact_Icc.inter_right (isClosed_eq hcont continuous_const)
  have hHne : H.Nonempty := by
    obtain ⟨z, hz, hzeq⟩ := hzeroExists
    exact ⟨z, hz, hzeq⟩
  obtain ⟨z, hzH, hzGreatest⟩ := hHcompact.exists_isGreatest hHne
  have hzIcc : z ∈ Icc x 1 := hzH.1
  have hzzero : Φ z = 0 := hzH.2
  have hpos : ∀ t ∈ Icc z 1, 0 ≤ Φ t := by
    intro t ht
    by_contra htneg
    push Not at htneg
    have hzeroMem : (0 : ℝ) ∈ uIcc (Φ t) (Φ 1) := by
      rw [hΦ1, uIcc_of_le (by linarith : Φ t ≤ (1 : ℝ))]
      exact ⟨htneg.le, zero_le_one⟩
    obtain ⟨u, hu, hueq⟩ :=
      (intermediate_value_uIcc hcont.continuousOn) hzeroMem
    have huIcc : u ∈ Icc t 1 := by
      simpa only [uIcc_of_le ht.2] using hu
    have huH : u ∈ H := by
      exact ⟨⟨le_trans hzIcc.1 (le_trans ht.1 huIcc.1), huIcc.2⟩, hueq⟩
    have huz : u ≤ z := hzGreatest huH
    have hzt : z ≤ t := ht.1
    have htu : t ≤ u := huIcc.1
    have hut : u = t := le_antisymm (le_trans huz hzt) htu
    subst u
    have htz : t = z := le_antisymm (le_trans htu huz) hzt
    subst t
    linarith
  have hz0 : -1 < z := by
    have hx0 : 0 ≤ x := le_trans hy₀0 hx.1
    linarith [hzIcc.1]
  have hQz : ∀ t ∈ Icc z 1, 0 ≤ chi + c ^ 2 * t ^ 2 := by
    intro t ht
    exact hQ t ⟨le_trans hx.1 (le_trans hzIcc.1 ht.1), ht.2⟩
  have hanti := antitoneOn_of_turning hsm heig hz0 hpos hQz
  have hcompare := hanti (left_mem_Icc.mpr hzIcc.2) (right_mem_Icc.mpr hzIcc.2) hzIcc.2
  rw [hzzero, hΦ1] at hcompare
  norm_num at hcompare

/-- The outer WKB start lies in `[0,1)` for `0 ≤ s < 1`. -/
theorem prolateOuterStart_mem_Ico {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    prolateOuterStart s ∈ Ico (0 : ℝ) 1 := by
  have harg0 : 0 ≤ (1 + s) / 2 := by linarith
  have harg1 : (1 + s) / 2 < 1 := by linarith
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  have hsquare : Real.sqrt ((1 + s) / 2) ^ 2 = (1 + s) / 2 :=
    Real.sq_sqrt harg0
  dsimp only [prolateOuterStart]
  nlinarith [Real.sqrt_nonneg ((1 + s) / 2)]

/-- Every point beyond `prolateOuterStart s` is strictly beyond the radial turning point when
`0 ≤ s < 1`. -/
theorem radial_separation_lt_sq_of_outerStart_le
    {s y : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hy : prolateOuterStart s ≤ y) :
    s < y ^ 2 := by
  have hstart0 : 0 ≤ prolateOuterStart s := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := hstart0.trans hy
  have harg0 : 0 ≤ (1 + s) / 2 := by linarith
  have hstartSq : prolateOuterStart s ^ 2 = (1 + s) / 2 := by
    exact Real.sq_sqrt harg0
  have hsq : prolateOuterStart s ^ 2 ≤ y ^ 2 :=
    pow_le_pow_left₀ hstart0 hy 2
  rw [hstartSq] at hsq
  linarith

/-- The Riccati subsolution sign condition holds beyond `prolateOuterStart s`. -/
theorem outer_sign_of_prolateOuterStart_le
    {c s y : ℝ} (hs0 : 0 ≤ s)
    (hy : prolateOuterStart s ≤ y) :
    c ^ 2 * (1 - 2 * y ^ 2) ≤ -(s * c ^ 2) := by
  have hstart0 : 0 ≤ prolateOuterStart s := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := hstart0.trans hy
  have harg0 : 0 ≤ (1 + s) / 2 := by linarith
  have hstartSq : prolateOuterStart s ^ 2 = (1 + s) / 2 :=
    Real.sq_sqrt harg0
  have hsq : prolateOuterStart s ^ 2 ≤ y ^ 2 :=
    pow_le_pow_left₀ hstart0 hy 2
  rw [hstartSq] at hsq
  nlinarith [sq_nonneg c]

end GaloisForLFunctions.RHTower

end
