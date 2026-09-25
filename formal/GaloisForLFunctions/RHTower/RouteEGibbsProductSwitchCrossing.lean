import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Tactic

/-!
# Route E product-switch Gibbs crossing and Gamma--Hankel orientation

A product-preserving four-corner switch has two distinct physical responses.
The sum of one-body Gibbs weights changes sign exactly once as inverse scale varies.
The two-particle Gibbs weight, and hence the boundary additive Gamma--Hankel
kernel, have one fixed orientation at every positive scale. These are finite
source-side laws only; Möbius signs on product cells remain uncontrolled.
-/

open Set Filter Topology
namespace RHTower
noncomputable section

private def crossF (s t k β : ℝ) : ℝ :=
  1 + Real.exp (-k * β) - Real.exp (-s * β) - Real.exp (-t * β)

private def crossG (s t k β : ℝ) : ℝ :=
  s * Real.exp ((k-s) * β) + t * Real.exp ((k-t) * β) - k

private theorem crossF_deriv (s t k β : ℝ) :
    deriv (crossF s t k) β =
      Real.exp (-k * β) * crossG s t k β := by
  have he (a : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (-a * x))
      (-a * Real.exp (-a * β)) β := by
    change HasDerivAt (Real.exp ∘ fun x : ℝ => -a * x) _ β
    apply ((Real.hasDerivAt_exp _).comp β
      ((hasDerivAt_id β).const_mul (-a))).congr_deriv
    simp only [id_eq]
    ring
  have h : HasDerivAt (crossF s t k)
      (-k * Real.exp (-k * β) + s * Real.exp (-s * β) +
        t * Real.exp (-t * β)) β := by
    have h' := (((hasDerivAt_const β (1 : ℝ)).add (he k)).sub (he s)).sub (he t)
    change HasDerivAt (crossF s t k) _ β at h'
    exact h'.congr_deriv (by ring)
  rw [h.deriv]
  unfold crossG
  have hk_s : Real.exp (-k * β) * Real.exp ((k - s) * β) =
      Real.exp (-s * β) := by rw [← Real.exp_add]; congr 1; ring
  have hk_t : Real.exp (-k * β) * Real.exp ((k - t) * β) =
      Real.exp (-t * β) := by rw [← Real.exp_add]; congr 1; ring
  rw [← hk_s, ← hk_t]
  ring

private theorem crossG_strictMono
    {s t k : ℝ} (hs : 0 < s) (ht : 0 < t) (hk : s + t < k) :
    StrictMono (crossG s t k) := by
  intro x y hxy
  have hks : 0 < k - s := by linarith
  have hkt : 0 < k - t := by linarith
  have h1 : Real.exp ((k-s)*x) < Real.exp ((k-s)*y) :=
    Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hxy hks)
  have h2 : Real.exp ((k-t)*x) < Real.exp ((k-t)*y) :=
    Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hxy hkt)
  dsimp [crossG]
  have hs1 := mul_lt_mul_of_pos_left h1 hs
  have ht1 := mul_lt_mul_of_pos_left h2 ht
  linarith

private theorem crossF_zero (s t k : ℝ) : crossF s t k 0 = 0 := by
  simp [crossF]

private theorem crossG_zero (s t k : ℝ) : crossG s t k 0 = s+t-k := by
  simp [crossG]

private theorem crossF_negative_near_zero
    {s t k : ℝ} (hk : s+t < k) :
    ∃ β : ℝ, 0 < β ∧ crossF s t k β < 0 := by
  have hcont : Continuous (crossG s t k) := by
    unfold crossG
    fun_prop
  have hzero : crossG s t k 0 < 0 := by rw [crossG_zero]; linarith
  have hnear : {x : ℝ | crossG s t k x < 0} ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.eventually (eventually_lt_nhds hzero)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let β := ε / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβball : β ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hβ]
    dsimp [β]; linarith
  have hGneg : ∀ x ∈ Icc (0 : ℝ) β, crossG s t k x < 0 := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    have hβlt : β < ε := by dsimp [β]; linarith
    exact lt_of_le_of_lt hx.2 hβlt
  have hFcont : ContinuousOn (crossF s t k) (Icc (0 : ℝ) β) := by
    have hc : Continuous (crossF s t k) := by unfold crossF; fun_prop
    exact hc.continuousOn
  have hanti : StrictAntiOn (crossF s t k) (Icc (0 : ℝ) β) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 β) hFcont
    intro x hx
    rw [interior_Icc] at hx
    rw [crossF_deriv]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (hGneg x ⟨hx.1.le, hx.2.le⟩)
  refine ⟨β, hβ, ?_⟩
  have hlt := hanti (left_mem_Icc.mpr hβ.le) (right_mem_Icc.mpr hβ.le) hβ
  rw [crossF_zero] at hlt
  exact hlt

private theorem exp_neg_one_lt_half : Real.exp (-1) < (1 / 2 : ℝ) := by
  have h : (2 : ℝ) < Real.exp 1 := by
    linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  rw [Real.exp_neg]
  simpa [one_div] using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) h)

private theorem crossF_positive_witness
    {s t k : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ∀ L : ℝ, ∃ β > L, 0 < crossF s t k β := by
  intro L
  let β := max L 0 + 1 / s + 1 / t
  have hβL : L < β := by
    dsimp [β]
    have h1 : 0 < 1 / s := div_pos zero_lt_one hs
    have h2 : 0 < 1 / t := div_pos zero_lt_one ht
    have hmax := le_max_left L (0 : ℝ)
    linarith
  have hsβ : 1 < s * β := by
    dsimp [β]
    have hm : 0 ≤ max L (0 : ℝ) := le_max_right L 0
    have hq : 0 < s / t := div_pos hs ht
    field_simp [hs.ne', ht.ne']
    nlinarith [mul_nonneg hs.le hm]
  have htβ : 1 < t * β := by
    dsimp [β]
    have hm : 0 ≤ max L (0 : ℝ) := le_max_right L 0
    field_simp [hs.ne', ht.ne']
    nlinarith [mul_nonneg ht.le hm]
  have hes : Real.exp (-s * β) < (1 / 2 : ℝ) :=
    (Real.exp_lt_exp.mpr (by linarith : -s * β < -1)).trans exp_neg_one_lt_half
  have het : Real.exp (-t * β) < (1 / 2 : ℝ) :=
    (Real.exp_lt_exp.mpr (by linarith : -t * β < -1)).trans exp_neg_one_lt_half
  refine ⟨β, hβL, ?_⟩
  unfold crossF
  have he := Real.exp_pos (-k * β)
  linarith

private theorem crossF_positive_root_unique
    {s t k β γ : ℝ} (hs : 0 < s) (ht : 0 < t) (hk : s+t < k)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hfβ : crossF s t k β = 0) (hfγ : crossF s t k γ = 0) :
    β = γ := by
  have hcont : Continuous (crossF s t k) := by unfold crossF; fun_prop
  have hmono := crossG_strictMono hs ht hk
  have hrolle {a b : ℝ} (ha : a < b)
      (heq : crossF s t k a = crossF s t k b) :
      ∃ u ∈ Ioo a b, crossG s t k u = 0 := by
    obtain ⟨u, hu, hdu⟩ := exists_deriv_eq_zero ha hcont.continuousOn heq
    refine ⟨u, hu, ?_⟩
    rw [crossF_deriv] at hdu
    exact (mul_eq_zero.mp hdu).resolve_left (Real.exp_ne_zero _)
  rcases lt_trichotomy β γ with hlt | heq | hgt
  · obtain ⟨u, hu, hgu⟩ := hrolle hβ (by rw [crossF_zero, hfβ])
    obtain ⟨v, hv, hgv⟩ := hrolle hlt (by rw [hfβ, hfγ])
    have huv : u < v := lt_trans hu.2 hv.1
    have := hmono huv
    rw [hgu, hgv] at this
    exact (False.elim (lt_irrefl 0 this))
  · exact heq
  · obtain ⟨u, hu, hgu⟩ := hrolle hγ (by rw [crossF_zero, hfγ])
    obtain ⟨v, hv, hgv⟩ := hrolle hgt (by rw [hfγ, hfβ])
    have huv : u < v := lt_trans hu.2 hv.1
    have := hmono huv
    rw [hgu, hgv] at this
    exact (False.elim (lt_irrefl 0 this))

/-- A nondegenerate ordered product rectangle has exactly one positive Gibbs inverse scale
at which its four-corner weight defect vanishes. -/
private theorem crossF_unique_crossing
    {s t k : ℝ} (hs : 0 < s) (ht : 0 < t) (hk : s+t < k) :
    ∃! β : ℝ, 0 < β ∧ crossF s t k β = 0 := by
  obtain ⟨β₁, hβ₁, hneg⟩ := crossF_negative_near_zero hk
  obtain ⟨β₂, hβ₂, hpos⟩ := crossF_positive_witness hs ht β₁
  have hcont : Continuous (crossF s t k) := by unfold crossF; fun_prop
  have hmem : (0 : ℝ) ∈ Icc (crossF s t k β₁) (crossF s t k β₂) :=
    ⟨hneg.le, hpos.le⟩
  obtain ⟨β, hβ, hzero⟩ :=
    intermediate_value_Icc hβ₂.le hcont.continuousOn hmem
  refine ⟨β, ⟨lt_of_lt_of_le hβ₁ hβ.1, hzero⟩, ?_⟩
  intro γ hγ
  exact crossF_positive_root_unique hs ht hk hγ.1 (lt_of_lt_of_le hβ₁ hβ.1)
    hγ.2 hzero

/-- Four-corner Gibbs defect of one ordered, product-preserving rectangle. -/
def routeEGibbsProductSwitchDefect (g h u v β : ℝ) : ℝ :=
  Real.exp (-β * (g*u)) + Real.exp (-β * (h*v)) -
    Real.exp (-β * (g*v)) - Real.exp (-β * (h*u))

private theorem routeEGibbsProductSwitchDefect_factor
    (g h u v β : ℝ) :
    routeEGibbsProductSwitchDefect g h u v β =
      Real.exp (-β * (g*u)) *
        crossF (g*(v-u)) ((h-g)*u) (h*v-g*u) β := by
  have hhv : Real.exp (-β * (g*u)) *
      Real.exp (-(h*v-g*u)*β) = Real.exp (-β*(h*v)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hgv : Real.exp (-β * (g*u)) *
      Real.exp (-(g*(v-u))*β) = Real.exp (-β*(g*v)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hhu : Real.exp (-β * (g*u)) *
      Real.exp (-((h-g)*u)*β) = Real.exp (-β*(h*u)) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold routeEGibbsProductSwitchDefect crossF
  rw [← hhv, ← hgv, ← hhu]
  ring

/-- Every strict ordered product rectangle has a unique positive inverse-temperature crossing.
The pair product is fixed, but its physical Gibbs sum changes orientation once. -/
theorem routeEGibbsProductSwitch_unique_crossing
    {g h u v : ℝ} (hg : 0 < g) (hu : 0 < u)
    (hgh : g < h) (huv : u < v) :
    ∃! β : ℝ, 0 < β ∧ routeEGibbsProductSwitchDefect g h u v β = 0 := by
  have hs : 0 < g*(v-u) := mul_pos hg (sub_pos.mpr huv)
  have ht : 0 < (h-g)*u := mul_pos (sub_pos.mpr hgh) hu
  have hk : g*(v-u) + (h-g)*u < h*v-g*u := by nlinarith [mul_pos (sub_pos.mpr hgh) (sub_pos.mpr huv)]
  obtain ⟨β, hβ, huniq⟩ := crossF_unique_crossing hs ht hk
  refine ⟨β, ⟨hβ.1, ?_⟩, ?_⟩
  · rw [routeEGibbsProductSwitchDefect_factor]
    exact mul_eq_zero.mpr (Or.inr hβ.2)
  · intro γ hγ
    apply huniq
    refine ⟨hγ.1, ?_⟩
    rw [routeEGibbsProductSwitchDefect_factor] at hγ
    exact (mul_eq_zero.mp hγ.2).resolve_left (Real.exp_ne_zero _)

/-- The same literal product switch has both Gibbs-curvature signs at positive scales. -/
theorem routeEGibbsProductSwitch_both_signs
    {g h u v : ℝ} (hg : 0 < g) (hu : 0 < u)
    (hgh : g < h) (huv : u < v) :
    ∃ betaLow betaHigh : ℝ, 0 < betaLow ∧ betaLow < betaHigh ∧
      routeEGibbsProductSwitchDefect g h u v betaLow < 0 ∧
      0 < routeEGibbsProductSwitchDefect g h u v betaHigh := by
  have hs : 0 < g*(v-u) := mul_pos hg (sub_pos.mpr huv)
  have ht : 0 < (h-g)*u := mul_pos (sub_pos.mpr hgh) hu
  have hk : g*(v-u) + (h-g)*u < h*v-g*u := by
    nlinarith [mul_pos (sub_pos.mpr hgh) (sub_pos.mpr huv)]
  obtain ⟨betaLow, hbetaLow, hneg⟩ := crossF_negative_near_zero hk
  obtain ⟨betaHigh, hbetaHigh, hpos⟩ := crossF_positive_witness hs ht betaLow
  refine ⟨betaLow, betaHigh, hbetaLow, hbetaHigh, ?_, ?_⟩
  · rw [routeEGibbsProductSwitchDefect_factor]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
  · rw [routeEGibbsProductSwitchDefect_factor]
    exact mul_pos (Real.exp_pos _) hpos

/-- The same product-preserving switch has an exact signed displacement in the
additive coordinate used by the Gamma--Hankel kernel. -/
theorem routeEGibbsProductSwitch_additive_gap (g h u v : ℝ) :
    (g*u + h*v) - (g*v + h*u) = (h-g)*(v-u) := by ring

/-- Pair Gibbs weight is monotone at every positive scale, in sharp contrast to
the one-body four-corner defect, which crosses zero once. -/
theorem routeEGibbsProductSwitch_pairWeight_strict
    {g h u v β : ℝ} (hβ : 0 < β) (hgh : g < h) (huv : u < v) :
    Real.exp (-β * (g*u + h*v)) <
      Real.exp (-β * (g*v + h*u)) := by
  apply Real.exp_lt_exp.mpr
  have hgap : 0 < (g*u + h*v) - (g*v + h*u) := by
    rw [routeEGibbsProductSwitch_additive_gap]
    exact mul_pos (sub_pos.mpr hgh) (sub_pos.mpr huv)
  nlinarith [mul_pos hβ hgap]

/-- At boundary exponent one, the Gamma--Hankel kernel has a strict orientation
opposite to the outer-pair additive gap. -/
theorem routeEGammaHankelProductSwitch_inverse_gap
    {g h u v : ℝ} (hg : 0 < g) (hu : 0 < u)
    (hgh : g < h) (huv : u < v) :
    1 / (g*u + h*v) - 1 / (g*v + h*u) =
      -((h-g)*(v-u)) / ((g*u + h*v)*(g*v + h*u)) ∧
    1 / (g*u + h*v) < 1 / (g*v + h*u) := by
  have hh : 0 < h := hg.trans hgh
  have hv : 0 < v := hu.trans huv
  have hp : 0 < g*u + h*v := add_pos (mul_pos hg hu) (mul_pos hh hv)
  have hq : 0 < g*v + h*u := add_pos (mul_pos hg hv) (mul_pos hh hu)
  have hgap : g*v + h*u < g*u + h*v := by
    rw [← sub_pos, routeEGibbsProductSwitch_additive_gap]
    exact mul_pos (sub_pos.mpr hgh) (sub_pos.mpr huv)
  constructor
  · field_simp [hp.ne', hq.ne']
    ring
  · exact one_div_lt_one_div_of_lt hq hgap

end
end RHTower
