import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousMeasure
import GaloisForLFunctions.RHTower.LiClockPositiveEvenSeriesRatio
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
/-!
# Exact fixed-prefix endpoint comparison

The complete omitted product region has smaller difference support than both retained
endpoint rectangles. Their exact half-tilted masses give geometric convergence of
actual-to-contiguous normalized even-moment ratios and full Borel-kernel ratios.
The squared normalization scale is the sharp all-order and nonnegative-clock ceiling.
The real and complex Borel series retain every source moment and both even factorials.
-/


open Set MeasureTheory Filter

namespace RHTower
private lemma endpoint_integral_restriction_loss {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {P Q : Set α} (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (hPQ : P⊆Q) {f : α→ℝ} (hf : Integrable f (μ.restrict Q)) :
    (∫x,f x ∂μ.restrict Q)-(∫x,f x ∂μ.restrict P) = ∫x,f x ∂μ.restrict (Q\P) := by
  have hU : P∪(Q\P)=Q := by
    ext x
    constructor
    · intro hx
      rcases hx with hx|hx
      · exact hPQ hx
      · exact hx.1
    · intro hx
      by_cases hp : x∈P
      · exact Or.inl hp
      · exact Or.inr ⟨hx,hp⟩
  have hd : Disjoint P (Q\P) := disjoint_left.mpr (by
    intro x hx hy
    exact hy.2 hx)
  have hm : μ.restrict Q = μ.restrict P + μ.restrict (Q\P) := by
    calc
      _ = μ.restrict (P∪(Q\P)) := congrArg μ.restrict hU.symm
      _ = _ := Measure.restrict_union hd (hQ.diff hP)
  have hp := hf.mono_measure (Measure.restrict_mono_set μ hPQ)
  have hb : Integrable f (μ.restrict (Q\P)) := hf.mono_measure
    (Measure.restrict_mono_set μ (show Q\P⊆Q from sdiff_subset))
  rw [hm,integral_add_measure hp hb]
  ring

private lemma endpoint_raw_product_loss_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {P Q : Set α} (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (hPQ : P⊆Q) {f w : α→ℝ} {a : ℝ} (_ha : 0≤a)
    (hnn : ∀x,0≤w x) (hbound : ∀x∈Q\P, |f x|≤a)
    (hw : Integrable w (μ.restrict Q)) (j : ℕ)
    (hfj : Integrable (fun x=>f x^(2*j)*w x) (μ.restrict Q)) :
    0≤(∫x,f x^(2*j)*w x ∂μ.restrict Q)-(∫x,f x^(2*j)*w x ∂μ.restrict P) ∧
    (∫x,f x^(2*j)*w x ∂μ.restrict Q)-(∫x,f x^(2*j)*w x ∂μ.restrict P) ≤
      a^(2*j)*((∫x,w x ∂μ.restrict Q)-(∫x,w x ∂μ.restrict P)) := by
  rw [endpoint_integral_restriction_loss μ hP hQ hPQ hfj,
    endpoint_integral_restriction_loss μ hP hQ hPQ hw]
  have hp : ∀x,0≤f x^(2*j) := by
    intro x
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hlow : 0≤∫x,f x^(2*j)*w x ∂μ.restrict (Q\P) :=
    integral_nonneg (fun x=>mul_nonneg (hp x) (hnn x))
  have hbad_le := Measure.restrict_mono_set μ (show Q\P⊆Q from sdiff_subset)
  have hpoint : ∀ᵐx ∂μ.restrict (Q\P), f x^(2*j)*w x≤a^(2*j)*w x := by
    filter_upwards [ae_restrict_mem (hQ.diff hP)] with x hx
    have hpow := pow_le_pow_left₀ (abs_nonneg (f x)) (hbound x hx) (2*j)
    rw [← abs_pow,abs_of_nonneg (hp x)] at hpow
    exact mul_le_mul_of_nonneg_right hpow (hnn x)
  have hhi := integral_mono_ae (hfj.mono_measure hbad_le)
    ((hw.mono_measure hbad_le).const_mul (a^(2*j))) hpoint
  rw [integral_const_mul] at hhi
  exact ⟨hlow,hhi⟩
end RHTower


open Set MeasureTheory

namespace RHTower

private lemma endpoint_bad_difference_bound {S : Set ℝ} {L a : ℝ}
    (hfirst : Ioc 0 (Real.log 2)⊆S) (hlast : Ioc a L⊆S)
    (hgap : L-Real.log 2≤a) :
    ∀p∈(Ioc 0 L ×ˢ Ioc 0 L)\(S×ˢ S), |p.1-p.2|≤a := by
  have hmissing : ∀x∈Ioc 0 L, x∉S → Real.log 2<x ∧ x≤a := by
    intro x hx hnot
    constructor
    · by_contra hh
      exact hnot (hfirst ⟨hx.1,le_of_not_gt hh⟩)
    · by_contra hh
      exact hnot (hlast ⟨lt_of_not_ge hh,hx.2⟩)
  intro p hp
  rw [abs_le]
  by_cases h₁ : p.1∈S
  · have h₂ : p.2∉S := by intro h₂; exact hp.2 ⟨h₁,h₂⟩
    have hx := hmissing p.2 hp.1.2 h₂
    constructor <;> linarith [hp.1.1.1,hp.1.1.2]
  · have hx := hmissing p.1 hp.1.1 h₁
    constructor <;> linarith [hp.1.2.1,hp.1.2.2]

private lemma endpoint_rectangles_subset_actual {S : Set ℝ} {L a δ : ℝ}
    (hfirst : Ioc 0 (Real.log 2)⊆S) (hlast : Ioc a L⊆S)
    (hδ : δ≤Real.log 2) (hδlast : a≤L-δ) :
    (Ioc 0 δ ×ˢ Ioc (L-δ) L) ∪ (Ioc (L-δ) L ×ˢ Ioc 0 δ) ⊆ S×ˢ S := by
  have hlo : Ioc 0 δ⊆S := fun x hx=>hfirst ⟨hx.1,hx.2.trans hδ⟩
  have hhi : Ioc (L-δ) L⊆S := fun x hx=>hlast ⟨hδlast.trans_lt hx.1,hx.2⟩
  intro p hp
  rcases hp with hp|hp
  · exact ⟨hlo hp.1,hhi hp.2⟩
  · exact ⟨hhi hp.1,hlo hp.2⟩

private lemma endpoint_gap_rectangle_subset_bad {S : Set ℝ} {L : ℝ}
    (hgap : Disjoint S (Ioc (Real.log 2) (Real.log 3)))
    (hL : Real.log 3≤L) :
    Ioc (Real.log 2) (Real.log 3) ×ˢ Ioc 0 (Real.log 2/2) ⊆
      (Ioc 0 L ×ˢ Ioc 0 L)\(S×ˢ S) := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h₂₃ : Real.log 2<Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  intro p hp
  constructor
  · exact ⟨⟨h₂.trans hp.1.1,hp.1.2.trans hL⟩,
      ⟨hp.2.1, hp.2.2.trans (by linarith)⟩⟩
  · intro hh
    exact disjoint_left.mp hgap hh.1 hp.1

private lemma endpoint_gap_rectangle_measure_pos :
    0<(volume.prod volume) (Ioc (Real.log 2) (Real.log 3) ×ˢ Ioc 0 (Real.log 2/2)) := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  have h₂₃ : Real.log 2<Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Measure.prod_prod,Real.volume_Ioc,Real.volume_Ioc]
  have h₁ : 0<ENNReal.ofReal (Real.log 3-Real.log 2) :=
    ENNReal.ofReal_pos.mpr (sub_pos.mpr h₂₃)
  have h₂ : 0<ENNReal.ofReal (Real.log 2/2-0) := ENNReal.ofReal_pos.mpr (by linarith)
  positivity

end RHTower


open Set MeasureTheory


namespace RHTower
private lemma endpoint_rectangles_measure_le {L δ : ℝ} (hδ : 0 < δ)
    (hL : 2*δ < L) :
    (volume.restrict (Ioc 0 δ)).prod (volume.restrict (Ioc (L-δ) L))+
      (volume.restrict (Ioc (L-δ) L)).prod (volume.restrict (Ioc 0 δ)) ≤
      (volume.restrict (Ioc 0 L)).prod (volume.restrict (Ioc 0 L)) := by
  have hd : Disjoint (Ioc 0 δ ×ˢ Ioc (L-δ) L) (Ioc (L-δ) L ×ˢ Ioc 0 δ) := by
    apply disjoint_left.mpr
    intro p hp hq
    have h₁ := hp.1.2
    have h₂ := hq.1.1
    linarith
  have hs : (Ioc 0 δ ×ˢ Ioc (L-δ) L) ∪ (Ioc (L-δ) L ×ˢ Ioc 0 δ) ⊆
      Ioc 0 L ×ˢ Ioc 0 L := by
    intro p hp
    rcases hp with hp|hp
    · exact ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, ⟨by linarith [hp.2.1],hp.2.2⟩⟩
    · exact ⟨⟨by linarith [hp.1.1],hp.1.2⟩, ⟨hp.2.1,by linarith [hp.2.2]⟩⟩
  rw [Measure.prod_restrict,Measure.prod_restrict,Measure.prod_restrict,
    ← Measure.restrict_union hd (measurableSet_Ioc.prod measurableSet_Ioc)]
  exact Measure.restrict_mono hs le_rfl

private lemma endpoint_interval_weight {a b : ℝ} (hab : a ≤ b) :
    (∫x:ℝ,Real.exp (-x/2) ∂volume.restrict (Ioc a b)) =
      2*(Real.exp (-a/2)-Real.exp (-b/2)) := by
  rw [← intervalIntegral.integral_of_le hab]
  have he : (fun x:ℝ=>Real.exp (-x/2)) = (fun x:ℝ=>Real.exp ((-1/2:ℝ)*x)) := by
    funext x
    congr 1
    ring
  rw [he,intervalIntegral.integral_comp_mul_left (fun x:ℝ=>Real.exp x)
    (by norm_num : (-1/2:ℝ)≠0),integral_exp]
  norm_num only [smul_eq_mul, inv_neg, inv_div, inv_one]
  ring_nf

private lemma endpoint_rectangles_moment_lower_of_dom {L δ : ℝ}
    (hL : 2*δ < L) (j : ℕ) (μ : Measure (ℝ×ℝ))
    (hdom : (volume.restrict (Ioc 0 δ)).prod (volume.restrict (Ioc (L-δ) L))+
      (volume.restrict (Ioc (L-δ) L)).prod (volume.restrict (Ioc 0 δ)) ≤ μ)
    (hint : Integrable (fun p:ℝ×ℝ => (p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2))
      μ)
    (hwint : Integrable (fun p:ℝ×ℝ => Real.exp (-(p.1+p.2)/2)) μ) :
    (2*(∫x:ℝ,Real.exp (-x/2) ∂volume.restrict (Ioc 0 δ))*
      (∫x:ℝ,Real.exp (-x/2) ∂volume.restrict (Ioc (L-δ) L)))*(L-2*δ)^(2*j) ≤
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2) ∂μ) := by
  let μ₁ := (volume.restrict (Ioc 0 δ)).prod (volume.restrict (Ioc (L-δ) L))
  let μ₂ := (volume.restrict (Ioc (L-δ) L)).prod (volume.restrict (Ioc 0 δ))
  let w := fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2)
  let f := fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)*w p
  change μ₁+μ₂ ≤ μ at hdom
  have h₁ : μ₁ ≤ μ := (Measure.le_add_right (ν':=μ₂) (le_refl μ₁)).trans hdom
  have h₂ : μ₂ ≤ μ := (Measure.le_add_left (ν':=μ₁) (le_refl μ₂)).trans hdom
  have hp : ∀p:ℝ×ℝ, 0 ≤ (p.1-p.2)^(2*j) := by
    intro p
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have h₁s : ∀ᵐp ∂μ₁, p∈Ioc 0 δ ×ˢ Ioc (L-δ) L := by
    dsimp only [μ₁]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have h₂s : ∀ᵐp ∂μ₂, p∈Ioc (L-δ) L ×ˢ Ioc 0 δ := by
    dsimp only [μ₂]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  have hpoint₁ : ∀ᵐp ∂μ₁, (L-2*δ)^(2*j)*w p ≤ f p := by
    filter_upwards [h₁s] with p hp₁
    have ha : L-2*δ ≤ |p.1-p.2| := by
      have ht := neg_le_abs (p.1-p.2)
      linarith [hp₁.1.2,hp₁.2.1]
    have ht := pow_le_pow_left₀ (by linarith : 0≤L-2*δ) ha (2*j)
    rw [← abs_pow,abs_of_nonneg (hp p)] at ht
    exact mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
  have hpoint₂ : ∀ᵐp ∂μ₂, (L-2*δ)^(2*j)*w p ≤ f p := by
    filter_upwards [h₂s] with p hp₂
    have ha : L-2*δ ≤ |p.1-p.2| := by
      have ht := le_abs_self (p.1-p.2)
      linarith [hp₂.1.1,hp₂.2.2]
    have ht := pow_le_pow_left₀ (by linarith : 0≤L-2*δ) ha (2*j)
    rw [← abs_pow,abs_of_nonneg (hp p)] at ht
    exact mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
  have hw : Integrable w μ := hwint
  have hf : Integrable f μ := hint
  have he : (∫p,w p ∂(μ₁+μ₂)) =
      2*(∫x:ℝ,Real.exp (-x/2) ∂volume.restrict (Ioc 0 δ))*
        (∫x:ℝ,Real.exp (-x/2) ∂volume.restrict (Ioc (L-δ) L)) := by
    rw [integral_add_measure (hw.mono_measure h₁) (hw.mono_measure h₂)]
    have hwfac : w = fun p:ℝ×ℝ=>Real.exp (-p.1/2)*Real.exp (-p.2/2) := by
      funext p
      dsimp only [w]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hwfac]
    dsimp only [μ₁,μ₂]
    rw [integral_prod_mul (fun x:ℝ=>Real.exp (-x/2)) (fun x:ℝ=>Real.exp (-x/2)),
      integral_prod_mul (fun x:ℝ=>Real.exp (-x/2)) (fun x:ℝ=>Real.exp (-x/2))]
    ring
  calc
    _ = (∫p,(L-2*δ)^(2*j)*w p ∂(μ₁+μ₂)) := by
      rw [integral_const_mul,he]
      ring
    _ ≤ ∫p,f p ∂(μ₁+μ₂) := integral_mono_ae
      ((hw.mono_measure hdom).const_mul _) (hf.mono_measure hdom)
      (ae_add_measure_iff.mpr ⟨hpoint₁,hpoint₂⟩)
    _ ≤ ∫p,f p ∂μ := integral_mono_measure hdom
      (Filter.Eventually.of_forall (fun p=>mul_nonneg (hp p) (Real.exp_pos _).le)) hf

private lemma endpoint_rectangles_mass_eq {L ε : ℝ} (hε : 0 ≤ ε) :
    2*(∫x:ℝ,Real.exp (-x/2) ∂volume.restrict (Ioc 0 (ε/4)))*
      (∫x:ℝ,Real.exp (-x/2) ∂volume.restrict (Ioc (L-ε/4) L)) =
      8*Real.exp (-L/2)*(1-Real.exp (-ε/8))*(Real.exp (ε/8)-1) := by
  rw [endpoint_interval_weight (by linarith : (0:ℝ)≤ε/4),
    endpoint_interval_weight (by linarith : L-ε/4≤L)]
  have h₁ : -(L-ε/4)/2 = -L/2+ε/8 := by ring
  have h₂ : -(ε/4)/2 = -ε/8 := by ring
  rw [h₁,h₂,Real.exp_add]
  simp only [neg_zero,zero_div,Real.exp_zero]
  ring

private lemma endpoint_rectangles_mass_pos {L ε : ℝ} (hε : 0 < ε) :
    0 < 8*Real.exp (-L/2)*(1-Real.exp (-ε/8))*(Real.exp (ε/8)-1) := by
  have h₁ : Real.exp (-ε/8) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h₂ : 1 < Real.exp (ε/8) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (sub_pos.mpr h₁)) (sub_pos.mpr h₂)
end RHTower


namespace RHTower

private lemma normalized_raw_defect {ZA ZU IA IU : ℝ}
    (hZA : ZA≠0) (hZU : ZU≠0) :
    (ZU/ZA)^2*(IU/ZU^2)-IA/ZA^2 = (IU-IA)/ZA^2 := by
  field_simp

private lemma normalized_raw_mass_defect {ZA ZU : ℝ} (hZA : ZA≠0) :
    (ZU^2-ZA^2)/ZA^2 = (ZU/ZA)^2-1 := by
  field_simp

private lemma normalized_raw_ratio_defect {ZA ZU IA IU : ℝ}
    (hZA : ZA≠0) (hZU : ZU≠0) (hIU : IU≠0) :
    (ZU/ZA)^2-(IA/ZA^2)/(IU/ZU^2) = (ZU/ZA)^2*(IU-IA)/IU := by
  field_simp

private lemma normalized_raw_defect_ceiling {ZA ZU IA IU a : ℝ} {n : ℕ}
    (hZA : ZA≠0) (hZU : ZU≠0) (hraw : IU-IA ≤ (ZU^2-ZA^2)*a^n) :
    (ZU/ZA)^2*(IU/ZU^2)-IA/ZA^2 ≤ ((ZU/ZA)^2-1)*a^n := by
  rw [normalized_raw_defect hZA hZU]
  calc
    _ ≤ ((ZU^2-ZA^2)*a^n)/ZA^2 :=
      div_le_div_of_nonneg_right hraw (sq_nonneg _)
    _ = ((ZU/ZA)^2-1)*a^n := by
      rw [mul_div_right_comm,normalized_raw_mass_defect hZA]

private lemma normalized_raw_defect_pos {ZA ZU IA IU : ℝ}
    (hZA : 0<ZA) (hZU : 0<ZU) (hraw : 0<IU-IA) :
    0<(ZU/ZA)^2*(IU/ZU^2)-IA/ZA^2 := by
  rw [normalized_raw_defect hZA.ne' hZU.ne']
  exact div_pos hraw (sq_pos_of_pos hZA)

private lemma common_factor_coefficient_ratio {a b d : ℝ} (hb : b≠0) (hd : d≠0) :
    (a/d)/(b/d) = a/b := by
  field_simp

private lemma common_factor_comparison {a b K d : ℝ} (hd : 0<d) :
    a/d≤K*(b/d) ↔ a≤K*b := by
  rw [← mul_div_assoc,div_le_div_iff_of_pos_right hd]

end RHTower


open Filter Set MeasureTheory
open scoped Topology


namespace RHTower

private lemma raw_defect_ratio_bound {κ D E a b I : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hD : 0 ≤ D) (hE : 0 < E) (ha : 0 ≤ a) (hb : 0 < b)
    (hI : 0 < I) {d : ℝ} (_hd : 0 ≤ d) (hupper : d ≤ D*a^n)
    (hlower : E*b^n ≤ I) :
    κ*d/I ≤ (κ*D/E)*(a/b)^n := by
  have hEb : 0 < E*b^n := mul_pos hE (pow_pos hb _)
  calc
    κ*d/I ≤ κ*(D*a^n)/I := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hκ) hI.le
    _ ≤ κ*(D*a^n)/(E*b^n) := by
      exact div_le_div_of_nonneg_left (mul_nonneg hκ (mul_nonneg hD (pow_nonneg ha _))) hEb hlower
    _ = (κ*D/E)*(a/b)^n := by
      rw [div_pow]
      field_simp

private lemma endpoint_geometric_limit {qA qU : ℕ → ℝ} {κ C ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hlo : ∀ j, 0 ≤ κ-qA j/qU j)
    (hhi : ∀ j, κ-qA j/qU j ≤ C*ρ^(2*j)) :
    Tendsto (fun j => qA j/qU j) atTop (𝓝 κ) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have heven : Tendsto (fun j : ℕ => ρ^(2*j)) atTop (𝓝 (0:ℝ)) := by
    simpa only [pow_mul, mul_comm, zero_pow (by decide : 2≠0)] using hp.pow 2
  have hdef : Tendsto (fun j => κ-qA j/qU j) atTop (𝓝 (0:ℝ)) :=
    squeeze_zero' (Eventually.of_forall hlo) (Eventually.of_forall hhi)
      (by simpa only [mul_zero] using heven.const_mul C)
  have h := (tendsto_const_nhds (x:=κ)).sub hdef
  simpa only [sub_sub_cancel, sub_zero] using h

end RHTower

namespace RHTower
noncomputable section

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ComplexConjugate

/-- The support bound of the complete omitted product region. -/
def liClockPairedEtaPartitionEndpointInnerRadius (N : ℕ) : ℝ :=
  Real.log (2*(N:ℝ)-1)

/-- The separation retained by both endpoint rectangles. -/
def liClockPairedEtaPartitionEndpointOuterRadius (N : ℕ) : ℝ :=
  (Real.log (2*(N:ℝ))+liClockPairedEtaPartitionEndpointInnerRadius N)/2

/-- The exact raw half-tilted mass of both mirrored endpoint rectangles. -/
def liClockPairedEtaPartitionEndpointRawMass (N : ℕ) : ℝ :=
  let L := Real.log (2*(N:ℝ))
  let ε := L-liClockPairedEtaPartitionEndpointInnerRadius N
  8*Real.exp (-L/2)*(1-Real.exp (-ε/8))*(Real.exp (ε/8)-1)

/-- The strict endpoint support-radius ratio for each nonempty prefix. -/
def liClockPairedEtaPartitionEndpointRatioDecay (N : ℕ) : ℝ :=
  liClockPairedEtaPartitionEndpointInnerRadius N/liClockPairedEtaPartitionEndpointOuterRadius N

/-- The full source-dependent geometric moment-error coefficient. -/
def liClockPairedEtaPartitionEndpointRatioErrorScale (N : ℕ) : ℝ :=
  let ZA := liClockPairedEtaPartitionNormalizer N
  let ZU := liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))
  (ZU/ZA)^2*(ZU^2-ZA^2)/liClockPairedEtaPartitionEndpointRawMass N

private abbrev epL (N : ℕ) := Real.log (2*(N:ℝ))
private abbrev epA (N : ℕ) := liClockPairedEtaPartitionEndpointInnerRadius N
private abbrev epB (N : ℕ) := liClockPairedEtaPartitionEndpointOuterRadius N
private abbrev epε (N : ℕ) := epL N-epA N
private abbrev epZA (N : ℕ) := liClockPairedEtaPartitionNormalizer N
private abbrev epZU (N : ℕ) := liClockPairedEtaContiguousPartitionNormalizer (epL N)
private abbrev epκ (N : ℕ) := (epZU N/epZA N)^2
private abbrev epS (N : ℕ) := liClockPairedEtaPartitionLogSupport N
private abbrev epU (N : ℕ) := Ioc 0 (epL N)

private lemma ep_length_pos {N : ℕ} (hN : 0<N) : 0<epL N := by
  apply Real.log_pos
  have hn : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  linarith

private lemma ep_inner_nonneg {N : ℕ} (hN : 0<N) : 0≤epA N := by
  apply Real.log_nonneg
  have hn : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  linarith

private lemma ep_inner_pos {N : ℕ} (hN : 2≤N) : 0<epA N := by
  apply Real.log_pos
  have hn : (2:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  linarith

private lemma ep_inner_lt_length {N : ℕ} (hN : 0<N) : epA N<epL N := by
  apply Real.log_lt_log
  · have hn : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
    linarith
  · linarith

private lemma ep_width_pos {N : ℕ} (hN : 0<N) : 0<epε N :=
  sub_pos.mpr (ep_inner_lt_length hN)

private lemma ep_width_le_length {N : ℕ} (hN : 0<N) : epε N≤epL N := by
  have := ep_inner_nonneg hN
  dsimp only [epε]
  linarith

private lemma ep_width_eq {N : ℕ} (hN : 0<N) :
    epε N=Real.log (2*(N:ℝ)/(2*(N:ℝ)-1)) := by
  have hn : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  exact (Real.log_div (by linarith) (by linarith)).symm

private lemma ep_width_le_log_two {N : ℕ} (hN : 0<N) : epε N≤Real.log 2 := by
  rw [ep_width_eq hN]
  have hn : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  have hden : 0<2*(N:ℝ)-1 := by linarith
  apply Real.log_le_log (div_pos (by linarith) hden)
  apply (div_le_iff₀ hden).2
  linarith

private lemma ep_outer_eq (N : ℕ) : epB N=epL N-epε N/2 := by
  dsimp only [epB,liClockPairedEtaPartitionEndpointOuterRadius,epε]
  ring

private lemma ep_outer_pos {N : ℕ} (hN : 0<N) : 0<epB N := by
  have hl := ep_length_pos hN
  have ha := ep_inner_nonneg hN
  dsimp only [epB,liClockPairedEtaPartitionEndpointOuterRadius]
  linarith

private lemma ep_first_interval_subset {N : ℕ} (hN : 0<N) :
    Ioc 0 (Real.log 2)⊆epS N := by
  intro x hx
  simp only [epS,liClockPairedEtaPartitionLogSupport,mem_iUnion]
  refine ⟨0,Finset.mem_range.mpr hN,?_⟩
  simpa only [Nat.cast_zero,mul_zero,zero_add,Real.log_one] using hx

private lemma ep_last_interval_subset {N : ℕ} (hN : 0<N) : Ioc (epA N) (epL N)⊆epS N := by
  have hn : (N-1:ℕ)+1=N := by omega
  have hc : ((N-1:ℕ):ℝ)+1=(N:ℝ) := by exact_mod_cast hn
  have hlo : 2*((N-1:ℕ):ℝ)+1=2*(N:ℝ)-1 := by linarith
  have hhi : 2*((N-1:ℕ):ℝ)+2=2*(N:ℝ) := by linarith
  intro x hx
  simp only [epS,liClockPairedEtaPartitionLogSupport,mem_iUnion]
  refine ⟨N-1,Finset.mem_range.mpr (by omega),?_⟩
  simpa only [hlo,hhi,epA,liClockPairedEtaPartitionEndpointInnerRadius,epL] using hx

private lemma ep_missing_gap_disjoint (N : ℕ) :
    Disjoint (epS N) (Ioc (Real.log 2) (Real.log 3)) := by
  apply disjoint_left.mpr
  intro u hu hg
  simp only [epS,liClockPairedEtaPartitionLogSupport,mem_iUnion] at hu
  obtain ⟨n,hn,hu⟩ := hu
  by_cases hn0 : n=0
  · subst n
    simp only [Nat.cast_zero,mul_zero,zero_add,Real.log_one] at hu
    linarith [hu.2,hg.1]
  · have hn1 : (1:ℝ)≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
    have hl : Real.log 3≤Real.log (2*(n:ℝ)+1) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [hu.1,hg.2]

end
end RHTower

namespace RHTower
noncomputable section

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ComplexConjugate

private abbrev epRawA (N j : ℕ) :=
  ∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
    ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)
private abbrev epRawU (N j : ℕ) :=
  ∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
    ∂(liClockPairedEtaContiguousLogMeasure (epL N)).prod
      (liClockPairedEtaContiguousLogMeasure (epL N))
private abbrev epμ : Measure (ℝ×ℝ) := volume.prod volume

private lemma ep_square_subset (N : ℕ) : epS N×ˢ epS N⊆epU N×ˢ epU N := by
  intro p hp
  exact ⟨liClockPairedEtaPartitionLogSupport_subset_Ioc N hp.1,
    liClockPairedEtaPartitionLogSupport_subset_Ioc N hp.2⟩

private lemma ep_raw_A_restrict (N j : ℕ) : epRawA N j =
    ∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2) ∂epμ.restrict (epS N×ˢ epS N) := by
  dsimp only [epRawA]
  rw [pairedEtaFiniteLogMeasure_eq_restrict_union,Measure.prod_restrict]

private lemma ep_raw_U_restrict (N j : ℕ) : epRawU N j =
    ∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2) ∂epμ.restrict (epU N×ˢ epU N) := by
  dsimp only [epRawU]
  rw [liClockPairedEtaContiguousLogMeasure,Measure.prod_restrict]

private lemma ep_raw_integrable_U (N j : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2))
      ((liClockPairedEtaContiguousLogMeasure (epL N)).prod (liClockPairedEtaContiguousLogMeasure (epL N))) :=
  integrable_liClockPairedEtaContiguousRawEvenMoment _ _

private lemma ep_raw_integrable_A (N j : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2))
      ((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) :=
  (ep_raw_integrable_U N j).mono_measure (pairedEtaFiniteLogMeasure_prod_le_contiguous N)

private lemma ep_raw_integrable_U_restrict (N j : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2))
      (epμ.restrict (epU N×ˢ epU N)) := by
  simpa only [liClockPairedEtaContiguousLogMeasure,Measure.prod_restrict] using ep_raw_integrable_U N j

private lemma ep_weight_integrable_U_restrict (N : ℕ) :
    Integrable (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2)) (epμ.restrict (epU N×ˢ epU N)) := by
  simpa only [Nat.mul_zero,pow_zero,one_mul] using ep_raw_integrable_U_restrict N 0

private lemma ep_raw_A_eq {N : ℕ} (hN : 0<N) (j : ℕ) :
    epRawA N j=(epZA N)^2*liClockPairedEtaSymmetrizedEvenMoment N j := by
  have h := liClockPairedEtaSymmetrizedEvenMoment_eq_double_integral N j
  have hz := (liClockPairedEtaPartitionNormalizer_pos hN).ne'
  have heq := (eq_div_iff (pow_ne_zero 2 hz)).mp h
  calc
    _ = liClockPairedEtaSymmetrizedEvenMoment N j*(epZA N)^2 := heq.symm
    _ = _ := mul_comm _ _

private lemma ep_raw_U_eq {N : ℕ} (hN : 0<N) (j : ℕ) :
    epRawU N j=(epZU N)^2*liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j := by
  have h := liClockPairedEtaContiguousSymmetrizedEvenMoment_eq_double_integral (epL N) j
  have hz := (liClockPairedEtaContiguousPartitionNormalizer_pos (ep_length_pos hN)).ne'
  have heq := (eq_div_iff (pow_ne_zero 2 hz)).mp h
  calc
    _ = liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j*(epZU N)^2 := heq.symm
    _ = _ := mul_comm _ _

private lemma ep_raw_A_zero {N : ℕ} (hN : 0<N) : epRawA N 0=(epZA N)^2 := by
  rw [ep_raw_A_eq hN,liClockPairedEtaSymmetrizedEvenMoment_zero hN,mul_one]

private lemma ep_raw_U_zero {N : ℕ} (hN : 0<N) : epRawU N 0=(epZU N)^2 := by
  rw [ep_raw_U_eq hN,liClockPairedEtaContiguousSymmetrizedEvenMoment_zero (ep_length_pos hN),mul_one]

private lemma ep_raw_loss_bound {N : ℕ} (hN : 0<N) (j : ℕ) :
    0≤epRawU N j-epRawA N j ∧
    epRawU N j-epRawA N j ≤ ((epZU N)^2-(epZA N)^2)*(epA N)^(2*j) := by
  have hs := measurableSet_liClockPairedEtaPartitionLogSupport N
  have hgap : epL N-Real.log 2≤epA N := by
    have := ep_width_le_log_two hN
    dsimp only [epε] at this
    linarith
  have hb := endpoint_raw_product_loss_bound epμ (hs.prod hs)
    (measurableSet_Ioc.prod measurableSet_Ioc) (ep_square_subset N) (ep_inner_nonneg hN)
    (fun p:ℝ×ℝ=>(Real.exp_pos (-(p.1+p.2)/2)).le)
    (endpoint_bad_difference_bound (ep_first_interval_subset hN) (ep_last_interval_subset hN) hgap)
    (ep_weight_integrable_U_restrict N) j (ep_raw_integrable_U_restrict N j)
  have hresult : 0≤epRawU N j-epRawA N j ∧
      epRawU N j-epRawA N j≤(epA N)^(2*j)*(epRawU N 0-epRawA N 0) := by
    simpa only [epRawU,epRawA,liClockPairedEtaContiguousLogMeasure,
      pairedEtaFiniteLogMeasure_eq_restrict_union,Measure.prod_restrict,Nat.mul_zero,pow_zero,one_mul] using hb
  rw [ep_raw_U_zero hN,ep_raw_A_zero hN] at hresult
  simpa only [mul_comm] using hresult

private lemma ep_raw_loss_pos {N : ℕ} (hN : 2≤N) (j : ℕ) :
    0<epRawU N j-epRawA N j := by
  let bad := (epU N×ˢ epU N)\(epS N×ˢ epS N)
  let rect := Ioc (Real.log 2) (Real.log 3) ×ˢ Ioc 0 (Real.log 2/2)
  let f := fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
  have hs := measurableSet_liClockPairedEtaPartitionLogSupport N
  have hN0 : 0<N := by omega
  have hL : Real.log 3≤epL N := by
    apply Real.log_le_log (by norm_num)
    have hn : (2:ℝ)≤(N:ℝ) := by exact_mod_cast hN
    linarith
  have hrect : rect⊆bad := endpoint_gap_rectangle_subset_bad (ep_missing_gap_disjoint N) hL
  have hrpos : 0<(epμ.restrict bad) rect := by
    rw [Measure.restrict_apply (measurableSet_Ioc.prod measurableSet_Ioc),inter_eq_left.mpr hrect]
    exact endpoint_gap_rectangle_measure_pos
  have hfs : rect⊆Function.support f := by
    intro p hp
    have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
    have hd : p.1-p.2≠0 := by linarith [hp.1.1,hp.2.2]
    exact mul_ne_zero (pow_ne_zero _ hd) (Real.exp_pos _).ne'
  have hfi : Integrable f (epμ.restrict bad) :=
    (ep_raw_integrable_U_restrict N j).mono_measure
      (Measure.restrict_mono_set epμ (show bad⊆epU N×ˢ epU N from sdiff_subset))
  have hpos : 0<∫p,f p ∂epμ.restrict bad :=
    (integral_pos_iff_support_of_nonneg (fun p=>by
      apply mul_nonneg _ (Real.exp_pos _).le
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) j) hfi).2 (hrpos.trans_le (measure_mono hfs))
  have heq : epRawU N j-epRawA N j = ∫p,f p ∂epμ.restrict bad := by
    rw [ep_raw_U_restrict,ep_raw_A_restrict]
    exact endpoint_integral_restriction_loss epμ (hs.prod hs)
      (measurableSet_Ioc.prod measurableSet_Ioc) (ep_square_subset N) (ep_raw_integrable_U_restrict N j)
  exact heq ▸ hpos

end
end RHTower

namespace RHTower
noncomputable section

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ComplexConjugate

private lemma ep_rectangles_disjoint {L δ : ℝ} (hL : 2*δ<L) :
    Disjoint (Ioc 0 δ×ˢ Ioc (L-δ) L) (Ioc (L-δ) L×ˢ Ioc 0 δ) := by
  apply disjoint_left.mpr
  intro p hp hq
  linarith [hp.1.2,hq.1.1]

private lemma ep_rectangles_dom_actual {N : ℕ} (hN : 0<N) :
    (volume.restrict (Ioc 0 (epε N/4))).prod (volume.restrict (Ioc (epL N-epε N/4) (epL N)))+
      (volume.restrict (Ioc (epL N-epε N/4) (epL N))).prod (volume.restrict (Ioc 0 (epε N/4))) ≤
      (pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N) := by
  have he := ep_width_pos hN
  have hel := ep_width_le_length hN
  have hL := ep_length_pos hN
  have hδL : 2*(epε N/4)<epL N := by linarith
  have hδ₂ : epε N/4≤Real.log 2 := by linarith [ep_width_le_log_two hN]
  have hδa : epA N≤epL N-epε N/4 := by dsimp only [epε] at he ⊢; linarith
  have hsub := endpoint_rectangles_subset_actual (ep_first_interval_subset hN)
    (ep_last_interval_subset hN) hδ₂ hδa
  rw [pairedEtaFiniteLogMeasure_eq_restrict_union,Measure.prod_restrict,Measure.prod_restrict,
    Measure.prod_restrict,← Measure.restrict_union (ep_rectangles_disjoint hδL)
      (measurableSet_Ioc.prod measurableSet_Ioc)]
  exact Measure.restrict_mono hsub le_rfl

private lemma ep_rectangles_lower {N : ℕ} (hN : 0<N) (j : ℕ) (μ : Measure (ℝ×ℝ))
    (hdom : (volume.restrict (Ioc 0 (epε N/4))).prod
        (volume.restrict (Ioc (epL N-epε N/4) (epL N)))+
      (volume.restrict (Ioc (epL N-epε N/4) (epL N))).prod
        (volume.restrict (Ioc 0 (epε N/4)))≤μ)
    (hint : Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)) μ)
    (hw : Integrable (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2)) μ) :
    liClockPairedEtaPartitionEndpointRawMass N*(epB N)^(2*j)≤
      ∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2) ∂μ := by
  have hδL : 2*(epε N/4)<epL N := by
    have := ep_width_le_length hN
    have := ep_length_pos hN
    linarith
  have h := endpoint_rectangles_moment_lower_of_dom hδL j μ hdom hint hw
  rw [endpoint_rectangles_mass_eq (ep_width_pos hN).le] at h
  have he : epL N-2*(epε N/4)=epB N := by rw [ep_outer_eq]; ring
  rw [he] at h
  exact h

private lemma ep_raw_lower_actual {N : ℕ} (hN : 0<N) (j : ℕ) :
    liClockPairedEtaPartitionEndpointRawMass N*(epB N)^(2*j)≤epRawA N j := by
  apply ep_rectangles_lower hN j _ (ep_rectangles_dom_actual hN) (ep_raw_integrable_A N j)
  simpa only [Nat.mul_zero,pow_zero,one_mul] using ep_raw_integrable_A N 0

private lemma ep_raw_lower_contiguous {N : ℕ} (hN : 0<N) (j : ℕ) :
    liClockPairedEtaPartitionEndpointRawMass N*(epB N)^(2*j)≤epRawU N j := by
  have hδ : 0<epε N/4 := by linarith [ep_width_pos hN]
  have hδL : 2*(epε N/4)<epL N := by
    have := ep_width_le_length hN
    have := ep_length_pos hN
    linarith
  refine ep_rectangles_lower hN j
    ((liClockPairedEtaContiguousLogMeasure (epL N)).prod (liClockPairedEtaContiguousLogMeasure (epL N)))
    ?_ (ep_raw_integrable_U N j) ?_
  · convert endpoint_rectangles_measure_le hδ hδL using 1
    rfl
  · simpa only [Nat.mul_zero,pow_zero,one_mul] using ep_raw_integrable_U N 0

theorem liClockPairedEtaPartitionEndpointRawMass_pos {N : ℕ} (hN : 0<N) :
    0<liClockPairedEtaPartitionEndpointRawMass N := endpoint_rectangles_mass_pos (ep_width_pos hN)

theorem liClockPairedEtaPartitionEndpointRatioDecay_nonneg_lt_one {N : ℕ} (hN : 0<N) :
    0≤liClockPairedEtaPartitionEndpointRatioDecay N ∧ liClockPairedEtaPartitionEndpointRatioDecay N<1 := by
  have hb := ep_outer_pos hN
  constructor
  · exact div_nonneg (ep_inner_nonneg hN) hb.le
  · apply (div_lt_iff₀ hb).2
    simp only [one_mul]
    have := ep_inner_lt_length hN
    dsimp only [epB,liClockPairedEtaPartitionEndpointOuterRadius]
    linarith

theorem liClockPairedEtaPartitionEndpointRatioErrorScale_nonneg {N : ℕ} (hN : 0<N) :
    0≤liClockPairedEtaPartitionEndpointRatioErrorScale N := by
  have hA := liClockPairedEtaPartitionNormalizer_pos hN
  have hAU := liClockPairedEtaPartitionNormalizer_le_contiguous N
  have hD : 0≤(epZU N)^2-(epZA N)^2 := by nlinarith
  exact div_nonneg (mul_nonneg (sq_nonneg _) hD) (liClockPairedEtaPartitionEndpointRawMass_pos hN).le

/-- Both mirrored endpoint rectangles remain in the complete actual product source. -/
theorem liClockPairedEtaPartitionEndpoint_evenMoment_lower {N : ℕ} (hN : 0<N) (j : ℕ) :
    liClockPairedEtaPartitionEndpointRawMass N*liClockPairedEtaPartitionEndpointOuterRadius N^(2*j)≤
      liClockPairedEtaPartitionNormalizer N^2*liClockPairedEtaSymmetrizedEvenMoment N j := by
  rw [← ep_raw_A_eq hN]
  exact ep_raw_lower_actual hN j

theorem liClockPairedEtaContiguousEndpoint_evenMoment_lower {N : ℕ} (hN : 0<N) (j : ℕ) :
    liClockPairedEtaPartitionEndpointRawMass N*liClockPairedEtaPartitionEndpointOuterRadius N^(2*j)≤
      liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2*
        liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j := by
  rw [← ep_raw_U_eq hN]
  exact ep_raw_lower_contiguous hN j

private lemma ep_moment_defect_eq {N : ℕ} (hN : 0<N) (j : ℕ) :
    epκ N*liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j-
      liClockPairedEtaSymmetrizedEvenMoment N j = (epRawU N j-epRawA N j)/(epZA N)^2 := by
  rw [liClockPairedEtaContiguousSymmetrizedEvenMoment_eq_double_integral,
    liClockPairedEtaSymmetrizedEvenMoment_eq_double_integral]
  exact normalized_raw_defect (liClockPairedEtaPartitionNormalizer_pos hN).ne'
    (liClockPairedEtaContiguousPartitionNormalizer_pos (ep_length_pos hN)).ne'

/-- Every source degree has strictly positive raw loss, with the complete smaller-support ceiling. -/
theorem liClockPairedEtaPartitionEndpoint_evenMoment_defect {N : ℕ} (hN : 2≤N) (j : ℕ) :
    let κ := (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
      liClockPairedEtaPartitionNormalizer N)^2
    0<κ*liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j-
      liClockPairedEtaSymmetrizedEvenMoment N j ∧
    κ*liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j-
      liClockPairedEtaSymmetrizedEvenMoment N j ≤
      (κ-1)*liClockPairedEtaPartitionEndpointInnerRadius N^(2*j) := by
  have hN0 : 0<N := by omega
  dsimp only
  constructor
  · rw [ep_moment_defect_eq hN0]
    exact div_pos (ep_raw_loss_pos hN j) (sq_pos_of_pos (liClockPairedEtaPartitionNormalizer_pos hN0))
  · rw [liClockPairedEtaContiguousSymmetrizedEvenMoment_eq_double_integral,
      liClockPairedEtaSymmetrizedEvenMoment_eq_double_integral]
    exact normalized_raw_defect_ceiling (liClockPairedEtaPartitionNormalizer_pos hN0).ne'
      (liClockPairedEtaContiguousPartitionNormalizer_pos (ep_length_pos hN0)).ne'
      (ep_raw_loss_bound hN0 j).2

private lemma ep_moment_ratio_error_bound {N : ℕ} (hN : 0<N) (j : ℕ) :
    0≤epκ N-liClockPairedEtaSymmetrizedEvenMoment N j/
      liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j ∧
    epκ N-liClockPairedEtaSymmetrizedEvenMoment N j/
      liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j≤
      liClockPairedEtaPartitionEndpointRatioErrorScale N*
        liClockPairedEtaPartitionEndpointRatioDecay N^(2*j) := by
  have hA := liClockPairedEtaPartitionNormalizer_pos hN
  have hU := liClockPairedEtaContiguousPartitionNormalizer_pos (ep_length_pos hN)
  have hI : 0<epRawU N j := by
    rw [ep_raw_U_eq hN]
    exact mul_pos (sq_pos_of_pos hU) (liClockPairedEtaContiguousSymmetrizedEvenMoment_pos (ep_length_pos hN) j)
  have hD : 0≤(epZU N)^2-(epZA N)^2 := by
    have := liClockPairedEtaPartitionNormalizer_le_contiguous N
    nlinarith
  rw [liClockPairedEtaSymmetrizedEvenMoment_eq_double_integral,
    liClockPairedEtaContiguousSymmetrizedEvenMoment_eq_double_integral,
    normalized_raw_ratio_defect hA.ne' hU.ne' hI.ne']
  constructor
  · exact div_nonneg (mul_nonneg (sq_nonneg _) (ep_raw_loss_bound hN j).1) hI.le
  · exact raw_defect_ratio_bound (sq_nonneg _) hD
      (liClockPairedEtaPartitionEndpointRawMass_pos hN) (ep_inner_nonneg hN) (ep_outer_pos hN)
      hI (ep_raw_loss_bound hN j).1 (ep_raw_loss_bound hN j).2 (ep_raw_lower_contiguous hN j)

end
end RHTower

namespace RHTower
noncomputable section

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ComplexConjugate

private lemma ep_scale_one_lt {N : ℕ} (hN : 2≤N) : 1<epκ N := by
  have hN0 : 0<N := by omega
  have hA := liClockPairedEtaPartitionNormalizer_pos hN0
  have hAU := liClockPairedEtaPartitionNormalizer_lt_contiguous hN
  have hq : 1<epZU N/epZA N := (lt_div_iff₀ hA).2 (by simpa only [one_mul] using hAU)
  nlinarith [sq_nonneg (epZU N/epZA N-1)]

theorem liClockPairedEtaPartitionEndpointRawMass_eq {N : ℕ} (hN : 0<N) :
    let L := Real.log (2*(N:ℝ))
    let ε := Real.log (2*(N:ℝ)/(2*(N:ℝ)-1))
    liClockPairedEtaPartitionEndpointRawMass N =
      8*Real.exp (-L/2)*(1-Real.exp (-ε/8))*(Real.exp (ε/8)-1) := by
  dsimp only
  rw [← ep_width_eq hN]
  rfl

theorem liClockPairedEtaPartitionEndpointOuterRadius_eq {N : ℕ} (hN : 0<N) :
    liClockPairedEtaPartitionEndpointOuterRadius N = Real.log (2*(N:ℝ))-
      Real.log (2*(N:ℝ)/(2*(N:ℝ)-1))/2 := by
  rw [← ep_width_eq hN]
  exact ep_outer_eq N

/-- The complete fixed-prefix moment error has an explicit geometric decay bound. -/
theorem liClockPairedEtaPartitionEndpoint_evenMoment_ratio_error {N : ℕ} (hN : 2≤N) (j : ℕ) :
    let κ := (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
      liClockPairedEtaPartitionNormalizer N)^2
    0<κ-liClockPairedEtaSymmetrizedEvenMoment N j/
      liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j ∧
    κ-liClockPairedEtaSymmetrizedEvenMoment N j/
      liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j≤
      liClockPairedEtaPartitionEndpointRatioErrorScale N*
        liClockPairedEtaPartitionEndpointRatioDecay N^(2*j) := by
  have hN0 : 0<N := by omega
  dsimp only
  constructor
  · have hU := liClockPairedEtaContiguousSymmetrizedEvenMoment_pos (ep_length_pos hN0) j
    have he : epκ N-liClockPairedEtaSymmetrizedEvenMoment N j/
        liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j =
        (epκ N*liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j-
          liClockPairedEtaSymmetrizedEvenMoment N j)/
          liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j := by
      field_simp
    rw [he]
    exact div_pos (liClockPairedEtaPartitionEndpoint_evenMoment_defect hN j).1 hU
  · exact (ep_moment_ratio_error_bound hN0 j).2

/-- Every nonempty fixed prefix has the sharp complete moment-ratio limit. -/
theorem liClockPairedEtaPartitionEndpoint_evenMoment_ratio_tendsto {N : ℕ} (hN : 0<N) :
    Tendsto (fun j:ℕ=>liClockPairedEtaSymmetrizedEvenMoment N j/
      liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j) atTop
      (𝓝 ((liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2)) :=
  endpoint_geometric_limit (liClockPairedEtaPartitionEndpointRatioDecay_nonneg_lt_one hN).1
    (liClockPairedEtaPartitionEndpointRatioDecay_nonneg_lt_one hN).2
    (fun j=>(ep_moment_ratio_error_bound hN j).1) (fun j=>(ep_moment_ratio_error_bound hN j).2)

theorem liClockPairedEtaPartitionEndpoint_eventually_evenMoment_gt_contiguous {N : ℕ} (hN : 2≤N) :
    ∀ᶠj:ℕ in atTop, liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j<
      liClockPairedEtaSymmetrizedEvenMoment N j := by
  have hN0 : 0<N := by omega
  have he := (liClockPairedEtaPartitionEndpoint_evenMoment_ratio_tendsto hN0).eventually
    (lt_mem_nhds (ep_scale_one_lt hN))
  filter_upwards [he] with j hj
  have hU := liClockPairedEtaContiguousSymmetrizedEvenMoment_pos (ep_length_pos hN0) j
  simpa only [one_mul] using (lt_div_iff₀ hU).mp hj

private abbrev epCA (N : ℕ) := liClockPairedEtaPartitionBorelCoefficient N
private abbrev epCU (N : ℕ) := liClockPairedEtaContiguousBorelCoefficient (epL N)

private lemma ep_coefficient_A_pos {N : ℕ} (hN : 0<N) (j : ℕ) : 0<epCA N j :=
  div_pos (liClockPairedEtaSymmetrizedEvenMoment_pos hN j) (by positivity)

private lemma ep_coefficient_U_pos {N : ℕ} (hN : 0<N) (j : ℕ) : 0<epCU N j :=
  liClockPairedEtaContiguousBorelCoefficient_pos (ep_length_pos hN) j

private lemma ep_series_A_summable {N : ℕ} (hN : 0<N) (t : ℝ) :
    Summable (fun j:ℕ=>epCA N j*t^(2*j)) := by
  apply (summable_liClockPairedEtaPartitionBorelTerm hN t).congr
  intro j
  dsimp only [epCA,liClockPairedEtaPartitionBorelCoefficient]
  ring

private lemma ep_series_U_summable {N : ℕ} (hN : 0<N) (t : ℝ) :
    Summable (fun j:ℕ=>epCU N j*t^(2*j)) :=
  summable_liClockPairedEtaContiguousBorelTerm (ep_length_pos hN) t

private lemma ep_series_A_eq (N : ℕ) (t : ℝ) :
    liClockPositiveEvenSeries (epCA N) t=liClockPairedEtaPartitionBorelKernel N t := by
  unfold liClockPositiveEvenSeries
  rw [liClockPairedEtaPartitionBorelKernel_eq_tsum]
  apply tsum_congr
  intro j
  dsimp only [epCA,liClockPairedEtaPartitionBorelCoefficient]
  ring

private lemma ep_series_U_eq (N : ℕ) (t : ℝ) :
    liClockPositiveEvenSeries (epCU N) t=liClockPairedEtaContiguousBorelKernel (epL N) t := rfl

private lemma ep_coefficient_ratio_eq {N : ℕ} (hN : 0<N) (j : ℕ) :
    epCA N j/epCU N j = liClockPairedEtaSymmetrizedEvenMoment N j/
      liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j :=
  common_factor_coefficient_ratio (liClockPairedEtaContiguousSymmetrizedEvenMoment_pos
    (ep_length_pos hN) j).ne' (by positivity)

private lemma ep_coefficient_ratio_tendsto {N : ℕ} (hN : 0<N) :
    Tendsto (fun j:ℕ=>epCA N j/epCU N j) atTop (𝓝 (epκ N)) := by
  have he : (fun j:ℕ=>epCA N j/epCU N j) =
      (fun j:ℕ=>liClockPairedEtaSymmetrizedEvenMoment N j/
        liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j) :=
    funext (ep_coefficient_ratio_eq hN)
  rw [he]
  exact liClockPairedEtaPartitionEndpoint_evenMoment_ratio_tendsto hN

private lemma ep_coefficient_ceiling {N : ℕ} (hN : 0<N) (j : ℕ) : epCA N j≤epκ N*epCU N j :=
  (common_factor_comparison (by positivity)).2 (liClockPairedEtaSymmetrizedEvenMoment_le_contiguous hN j)

private lemma ep_coefficient_lt_ceiling {N : ℕ} (hN : 2≤N) (j : ℕ) : epCA N j<epκ N*epCU N j := by
  have hfac : 0<((2*j).factorial:ℝ)^2 := by positivity
  change liClockPairedEtaSymmetrizedEvenMoment N j/((2*j).factorial:ℝ)^2 <
    epκ N*(liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j/((2*j).factorial:ℝ)^2)
  rw [← mul_div_assoc,div_lt_div_iff_of_pos_right hfac]
  exact sub_pos.mp (liClockPairedEtaPartitionEndpoint_evenMoment_defect hN j).1

end
end RHTower

namespace RHTower
noncomputable section

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ComplexConjugate

/-- The complete positive-clock kernel ratio has the same sharp fixed-prefix endpoint limit. -/
theorem liClockPairedEtaPartitionEndpoint_borel_ratio_tendsto {N : ℕ} (hN : 0<N) :
    Tendsto (fun t:ℝ=>liClockPairedEtaPartitionBorelKernel N t/
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t) atTop
      (𝓝 ((liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2)) := by
  have h := liClockPositiveEvenSeries_ratio_tendsto (fun j=>(ep_coefficient_A_pos hN j).le)
    (ep_coefficient_U_pos hN) (ep_series_A_summable hN) (ep_series_U_summable hN)
    (ep_coefficient_ratio_tendsto hN)
  simpa only [ep_series_A_eq,ep_series_U_eq] using h

theorem liClockPairedEtaPartitionEndpoint_borel_le_ceiling {N : ℕ} (hN : 0<N) {t : ℝ} (_ht : 0≤t) :
    liClockPairedEtaPartitionBorelKernel N t≤
      (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t := by
  have h := liClockPositiveEvenSeries_le_ceiling (ep_coefficient_ceiling hN) t
    (ep_series_A_summable hN t) (ep_series_U_summable hN t)
  simpa only [ep_series_A_eq,ep_series_U_eq] using h

theorem liClockPairedEtaPartitionEndpoint_borel_lt_ceiling {N : ℕ} (hN : 2≤N) {t : ℝ} (_ht : 0≤t) :
    liClockPairedEtaPartitionBorelKernel N t<
      (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2*
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t := by
  have hN0 : 0<N := by omega
  have h := liClockPositiveEvenSeries_lt_ceiling (ep_coefficient_ceiling hN0)
    (ep_coefficient_lt_ceiling hN 0) t (ep_series_A_summable hN0 t) (ep_series_U_summable hN0 t)
  simpa only [ep_series_A_eq,ep_series_U_eq] using h

/-- The endpoint constant is optimal simultaneously across every natural moment order. -/
theorem liClockPairedEtaPartitionEndpoint_evenMoment_ceiling_iff {N : ℕ} (hN : 0<N) (K : ℝ) :
    (∀j:ℕ, liClockPairedEtaSymmetrizedEvenMoment N j≤
      K*liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j) ↔
      (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2≤K :=
  liClockPositiveEvenSeries_coefficient_ceiling_iff
    (fun j=>(liClockPairedEtaSymmetrizedEvenMoment_pos hN j).le)
    (liClockPairedEtaContiguousSymmetrizedEvenMoment_pos (ep_length_pos hN))
    (liClockPairedEtaPartitionEndpoint_evenMoment_ratio_tendsto hN)
    (liClockPairedEtaSymmetrizedEvenMoment_le_contiguous hN)

/-- The same endpoint constant is optimal across all nonnegative clocks of the full kernel. -/
theorem liClockPairedEtaPartitionEndpoint_borel_ceiling_iff {N : ℕ} (hN : 0<N) (K : ℝ) :
    (∀t:ℝ,0≤t→liClockPairedEtaPartitionBorelKernel N t≤
      K*liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t) ↔
      (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
        liClockPairedEtaPartitionNormalizer N)^2≤K := by
  have h := liClockPositiveEvenSeries_ceiling_iff (K:=K) (fun j=>(ep_coefficient_A_pos hN j).le)
    (ep_coefficient_U_pos hN) (ep_series_A_summable hN) (ep_series_U_summable hN)
    (ep_coefficient_ratio_tendsto hN) (ep_coefficient_ceiling hN)
  simpa only [ep_series_A_eq,ep_series_U_eq] using h

theorem liClockPairedEtaPartitionEndpoint_borel_sub_contiguous_tendsto_atTop {N : ℕ} (hN : 2≤N) :
    Tendsto (fun t:ℝ=>liClockPairedEtaPartitionBorelKernel N t-
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t) atTop atTop := by
  have hN0 : 0<N := by omega
  have h := liClockPositiveEvenSeries_sub_tendsto_atTop (fun j=>(ep_coefficient_A_pos hN0 j).le)
    (ep_coefficient_U_pos hN0) (ep_series_A_summable hN0) (ep_series_U_summable hN0)
    (ep_coefficient_ratio_tendsto hN0) (ep_scale_one_lt hN)
  simpa only [ep_series_A_eq,ep_series_U_eq] using h

theorem liClockPairedEtaPartitionEndpoint_borel_ceiling_sub_tendsto_atTop {N : ℕ} (hN : 2≤N) :
    Tendsto (fun t:ℝ=>(liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
      liClockPairedEtaPartitionNormalizer N)^2*
        liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t-
      liClockPairedEtaPartitionBorelKernel N t) atTop atTop := by
  have hN0 : 0<N := by omega
  have h := liClockPositiveEvenSeries_ceiling_sub_tendsto_atTop
    (fun j=>(ep_coefficient_A_pos hN0 j).le) (ep_coefficient_U_pos hN0)
    (ep_series_A_summable hN0) (ep_series_U_summable hN0)
    (ep_coefficient_ceiling hN0) (ep_coefficient_lt_ceiling hN 1)
  simpa only [ep_series_A_eq,ep_series_U_eq] using h

theorem liClockPairedEtaPartitionEndpoint_eventually_borel_gt_contiguous {N : ℕ} (hN : 2≤N) :
    ∀ᶠt:ℝ in atTop, liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t<
      liClockPairedEtaPartitionBorelKernel N t := by
  have hN0 : 0<N := by omega
  have he := (liClockPairedEtaPartitionEndpoint_borel_ratio_tendsto hN0).eventually
    (lt_mem_nhds (ep_scale_one_lt hN))
  filter_upwards [he] with t ht
  have hU := liClockPairedEtaContiguousBorelKernel_pos (ep_length_pos hN0) t
  simpa only [one_mul] using (lt_div_iff₀ hU).mp ht

end
end RHTower

namespace RHTower
noncomputable section

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ComplexConjugate

/-- Every finite source defect degree below the chosen cutoff. -/
def liClockPairedEtaPartitionEndpointBorelDefectPrefix (N J : ℕ) : ℝ :=
  let κ := (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
    liClockPairedEtaPartitionNormalizer N)^2
  ∑ j ∈ Finset.range J,
    (κ * liClockPairedEtaContiguousBorelCoefficient (Real.log (2*(N:ℝ))) j -
      liClockPairedEtaPartitionBorelCoefficient N j)

private lemma ep_coefficient_defect_abs {N : ℕ} (hN : 0<N) (j : ℕ) :
    |epCA N j-epκ N*epCU N j|=epκ N*epCU N j-epCA N j := by
  rw [abs_of_nonpos (sub_nonpos.mpr (ep_coefficient_ceiling hN j)),neg_sub]

private lemma ep_coefficient_defect_error {N : ℕ} (hN : 0<N) (j : ℕ) :
    epκ N*epCU N j-epCA N j≤liClockPairedEtaPartitionEndpointRatioErrorScale N*
      liClockPairedEtaPartitionEndpointRatioDecay N^(2*j)*epCU N j := by
  have hU := ep_coefficient_U_pos hN j
  have he : (epκ N*epCU N j-epCA N j)/epCU N j=epκ N-epCA N j/epCU N j := by
    field_simp
  apply (div_le_iff₀ hU).mp
  rw [he,ep_coefficient_ratio_eq hN]
  exact (ep_moment_ratio_error_bound hN j).2

/-- Exact finite-prefix plus complete-tail control for every cutoff and every clock at least one. -/
theorem liClockPairedEtaPartitionEndpoint_borel_ratio_error {N : ℕ} (hN : 2≤N)
    (J : ℕ) (hJ : 0<J) {t : ℝ} (ht : 1≤t) :
    let κ := (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
      liClockPairedEtaPartitionNormalizer N)^2
    0<κ-liClockPairedEtaPartitionBorelKernel N t/
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t ∧
    κ-liClockPairedEtaPartitionBorelKernel N t/
      liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t≤
      liClockPairedEtaPartitionEndpointRatioErrorScale N*
        liClockPairedEtaPartitionEndpointRatioDecay N^(2*J)+
      liClockPairedEtaPartitionEndpointBorelDefectPrefix N J/
        (liClockPairedEtaContiguousBorelCoefficient (Real.log (2*(N:ℝ))) J*t^2) := by
  have hN0 : 0<N := by omega
  have hρ := liClockPairedEtaPartitionEndpointRatioDecay_nonneg_lt_one hN0
  have hC := liClockPairedEtaPartitionEndpointRatioErrorScale_nonneg hN0
  let δ := liClockPairedEtaPartitionEndpointRatioErrorScale N*
    liClockPairedEtaPartitionEndpointRatioDecay N^(2*J)
  have hδ : 0≤δ := mul_nonneg hC (pow_nonneg hρ.1 _)
  have hbound : ∀j,J≤j→|epCA N j-epκ N*epCU N j|≤δ*epCU N j := by
    intro j hj
    rw [ep_coefficient_defect_abs hN0]
    have hp := pow_le_pow_of_le_one hρ.1 hρ.2.le (show 2*J≤2*j by omega)
    calc
      _ ≤ liClockPairedEtaPartitionEndpointRatioErrorScale N*
          liClockPairedEtaPartitionEndpointRatioDecay N^(2*j)*epCU N j := ep_coefficient_defect_error hN0 j
      _ ≤ δ*epCU N j := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC)
        (ep_coefficient_U_pos hN0 j).le
  have herr := liClockPositiveEvenSeries_relative_error_le J hJ
    (fun j=>(ep_coefficient_A_pos hN0 j).le) (ep_coefficient_U_pos hN0) hδ ht
    (ep_series_A_summable hN0 t) (ep_series_U_summable hN0 t) hbound
  rw [ep_series_A_eq,ep_series_U_eq] at herr
  simp_rw [ep_coefficient_defect_abs hN0] at herr
  have hU := liClockPairedEtaContiguousBorelKernel_pos (ep_length_pos hN0) t
  have hlt : liClockPairedEtaPartitionBorelKernel N t/
      liClockPairedEtaContiguousBorelKernel (epL N) t<epκ N :=
    (div_lt_iff₀ hU).2 (liClockPairedEtaPartitionEndpoint_borel_lt_ceiling hN (by linarith))
  rw [abs_of_nonpos (sub_nonpos.mpr hlt.le),neg_sub] at herr
  dsimp only
  constructor
  · exact sub_pos.mpr hlt
  · calc
      _ ≤ liClockPairedEtaPartitionEndpointBorelDefectPrefix N J/(epCU N J*t^2)+δ := herr
      _ = _ := add_comm _ _

private lemma ep_defect_summable {N : ℕ} (hN : 0<N) (t : ℝ) :
    Summable (fun j:ℕ=>(epκ N*epCU N j-epCA N j)*t^(2*j)) := by
  apply ((ep_series_U_summable hN t).mul_left (epκ N)).sub (ep_series_A_summable hN t) |>.congr
  intro j
  ring

private lemma ep_defect_tsum {N : ℕ} (hN : 0<N) (t : ℝ) :
    (∑'j,(epκ N*epCU N j-epCA N j)*t^(2*j)) =
      epκ N*liClockPairedEtaContiguousBorelKernel (epL N) t-liClockPairedEtaPartitionBorelKernel N t := by
  have he : (fun j:ℕ=>(epκ N*epCU N j-epCA N j)*t^(2*j)) =
      (fun j:ℕ=>epκ N*(epCU N j*t^(2*j))-epCA N j*t^(2*j)) := by
    funext j
    ring
  rw [he,Summable.tsum_sub ((ep_series_U_summable hN t).mul_left (epκ N))
    (ep_series_A_summable hN t),tsum_mul_left]
  change epκ N*liClockPositiveEvenSeries (epCU N) t-liClockPositiveEvenSeries (epCA N) t=_
  rw [ep_series_U_eq,ep_series_A_eq]

theorem liClockPairedEtaPartitionEndpoint_borel_defect_ge_scale_sub_one {N : ℕ} (hN : 2≤N)
    {t : ℝ} (_ht : 0≤t) :
    let κ := (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
      liClockPairedEtaPartitionNormalizer N)^2
    κ-1≤κ*liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t-
      liClockPairedEtaPartitionBorelKernel N t := by
  have hN0 : 0<N := by omega
  have h := (ep_defect_summable hN0 t).le_tsum 0 (fun j _=>by
    apply mul_nonneg (sub_nonneg.mpr (ep_coefficient_ceiling hN0 j))
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) j)
  rw [ep_defect_tsum hN0] at h
  simpa only [Nat.mul_zero,pow_zero,mul_one,epCA,epCU,liClockPairedEtaPartitionBorelCoefficient,
    liClockPairedEtaContiguousBorelCoefficient,liClockPairedEtaSymmetrizedEvenMoment_zero hN0,
    liClockPairedEtaContiguousSymmetrizedEvenMoment_zero (ep_length_pos hN0),Nat.factorial_zero,
    Nat.cast_one,one_pow,div_one,mul_one] using h

private lemma endpoint_even_factorial_series_summable (r : ℝ) :
    Summable (fun j:ℕ=>r^(2*j)/((2*j).factorial:ℝ)^2) := by
  apply (Real.summable_pow_div_factorial (r^2)).of_nonneg_of_le
  · intro j
    rw [pow_mul]
    positivity
  · intro j
    have hf : (j.factorial:ℝ)≤((2*j).factorial:ℝ)^2 := by
      have h₁ : (j.factorial:ℝ)≤((2*j).factorial:ℝ) :=
        by exact_mod_cast Nat.factorial_le (show j≤2*j by omega)
      have h₂ : (1:ℝ)≤((2*j).factorial:ℝ) :=
        by exact_mod_cast Nat.factorial_le (Nat.zero_le (2*j))
      nlinarith
    rw [pow_mul]
    exact div_le_div_of_nonneg_left (pow_nonneg (sq_nonneg r) j) (by positivity) hf

theorem liClockPairedEtaPartitionEndpoint_borel_defect_le_full_envelope {N : ℕ} (hN : 2≤N)
    {t : ℝ} (_ht : 0≤t) :
    let κ := (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))/
      liClockPairedEtaPartitionNormalizer N)^2
    κ*liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) t-
      liClockPairedEtaPartitionBorelKernel N t≤
      (κ-1)*(∑'j:ℕ,(liClockPairedEtaPartitionEndpointInnerRadius N*t)^(2*j)/((2*j).factorial:ℝ)^2) := by
  have hN0 : 0<N := by omega
  have hupper := (endpoint_even_factorial_series_summable (epA N*t)).mul_left (epκ N-1)
  have hpoint : ∀j:ℕ,(epκ N*epCU N j-epCA N j)*t^(2*j)≤
      (epκ N-1)*((epA N*t)^(2*j)/((2*j).factorial:ℝ)^2) := by
    intro j
    have hd := (liClockPairedEtaPartitionEndpoint_evenMoment_defect hN j).2
    have hc : epκ N*epCU N j-epCA N j≤
        (epκ N-1)*(epA N)^(2*j)/((2*j).factorial:ℝ)^2 := by
      have he : epκ N*epCU N j-epCA N j =
          (epκ N*liClockPairedEtaContiguousSymmetrizedEvenMoment (epL N) j-
            liClockPairedEtaSymmetrizedEvenMoment N j)/((2*j).factorial:ℝ)^2 := by
        dsimp only [epCU,epCA,liClockPairedEtaContiguousBorelCoefficient,liClockPairedEtaPartitionBorelCoefficient]
        ring
      rw [he]
      exact div_le_div_of_nonneg_right hd (sq_nonneg _)
    have hp : 0≤t^(2*j) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg t) j
    calc
      _ ≤ ((epκ N-1)*(epA N)^(2*j)/((2*j).factorial:ℝ)^2)*t^(2*j) :=
        mul_le_mul_of_nonneg_right hc hp
      _ = _ := by rw [mul_pow]; ring
  have h := (ep_defect_summable hN0 t).tsum_le_tsum hpoint hupper
  rw [ep_defect_tsum hN0,tsum_mul_left] at h
  exact h

end
end RHTower

namespace RHTower
noncomputable section

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ComplexConjugate

/-- The literal full complex Borel kernel of the actual normalized difference moments. -/
def liClockPairedEtaPartitionBorelKernelComplex (N : ℕ) (z : ℂ) : ℂ :=
  ∑'j:ℕ,(liClockPairedEtaPartitionBorelCoefficient N j:ℂ)*z^(2*j)

private lemma ep_coefficient_A_le {N : ℕ} (hN : 0<N) (j : ℕ) :
    epCA N j≤(epL N^2)^j/(j.factorial:ℝ) := by
  have hf : (j.factorial:ℝ)≤((2*j).factorial:ℝ)^2 := by
    have h₁ : (j.factorial:ℝ)≤((2*j).factorial:ℝ) :=
      by exact_mod_cast Nat.factorial_le (show j≤2*j by omega)
    have h₂ : (1:ℝ)≤((2*j).factorial:ℝ) :=
      by exact_mod_cast Nat.factorial_le (Nat.zero_le (2*j))
    nlinarith
  change liClockPairedEtaSymmetrizedEvenMoment N j/((2*j).factorial:ℝ)^2≤_
  calc
    _ ≤ (epL N)^(2*j)/((2*j).factorial:ℝ)^2 :=
      div_le_div_of_nonneg_right (liClockPairedEtaSymmetrizedEvenMoment_le_log_power hN j) (sq_nonneg _)
    _ ≤ (epL N)^(2*j)/(j.factorial:ℝ) :=
      div_le_div_of_nonneg_left (by rw [pow_mul]; positivity) (by positivity) hf
    _ = _ := by rw [pow_mul]

private lemma ep_complex_term_norm_le {N : ℕ} (hN : 0<N) {T : ℝ} {z : ℂ}
    (hz : ‖z‖≤T) (j : ℕ) :
    ‖(epCA N j:ℂ)*z^(2*j)‖≤(epL N^2*T^2)^j/(j.factorial:ℝ) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ep_coefficient_A_pos hN j),norm_pow]
  calc
    _ ≤ ((epL N^2)^j/(j.factorial:ℝ))*T^(2*j) :=
      mul_le_mul (ep_coefficient_A_le hN j) (pow_le_pow_left₀ (norm_nonneg _) hz _)
        (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by rw [mul_pow,← pow_mul]; ring

theorem summable_norm_liClockPairedEtaPartitionBorelTermComplex {N : ℕ} (hN : 0<N) (z : ℂ) :
    Summable (fun j:ℕ=>‖(liClockPairedEtaPartitionBorelCoefficient N j:ℂ)*z^(2*j)‖) :=
  (Real.summable_pow_div_factorial (epL N^2*‖z‖^2)).of_nonneg_of_le
    (fun _=>norm_nonneg _) (ep_complex_term_norm_le hN (le_refl ‖z‖))

theorem hasSumUniformlyOn_liClockPairedEtaPartitionBorelTermComplex {N : ℕ} (hN : 0<N)
    {T : ℝ} (_hT : 0≤T) :
    HasSumUniformlyOn (fun j:ℕ=>fun z:ℂ=>(liClockPairedEtaPartitionBorelCoefficient N j:ℂ)*z^(2*j))
      (liClockPairedEtaPartitionBorelKernelComplex N) (closedBall 0 T) := by
  exact HasSumUniformlyOn.of_norm_le_summable (Real.summable_pow_div_factorial (epL N^2*T^2))
    (fun j z hz=>ep_complex_term_norm_le hN (by simpa only [mem_closedBall,dist_zero_right] using hz) j)

theorem summableLocallyUniformlyOn_liClockPairedEtaPartitionBorelTermComplex {N : ℕ} (hN : 0<N) :
    SummableLocallyUniformlyOn (fun j:ℕ=>fun z:ℂ=>(liClockPairedEtaPartitionBorelCoefficient N j:ℂ)*z^(2*j)) univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K hK hKc
  obtain ⟨C,hC⟩ := hKc.bddAbove_image continuous_norm.continuousOn
  let T := max C 0
  refine ⟨_,Real.summable_pow_div_factorial (epL N^2*T^2),?_⟩
  intro j z hz
  exact ep_complex_term_norm_le hN ((hC ⟨z,hz,rfl⟩).trans (le_max_left _ _)) j

theorem liClockPairedEtaPartitionBorelKernelComplex_ofReal {N : ℕ} (_hN : 0<N) (t : ℝ) :
    liClockPairedEtaPartitionBorelKernelComplex N (t:ℂ)=(liClockPairedEtaPartitionBorelKernel N t:ℂ) := by
  unfold liClockPairedEtaPartitionBorelKernelComplex
  simp_rw [← Complex.ofReal_pow,← Complex.ofReal_mul]
  rw [← ep_series_A_eq]
  exact (Complex.ofReal_tsum _).symm

end
end RHTower
