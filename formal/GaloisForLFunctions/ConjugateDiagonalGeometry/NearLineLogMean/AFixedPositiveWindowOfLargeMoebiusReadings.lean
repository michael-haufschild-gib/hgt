import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheExponentOfTheMollifiedErrorIsRigid
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros

/-!
# Persistent large pure Möbius readings in a fixed positive-height window

For each subcritical exponent a single interval of any prescribed positive length, entirely
above height one, has arbitrarily small low-value measure at every large
cutoff. The chosen window may depend on the exponent and the allowed
exceptional measure. Its center works for all fixed amplitude constants.
-/
noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open MultiscaleMollifiedZetaField
open SquareRootThreshold (zetaZeroWidth zetaZeroWidth_eq_zetaZeroAbscissa_sub_half)

private theorem near_width_in_upper_strip {t : ℝ} (ht : 0<t) (hw : t<zetaZeroWidth) :
    ∃ ρ : ℂ, riemannZeta ρ=0 ∧ 1/2<ρ.re ∧ ρ.re<1 ∧
      zetaZeroWidth-(ρ.re-1/2)<t ∧ 4≤ρ.im := by
  have hb : 1/2+zetaZeroWidth-t < _root_.RHTower.zetaZeroAbscissa := by
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]; linarith only [ht]
  obtain ⟨z,hz,hz1,hzr⟩ := _root_.RHTower.exists_zetaZero_mem_openStrip_lt_re hb
  have hr : 1/2<z.re := by linarith only [hw,hzr]
  have hg : zetaZeroWidth-(z.re-1/2)<t := by linarith only [hzr]
  have hi := _root_.RHTower.four_le_abs_im_of_zeta_zero (by linarith only [hr]) hz1 hz
  rcases le_total 0 z.im with hpos|hneg
  · exact ⟨z,hz,hr,hz1,hg,by rwa [abs_of_nonneg hpos] at hi⟩
  · rw [abs_of_nonpos hneg] at hi
    exact ⟨conj z,by rw [riemannZeta_conj,hz,map_zero],by simpa using hr,by simpa using hz1,
      by simpa using hg,by simpa using hi⟩

private theorem sparse_error_window {κ η L : ℝ} (hL : 0<L) (hκ : 0≤κ) (hw : κ<zetaZeroWidth)
    (hη : 0<η) : ∃ γ : ℝ, 4≤γ ∧ ∀ᶠ N : ℕ in atTop,
      volume.real (lowSet N κ ∩ Icc γ (γ+L)) ≤ η := by
  let w := zetaZeroWidth
  have hw0 : 0<w := hκ.trans_lt hw
  let p := (w/2)/(Real.pi*(1/4+L^2))
  have hp : 0<p := by dsimp only [p]; positivity
  let t := min (w/2) ((p*η/4)*(w-κ))
  have hg := sub_pos.mpr hw
  have ht : 0<t := lt_min (half_pos hw0) (mul_pos (by positivity) hg)
  obtain ⟨ρ,hz,hre,hre1,hdiff,hi⟩ := near_width_in_upper_strip ht
    ((min_le_left ..).trans_lt (half_lt_self hw0))
  have hd := sub_pos.mpr hre
  have hlower : ∀ u ∈ Icc ρ.im (ρ.im+L), p≤zeroPoisson ρ u := by
    intro u hu
    have hdlo : w/2≤ρ.re-1/2 := by
      have hlim : t≤w/2 := min_le_left ..; linarith only [hdiff,hlim]
    have hdsq : (ρ.re-1/2)^2≤1/4 := by
      have he : ρ.re-1/2≤1/2 := by linarith only [hre1]
      have hs := pow_le_pow_left₀ hd.le he 2
      norm_num at hs
      exact hs
    have h := poisson_lower_bound hd (show |u-ρ.im|≤L from abs_le.mpr
      ⟨by linarith only [hu.1,hL],by linarith only [hu.2]⟩)
    exact (div_le_div₀ hd.le hdlo (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith only [hdsq]) Real.pi_pos.le)).trans h
  have hfrac : (w-(ρ.re-1/2))/(w-κ) ≤ p*η/4 :=
    (div_le_iff₀ hg).mpr (hdiff.le.trans (min_le_right ..))
  refine ⟨ρ.im,hi,?_⟩
  filter_upwards [eventually_poissonMass_lowSet_le hz hre hre1 hκ hw (η:=p*η/4) (by positivity)] with N hN
  have hmass := mul_volume_le_setIntegral (integrable_zeroPoisson hre) (zeroPoisson_nonneg hre)
    (measurableSet_lowSet N κ) hlower
  apply le_of_mul_le_mul_left _ hp
  linarith only [hmass,hN,hfrac,mul_pos hp hη]

/-- Almost the full measure of one fixed interval sees a large pure
Möbius section for every large integer cutoff. Its center can be fixed
before choosing the amplitude constant C. -/
theorem fixed_positive_window_of_large_moebius_sections {b η L : ℝ} (hL : 0<L) (hb : 0≤b)
    (hw : b<zetaZeroWidth) (hη : 0<η) :
    ∃ γ : ℝ, 4≤γ ∧ ∀ C : ℝ, ∀ᶠ N : ℕ in atTop,
      volume.real {u : ℝ | u∈Icc γ (γ+L) ∧
        ‖moebiusPoly N (linePoint u)‖ ≤ C*(N:ℝ)^b} ≤ η := by
  obtain ⟨κ,hbκ,hκw⟩ := exists_between hw
  obtain ⟨γ,hγ,hl⟩ := sparse_error_window hL (hb.trans hbκ.le) hκw hη
  refine ⟨γ,hγ,fun C => ?_⟩
  let B := 18*(1+|γ|+L)
  have hB : 0≤B := by dsimp only [B]; positivity
  have he := ((tendsto_rpow_atTop (sub_pos.mpr hbκ)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (B*|C|+1)
  filter_upwards [hl,he,eventually_ge_atTop 1] with N hN hlarge hn
  have h1 : (1:ℝ)≤N := Nat.one_le_cast.mpr hn
  have hx := zero_lt_one.trans_le h1
  apply le_trans (measureReal_mono ?_ (ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_right))) hN
  intro u hu
  refine ⟨?_,hu.1⟩
  have hab : |u|≤|γ|+L := abs_le.mpr ⟨by linarith only [hu.1.1,neg_abs_le γ,hL],
    by linarith only [hu.1.2,le_abs_self γ]⟩
  have hz : ‖riemannZeta (linePoint u)‖≤B := (norm_zeta_linePoint_le u).trans
    (by dsimp only [B]; linarith only [hab])
  have hm := hu.2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx.le _))
  have h := norm_sub_le (riemannZeta (linePoint u)*moebiusPoly N (linePoint u)) 1
  rw [norm_one,norm_mul] at h
  have hcost := mul_le_mul hz hm (norm_nonneg _) hB
  have hdom := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hx.le b)
  change (B*|C|+1)*(N:ℝ)^b ≤ (N:ℝ)^(κ-b)*(N:ℝ)^b at hdom
  rw [←Real.rpow_add hx,sub_add_cancel] at hdom
  change ‖riemannZeta (linePoint u)*moebiusPoly N (linePoint u)-1‖ ≤ (N:ℝ)^κ
  linarith only [h,hcost,hdom,Real.one_le_rpow h1 hb]

/-- Energy recorded after deleting arbitrary measurable observation times
from the original positive interval [1,H]. -/
def retainedMoebiusEnergy (N : ℕ) (H : ℝ) (D : Set ℝ) :=
  ∫ u in Icc 1 H \ D, ‖moebiusPoly N (linePoint u)‖^2

/-- For each allowed amount d of missing time there is one fixed
positive-frequency window that still pays the entire subcritical power
after any deletion of measure at most d. The observer may select the
deleted set after seeing the values of the polynomial. -/
theorem positive_moebius_energy_after_erasure {b d : ℝ} (hb : 0≤b)
    (hw : b<zetaZeroWidth) (hd : 0≤d) :
    ∃ γ : ℝ, 4≤γ ∧ ∀ᶠ N : ℕ in atTop, ∀ H : ℝ, γ+(d+2)≤H →
      ∀ D : Set ℝ, MeasurableSet D → volume D≤ENNReal.ofReal d →
        (N:ℝ)^(2*b) ≤ retainedMoebiusEnergy N H D := by
  have hL : 0<d+2 := by linarith only [hd]
  obtain ⟨γ,hγ,h⟩ := fixed_positive_window_of_large_moebius_sections hL hb hw (η:=1) zero_lt_one
  refine ⟨γ,hγ,?_⟩
  filter_upwards [h 1,eventually_ge_atTop 1] with N hbad hN
  intro H hH D hmD hD
  let W := Icc γ (γ+(d+2))
  let B := {u : ℝ | u∈W ∧ ‖moebiusPoly N (linePoint u)‖≤(N:ℝ)^b}
  let G := (W \ D) \ B
  have hc : Continuous (fun u => ‖moebiusPoly N (linePoint u)‖) :=
    ((differentiable_moebiusPoly N).continuous.comp (by unfold linePoint; fun_prop)).norm
  have hmB : MeasurableSet B := measurableSet_Icc.inter (measurableSet_le hc.measurable measurable_const)
  have hmG : MeasurableSet G := (measurableSet_Icc.diff hmD).diff hmB
  have hfinD := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD
  have hdreal : volume.real D≤d := (ENNReal.toReal_mono ENNReal.ofReal_ne_top hD).trans_eq (ENNReal.toReal_ofReal hd)
  have hfinB : volume B≠⊤ := ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono (fun _ h => h.1))
  have hfinG : volume G≠⊤ := ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono (fun _ h => h.1.1))
  have hB : volume.real B≤1 := by simpa only [one_mul] using hbad
  have hW : volume.real W=d+2 := by
    rw [W,Real.volume_real_Icc_of_le (by linarith only [hL])]; ring
  have hG : 1≤volume.real G := by
    have h₁ := le_measureReal_sdiff (μ:=volume) (s₁:=W) hfinD
    have h₂ := le_measureReal_sdiff (μ:=volume) (s₁:=W \ D) hfinB
    change _ ≤ volume.real G at h₂
    linarith only [h₁,h₂,hdreal,hB,hW]
  have hs : G ⊆ Icc 1 H \ D := fun u hu =>
    ⟨⟨(by linarith only [hγ] : 1≤γ).trans hu.1.1.1,hu.1.1.2.trans hH⟩,hu.1.2⟩
  have hint : IntegrableOn (fun u => ‖moebiusPoly N (linePoint u)‖^2) (Icc 1 H \ D) :=
    (hc.pow 2).integrableOn_Icc.mono_set sdiff_subset
  have ht : ∫ _u in G, ((N:ℝ)^b)^2 ≤ ∫ u in G, ‖moebiusPoly N (linePoint u)‖^2 := by
    apply setIntegral_mono_on (integrableOn_const hfinG) (hint.mono_set hs) hmG
    intro u hu
    have hr : (N:ℝ)^b < ‖moebiusPoly N (linePoint u)‖ :=
      lt_of_not_ge (fun hlt => hu.2 ⟨hu.1.1,hlt⟩)
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hr.le 2
  rw [setIntegral_const,smul_eq_mul] at ht
  have hfull := setIntegral_mono_set hint (.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall (fun _ hu => hs hu))
  rw [mul_comm (2:ℝ),Real.rpow_mul (Nat.cast_nonneg _),Real.rpow_two]
  exact (le_mul_of_one_le_left (sq_nonneg _) hG).trans (ht.trans hfull)

#print axioms positive_moebius_energy_after_erasure
#print axioms fixed_positive_window_of_large_moebius_sections
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
