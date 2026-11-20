import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheExponentOfTheMollifiedErrorIsRigid
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Measuring the zero width on a single expanding frequency window

An expanding symmetric interval eventually contains every fixed local
test of the mollified error. On a window of subpower height the loss
from pointwise Abel summation is subpower too. Consequently one
measurement schedule suffices, even if its height grows only
logarithmically with the integer length.
-/
noncomputable section
open Complex Filter MeasureTheory Set Topology
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open MultiscaleMollifiedZetaField
open SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg zetaZeroWidth_le_iff_xiZeroHalfPlaneBound)

/-- Pure Möbius energy on a symmetric critical-line interval. -/
def symmetricMoebiusEnergy (N : ℕ) (H : ℝ) : ℝ :=
  ∫ t in Icc (-H) H, ‖moebiusPoly N (linePoint t)‖^2

private theorem continuous_reading (N : ℕ) : Continuous (fun t => ‖moebiusPoly N (linePoint t)‖^2) :=
  ((differentiable_moebiusPoly N).continuous.comp (by unfold linePoint; fun_prop)).norm.pow 2

/-- A global pure energy measurement pays for the mollified error
on every fixed interior interval, with a constant independent of N. -/
theorem local_error_paid_by_pure_window (τ : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ N H, |τ|+1 ≤ H →
      (∫ u in Icc (τ-1) (τ+1), ‖lineError (moebiusPoly N) u‖^2) ≤
        C*symmetricMoebiusEnergy N H+4 := by
  let B := 18*(2+|τ|)
  have hB : 0≤B := by dsimp only [B]; positivity
  refine ⟨2*B^2,by positivity,fun N H hH => ?_⟩
  let W := Icc (τ-1) (τ+1)
  let f := fun t => ‖moebiusPoly N (linePoint t)‖^2
  have hf : Continuous f := continuous_reading N
  have he : Continuous (fun u => ‖lineError (moebiusPoly N) u‖^2) :=
    (continuous_lineError (differentiable_moebiusPoly N)).norm.pow 2
  have hsub : W ⊆ Icc (-H) H := by
    intro u hu
    exact ⟨by linarith only [hu.1,neg_abs_le τ,hH],by linarith only [hu.2,le_abs_self τ,hH]⟩
  have hpt (u : ℝ) (hu : u∈W) : ‖lineError (moebiusPoly N) u‖^2 ≤ 2*B^2*f u+2 := by
    have hab : |u|≤1+|τ| := abs_le.mpr
      ⟨by linarith only [hu.1,neg_abs_le τ],by linarith only [hu.2,le_abs_self τ]⟩
    have hz : ‖riemannZeta (linePoint u)‖≤B := (norm_zeta_linePoint_le u).trans (by dsimp only [B]; linarith)
    have hnorm := norm_sub_le (riemannZeta (linePoint u)*moebiusPoly N (linePoint u)) 1
    rw [norm_mul,norm_one] at hnorm
    have hm := hnorm.trans (add_le_add (mul_le_mul_of_nonneg_right hz (norm_nonneg _)) (le_refl (1:ℝ)))
    have hh := pow_le_pow_left₀ (norm_nonneg _) hm 2
    change ‖riemannZeta (linePoint u)*moebiusPoly N (linePoint u)-1‖^2 ≤ _
    dsimp only [f]
    linarith only [hh,sq_nonneg (B*‖moebiusPoly N (linePoint u)‖-1)]
  have h := setIntegral_mono_on (he.integrableOn_Icc)
    (((hf.const_mul (2*B^2)).add continuous_const).integrableOn_Icc) measurableSet_Icc hpt
  rw [integral_add (hf.integrableOn_Icc.const_mul _) (integrableOn_const measure_Icc_lt_top.ne),
    integral_const_mul,setIntegral_const,Real.volume_real_Icc_of_le (by linarith : τ-1≤τ+1),smul_eq_mul] at h
  have hsub' := setIntegral_mono_set hf.integrableOn_Icc (Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (fun _ hu => hsub hu))
  change _ ≤ symmetricMoebiusEnergy N H at hsub'
  linarith only [h,mul_le_mul_of_nonneg_left hsub' (by positivity : 0≤2*B^2)]

/-- For any divergent height schedule, frequently small pure moments
of power 2β imply that every zero lies within β of the critical line. -/
theorem width_le_of_single_expanding_window {H : ℕ → ℝ} (hH : Tendsto H atTop atTop)
    {β : ℝ} (hb : 0≤β) (h : ∀ e : ℝ, 0<e → ∃ᶠ N : ℕ in atTop,
      symmetricMoebiusEnergy N (H N) ≤ (N:ℝ)^(2*(β+e))) : zetaZeroWidth≤β := by
  apply zetaZeroWidth_le_of_frequently_window_moment hb (p:=2) (by norm_num)
  intro τ ε hε
  obtain ⟨C,hC,hW⟩ := local_error_paid_by_pure_window τ
  have hbig := ((tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (C+4)
  apply ((h (ε/2) (half_pos hε)).and_eventually
    ((hH.eventually_ge_atTop (|τ|+1)).and (hbig.and (eventually_ge_atTop 1)))).mono
  rintro N ⟨he,hwide,hbnd,hN⟩
  have hN1 := (Nat.one_le_cast (α:=ℝ)).mpr hN
  have hr := Real.one_le_rpow hN1 (show 0≤2*(β+ε/2) by linarith)
  have hp := mul_le_mul_of_nonneg_right hbnd (Real.rpow_nonneg (Nat.cast_nonneg N) (2*(β+ε/2)))
  change (C+4)*(N:ℝ)^(2*(β+ε/2)) ≤ (N:ℝ)^ε*(N:ℝ)^(2*(β+ε/2)) at hp
  rw [←Real.rpow_add (zero_lt_one.trans_le hN1),show ε+2*(β+ε/2)=2*(β+ε) by ring] at hp
  change (∫ u in Icc (τ-1) (τ+1), ‖lineError (moebiusPoly N) u‖^(2:ℝ)) ≤ _
  simp only [Real.rpow_two]
  linarith only [hW N _ hwide,mul_le_mul_of_nonneg_left he hC,hp,hr]

private theorem window_abel_upper {e : ℝ} (he : 0<e) :
    ∃ C : ℝ, 0≤C ∧ ∀ {N : ℕ}, 1≤N → ∀ {H : ℝ}, 0≤H →
      symmetricMoebiusEnergy N H ≤ C*(1+H)^3*(N:ℝ)^(2*(zetaZeroWidth+e)) := by
  obtain ⟨K,hK,h⟩ := exists_norm_moebiusPoly_line_le he
  refine ⟨8*K^2,by positivity,fun {N} hN {H} hH => ?_⟩
  let A := (N:ℝ)^(zetaZeroWidth+e)
  have hA : 0≤A := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let D := (2*A*(K*(1+H)))^2
  have hD : 0≤D := sq_nonneg _
  have hm := setIntegral_mono_on ((continuous_reading N).integrableOn_Icc)
    (integrableOn_const (c:=D) measure_Icc_lt_top.ne) measurableSet_Icc (fun t ht => by
      have ht' : |t|≤H := abs_le.mpr ht
      apply pow_le_pow_left₀ (norm_nonneg _) ((h N t hN).trans ?_)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) ht') hK)
        (mul_nonneg (by norm_num) hA))
  rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : -H≤H),smul_eq_mul] at hm
  change symmetricMoebiusEnergy N H ≤ (H- -H)*D at hm
  have hsq : (N:ℝ)^(2*(zetaZeroWidth+e))=A^2 := by
    rw [mul_comm (2:ℝ),Real.rpow_mul (Nat.cast_nonneg _),Real.rpow_two]
  rw [hsq]
  have ht := mul_le_mul_of_nonneg_right (show H- -H≤2*(1+H) by linarith) hD
  exact hm.trans (ht.trans_eq (by dsimp only [D]; ring))

/-- An arbitrarily small exponent loss bounds the pure energy for every
large cutoff on any subpower height schedule. -/
theorem expanding_window_upper {H : ℕ → ℝ} (hH : Tendsto H atTop atTop)
    (hs : ∀ a : ℝ, 0<a → ∀ᶠ N : ℕ in atTop, 1+H N≤(N:ℝ)^a)
    {β e : ℝ} (hw : zetaZeroWidth≤β) (he : 0<e) : ∀ᶠ N : ℕ in atTop,
      symmetricMoebiusEnergy N (H N) ≤ (N:ℝ)^(2*(β+e)) := by
  obtain ⟨C,hC,h⟩ := window_abel_upper (by positivity : 0<e/4)
  have hc := ((tendsto_rpow_atTop (by positivity : 0<e/2)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop C
  filter_upwards [hc,hH.eventually_ge_atTop 0,hs (e/3) (by positivity),eventually_ge_atTop 1]
    with N hcn hpos hsmall hN
  have hN1 := (Nat.one_le_cast (α:=ℝ)).mpr hN
  have hx := zero_lt_one.trans_le hN1
  have hh := pow_le_pow_left₀ (by linarith only [hpos] : 0≤1+H N) hsmall 3
  have hpow : ((N:ℝ)^(e/3))^3=(N:ℝ)^e := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]
    congr 1; push_cast; ring
  rw [hpow] at hh
  have hs' := mul_le_mul hcn hh (pow_nonneg (by linarith only [hpos]) 3) (Real.rpow_nonneg hx.le _)
  have hp := mul_le_mul_of_nonneg_right hs' (Real.rpow_nonneg hx.le (2*(zetaZeroWidth+e/4)))
  rw [←Real.rpow_add hx,←Real.rpow_add hx] at hp
  exact (h hN hpos).trans (hp.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hw])))

/-- Sparse smallness on a single expanding subpower window measures the
same zero width as the family of polynomial-length experiments. -/
theorem single_subpower_window_iff {H : ℕ → ℝ} (hH : Tendsto H atTop atTop)
    (hs : ∀ a : ℝ, 0<a → ∀ᶠ N : ℕ in atTop, 1+H N≤(N:ℝ)^a) {β : ℝ} (hb : 0≤β) :
    (∀ e : ℝ, 0<e → ∃ᶠ N : ℕ in atTop,
      symmetricMoebiusEnergy N (H N) ≤ (N:ℝ)^(2*(β+e))) ↔ zetaZeroWidth≤β :=
  ⟨width_le_of_single_expanding_window hH hb,fun hw _ he => (expanding_window_upper hH hs hw he).frequently⟩

/-- Every order strictly below the zero width is exceeded at every
large cutoff, for any divergent schedule, however slowly it expands. -/
theorem expanding_window_lower {H : ℕ → ℝ} (hH : Tendsto H atTop atTop)
    {b : ℝ} (hb : 0≤b) (hbw : b<zetaZeroWidth) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)^(2*b) < symmetricMoebiusEnergy N (H N) := by
  by_contra hn
  have fail : ∃ᶠ N : ℕ in atTop, symmetricMoebiusEnergy N (H N) ≤ (N:ℝ)^(2*b) := by
    simpa only [Filter.Frequently,not_le] using hn
  apply hbw.not_ge
  apply width_le_of_single_expanding_window hH hb
  intro e he
  apply (fail.and_eventually (eventually_ge_atTop 1)).mono
  rintro N ⟨h,hN⟩
  exact h.trans (Real.rpow_le_rpow_of_exponent_le ((Nat.one_le_cast (α:=ℝ)).mpr hN)
    (by linarith only [he]))

/-- The ordinary logarithmic growth order of one symmetric pure
Möbius energy is precisely twice the actual zero width. -/
theorem pure_moebius_single_window_log_order {H : ℕ → ℝ} (hH : Tendsto H atTop atTop)
    (hs : ∀ a : ℝ, 0<a → ∀ᶠ N : ℕ in atTop, 1+H N≤(N:ℝ)^a) :
    Tendsto (fun N : ℕ => Real.log (max 1 (symmetricMoebiusEnergy N (H N)))/Real.log (N:ℝ))
      atTop (𝓝 (2*zetaZeroWidth)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    by_cases hb0 : b<0
    · filter_upwards [eventually_ge_atTop 2] with N hN
      exact hb0.trans_le (div_nonneg (Real.log_nonneg (le_max_left ..))
        (Real.log_nonneg (Nat.one_le_cast.mpr (by omega : 1≤N))))
    · have hw : b/2<zetaZeroWidth := by linarith only [hb]
      filter_upwards [expanding_window_lower hH (half_nonneg (le_of_not_gt hb0)) hw,
        eventually_ge_atTop 2] with N h hN
      have hx : 1<(N:ℝ) := by exact_mod_cast (by omega : 1<N)
      have ht := Real.log_lt_log (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _) (h.trans_le (le_max_right 1 _))
      rw [Real.log_rpow (zero_lt_one.trans hx)] at ht
      apply (lt_div_iff₀ (Real.log_pos hx)).mpr
      rwa [show 2*(b/2)=b by ring] at ht
  · intro b hb
    let e := (b-2*zetaZeroWidth)/4
    have he : 0<e := by dsimp only [e]; linarith only [hb]
    have hc : 2*(zetaZeroWidth+e)<b := by dsimp only [e]; linarith only [hb]
    filter_upwards [expanding_window_upper hH hs le_rfl he,eventually_ge_atTop 2] with N h hN
    have hx : 1<(N:ℝ) := by exact_mod_cast (by omega : 1<N)
    have hbig := Real.one_le_rpow hx.le (show 0≤2*(zetaZeroWidth+e) by linarith only [zetaZeroWidth_nonneg,he])
    have hl := Real.log_le_log (zero_lt_one.trans_le (le_max_left 1 _)) (max_le hbig h)
    rw [Real.log_rpow (zero_lt_one.trans hx)] at hl
    exact (div_lt_iff₀ (Real.log_pos hx)).mpr (hl.trans_lt (mul_lt_mul_of_pos_right hc (Real.log_pos hx)))

theorem log_height_subpower {a : ℝ} (ha : 0<a) :
    ∀ᶠ N : ℕ in atTop, 1+Real.log (N:ℝ)≤(N:ℝ)^a := by
  have h₁ := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    ((Real.isLittleO_log_rpow_atTop ha).bound (by norm_num : 0<(1/2:ℝ)))
  have h₂ := ((tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 2
  filter_upwards [h₁,h₂,eventually_ge_atTop 1] with N h hbig hN
  have hx : 1≤(N:ℝ) := Nat.one_le_cast.mpr hN
  change ‖Real.log (N:ℝ)‖ ≤ (1/2:ℝ)*‖(N:ℝ)^a‖ at h
  rw [Real.norm_of_nonneg (Real.log_nonneg hx),Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) a)] at h
  linarith only [h,hbig]

/-- A single prescribed window through height log N yields an RH
criterion using only the pure Möbius polynomial. The cutoffs for
distinct epsilon losses may be chosen independently. -/
theorem rh_iff_log_height_moebius_energy :
    RiemannHypothesis ↔ ∀ e : ℝ, 0<e → ∃ᶠ N : ℕ in atTop,
      symmetricMoebiusEnergy N (Real.log (N:ℝ)) ≤ (N:ℝ)^(2*e) := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero,
    ←zetaZeroWidth_le_iff_xiZeroHalfPlaneBound le_rfl]
  simpa only [zero_add] using (single_subpower_window_iff
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
    (fun _ h => log_height_subpower h) (β:=0) le_rfl).symm

#print axioms rh_iff_log_height_moebius_energy
#print axioms pure_moebius_single_window_log_order
#print axioms local_error_paid_by_pure_window
#print axioms width_le_of_single_expanding_window
#print axioms single_subpower_window_iff
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
