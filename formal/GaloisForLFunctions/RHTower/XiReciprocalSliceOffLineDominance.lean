import GaloisForLFunctions.RHTower.XiReciprocalSliceDominance
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Reciprocal slice positivity fails only near off-line zeros

At a height `t` with `Ξ(t) ≠ 0`, the pair product splits as
`h_t(σ)/h_t(0) = Π_{critical z} (1 − σ²/(z − t)²) · Π_{off-line z} (1 − σ²/(z − t)²)`.
The critical factor has reciprocal coefficients that are a Pólya frequency sequence of every order
(`evenRecipPF_critical_except`).  Only the off-line factor can spoil positivity.

**Theorem** (`xiReciprocalSlicePositive_of_offLine_dominance`).  Let `γ` be a real zero of `Ξ` and
`d = |t − γ|`.  If `d² Σ_{off-line z} 1/|z − t|² ≤ 1/20`, then every Taylor coefficient of
`1/(Ξ(t+σ)Ξ(t−σ))` at `0` is nonnegative.  No condition is imposed on the other critical zeros.

**Failure localization** (`offLine_mass_gt_of_not_xiReciprocalSlicePositive`).  If reciprocal
slice positivity fails at `t`, then for every real zero `γ` the off-line zeros carry inverse-square
mass `Σ_{off-line z} 1/|z − t|² > 1/(20 (t − γ)²)`.  Under RH there are no off-line zeros and
positivity holds at every height.

Proof.  Write `1/h_t = h_t(0)^{−1} · A · B`.  Here `A` is the reciprocal of `(1 − σ²/d²)` times the
other critical factors: its coefficients `a_n ≥ 0` satisfy `a_{n−j} ≤ d^{2j} a_n`.  And
`B = 1/Π_{off-line}` has `|B| ≤ e^{3/10}` on `|σ| = √3 d`, hence `|b_j| ≤ e^{3/10}/(3d²)^j` by
Cauchy's estimate.  Then `Re Σ_j a_{n−j} b_j ≥ a_n (1 − e^{3/10}/2) ≥ 0`.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder Nat
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A zero copy is critical when its spectral point is real. -/
def XiCopyCritical (q : XiZeroCopy) : Prop := (xiSpectralPoint q).im = 0

/-- The factor `1 − σ²/(z_q − t)²` written as `1 + f`. -/
def sliceFactorTerm (t : ℝ) (q : XiZeroCopy) (σ : ℂ) : ℂ := -(σ ^ 2 / (xiSpectralPoint q - t) ^ 2)

theorem norm_sliceFactorTerm (t : ℝ) (q : XiZeroCopy) (σ : ℂ) :
    ‖sliceFactorTerm t q σ‖ = ‖σ‖ ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) := by
  unfold sliceFactorTerm
  rw [norm_neg, norm_div, norm_pow, norm_pow]
  ring

theorem summable_norm_sliceFactorTerm (t : ℝ) (σ : ℂ) (p : XiZeroCopy → Prop) :
    Summable (fun q : {q // p q} => ‖sliceFactorTerm t q.1 σ‖) := by
  have h := (summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)).mul_left (‖σ‖ ^ 2)
  refine (h.comp_injective Subtype.val_injective).congr fun q => ?_
  simp only [Function.comp_apply, norm_sliceFactorTerm]

/-- The product of the factors over a predicate. -/
def slicePartialProduct (t : ℝ) (p : XiZeroCopy → Prop) (σ : ℂ) : ℂ :=
  ∏' q : {q // p q}, (1 + sliceFactorTerm t q.1 σ)

theorem hasProd_slicePartialProduct (t : ℝ) (p : XiZeroCopy → Prop) (σ : ℂ) :
    HasProd (fun q : {q // p q} => 1 + sliceFactorTerm t q.1 σ) (slicePartialProduct t p σ) :=
  (multipliable_one_add_of_summable (summable_norm_sliceFactorTerm t σ p)).hasProd

open scoped Classical in
/-- Filtered finite products converge to the predicate product. -/
theorem tendsto_prod_filter_slicePartialProduct (t : ℝ) (p : XiZeroCopy → Prop) (σ : ℂ) :
    Tendsto (fun S : Finset XiZeroCopy => ∏ q ∈ S with p q, (1 + sliceFactorTerm t q σ)) atTop
      (𝓝 (slicePartialProduct t p σ)) := by
  have h0 : HasProd (fun q : ↥({q | p q} : Set XiZeroCopy) => 1 + sliceFactorTerm t q.1 σ)
      (slicePartialProduct t p σ) := hasProd_slicePartialProduct t p σ
  have h := (hasProd_subtype_iff_mulIndicator (f := fun q => 1 + sliceFactorTerm t q σ)).mp h0
  refine h.congr fun S => ?_
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun q _ => ?_
  by_cases hq : p q <;> simp [hq]

/-- Locally uniform convergence of a predicate product on a disk. -/
theorem hasProdLocallyUniformlyOn_slicePartialProduct (t : ℝ) (p : XiZeroCopy → Prop) (R : ℝ) :
    HasProdLocallyUniformlyOn (fun (q : {q // p q}) (σ : ℂ) => 1 + sliceFactorTerm t q.1 σ)
      (slicePartialProduct t p) (ball (0 : ℂ) R) := by
  have hu : Summable (fun q : {q // p q} => R ^ 2 * (1 / ‖xiSpectralPoint q.1 - t‖ ^ 2)) :=
    ((summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)).comp_injective
      Subtype.val_injective).mul_left _
  have h := Summable.hasProdLocallyUniformlyOn_one_add (f := fun (q : {q // p q}) σ =>
    sliceFactorTerm t q.1 σ) (K := ball (0 : ℂ) R) isOpen_ball hu
    (Eventually.of_forall fun (q : {q // p q}) (σ : ℂ) (hσ : σ ∈ ball (0 : ℂ) R) => ?_)
    (fun q => by unfold sliceFactorTerm; fun_prop)
  · exact h
  · rw [norm_sliceFactorTerm]
    have hσ' : ‖σ‖ < R := by simpa using hσ
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg σ) hσ'.le 2

/-- The whole product is the normalized pair product. -/
theorem slicePartialProduct_mul_eq {t : ℝ} (ht : XiC t ≠ 0) {q₀ : XiZeroCopy}
    (hq₀ : XiCopyCritical q₀) (σ : ℂ) :
    (1 + sliceFactorTerm t q₀ σ) *
        (slicePartialProduct t (fun q => XiCopyCritical q ∧ q ≠ q₀) σ *
          slicePartialProduct t (fun q => ¬ XiCopyCritical q) σ) =
      xiHorizontalPair t σ / xiHorizontalPair t 0 := by
  classical
  have hfull := tendsto_prod_one_sub_sq_div ht σ
  have hc := tendsto_prod_filter_slicePartialProduct t (fun q => XiCopyCritical q ∧ q ≠ q₀) σ
  have ho := tendsto_prod_filter_slicePartialProduct t (fun q => ¬ XiCopyCritical q) σ
  have hprod := (hc.mul ho).const_mul (1 + sliceFactorTerm t q₀ σ)
  refine tendsto_nhds_unique hprod (hfull.congr' ?_)
  filter_upwards [eventually_ge_atTop {q₀}] with S hS
  have hmem : q₀ ∈ S := hS (Finset.mem_singleton_self q₀)
  have hq₀c : ∀ q ∈ S, (1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2) = 1 + sliceFactorTerm t q σ :=
    fun q _ => by unfold sliceFactorTerm; ring
  rw [Finset.prod_congr rfl hq₀c]
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun q => q = q₀)]
  have h1 : (S.filter fun q => q = q₀) = {q₀} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · rintro rfl
      exact ⟨hmem, rfl⟩
  rw [h1, Finset.prod_singleton]
  congr 1
  rw [← Finset.prod_filter_mul_prod_filter_not (S.filter fun q => ¬ q = q₀) XiCopyCritical,
    Finset.filter_filter, Finset.filter_filter]
  have e1 : (S.filter fun q => ¬ q = q₀ ∧ XiCopyCritical q) =
      S.filter fun q => XiCopyCritical q ∧ q ≠ q₀ := by
    ext q
    simp only [Finset.mem_filter]
    tauto
  have e2 : (S.filter fun q => ¬ q = q₀ ∧ ¬ XiCopyCritical q) =
      S.filter fun q => ¬ XiCopyCritical q := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h, -, h'⟩
      exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      refine ⟨h, fun hq => h' (hq ▸ hq₀), h'⟩
  rw [e1, e2]
  congr 1 <;> exact Finset.prod_congr (by ext; simp) (fun _ _ => rfl)

/-- Finite products over a subtype are finite products over the image. -/
theorem prod_subtype_eq_prod_map {p : XiZeroCopy → Prop} (S : Finset {q // p q})
    (g : XiZeroCopy → ℂ) :
    ∏ q ∈ S, g q.1 = ∏ q ∈ S.map (Function.Embedding.subtype p), g q := by
  rw [Finset.prod_map]
  rfl

open scoped Classical in
/-- A uniform lower bound for products over a predicate on a small disk. -/
theorem norm_slicePartialProduct_ge {t : ℝ} (ht : XiC t ≠ 0) (p : XiZeroCopy → Prop)
    {σ : ℂ} {r M : ℝ} (hσ : ‖σ‖ ≤ r) (hr : ∀ q, p q → r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2)
    (hM : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, p q) →
      2 * r ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ M) :
    Real.exp (-M) ≤ ‖slicePartialProduct t p σ‖ := by
  have h := tendsto_prod_filter_slicePartialProduct t p σ
  refine ge_of_tendsto h.norm (Eventually.of_forall fun S => ?_)
  have hF : ∀ q ∈ S.filter p, p q := fun q hq => (Finset.mem_filter.mp hq).2
  have hb := norm_prod_one_sub_sq_div_ge (S.filter p) hσ (fun q hq => hr q (hF q hq))
    (fun q _ => xiSpectralPoint_ne_ofReal ht q)
  have e : ∏ q ∈ S.filter p, (1 + sliceFactorTerm t q σ) =
      ∏ q ∈ S.filter p, (1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2) := by
    refine Finset.prod_congr rfl fun q _ => ?_
    unfold sliceFactorTerm
    ring
  rw [e]
  refine le_trans ?_ hb
  apply Real.exp_le_exp.mpr
  have := hM _ hF
  linarith

/-- **The critical factor is reciprocally totally positive.**  The product over the critical zero
copies other than `q₀` is even-reciprocally `PF_∞`. -/
theorem evenRecipPF_critical_except {t : ℝ} (ht : XiC t ≠ 0) (q₀ : XiZeroCopy) :
    EvenRecipPF (slicePartialProduct t (fun q => XiCopyCritical q ∧ q ≠ q₀)) := by
  classical
  set p : XiZeroCopy → Prop := fun q => XiCopyCritical q ∧ q ≠ q₀ with hp
  set St : ℝ := ∑' q, 1 / ‖xiSpectralPoint q - t‖ ^ 2 with hSt
  have hsum := summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)
  have hS0 : 0 ≤ St := tsum_nonneg fun q => by positivity
  set R : ℝ := 1 / (2 * (St + 1)) with hR
  have hR0 : 0 < R := by positivity
  have hR2 : R ^ 2 ≤ 1 / (4 * (St + 1)) := by
    rw [hR, div_pow, one_pow, mul_pow]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have hsq : ∀ q, R ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2 := by
    intro q
    have hle : 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ St :=
      hsum.le_tsum q (fun j _ => by positivity)
    rw [div_eq_mul_one_div]
    calc R ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) ≤ 1 / (4 * (St + 1)) * St :=
          mul_le_mul hR2 hle (by positivity) (by positivity)
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hM : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, p q) →
      2 * R ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 := by
    intro F _
    have hle : ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ St :=
      hsum.sum_le_tsum F (fun j _ => by positivity)
    calc 2 * R ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 2 * (1 / (4 * (St + 1))) * St :=
          mul_le_mul (by linarith) hle (Finset.sum_nonneg fun q _ => by positivity) (by positivity)
      _ ≤ 1 := by
          rw [show 2 * (1 / (4 * (St + 1))) * St = St / (2 * (St + 1)) by field_simp; ring,
            div_le_one (by positivity)]
          linarith
  -- the finite products
  set U : Finset {q // p q} → ℂ → ℂ := fun S σ => ∏ q ∈ S, (1 + sliceFactorTerm t q.1 σ) with hU
  have hfac : ∀ q : {q // p q}, EvenRecipPF (fun σ => 1 + sliceFactorTerm t q.1 σ) := by
    intro q
    obtain ⟨hcrit, -⟩ := q.2
    unfold XiCopyCritical at hcrit
    set x : ℝ := (xiSpectralPoint q.1).re with hx
    have hz : xiSpectralPoint q.1 = (x : ℂ) := Complex.ext (by simp [hx]) (by simpa using hcrit)
    have hne : x - t ≠ 0 := by
      intro h
      apply xiSpectralPoint_ne_ofReal ht q.1
      rw [hz]
      congr 1
      linarith
    set a : ℝ := (x - t) ^ 2 with ha
    have ha0 : 0 < a := by positivity
    have e : (fun σ => 1 + sliceFactorTerm t q.1 σ) = fun σ : ℂ => 1 - σ ^ 2 / (a : ℂ) := by
      funext σ
      unfold sliceFactorTerm
      rw [hz, ha]
      push_cast
      ring
    rw [e]
    exact EvenRecipPF.one_sub_sq_div ha0
  have hUpf : ∀ S, EvenRecipPF (U S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa [hU] using EvenRecipPF.one
    | insert q S hq ih =>
      have e : U (insert q S) = (fun σ => 1 + sliceFactorTerm t q.1 σ) * U S := by
        funext σ
        simp only [hU, Pi.mul_apply, Finset.prod_insert hq]
      rw [e]
      exact (hfac q).mul ih
  have hUd : ∀ S, DifferentiableOn ℂ (U S) (ball 0 R) := by
    intro S
    refine (Differentiable.differentiableOn ?_)
    simp only [hU]
    refine Differentiable.fun_finsetProd fun q _ => ?_
    unfold sliceFactorTerm
    fun_prop
  have hUne : ∀ S, ∀ σ ∈ ball (0 : ℂ) R, U S σ ≠ 0 := by
    intro S σ hσ h0
    have hσ' : ‖σ‖ ≤ R := by simpa using (mem_ball_zero_iff.mp hσ).le
    have hb := norm_prod_one_sub_sq_div_ge (S.map (Function.Embedding.subtype p)) hσ'
      (fun q _ => hsq q) (fun q _ => xiSpectralPoint_ne_ofReal ht q)
    have e : U S σ = ∏ q ∈ S.map (Function.Embedding.subtype p),
        (1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2) := by
      simp only [hU]
      rw [prod_subtype_eq_prod_map S (fun q => 1 + sliceFactorTerm t q σ)]
      refine Finset.prod_congr rfl fun q _ => ?_
      unfold sliceFactorTerm
      ring
    rw [← e, h0, norm_zero] at hb
    exact absurd hb (not_le.mpr (Real.exp_pos _))
  have hconv : TendstoLocallyUniformlyOn U (slicePartialProduct t p) atTop (ball 0 R) :=
    hasProdLocallyUniformlyOn_slicePartialProduct t p R
  have hud : DifferentiableOn ℂ (slicePartialProduct t p) (ball 0 R) :=
    hconv.differentiableOn (Eventually.of_forall hUd) isOpen_ball
  have hune : ∀ σ ∈ ball (0 : ℂ) R, slicePartialProduct t p σ ≠ 0 := by
    intro σ hσ h0
    have hσ' : ‖σ‖ ≤ R := by simpa using (mem_ball_zero_iff.mp hσ).le
    have hb := norm_slicePartialProduct_ge ht p hσ' (fun q _ => hsq q) hM
    rw [h0, norm_zero] at hb
    exact absurd hb (not_le.mpr (Real.exp_pos _))
  exact EvenRecipPF.of_tendstoLocallyUniformlyOn hR0 hUpf hUd hUne hud hune hconv

theorem slicePartialProduct_zero (t : ℝ) (p : XiZeroCopy → Prop) :
    slicePartialProduct t p 0 = 1 := by
  simp [slicePartialProduct, sliceFactorTerm]

/-- The value `h_t(0) = Ξ(t)²` is a positive real number. -/
theorem xiHorizontalPair_zero_eq_ofReal {t : ℝ} :
    xiHorizontalPair t 0 = (((XiC t).re ^ 2 : ℝ) : ℂ) := by
  have hreal : (XiC t).im = 0 := by
    have h := XiC_conj (t : ℂ)
    rw [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  unfold xiHorizontalPair
  rw [add_zero, sub_zero]
  apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im, hreal]

/-- **Off-line dominance.**  If `γ` is a real zero of `Ξ` and the off-line zeros satisfy
`(t − γ)² Σ_{off-line z} 1/|z − t|² ≤ 1/20`, then every Taylor coefficient of `1/(Ξ(t+σ)Ξ(t−σ))`
at `0` is nonnegative. -/
theorem xiReciprocalSlicePositive_of_offLine_dominance {t γ : ℝ} (ht : XiC t ≠ 0)
    (q₀ : XiZeroCopy) (hq₀ : xiSpectralPoint q₀ = (γ : ℂ))
    (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q) →
      (t - γ) ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 20) :
    XiReciprocalSlicePositive t := by
  set d : ℝ := t - γ with hd
  have hγ0 : XiC (γ : ℂ) = 0 := by rw [← hq₀]; exact XiC_xiSpectralPoint_eq_zero q₀
  have hd0 : d ≠ 0 := by
    intro h
    apply ht
    rw [show t = γ by linarith [h]]
    exact hγ0
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hd2 : 0 < d ^ 2 := by positivity
  have hq₀c : XiCopyCritical q₀ := by
    unfold XiCopyCritical
    rw [hq₀, Complex.ofReal_im]
  set Pc := slicePartialProduct t (fun q => XiCopyCritical q ∧ q ≠ q₀) with hPcdef
  set Po := slicePartialProduct t (fun q => ¬ XiCopyCritical q) with hPodef
  have hPc := evenRecipPF_critical_except ht q₀
  set Afun : ℂ → ℂ := fun σ => (1 - σ ^ 2 / ((d ^ 2 : ℝ) : ℂ)) * Pc σ with hAfun
  have hA : EvenRecipPF Afun := (EvenRecipPF.one_sub_sq_div hd2).mul hPc
  have hh0 : xiHorizontalPair t 0 = (((XiC t).re ^ 2 : ℝ) : ℂ) := xiHorizontalPair_zero_eq_ofReal
  have hXre : (XiC t).re ≠ 0 := by
    intro h
    apply ht
    have hreal : (XiC t).im = 0 := by
      have h := XiC_conj (t : ℂ)
      rw [Complex.conj_ofReal] at h
      have := congrArg Complex.im h
      simp only [Complex.conj_im] at this
      linarith
    exact Complex.ext h hreal
  have hh0ne : xiHorizontalPair t 0 ≠ 0 := by
    rw [hh0]
    exact_mod_cast pow_ne_zero 2 hXre
  have hid : ∀ σ, xiHorizontalPair t σ = xiHorizontalPair t 0 * (Afun σ * Po σ) := by
    intro σ
    have h := slicePartialProduct_mul_eq ht hq₀c σ
    have hf : 1 + sliceFactorTerm t q₀ σ = 1 - σ ^ 2 / ((d ^ 2 : ℝ) : ℂ) := by
      unfold sliceFactorTerm
      rw [hq₀, hd]
      push_cast
      ring
    rw [hf, eq_div_iff hh0ne] at h
    simp only [hAfun]
    rw [← h]
    ring
  -- the off-line factor on the disk `|σ| ≤ √3 d`
  set r : ℝ := Real.sqrt 3 * |d| with hr
  have hr2 : r ^ 2 = 3 * d ^ 2 := by
    rw [hr, mul_pow, Real.sq_sqrt (by norm_num), sq_abs]
  have hrpos : 0 < r := by positivity
  have hsingle : ∀ q, ¬ XiCopyCritical q → d ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 20 := by
    intro q hq
    have := hS {q} (by simpa using hq)
    simpa [div_eq_mul_inv] using this
  have hpos_off : ∀ q, ¬ XiCopyCritical q → 20 * d ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 := by
    intro q hq
    have hpos : 0 < ‖xiSpectralPoint q - t‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q))) 2
    have := hsingle q hq
    rw [div_le_iff₀ hpos] at this
    linarith
  have hbound : ∀ σ : ℂ, ‖σ‖ ≤ r → Real.exp (-(3 / 10)) ≤ ‖Po σ‖ := by
    intro σ hσ
    refine norm_slicePartialProduct_ge ht _ hσ (fun q hq => ?_) (fun F hF => ?_)
    · have hpos : 0 < ‖xiSpectralPoint q - t‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q))) 2
      rw [hr2, div_le_iff₀ hpos]
      have := hpos_off q hq
      linarith
    · have := hS F hF
      rw [hr2]
      nlinarith
  have hPone : ∀ σ : ℂ, ‖σ‖ ≤ r → Po σ ≠ 0 := fun σ hσ h => by
    have := hbound σ hσ
    rw [h, norm_zero] at this
    exact absurd this (not_le.mpr (Real.exp_pos _))
  -- differentiability of the off-line factor near the disk
  have hPodiff : DifferentiableOn ℂ Po (ball 0 (2 * |d|)) := by
    have hconv : TendstoLocallyUniformlyOn (fun (S : Finset {q // ¬ XiCopyCritical q}) σ =>
        ∏ q ∈ S, (1 + sliceFactorTerm t q.1 σ)) Po atTop (ball 0 (2 * |d|)) :=
      hasProdLocallyUniformlyOn_slicePartialProduct t _ _
    refine hconv.differentiableOn (Eventually.of_forall fun S => ?_) isOpen_ball
    refine Differentiable.differentiableOn ?_
    refine Differentiable.fun_finsetProd fun q _ => ?_
    unfold sliceFactorTerm
    fun_prop
  have hr_lt : r < 2 * |d| := by
    rw [hr]
    have h3 : Real.sqrt 3 < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have := abs_pos.mpr hd0
    nlinarith
  have hdiffOn : DifferentiableOn ℂ (fun σ => (Po σ)⁻¹) (closure (ball (0 : ℂ) r)) := by
    rw [closure_ball _ hrpos.ne']
    intro σ hσ
    have hσ' : ‖σ‖ ≤ r := by simpa using hσ
    have hσb : σ ∈ ball (0 : ℂ) (2 * |d|) := by
      rw [mem_ball_zero_iff]
      linarith
    exact ((hPodiff σ hσb).differentiableAt (isOpen_ball.mem_nhds hσb)).inv
      (hPone σ hσ') |>.differentiableWithinAt
  have hcauchy : ∀ n, ‖iteratedDeriv n (fun σ => (Po σ)⁻¹) 0‖ ≤
      n ! * Real.exp (3 / 10) / r ^ n := by
    intro n
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hrpos
      hdiffOn.diffContOnCl fun σ hσ => ?_
    have hσr : ‖σ‖ = r := by simpa using hσ
    rw [norm_inv]
    have := hbound σ hσr.le
    calc ‖Po σ‖⁻¹ ≤ (Real.exp (-(3 / 10)))⁻¹ := inv_anti₀ (Real.exp_pos _) this
      _ = Real.exp (3 / 10) := by rw [Real.exp_neg, inv_inv]
  set b : ℕ → ℂ := evenCoeffC (fun σ => (Po σ)⁻¹) with hb
  have hb0 : b 0 = 1 := by
    simp [hb, evenCoeffC, hPodef, slicePartialProduct_zero]
  have hbbound : ∀ k, ‖b k‖ ≤ Real.exp (3 / 10) / (3 * d ^ 2) ^ k := by
    intro k
    have h := hcauchy (2 * k)
    simp only [hb, evenCoeffC, norm_mul, norm_inv, Complex.norm_natCast]
    have hfac : (0 : ℝ) < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [inv_mul_le_iff₀ hfac]
    calc ‖iteratedDeriv (2 * k) (fun σ => (Po σ)⁻¹) 0‖ ≤ (2 * k) ! * Real.exp (3 / 10) / r ^ (2 * k) := h
      _ = ((2 * k).factorial : ℝ) * (Real.exp (3 / 10) / (3 * d ^ 2) ^ k) := by
          rw [pow_mul, hr2]
          ring
  have hPoA : AnalyticAt ℂ (fun σ => (Po σ)⁻¹) 0 := by
    have hσb : (0 : ℂ) ∈ ball (0 : ℂ) (2 * |d|) := mem_ball_self (by positivity)
    exact ((hPodiff.analyticAt (isOpen_ball.mem_nhds hσb))).inv (hPone 0 (by simp; positivity))
  -- the critical coefficients and their domination
  set A : ℕ → ℝ := evenRecipCoeff Afun with hAdef
  set A' : ℕ → ℝ := evenRecipCoeff Pc with hA'def
  have hA'nn : ∀ k, 0 ≤ A' k := by
    intro k
    have := hPc.pf 1 1 le_rfl (fun _ => 0) (fun _ => k) (Subsingleton.strictMono _)
      (Subsingleton.strictMono _)
    simpa [toeplitzMinor, Matrix.det_unique, zext_natCast] using this
  have hAconv : ∀ m, A m = ∑ i ∈ Finset.range (m + 1), (1 / d ^ 2) ^ i * A' (m - i) := by
    intro m
    have hinvA : (fun σ => (Afun σ)⁻¹) =
        recipQuad (1 / ((d ^ 2 : ℝ) : ℂ)) * fun σ => (Pc σ)⁻¹ := by
      funext σ
      simp only [hAfun, Pi.mul_apply, recipQuad, mul_inv]
      congr 2
      ring
    have hQ := analyticAt_recipQuad (1 / ((d ^ 2 : ℝ) : ℂ))
    have hQo := iteratedDeriv_recipQuad_odd (1 / ((d ^ 2 : ℝ) : ℂ))
    have h := evenCoeffC_mul hQ hPc.analyticAt_inv hQo m
    rw [← hinvA] at h
    have hre := congrArg Complex.re h
    simp only [evenCoeffC] at hre
    rw [hA.coeff_real, Complex.ofReal_re, Complex.re_sum] at hre
    rw [hAdef, hre]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hq := evenCoeffC_recipQuad (1 / ((d ^ 2 : ℝ) : ℂ)) i
    simp only [evenCoeffC] at hq
    rw [hq, hPc.coeff_real]
    have : (1 / ((d ^ 2 : ℝ) : ℂ)) ^ i = (((1 / d ^ 2) ^ i : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hAnn : ∀ m, 0 ≤ A m := by
    intro m
    rw [hAconv m]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hA'nn _)
  have hdom : ∀ n i, i ≤ n → (1 / d ^ 2) ^ i * A (n - i) ≤ A n := by
    intro n i hin
    rw [hAconv n, hAconv (n - i), Finset.mul_sum]
    have hsplit : ∑ k ∈ Finset.range (n + 1), (1 / d ^ 2) ^ k * A' (n - k) =
        ∑ k ∈ Finset.range i, (1 / d ^ 2) ^ k * A' (n - k) +
          ∑ k ∈ Finset.range (n - i + 1), (1 / d ^ 2) ^ (i + k) * A' (n - (i + k)) := by
      rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ n + 1 by omega),
        Finset.sum_Ico_eq_sum_range, show n + 1 - i = n - i + 1 by omega]
    rw [hsplit]
    have h1 : 0 ≤ ∑ k ∈ Finset.range i, (1 / d ^ 2) ^ k * A' (n - k) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hA'nn _)
    have h2 : ∑ k ∈ Finset.range (n - i + 1), (1 / d ^ 2) ^ i * ((1 / d ^ 2) ^ k * A' (n - i - k)) =
        ∑ k ∈ Finset.range (n - i + 1), (1 / d ^ 2) ^ (i + k) * A' (n - (i + k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add, show n - i - k = n - (i + k) by omega]
      ring
    linarith
  -- the coefficient formula
  have hinv_eq : (fun σ => (xiHorizontalPair t σ)⁻¹) =
      (fun _ => (xiHorizontalPair t 0)⁻¹) * ((fun σ => (Afun σ)⁻¹) * fun σ => (Po σ)⁻¹) := by
    funext σ
    simp only [Pi.mul_apply]
    rw [hid σ, mul_inv, mul_inv]
  have hconstA : AnalyticAt ℂ (fun _ : ℂ => (xiHorizontalPair t 0)⁻¹) 0 := analyticAt_const
  have hconstO : ∀ k : ℕ, iteratedDeriv (2 * k + 1) (fun _ : ℂ => (xiHorizontalPair t 0)⁻¹) 0 = 0 :=
    fun k => by rw [iteratedDeriv_const]; simp
  have hcoef : ∀ n, evenCoeffC (fun σ => (xiHorizontalPair t σ)⁻¹) n =
      (xiHorizontalPair t 0)⁻¹ * ∑ j ∈ Finset.range (n + 1), ((A j : ℝ) : ℂ) * b (n - j) := by
    intro n
    rw [hinv_eq, evenCoeffC_mul hconstA (hA.analyticAt_inv.mul hPoA) hconstO]
    rw [Finset.sum_eq_single 0]
    · simp only [evenCoeffC, mul_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
        iteratedDeriv_zero, Nat.sub_zero]
      congr 1
      have := evenCoeffC_mul hA.analyticAt_inv hPoA hA.odd n
      simp only [evenCoeffC] at this ⊢
      rw [this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hA.coeff_real]
      rfl
    · intro j _ hj
      simp only [evenCoeffC]
      rw [iteratedDeriv_const, if_neg (by omega), mul_zero, zero_mul]
    · intro h
      simp at h
  have hsumre : ∀ n, 0 ≤ (∑ j ∈ Finset.range (n + 1), ((A j : ℝ) : ℂ) * b (n - j)).re := by
    intro n
    rw [Complex.re_sum]
    simp only [Complex.re_ofReal_mul]
    rw [← Finset.sum_range_reflect]
    have hre : ∀ i ∈ Finset.range (n + 1), A (n + 1 - 1 - i) * (b (n - (n + 1 - 1 - i))).re =
        A (n - i) * (b i).re := by
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show n + 1 - 1 - i = n - i by omega, show n - (n - i) = i by omega]
    rw [Finset.sum_congr rfl hre, Finset.sum_range_succ', Nat.sub_zero, hb0, Complex.one_re,
      mul_one]
    have htail : |∑ i ∈ Finset.range n, A (n - (i + 1)) * (b (i + 1)).re| ≤
        A n * (Real.exp (3 / 10) / 2) := by
      calc |∑ i ∈ Finset.range n, A (n - (i + 1)) * (b (i + 1)).re|
          ≤ ∑ i ∈ Finset.range n, |A (n - (i + 1)) * (b (i + 1)).re| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range n, A n * (Real.exp (3 / 10) * (1 / 3) ^ (i + 1)) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hin : i + 1 ≤ n := Finset.mem_range.mp hi
            rw [abs_mul, abs_of_nonneg (hAnn _)]
            have h1 := (Complex.abs_re_le_norm (b (i + 1))).trans (hbbound (i + 1))
            have h2 := hdom n (i + 1) hin
            have hd2' : (0 : ℝ) < (1 / d ^ 2) ^ (i + 1) := by positivity
            have h3 : A (n - (i + 1)) ≤ (d ^ 2) ^ (i + 1) * A n := by
              have : (d ^ 2) ^ (i + 1) * ((1 / d ^ 2) ^ (i + 1) * A (n - (i + 1))) =
                  A (n - (i + 1)) := by
                rw [← mul_assoc, ← mul_pow, mul_one_div_cancel hd2.ne', one_pow, one_mul]
              rw [← this]
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
            calc A (n - (i + 1)) * |(b (i + 1)).re|
                ≤ ((d ^ 2) ^ (i + 1) * A n) * (Real.exp (3 / 10) / (3 * d ^ 2) ^ (i + 1)) :=
                  mul_le_mul h3 h1 (abs_nonneg _) (mul_nonneg (by positivity) (hAnn n))
              _ = A n * (Real.exp (3 / 10) * (1 / 3) ^ (i + 1)) := by
                  rw [mul_pow]
                  field_simp
                  rw [mul_assoc, ← mul_pow]
                  norm_num
        _ = A n * Real.exp (3 / 10) * ∑ i ∈ Finset.range n, (1 / 3 : ℝ) ^ (i + 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ ≤ A n * Real.exp (3 / 10) * (1 / 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hAnn n) (Real.exp_pos _).le)
            have hg := geom_sum_eq (show (1 / 3 : ℝ) ≠ 1 by norm_num) n
            have : ∑ i ∈ Finset.range n, (1 / 3 : ℝ) ^ (i + 1) =
                (1 / 3) * ∑ i ∈ Finset.range n, (1 / 3 : ℝ) ^ i := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
            have hg' : ((1 / 3 : ℝ) ^ n - 1) / (1 / 3 - 1) = 3 / 2 * (1 - (1 / 3) ^ n) := by
              field_simp
              ring
            rw [this, hg, hg']
            have hp : 0 < (1 / 3 : ℝ) ^ n := by positivity
            linarith
        _ = A n * (Real.exp (3 / 10) / 2) := by ring
    have hexp := exp_three_tenths_lt_two
    have := (abs_le.mp htail).1
    have hAn := hAnn n
    nlinarith
  intro n
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hc := hcoef m
    simp only [evenCoeffC] at hc
    have hfac : (((2 * m).factorial : ℂ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hD : iteratedDeriv (2 * m) (fun σ => (xiHorizontalPair t σ)⁻¹) 0 =
        ((2 * m).factorial : ℂ) * ((xiHorizontalPair t 0)⁻¹ *
          ∑ j ∈ Finset.range (m + 1), ((A j : ℝ) : ℂ) * b (m - j)) := by
      rw [← hc]
      field_simp
    rw [Complex.nonneg_iff]
    constructor
    · rw [hD, hh0, ← Complex.ofReal_inv]
      have hcast : ((2 * m).factorial : ℂ) = (((2 * m).factorial : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
      exact mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr (by positivity))) (hsumre m)
    · exact (im_iteratedDeriv_inv_xiHorizontalPair t (2 * m)).symm
  · rw [iteratedDeriv_inv_xiHorizontalPair_odd]

/-- **Reciprocal slice positivity fails only near off-line zeros.**  If positivity fails at a
height `t` with `Ξ(t) ≠ 0`, then for every real zero `γ`, some finite family of off-line zeros
carries inverse-square mass greater than `1/(20 (t − γ)²)`. -/
theorem offLine_mass_gt_of_not_xiReciprocalSlicePositive {t γ : ℝ} (ht : XiC t ≠ 0)
    (hfail : ¬ XiReciprocalSlicePositive t) (q₀ : XiZeroCopy) (hq₀ : xiSpectralPoint q₀ = (γ : ℂ)) :
    ∃ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q) ∧
      1 / 20 < (t - γ) ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 := by
  by_contra h
  push Not at h
  exact hfail (xiReciprocalSlicePositive_of_offLine_dominance ht q₀ hq₀ h)

/-- Without off-line zeros, the hypothesis is empty: RH gives reciprocal slice positivity at every
height through any real zero. -/
theorem xiReciprocalSlicePositive_of_no_offLine {t γ : ℝ} (ht : XiC t ≠ 0)
    (hcrit : ∀ q : XiZeroCopy, XiCopyCritical q) (q₀ : XiZeroCopy)
    (hq₀ : xiSpectralPoint q₀ = (γ : ℂ)) : XiReciprocalSlicePositive t := by
  refine xiReciprocalSlicePositive_of_offLine_dominance ht q₀ hq₀ fun F hF => ?_
  rcases F.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simp
  · exact absurd (hcrit q) (hF q hq)

end

end RHTower
