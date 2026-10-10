import GaloisForLFunctions.RHTower.XiReciprocalSliceOrderKDominance
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Near-line off-line zeros act as double critical zeros on the reciprocal slice

At a height `t` with `Ξ(t) ≠ 0`, an off-line zero `z = γ + iδ` of `Ξ` comes with its mirror
`z̄ = γ − iδ`.  Write `c = z − t`.  The pair contributes the factor
`(1 − σ²/c²)(1 − σ²/c̄²)` to `h_t(σ) = Ξ(t+σ)Ξ(t−σ)`.  Rotating both points onto the real axis
replaces it by the double critical factor `(1 − σ²/|c|²)²`.  The defect of this rotation is exactly

  `(1 − u/|c|²)² − (1 − u/c²)(1 − u/c̄²) = u (c − c̄)²/|c|⁴ = −4u δ²/|c|⁴`,  `u = σ²`,

which is **second order** in the displacement `δ` from the critical line (`norm_pairRatio_le`).

**Theorem** (`pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_nearDouble`).  Let `k ≥ 1`.  Let
`C₀` be a set of at least `k` critical zero copies within distance `D` of `t`.  Suppose every
off-line zero lies at distance at least `3kD` from `t`, and

  `D² Σ_{off-line z} (Im z)²/|z − t|⁴ ≤ 1/(100 k³)`.

Then the even reciprocal coefficients of `Ξ(t+σ)Ξ(t−σ)` form a `PF_k` sequence, and the slice lift
is reciprocally totally positive of order `k`
(`reciprocalTPUpTo_xiSliceLift_of_offLine_nearDouble`).

Compared with first-order dominance (`pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_sparse`,
mass `Σ 1/|z − t|²`), each off-line zero is now weighted by the extra factor `(δ/|z − t|)²`.
Off-line zeros close to the critical line are invisible to reciprocal total positivity unless
they are among the nearest zeros to `t`.  Only exposed off-line zeros, and off-line zeros far from
the line, can make the slice fail.

Proof.  Split `1/h_t = h_t(0)^{−1} · [1/(C · A)] · [A/O]`.  Here `C` is the critical product and
`O` the off-line product.  `A` is the product of the rotated factors `1 − σ²/|z − t|²` over the
off-line copies.  The first bracket is a limit of geometric products.  For the second, reindexing
the off-line copies by critical-line conjugation (`xiZeroCopyLineConjEquiv`) gives
`O² = Π (1 − σ²/c²)(1 − σ²/c̄²)`.  So `(A/O)² = Π (pair ratio)`, and
`|A/O| ≤ exp(8 s² Σ δ²/|c|⁴)` on `|σ| = s`.  Cauchy estimates at `s = 2kD` and the perturbation
law `toeplitzMinor_cauchyConv_ge_of_perturbation` finish as in first-order dominance.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The pair ratio -/

/-- **The pair ratio is second order in the displacement.**  For `c ≠ 0` and `‖u‖ ≤ ‖c‖²/2`,
`‖(1 − u/|c|²)² / ((1 − u/c²)(1 − u/c̄²))‖ ≤ 1 + 16 ‖u‖ (Im c)²/‖c‖⁴`. -/
theorem norm_pairRatio_le {u c : ℂ} (hc : c ≠ 0) (hu : ‖u‖ ≤ ‖c‖ ^ 2 / 2) :
    ‖(1 - u / ((‖c‖ ^ 2 : ℝ) : ℂ)) ^ 2 /
        ((1 - u / c ^ 2) * (1 - u / (starRingEnd ℂ c) ^ 2))‖ ≤
      1 + 16 * ‖u‖ * c.im ^ 2 / ‖c‖ ^ 4 := by
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hcc : starRingEnd ℂ c ≠ 0 := (map_ne_zero _).mpr hc
  have hnorm : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * starRingEnd ℂ c := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsmall : ‖u‖ / ‖c‖ ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hA : 1 / 2 ≤ ‖1 - u / c ^ 2‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (u / c ^ 2)
    rw [norm_one, norm_div, norm_pow] at h1
    linarith
  have hB : 1 / 2 ≤ ‖1 - u / (starRingEnd ℂ c) ^ 2‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (u / (starRingEnd ℂ c) ^ 2)
    rw [norm_one, norm_div, norm_pow, Complex.norm_conj] at h1
    linarith
  have hAne : (1 - u / c ^ 2) ≠ 0 := fun h => by rw [h, norm_zero] at hA; linarith
  have hBne : (1 - u / (starRingEnd ℂ c) ^ 2) ≠ 0 := fun h => by
    rw [h, norm_zero] at hB; linarith
  have hdef : (1 - u / ((‖c‖ ^ 2 : ℝ) : ℂ)) ^ 2 =
      (1 - u / c ^ 2) * (1 - u / (starRingEnd ℂ c) ^ 2) +
        u * (c - starRingEnd ℂ c) ^ 2 / (c * starRingEnd ℂ c) ^ 2 := by
    rw [hnorm]
    field_simp
    ring
  have hdefn : ‖u * (c - starRingEnd ℂ c) ^ 2 / (c * starRingEnd ℂ c) ^ 2‖ =
      4 * ‖u‖ * c.im ^ 2 / ‖c‖ ^ 4 := by
    rw [Complex.sub_conj, norm_div, norm_mul, norm_pow, norm_pow, norm_mul, norm_mul,
      Complex.norm_I, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, mul_one, abs_mul,
      mul_pow, sq_abs]
    norm_num
    ring
  rw [hdef, add_div, div_self (mul_ne_zero hAne hBne)]
  calc ‖1 + u * (c - starRingEnd ℂ c) ^ 2 / (c * starRingEnd ℂ c) ^ 2 /
        ((1 - u / c ^ 2) * (1 - u / (starRingEnd ℂ c) ^ 2))‖
      ≤ 1 + ‖u * (c - starRingEnd ℂ c) ^ 2 / (c * starRingEnd ℂ c) ^ 2‖ /
          (‖1 - u / c ^ 2‖ * ‖1 - u / (starRingEnd ℂ c) ^ 2‖) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_one, norm_div, norm_mul]
    _ ≤ 1 + (4 * ‖u‖ * c.im ^ 2 / ‖c‖ ^ 4) / (1 / 2 * (1 / 2)) := by
        rw [hdefn]
        gcongr
    _ = 1 + 16 * ‖u‖ * c.im ^ 2 / ‖c‖ ^ 4 := by ring

/-! ## The rotated off-line product -/

/-- The factor `1 − σ²/|z_q − t|²` written as `1 + f`: the zero copy rotated onto the real axis
about `t`. -/
def sliceProjTerm (t : ℝ) (q : XiZeroCopy) (σ : ℂ) : ℂ :=
  -(σ ^ 2 / ((‖xiSpectralPoint q - t‖ ^ 2 : ℝ) : ℂ))

theorem norm_sliceProjTerm (t : ℝ) (q : XiZeroCopy) (σ : ℂ) :
    ‖sliceProjTerm t q σ‖ = ‖σ‖ ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) := by
  unfold sliceProjTerm
  rw [norm_neg, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  ring

theorem summable_norm_sliceProjTerm (t : ℝ) (σ : ℂ) (p : XiZeroCopy → Prop) :
    Summable (fun q : {q // p q} => ‖sliceProjTerm t q.1 σ‖) := by
  have h := (summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)).mul_left (‖σ‖ ^ 2)
  refine (h.comp_injective Subtype.val_injective).congr fun q => ?_
  simp only [Function.comp_apply, norm_sliceProjTerm]

/-- The product of the rotated factors over a predicate. -/
def sliceProjProduct (t : ℝ) (p : XiZeroCopy → Prop) (σ : ℂ) : ℂ :=
  ∏' q : {q // p q}, (1 + sliceProjTerm t q.1 σ)

theorem hasProd_sliceProjProduct (t : ℝ) (p : XiZeroCopy → Prop) (σ : ℂ) :
    HasProd (fun q : {q // p q} => 1 + sliceProjTerm t q.1 σ) (sliceProjProduct t p σ) :=
  (multipliable_one_add_of_summable (summable_norm_sliceProjTerm t σ p)).hasProd

open scoped Classical in
/-- Filtered finite products converge to the rotated product. -/
theorem tendsto_prod_filter_sliceProjProduct (t : ℝ) (p : XiZeroCopy → Prop) (σ : ℂ) :
    Tendsto (fun S : Finset XiZeroCopy => ∏ q ∈ S with p q, (1 + sliceProjTerm t q σ)) atTop
      (𝓝 (sliceProjProduct t p σ)) := by
  have h0 : HasProd (fun q : ↥({q | p q} : Set XiZeroCopy) => 1 + sliceProjTerm t q.1 σ)
      (sliceProjProduct t p σ) := hasProd_sliceProjProduct t p σ
  have h := (hasProd_subtype_iff_mulIndicator (f := fun q => 1 + sliceProjTerm t q σ)).mp h0
  refine h.congr fun S => ?_
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun q _ => ?_
  by_cases hq : p q <;> simp [hq]

theorem hasProdLocallyUniformlyOn_sliceProjProduct (t : ℝ) (p : XiZeroCopy → Prop) (R : ℝ) :
    HasProdLocallyUniformlyOn (fun (q : {q // p q}) (σ : ℂ) => 1 + sliceProjTerm t q.1 σ)
      (sliceProjProduct t p) (ball (0 : ℂ) R) := by
  have hu : Summable (fun q : {q // p q} => R ^ 2 * (1 / ‖xiSpectralPoint q.1 - t‖ ^ 2)) :=
    ((summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)).comp_injective
      Subtype.val_injective).mul_left _
  have h := Summable.hasProdLocallyUniformlyOn_one_add (f := fun (q : {q // p q}) σ =>
    sliceProjTerm t q.1 σ) (K := ball (0 : ℂ) R) isOpen_ball hu
    (Eventually.of_forall fun (q : {q // p q}) (σ : ℂ) (hσ : σ ∈ ball (0 : ℂ) R) => ?_)
    (fun q => by unfold sliceProjTerm; fun_prop)
  · exact h
  · rw [norm_sliceProjTerm]
    have hσ' : ‖σ‖ < R := by simpa using hσ
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg σ) hσ'.le 2

theorem differentiable_sliceProjProduct (t : ℝ) (p : XiZeroCopy → Prop) :
    Differentiable ℂ (sliceProjProduct t p) := by
  intro σ
  have hd : DifferentiableOn ℂ (sliceProjProduct t p) (ball 0 (‖σ‖ + 1)) :=
    (hasProdLocallyUniformlyOn_sliceProjProduct t p (‖σ‖ + 1)).differentiableOn
      (Eventually.of_forall fun S =>
        (Differentiable.fun_finsetProd fun q _ => by
          unfold sliceProjTerm; fun_prop).differentiableOn) isOpen_ball
  exact hd.differentiableAt (isOpen_ball.mem_nhds (by simp))

theorem sliceProjProduct_zero (t : ℝ) (p : XiZeroCopy → Prop) :
    sliceProjProduct t p 0 = 1 := by
  simp [sliceProjProduct, sliceProjTerm]

/-- A rotated factor is `1 − σ²/a` with `a = |z − t|² > 0`. -/
theorem one_add_sliceProjTerm_eq {t : ℝ} (ht : XiC t ≠ 0) (q : XiZeroCopy) :
    0 < ‖xiSpectralPoint q - t‖ ^ 2 ∧
      (fun σ => 1 + sliceProjTerm t q σ) =
        fun σ : ℂ => 1 - σ ^ 2 / ((‖xiSpectralPoint q - t‖ ^ 2 : ℝ) : ℂ) := by
  have hpos : 0 < ‖xiSpectralPoint q - t‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q))
  refine ⟨by positivity, funext fun σ => ?_⟩
  unfold sliceProjTerm
  ring

/-- A lower bound for a finite product of rotated factors. -/
theorem norm_prod_one_add_sliceProjTerm_ge {t : ℝ} (F : Finset XiZeroCopy) {σ : ℂ} {r : ℝ}
    (hσ : ‖σ‖ ≤ r) (hr : ∀ q ∈ F, r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2) :
    Real.exp (-(2 * r ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2)) ≤
      ‖∏ q ∈ F, (1 + sliceProjTerm t q σ)‖ := by
  rw [norm_prod, Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod (fun q _ => (Real.exp_pos _).le) fun q hq => ?_
  have hx : ‖sliceProjTerm t q σ‖ ≤ r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 := by
    rw [norm_sliceProjTerm, mul_one_div]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg σ) hσ 2) (by positivity)
  have hy := hr q hq
  have h1 := norm_add_le (1 + sliceProjTerm t q σ) (-sliceProjTerm t q σ)
  rw [add_neg_cancel_right, norm_one, norm_neg] at h1
  calc Real.exp (-(2 * r ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)))
      = Real.exp (-(2 * (r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2))) := by ring_nf
    _ ≤ 1 - r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 :=
        exp_neg_two_mul_le_one_sub (by positivity) hy
    _ ≤ ‖1 + sliceProjTerm t q σ‖ := by linarith

open scoped Classical in
/-- A uniform lower bound for rotated products over a predicate on a small disk. -/
theorem norm_sliceProjProduct_ge (t : ℝ) (p : XiZeroCopy → Prop) {σ : ℂ} {r M : ℝ}
    (hσ : ‖σ‖ ≤ r) (hr : ∀ q, p q → r ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2)
    (hM : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, p q) →
      2 * r ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ M) :
    Real.exp (-M) ≤ ‖sliceProjProduct t p σ‖ := by
  refine ge_of_tendsto (tendsto_prod_filter_sliceProjProduct t p σ).norm
    (Eventually.of_forall fun S => ?_)
  have hF : ∀ q ∈ S.filter p, p q := fun q hq => (Finset.mem_filter.mp hq).2
  refine le_trans ?_ (norm_prod_one_add_sliceProjTerm_ge (S.filter p) hσ
    fun q hq => hr q (hF q hq))
  exact Real.exp_le_exp.mpr (by linarith [hM _ hF])

/-- A radius on which every slice factor is small. -/
theorem exists_slice_small_radius (t : ℝ) : ∃ R : ℝ, 0 < R ∧
    (∀ q, R ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2) ∧
    ∀ F : Finset XiZeroCopy, 2 * R ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 := by
  set St : ℝ := ∑' q, 1 / ‖xiSpectralPoint q - t‖ ^ 2 with hSt
  have hsum := summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)
  have hS0 : 0 ≤ St := tsum_nonneg fun q => by positivity
  set R : ℝ := 1 / (2 * (St + 1)) with hR
  have hR2 : R ^ 2 ≤ 1 / (4 * (St + 1)) := by
    rw [hR, div_pow, one_pow, mul_pow]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  refine ⟨R, by positivity, fun q => ?_, fun F => ?_⟩
  · have hle : 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ St := hsum.le_tsum q (fun j _ => by positivity)
    rw [div_eq_mul_one_div]
    calc R ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) ≤ 1 / (4 * (St + 1)) * St :=
          mul_le_mul hR2 hle (by positivity) (by positivity)
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  · have hle : ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ St :=
      hsum.sum_le_tsum F (fun j _ => by positivity)
    calc 2 * R ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 2 * (1 / (4 * (St + 1))) * St :=
          mul_le_mul (by linarith) hle (Finset.sum_nonneg fun q _ => by positivity) (by positivity)
      _ ≤ 1 := by
          rw [show 2 * (1 / (4 * (St + 1))) * St = St / (2 * (St + 1)) by field_simp; ring,
            div_le_one (by positivity)]
          linarith

/-- **The rotated product is reciprocally totally positive.** -/
theorem evenRecipPF_sliceProjProduct {t : ℝ} (ht : XiC t ≠ 0) (p : XiZeroCopy → Prop) :
    EvenRecipPF (sliceProjProduct t p) := by
  classical
  obtain ⟨R, hR0, hsq, hM⟩ := exists_slice_small_radius t
  set U : Finset {q // p q} → ℂ → ℂ := fun S σ => ∏ q ∈ S, (1 + sliceProjTerm t q.1 σ) with hU
  have hfac : ∀ q : {q // p q}, EvenRecipPF (fun σ => 1 + sliceProjTerm t q.1 σ) := fun q => by
    obtain ⟨hpos, he⟩ := one_add_sliceProjTerm_eq ht q.1
    rw [he]
    exact EvenRecipPF.one_sub_sq_div hpos
  have hUpf : ∀ S, EvenRecipPF (U S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa [hU] using EvenRecipPF.one
    | insert q S hq ih =>
      have e : U (insert q S) = (fun σ => 1 + sliceProjTerm t q.1 σ) * U S := by
        funext σ
        simp only [hU, Pi.mul_apply, Finset.prod_insert hq]
      rw [e]
      exact (hfac q).mul ih
  have hUd : ∀ S, DifferentiableOn ℂ (U S) (ball 0 R) := fun S =>
    (Differentiable.fun_finsetProd fun q _ => by unfold sliceProjTerm; fun_prop).differentiableOn
  have hUne : ∀ S, ∀ σ ∈ ball (0 : ℂ) R, U S σ ≠ 0 := by
    intro S σ hσ h0
    have hσ' : ‖σ‖ ≤ R := by simpa using (mem_ball_zero_iff.mp hσ).le
    have hb := norm_prod_one_add_sliceProjTerm_ge (S.map (Function.Embedding.subtype p)) hσ'
      (fun q _ => hsq q)
    rw [Finset.prod_map] at hb
    change Real.exp _ ≤ ‖U S σ‖ at hb
    rw [h0, norm_zero] at hb
    exact absurd hb (not_le.mpr (Real.exp_pos _))
  have hconv : TendstoLocallyUniformlyOn U (sliceProjProduct t p) atTop (ball 0 R) :=
    hasProdLocallyUniformlyOn_sliceProjProduct t p R
  have hune : ∀ σ ∈ ball (0 : ℂ) R, sliceProjProduct t p σ ≠ 0 := by
    intro σ hσ h0
    have hσ' : ‖σ‖ ≤ R := by simpa using (mem_ball_zero_iff.mp hσ).le
    have hb := norm_sliceProjProduct_ge t p hσ' (fun q _ => hsq q) (fun F _ => hM F)
    rw [h0, norm_zero] at hb
    exact absurd hb (not_le.mpr (Real.exp_pos _))
  exact EvenRecipPF.of_tendstoLocallyUniformlyOn hR0 hUpf hUd hUne
    (differentiable_sliceProjProduct t p).differentiableOn hune hconv

/-- The even reciprocal coefficients of the finite rotated products converge. -/
theorem tendsto_evenRecipCoeff_sliceProjProduct {t : ℝ} (p : XiZeroCopy → Prop) (n : ℕ) :
    Tendsto (fun S : Finset {q // p q} =>
      evenRecipCoeff (fun σ => ∏ q ∈ S, (1 + sliceProjTerm t q.1 σ)) n) atTop
      (𝓝 (evenRecipCoeff (sliceProjProduct t p) n)) := by
  classical
  obtain ⟨R, hR0, hsq, hM⟩ := exists_slice_small_radius t
  set U : Finset {q // p q} → ℂ → ℂ := fun S σ => ∏ q ∈ S, (1 + sliceProjTerm t q.1 σ) with hU
  have hUd : ∀ S, DifferentiableOn ℂ (U S) (ball 0 R) := fun S =>
    (Differentiable.fun_finsetProd fun q _ => by unfold sliceProjTerm; fun_prop).differentiableOn
  have hUne : ∀ S, ∀ σ ∈ ball (0 : ℂ) R, U S σ ≠ 0 := by
    intro S σ hσ h0
    have hσ' : ‖σ‖ ≤ R := by simpa using (mem_ball_zero_iff.mp hσ).le
    have hb := norm_prod_one_add_sliceProjTerm_ge (S.map (Function.Embedding.subtype p)) hσ'
      (fun q _ => hsq q)
    rw [Finset.prod_map] at hb
    change Real.exp _ ≤ ‖U S σ‖ at hb
    rw [h0, norm_zero] at hb
    exact absurd hb (not_le.mpr (Real.exp_pos _))
  have hune : ∀ σ ∈ ball (0 : ℂ) R, sliceProjProduct t p σ ≠ 0 := by
    intro σ hσ h0
    have hσ' : ‖σ‖ ≤ R := by simpa using (mem_ball_zero_iff.mp hσ).le
    have hb := norm_sliceProjProduct_ge t p hσ' (fun q _ => hsq q) (fun F _ => hM F)
    rw [h0, norm_zero] at hb
    exact absurd hb (not_le.mpr (Real.exp_pos _))
  exact tendsto_evenRecipCoeff_of_tendstoLocallyUniformlyOn hR0 hUd hUne
    (differentiable_sliceProjProduct t p).differentiableOn hune
    (hasProdLocallyUniformlyOn_sliceProjProduct t p R) n

/-! ## The off-line ratio -/

/-- Critical-line conjugation preserves being off-line. -/
theorem xiCopyCritical_lineConj_iff (q : XiZeroCopy) :
    XiCopyCritical (xiZeroCopyLineConjEquiv q) ↔ XiCopyCritical q := by
  unfold XiCopyCritical
  rw [xiSpectralPoint_lineConj, Complex.conj_im, neg_eq_zero]

open scoped Classical in
/-- **The rotated off-line ratio is second order in the displacements.**  On `|σ| ≤ s`, if every
off-line copy has `s²/|z − t|² ≤ 1/2` and `16 s² Σ (Im z)²/|z − t|⁴ ≤ 2M`, then
`|A(σ)/O(σ)| ≤ e^M`.  Here `A` is the rotated and `O` the true off-line product. -/
theorem norm_sliceProjProduct_mul_inv_le {t : ℝ} (ht : XiC t ≠ 0) {σ : ℂ} {s M : ℝ}
    (hσ : ‖σ‖ ≤ s)
    (hr : ∀ q, ¬ XiCopyCritical q → s ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2)
    (hE : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q) →
      16 * s ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 ≤ 2 * M) :
    ‖sliceProjProduct t (fun q => ¬ XiCopyCritical q) σ *
        (slicePartialProduct t (fun q => ¬ XiCopyCritical q) σ)⁻¹‖ ≤ Real.exp M := by
  obtain ⟨poff, hpoff⟩ : ∃ poff : XiZeroCopy → Prop, poff = fun q => ¬ XiCopyCritical q :=
    ⟨_, rfl⟩
  rw [← hpoff]
  obtain ⟨Lc, hLc⟩ : ∃ Lc : XiZeroCopy ≃ XiZeroCopy, Lc = xiZeroCopyLineConjEquiv := ⟨_, rfl⟩
  have hoff_iff : ∀ q, poff (Lc q) ↔ poff q := fun q => by
    rw [hpoff, hLc]
    exact not_congr (xiCopyCritical_lineConj_iff q)
  have hconj : ∀ q, xiSpectralPoint (Lc q) - t = starRingEnd ℂ (xiSpectralPoint q - t) := by
    intro q
    rw [hLc, xiSpectralPoint_lineConj, map_sub, Complex.conj_ofReal]
  -- the true off-line product does not vanish on the disk
  have hsum := summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)
  have hOne : slicePartialProduct t poff σ ≠ 0 := by
    intro h0
    have hb := norm_slicePartialProduct_ge ht poff hσ (fun q hq => hr q (by rw [hpoff] at hq; exact hq))
      (M := 2 * s ^ 2 * ∑' q, 1 / ‖xiSpectralPoint q - t‖ ^ 2) (fun F _ => by
        have h1 := hsum.sum_le_tsum F (fun j _ => by positivity)
        have h2 : (0 : ℝ) ≤ 2 * s ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left h1 h2)
    rw [h0, norm_zero] at hb
    exact absurd hb (not_le.mpr (Real.exp_pos _))
  -- three finite-product limits
  have hO := tendsto_prod_filter_slicePartialProduct t poff σ
  have hA := tendsto_prod_filter_sliceProjProduct t poff σ
  have hmap : Tendsto (fun S : Finset XiZeroCopy => S.map Lc.toEmbedding) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun T => ⟨T.map Lc.symm.toEmbedding, fun S hS x hx => ?_⟩
    rw [Finset.mem_map]
    exact ⟨Lc.symm x, hS (Finset.mem_map.mpr ⟨x, hx, rfl⟩), by simp⟩
  have hO' : Tendsto (fun S : Finset XiZeroCopy =>
      ∏ q ∈ S with poff q, (1 + sliceFactorTerm t (Lc q) σ)) atTop
      (𝓝 (slicePartialProduct t poff σ)) := by
    refine (hO.comp hmap).congr fun S => ?_
    simp only [Function.comp_apply]
    rw [Finset.filter_map, Finset.prod_map]
    refine Finset.prod_congr (Finset.filter_congr fun q _ => ?_) fun q _ => rfl
    exact hoff_iff q
  have hlim := (hA.pow 2).div (hO.mul hO') (mul_ne_zero hOne hOne)
  -- every finite pair product is bounded
  have hbound : ∀ S : Finset XiZeroCopy,
      ‖(∏ q ∈ S with poff q, (1 + sliceProjTerm t q σ)) ^ 2 /
        ((∏ q ∈ S with poff q, (1 + sliceFactorTerm t q σ)) *
          ∏ q ∈ S with poff q, (1 + sliceFactorTerm t (Lc q) σ))‖ ≤ Real.exp (2 * M) := by
    intro S
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib, norm_prod]
    calc ∏ q ∈ S with poff q, ‖(1 + sliceProjTerm t q σ) ^ 2 /
          ((1 + sliceFactorTerm t q σ) * (1 + sliceFactorTerm t (Lc q) σ))‖
        ≤ ∏ q ∈ S with poff q, Real.exp (16 * s ^ 2 *
            ((xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4)) := by
          refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q hq => ?_
          have hq' : poff q := (Finset.mem_filter.mp hq).2
          have hc : xiSpectralPoint q - t ≠ 0 := sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q)
          have hcn : 0 < ‖xiSpectralPoint q - t‖ := norm_pos_iff.mpr hc
          have hσ2 : ‖σ ^ 2‖ ≤ s ^ 2 := by
            rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hσ 2
          have hu : ‖σ ^ 2‖ ≤ ‖xiSpectralPoint q - t‖ ^ 2 / 2 := by
            have h1 := hr q (by rw [hpoff] at hq'; exact hq')
            rw [div_le_iff₀ (by positivity)] at h1
            linarith
          have e : (1 + sliceProjTerm t q σ) ^ 2 /
              ((1 + sliceFactorTerm t q σ) * (1 + sliceFactorTerm t (Lc q) σ)) =
              (1 - σ ^ 2 / ((‖xiSpectralPoint q - t‖ ^ 2 : ℝ) : ℂ)) ^ 2 /
                ((1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2) *
                  (1 - σ ^ 2 / (starRingEnd ℂ (xiSpectralPoint q - t)) ^ 2)) := by
            unfold sliceProjTerm sliceFactorTerm
            rw [hconj q]
            ring
          rw [e]
          refine (norm_pairRatio_le hc hu).trans ?_
          have him : (xiSpectralPoint q - t).im = (xiSpectralPoint q).im := by simp
          rw [him]
          have h1 := Real.add_one_le_exp (16 * s ^ 2 *
            ((xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4))
          have h2 : 16 * ‖σ ^ 2‖ * (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 ≤
              16 * s ^ 2 * ((xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4) := by
            rw [mul_div_assoc]
            gcongr
          linarith
      _ = Real.exp (16 * s ^ 2 *
            ∑ q ∈ S with poff q, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4) := by
          rw [Finset.mul_sum, Real.exp_sum]
      _ ≤ Real.exp (2 * M) := Real.exp_le_exp.mpr (hE _ fun q hq => by
          have := (Finset.mem_filter.mp hq).2
          rw [hpoff] at this
          exact this)
  have hsq := le_of_tendsto hlim.norm (Eventually.of_forall hbound)
  have e2 : ‖sliceProjProduct t poff σ * (slicePartialProduct t poff σ)⁻¹‖ ^ 2 =
      ‖sliceProjProduct t poff σ ^ 2 /
        (slicePartialProduct t poff σ * slicePartialProduct t poff σ)‖ := by
    rw [← norm_pow]
    congr 1
    field_simp
  have h3 : ‖sliceProjProduct t poff σ * (slicePartialProduct t poff σ)⁻¹‖ ^ 2 ≤
      Real.exp M ^ 2 := by
    rw [e2, ← Real.exp_nat_mul]
    push_cast
    exact hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp h3

/-! ## Near-double dominance -/

/-- Geometric products of a concatenation. -/
theorem geomProdSeq_append (xs ys : List ℝ) :
    geomProdSeq (xs ++ ys) = cauchyConv (geomProdSeq xs) (geomProdSeq ys) := by
  have hx : geomProdSeq xs = fun n => PowerSeries.coeff n (xs.map geomPowerSeries).prod := rfl
  have hy : geomProdSeq ys = fun n => PowerSeries.coeff n (ys.map geomPowerSeries).prod := rfl
  rw [hx, hy, cauchyConv_coeff]
  funext n
  simp only [geomProdSeq, List.map_append, List.prod_append]

/-- **Order-`k` near-double dominance.**  Let `k ≥ 1` and let `C₀` be a set of at least `k`
critical zero copies within distance `D` of `t`.  If every off-line copy lies at distance at least
`3kD` from `t` and `D² Σ_{off-line} (Im z)²/|z − t|⁴ ≤ 1/(100k³)`, then the even reciprocal
coefficients of `Ξ(t+σ)Ξ(t−σ)` form a `PF_k` sequence. -/
theorem pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_nearDouble {t : ℝ} (ht : XiC t ≠ 0)
    {k : ℕ} (hk : 1 ≤ k) (C₀ : Finset XiZeroCopy) (hC₀ : ∀ q ∈ C₀, XiCopyCritical q)
    (hk₀ : k ≤ C₀.card) {D : ℝ} (hD : ∀ q ∈ C₀, ‖xiSpectralPoint q - t‖ ≤ D)
    (hfar : ∀ q, ¬ XiCopyCritical q → 3 * k * D ≤ ‖xiSpectralPoint q - t‖)
    (hoff : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q) →
      D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 ≤
        1 / (100 * k ^ 3)) :
    PFSeq k (evenRecipCoeff (xiHorizontalPair t)) := by
  classical
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨q₀, hq₀⟩ : C₀.Nonempty := Finset.card_pos.mp (by omega)
  have hq₀c := hC₀ q₀ hq₀
  have hDpos : 0 < D := lt_of_lt_of_le
    (norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal ht q₀))) (hD q₀ hq₀)
  -- the factors
  obtain ⟨p', hp'⟩ : ∃ p' : XiZeroCopy → Prop, p' = fun q => XiCopyCritical q ∧ q ≠ q₀ :=
    ⟨_, rfl⟩
  obtain ⟨poff, hpoff⟩ : ∃ poff : XiZeroCopy → Prop, poff = fun q => ¬ XiCopyCritical q :=
    ⟨_, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C' : ℂ → ℂ, C' = slicePartialProduct t p' := ⟨_, rfl⟩
  obtain ⟨Coff, hCoff⟩ : ∃ Coff : ℂ → ℂ, Coff = slicePartialProduct t poff := ⟨_, rfl⟩
  obtain ⟨Aug, hAug⟩ : ∃ Aug : ℂ → ℂ, Aug = sliceProjProduct t poff := ⟨_, rfl⟩
  obtain ⟨ha₀, hf₀⟩ := one_add_sliceFactorTerm_eq_of_critical ht hq₀c
  obtain ⟨a₀, ha₀def⟩ : ∃ a₀ : ℝ, a₀ = ((xiSpectralPoint q₀).re - t) ^ 2 := ⟨_, rfl⟩
  rw [← ha₀def] at ha₀ hf₀
  obtain ⟨f₀, hf₀def⟩ : ∃ f₀ : ℂ → ℂ, f₀ = fun σ => 1 + sliceFactorTerm t q₀ σ := ⟨_, rfl⟩
  have hf₀pf : EvenRecipPF f₀ := by rw [hf₀def, hf₀]; exact EvenRecipPF.one_sub_sq_div ha₀
  have hf₀c : evenRecipCoeff f₀ = fun n => a₀⁻¹ ^ n := by
    rw [hf₀def, hf₀]; exact evenRecipCoeff_one_sub_sq_div ha₀
  have hC'pf : EvenRecipPF C' := by rw [hC', hp']; exact evenRecipPF_critical_except ht q₀
  have hAugpf : EvenRecipPF Aug := by rw [hAug]; exact evenRecipPF_sliceProjProduct ht poff
  obtain ⟨Ccrit, hCcrit⟩ : ∃ Ccrit : ℂ → ℂ, Ccrit = f₀ * C' := ⟨_, rfl⟩
  have hCcritpf : EvenRecipPF Ccrit := by rw [hCcrit]; exact hf₀pf.mul hC'pf
  obtain ⟨B, hB⟩ : ∃ B : ℂ → ℂ, B = Ccrit * Aug := ⟨_, rfl⟩
  have hBpf : EvenRecipPF B := by rw [hB]; exact hCcritpf.mul hAugpf
  obtain ⟨aB, haB⟩ : ∃ aB : ℕ → ℝ, aB = evenRecipCoeff B := ⟨_, rfl⟩
  have haB_eq : aB = cauchyConv (cauchyConv (fun n => a₀⁻¹ ^ n) (evenRecipCoeff C'))
      (evenRecipCoeff Aug) := by
    rw [haB, hB, evenRecipCoeff_mul hCcritpf hAugpf, hCcrit, evenRecipCoeff_mul hf₀pf hC'pf,
      hf₀c]
  -- the perturbation `A/O`
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun σ => Aug σ * (Coff σ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℂ, b = fun j =>
      (((2 * j).factorial : ℂ))⁻¹ * iteratedDeriv (2 * j) P 0 := ⟨_, rfl⟩
  obtain ⟨qs, hqs⟩ : ∃ qs : ℕ → ℝ, qs = fun j => (b j).re := ⟨_, rfl⟩
  have hCoff0 : Coff 0 = 1 := by rw [hCoff]; exact slicePartialProduct_zero t poff
  have hAug0 : Aug 0 = 1 := by rw [hAug]; exact sliceProjProduct_zero t poff
  have hP0 : P 0 = 1 := by rw [hP]; simp [hCoff0, hAug0]
  have hqs0 : qs 0 = 1 := by simp [hqs, hb, hP0]
  have hCoffd : Differentiable ℂ Coff := by
    rw [hCoff]; exact differentiable_slicePartialProduct t poff
  have hAugd : Differentiable ℂ Aug := by rw [hAug]; exact differentiable_sliceProjProduct t poff
  have hPan : AnalyticAt ℂ P 0 := by
    rw [hP]
    exact (hAugd.analyticAt 0).mul
      ((hCoffd.analyticAt 0).inv (by rw [hCoff0]; exact one_ne_zero))
  have hAugev : ∀ᶠ σ in 𝓝 (0 : ℂ), Aug σ ≠ 0 :=
    hAugd.continuous.continuousAt.eventually_ne (by rw [hAug0]; exact one_ne_zero)
  have hev : (fun σ => ((Ccrit * Coff) σ)⁻¹) =ᶠ[𝓝 0] (fun σ => (B σ)⁻¹) * P := by
    filter_upwards [hAugev] with σ hσ
    simp only [Pi.mul_apply, hB, hP]
    rw [mul_inv, mul_inv, mul_assoc, ← mul_assoc (Aug σ)⁻¹, inv_mul_cancel₀ hσ, one_mul]
  have hu_eq : evenRecipCoeff (Ccrit * Coff) = cauchyConv aB qs := by
    funext m
    unfold evenRecipCoeff cauchyConv
    rw [hev.iteratedDeriv_eq, factorial_inv_mul_iteratedDeriv_mul_even_of_analyticAt
      hBpf.analyticAt_inv hPan hBpf.odd, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hBpf.coeff_real, Complex.re_ofReal_mul, haB, hqs, hb]
  -- the pair product
  have hreal : (XiC (t : ℂ)).im = 0 := by
    have h := XiC_conj (t : ℂ)
    rw [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = (XiC (t : ℂ)).re ^ 2 := ⟨_, rfl⟩
  have hre0 : (XiC (t : ℂ)).re ≠ 0 := by
    intro h0
    apply ht
    exact Complex.ext (by simp [h0]) (by simp [hreal])
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  have hsplit : ∀ σ, xiHorizontalPair t σ = (c0 : ℂ) * (Ccrit * Coff) σ := by
    intro σ
    have h := slicePartialProduct_mul_eq ht hq₀c σ
    rw [xiHorizontalPair_zero_eq_ofReal, ← hc0] at h
    have hne : ((c0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0pos.ne'
    rw [eq_div_iff hne] at h
    rw [← h, hCcrit, hf₀def, hC', hCoff, hp', hpoff]
    simp only [Pi.mul_apply]
    ring
  have hcoef : evenRecipCoeff (xiHorizontalPair t) =
      fun n => c0⁻¹ * evenRecipCoeff (Ccrit * Coff) n := by
    funext n
    have hinv : (fun σ => (xiHorizontalPair t σ)⁻¹) =
        fun σ => ((c0 : ℂ))⁻¹ * ((Ccrit * Coff) σ)⁻¹ := by
      funext σ; rw [hsplit σ, mul_inv]
    unfold evenRecipCoeff
    rw [hinv, iteratedDeriv_const_mul_field, mul_left_comm, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul]
  rw [hcoef, hu_eq]
  refine PFSeq.const_mul ?_ (inv_nonneg.mpr hc0pos.le)
  -- the truncations
  obtain ⟨aq, haq⟩ : ∃ aq : XiZeroCopy → ℝ, aq = fun q => ((xiSpectralPoint q).re - t) ^ 2 :=
    ⟨_, rfl⟩
  have haqpos : ∀ q, XiCopyCritical q → 0 < aq q := fun q hq => by
    rw [haq]; exact (one_add_sliceFactorTerm_eq_of_critical ht hq).1
  have hcritp' : ∀ q, p' q → XiCopyCritical q := fun q hq => by rw [hp'] at hq; exact hq.1
  obtain ⟨pq, hpq⟩ : ∃ pq : XiZeroCopy → ℝ, pq = fun q => ‖xiSpectralPoint q - t‖ ^ 2 :=
    ⟨_, rfl⟩
  have hpqpos : ∀ q, 0 < pq q := fun q => by rw [hpq]; exact (one_add_sliceProjTerm_eq ht q).1
  obtain ⟨U, hU⟩ : ∃ U : Finset {q // p' q} → ℂ → ℂ,
      U = fun S σ => ∏ q ∈ S, (1 + sliceFactorTerm t q.1 σ) := ⟨_, rfl⟩
  have hU_eq : ∀ S, U S = oneSubSqProd (S.toList.map fun q => aq q.1) := by
    intro S
    funext σ
    simp only [hU, oneSubSqProd, List.map_map]
    rw [Finset.prod_map_toList]
    refine Finset.prod_congr rfl fun q _ => ?_
    have := congrFun (one_add_sliceFactorTerm_eq_of_critical ht (hcritp' q.1 q.2)).2 σ
    simp only [haq, Function.comp_apply]
    exact this
  have hUc : ∀ S, evenRecipCoeff (U S) =
      geomProdSeq ((S.toList.map fun q => aq q.1).map (·⁻¹)) := by
    intro S
    rw [hU_eq]
    refine (evenRecipPF_oneSubSqProd fun a ha => ?_).2
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
    exact haqpos q.1 (hcritp' q.1 q.2)
  obtain ⟨V, hV⟩ : ∃ V : Finset {q // poff q} → ℂ → ℂ,
      V = fun S σ => ∏ q ∈ S, (1 + sliceProjTerm t q.1 σ) := ⟨_, rfl⟩
  have hV_eq : ∀ S, V S = oneSubSqProd (S.toList.map fun q => pq q.1) := by
    intro S
    funext σ
    simp only [hV, oneSubSqProd, List.map_map]
    rw [Finset.prod_map_toList]
    refine Finset.prod_congr rfl fun q _ => ?_
    have := congrFun (one_add_sliceProjTerm_eq ht q.1).2 σ
    simp only [hpq, Function.comp_apply]
    exact this
  have hVc : ∀ S, evenRecipCoeff (V S) =
      geomProdSeq ((S.toList.map fun q => pq q.1).map (·⁻¹)) := by
    intro S
    rw [hV_eq]
    refine (evenRecipPF_oneSubSqProd fun a ha => ?_).2
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
    exact hpqpos q.1
  obtain ⟨L, hL⟩ : ∃ L : Finset {q // p' q} × Finset {q // poff q} → List ℝ,
      L = fun S => ((a₀ :: S.1.toList.map fun q => aq q.1) ++
        S.2.toList.map fun q => pq q.1).map (·⁻¹) := ⟨_, rfl⟩
  have hW : ∀ S, cauchyConv (cauchyConv (fun n => a₀⁻¹ ^ n) (evenRecipCoeff (U S.1)))
      (evenRecipCoeff (V S.2)) = geomProdSeq (L S) := by
    intro S
    rw [hUc, hVc, hL]
    simp only [List.map_append, List.map_cons]
    rw [geomProdSeq_append, cauchyConv_geometric_geomProdSeq]
  have hconvW : ∀ n, Tendsto (fun S => geomProdSeq (L S) n) (atTop ×ˢ atTop) (𝓝 (aB n)) := by
    intro n
    simp_rw [← hW]
    rw [haB_eq]
    unfold cauchyConv
    refine tendsto_finsetSum _ fun i _ => Tendsto.mul ?_ ?_
    · refine tendsto_finsetSum _ fun j _ => ?_
      have hlim := tendsto_evenRecipCoeff_slicePartialProduct ht p' (i - j)
      rw [← hC'] at hlim
      have := (hlim.comp (tendsto_fst (g := (atTop : Filter (Finset {q // poff q}))))).const_mul
        (a₀⁻¹ ^ j)
      simpa [hU] using this
    · have hlim := tendsto_evenRecipCoeff_sliceProjProduct (t := t) poff (n - i)
      rw [← hAug] at hlim
      have := hlim.comp (tendsto_snd (f := (atTop : Filter (Finset {q // p' q}))))
      simp only [hV]
      exact this
  -- sorted lists
  obtain ⟨Ls, hLs⟩ : ∃ Ls : Finset {q // p' q} × Finset {q // poff q} → List ℝ,
      Ls = fun S => (L S : Multiset ℝ).sort (· ≥ ·) := ⟨_, rfl⟩
  have hLs_perm : ∀ S, (Ls S).Perm (L S) := fun S => by
    rw [hLs]; exact Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
  have hLs_sorted : ∀ S, (Ls S).Pairwise (· ≥ ·) := fun S => by
    rw [hLs]; exact Multiset.pairwise_sort _ _
  have hL_nn : ∀ S, ∀ x ∈ L S, 0 ≤ x := by
    intro S x hx
    rw [hL, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact inv_nonneg.mpr ha₀.le
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
        exact inv_nonneg.mpr (haqpos q.1 (hcritp' q.1 q.2)).le
    · obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
      exact inv_nonneg.mpr (hpqpos q.1).le
  have hLs_nn : ∀ S, ∀ x ∈ Ls S, 0 ≤ x := fun S x hx => hL_nn S x ((hLs_perm S).subset hx)
  -- the large values
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (D ^ 2)⁻¹ := ⟨_, rfl⟩
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hinv_ge : ∀ q ∈ C₀, θ ≤ (aq q)⁻¹ := by
    intro q hq
    have hpos := haqpos q (hC₀ q hq)
    have hle : aq q ≤ D ^ 2 := by
      have e : aq q = ‖xiSpectralPoint q - t‖ ^ 2 := by
        rw [haq, norm_sq_eq_of_critical (hC₀ q hq)]
      rw [e]
      exact pow_le_pow_left₀ (norm_nonneg _) (hD q hq) 2
    rw [hθ]
    exact inv_anti₀ hpos hle
  obtain ⟨C₀', hC₀'⟩ : ∃ C₀' : Finset {q // p' q}, C₀' = (C₀.erase q₀).subtype p' := ⟨_, rfl⟩
  have hcard' : C₀'.card + 1 = C₀.card := by
    rw [hC₀', Finset.card_subtype]
    have hfilt : (C₀.erase q₀).filter p' = C₀.erase q₀ :=
      Finset.filter_true_of_mem fun q hq => by
        rw [hp']; exact ⟨hC₀ q (Finset.mem_of_mem_erase hq), Finset.ne_of_mem_erase hq⟩
    rw [hfilt, Finset.card_erase_of_mem hq₀]
    have := Finset.card_pos.mpr ⟨q₀, hq₀⟩
    omega
  have hcount : ∀ S : Finset {q // p' q} × Finset {q // poff q}, C₀' ⊆ S.1 →
      k ≤ ((Ls S).filter fun x => decide (θ ≤ x)).length := by
    intro S hS
    have ha₀θ : θ ≤ a₀⁻¹ := by
      have := hinv_ge q₀ hq₀
      rw [haq] at this
      simpa [ha₀def] using this
    rw [((hLs_perm S).filter _).length_eq, hL]
    simp only [List.map_append, List.map_cons, List.filter_append, List.length_append]
    rw [List.filter_cons_of_pos (by simpa using ha₀θ), List.length_cons, List.map_map,
      List.filter_map, List.length_map]
    have hsub : C₀' ⊆ (S.1.toList.filter
        ((fun x => decide (θ ≤ x)) ∘ (·⁻¹) ∘ fun q => aq q.1)).toFinset := by
      intro q hq
      rw [List.mem_toFinset, List.mem_filter, Finset.mem_toList]
      refine ⟨hS hq, ?_⟩
      have hq' : q.1 ∈ C₀ := by
        rw [hC₀', Finset.mem_subtype] at hq
        exact Finset.mem_of_mem_erase hq
      simpa using hinv_ge q.1 hq'
    have := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
    omega
  -- the constants
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 8 / (25 * k) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = Real.exp M / (1 - 1 / (4 * k)) := ⟨_, rfl⟩
  have h4k : 1 / (4 * (k : ℝ)) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h1sub : 0 < 1 - 1 / (4 * (k : ℝ)) := by linarith
  have hQ1 : 1 ≤ Q := by
    rw [hQdef, le_div_iff₀ h1sub, one_mul]
    have : (1 : ℝ) ≤ Real.exp M := Real.one_le_exp (by rw [hMdef]; positivity)
    have : 0 < 1 / (4 * (k : ℝ)) := by positivity
    linarith
  have hQk : Q ^ k ≤ 2 := by rw [hQdef, hMdef]; exact offLineQ_pow_le_two hk
  -- the Cauchy bound for `A/O` at radius `s = 2kD`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 2 * k * D := ⟨_, rfl⟩
  have hspos : 0 < s := by rw [hs]; positivity
  have hs2 : s ^ 2 = 4 * k ^ 2 * D ^ 2 := by rw [hs]; ring
  have hr : ∀ q, ¬ XiCopyCritical q → s ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2 := by
    intro q hq
    have h1 := hfar q hq
    have h2 : (3 * k * D) ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : 0 < ‖xiSpectralPoint q - t‖ ^ 2 := lt_of_lt_of_le (by positivity) h2
    rw [div_le_iff₀ h3, hs2]
    nlinarith
  have hE : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q) →
      16 * s ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 ≤
        2 * M := by
    intro F hF
    have h1 := hoff F hF
    rw [hs2, hMdef]
    have h2 : 16 * (4 * (k : ℝ) ^ 2 * D ^ 2) *
        ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 ≤
          64 * k ^ 2 * (1 / (100 * k ^ 3)) := by
      have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 64 * k ^ 2 by positivity)
      nlinarith
    have h3 : 64 * (k : ℝ) ^ 2 * (1 / (100 * k ^ 3)) = 2 * (8 / (25 * k)) := by field_simp; ring
    linarith
  have hCoffne : ∀ σ : ℂ, ‖σ‖ ≤ s → Coff σ ≠ 0 := by
    intro σ hσ h0
    have hsum := summable_inv_sq_norm_xiSpectralPoint_sub (t : ℂ)
    have hb := norm_slicePartialProduct_ge ht poff hσ
      (fun q hq => hr q (by rw [hpoff] at hq; exact hq))
      (M := 2 * s ^ 2 * ∑' q, 1 / ‖xiSpectralPoint q - t‖ ^ 2) (fun F _ => by
        have h1 := hsum.sum_le_tsum F (fun j _ => by positivity)
        exact mul_le_mul_of_nonneg_left h1 (by positivity))
    rw [← hCoff, h0, norm_zero] at hb
    exact absurd hb (not_le.mpr (Real.exp_pos _))
  have hPbound : ∀ σ ∈ sphere (0 : ℂ) s, ‖P σ‖ ≤ Real.exp M := by
    intro σ hσ
    have hσ' : ‖σ‖ ≤ s := (mem_sphere_zero_iff_norm.mp hσ).le
    have := norm_sliceProjProduct_mul_inv_le ht hσ' hr hE
    rw [hP]
    rw [hAug, hCoff, hpoff]
    exact this
  have hdiff : DiffContOnCl ℂ P (ball 0 s) := by
    rw [hP]
    refine ⟨fun σ hσ => ((hAugd σ).mul ((hCoffd σ).inv
      (hCoffne σ (mem_ball_zero_iff.mp hσ).le))).differentiableWithinAt, ?_⟩
    rw [closure_ball _ hspos.ne']
    exact hAugd.continuous.continuousOn.mul (hCoffd.continuous.continuousOn.inv₀
      fun σ hσ => hCoffne σ (mem_closedBall_zero_iff.mp hσ))
  have hbnd : ∀ j, |qs j| ≤ Real.exp M / s ^ (2 * j) := by
    intro j
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (2 * j) hspos hdiff
      hPbound
    have hfac : (0 : ℝ) < ((2 * j).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [hqs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [hb]
    simp only
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (((2 * j).factorial : ℝ))⁻¹ * ‖iteratedDeriv (2 * j) P 0‖
        ≤ (((2 * j).factorial : ℝ))⁻¹ * (((2 * j).factorial : ℝ) * Real.exp M / s ^ (2 * j)) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hfac.le)
      _ = Real.exp M / s ^ (2 * j) := by field_simp
  -- every shifted truncation is `PF_k`
  have hPF : ∀ S : Finset {q // p' q} × Finset {q // poff q},
      PFSeq k (cauchyConv (geomProdSeq (Ls (S.1 ∪ C₀', S.2))) qs) := by
    intro S
    obtain ⟨S', hS'⟩ : ∃ S', S' = (S.1 ∪ C₀', S.2) := ⟨_, rfl⟩
    rw [← hS']
    have hxk : θ ≤ (Ls S').getD (k - 1) 0 :=
      le_getD_of_le_length_filter (Ls S') (hLs_sorted S') k hk
        (hcount S' (by rw [hS']; exact Finset.subset_union_right))
    have hxk0 : 0 < (Ls S').getD (k - 1) 0 := lt_of_lt_of_le hθpos hxk
    have hρ : (k : ℝ) / (Ls S').getD (k - 1) 0 ≤ k * D ^ 2 := by
      rw [div_le_iff₀ hxk0]
      have : (k : ℝ) * D ^ 2 * θ = k := by rw [hθ]; field_simp
      nlinarith
    have hQb : ∀ T, ∑ t ∈ Finset.range T,
        |qs t| * ((k : ℝ) / (Ls S').getD (k - 1) 0) ^ t ≤ Q := by
      intro T
      have hρ0 : 0 ≤ (k : ℝ) / (Ls S').getD (k - 1) 0 := by positivity
      calc ∑ t ∈ Finset.range T, |qs t| * ((k : ℝ) / (Ls S').getD (k - 1) 0) ^ t
          ≤ ∑ t ∈ Finset.range T, Real.exp M * (1 / (4 * k)) ^ t := by
            refine Finset.sum_le_sum fun t _ => ?_
            have h1 := hbnd t
            have h2 : ((k : ℝ) / (Ls S').getD (k - 1) 0) ^ t ≤ (k * D ^ 2) ^ t :=
              pow_le_pow_left₀ hρ0 hρ t
            calc |qs t| * ((k : ℝ) / (Ls S').getD (k - 1) 0) ^ t
                ≤ (Real.exp M / s ^ (2 * t)) * (k * D ^ 2) ^ t :=
                  mul_le_mul h1 h2 (by positivity) (by positivity)
              _ = Real.exp M * ((k * D ^ 2) / (4 * k ^ 2 * D ^ 2)) ^ t := by
                  rw [pow_mul, hs2, div_pow]
                  ring
              _ = Real.exp M * (1 / (4 * k)) ^ t := by
                  have e : (k : ℝ) * D ^ 2 / (4 * k ^ 2 * D ^ 2) = 1 / (4 * k) := by
                    field_simp
                  rw [e]
        _ = Real.exp M * ∑ t ∈ Finset.range T, (1 / (4 * (k : ℝ))) ^ t := by
            rw [Finset.mul_sum]
        _ ≤ Real.exp M * (1 / (1 - 1 / (4 * k))) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            rw [Finset.range_eq_Ico]
            have := geom_sum_Ico_le_of_lt_one (m := 0) (n := T) (x := 1 / (4 * (k : ℝ)))
              (by positivity) (by linarith)
            simpa using this
        _ = Q := by rw [hQdef]; ring
    intro m hm i j hi hj
    have h := toeplitzMinor_cauchyConv_ge_of_perturbation (hLs_sorted S') (hLs_nn S') hm hxk0
      hqs0 hQb hi hj
    have hM0 : 0 ≤ toeplitzMinor (geomProdSeq (Ls S')) m i j :=
      pfSeq_geomProdSeq (hLs_nn S') m m le_rfl i j hi hj
    have hQm : Q ^ m ≤ 2 := (pow_le_pow_right₀ hQ1 hm).trans hQk
    exact le_trans (mul_nonneg (by linarith) hM0) h
  -- pass to the limit
  have hshift : Tendsto (fun S : Finset {q // p' q} => S ∪ C₀') atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun S₁ => ⟨S₁, fun S hS => hS.trans Finset.subset_union_left⟩
  have hshift2 : Tendsto (fun S : Finset {q // p' q} × Finset {q // poff q} => (S.1 ∪ C₀', S.2))
      (atTop ×ˢ atTop) (atTop ×ˢ atTop) := hshift.prodMap tendsto_id
  refine PFSeq.of_tendsto (l := atTop ×ˢ atTop) hPF fun n => ?_
  unfold cauchyConv
  refine tendsto_finsetSum _ fun j _ => ?_
  have h1 : Tendsto (fun S : Finset {q // p' q} × Finset {q // poff q} =>
      geomProdSeq (Ls (S.1 ∪ C₀', S.2)) j) (atTop ×ˢ atTop) (𝓝 (aB j)) := by
    have e : (fun S : Finset {q // p' q} × Finset {q // poff q} =>
        geomProdSeq (Ls (S.1 ∪ C₀', S.2)) j) =
          fun S => geomProdSeq (L (S.1 ∪ C₀', S.2)) j := by
      funext S; rw [geomProdSeq_perm (hLs_perm _)]
    rw [e]
    exact (hconvW j).comp hshift2
  exact h1.mul_const _

/-- **Order-`k` reciprocal total positivity from near-line off-line zeros.**  Under the hypotheses
of `pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_nearDouble`, the slice lift
`F_t(y) = h_t(√(−y))` is reciprocally totally positive of order `k`. -/
theorem reciprocalTPUpTo_xiSliceLift_of_offLine_nearDouble {t : ℝ} (ht : XiC t ≠ 0)
    {k : ℕ} (hk : 1 ≤ k) (C₀ : Finset XiZeroCopy) (hC₀ : ∀ q ∈ C₀, XiCopyCritical q)
    (hk₀ : k ≤ C₀.card) {D : ℝ} (hD : ∀ q ∈ C₀, ‖xiSpectralPoint q - t‖ ≤ D)
    (hfar : ∀ q, ¬ XiCopyCritical q → 3 * k * D ≤ ‖xiSpectralPoint q - t‖)
    (hoff : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q) →
      D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 / ‖xiSpectralPoint q - t‖ ^ 4 ≤
        1 / (100 * k ^ 3)) :
    ReciprocalTPUpTo k (xiSliceLift t) := by
  have hreal : ∀ m, (((2 * m).factorial : ℂ))⁻¹ *
      iteratedDeriv (2 * m) (fun σ => (xiHorizontalPair t σ)⁻¹) 0 =
        ((evenRecipCoeff (xiHorizontalPair t) m : ℝ) : ℂ) := by
    intro m
    apply Complex.ext
    · simp [evenRecipCoeff]
    · rw [Complex.mul_im, im_iteratedDeriv_inv_xiHorizontalPair, mul_zero, zero_add,
        Complex.ofReal_im]
      have : ((((2 * m).factorial : ℂ))⁻¹).im = 0 := by
        rw [show (((2 * m).factorial : ℂ))⁻¹ = ((((2 * m).factorial : ℝ))⁻¹ : ℝ) by
          push_cast; rfl]
        exact Complex.ofReal_im _
      rw [this, zero_mul]
  have hh0 : xiHorizontalPair t 0 ≠ 0 := by
    unfold xiHorizontalPair
    simpa using mul_ne_zero ht ht
  exact reciprocalTPUpTo_evenSquareLift_of_pfSeq (differentiable_xiHorizontalPair t)
    (xiHorizontalPair_neg' t) hh0 hreal hk
    (pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_nearDouble ht hk C₀ hC₀ hk₀ hD hfar hoff)

end

end RHTower
