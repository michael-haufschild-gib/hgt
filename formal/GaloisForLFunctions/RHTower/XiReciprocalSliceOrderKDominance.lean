import GaloisForLFunctions.RHTower.XiReciprocalSliceOffLineDominance
import GaloisForLFunctions.HTGeometry.ToeplitzPerturbationCornerRatio
import GaloisForLFunctions.RHTower.XiReciprocalSliceLocalOrder

/-!
# Order-`k` off-line dominance for the reciprocal slice

At a height `t` with `Ξ(t) ≠ 0`, write the normalized pair product as
`h_t(σ)/h_t(0) = C(σ) · O(σ)`, the products over the critical and the off-line zero copies.  The
even reciprocal coefficients of `C` are the limits of geometric products
`∏ 1/(1 − x_q u)`, `x_q = (γ_q − t)^{−2}`.  The off-line factor is a perturbation, controlled by
Cauchy estimates.

**Theorem** (`pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_sparse`).  Let `k ≥ 1`, let `C₀` be
a set of at least `k` critical zero copies, all within distance `D` of `t`, and suppose the
off-line zeros satisfy `D² Σ_{off-line z} 1/|z − t|² ≤ 1/(25k³)`.  Then the even reciprocal
coefficients of `Ξ(t+σ)Ξ(t−σ)` form a `PF_k` sequence.

Failure of reciprocal total positivity of order `k` at `t` therefore forces off-line mass at
scale `D_k(t)`, the distance from `t` to its `k`-th nearest critical zero.  Conversely, total
positivity of order `k` at `t` makes every zero real whose disk around `t` carries at most `k`
zeros (`im_eq_zero_of_reciprocalTPUpTo`, from finite-order zero location): order `k` sees exactly
the `k` nearest zeros, and dominance controls everything beyond them.

The proof applies the perturbation law `toeplitzMinor_cauchyConv_ge_of_perturbation` to every
finite truncation of `C`, with the corner ratio `ρ = k/x_k ≤ kD²`.  The off-line coefficients obey
`|b_j| ≤ e^{8/(25k)}/(4k²D²)^j`.  Hence `Q = e^{8/(25k)}/(1 − 1/(4k))`, and
`Q^k ≤ e^{8/25 + 1/3} < 2`.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Geometric products as reciprocal coefficients -/

theorem geomProdSeq_perm {xs ys : List ℝ} (h : xs.Perm ys) : geomProdSeq xs = geomProdSeq ys := by
  funext n
  unfold geomProdSeq
  rw [(h.map geomPowerSeries).prod_eq]

theorem cauchyConv_geometric_geomProdSeq (x : ℝ) (xs : List ℝ) :
    cauchyConv (fun n => x ^ n) (geomProdSeq xs) = geomProdSeq (x :: xs) := by
  have hx : (fun n : ℕ => x ^ n) = fun n => PowerSeries.coeff n (geomPowerSeries x) :=
    funext fun n => (coeff_geomPowerSeries x n).symm
  rw [hx]
  have hg : geomProdSeq xs = fun n => PowerSeries.coeff n (xs.map geomPowerSeries).prod := rfl
  rw [hg, cauchyConv_coeff]
  funext n
  simp only [geomProdSeq, List.map_cons, List.prod_cons]

/-- Even reciprocal coefficients of a product of even-reciprocally `PF` factors. -/
theorem evenRecipCoeff_mul {u v : ℂ → ℂ} (hu : EvenRecipPF u) (hv : EvenRecipPF v) :
    evenRecipCoeff (u * v) = cauchyConv (evenRecipCoeff u) (evenRecipCoeff v) := by
  have hinv : (fun σ => ((u * v) σ)⁻¹) = (fun σ => (u σ)⁻¹) * fun σ => (v σ)⁻¹ := by
    funext σ
    simp only [Pi.mul_apply, mul_inv]
  funext k
  unfold evenRecipCoeff cauchyConv
  rw [hinv, factorial_inv_mul_iteratedDeriv_mul_even_of_analyticAt hu.analyticAt_inv
    hv.analyticAt_inv hu.odd, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hu.coeff_real, hv.coeff_real, ← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

theorem evenRecipCoeff_one : evenRecipCoeff (fun _ => 1) = twoTermSeq 1 0 := by
  have hinv : (fun σ : ℂ => ((fun _ : ℂ => (1 : ℂ)) σ)⁻¹) = fun _ => (1 : ℂ) := by
    funext σ
    simp
  funext m
  unfold evenRecipCoeff twoTermSeq
  rw [hinv, iteratedDeriv_const]
  rcases m with _ | _ | m <;> simp

theorem evenRecipCoeff_one_sub_sq_div {a : ℝ} (ha : 0 < a) :
    evenRecipCoeff (fun σ : ℂ => 1 - σ ^ 2 / a) = fun m => a⁻¹ ^ m := by
  set g : ℂ → ℂ := fun z => (1 - z / a)⁻¹ with hg
  have hgan : AnalyticAt ℂ g 0 := (hasFPowerSeriesAt_inv_one_sub_div ha).analyticAt
  have hinv : (fun σ : ℂ => ((fun σ : ℂ => 1 - σ ^ 2 / (a : ℂ)) σ)⁻¹) = fun σ => g (σ ^ 2) := rfl
  funext m
  unfold evenRecipCoeff
  rw [hinv, iteratedDeriv_comp_sq hgan, iteratedDeriv_eq_of_hasFPowerSeriesAt
    (hasFPowerSeriesAt_inv_one_sub_div ha)]
  have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have h2m : ((2 * m).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

/-- `∏_{a ∈ L} (1 − σ²/a)`. -/
def oneSubSqProd (L : List ℝ) (σ : ℂ) : ℂ := (L.map fun a : ℝ => 1 - σ ^ 2 / (a : ℂ)).prod

/-- **Finite products.**  For positive `a`'s the product `∏ (1 − σ²/a)` is even-reciprocally `PF`,
with reciprocal coefficients the geometric product of the ratios `1/a`. -/
theorem evenRecipPF_oneSubSqProd {L : List ℝ} (hL : ∀ a ∈ L, 0 < a) :
    EvenRecipPF (oneSubSqProd L) ∧
      evenRecipCoeff (oneSubSqProd L) = geomProdSeq (L.map (·⁻¹)) := by
  induction L with
  | nil =>
    have e : oneSubSqProd [] = fun _ => 1 := by funext σ; simp [oneSubSqProd]
    rw [e, List.map_nil, geomProdSeq_nil]
    exact ⟨EvenRecipPF.one, evenRecipCoeff_one⟩
  | cons a L ih =>
    have ha := hL a List.mem_cons_self
    obtain ⟨hpf, hc⟩ := ih fun b hb => hL b (List.mem_cons_of_mem a hb)
    have e : oneSubSqProd (a :: L) = (fun σ : ℂ => 1 - σ ^ 2 / (a : ℂ)) * oneSubSqProd L := by
      funext σ; simp [oneSubSqProd]
    rw [e]
    refine ⟨(EvenRecipPF.one_sub_sq_div ha).mul hpf, ?_⟩
    rw [evenRecipCoeff_mul (EvenRecipPF.one_sub_sq_div ha) hpf, hc,
      evenRecipCoeff_one_sub_sq_div ha, List.map_cons]
    exact cauchyConv_geometric_geomProdSeq _ _

/-- Even reciprocal coefficients converge under locally uniform convergence of nonvanishing
holomorphic functions. -/
theorem tendsto_evenRecipCoeff_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι}
    {U : ι → ℂ → ℂ} {u : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hUd : ∀ i, DifferentiableOn ℂ (U i) (ball 0 r)) (hUne : ∀ i, ∀ σ ∈ ball (0 : ℂ) r, U i σ ≠ 0)
    (hud : DifferentiableOn ℂ u (ball 0 r)) (hune : ∀ σ ∈ ball (0 : ℂ) r, u σ ≠ 0)
    (h : TendstoLocallyUniformlyOn U u l (ball 0 r)) (n : ℕ) :
    Tendsto (fun i => evenRecipCoeff (U i) n) l (𝓝 (evenRecipCoeff u n)) := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hinv : TendstoLocallyUniformlyOn (fun i σ => (U i σ)⁻¹) (fun σ => (u σ)⁻¹) l
      (ball 0 r) := h.inv₀ hud.continuousOn hune
  have hinvd : ∀ᶠ i in l, DifferentiableOn ℂ (fun σ => (U i σ)⁻¹) (ball 0 r) :=
    Eventually.of_forall fun i => (hUd i).inv fun σ hσ => hUne i σ hσ
  have hd := ((GaloisForLFunctions.tendstoLocallyUniformlyOn_iteratedDeriv isOpen_ball hinv
    hinvd (2 * n)).1.tendsto_at h0)
  unfold evenRecipCoeff
  exact (Complex.continuous_re.tendsto _).comp (hd.const_mul _)

/-- In a decreasing list, if at least `k` entries are `≥ θ`, so is the `k`-th one. -/
theorem le_getD_of_le_length_filter {θ : ℝ} :
    ∀ (xs : List ℝ), xs.Pairwise (· ≥ ·) → ∀ k : ℕ, 1 ≤ k →
      k ≤ (xs.filter fun x => decide (θ ≤ x)).length → θ ≤ xs.getD (k - 1) 0
  | [], _, k, hk, hlen => by simp at hlen; omega
  | x :: xs, hs, k, hk, hlen => by
    by_cases hx : θ ≤ x
    · rcases Nat.eq_or_lt_of_le hk with rfl | hk2
      · simpa using hx
      · have hlen' : k - 1 ≤ (xs.filter fun y => decide (θ ≤ y)).length := by
          have e : ((x :: xs).filter fun y => decide (θ ≤ y)).length =
              (xs.filter fun y => decide (θ ≤ y)).length + 1 := by
            rw [List.filter_cons_of_pos (by simpa using hx), List.length_cons]
          omega
        have := le_getD_of_le_length_filter xs (List.pairwise_cons.mp hs).2 (k - 1) (by omega)
          hlen'
        rw [show k - 1 = (k - 1 - 1) + 1 by omega, List.getD_cons_succ]
        exact this
    · have hall : (xs.filter fun y => decide (θ ≤ y)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have := (List.pairwise_cons.mp hs).1 y hy
        simp only [decide_eq_true_eq]
        push Not at hx ⊢
        linarith
      rw [List.filter_cons_of_neg (by simpa using hx), hall] at hlen
      simp at hlen
      omega

/-! ## The slice factors -/

/-- Partial products of slice factors are entire. -/
theorem differentiable_slicePartialProduct (t : ℝ) (p : XiZeroCopy → Prop) :
    Differentiable ℂ (slicePartialProduct t p) := by
  intro σ
  have hconv : TendstoLocallyUniformlyOn
      (fun (S : Finset {q // p q}) σ => ∏ q ∈ S, (1 + sliceFactorTerm t q.1 σ))
      (slicePartialProduct t p) atTop (ball (0 : ℂ) (‖σ‖ + 1)) :=
    hasProdLocallyUniformlyOn_slicePartialProduct t p (‖σ‖ + 1)
  have hd : DifferentiableOn ℂ (slicePartialProduct t p) (ball 0 (‖σ‖ + 1)) :=
    hconv.differentiableOn (Eventually.of_forall fun S =>
      (Differentiable.fun_finsetProd fun q _ => by unfold sliceFactorTerm; fun_prop).differentiableOn)
      isOpen_ball
  exact hd.differentiableAt (isOpen_ball.mem_nhds (by simp))

/-- **Coefficients of truncations.**  The even reciprocal coefficients of the finite slice
products converge to those of the predicate product. -/
theorem tendsto_evenRecipCoeff_slicePartialProduct {t : ℝ} (ht : XiC t ≠ 0)
    (p : XiZeroCopy → Prop) (n : ℕ) :
    Tendsto (fun S : Finset {q // p q} =>
      evenRecipCoeff (fun σ => ∏ q ∈ S, (1 + sliceFactorTerm t q.1 σ)) n) atTop
      (𝓝 (evenRecipCoeff (slicePartialProduct t p) n)) := by
  classical
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
  set U : Finset {q // p q} → ℂ → ℂ := fun S σ => ∏ q ∈ S, (1 + sliceFactorTerm t q.1 σ) with hU
  have hUd : ∀ S, DifferentiableOn ℂ (U S) (ball 0 R) := fun S =>
    (Differentiable.fun_finsetProd fun q _ => by unfold sliceFactorTerm; fun_prop).differentiableOn
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
    (differentiable_slicePartialProduct t p).differentiableOn
  have hune : ∀ σ ∈ ball (0 : ℂ) R, slicePartialProduct t p σ ≠ 0 := by
    intro σ hσ h0
    have hσ' : ‖σ‖ ≤ R := by simpa using (mem_ball_zero_iff.mp hσ).le
    have hb := norm_slicePartialProduct_ge ht p hσ' (fun q _ => hsq q) hM
    rw [h0, norm_zero] at hb
    exact absurd hb (not_le.mpr (Real.exp_pos _))
  exact tendsto_evenRecipCoeff_of_tendstoLocallyUniformlyOn hR0 hUd hUne hud hune hconv n

/-- **Cauchy bound for a reciprocal slice factor.**  On `|σ| ≤ s`, small factors keep
`|1/∏| ≤ e^M`, so the even Taylor coefficients of the reciprocal are at most `e^M/s^{2j}`. -/
theorem norm_evenCoeff_inv_slicePartialProduct_le {t : ℝ} (ht : XiC t ≠ 0) (p : XiZeroCopy → Prop)
    {s M : ℝ} (hs : 0 < s) (hr : ∀ q, p q → s ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2)
    (hM : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, p q) →
      2 * s ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ M) (j : ℕ) :
    ‖(((2 * j).factorial : ℂ))⁻¹ *
        iteratedDeriv (2 * j) (fun σ => (slicePartialProduct t p σ)⁻¹) 0‖ ≤
      Real.exp M / s ^ (2 * j) := by
  have hne : ∀ σ : ℂ, ‖σ‖ ≤ s → slicePartialProduct t p σ ≠ 0 := fun σ hσ h0 => by
    have := norm_slicePartialProduct_ge ht p hσ hr hM
    rw [h0, norm_zero] at this
    exact absurd this (not_le.mpr (Real.exp_pos _))
  have hbound : ∀ σ ∈ sphere (0 : ℂ) s, ‖(slicePartialProduct t p σ)⁻¹‖ ≤ Real.exp M := by
    intro σ hσ
    have hσ' : ‖σ‖ ≤ s := (mem_sphere_zero_iff_norm.mp hσ).le
    have h1 := norm_slicePartialProduct_ge ht p hσ' hr hM
    rw [norm_inv, inv_le_comm₀ (norm_pos_iff.mpr (hne σ hσ')) (Real.exp_pos _), ← Real.exp_neg]
    exact h1
  have hd := differentiable_slicePartialProduct t p
  have hdiff : DiffContOnCl ℂ (fun σ => (slicePartialProduct t p σ)⁻¹) (ball 0 s) := by
    refine ⟨fun σ hσ => ((hd σ).inv (hne σ ?_)).differentiableWithinAt, ?_⟩
    · exact (mem_ball_zero_iff.mp hσ).le
    · rw [closure_ball _ hs.ne']
      exact hd.continuous.continuousOn.inv₀ fun σ hσ => hne σ (mem_closedBall_zero_iff.mp hσ)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (2 * j) hs hdiff hbound
  have hfac : (0 : ℝ) < ((2 * j).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (((2 * j).factorial : ℝ))⁻¹ *
        ‖iteratedDeriv (2 * j) (fun σ => (slicePartialProduct t p σ)⁻¹) 0‖
      ≤ (((2 * j).factorial : ℝ))⁻¹ * (((2 * j).factorial : ℝ) * Real.exp M / s ^ (2 * j)) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hfac.le)
    _ = Real.exp M / s ^ (2 * j) := by field_simp

/-! ## The constants -/

/-- `Q = e^{8/(25k)}/(1 − 1/(4k))` satisfies `Q^k ≤ 2`. -/
theorem offLineQ_pow_le_two {k : ℕ} (hk : 1 ≤ k) :
    (Real.exp (8 / (25 * k)) / (1 - 1 / (4 * k))) ^ k ≤ 2 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set x : ℝ := 1 / (4 * k) with hx
  have hx0 : 0 < x := by positivity
  have hx4 : x ≤ 1 / 4 := by
    rw [hx]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h1x : 0 < 1 - x := by linarith
  have hinv : 1 / (1 - x) ≤ Real.exp (x / (1 - x)) := by
    have := Real.add_one_le_exp (x / (1 - x))
    have e : x / (1 - x) + 1 = 1 / (1 - x) := by field_simp; ring
    linarith
  have hkx : (k : ℝ) * (x / (1 - x)) ≤ 1 / 3 := by
    rw [hx, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (k : ℝ) * (1 / (4 * k)) = 1 / 4 := by field_simp
    rw [this]
    have h2 : 1 - 1 / (4 * (k : ℝ)) ≥ 3 / 4 := by
      have : 1 / (4 * (k : ℝ)) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    nlinarith
  rw [div_eq_mul_one_div, mul_pow, ← Real.exp_nat_mul]
  have hka : (k : ℝ) * (8 / (25 * k)) = 8 / 25 := by field_simp
  rw [hka]
  calc Real.exp (8 / 25) * (1 / (1 - x)) ^ k
      ≤ Real.exp (8 / 25) * Real.exp (x / (1 - x)) ^ k := by
        gcongr
    _ = Real.exp (8 / 25 + k * (x / (1 - x))) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (Real.log 2) := by
        apply Real.exp_le_exp.mpr
        have := Real.log_two_gt_d9
        norm_num at this ⊢
        linarith
    _ = 2 := Real.exp_log (by norm_num)

/-! ## Order-`k` dominance -/

/-- The slice factor of a critical copy is `1 − σ²/a` with `a = (γ − t)² > 0`. -/
theorem one_add_sliceFactorTerm_eq_of_critical {t : ℝ} (ht : XiC t ≠ 0) {q : XiZeroCopy}
    (hq : XiCopyCritical q) :
    0 < ((xiSpectralPoint q).re - t) ^ 2 ∧
      (fun σ => 1 + sliceFactorTerm t q σ) =
        fun σ : ℂ => 1 - σ ^ 2 / ((((xiSpectralPoint q).re - t) ^ 2 : ℝ) : ℂ) := by
  unfold XiCopyCritical at hq
  set x : ℝ := (xiSpectralPoint q).re with hx
  have hz : xiSpectralPoint q = (x : ℂ) := Complex.ext (by simp [hx]) (by simpa using hq)
  have hne : x - t ≠ 0 := by
    intro h
    apply xiSpectralPoint_ne_ofReal ht q
    rw [hz]
    congr 1
    linarith
  refine ⟨by positivity, ?_⟩
  funext σ
  unfold sliceFactorTerm
  rw [hz]
  push_cast
  ring

/-- For a critical copy, `‖z − t‖² = (γ − t)²`. -/
theorem norm_sq_eq_of_critical {t : ℝ} {q : XiZeroCopy} (hq : XiCopyCritical q) :
    ‖xiSpectralPoint q - t‖ ^ 2 = ((xiSpectralPoint q).re - t) ^ 2 := by
  unfold XiCopyCritical at hq
  have hz : xiSpectralPoint q - t = (((xiSpectralPoint q).re - t : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simpa using hq)
  rw [hz, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Order-`k` off-line dominance.**  Let `k ≥ 1` and let `C₀` be a set of at least `k` critical
zero copies within distance `D` of `t`.  If the off-line copies satisfy
`D² Σ_{off-line} 1/|z − t|² ≤ 1/(25k³)`, then the even reciprocal coefficients of
`Ξ(t+σ)Ξ(t−σ)` form a `PF_k` sequence. -/
theorem pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_sparse {t : ℝ} (ht : XiC t ≠ 0)
    {k : ℕ} (hk : 1 ≤ k) (C₀ : Finset XiZeroCopy) (hC₀ : ∀ q ∈ C₀, XiCopyCritical q)
    (hk₀ : k ≤ C₀.card) {D : ℝ} (hD : ∀ q ∈ C₀, ‖xiSpectralPoint q - t‖ ≤ D)
    (hoff : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q) →
      D ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / (25 * k ^ 3)) :
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
  obtain ⟨ha₀, hf₀⟩ := one_add_sliceFactorTerm_eq_of_critical ht hq₀c
  obtain ⟨a₀, ha₀def⟩ : ∃ a₀ : ℝ, a₀ = ((xiSpectralPoint q₀).re - t) ^ 2 := ⟨_, rfl⟩
  rw [← ha₀def] at ha₀ hf₀
  obtain ⟨f₀, hf₀def⟩ : ∃ f₀ : ℂ → ℂ, f₀ = fun σ => 1 + sliceFactorTerm t q₀ σ := ⟨_, rfl⟩
  have hf₀pf : EvenRecipPF f₀ := by rw [hf₀def, hf₀]; exact EvenRecipPF.one_sub_sq_div ha₀
  have hf₀c : evenRecipCoeff f₀ = fun n => a₀⁻¹ ^ n := by
    rw [hf₀def, hf₀]; exact evenRecipCoeff_one_sub_sq_div ha₀
  have hC'pf : EvenRecipPF C' := by rw [hC', hp']; exact evenRecipPF_critical_except ht q₀
  obtain ⟨Ccrit, hCcrit⟩ : ∃ Ccrit : ℂ → ℂ, Ccrit = f₀ * C' := ⟨_, rfl⟩
  have hCcritpf : EvenRecipPF Ccrit := by rw [hCcrit]; exact hf₀pf.mul hC'pf
  obtain ⟨aC, haC⟩ : ∃ aC : ℕ → ℝ, aC = evenRecipCoeff Ccrit := ⟨_, rfl⟩
  have haC_eq : aC = cauchyConv (fun n => a₀⁻¹ ^ n) (evenRecipCoeff C') := by
    rw [haC, hCcrit, evenRecipCoeff_mul hf₀pf hC'pf, hf₀c]
  -- the off-line coefficients
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℂ, b = fun j =>
      (((2 * j).factorial : ℂ))⁻¹ * iteratedDeriv (2 * j) (fun σ => (Coff σ)⁻¹) 0 := ⟨_, rfl⟩
  obtain ⟨qs, hqs⟩ : ∃ qs : ℕ → ℝ, qs = fun j => (b j).re := ⟨_, rfl⟩
  have hCoff0 : Coff 0 = 1 := by rw [hCoff]; exact slicePartialProduct_zero t poff
  have hqs0 : qs 0 = 1 := by simp [hqs, hb, hCoff0]
  have hCoffd : Differentiable ℂ Coff := by rw [hCoff]; exact differentiable_slicePartialProduct t poff
  have hCoffan : AnalyticAt ℂ (fun σ => (Coff σ)⁻¹) 0 :=
    (hCoffd.analyticAt 0).inv (by rw [hCoff0]; exact one_ne_zero)
  have hu_eq : evenRecipCoeff (Ccrit * Coff) = cauchyConv aC qs := by
    have hinv : (fun σ => ((Ccrit * Coff) σ)⁻¹) =
        (fun σ => (Ccrit σ)⁻¹) * fun σ => (Coff σ)⁻¹ := by
      funext σ; simp only [Pi.mul_apply, mul_inv]
    funext m
    unfold evenRecipCoeff cauchyConv
    rw [hinv, factorial_inv_mul_iteratedDeriv_mul_even_of_analyticAt hCcritpf.analyticAt_inv
      hCoffan hCcritpf.odd, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hCcritpf.coeff_real, Complex.re_ofReal_mul, haC, hqs, hb]
  -- the pair product
  have hreal : (XiC (t : ℂ)).im = 0 := by
    have h := XiC_conj (t : ℂ)
    rw [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hre0 : (XiC (t : ℂ)).re ≠ 0 := by
    intro h0
    apply ht
    exact Complex.ext (by simp [h0]) (by simp [hreal])
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = (XiC (t : ℂ)).re ^ 2 := ⟨_, rfl⟩
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
  -- the critical truncations
  obtain ⟨aq, haq⟩ : ∃ aq : XiZeroCopy → ℝ, aq = fun q => ((xiSpectralPoint q).re - t) ^ 2 :=
    ⟨_, rfl⟩
  have haqpos : ∀ q, XiCopyCritical q → 0 < aq q := fun q hq => by
    rw [haq]; exact (one_add_sliceFactorTerm_eq_of_critical ht hq).1
  have hcritp' : ∀ q, p' q → XiCopyCritical q := fun q hq => by rw [hp'] at hq; exact hq.1
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
  have hUpf : ∀ S, EvenRecipPF (U S) ∧
      evenRecipCoeff (U S) = geomProdSeq ((S.toList.map fun q => aq q.1).map (·⁻¹)) := by
    intro S
    rw [hU_eq]
    refine evenRecipPF_oneSubSqProd fun a ha => ?_
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
    exact haqpos q.1 (hcritp' q.1 q.2)
  obtain ⟨L, hL⟩ : ∃ L : Finset {q // p' q} → List ℝ,
      L = fun S => (a₀ :: S.toList.map fun q => aq q.1).map (·⁻¹) := ⟨_, rfl⟩
  have hW : ∀ S, cauchyConv (fun n => a₀⁻¹ ^ n) (evenRecipCoeff (U S)) = geomProdSeq (L S) := by
    intro S
    rw [(hUpf S).2, hL]
    simp only [List.map_cons]
    exact cauchyConv_geometric_geomProdSeq _ _
  have hconvW : ∀ n, Tendsto (fun S => geomProdSeq (L S) n) atTop (𝓝 (aC n)) := by
    intro n
    simp_rw [← hW]
    rw [haC_eq]
    unfold cauchyConv
    have hlim := fun i => tendsto_evenRecipCoeff_slicePartialProduct ht p' i
    rw [← hC'] at hlim
    exact tendsto_finsetSum _ fun j _ => by
      have := (hlim (n - j)).const_mul (a₀⁻¹ ^ j)
      simpa [hU] using this
  -- sorted lists
  obtain ⟨Ls, hLs⟩ : ∃ Ls : Finset {q // p' q} → List ℝ,
      Ls = fun S => (L S : Multiset ℝ).sort (· ≥ ·) := ⟨_, rfl⟩
  have hLs_perm : ∀ S, (Ls S).Perm (L S) := fun S => by
    rw [hLs]; exact Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
  have hLs_sorted : ∀ S, (Ls S).Pairwise (· ≥ ·) := fun S => by
    rw [hLs]; exact Multiset.pairwise_sort _ _
  have hL_nn : ∀ S, ∀ x ∈ L S, 0 ≤ x := by
    intro S x hx
    rw [hL, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rcases List.mem_cons.mp ha with rfl | ha
    · exact inv_nonneg.mpr ha₀.le
    · obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
      exact inv_nonneg.mpr (haqpos q.1 (hcritp' q.1 q.2)).le
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
  have hcount : ∀ S, C₀' ⊆ S → k ≤ ((Ls S).filter fun x => decide (θ ≤ x)).length := by
    intro S hS
    have ha₀θ : θ ≤ a₀⁻¹ := by
      have := hinv_ge q₀ hq₀
      rw [haq] at this
      simpa [ha₀def] using this
    rw [((hLs_perm S).filter _).length_eq, hL]
    simp only [List.map_cons]
    rw [List.filter_cons_of_pos (by simpa using ha₀θ), List.length_cons, List.map_map,
      List.filter_map, List.length_map]
    have hsub : C₀' ⊆ (S.toList.filter ((fun x => decide (θ ≤ x)) ∘ (·⁻¹) ∘ fun q => aq q.1)).toFinset := by
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
  -- off-line Cauchy bound at radius `s = 2kD`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 2 * k * D := ⟨_, rfl⟩
  have hspos : 0 < s := by rw [hs]; positivity
  have hs2 : s ^ 2 = 4 * k ^ 2 * D ^ 2 := by rw [hs]; ring
  have hr : ∀ q, poff q → s ^ 2 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / 2 := by
    intro q hq
    have h1 := hoff {q} (by rw [hpoff] at hq; simpa using hq)
    rw [Finset.sum_singleton] at h1
    rw [hs2, div_eq_mul_one_div]
    have h2 : 4 * (k : ℝ) ^ 2 * D ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) ≤
        4 * k ^ 2 * (1 / (25 * k ^ 3)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 4 * (k : ℝ) ^ 2 * (1 / (25 * k ^ 3)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hMb : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, poff q) →
      2 * s ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ M := by
    intro F hF
    have h1 := hoff F (fun q hq => by have := hF q hq; rw [hpoff] at this; exact this)
    rw [hs2, hMdef]
    have h2 : 2 * (4 * (k : ℝ) ^ 2 * D ^ 2) * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤
        8 * k ^ 2 * (1 / (25 * k ^ 3)) := by
      have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 8 * k ^ 2 by positivity)
      nlinarith
    have h3 : 8 * (k : ℝ) ^ 2 * (1 / (25 * k ^ 3)) = 8 / (25 * k) := by field_simp
    linarith
  have hbnd : ∀ j, |qs j| ≤ Real.exp M / s ^ (2 * j) := fun j => by
    have := norm_evenCoeff_inv_slicePartialProduct_le ht poff hspos hr hMb j
    rw [← hCoff] at this
    rw [hqs]
    exact (Complex.abs_re_le_norm _).trans (by rw [hb]; exact this)
  -- every shifted truncation is `PF_k`
  have hPF : ∀ S, PFSeq k (cauchyConv (geomProdSeq (Ls (S ∪ C₀'))) qs) := by
    intro S
    obtain ⟨S', hS'⟩ : ∃ S', S' = S ∪ C₀' := ⟨_, rfl⟩
    rw [← hS']
    have hxk : θ ≤ (Ls S').getD (k - 1) 0 :=
      le_getD_of_le_length_filter (Ls S') (hLs_sorted S') k hk
        (hcount S' (by rw [hS']; exact Finset.subset_union_right))
    have hxk0 : 0 < (Ls S').getD (k - 1) 0 := lt_of_lt_of_le hθpos hxk
    have hρ : (k : ℝ) / (Ls S').getD (k - 1) 0 ≤ k * D ^ 2 := by
      rw [div_le_iff₀ hxk0]
      have : (k : ℝ) * D ^ 2 * θ = k := by rw [hθ]; field_simp
      nlinarith
    have hQb : ∀ T, ∑ t ∈ Finset.range T, |qs t| * ((k : ℝ) / (Ls S').getD (k - 1) 0) ^ t ≤ Q := by
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
  refine PFSeq.of_tendsto (l := atTop) hPF fun n => ?_
  unfold cauchyConv
  refine tendsto_finsetSum _ fun j _ => ?_
  have h1 : Tendsto (fun S => geomProdSeq (Ls (S ∪ C₀')) j) atTop (𝓝 (aC j)) := by
    have e : (fun S => geomProdSeq (Ls (S ∪ C₀')) j) = fun S => geomProdSeq (L (S ∪ C₀')) j := by
      funext S; rw [geomProdSeq_perm (hLs_perm _)]
    rw [e]
    exact (hconvW j).comp hshift
  exact h1.mul_const _

/-- **Failure localization of order `k`.**  If the even reciprocal coefficients of
`Ξ(t+σ)Ξ(t−σ)` are not `PF_k`, then for every set `C₀` of at least `k` critical copies within
distance `D` of `t`, some finite set of off-line copies carries
`D² Σ 1/|z − t|² > 1/(25k³)`. -/
theorem offLine_mass_gt_of_not_pfSeq {t : ℝ} (ht : XiC t ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    (hfail : ¬ PFSeq k (evenRecipCoeff (xiHorizontalPair t))) (C₀ : Finset XiZeroCopy)
    (hC₀ : ∀ q ∈ C₀, XiCopyCritical q) (hk₀ : k ≤ C₀.card) {D : ℝ}
    (hD : ∀ q ∈ C₀, ‖xiSpectralPoint q - t‖ ≤ D) :
    ∃ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q) ∧
      1 / (25 * k ^ 3) < D ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 := by
  by_contra hno
  push Not at hno
  exact hfail (pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_sparse ht hk C₀ hC₀ hk₀ hD hno)

/-- Reciprocal total positivity of order `k` of an even-square lift from `PF_k` of its even
reciprocal coefficients. -/
theorem reciprocalTPUpTo_evenSquareLift_of_pfSeq {u : ℂ → ℂ} (hu : Differentiable ℂ u)
    (heven : ∀ z, u (-z) = u z) (h0 : u 0 ≠ 0)
    (hreal : ∀ m, (((2 * m).factorial : ℂ))⁻¹ * iteratedDeriv (2 * m) (fun σ => (u σ)⁻¹) 0 =
      ((evenRecipCoeff u m : ℝ) : ℂ))
    {k : ℕ} (hk : 1 ≤ k) (hpf : PFSeq k (evenRecipCoeff u)) :
    ReciprocalTPUpTo k (fun y => evenSquareLift u (-y)) := by
  set F : ℂ → ℂ := fun y => evenSquareLift u (-y) with hF
  have hdiff : Differentiable ℂ F := (differentiable_evenSquareLift hu).comp differentiable_neg
  have hsq : ∀ σ : ℂ, F (-(σ ^ 2)) = u σ := by
    intro σ
    simp only [hF, neg_neg]
    exact evenSquareLift_sq hu heven σ
  have hF0 : F 0 ≠ 0 := by
    have h := hsq 0
    rw [show -((0 : ℂ) ^ 2) = 0 by ring] at h
    rw [h]
    exact h0
  set g : ℂ → ℂ := recipNeg F with hg
  have hgsq : (fun σ => g (σ ^ 2)) = fun σ => (u σ)⁻¹ := by
    funext σ
    simp only [hg, recipNeg]
    rw [hsq]
  have hgan : AnalyticAt ℂ g 0 := by
    have hne : F (-0) ≠ 0 := by simpa using hF0
    exact ((hdiff.comp differentiable_neg).analyticAt 0).inv hne
  have hcoef : ∀ n, ((n.factorial : ℂ))⁻¹ * iteratedDeriv n g 0 =
      ((evenRecipCoeff u n : ℝ) : ℂ) := by
    intro n
    rw [← iteratedDeriv_comp_sq hgan n, hgsq]
    exact hreal n
  have hnn : ∀ n, 0 ≤ evenRecipCoeff u n := by
    intro n
    have := (PFSeq.of_le hk hpf) 1 le_rfl (fun _ => 0) (fun _ => n) (Subsingleton.strictMono _)
      (Subsingleton.strictMono _)
    simpa [toeplitzMinor, Matrix.det_unique, zext_natCast] using this
  refine ⟨hdiff, hF0, fun n => ?_, ?_⟩
  · have hD : iteratedDeriv n g 0 = ((n.factorial : ℂ)) * ((evenRecipCoeff u n : ℝ) : ℂ) := by
      rw [← hcoef n]
      have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      field_simp
    show 0 ≤ iteratedDeriv n g 0
    rw [hD]
    exact mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.mpr (hnn n))
  · have heq : recipCoeff F = evenRecipCoeff u := by
      funext n
      unfold recipCoeff
      rw [← hg, hcoef n, Complex.ofReal_re]
    rw [heq]
    intro m hm i₀ j hj
    exact hpf m hm _ j (fun a b hab => by simpa using hab) hj

/-- **Order-`k` reciprocal total positivity from sparse off-line zeros.**  Under the hypotheses of
`pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_sparse`, the slice lift `F_t(y) = h_t(√(−y))`
is reciprocally totally positive of order `k`. -/
theorem reciprocalTPUpTo_xiSliceLift_of_offLine_sparse {t : ℝ} (ht : XiC t ≠ 0)
    {k : ℕ} (hk : 1 ≤ k) (C₀ : Finset XiZeroCopy) (hC₀ : ∀ q ∈ C₀, XiCopyCritical q)
    (hk₀ : k ≤ C₀.card) {D : ℝ} (hD : ∀ q ∈ C₀, ‖xiSpectralPoint q - t‖ ≤ D)
    (hoff : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q) →
      D ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / (25 * k ^ 3)) :
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
    (pfSeq_evenRecipCoeff_xiHorizontalPair_of_offLine_sparse ht hk C₀ hC₀ hk₀ hD hoff)

/-- **The converse half: order `k` sees the `k` nearest zeros.**  If the slice lift at `t` is
reciprocally totally positive of order `k`, every zero `z` of `Ξ` is real as soon as the disk
`‖y‖ ≤ |z − t|²` carries at most `k` zeros of `F_t`, counted with multiplicity. -/
theorem im_eq_zero_of_reciprocalTPUpTo {t : ℝ} (ht : XiC t ≠ 0) {k : ℕ}
    (hTP : ReciprocalTPUpTo k (xiSliceLift t)) {z : ℂ} (hz : XiC z = 0)
    (hcount : ∑ y ∈ (zeros_finite_closedBall (differentiable_xiSliceLift t)
      (xiSliceLift_zero_ne_zero ht) ‖(z - t) ^ 2‖).toFinset,
        analyticOrderNatAt (xiSliceLift t) y ≤ k) : z.im = 0 := by
  have hzero : xiSliceLift t (-((z - t) ^ 2)) = 0 := by
    rw [xiSliceLift_neg_sq]
    unfold xiHorizontalPair
    rw [show (t : ℂ) + (z - t) = z by ring, hz, zero_mul]
  obtain ⟨D, hD, hDeq⟩ := hTP.eq_neg_of_apply_eq_zero hzero
    (S := (zeros_finite_closedBall (differentiable_xiSliceLift t)
      (xiSliceLift_zero_ne_zero ht) ‖(z - t) ^ 2‖).toFinset)
    (fun y hy hy0 => by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, mem_closedBall, dist_zero_right]
      refine ⟨hy.trans (by rw [norm_neg]), hy0⟩)
    hcount
  have ht2 : (z - t) ^ 2 = (D : ℂ) := by linear_combination -hDeq
  have him := congrArg Complex.im ht2
  have hre := congrArg Complex.re ht2
  simp only [sq, Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero] at him hre
  by_contra hne
  have hre0 : z.re - t = 0 := by
    have : 2 * (z.re - t) * z.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hne
  rw [hre0] at hre
  nlinarith [sq_nonneg z.im]

end

end RHTower
