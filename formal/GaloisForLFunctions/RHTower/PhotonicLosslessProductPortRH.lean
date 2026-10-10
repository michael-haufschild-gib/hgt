import GaloisForLFunctions.RHTower.PhotonicLosslessTemporalStackRealZeros
import GaloisForLFunctions.RHTower.XiCosineShiftLaguerrePolya
import GaloisForLFunctions.RHTower.ArchimedeanGenusZeroSum
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# The multiplicative port of lossless temporal media is RH-complete

Two lossless temporal slabs of the same duration `τ`, with impedances `1` and
`cot²(γτ)`, have the displacement entry

  `A(k) = 1 - sin²(kτ)/sin²(γτ)`,

whose zeros are `±γ + πℤ/τ`. As `τ → 0` it converges locally uniformly to
`1 - k²/γ²`. A multiplicative port multiplies the transfer entries of
independent lossless media. It is order-blind and multiplicative, and nonlinear
in the fields.

Under RH the zeros of `Ξ` are real and come in pairs `±γ`, so the ball
truncations of the Hadamard product are finite products of factors `1 - z²/γ²`.
Each factor is a limit of two-slab entries, and a diagonal choice gives lossless
product approximants of `Ξ`. Conversely, every multiplicatively ported lossless
entry has only real zeros, and the Hurwitz closed-locus transfer applies.
Therefore

  RH ⟺ `XiC` is a locally uniform limit of nonzero multiples of finite products
       of displacement entries of lossless temporal Maxwell stacks.

So the PTR energy receiver is exactly RH; nothing is lost in the photonic
formulation.
-/

open Complex Set Filter Topology Metric

namespace RHTower

noncomputable section

/-! ### The two-slab factor -/

/-- Two lossless slabs of equal duration `τ`, impedances `1` and `cot²(γτ)`. -/
def ptrPairSlab (γ τ : ℝ) : List (ℝ × ℝ) :=
  [(1, τ), (Real.cos (γ * τ) ^ 2 / Real.sin (γ * τ) ^ 2, τ)]

theorem ptrPairSlab_pos {γ τ : ℝ} (hτ : 0 < τ) (h0 : 0 < γ * τ) (h1 : γ * τ < Real.pi / 2) :
    ∀ x ∈ ptrPairSlab γ τ, 0 < x.1 ∧ 0 < x.2 := by
  have hs : 0 < Real.sin (γ * τ) :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos (γ * τ) := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  intro x hx
  simp only [ptrPairSlab, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨one_pos, hτ⟩
  · exact ⟨by positivity, hτ⟩

/-- The two-slab displacement entry is `1 - sin²(kτ)/sin²(γτ)`. -/
theorem ptrPairSlab_entry {γ τ : ℝ} (hs : Real.sin (γ * τ) ≠ 0) (k : ℂ) :
    ptrLosslessStackEntry (ptrPairSlab γ τ) k =
      1 - Complex.sin (k * τ) ^ 2 / (Real.sin (γ * τ) : ℂ) ^ 2 := by
  have hs' : Complex.sin ((γ : ℂ) * τ) ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sin]; exact_mod_cast hs
  have hcs := Complex.cos_sq_add_sin_sq ((γ : ℂ) * τ)
  have hk := Complex.cos_sq_add_sin_sq (k * τ)
  simp only [ptrLosslessStackEntry, ptrLosslessStack, ptrPairSlab, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, ptrLosslessSlab, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  have key : ∀ c s u v : ℂ, s ≠ 0 → c ^ 2 + s ^ 2 = 1 → u ^ 2 + v ^ 2 = 1 →
      u * u + v / 1 * -(c ^ 2 / s ^ 2 * v) = 1 - v ^ 2 / s ^ 2 := by
    intro c s u v hs h1 h2
    field_simp
    linear_combination s ^ 2 * h2 - v ^ 2 * h1
  exact key _ _ _ _ hs' hcs hk

/-! ### The removable-singularity sine -/

/-- `sin w = w · ptrSinc w`, with `ptrSinc 0 = 1`. -/
def ptrSinc : ℂ → ℂ := dslope Complex.sin 0

theorem ptrSinc_mul (w : ℂ) : w * ptrSinc w = Complex.sin w := by
  have h := sub_smul_dslope Complex.sin 0 w
  simpa [ptrSinc] using h

theorem ptrSinc_zero : ptrSinc 0 = 1 := by
  rw [ptrSinc, dslope_same, Complex.deriv_sin, Complex.cos_zero]

theorem continuousAt_ptrSinc (w : ℂ) : ContinuousAt ptrSinc w := by
  rcases eq_or_ne w 0 with rfl | hw
  · exact continuousAt_dslope_same.mpr Complex.differentiable_sin.differentiableAt
  · exact (continuousAt_dslope_of_ne hw).mpr Complex.continuous_sin.continuousAt

/-- The two-slab entry in sinc form. -/
theorem ptrPairSlab_entry_sinc {γ τ : ℝ} (hγ : γ ≠ 0) (hτ : τ ≠ 0)
    (hs : Real.sin (γ * τ) ≠ 0) (k : ℂ) :
    ptrLosslessStackEntry (ptrPairSlab γ τ) k =
      1 - (k / γ) ^ 2 * (ptrSinc (k * τ) / ptrSinc ((γ * τ : ℝ) : ℂ)) ^ 2 := by
  rw [ptrPairSlab_entry hs]
  have hγτ : ((γ * τ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero hγ hτ
  have hsinγ : (Real.sin (γ * τ) : ℂ) = ((γ * τ : ℝ) : ℂ) * ptrSinc ((γ * τ : ℝ) : ℂ) := by
    rw [ptrSinc_mul, ← Complex.ofReal_sin]
  have hS : ptrSinc ((γ * τ : ℝ) : ℂ) ≠ 0 := by
    intro h
    apply hs
    have : (Real.sin (γ * τ) : ℂ) = 0 := by rw [hsinγ, h, mul_zero]
    exact_mod_cast this
  have hsink : Complex.sin (k * τ) = (k * τ) * ptrSinc (k * τ) := (ptrSinc_mul _).symm
  rw [hsink, hsinγ]
  have hγ' : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  push_cast
  field_simp

/-- The step durations `π/(4γ(n+1))`. -/
def ptrPairDuration (γ : ℝ) (n : ℕ) : ℝ := Real.pi / (4 * γ * ((n : ℝ) + 1))

/-- **Two-slab factor law.** For `γ > 0` the entries of the two-slab media with
durations `π/(4γ(n+1))` converge locally uniformly to `1 - k²/γ²`. -/
theorem tendstoLocallyUniformly_ptrPairSlab {γ : ℝ} (hγ : 0 < γ) :
    TendstoLocallyUniformly
      (fun n k => ptrLosslessStackEntry (ptrPairSlab γ (ptrPairDuration γ n)) k)
      (fun k => 1 - k ^ 2 / (γ : ℂ) ^ 2) atTop := by
  set τ := ptrPairDuration γ with hτdef
  have hτpos : ∀ n, 0 < τ n := fun n => by
    simp only [hτdef, ptrPairDuration]; positivity
  have hγτ : ∀ n, γ * τ n = Real.pi / (4 * ((n : ℝ) + 1)) := fun n => by
    simp only [hτdef, ptrPairDuration]; field_simp
  have hs : ∀ n, Real.sin (γ * τ n) ≠ 0 := fun n => by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hγ (hτpos n))
    rw [hγτ n]
    have : (1 : ℝ) ≤ 4 * ((n : ℝ) + 1) := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hτlim : Tendsto τ atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 := h.const_mul (Real.pi / (4 * γ))
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    simp only [hτdef, ptrPairDuration]
    field_simp
  -- joint continuity of the sinc ratio at the origin
  set F : ℂ × ℂ → ℂ := fun w => 1 - (ptrSinc w.1 / ptrSinc w.2) ^ 2 with hFdef
  have hF : ContinuousAt F (0, 0) := by
    have h1 : ContinuousAt (fun w : ℂ × ℂ => ptrSinc w.1) (0, 0) :=
      (continuousAt_ptrSinc ((0, 0) : ℂ × ℂ).1).comp continuousAt_fst
    have h2 : ContinuousAt (fun w : ℂ × ℂ => ptrSinc w.2) (0, 0) :=
      (continuousAt_ptrSinc ((0, 0) : ℂ × ℂ).2).comp continuousAt_snd
    have hne : ptrSinc ((0, 0) : ℂ × ℂ).2 ≠ 0 := by simp [ptrSinc_zero]
    exact continuousAt_const.sub ((h1.div h2 hne).pow 2)
  have hF0 : F (0, 0) = 0 := by simp [hFdef, ptrSinc_zero]
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  refine ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩
  set R : ℝ := ‖x‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  set M : ℝ := (R / γ) ^ 2 + 1 with hM
  have hMpos : 0 < M := by positivity
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.mp hF (ε / M) (div_pos hε hMpos)
  have hev : ∀ᶠ n in atTop, τ n * (R + γ) < δ := by
    have := (hτlim.mul_const (R + γ)).eventually (gt_mem_nhds (by rw [zero_mul]; exact hδ))
    exact this
  filter_upwards [hev] with n hn
  intro k hk
  have hkR : ‖k‖ ≤ R := by
    have := norm_le_of_mem_closedBall (ball_subset_closedBall hk)
    have h2 : ‖k‖ ≤ ‖x‖ + 1 := by
      have := mem_ball.mp hk
      rw [dist_eq_norm] at this
      have := norm_le_insert' k x
      linarith [norm_sub_rev k x]
    exact h2
  have hentry := ptrPairSlab_entry_sinc hγ.ne' (hτpos n).ne' (hs n) k
  have hdist : dist ((k * τ n, ((γ * τ n : ℝ) : ℂ)) : ℂ × ℂ) (0, 0) < δ := by
    rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
    apply max_lt
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hτpos n)]
      nlinarith [hτpos n, norm_nonneg k]
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hγ (hτpos n))]
      nlinarith [hτpos n]
  have hsmall := hδF hdist
  rw [hF0, dist_zero_right] at hsmall
  simp only [hFdef] at hsmall
  rw [hentry, dist_eq_norm]
  have hrw : 1 - k ^ 2 / (γ : ℂ) ^ 2 -
      (1 - (k / γ) ^ 2 * (ptrSinc (k * τ n) / ptrSinc ((γ * τ n : ℝ) : ℂ)) ^ 2) =
      (k / γ) ^ 2 * -(1 - (ptrSinc (k * τ n) / ptrSinc ((γ * τ n : ℝ) : ℂ)) ^ 2) := by
    have hγ' : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
    field_simp
    ring
  rw [hrw, norm_mul, norm_neg]
  have hkγ : ‖(k / γ) ^ 2‖ ≤ (R / γ) ^ 2 := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ]
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hkR hγ.le) 2
  calc ‖(k / γ) ^ 2‖ * ‖1 - (ptrSinc (k * τ n) / ptrSinc ((γ * τ n : ℝ) : ℂ)) ^ 2‖
      ≤ (R / γ) ^ 2 * (ε / M) := mul_le_mul hkγ hsmall.le (norm_nonneg _) (by positivity)
    _ < ε := by
      rw [hM, mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith

/-! ### Finite products of locally uniform limits -/

theorem tendstoLocallyUniformly_finset_prod {ι : Type*} (s : Finset ι)
    {F : ι → ℕ → ℂ → ℂ} {f : ι → ℂ → ℂ}
    (hF : ∀ i ∈ s, TendstoLocallyUniformly (F i) (f i) atTop)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    TendstoLocallyUniformly (fun n z => ∏ i ∈ s, F i n z) (fun z => ∏ i ∈ s, f i z) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε x
    exact ⟨univ, univ_mem, Eventually.of_forall fun n y _ => by simp [hε]⟩
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    have hA := hF a (Finset.mem_insert_self a s)
    have hS := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hcA := hf a (Finset.mem_insert_self a s)
    have hcS : Continuous fun z => ∏ i ∈ s, f i z :=
      continuous_finsetProd s fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have := (tendstoLocallyUniformlyOn_univ.mpr hA).mul₀ (tendstoLocallyUniformlyOn_univ.mpr hS)
      hcA.continuousOn hcS.continuousOn
    exact tendstoLocallyUniformlyOn_univ.mp this

/-! ### Pairing of the Xi divisor under RH -/

theorem xiSpectralPoint_im_eq_zero_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 0 := by
  have hre := xi_divisor_support_re_eq_half_of_rh hRH q.1
  simp [xiSpectralPoint, hre]

/-- Positive-ordinate half of the zero ball. -/
def xiZeroBallPos (m : ℕ) : Finset XiZeroCopy :=
  (xiZeroBall m).filter fun q => 0 < (xiSpectralPoint q).re

/-- Under RH the ball product pairs into factors `1 - z²/γ²` over positive ordinates. -/
theorem prod_xiZeroBall_eq_pos_of_rh (hRH : RiemannHypothesis) (m : ℕ) (z : ℂ) :
    ∏ q ∈ xiZeroBall m, (1 - z / xiSpectralPoint q) =
      ∏ q ∈ xiZeroBallPos m, (1 - z ^ 2 / (((xiSpectralPoint q).re : ℝ) : ℂ) ^ 2) := by
  classical
  have hreal : ∀ q, xiSpectralPoint q = (((xiSpectralPoint q).re : ℝ) : ℂ) := fun q => by
    apply Complex.ext <;> simp [xiSpectralPoint_im_eq_zero_of_rh hRH q]
  have hre0 : ∀ q, (xiSpectralPoint q).re ≠ 0 := fun q h => by
    apply xiSpectralPoint_ne_zero q
    rw [hreal q, h, Complex.ofReal_zero]
  rw [← Finset.prod_filter_mul_prod_filter_not (xiZeroBall m)
    (fun q => 0 < (xiSpectralPoint q).re)]
  have hneg : ∏ q ∈ xiZeroBall m with ¬ 0 < (xiSpectralPoint q).re, (1 - z / xiSpectralPoint q) =
      ∏ q ∈ xiZeroBallPos m, (1 + z / xiSpectralPoint q) := by
    symm
    refine Finset.prod_nbij' xiZeroCopyReflectEquiv xiZeroCopyReflectEquiv.symm ?_ ?_
      (fun q _ => by simp) (fun q _ => by simp) ?_
    · intro q hq
      simp only [xiZeroBallPos, Finset.mem_filter] at hq ⊢
      refine ⟨?_, ?_⟩
      · rw [mem_xiZeroBall, xiSpectralPoint_reflect, norm_neg]; exact mem_xiZeroBall.mp hq.1
      · rw [xiSpectralPoint_reflect, Complex.neg_re]; linarith [hq.2]
    · intro q hq
      simp only [xiZeroBallPos, Finset.mem_filter] at hq ⊢
      refine ⟨?_, ?_⟩
      · rw [mem_xiZeroBall, xiSpectralPoint_reflect_symm, norm_neg]; exact mem_xiZeroBall.mp hq.1
      · rw [xiSpectralPoint_reflect_symm, Complex.neg_re]
        have h1 := hre0 q
        have h2 := hq.2
        push Not at h2
        have : (xiSpectralPoint q).re < 0 := lt_of_le_of_ne h2 h1
        linarith
    · intro q _
      rw [xiSpectralPoint_reflect, div_neg, sub_neg_eq_add]
  rw [hneg]
  change (∏ q ∈ xiZeroBallPos m, (1 - z / xiSpectralPoint q)) * _ = _
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hw : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  rw [← hreal q]
  field_simp
  ring

/-! ### The equivalence -/

/-- Multiplicatively ported lossless entry: `c · ∏ A_l(k)` over a list of lossless stacks. -/
def ptrLosslessProductPort (c : ℂ) (L : List (List (ℝ × ℝ))) (k : ℂ) : ℂ :=
  c * (L.map fun l => ptrLosslessStackEntry l k).prod

theorem ptrLosslessProductPort_differentiable (c : ℂ) (L : List (List (ℝ × ℝ))) :
    Differentiable ℂ (ptrLosslessProductPort c L) := by
  unfold ptrLosslessProductPort
  apply Differentiable.const_mul
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (ptrLosslessStack_differentiable l 0 0).mul ih

theorem ptrLosslessProductPort_zero_im_eq_zero {c : ℂ} (hc : c ≠ 0)
    {L : List (List (ℝ × ℝ))} (hL : ∀ l ∈ L, ∀ x ∈ l, 0 < x.1 ∧ 0 < x.2) {k : ℂ}
    (hk : ptrLosslessProductPort c L k = 0) : k.im = 0 := by
  unfold ptrLosslessProductPort at hk
  rcases mul_eq_zero.mp hk with h | h
  · exact absurd h hc
  · rw [List.prod_eq_zero_iff, List.mem_map] at h
    obtain ⟨l, hl, hzero⟩ := h
    exact ptrLosslessStackEntry_zero_im_eq_zero (hL l hl) hzero

/-- **The lossless multiplicative port is RH-complete.** RH holds if and only if
`XiC` is a locally uniform limit of nonzero multiples of finite products of
displacement entries of lossless temporal Maxwell stacks. -/
theorem riemannHypothesis_iff_XiC_limit_losslessProductPort :
    RiemannHypothesis ↔
      ∃ (c : ℕ → ℂ) (L : ℕ → List (List (ℝ × ℝ))),
        (∀ n, c n ≠ 0) ∧ (∀ n, ∀ l ∈ L n, ∀ x ∈ l, 0 < x.1 ∧ 0 < x.2) ∧
        TendstoLocallyUniformly (fun n => ptrLosslessProductPort (c n) (L n)) XiC atTop := by
  constructor
  · intro hRH
    -- the paired ball truncations converge to Ξ
    set P : ℕ → ℂ → ℂ := fun m z =>
      XiC 0 * ∏ q ∈ xiZeroBallPos m, (1 - z ^ 2 / (((xiSpectralPoint q).re : ℝ) : ℂ) ^ 2)
      with hPdef
    have hP : TendstoLocallyUniformly P XiC atTop := by
      have h := tendstoLocallyUniformly_prod_xiZeroBall
      have hc : TendstoLocallyUniformly (fun (_ : ℕ) (_ : ℂ) => XiC 0) (fun _ => XiC 0) atTop := by
        rw [Metric.tendstoLocallyUniformly_iff]
        intro ε hε x
        exact ⟨univ, univ_mem, Eventually.of_forall fun n y _ => by simp [hε]⟩
      have hprod := (tendstoLocallyUniformlyOn_univ.mpr hc).mul₀
        (tendstoLocallyUniformlyOn_univ.mpr h) continuousOn_const
        (xiCanonicalProduct_analytic.continuousOn)
      have hprod' := tendstoLocallyUniformlyOn_univ.mp hprod
      rw [XiC_eq_constant_mul_canonicalProduct]
      refine hprod'.congr fun m z => ?_
      simp only [hPdef, Pi.mul_apply]
      rw [prod_xiZeroBall_eq_pos_of_rh hRH m z]
    -- positive ordinates
    have hγpos : ∀ m, ∀ q ∈ xiZeroBallPos m, 0 < (xiSpectralPoint q).re := fun m q hq =>
      (Finset.mem_filter.mp hq).2
    -- two-slab approximants of each truncation
    set A : ℕ → ℕ → ℂ → ℂ := fun m n z =>
      XiC 0 * ∏ q ∈ xiZeroBallPos m,
        ptrLosslessStackEntry (ptrPairSlab (xiSpectralPoint q).re
          (ptrPairDuration (xiSpectralPoint q).re n)) z with hAdef
    have hA : ∀ m, TendstoLocallyUniformly (A m) (P m) atTop := by
      intro m
      have hprod := tendstoLocallyUniformly_finset_prod (xiZeroBallPos m)
        (F := fun q n z => ptrLosslessStackEntry (ptrPairSlab (xiSpectralPoint q).re
          (ptrPairDuration (xiSpectralPoint q).re n)) z)
        (f := fun q z => 1 - z ^ 2 / (((xiSpectralPoint q).re : ℝ) : ℂ) ^ 2)
        (fun q hq => tendstoLocallyUniformly_ptrPairSlab (hγpos m q hq))
        (fun q _ => by fun_prop)
      have hc : TendstoLocallyUniformly (fun (_ : ℕ) (_ : ℂ) => XiC 0) (fun _ => XiC 0) atTop := by
        rw [Metric.tendstoLocallyUniformly_iff]
        intro ε hε x
        exact ⟨univ, univ_mem, Eventually.of_forall fun n y _ => by simp [hε]⟩
      have hcont : Continuous fun z => ∏ q ∈ xiZeroBallPos m,
          (1 - z ^ 2 / (((xiSpectralPoint q).re : ℝ) : ℂ) ^ 2) :=
        continuous_finsetProd _ fun q _ => by fun_prop
      have hmul := (tendstoLocallyUniformlyOn_univ.mpr hc).mul₀
        (tendstoLocallyUniformlyOn_univ.mpr hprod) continuousOn_const hcont.continuousOn
      exact (tendstoLocallyUniformlyOn_univ.mp hmul).congr fun n z => rfl
    -- diagonal choice
    have hk : ∀ m : ℕ, ∃ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) m,
        dist (P m z) (A m n z) < 1 / ((m : ℝ) + 1) := by
      intro m
      have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp (hA m)) _
        (isCompact_closedBall (0 : ℂ) m)
      rw [Metric.tendstoUniformlyOn_iff] at hu
      exact (hu _ (by positivity)).exists
    choose N hN using hk
    have hXiC0 : XiC 0 ≠ 0 := XiC_zero_ne
    refine ⟨fun _ => XiC 0, fun m => (xiZeroBallPos m).toList.map fun q =>
        ptrPairSlab (xiSpectralPoint q).re (ptrPairDuration (xiSpectralPoint q).re (N m)),
      fun _ => hXiC0, ?_, ?_⟩
    · intro m l hl x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      have hqm := Finset.mem_toList.mp hq
      have hγ := hγpos m q hqm
      have hτ : 0 < ptrPairDuration (xiSpectralPoint q).re (N m) := by
        unfold ptrPairDuration; positivity
      have hγτ : (xiSpectralPoint q).re * ptrPairDuration (xiSpectralPoint q).re (N m) =
          Real.pi / (4 * ((N m : ℝ) + 1)) := by
        unfold ptrPairDuration; field_simp
      refine ptrPairSlab_pos hτ (mul_pos hγ hτ) ?_ x hx
      rw [hγτ, div_lt_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ 4 * ((N m : ℝ) + 1) := by
        have := (Nat.cast_nonneg (N m) : (0 : ℝ) ≤ N m); linarith
      nlinarith [Real.pi_pos]
    · have hrepr : ∀ m z, ptrLosslessProductPort (XiC 0) ((xiZeroBallPos m).toList.map fun q =>
          ptrPairSlab (xiSpectralPoint q).re (ptrPairDuration (xiSpectralPoint q).re (N m))) z =
          A m (N m) z := by
        intro m z
        simp only [ptrLosslessProductPort, List.map_map, hAdef]
        rw [← Finset.prod_map_toList]
        rfl
      rw [tendstoLocallyUniformly_iff_forall_isCompact]
      intro K hK
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
      have hPu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hP) K hK
      rw [Metric.tendstoUniformlyOn_iff] at hPu
      have h1 := hPu (ε / 2) (half_pos hε)
      have h2 : ∀ᶠ m : ℕ in atTop, R ≤ m ∧ 1 / ((m : ℝ) + 1) < ε / 2 := by
        have ha := tendsto_natCast_atTop_atTop.eventually_ge_atTop R
        have hb := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
          (gt_mem_nhds (half_pos hε))
        exact ha.and hb
      filter_upwards [h1, h2] with m hm1 hm2 z hz
      rw [hrepr]
      have hzm : z ∈ closedBall (0 : ℂ) m := by
        have := hR hz
        rw [mem_closedBall] at this ⊢
        linarith [hm2.1]
      calc dist (XiC z) (A m (N m) z)
          ≤ dist (XiC z) (P m z) + dist (P m z) (A m (N m) z) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (hm1 z hz) ((hN m z hzm).trans hm2.2)
        _ = ε := add_halves ε
  · rintro ⟨c, L, hc, hL, hconv⟩
    apply riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hconv
    · exact Eventually.of_forall fun n => ptrLosslessProductPort_differentiable (c n) (L n)
    · exact Eventually.of_forall fun n z hz =>
        ptrLosslessProductPort_zero_im_eq_zero (hc n) (hL n) hz

end

end RHTower
