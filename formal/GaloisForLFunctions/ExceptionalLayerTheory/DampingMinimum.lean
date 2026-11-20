import GaloisForLFunctions.ExceptionalLayerTheory.ArbitraryDampingContractionReadsTheDivisor
import GaloisForLFunctions.RHTower.BakerGeneralProof.FrequencyModulus
import GaloisForLFunctions.HTGeometry.ClogVertLog

/-!
# Least degree and noise gain of a damping filter

An equally spaced damping grid measures exponential nodes. The
interpolating polynomial that isolates one node kills each distinct
competing site once. Its coefficient norm gives the exact gain for
independent complex errors in the weighted samples. As the grid contracts,
the leading constant depends on the product of the actual site gaps.
-/

noncomputable section
open Complex Polynomial Filter Topology RHTower XiAtlasFinitePart
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.BakerGeneralProof
open private tendsto_exp_difference_div_step from
  GaloisForLFunctions.ExceptionalLayerTheory.ArbitraryDampingContractionReadsTheDivisor

namespace GaloisForLFunctions.ExceptionalLayerTheory.DampingInterpolation

/-- Mode location in the geometric damping coordinate. -/
def node (β h : ℝ) (w : ℂ) := Complex.exp ((h:ℂ)*(w-β))

/-- The pole and the distinct competing zero sites. -/
def rejected (F : Finset XiZeroCopy) (ρ : ℂ) := insert 1 ((F.image xiZero).erase ρ)

/-- Monic polynomial killing the competing nodes. -/
def rejector (S : Finset ℂ) (β h : ℝ) : ℂ[X] := ∏ w ∈ S,(X-C (node β h w))

/-- Unit response at the target when it is resolved by the grid. -/
def detector (S : Finset ℂ) (β h : ℝ) (ρ : ℂ) : ℂ[X] :=
  C ((rejector S β h).eval (node β h ρ))⁻¹*rejector S β h

private theorem rejector_eval (S : Finset ℂ) (β h : ℝ) (z : ℂ) :
    (rejector S β h).eval z=∏ w ∈ S,(z-node β h w) := by
  simp [rejector,Polynomial.eval_prod]

private theorem rejector_kills {w : ℂ} {S : Finset ℂ} (hw : w ∈ S) (β h : ℝ) :
    (rejector S β h).eval (node β h w)=0 := by
  rw [rejector_eval]
  exact Finset.prod_eq_zero hw (sub_self _)

private theorem rejector_degree (S : Finset ℂ) (β h : ℝ) : (rejector S β h).natDegree=S.card := by
  unfold rejector
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]
  simp

private theorem resolved_value {S : Finset ℂ} {ρ : ℂ} (hr : ρ ∉ S) {β h : ℝ}
    (hi : Set.InjOn (node β h) (↑(insert ρ S) : Set ℂ)) :
    (rejector S β h).eval (node β h ρ) ≠ 0 := by
  rw [rejector_eval]
  exact Finset.prod_ne_zero_iff.mpr fun w hw => sub_ne_zero.mpr fun e =>
    hr (by simpa only [hi (Finset.mem_insert_self ..) (Finset.mem_insert_of_mem hw) e] using hw)

private theorem detector_value {S : Finset ℂ} {ρ : ℂ} (hr : ρ ∉ S) {β h : ℝ}
    (hi : Set.InjOn (node β h) (↑(insert ρ S) : Set ℂ)) :
    (detector S β h ρ).eval (node β h ρ)=1 := by
  rw [detector,Polynomial.eval_mul,Polynomial.eval_C,inv_mul_cancel₀ (resolved_value hr hi)]

private theorem detector_kills {w : ℂ} {S : Finset ℂ} (hw : w ∈ S) (β h : ℝ) (ρ : ℂ) :
    (detector S β h ρ).eval (node β h w)=0 := by
  rw [detector,Polynomial.eval_mul,rejector_kills hw,mul_zero]

/-- A normalized interpolant needs at least one degree for each distinct
rejected site. At minimal degree every coefficient is determined. -/
theorem least_degree_unique {S : Finset ℂ} {ρ : ℂ} (hr : ρ ∉ S) {β h : ℝ}
    (hi : Set.InjOn (node β h) (↑(insert ρ S) : Set ℂ))
    (P : ℂ[X]) (hP : P.eval (node β h ρ)=1) (hz : ∀ w ∈ S,P.eval (node β h w)=0) :
    S.card ≤ P.natDegree ∧ (P.natDegree ≤ S.card ↔ P=detector S β h ρ) := by
  classical
  have hn := resolved_value hr hi
  have hdeg : (detector S β h ρ).natDegree=S.card := by
    rw [detector,natDegree_C_mul (inv_ne_zero hn),rejector_degree]
  let V := S.image (node β h)
  have hv : V.card=S.card := Finset.card_image_of_injOn
    (hi.mono fun _ hw => Finset.mem_insert_of_mem hw)
  have h₁ : S.card ≤ P.natDegree := by
    by_contra! hh
    have he := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P V
      (fun _ hv => by obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hz w hw) (hh.trans_eq hv.symm)
    rw [he,Polynomial.eval_zero] at hP
    exact zero_ne_one hP
  refine ⟨h₁,?_,fun he => he ▸ hdeg.le⟩
  intro hb
  let U := insert ρ S
  have huv : (U.image (node β h)).card=S.card+1 :=
    (Finset.card_image_of_injOn hi).trans (Finset.card_insert_of_notMem hr)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _ (U.image (node β h))
  · intro z hmem
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hmem
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hP.trans (detector_value hr hi).symm
    · exact (hz w hw).trans (detector_kills hw β h ρ).symm
  · rw [huv,hdeg]
    exact Nat.lt_succ_of_le (max_le hb le_rfl)

private theorem node_to_one {h : ℝ → ℝ} (hl : Tendsto h atTop (𝓝 0)) (β : ℝ) (w : ℂ) :
    Tendsto (fun t => node β (h t) w) atTop (𝓝 1) := by
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    (((Complex.continuous_ofReal.tendsto 0).comp hl).mul_const (w-β))
  simpa only [node,Function.comp_def,Complex.ofReal_zero,zero_mul,Complex.exp_zero] using he

private theorem gap_limit {h : ℝ → ℝ} (hl : Tendsto h atTop (𝓝 0))
    (hn : ∀ᶠ t : ℝ in atTop,h t ≠ 0) (β : ℝ) (w z : ℂ) :
    Tendsto (fun t : ℝ => (node β (h t) w-node β (h t) z)/(h t:ℂ)) atTop (𝓝 (w-z)) := by
  simpa only [node,sub_sub_sub_cancel_right] using tendsto_exp_difference_div_step hl hn (w-β) (z-β)

/-- A contracting nonzero grid eventually resolves every distinct pair. -/
theorem eventually_resolved (S : Finset ℂ) (β : ℝ) {h : ℝ → ℝ} (hl : Tendsto h atTop (𝓝 0))
    (hn : ∀ᶠ t : ℝ in atTop,h t ≠ 0) :
    ∀ᶠ t : ℝ in atTop,Set.InjOn (node β (h t)) (↑S : Set ℂ) := by
  classical
  have hp (w z : ℂ) : ∀ᶠ t : ℝ in atTop,node β (h t) w=node β (h t) z → w=z := by
    by_cases he : w=z
    · exact Eventually.of_forall fun _ _ => he
    · filter_upwards [(gap_limit hl hn β w z).eventually_ne (sub_ne_zero.mpr he)] with t ht hh
      exact (ht (by rw [hh,sub_self,zero_div])).elim
  have hpair := (Filter.eventually_all_finset S).mpr fun w _ =>
    (Filter.eventually_all_finset S).mpr fun z _ => hp w z
  exact hpair.mono fun _ ht w hw z hz => ht w hw z hz


/-- Exact worst-case error on arbitrary independent complex observations
of norm at most one. Each sample error can align its own coefficient. -/
theorem worst_sample_error (P : ℂ[X]) :
    IsGreatest {r : ℝ | ∃ e : ℕ → ℂ,(∀ j, ‖e j‖ ≤ 1) ∧
      ‖∑ j ∈ Finset.range (P.natDegree+1),P.coeff j*e j‖=r} (coeffNormSum P) := by
  let e := fun j => (starRingEnd ℂ) (P.coeff j)/(‖P.coeff j‖:ℂ)
  have eb (j : ℕ) : ‖e j‖ ≤ 1 := by
    rw [show ‖e j‖=‖P.coeff j‖/‖P.coeff j‖ by simp [e]]
    exact div_self_le_one _
  have align (j : ℕ) : P.coeff j*e j=(‖P.coeff j‖:ℂ) := by
    by_cases hz : P.coeff j=0
    · simp [e,hz]
    · change P.coeff j*((starRingEnd ℂ) (P.coeff j)/(‖P.coeff j‖:ℂ)) = _
      rw [←mul_div_assoc,Complex.mul_conj',div_eq_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))]
      ring
  constructor
  · refine ⟨e,eb,?_⟩
    simp only [align,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),coeffNormSum]
  · rintro r ⟨v,hv,rfl⟩
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hv j))

private theorem scalar_gain (c : ℂ) (P : ℂ[X]) :
    coeffNormSum (C c*P)=‖c‖*coeffNormSum P := by
  by_cases hc : c=0
  · simp [hc,coeffNormSum]
  · unfold coeffNormSum
    rw [natDegree_C_mul hc,Finset.mul_sum]
    simp only [Polynomial.coeff_C_mul,norm_mul]

private theorem norm_rejector_limit (S : Finset ℂ) (β : ℝ) {h : ℝ → ℝ} (hl : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun t => coeffNormSum (rejector S β (h t))) atTop (𝓝 (2^S.card)) := by
  have hhigh := tendsto_finsetProd S fun w _ => (tendsto_const_nhds (x := (1:ℝ))).add (node_to_one hl β w).norm
  have hlow := tendsto_finsetProd S fun w _ => ((tendsto_const_nhds (x := (-1:ℂ))).sub (node_to_one hl β w)).norm
  have hh : Tendsto (fun t => ∏ w ∈ S, (1+‖node β (h t) w‖)) atTop (𝓝 (2^S.card)) := by
    simpa only [norm_one,one_add_one_eq_two,Finset.prod_const] using hhigh
  have hb : Tendsto (fun t => ∏ w ∈ S, ‖-1-node β (h t) w‖) atTop (𝓝 (2^S.card)) := by
    simpa only [show (-1:ℂ)-1 = -(2:ℂ) by norm_num,norm_neg,Complex.norm_ofNat,Finset.prod_const] using hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hb hh (fun t => ?_) (fun t => ?_)
  · have hv := norm_polyEval_le_of_norm_le_one (rejector S β (h t)) (w := -1) (by simp)
    simpa only [rejector_eval,norm_prod,coeffNormSum] using hv
  · exact (coeffNormSum_prod_le S _).trans (Finset.prod_le_prod
      (fun _ _ => coeffNormSum_nonneg _) (fun w _ => coeffNormSum_X_sub_C_le _))

/-- For the unique shortest unit-response filter, noise of size ε per
weighted sample is amplified by asymptotically 2^D/(h^D ∏|ρ-w|).
Multiplicity is absent from both D and the gap product. -/
theorem scaled_gain_limit (S : Finset ℂ) {ρ : ℂ} (hr : ρ ∉ S) (β : ℝ)
    {h : ℝ → ℝ} (hl : Tendsto h atTop (𝓝 0)) (hn : ∀ᶠ t : ℝ in atTop,h t ≠ 0) :
    Tendsto (fun t => |h t|^S.card*coeffNormSum (detector S β (h t) ρ))
      atTop (𝓝 (2^S.card/∏ w ∈ S,‖ρ-w‖)) := by
  have he := (tendsto_finsetProd S (fun w _ => gap_limit hl hn β ρ w)).norm
  have hval : Tendsto (fun t : ℝ => ‖(rejector S β (h t)).eval (node β (h t) ρ)/(h t:ℂ)^S.card‖)
      atTop (𝓝 (∏ w ∈ S,‖ρ-w‖)) := by
    simpa only [rejector_eval,Finset.prod_div_distrib,Finset.prod_const,norm_prod] using he
  have hgap : ∏ w ∈ S,‖ρ-w‖ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w hw =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun he => hr (by simpa only [he] using hw))
  have hh := (norm_rejector_limit S β hl).div hval hgap
  exact hh.congr fun t => by
    simp only [Pi.div_apply]
    rw [detector,scalar_gain,norm_inv,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring

/-- The distinct-site filter reads the full multiplicity from the actual
prime data on each resolved grid, even when several copies occupy one site. -/
theorem prime_reading (F : Finset XiZeroCopy) {θ σ β a h : ℝ} (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (hgap : θ < σ) (hrest : ∀ q : XiZeroCopy,q ∉ F → (xiZero q).re ≤ θ)
    (hb : σ ≤ β) (ha : 0 < a) (hh : 0 ≤ h) (ρ : ℂ) (hρ : ρ ≠ 1)
    (hr : 0 < gaussianObservationRate ρ σ a)
    (hi : Set.InjOn (node β h) (↑(insert ρ (rejected F ρ)) : Set ℂ)) :
    Tendsto (fun t : ℝ => primeDampingFilter (detector (rejected F ρ) β h ρ) σ β a h t /
      gaussianMBKernel (Real.exp (-a*t)) (ρ-((σ:ℂ)+t*I))) atTop
      (𝓝 (-((F.filter fun q => xiZero q=ρ).card:ℂ))) := by
  classical
  have hout : ρ ∉ rejected F ρ := by simp [rejected,hρ]
  have hsel := primeDampingFilter_reads_selected_zero F hσ hσ1 hgap hrest hb ha hh ρ hr
    (detector (rejected F ρ) β h ρ) (detector_kills (Finset.mem_insert_self ..) β h ρ)
    (fun q hq he => detector_kills (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨he,Finset.mem_image_of_mem _ hq⟩)) β h ρ)
  change Tendsto _ _ (𝓝 (-((F.filter fun q => xiZero q=ρ).card:ℂ)* (detector (rejected F ρ) β h ρ).eval (node β h ρ))) at hsel
  rwa [detector_value hout hi,mul_one] at hsel


/-- Response to additive errors in the weighted grid readings. -/
def sampleError (P : ℂ[X]) (e : ℕ → ℂ) := ∑ j ∈ Finset.range (P.natDegree+1),P.coeff j*e j

private theorem error_bound (P : ℂ[X]) {e : ℕ → ℂ} {δ : ℝ} (he : ∀ j,‖e j‖ ≤ δ) :
    ‖sampleError P e‖ ≤ δ*coeffNormSum P := by
  rw [coeffNormSum,Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul,mul_comm δ]
  exact mul_le_mul_of_nonneg_left (he j) (norm_nonneg _)

/-- Recovery for every admissible perturbation is equivalent to vanishing
of the exact worst-case normalized noise. The equivalence also covers
time-dependent filters and complex normalizing factors. -/
theorem robust_limit_iff {P : ℝ → ℂ[X]} {A g : ℝ → ℂ} {L : ℂ}
    (ha : Tendsto (fun t => A t/g t) atTop (𝓝 L)) {δ : ℝ → ℝ} (hd : ∀ t,0 ≤ δ t) :
    (∀ e : ℝ → ℕ → ℂ,(∀ t j, ‖e t j‖ ≤ δ t) →
      Tendsto (fun t => (A t+sampleError (P t) (e t))/g t) atTop (𝓝 L)) ↔
    Tendsto (fun t => δ t*coeffNormSum (P t)/‖g t‖) atTop (𝓝 0) := by
  constructor
  · intro h
    choose v hv hval using fun t => (worst_sample_error (P t)).1
    let e := fun (t : ℝ) j => (δ t:ℂ)*v t j
    have he (t : ℝ) (j : ℕ) : ‖e t j‖ ≤ δ t := by
      rw [show ‖e t j‖=δ t*‖v t j‖ by simp only [e,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hd t)]]
      exact mul_le_of_le_one_right (hd t) (hv t j)
    have hb := ((h e he).sub ha).norm
    rw [sub_self,norm_zero] at hb
    refine hb.congr fun t => ?_
    rw [add_div,add_sub_cancel_left,norm_div]
    have hsum : sampleError (P t) (e t)=(δ t:ℂ)*sampleError (P t) (v t) := by
      unfold sampleError
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by dsimp only [e]; ring
    rw [hsum,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hd t),sampleError,hval]
  · intro h e he
    have hsmall : Tendsto (fun t => sampleError (P t) (e t)/g t) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ h
      exact Eventually.of_forall fun t => by
        rw [norm_div]
        exact div_le_div_of_nonneg_right (error_bound _ (he t)) (norm_nonneg _)
    simpa only [add_zero,add_div] using ha.add hsmall

private theorem full_gain_limit (F : Finset XiZeroCopy) (ρ : ℂ) (β : ℝ) {h : ℝ → ℝ}
    (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun t => coeffNormSum (divisorDampingFilter F ρ β (h t))) atTop
      (𝓝 (2^(1+(F.filter fun q => xiZero q≠ρ).card))) := by
  classical
  let E := F.filter fun q => xiZero q≠ρ
  let K := fun (t : ℝ) (w : ℂ) => X-C (node β (h t) w)
  have high (z : ℂ) : Tendsto (fun t => 1+‖node β (h t) z‖) atTop (𝓝 2) := by
    simpa only [norm_one,one_add_one_eq_two] using (tendsto_const_nhds (x := (1:ℝ))).add (node_to_one hh β z).norm
  have low (z : ℂ) : Tendsto (fun t => ‖(-1:ℂ)-node β (h t) z‖) atTop (𝓝 2) := by
    simpa only [show (-1:ℂ)-1 = -(2:ℂ) by norm_num,norm_neg,Complex.norm_ofNat] using
      ((tendsto_const_nhds (x := (-1:ℂ))).sub (node_to_one hh β z)).norm
  have h₁ := (low 1).mul (tendsto_finsetProd E fun q _ => low (xiZero q))
  have h₂ := (high 1).mul (tendsto_finsetProd E fun q _ => high (xiZero q))
  simp only [Finset.prod_const] at h₁ h₂
  rw [pow_add,pow_one]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h₁ h₂
  · intro t
    have he := norm_polyEval_le_of_norm_le_one (divisorDampingFilter F ρ β (h t)) (w := -1) (by simp)
    simpa only [E,node,divisorDampingFilter,Polynomial.eval_mul,Polynomial.eval_prod,
      Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,norm_mul,norm_prod,coeffNormSum] using he
  · intro t
    change coeffNormSum (K t 1*∏ q ∈ E,K t (xiZero q)) ≤ _
    refine (coeffNormSum_mul_le _ _).trans (mul_le_mul (coeffNormSum_X_sub_C_le _)
      ((coeffNormSum_prod_le E _).trans (Finset.prod_le_prod (fun _ _ => coeffNormSum_nonneg _)
      (fun _ _ => coeffNormSum_X_sub_C_le _))) (coeffNormSum_nonneg _) (by positivity))

/-- At arbitrary contracting spacings the actual prime filter recovers the
selected divisor limit under every weighted-sample error of size δ exactly
when δ is little-o of the selected Gaussian mode times h^D. -/
theorem prime_recovery_noise_threshold (F : Finset XiZeroCopy) {θ σ β a : ℝ} (hσ : 1/2 < σ)
    (hgap : θ < σ) (hrest : ∀ q : XiZeroCopy,q ∉ F → (xiZero q).re ≤ θ)
    (ha : 0 < a) (ρ : ℂ) (hρσ : σ < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ=0)
    (hr : 0 < gaussianObservationRate ρ σ a) {h : ℝ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (hp : ∀ᶠ t : ℝ in atTop,0 < h t) {δ : ℝ → ℝ} (hd : ∀ t,0 ≤ δ t) :
    let E := F.filter fun q => xiZero q≠ρ
    let P := fun t => divisorDampingFilter F ρ β (h t)
    let A := fun t => primeDampingFilter (P t) σ β a (h t) t
    let g := fun t => (h t:ℂ)^(1+E.card)*gaussianMBKernel (Real.exp (-a*t)) (ρ-((σ:ℂ)+t*I))
    let L := -((analyticOrderAt zetaResidueUnit ρ).toNat:ℂ)*((ρ-1)*∏ q ∈ E,(ρ-xiZero q))
    (∀ e : ℝ → ℕ → ℂ,(∀ t j,‖e t j‖ ≤ δ t) →
      Tendsto (fun t => (A t+sampleError (P t) (e t))/g t) atTop (𝓝 L)) ↔
      Tendsto (fun t => δ t/‖g t‖) atTop (𝓝 0) := by
  intro E P A g L
  have hbase : Tendsto (fun t => A t/g t) atTop (𝓝 L) :=
    arbitrary_contracting_prime_filter_reads_selected_zero F hσ hgap hrest ha ρ hρσ hρ1 hρ hr hh hp
  rw [robust_limit_iff hbase hd]
  have hgain : Tendsto (fun t => coeffNormSum (P t)) atTop (𝓝 (2^(1+E.card))) :=
    full_gain_limit F ρ β hh
  have hc : (2:ℝ)^(1+E.card) ≠ 0 := by positivity
  constructor
  · intro hlim
    have he := hlim.div hgain hc
    rw [zero_div] at he
    refine he.congr' ?_
    filter_upwards [hgain.eventually_ne hc] with t ht
    simp only [Pi.div_apply]
    field_simp [ht]
  · intro hlim
    have he := hlim.mul hgain
    rw [zero_mul] at he
    exact he.congr fun _ => by ring


end GaloisForLFunctions.ExceptionalLayerTheory.DampingInterpolation
