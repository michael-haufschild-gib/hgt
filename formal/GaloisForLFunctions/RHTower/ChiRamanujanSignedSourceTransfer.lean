import GaloisForLFunctions.RHTower.ChiRamanujanUniformSourceEnvelope
import GaloisForLFunctions.RHTower.ChiRamanujanMixedCompletedSource
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Signed transfer of the complete growing Mellin source

For every fixed positive pair of logarithmic Mellin lines and every fixed
Schwartz test on the full frequency plane, the integral of the ORIGINAL
complete labelled source, divided by log N, tends to zero.

Partition by the coordinate nearer its axis and rescale that coordinate.
The uniform source envelope gives an integrable product majorant; the exact
mixed-source limit and zero vertical integral of its entire profile cancel
each sector. Exact label exchange retains both growing cofactors, both
exclusions, the allowed first/second collision and every valuation sector.

This theorem treats fixed tests. The actual physical profile depends on N;
its shrinking cutoff edges and complete frequency tails require a further
transfer proof. No physical norm saving or RH conclusion is asserted.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace RHTower.BAGTrace

private theorem local_swap (z x y : ℂ) (k : ℤ) :
    weightedConeEuler z x y k=weightedConeEuler z y x k := by
  have he : weightedEuler z x y=weightedEuler z y x := by
    unfold weightedEuler
    ring
  have hm : weightedConeEulerMinusOne z x y=weightedConeEulerMinusOne z y x := by
    unfold weightedConeEulerMinusOne
    rw [he]
    ring
  have h2 : weightedConeEulerMinusTwo z x y=weightedConeEulerMinusTwo z y x := by
    unfold weightedConeEulerMinusTwo
    rw [hm]
    ring
  unfold weightedConeEuler
  split_ifs <;> first | exact h2 | exact hm | exact he | (rw [he]; ring)

private theorem source_swap (P : Finset Nat.Primes) (s t : ℂ) :
    criticalCompletedConeEuler P s t=criticalCompletedConeEuler P t s := by
  classical
  have hl (p q r : P) : criticalWeightedLabelEuler P p q r s t=
      criticalWeightedLabelEuler P q p r t s := by
    unfold criticalWeightedLabelEuler
    congr 1
    · push_cast; ring
    · apply Finset.prod_congr rfl
      intro ℓ _
      rw [local_swap]
      have he : criticalLabelShift r ℓ-criticalLabelShift p ℓ-criticalLabelShift q ℓ=
          criticalLabelShift r ℓ-criticalLabelShift q ℓ-criticalLabelShift p ℓ := by omega
      rw [he]
      ring
  have hc : criticalWeightedConeEuler P s t=criticalWeightedConeEuler P t s := by
    unfold criticalWeightedConeEuler
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    simp only [or_comm,hl]
  unfold criticalCompletedConeEuler
  rw [hc,mul_comm (criticalCofactor P s)]

private def line (ρ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  1+((ρ/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I

private theorem line_re (ρ : ℝ) (N : ℕ) (t : ℝ) : (line ρ N t).re=1+ρ/Real.log N := by
  simp only [line,Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]

private theorem line_measurable (ρ : ℝ) (N : ℕ) : Measurable (line ρ N) := by
  unfold line
  fun_prop

private theorem base_measurable (p : Nat.Primes) : Measurable (cubicPrimeBase p) := by
  unfold cubicPrimeBase
  fun_prop

private theorem weighted_measurable (P : Finset Nat.Primes) :
    Measurable (fun w : ℂ × ℂ => criticalWeightedConeEuler P w.1 w.2) := by
  classical
  unfold criticalWeightedConeEuler criticalWeightedLabelEuler
  apply Finset.measurable_sum
  intro r _
  apply Finset.measurable_sum
  intro p _
  apply Finset.measurable_sum
  intro q _
  by_cases h : p=r ∨ q=r
  · simp only [if_pos h]; fun_prop
  · simp only [if_neg h]
    apply Measurable.const_mul
    apply Finset.measurable_prod
    intro ℓ _
    have hx : Measurable (fun w : ℂ × ℂ => cubicPrimeBase ℓ w.1) :=
      (base_measurable ℓ).comp measurable_fst
    have hy : Measurable (fun w : ℂ × ℂ => cubicPrimeBase ℓ w.2) :=
      (base_measurable ℓ).comp measurable_snd
    unfold weightedConeEuler
    split_ifs <;>
      simp only [weightedConeEulerMinusTwo,weightedConeEulerMinusOne,weightedEuler] <;>
      fun_prop

private theorem cofactor_line_measurable (P : Finset Nat.Primes)
    (ρ : {r : ℝ // 0<r}) {N : ℕ} (hN : 2≤N) :
    Measurable (fun t => criticalCofactor P (line ρ N t)) := by
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have he (t : ℝ) : criticalCofactor P (line ρ N t)=
      ∑' n : ℕ,criticalCofactorTerm P (line ρ N t) n := by
    apply (criticalCofactor_hasSum P _).tsum_eq.symm
    rw [line_re]
    exact lt_add_of_pos_right _ (div_pos ρ.property hL)
  simp_rw [he]
  apply Measurable.tsum
  intro n
  simp_rw [criticalCofactorTerm_eq]
  split_ifs with hn
  · fun_prop
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (not_or.mp hn).1
    unfold line
    fun_prop

private def source (ρ₁ ρ₂ : {r : ℝ // 0<r}) (N : ℕ) (w : ℝ × ℝ) : ℂ :=
  criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
    (line ρ₁ N w.1) (line ρ₂ N w.2)

private theorem source_measurable (ρ₁ ρ₂ : {r : ℝ // 0<r})
    {N : ℕ} (hN : 2≤N) : Measurable (source ρ₁ ρ₂ N) := by
  unfold source criticalCompletedConeEuler
  exact ((weighted_measurable _).comp
    (((line_measurable ρ₁ N).comp measurable_fst).prodMk
      ((line_measurable ρ₂ N).comp measurable_snd))).mul
    (((cofactor_line_measurable _ ρ₁ hN).comp measurable_fst).mul
      ((cofactor_line_measurable _ ρ₂ hN).comp measurable_snd))

private def axisWeight (t : ℝ) : ℝ := 1/(1+|t|)^2

private theorem axisWeight_pos (t : ℝ) : 0<axisWeight t := by
  unfold axisWeight
  positivity

private theorem axisWeight_le_one (t : ℝ) : axisWeight t≤1 := by
  unfold axisWeight
  apply (div_le_one (by positivity)).mpr
  nlinarith [abs_nonneg t]

private theorem axisWeight_antitone {x y : ℝ} (h : |x|≤|y|) :
    axisWeight y≤axisWeight x := by
  unfold axisWeight
  gcongr

private theorem axisWeight_integrable : Integrable axisWeight := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  convert h using 1
  ext t
  rw [Real.norm_eq_abs,Real.rpow_neg (by positivity),Real.rpow_two]
  simp only [axisWeight,one_div]

private theorem weight_pair_integrable (K : ℝ) :
    Integrable (fun w : ℝ × ℝ => K*axisWeight w.1*axisWeight w.2)
      ((volume : Measure ℝ).prod volume) := by
  have h := (axisWeight_integrable.mul_prod axisWeight_integrable).const_mul K
  apply h.congr
  exact Eventually.of_forall (fun w => (mul_assoc K (axisWeight w.1) (axisWeight w.2)).symm)

private theorem schwartz_decay (Φ : SchwartzMap (ℝ × ℝ) ℂ) (k : ℕ) :
    ∃ B : ℝ, 0<B ∧ ∀ w : ℝ × ℝ,
      (1+|w.1|+|w.2|)^k*‖Φ w‖≤B*axisWeight w.1*axisWeight w.2 := by
  let S := (2 : ℝ)^(k+4)*(Finset.Iic (k+4,0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ
  let B := (2 : ℝ)^(k+4)*S+1
  have hS : 0≤S := by dsimp [S]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro w
  have hs : (1+‖w‖)^(k+4)*‖Φ w‖≤S := by
    simpa only [norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k+4,0))
        (k := k+4) (n := 0) le_rfl le_rfl Φ w)
  have hx : |w.1|≤‖w‖ := by simpa only [Prod.norm_def,Real.norm_eq_abs] using
    (le_max_left ‖w.1‖ ‖w.2‖)
  have hy : |w.2|≤‖w‖ := by simpa only [Prod.norm_def,Real.norm_eq_abs] using
    (le_max_right ‖w.1‖ ‖w.2‖)
  have hT : 0≤1+|w.1|+|w.2| := by positivity
  have hT' : 1+|w.1|+|w.2|≤2*(1+‖w‖) := by linarith
  have hxT : (1+|w.1|)^2≤(1+|w.1|+|w.2|)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg w.2]) 2
  have hyT : (1+|w.2|)^2≤(1+|w.1|+|w.2|)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg w.1]) 2
  have hb : 0≤(1+|w.1|+|w.2|)^k*‖Φ w‖ :=
    mul_nonneg (pow_nonneg hT k) (norm_nonneg _)
  have hh : (1+|w.1|+|w.2|)^k*‖Φ w‖*(1+|w.1|)^2*(1+|w.2|)^2≤B := by
    calc _ ≤ (1+|w.1|+|w.2|)^k*‖Φ w‖*
          (1+|w.1|+|w.2|)^2*(1+|w.1|+|w.2|)^2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hxT hb) hyT (sq_nonneg _)
              (mul_nonneg hb (sq_nonneg _))
         _ = (1+|w.1|+|w.2|)^(k+4)*‖Φ w‖ := by
           have hp (a b : ℝ) : a^k*b*a^2*a^2=a^(k+4)*b := by rw [pow_add]; ring
           exact hp _ _
         _ ≤ (2*(1+‖w‖))^(k+4)*‖Φ w‖ := by gcongr
         _ = (2 : ℝ)^(k+4)*((1+‖w‖)^(k+4)*‖Φ w‖) := by rw [mul_pow,mul_assoc]
         _ ≤ (2 : ℝ)^(k+4)*S := by gcongr
         _ ≤ B := by dsimp [B]; linarith
  simp only [axisWeight,mul_one_div]
  apply (le_div_iff₀ (by positivity : 0<(1+|w.2|)^2)).mpr
  apply (le_div_iff₀ (by positivity : 0<(1+|w.1|)^2)).mpr
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

private def sector (strict : Bool) : Set (ℝ × ℝ) :=
  {w | if strict then |w.1| < |w.2| else |w.1| ≤ |w.2|}

private theorem sector_measurable (strict : Bool) : MeasurableSet (sector strict) := by
  cases strict <;> dsimp [sector] <;> measurability

private theorem sector_le {strict : Bool} {w : ℝ × ℝ} (h : w∈sector strict) :
    |w.1|≤|w.2| := by
  cases strict
  · exact h
  · exact le_of_lt h

private theorem paired_bound (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (Φ : SchwartzMap (ℝ × ℝ) ℂ) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop, 2≤N ∧ ∀ w : ℝ × ℝ,
      ‖source ρ₁ ρ₂ N w*Φ w‖≤K*(Real.log N)^2*axisWeight w.1*axisWeight w.2 ∧
      ‖source ρ₁ ρ₂ N w*Φ w‖/(Real.log N)^2≤
        K*axisWeight w.2*(axisWeight (Real.log N*w.1)+axisWeight (Real.log N*w.2)) := by
  obtain ⟨C,hC,hsource⟩ := criticalCompletedConeEuler_uniform_axes_bound ρ₁ ρ₂
  obtain ⟨B,hB,hdecay⟩ := schwartz_decay Φ 54
  refine ⟨2*C*B,by positivity,?_⟩
  filter_upwards [hsource,eventually_ge_atTop 2] with N hs hN
  refine ⟨hN,?_⟩
  intro w
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hw₁ := (axisWeight_pos w.1).le
  have hw₂ := (axisWeight_pos w.2).le
  have hL₁ := (axisWeight_pos (Real.log N*w.1)).le
  have hL₂ := (axisWeight_pos (Real.log N*w.2)).le
  have henv : ‖source ρ₁ ρ₂ N w‖≤ C*(Real.log N)^2*(1+|w.1|+|w.2|)^54*
      (axisWeight (Real.log N*w.1)+axisWeight (Real.log N*w.2)) := by
    refine (hs w.1 w.2).trans_eq ?_
    simp only [axisWeight,abs_mul,abs_of_pos hL,div_eq_mul_inv,mul_add,one_mul]
    ac_rfl
  have hpair : ‖source ρ₁ ρ₂ N w*Φ w‖≤
      C*(Real.log N)^2*(B*axisWeight w.1*axisWeight w.2)*
        (axisWeight (Real.log N*w.1)+axisWeight (Real.log N*w.2)) := by
    rw [norm_mul]
    calc _ ≤ (C*(Real.log N)^2*(1+|w.1|+|w.2|)^54*
        (axisWeight (Real.log N*w.1)+axisWeight (Real.log N*w.2)))*‖Φ w‖ :=
          mul_le_mul_of_nonneg_right henv (norm_nonneg _)
         _ = C*(Real.log N)^2*((1+|w.1|+|w.2|)^54*‖Φ w‖)*
          (axisWeight (Real.log N*w.1)+axisWeight (Real.log N*w.2)) := by ac_rfl
         _ ≤ _ := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left (hdecay w) (mul_nonneg hC.le (sq_nonneg _)))
           (add_nonneg hL₁ hL₂)
  constructor
  · calc _ ≤ C*(Real.log N)^2*(B*axisWeight w.1*axisWeight w.2)*(1+1) := by
           apply hpair.trans
           exact mul_le_mul_of_nonneg_left
             (add_le_add (axisWeight_le_one _) (axisWeight_le_one _))
             (mul_nonneg (mul_nonneg hC.le (sq_nonneg _))
               (mul_nonneg (mul_nonneg hB.le hw₁) hw₂))
         _ = _ := by ring
  · apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    calc _ ≤ C*(Real.log N)^2*(B*1*axisWeight w.2)*
          (axisWeight (Real.log N*w.1)+axisWeight (Real.log N*w.2)) := by
           apply hpair.trans
           exact mul_le_mul_of_nonneg_right
             (mul_le_mul_of_nonneg_left
               (mul_le_mul_of_nonneg_right
                 (mul_le_mul_of_nonneg_left (axisWeight_le_one _) hB.le) hw₂)
               (mul_nonneg hC.le (sq_nonneg _))) (add_nonneg hL₁ hL₂)
         _ ≤ _ := by
           have hp : 0≤C*(Real.log N)^2*(B*axisWeight w.2)*
               (axisWeight (Real.log N*w.1)+axisWeight (Real.log N*w.2)) :=
             mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _))
               (mul_nonneg hB.le (axisWeight_pos _).le))
               (add_nonneg (axisWeight_pos _).le (axisWeight_pos _).le)
           have htwice := le_add_of_nonneg_right
             (a := C*(Real.log N)^2*(B*axisWeight w.2)*
               (axisWeight (Real.log N*w.1)+axisWeight (Real.log N*w.2))) hp
           convert htwice using 1 <;> ring

private def rescaledSector (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (Φ : SchwartzMap (ℝ × ℝ) ℂ) (strict : Bool) (N : ℕ) (w : ℝ × ℝ) : ℂ :=
  (sector strict).indicator (fun z => source ρ₁ ρ₂ N z*Φ z)
    (w.1/Real.log N,w.2)/(Real.log N : ℂ)^2

private theorem rescaled_measurable (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (Φ : SchwartzMap (ℝ × ℝ) ℂ) (strict : Bool) {N : ℕ} (hN : 2≤N) :
    Measurable (rescaledSector ρ₁ ρ₂ Φ strict N) := by
  have hf := ((source_measurable ρ₁ ρ₂ hN).mul Φ.continuous.measurable).indicator
    (sector_measurable strict)
  exact (hf.comp (by fun_prop)).div_const _

private theorem rescaled_bound (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (Φ : SchwartzMap (ℝ × ℝ) ℂ) (strict : Bool) :
    ∃ K : ℝ, 0<K ∧ ∀ᶠ N : ℕ in atTop, 2≤N ∧ ∀ w : ℝ × ℝ,
      ‖rescaledSector ρ₁ ρ₂ Φ strict N w‖≤K*axisWeight w.1*axisWeight w.2 := by
  obtain ⟨K,hK,hbound⟩ := paired_bound ρ₁ ρ₂ Φ
  refine ⟨2*K,by positivity,?_⟩
  filter_upwards [hbound] with N hN
  refine ⟨hN.1,?_⟩
  intro w
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N from lt_of_lt_of_le (by norm_num) hN.1))
  by_cases hw : (w.1/Real.log N,w.2)∈sector strict
  · have hw' := sector_le hw
    have hnear : |w.1|≤|Real.log N*w.2| := by
      change |w.1/Real.log N|≤|w.2| at hw'
      rw [abs_div,abs_of_pos hL,div_le_iff₀ hL] at hw'
      simpa only [abs_mul,abs_of_pos hL,mul_comm] using hw'
    have h := (hN.2 (w.1/Real.log N,w.2)).2
    have he : Real.log N*(w.1/Real.log N)=w.1 := by field_simp
    simp only [he] at h
    unfold rescaledSector
    rw [indicator_of_mem hw,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
    calc _ ≤ K*axisWeight w.2*(axisWeight w.1+axisWeight (Real.log N*w.2)) := h
         _ ≤ K*axisWeight w.2*(axisWeight w.1+axisWeight w.1) :=
           mul_le_mul_of_nonneg_left (add_le_add_right (axisWeight_antitone hnear) _)
             (mul_nonneg hK.le (axisWeight_pos _).le)
         _ = _ := by ring
  · simp only [rescaledSector,indicator_of_notMem hw,zero_div,norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (axisWeight_pos _).le) (axisWeight_pos _).le

private theorem source_mixed_limit (ρ₁ ρ₂ : {r : ℝ // 0<r}) (x y : ℝ) (hy : y≠0) :
    Tendsto (fun N : ℕ => source ρ₁ ρ₂ N (x/Real.log N,y)/(Real.log N : ℂ)^2)
      atTop (𝓝 ((Real.exp (-2*Real.eulerMascheroniConstant) : ℂ)*
        criticalMixedProfile ((ρ₁ : ℂ)+(x : ℂ)*Complex.I))) := by
  have hu : (ρ₁ : ℂ)+(x : ℂ)*Complex.I≠0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,mul_zero,zero_mul,sub_self,add_zero,Complex.zero_re] at h
    exact ρ₁.property.ne' h
  have h := criticalCompletedConeEuler_mixed_tendsto
    (Units.mk0 ((ρ₁ : ℂ)+(x : ℂ)*Complex.I) hu) (ρ₂ : ℂ) (Units.mk0 y hy)
  apply h.congr'
  filter_upwards with N
  have hfirst : 1+((ρ₁ : ℂ)+(x : ℂ)*Complex.I)/(Real.log N : ℂ)=
      line ρ₁ N (x/Real.log N) := by
    simp only [line,Complex.ofReal_div]
    ring
  have hsecond : 1+((ρ₂ : ℂ)/(Real.log N : ℂ)+(y : ℂ)*Complex.I)=line ρ₂ N y := by
    simp only [line,Complex.ofReal_div]
    ring
  change criticalCompletedConeEuler _
      (1+((ρ₁ : ℂ)+(x : ℂ)*Complex.I)/(Real.log N : ℂ))
      (1+((ρ₂ : ℂ)/(Real.log N : ℂ)+(y : ℂ)*Complex.I))/(Real.log N : ℂ)^2=_
  rw [hfirst,hsecond]
  rfl

private theorem rescaled_limit (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (Φ : SchwartzMap (ℝ × ℝ) ℂ) (strict : Bool) (w : ℝ × ℝ) (hy : w.2≠0) :
    Tendsto (fun N : ℕ => rescaledSector ρ₁ ρ₂ Φ strict N w) atTop
      (𝓝 (((Real.exp (-2*Real.eulerMascheroniConstant) : ℂ)*
        criticalMixedProfile ((ρ₁ : ℂ)+(w.1 : ℂ)*Complex.I))*Φ (0,w.2))) := by
  have hpoint := source_mixed_limit ρ₁ ρ₂ w.1 w.2 hy
  have hphi := (Φ.continuous.tendsto (0,w.2)).comp
    ((tendsto_drift_zero w.1).prodMk_nhds (tendsto_const_nhds (x := w.2)))
  have hzero : Tendsto (fun N : ℕ => |w.1/Real.log N|) atTop (𝓝 0) := by
    simpa only [abs_zero] using (tendsto_drift_zero w.1).abs
  have hlt : ∀ᶠ N : ℕ in atTop, |w.1/Real.log N| < |w.2| :=
    hzero.eventually (gt_mem_nhds (abs_pos.mpr hy))
  apply (hpoint.mul hphi).congr'
  filter_upwards [hlt] with N hN
  have hw : (w.1/Real.log N,w.2)∈sector strict := by
    cases strict
    · exact hN.le
    · exact hN
  simp only [rescaledSector,indicator_of_mem hw,Function.comp_apply]
  ring

private theorem rescaled_integral_tendsto (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (Φ : SchwartzMap (ℝ × ℝ) ℂ) (strict : Bool) :
    Tendsto (fun N : ℕ => ∫ w : ℝ × ℝ,rescaledSector ρ₁ ρ₂ Φ strict N w)
      atTop (𝓝 0) := by
  obtain ⟨K,hK,hbound⟩ := rescaled_bound ρ₁ ρ₂ Φ strict
  have hi : Integrable (fun w : ℝ × ℝ => K*axisWeight w.1*axisWeight w.2) := by
    exact weight_pair_integrable K
  have hm : ∀ᶠ N : ℕ in atTop, AEStronglyMeasurable (rescaledSector ρ₁ ρ₂ Φ strict N) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (rescaled_measurable ρ₁ ρ₂ Φ strict hN).aestronglyMeasurable
  have hb : ∀ᶠ N : ℕ in atTop, ∀ᵐ w : ℝ × ℝ,
      ‖rescaledSector ρ₁ ρ₂ Φ strict N w‖≤K*axisWeight w.1*axisWeight w.2 := by
    filter_upwards [hbound] with N hN
    exact Eventually.of_forall hN.2
  have hne : ∀ᵐ w : ℝ × ℝ, w.2≠0 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    exact Eventually.of_forall (fun _ => volume.ae_ne (0 : ℝ))
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun w : ℝ × ℝ => K*axisWeight w.1*axisWeight w.2) hm hb hi
    (hne.mono (fun w hw => rescaled_limit ρ₁ ρ₂ Φ strict w hw))
  have hzero : (∫ w : ℝ × ℝ,
      ((Real.exp (-2*Real.eulerMascheroniConstant) : ℂ)*
        criticalMixedProfile ((ρ₁ : ℂ)+(w.1 : ℂ)*Complex.I))*Φ (0,w.2))=0 := by
    change (∫ w : ℝ × ℝ,
      ((Real.exp (-2*Real.eulerMascheroniConstant) : ℂ)*
        criticalMixedProfile ((ρ₁ : ℂ)+(w.1 : ℂ)*Complex.I))*Φ (0,w.2)
        ∂(volume : Measure ℝ).prod volume)=0
    rw [integral_prod_mul
      (fun x : ℝ => (Real.exp (-2*Real.eulerMascheroniConstant) : ℂ)*
        criticalMixedProfile ((ρ₁ : ℂ)+(x : ℂ)*Complex.I))
      (fun y : ℝ => Φ (0,y)),integral_const_mul,(criticalMixedProfile_vertical_integral_zero ρ₁).2,
      mul_zero,zero_mul]
  rwa [hzero] at hlim

private theorem pairing_integrable (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (Φ : SchwartzMap (ℝ × ℝ) ℂ) :
    ∀ᶠ N : ℕ in atTop, Integrable (fun w => source ρ₁ ρ₂ N w*Φ w) := by
  obtain ⟨K,hK,hbound⟩ := paired_bound ρ₁ ρ₂ Φ
  filter_upwards [hbound] with N hN
  have hi : Integrable (fun w : ℝ × ℝ => K*(Real.log N)^2*axisWeight w.1*axisWeight w.2) := by
    exact weight_pair_integrable (K*(Real.log N)^2)
  exact hi.mono' (((source_measurable ρ₁ ρ₂ hN.1).mul Φ.continuous.measurable).aestronglyMeasurable)
    (Eventually.of_forall (fun w => (hN.2 w).1))

private theorem rescaled_integrable (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (Φ : SchwartzMap (ℝ × ℝ) ℂ) (strict : Bool) :
    ∀ᶠ N : ℕ in atTop, Integrable (rescaledSector ρ₁ ρ₂ Φ strict N) := by
  obtain ⟨K,hK,hbound⟩ := rescaled_bound ρ₁ ρ₂ Φ strict
  filter_upwards [hbound] with N hN
  have hi : Integrable (fun w : ℝ × ℝ => K*axisWeight w.1*axisWeight w.2) := by
    exact weight_pair_integrable K
  exact hi.mono' (rescaled_measurable ρ₁ ρ₂ Φ strict hN.1).aestronglyMeasurable
    (Eventually.of_forall hN.2)

private theorem rescale_integral {g : ℝ × ℝ → ℂ} (hg : Integrable g)
    {L : ℝ} (hL : 0<L)
    (hi : Integrable (fun w : ℝ × ℝ => g (w.1/L,w.2)/(L : ℂ)^2)) :
    (∫ w : ℝ × ℝ,g (w.1/L,w.2)/(L : ℂ)^2)=(∫ w : ℝ × ℝ,g w)/(L : ℂ) := by
  change (∫ w : ℝ × ℝ,g (w.1/L,w.2)/(L : ℂ)^2 ∂volume.prod volume)=_
  rw [integral_prod_symm _ hi]
  have he (y : ℝ) : (∫ x : ℝ,g (x/L,y)/(L : ℂ)^2)=
      (∫ x : ℝ,g (x,y))/(L : ℂ) := by
    rw [integral_div,Measure.integral_comp_div (fun x : ℝ => g (x,y)) L,abs_of_pos hL]
    change (L : ℂ)*(∫ x : ℝ,g (x,y))/(L : ℂ)^2=_
    have hLc : (L : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL.ne'
    field_simp
  simp_rw [he]
  rw [integral_div]
  congr 1
  exact (integral_prod_symm g hg).symm

private theorem sector_integral_tendsto (ρ₁ ρ₂ : {r : ℝ // 0<r})
    (Φ : SchwartzMap (ℝ × ℝ) ℂ) (strict : Bool) :
    Tendsto (fun N : ℕ => (∫ w : ℝ × ℝ,
      (sector strict).indicator (fun z => source ρ₁ ρ₂ N z*Φ z) w)/(Real.log N : ℂ))
      atTop (𝓝 0) := by
  apply (rescaled_integral_tendsto ρ₁ ρ₂ Φ strict).congr'
  filter_upwards [pairing_integrable ρ₁ ρ₂ Φ,rescaled_integrable ρ₁ ρ₂ Φ strict,
    eventually_ge_atTop 2] with N hi hr hN
  exact rescale_integral (hi.indicator (sector_measurable strict))
    (Real.log_pos (by exact_mod_cast (show 1<N by omega))) hr

private def swapTest (Φ : SchwartzMap (ℝ × ℝ) ℂ) : SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) Φ

private theorem partition_integral (f : ℝ × ℝ → ℂ) (hf : Integrable f) :
    (∫ w : ℝ × ℝ,f w)=(∫ w : ℝ × ℝ,(sector false).indicator f w)+
      ∫ w : ℝ × ℝ,(sector true).indicator (fun z => f z.swap) w := by
  have he (w : ℝ × ℝ) : f w=(sector false).indicator f w+
      (sector true).indicator (fun z => f z.swap) w.swap := by
    by_cases hw : |w.1|≤|w.2|
    · simp [sector,hw,not_lt.mpr hw]
    · simp [sector,hw,lt_of_not_ge hw]
  calc _ = ∫ w : ℝ × ℝ,(sector false).indicator f w+
        (sector true).indicator (fun z => f z.swap) w.swap := by
          apply integral_congr_ae
          exact Eventually.of_forall he
       _ = (∫ w : ℝ × ℝ,(sector false).indicator f w)+
          ∫ w : ℝ × ℝ,(sector true).indicator (fun z => f z.swap) w.swap :=
            integral_add (hf.indicator (sector_measurable false))
              ((hf.swap.indicator (sector_measurable true)).swap)
       _ = _ := by
         congr 1
         exact integral_prod_swap _

/-- Signed full-plane cancellation for the actual complete growing source
against every fixed Schwartz test. Both growing cofactors, both exclusions,
the allowed first/second collision and all valuation sectors are retained. -/
theorem criticalCompletedConeEuler_schwartz_integral_tendsto
    (ρ₁ ρ₂ : {r : ℝ // 0<r}) (Φ : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (fun N : ℕ => (∫ w : ℝ × ℝ,
      criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
        (1+(((ρ₁ : ℝ)/Real.log N : ℝ) : ℂ)+(w.1 : ℂ)*Complex.I)
        (1+(((ρ₂ : ℝ)/Real.log N : ℝ) : ℂ)+(w.2 : ℂ)*Complex.I)*Φ w)/
          (Real.log N : ℂ)) atTop (𝓝 0) := by
  have h₁ := sector_integral_tendsto ρ₁ ρ₂ Φ false
  have h₂ := sector_integral_tendsto ρ₂ ρ₁ (swapTest Φ) true
  have h := h₁.add h₂
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [pairing_integrable ρ₁ ρ₂ Φ] with N hi
  change _=(∫ w : ℝ × ℝ,source ρ₁ ρ₂ N w*Φ w)/(Real.log N : ℂ)
  rw [partition_integral _ hi,add_div]
  have he : (∫ w : ℝ × ℝ,(sector true).indicator
      (fun z => source ρ₂ ρ₁ N z*swapTest Φ z) w)=
      ∫ w : ℝ × ℝ,(sector true).indicator
        (fun z => source ρ₁ ρ₂ N z.swap*Φ z.swap) w := by
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : w∈sector true
    · simp only [indicator_of_mem hw]
      change criticalCompletedConeEuler _ (line ρ₂ N w.1) (line ρ₁ N w.2)*Φ w.swap=
        criticalCompletedConeEuler _ (line ρ₁ N w.2) (line ρ₂ N w.1)*Φ w.swap
      rw [source_swap]
    · simp only [indicator_of_notMem hw]
  rw [he]


end RHTower.BAGTrace
