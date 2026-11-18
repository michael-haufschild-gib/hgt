import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.ConductorGraphPrimeLimit
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.DilatingTheOrdinaryPrimeMeasure
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniW02Correction

/-!
# Pole moments from separated conductor graph contacts

Move the upper divisor through a multiplicative factor x. Its directed finite-place
logarithmic restriction order, normalized by √x, recovers the product of opposite
pole moments. Ordinary primes already give this limit. Both graph profiles may be signed.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Filter Topology MeasureTheory Finset Zeta23 _root_.RHTower LogCells
open scoped ArithmeticFunction.vonMangoldt

/-- All proper prime powers below the moving edge have vanishing linear density. -/
private theorem proper_mass {B : ℝ} (hB : 0 < B) :
    Tendsto (fun x : ℝ => (Chebyshev.psi (B*x) - Chebyshev.theta (B*x))/x)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => B*x) atTop atTop := tendsto_id.const_mul_atTop hB
  have h := ((tendsto_psi_div_self.sub tendsto_theta_div_self).comp ht).mul_const B
  rw [sub_self, zero_mul] at h
  apply h.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun x hx => ?_)
  change (_ / (B*x) - _ / (B*x))*B = _
  field_simp [hB.ne',hx.ne']

private theorem compact_prime_limits {H : ℝ → ℝ} (hc : Continuous H) (hk : HasCompactSupport H) :
    Tendsto (fun x : ℝ => (∑' p : Nat.Primes, Real.log (p : ℕ)*H ((p : ℕ)/x))/x)
        atTop (𝓝 (∫ y in Set.Ici (0:ℝ), H y)) ∧
    Tendsto (fun x : ℝ => (∑' k : ℕ, Λ k * H (k/x))/x)
        atTop (𝓝 (∫ y in Set.Ici (0:ℝ), H y)) := by
  classical
  have hc' : Continuous (fun y : ℝ => H y * (1+y^2)) := hc.mul (by fun_prop)
  obtain ⟨C,hC⟩ := (hk.mul_right (f' := fun y : ℝ => 1+y^2)).exists_bound_of_continuous hc'
  have hC' : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hp := ExclusionOfTheCriticalState.tendsto_dilated_ordinary_prime_sum hc hC' (fun y _ => by
    apply (le_div_iff₀ (by positivity : 0 < 1+y^2)).mpr
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (show 0 < 1+y^2 by positivity)] using hC y)
  refine ⟨hp, ?_⟩
  obtain ⟨D,hD⟩ := hk.exists_bound_of_continuous hc
  obtain ⟨b,hb⟩ := hk.bddAbove
  let B := max b 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hz {y : ℝ} (hy : B < y) : H y = 0 := by
    by_contra hn
    exact hy.not_ge ((hb (subset_tsupport H hn)).trans (le_max_left _ _))
  let F (x : ℝ) (k : ℕ) := Λ k * H (k/x)
  let S (x : ℝ) := Finset.Ioc 0 ⌊B*x⌋₊
  have hout {x : ℝ} (hx : 0 < x) {k : ℕ} (hk' : k ∉ S x) : F x k = 0 := by
    by_cases hk0 : k = 0
    · simp [F,hk0]
    have hlt : ⌊B*x⌋₊ < k := by
      change k ∉ Finset.Ioc 0 ⌊B*x⌋₊ at hk'
      simp only [Finset.mem_Ioc,not_and] at hk'
      exact lt_of_not_ge (hk' (Nat.pos_of_ne_zero hk0))
    exact mul_eq_zero_of_right _ (hz ((lt_div_iff₀ hx).mpr (Nat.lt_of_floor_lt hlt)))
  have hsum {x : ℝ} (hx : 0 < x) :
      (∑' p : Nat.Primes, Real.log (p : ℕ)*H ((p : ℕ)/x)) =
        ∑ k ∈ (S x).filter Nat.Prime, F x k := by
    let P (k : ℕ) := if k.Prime then F x k else 0
    have he : (∑' p : Nat.Primes, P p.val) = ∑' k : ℕ, P k := by
      apply tsum_subtype_eq_of_support_subset (s := {k : ℕ | k.Prime})
      intro k hk'
      by_contra hn
      exact hk' (if_neg hn)
    calc _ = ∑' p : Nat.Primes, P p.val := tsum_congr fun p => by
           simp only [P,if_pos p.property,F,ArithmeticFunction.vonMangoldt_apply_prime p.property]
         _ = ∑' k : ℕ, P k := he
         _ = ∑ k ∈ S x, P k := tsum_eq_sum fun k hk' => by simp [P,hout hx hk']
         _ = _ := (Finset.sum_filter ..).symm
  let err (x : ℝ) := (∑ k ∈ (S x).filter (fun k => ¬ k.Prime), F x k)/x
  have herr : Tendsto err atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (g := fun x : ℝ => (Chebyshev.psi (B*x)-Chebyshev.theta (B*x))/x*D)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      dsimp only [err]
      rw [Real.norm_eq_abs,abs_div,abs_of_pos hx,div_mul_eq_mul_div₀]
      apply div_le_div_of_nonneg_right _ hx.le
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      change |Λ k * H (k/x)| ≤ Λ k * D
      rw [abs_mul,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_left (hD _) ArithmeticFunction.vonMangoldt_nonneg
    · simpa only [zero_mul] using (proper_mass hB).mul_const D
  have h := hp.add herr
  rw [add_zero] at h
  apply h.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun x hx => ?_)
  dsimp only [err]
  rw [hsum hx,← add_div,Finset.sum_filter_add_sum_filter_not]
  congr 1
  exact (tsum_eq_sum fun k hk' => hout hx hk').symm

/-- Transfer a compact logarithmic test to the positive multiplicative coordinate.
Its Jacobian turns the square-root weight into the positive half moment. -/
private theorem log_test {h : ℝ → ℝ} (hc : Continuous h) (hk : HasCompactSupport h) :
    ∃ H : ℝ → ℝ, Continuous H ∧ HasCompactSupport H ∧
      (∀ y : ℝ, 0 < y → H y = h (Real.log y)/Real.sqrt y) ∧
      (∫ y in Set.Ici (0:ℝ), H y) = ∫ t : ℝ, h t * Real.exp (t/2) := by
  obtain ⟨l,hl⟩ := hk.bddBelow
  obtain ⟨b,hb⟩ := hk.bddAbove
  let L := Real.exp (l-1)
  let U := Real.exp (max b l + 1)
  have hL : 0 < L := Real.exp_pos _
  have hLU : L < U := Real.exp_lt_exp.mpr (by linarith only [le_max_right b l])
  let z (y : ℝ) := max L y
  have hzc : Continuous z := continuous_const.max continuous_id
  have hzp (y : ℝ) : 0 < z y := hL.trans_le (le_max_left _ _)
  let H (y : ℝ) := h (Real.log (z y))/Real.sqrt (z y)
  have hlow {t : ℝ} (ht : t < l) : h t = 0 := by
    by_contra hn
    exact ht.not_ge (hl (subset_tsupport h hn))
  have hval {y : ℝ} (hy : 0 < y) : H y = h (Real.log y)/Real.sqrt y := by
    rcases le_total L y with hly | hyl
    · simp [H,z,max_eq_right hly]
    · have he : Real.log L = l-1 := Real.log_exp _
      have ht := (Real.log_le_log hy hyl).trans_eq he
      simp [H,z,max_eq_left hyl,he,hlow (by linarith : l-1 < l),hlow (by linarith : Real.log y < l)]
  refine ⟨H,(hc.comp (hzc.log fun y => (hzp y).ne')).div (Real.continuous_sqrt.comp hzc)
    (fun y => (Real.sqrt_pos.mpr (hzp y)).ne'), ?_, fun _ hy => hval hy, ?_⟩
  · apply HasCompactSupport.intro (K := Set.Icc L U) isCompact_Icc
    intro y hy
    by_cases hyl : y < L
    · simp [H,z,max_eq_left hyl.le,L,hlow (by linarith : l-1 < l)]
    have hu : U < y := lt_of_not_ge fun h => hy ⟨le_of_not_gt hyl,h⟩
    have hy' := hL.trans (hLU.trans hu)
    rw [hval hy']
    have hz' : h (Real.log y) = 0 := by
      by_contra hn
      have hh := hb (subset_tsupport h hn)
      have hv := Real.log_lt_log (Real.exp_pos _) hu
      rw [Real.log_exp] at hv
      linarith only [hh,hv,le_max_left b l]
    rw [hz',zero_div]
  · rw [integral_Ici_eq_integral_Ioi,← Real.range_exp,← Set.image_univ]
    rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
    rw [Measure.restrict_univ]
    apply integral_congr_ae (Eventually.of_forall fun t => ?_)
    rw [abs_of_pos (Real.exp_pos t), smul_eq_mul,hval (Real.exp_pos t),Real.log_exp]
    have hs : Real.exp t = Real.exp (t/2)^2 := by rw [sq,← Real.exp_add]; congr 1; ring
    rw [hs,Real.sqrt_sq (Real.exp_pos _).le]
    field_simp

/-- Dilates of a compact logarithmic test against ordinary primes converge to its
positive half moment. The ordinary test is divided by the square root in
multiplicative coordinates. -/
theorem tendsto_ordinary_prime_log_test {h : ℝ → ℝ} (hc : Continuous h) (hk : HasCompactSupport h) :
    Tendsto (fun x : ℝ => (∑' p : Nat.Primes,
      Real.log (p:ℕ)*(h (Real.log ((p:ℕ)/x))/Real.sqrt ((p:ℕ)/x)))/x)
      atTop (𝓝 (∫ t : ℝ, h t*Real.exp (t/2))) := by
  obtain ⟨H,hH,hK,hp,hi⟩ := log_test hc hk
  rw [← hi]
  refine (compact_prime_limits hH hK).1.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  exact congrArg (·/x) (tsum_congr fun p : Nat.Primes => congrArg (Real.log (p:ℕ)*·)
    (hp _ (div_pos (Nat.cast_pos.mpr p.property.pos) hx)))

/-- Ordinary-prime part of the directed graph pairing. -/
def ordinaryGraphPair (f g : ℝ → ℝ) : ℝ :=
  ∑' p : Nat.Primes, (2*Real.log (p : ℕ)/Real.sqrt (p : ℕ)) *
    ∫ u : ℝ, f u * g (u + Real.log (p : ℕ))

/-- The mixed integral has the orientation of the upper graph at the positive pole. -/
private theorem mixed_lag (f g : ℝ → ℝ) (t : ℝ) :
    (∫ u : ℝ, f u * g (u+t)) = ccmRealCorrelation g f t := by
  rw [← ccmRealCorrelation_neg f g,ccmRealCorrelation]
  simp only [sub_neg_eq_add]

private theorem separated_weight {H h : ℝ → ℝ}
    (hH : ∀ y : ℝ, 0 < y → H y = h (Real.log y)/Real.sqrt y)
    (w : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2*w/Real.sqrt y*h (Real.log y - Real.log x)/Real.sqrt x = 2*(w*H (y/x)/x) := by
  rw [hH _ (div_pos hy hx),Real.log_div hy.ne' hx.ne',Real.sqrt_div hy.le]
  have hs := Real.sq_sqrt hx.le
  field_simp [(Real.sqrt_pos.mpr hy).ne',(Real.sqrt_pos.mpr hx).ne',hx.ne']
  linear_combination -(w*h (Real.log y-Real.log x))*hs

/-- Translating the upper graph to conductor scale x extracts the rank-one polar
pairing from its finite contacts. Removing every proper prime power gives the same limit. -/
theorem tendsto_separated_graph_pair {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    let upper := fun (x v : ℝ) => g (v-Real.log x)
    let P := 2*(ccmRealExponentialMoment (1/2) g * ccmRealExponentialMoment (-(1/2)) f)
    Tendsto (fun x : ℝ => ordinaryGraphPair f (upper x)/Real.sqrt x) atTop (𝓝 P) ∧
    Tendsto (fun x : ℝ => smoothPrimePair f (upper x)/Real.sqrt x) atTop (𝓝 P) := by
  dsimp only
  let h := ccmRealCorrelation g f
  have he : h = fun t => (EF.weilTest (cx g) (cx f) t).re := by
    funext t
    rw [weilTest_ofReal]
    rfl
  have hc : Continuous h := by
    rw [he]
    exact Complex.continuous_re.comp (EF.weilTest_contDiff (cx_contDiff hg) (cx_contDiff hf).continuous (cx_hasCompactSupport hgc)).continuous
  have hk : HasCompactSupport h := by
    rw [he]
    exact (EF.weilTest_hasCompactSupport (cx_hasCompactSupport hgc) (cx_hasCompactSupport hfc)).comp_left Complex.zero_re
  obtain ⟨H,hHc,hHk,hHv,hHi⟩ := log_test hc hk
  have htilt {a : ℝ} {v : ℝ → ℝ} (hv : Continuous v) (hvk : HasCompactSupport v) :
      Integrable (ccmRealExponentialTilt a v) :=
    (hv.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hvk.mul_right
  have hi := integral_ccmRealCorrelation_mul_exp (1/2) g f (htilt hg.continuous hgc) (htilt hf.continuous hfc)
  simp only [show ∀ t : ℝ, (1/2)*t = t/2 by intro t; ring] at hi
  change (∫ y in Set.Ici (0:ℝ), H y) = ∫ t : ℝ, ccmRealCorrelation g f t * Real.exp (t/2) at hHi
  rw [hi] at hHi
  obtain ⟨hp,ha⟩ := compact_prime_limits hHc hHk
  rw [hHi] at hp ha
  have hlag (x y : ℝ) : (∫ u : ℝ, f u * g (u+Real.log y-Real.log x)) =
      h (Real.log y-Real.log x) := by
    simpa only [← add_sub_assoc] using mixed_lag f g (Real.log y-Real.log x)
  constructor
  · apply (hp.const_mul 2).congr' ((eventually_gt_atTop (0:ℝ)).mono fun x hx => ?_)
    rw [ordinaryGraphPair, ← tsum_div_const, ← tsum_div_const, ← tsum_mul_left]
    exact tsum_congr fun p => by
      rw [hlag]
      exact (separated_weight hHv _ hx (Nat.cast_pos.mpr p.property.pos)).symm
  · apply (ha.const_mul 2).congr' ((eventually_gt_atTop (0:ℝ)).mono fun x hx => ?_)
    rw [smoothPrimePair, ← tsum_div_const, ← tsum_div_const, ← tsum_mul_left]
    apply tsum_congr
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp
    · rw [hlag]
      exact (separated_weight hHv _ hx (Nat.cast_pos.mpr hk')).symm

/-- A single sequence of finite integral graph restriction orders realizes the polar
product. Each sufficiently large multiplicity works at its specified separation. -/
theorem separated_graph_orders_recover_pole {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∃ (R : ℝ) (B : ℕ) (M : ℕ → ℕ), (0 < R ∧ 1 ≤ B) ∧
      ∀ s : ℕ → ℕ, (∀ᶠ n in atTop, M n ≤ s n) →
        Tendsto (fun n : ℕ => sampledGraphHeight (s n) (B*(n+1)) R f
          (fun v => g (v-Real.log n)) / (s n : ℝ)^2 / Real.sqrt n) atTop
          (𝓝 (2*(ccmRealExponentialMoment (1/2) g * ccmRealExponentialMoment (-(1/2)) f))) := by
  let upper (n : ℕ) := fun v : ℝ => g (v-Real.log n)
  obtain ⟨R,hR,B,hB,_,_,hw,_⟩ := exists_compact_logSamples_rate hf hg hfc hgc
  have hlim (n : ℕ) : Tendsto (fun m : ℕ => sampledGraphHeight m (B*(n+1)) R f (upper n)/(m : ℝ)^2)
      atTop (𝓝 (smoothPrimePair f (upper n))) := by
    apply tendsto_sampledGraphHeight_of_support hf (hg.comp (contDiff_id.sub contDiff_const)) hfc
      (hgc.comp_homeomorph (Homeomorph.subRight (Real.log (n:ℝ)))) (Nat.mul_pos hB (Nat.succ_pos n))
    intro u hu
    have hn := Real.log_natCast_nonneg n
    rcases hu with hl | hr
    · exact ⟨(hw _ (.inl hl)).1,(hw _ (.inl (show u-Real.log n ≤ -R by linarith))).2⟩
    · rw [Nat.cast_mul,Real.log_mul (show (B:ℝ) ≠ 0 by positivity) (show ((n+1:ℕ):ℝ) ≠ 0 by positivity)] at hr
      have hlog : Real.log (n : ℝ) ≤ Real.log ((n+1 : ℕ) : ℝ) := by
        rcases Nat.eq_zero_or_pos n with rfl | hn'
        · simp
        · exact Real.log_le_log (Nat.cast_pos.mpr hn') (by exact_mod_cast Nat.le_succ n)
      exact ⟨(hw _ (.inr (by linarith only [hr,hlog,hn]))).1,
        (hw _ (.inr (show Real.log B-R ≤ u-Real.log n by linarith only [hr,hlog]))).2⟩
  let A (n m : ℕ) := sampledGraphHeight m (B*(n+1)) R f (upper n)/(m : ℝ)^2/Real.sqrt n
  let L (n : ℕ) := smoothPrimePair f (upper n)/Real.sqrt n
  have he (n : ℕ) : ∃ M : ℕ, ∀ m ≥ M, |A n m - L n| < 1/((n : ℝ)+1) :=
    (Metric.tendsto_atTop.mp ((hlim n).div_const (Real.sqrt n)) _ (by positivity))
  choose M hM using he
  refine ⟨R,B,M,⟨hR,hB⟩,fun s hs => ?_⟩
  have hz : Tendsto (fun n => A n (s n)-L n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (hs.mono fun n hn => (hM n _ hn).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h := (tendsto_separated_graph_pair hf hg hfc hgc).2.comp tendsto_natCast_atTop_atTop
  simpa only [zero_add,sub_add_cancel,Function.comp_apply,A,L,upper] using hz.add h

#print axioms tendsto_separated_graph_pair
#print axioms tendsto_ordinary_prime_log_test
#print axioms separated_graph_orders_recover_pole

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
