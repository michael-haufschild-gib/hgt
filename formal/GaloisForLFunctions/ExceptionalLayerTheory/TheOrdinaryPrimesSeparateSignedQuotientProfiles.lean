import GaloisForLFunctions.RHTower.HarmonicResidueAbscissaReader
import GaloisForLFunctions.RHTower.PrimeZetaAbelRepresentation
import GaloisForLFunctions.ExceptionalLayerTheory.EveryFiniteCofactorSeesTheOrdinaryPrimeCount
import GaloisForLFunctions.ExceptionalLayerTheory.DistinctPrimeFactorsInDyadicBinomialGcds

/-!
# The prime logarithm and signed quotient profiles

On the real ray to the right of one the prime series tends to infinity,
while its product with the distance to one tends to zero. These two
limits exclude every integer order of a meromorphic germ. Thus multiplication
by a nonzero meromorphic symbol cannot remove this singularity.
-/

noncomputable section

open Complex Filter Topology Set Finset ArithmeticFunction
open scoped LSeries.notation

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem primeZeta_right_limits :
    Tendsto _root_.RHTower.primeZeta (𝓝[>] (1:ℝ)) atTop ∧
    Tendsto (fun x : ℝ => (x-1)*_root_.RHTower.primeZeta x) (𝓝[>] (1:ℝ)) (𝓝 0) := by
  have h := _root_.RHTower.tendsto_primeZeta_add_log_sub
  have hδ : Tendsto (fun x : ℝ => x-1) (𝓝[>] 1) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' 1 0 (sub_self _)).mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun x : ℝ => x*Real.log x) (𝓝 0) (𝓝 0) := by
    simpa using Real.continuous_mul_log.tendsto 0
  constructor
  · apply (h.add_atTop _root_.RHTower.tendsto_abscissaLog_atTop).congr
    intro x
    dsimp only [_root_.RHTower.abscissaLog]
    ring
  · convert (hδ.mul h).sub (hlog.comp hδ) using 1
    · funext x; dsimp only [Function.comp_apply]; ring
    · ring

private theorem real_right_tendsto_complex_punctured : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (1:ℝ))),?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun eq => (show (1:ℝ)<x from hx).ne' (by exact_mod_cast eq)

/-- No meromorphic germ at one agrees on the right real ray with the ordinary
prime series. The obstruction already holds along that single ray. -/
theorem primeZeta_no_meromorphic_right_germ (F : ℂ → ℂ) (hF : MeromorphicAt F 1) :
    ¬ (fun x : ℝ => F x) =ᶠ[𝓝[>] 1] fun x => (_root_.RHTower.primeZeta x:ℂ) := by
  intro he
  obtain ⟨h∞,hzero⟩ := primeZeta_right_limits
  have hlarge : Tendsto (fun x : ℝ => ‖F x‖) (𝓝[>] 1) atTop := by
    apply h∞.congr'
    filter_upwards [he,h∞.eventually_ge_atTop 0] with x hx hp
    rw [hx,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  let G := (fun z : ℂ => z-1)*F
  have hsmall : Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 0) := by
    apply (show Tendsto (fun x : ℝ => (((x-1)*_root_.RHTower.primeZeta x:ℝ):ℂ))
        (𝓝[>] 1) (𝓝 0) by simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hzero).congr'
    filter_upwards [he] with x hx
    simp only [G,Pi.mul_apply,hx,ofReal_mul,ofReal_sub,ofReal_one]
  have hneg : meromorphicOrderAt F 1<0 := by
    by_contra! h
    obtain ⟨c,hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hF h
    exact not_tendsto_atTop_of_tendsto_nhds (hc.comp real_right_tendsto_complex_punctured).norm hlarge
  obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp hneg.ne_top
  have hkneg : k<0 := by simpa only [← hk,← WithTop.coe_zero,WithTop.coe_lt_coe] using hneg
  have hlin : MeromorphicAt (fun z : ℂ => z-1) 1 := (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hG : MeromorphicAt G 1 := hlin.mul hF
  have ho : meromorphicOrderAt G 1=((1+k:ℤ):WithTop ℤ) := by
    rw [G,meromorphicOrderAt_mul hlin hF,meromorphicOrderAt_id_sub_const,← hk]
    norm_cast
  rcases lt_or_eq_of_le (by omega : 1+k≤0) with hl | hz
  · have hlt : meromorphicOrderAt G 1<0 := by rw [ho]; exact_mod_cast hl
    have ht := (tendsto_norm_atTop_iff_cobounded.mpr (tendsto_cobounded_of_meromorphicOrderAt_neg hlt)).comp real_right_tendsto_complex_punctured
    exact not_tendsto_atTop_of_tendsto_nhds hsmall.norm ht
  · have hzero' : meromorphicOrderAt G 1=0 := by simp [ho,hz]
    obtain ⟨c,hc,hl⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hG hzero'
    exact hc (tendsto_nhds_unique (hl.comp real_right_tendsto_complex_punctured) hsmall)

#print axioms primeZeta_no_meromorphic_right_germ

private def quotientProfileCoefficients (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n-f (n-1),by simp⟩

private theorem quotientProfile_prefix (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, quotientProfileCoefficients f n = f N-f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1≤N+1),ih]
    change f N-f 0+(f (N+1)-f ((N+1)-1))=_
    simp only [Nat.add_sub_cancel]; ring

private theorem ordinaryPrime_series_real {x : ℝ} (hx : 1<x) :
    LSeries (fun n => (lastClassOrdinaryPrimeIndicator n : ℂ)) (x:ℂ)=(_root_.RHTower.primeZeta x:ℂ) := by
  rw [← _root_.RHTower.tsum_primeIndicatorRpow,Complex.ofReal_tsum]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n.Prime
  · rw [if_pos hn,LSeries.term_of_ne_zero hn.ne_zero]
    have hp : lastClassOrdinaryPrimeIndicator n=1 := if_pos hn
    rw [hp,ofReal_one,one_div,Complex.ofReal_cpow (Nat.cast_nonneg n),ofReal_neg,ofReal_natCast,Complex.cpow_neg]
  · have hp : lastClassOrdinaryPrimeIndicator n=0 := if_neg hn
    simp [hn,LSeries.term,hp]

private theorem real_prefix_bound {a : ArithmeticFunction ℝ} {b C : ℝ} (hb : 0≤b) (hC : 0≤C)
    (h : ∀ N : ℕ, 1≤N → |∑ n ∈ Icc 1 N, a n| ≤ C*(N:ℝ)^b) {x : ℝ} (hx : 1≤x) :
    ‖∑ n ∈ Icc 1 ⌊x⌋₊, (a n:ℂ)‖ ≤ C*x^b := by
  rw [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs]
  exact (h _ ((Nat.one_le_floor_iff x).mpr hx)).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (zero_le_one.trans hx)) hb) hC)

/-- A profile of strictly sublinear power growth has an unweighted prime count
of strictly sublinear power growth only when it vanishes at every positive integer. -/
theorem sublinear_prime_quotient_count_iff_zero (f : ℕ → ℝ) {a b : ℝ}
    (ha : 0≤a) (ha1 : a<1) (hb : 0≤b) (hb1 : b<1)
    (hf : ∃ B : ℝ, 0≤B ∧ ∀ n : ℕ, 1≤n → |f n|≤B*(n:ℝ)^a) :
    (∃ C : ℝ, ∀ N : ℕ, 1≤N → |∑ p ∈ Nat.primesLE N, f (N/p)| ≤ C*(N:ℝ)^b) ↔
      ∀ n : ℕ, 1≤n → f n=0 := by
  constructor
  · rintro ⟨C,hC⟩
    obtain ⟨B,hB,hf⟩ := hf
    let F := fun n : ℕ => if n=0 then (0:ℝ) else f n
    let d := quotientProfileCoefficients F
    let v := lastClassOrdinaryPrimeIndicator
    let P := LSeries (fun n => (v n:ℂ))
    let D := HeckeLFunctions.growthCont (fun n => (d n:ℂ)) a
    let H := HeckeLFunctions.growthCont (fun n => ((v*d) n:ℂ)) b
    have hdpre (N : ℕ) : ∑ n ∈ Icc 1 N, d n=F N := by
      rw [d,quotientProfile_prefix,show F 0=0 by simp [F],sub_zero]
    have hp (N : ℕ) : ∑ n ∈ Icc 1 N, (v*d) n = ∑ p ∈ Nat.primesLE N, f (N/p) := by
      rw [_root_.RHTower.sum_Icc_mul_apply,Nat.primesLE_eq_filter_Icc_one,sum_filter]
      refine sum_congr rfl fun p hp => ?_
      have hdiv := (Nat.one_le_div_iff (mem_Icc.mp hp).1).mpr (mem_Icc.mp hp).2
      rw [hdpre,F,if_neg (Nat.ne_of_gt hdiv)]
      change (if p.Prime then (1:ℝ) else 0)*_=_
      split <;> simp_all
    have hC0 : 0≤C := by simpa using (abs_nonneg _).trans (hC 1 le_rfl)
    have hDpre (x : ℝ) (hx : 1≤x) : ‖∑ n ∈ Icc 1 ⌊x⌋₊, (d n:ℂ)‖≤B*x^a :=
      real_prefix_bound ha hB (fun N hn => by rw [hdpre,F,if_neg (Nat.ne_of_gt hn)]; exact hf N hn) hx
    have hHpre (x : ℝ) (hx : 1≤x) : ‖∑ n ∈ Icc 1 ⌊x⌋₊, ((v*d) n:ℂ)‖≤C*x^b :=
      real_prefix_bound hb hC0 (fun N hn => by rw [hp]; exact hC N hn) hx
    have hD : DifferentiableOn ℂ D {z : ℂ | a<z.re} :=
      HeckeLFunctions.differentiableOn_growthCont (by simp) ha hDpre
    have hH : DifferentiableOn ℂ H {z : ℂ | b<z.re} :=
      HeckeLFunctions.differentiableOn_growthCont (by simp) hb hHpre
    have hv {s : ℂ} (hs : 1<s.re) : LSeriesSummable (fun n => (v n:ℂ)) s := by
      apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
      intro n _
      by_cases hn : n.Prime
      · rw [show v n=1 from if_pos hn]; simp
      · rw [show v n=0 from if_neg hn]; simp
    have hP : DifferentiableOn ℂ P {z : ℂ | 1<z.re} := by
      intro z hz
      obtain ⟨u,hu,hu'⟩ := exists_between (show 1<z.re from hz)
      have hab := (hv (s := (u:ℂ)) hu).abscissaOfAbsConv_le
      exact (LSeries_hasDerivAt (hab.trans_lt (by exact_mod_cast hu'))).differentiableAt.differentiableWithinAt
    have hFlinear (n : ℕ) : |F n|≤B*n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [F]
      rw [F,if_neg hn.ne']
      exact (hf n hn).trans (mul_le_mul_of_nonneg_left (by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1≤(n:ℝ)) ha1.le) hB)
    have hd {s : ℂ} (hs : 2<s.re) : LSeriesSummable (fun n => (d n:ℂ)) s := by
      apply LSeriesSummable_of_le_const_mul_rpow hs
      refine ⟨2*B,fun n _ => ?_⟩
      rw [Complex.norm_real,Real.norm_eq_abs,show (2:ℝ)-1=1 by norm_num,Real.rpow_one]
      change |F n-F (n-1)|≤_
      have ht := (hFlinear (n-1)).trans (mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.sub_le n 1 : ((n-1:ℕ):ℝ)≤n) hB)
      exact ((abs_sub _ _).trans (add_le_add (hFlinear n) ht)).trans_eq (by ring)
    have hDS {s : ℂ} (hs : 2<s.re) : D s=LSeries (fun n => (d n:ℂ)) s :=
      HeckeLFunctions.growthCont_eq_LSeries (by simp) ha hDpre (by linarith only [ha1,hs]) (hd hs)
    have hfact {s : ℂ} (hs : 2<s.re) : H s=(P*D) s := by
      have hs1 : 1<s.re := by linarith only [hs]
      have he : (fun n => ((v*d) n:ℂ))=((fun n => (v n:ℂ)) ⍟ fun n => (d n:ℂ)) := by
        funext n
        rw [LSeries.convolution_def]
        exact _root_.RHTower.Sieve.coe_mul_apply _ _ _
      have hcs : LSeriesSummable (fun n => ((v*d) n:ℂ)) s := by rw [he]; exact (hv hs1).convolution (hd hs)
      rw [show H s=LSeries _ s from HeckeLFunctions.growthCont_eq_LSeries (by simp) hb hHpre
        (hb1.trans hs1) hcs,he,LSeries_convolution' (hv hs1) (hd hs),Pi.mul_apply,hDS hs]
    have hopen (u : ℝ) : IsOpen {z : ℂ | u<z.re} := isOpen_lt continuous_const Complex.continuous_re
    have heuler : EqOn H (P*D) {z : ℂ | 1<z.re} :=
      ((hH.mono (fun _ hz => hb1.trans hz)).analyticOnNhd (hopen 1)).eqOn_of_preconnected_of_eventuallyEq
        ((hP.mul (hD.mono fun _ hz => ha1.trans hz)).analyticOnNhd (hopen 1))
        (convex_halfSpace_re_gt 1).isPreconnected (z₀ := (3:ℂ)) (by norm_num)
        (((hopen 2).mem_nhds (show (3:ℂ) ∈ {z : ℂ | 2<z.re} by norm_num)).mono fun _ hz => hfact hz)
    have hDmer : MeromorphicOn D {z : ℂ | a<z.re} := (hD.analyticOnNhd (hopen a)).meromorphicOn
    have h1 : (1:ℂ) ∈ {z : ℂ | a<z.re} := by simpa using ha1
    have ht : meromorphicOrderAt D 1=⊤ := by
      by_contra hn
      have hG := ((hH.analyticOnNhd (hopen b) 1 (by simpa using hb1)).meromorphicAt).div (hDmer 1 h1)
      apply primeZeta_no_meromorphic_right_germ (H/D) hG
      filter_upwards [real_right_tendsto_complex_punctured.eventually
        ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hDmer 1 h1)).mp hn),self_mem_nhdsWithin] with x hdx hx
      change H x / D x = _
      rw [heuler (show (x:ℂ) ∈ {z : ℂ | 1<z.re} from hx),Pi.mul_apply,mul_div_cancel_right₀ _ hdx,
        show P x=(_root_.RHTower.primeZeta x:ℂ) from ordinaryPrime_series_real hx]
    have hall : (fun x : ℝ => LSeries (fun n => (d n:ℂ)) x) =ᶠ[atTop] 0 := by
      filter_upwards [eventually_gt_atTop (2:ℝ)] with x hx
      have hx' : (x:ℂ) ∈ {z : ℂ | a<z.re} := by change a<x; linarith only [ha1,hx]
      have ht' : meromorphicOrderAt D (x:ℂ)=⊤ := by
        by_contra hh
        exact (hDmer.meromorphicOrderAt_ne_top_of_isPreconnected (convex_halfSpace_re_gt a).isPreconnected hx' h1 hh) ht
      have he := meromorphicOrderAt_eq_top_iff.mp ht'
      have hl : Tendsto D (𝓝[≠] (x:ℂ)) (𝓝 0) := tendsto_const_nhds.congr' he.symm
      rw [← hDS (s := (x:ℂ)) hx]
      exact tendsto_nhds_unique ((hD.analyticOnNhd (hopen a) _ hx').continuousAt.continuousWithinAt.tendsto) hl
    have hab := (hd (s := (3:ℂ)) (by norm_num)).abscissaOfAbsConv_le
    have hz := (LSeries_eventually_eq_zero_iff'.mp hall).resolve_right (ne_top_of_le_ne_top (EReal.coe_ne_top _) hab)
    intro n hn
    have hsum : ∑ m ∈ Icc 1 n, d m=0 :=
      sum_eq_zero fun m hm => Complex.ofReal_eq_zero.mp (hz m (Nat.ne_of_gt (mem_Icc.mp hm).1))
    rwa [hdpre,F,if_neg (Nat.ne_of_gt hn)] at hsum
  · refine fun h => ⟨0,fun N _ => ?_⟩
    have he (p : ℕ) (hp : p∈Nat.primesLE N) := h (N/p)
      ((Nat.one_le_div_iff (Nat.prime_of_mem_primesLE hp).pos).mpr (Nat.mem_primesLE.mp hp).1)
    rw [sum_eq_zero he,abs_zero,zero_mul]

#print axioms sublinear_prime_quotient_count_iff_zero

end GaloisForLFunctions.ExceptionalLayerTheory
