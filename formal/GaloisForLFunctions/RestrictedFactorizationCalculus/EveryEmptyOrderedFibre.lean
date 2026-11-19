import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCubeRootExchange

/-!
# Evacuating every empty ordered fibre

Write an odd source as `a*r`, with largest prime `r`. At every sufficiently
large cutoff the scale `X/a` grows uniformly: otherwise all prime factors of
the squarefree source would belong to a fixed primorial. Empty positive supply
in the ordered fibre then forces the largest prime of `a` above `√(X/a)`.
Removing that prime with `r` puts the source in the cube-root exchange band.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- If the cofactor primes are below the square root of its quotient scale,
two larger primes in separated windows give a positive endpoint. -/
private theorem eventually_positive_fibre :
    ∃ Y : ℝ, ∀ X a : ℕ, Squarefree a → Even a.primeFactors.card →
      Y ≤ Real.sqrt ((X:ℝ)/a) →
      (∀ d ∈ a.primeFactors, (d:ℝ) ≤ Real.sqrt ((X:ℝ)/a)) → (fibrePos X a).Nonempty := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (prime_between (by norm_num : (0:ℝ)<1/8))
  refine ⟨max 2 T,fun X a ha he hscale hsmall => ?_⟩
  let t := Real.sqrt ((X:ℝ)/a)
  have ht : 2 ≤ t := (le_max_left _ _).trans hscale
  have hTt : T ≤ t := (le_max_right _ _).trans hscale
  have ha0 : (0:ℝ)<a := by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  have ht0 : 0<t := by linarith only [ht]
  have ht2 : t^2 = (X:ℝ)/a := Real.sq_sqrt (by positivity)
  obtain ⟨p,hp,hp0,hp1⟩ := hT t hTt
  obtain ⟨q,hq,hq0,hq1⟩ := hT ((1+1/8)*t) (by linarith only [hTt,ht])
  have hpq : p < q := by exact_mod_cast hp1.trans hq0
  have htp : ∀ d ∈ a.primeFactors, d < p := fun d hd => by exact_mod_cast (hsmall d hd).trans_lt hp0
  have htq : ∀ d ∈ (a*p).primeFactors, d < q := by
    intro d hd
    rw [Nat.primeFactors_mul ha.ne_zero hp.ne_zero,hp.primeFactors] at hd
    rcases mem_union.mp hd with hd | hd
    · exact (htp _ hd).trans hpq
    · exact (mem_singleton.mp hd) ▸ hpq
  have hprice : μ (a*(p*q)) = 1 := by
    rw [← mul_assoc,mu_append (Nat.mul_ne_zero ha.ne_zero hp.ne_zero) hq htq,
      mu_append ha.ne_zero hp htp,moebius_eq_neg_one_pow_omega ha,he.neg_one_pow]; norm_num
  have hl : (X:ℝ)/a < (p:ℝ)*q := by
    rw [← ht2,pow_two]
    exact mul_lt_mul_of_pos_left (by linarith only [hq0,ht0] : t < (q:ℝ)) ht0 |>.trans_le
      (mul_le_mul_of_nonneg_right hp0.le (Nat.cast_nonneg _))
  have hu : (p:ℝ)*q ≤ 2*((X:ℝ)/a) := by
    rw [← ht2]
    calc _ ≤ ((1+1/8)*t)*((1+1/8)*((1+1/8)*t)) :=
              mul_le_mul hp1.le hq1.le (Nat.cast_nonneg _) (by positivity)
         _ ≤ _ := by nlinarith only [sq_nonneg t]
  have hI : a*(p*q) ∈ Ioc X (2*X) := by
    apply mem_Ioc.mpr
    constructor
    · exact_mod_cast (by simpa only [mul_comm (a:ℝ)] using (div_lt_iff₀ ha0).1 hl :
        (X:ℝ)<a*((p:ℝ)*q))
    · rw [← mul_div_assoc,le_div_iff₀ ha0] at hu
      exact_mod_cast (by simpa only [mul_comm (a:ℝ)] using hu : (a:ℝ)*((p:ℝ)*q) ≤ 2*X)
  have hm : a*(p*q) ∈ posParity (Ioc X (2*X)) := mem_filter.mpr ⟨hI,hprice⟩
  exact ⟨a*(p*q),mem_filter.mpr ⟨hm,(ordered_cofactor_of_positive hm).trans
    (ordered_stems ha.ne_zero hp hq hpq htp).2⟩⟩

/-- Uniform escape of the largest-prime quotient scale over all negative vertices. -/
private theorem eventually_quotient_ge (R : ℝ) : ∀ᶠ X : ℕ in atTop,
    ∀ n ∈ negParity (Ioc X (2*X)), R ≤ (X:ℝ)/evenPrefixCofactor n := by
  let B := ⌈2*R⌉₊
  let P := ∏ p ∈ Nat.primesLE B,p
  filter_upwards [eventually_ge_atTop (max 1 P)] with X hX n hn
  let a := evenPrefixCofactor n
  obtain ⟨ha,_,r,hr,hnr,ht⟩ := mem_fibreNeg_structure ((le_max_left _ _).trans hX)
    (show n ∈ fibreNeg X a from mem_filter.mpr ⟨hn,rfl⟩)
  have hnI := mem_Ioc.mp (mem_filter.mp hn).1
  have hs := squarefree_iff_moebius_ne_zero.mpr (show μ n ≠ 0 by
    rw [(mem_filter.mp hn).2]; decide)
  have ha0 : (0:ℝ)<a := by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  change R ≤ (X:ℝ)/a
  by_contra! h
  have hrB : r ≤ B := by
    have hru : (r:ℝ) ≤ 2*((X:ℝ)/a) := by
      rw [← mul_div_assoc,le_div_iff₀ ha0,mul_comm]
      exact_mod_cast (hnr ▸ hnI.2 : a*r ≤ 2*X)
    exact_mod_cast (le_trans (by linarith only [h,hru] : (r:ℝ) ≤ 2*R) (Nat.le_ceil _))
  have hsub : n.primeFactors ⊆ Nat.primesLE B := by
    intro d hd
    refine Nat.mem_primesLE.mpr ⟨?_,Nat.prime_of_mem_primeFactors hd⟩
    rw [hnr,Nat.primeFactors_mul ha.ne_zero hr.ne_zero,hr.primeFactors] at hd
    rcases mem_union.mp hd with h | h
    · exact (ht _ h).le.trans hrB
    · exact (mem_singleton.mp h) ▸ hrB
  have hdiv := prod_dvd_prod_of_subset n.primeFactors (Nat.primesLE B) (fun p => p) hsub
  rw [Nat.prod_primeFactors_of_squarefree hs] at hdiv
  have hP : 0 < P := Finset.prod_pos (fun _ hp => (Nat.prime_of_mem_primesLE hp).pos)
  exact (not_lt_of_ge ((Nat.le_of_dvd hP hdiv).trans ((le_max_right _ _).trans hX))) hnI.1

/-- Every negative integer in an empty ordered fibre, at every sufficiently
large dyadic cutoff, belongs to one common restricted matching. -/
theorem eventually_every_empty_fibre_covered : ∀ᶠ X : ℕ in atTop,
    ∀ A : OppositeParityMatching OrderedExchange (Ioc X (2*X)),
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)), A.sources ⊆ M.sources ∧
      (negParity (Ioc X (2*X))).filter (fun n => fibrePos X (evenPrefixCofactor n) = ∅) ⊆
        M.targets := by
  obtain ⟨Z,hex⟩ := exists_cube_root_exchange
  obtain ⟨Y,hpos⟩ := eventually_positive_fibre
  let V := max 2 (max Y Z)
  have hV : 2 ≤ V := le_max_left _ _
  have hVY : Y ≤ V := (le_max_left _ _).trans (le_max_right _ _)
  have hVZ : Z ≤ V := (le_max_right _ _).trans (le_max_right _ _)
  have hV0 : 0 ≤ V := by linarith only [hV]
  have hV1 : 1 ≤ V := by linarith only [hV]
  filter_upwards [eventually_ge_atTop 1,eventually_quotient_ge (V^6)] with X hX hlarge
  intro A
  obtain ⟨M,hA,hM⟩ := hex X A
  refine ⟨M,hA,fun n hn => ?_⟩
  obtain ⟨hn,hbad⟩ := mem_filter.mp hn
  let a := evenPrefixCofactor n
  obtain ⟨ha,he,r,hr,hnr,ht⟩ := mem_fibreNeg_structure hX
    (show n ∈ fibreNeg X a from mem_filter.mpr ⟨hn,rfl⟩)
  have ha0 : (0:ℝ)<a := by exact_mod_cast Nat.pos_of_ne_zero ha.ne_zero
  let t := Real.sqrt ((X:ℝ)/a)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t^2 = (X:ℝ)/a := Real.sq_sqrt (by positivity)
  have hVt : V ≤ t := by
    apply (pow_le_pow_iff_left₀ hV0 ht0 (by decide : 2 ≠ 0)).mp
    rw [ht2]
    exact (pow_le_pow_right₀ hV1 (by decide : 2 ≤ 6)).trans (hlarge n hn)
  have hexq : ∃ d ∈ a.primeFactors, t < (d:ℝ) := by
    by_contra! h
    have hne := hpos X a ha he (hVY.trans hVt) h
    exact hne.ne_empty hbad
  obtain ⟨d,hd,hdt⟩ := hexq
  have hne : a.primeFactors.Nonempty := ⟨d,hd⟩
  let q := a.primeFactors.max' hne
  have hqa : q ∈ a.primeFactors := max'_mem _ _
  have hq := Nat.prime_of_mem_primeFactors hqa
  have hqr := ht q hqa
  let c := a/q
  have hcq : c*q = a := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hqa)
  have hsq : Squarefree (c*q) := hcq ▸ ha
  obtain ⟨hcop,hc,_⟩ := Nat.squarefree_mul_iff.mp hsq
  have hc0 : (0:ℝ)<c := by exact_mod_cast Nat.pos_of_ne_zero hc.ne_zero
  have hq0 : (0:ℝ)<q := by exact_mod_cast hq.pos
  have htop : ∀ e ∈ c.primeFactors, e < q := by
    have hnot : ¬ q ∣ c := (hq.coprime_iff_not_dvd).1 hcop.symm
    intro e he'
    have hdv := Nat.dvd_of_mem_primeFactors he'
    have hem : e ∈ a.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors he',hcq ▸ dvd_mul_of_dvd_left hdv q,ha.ne_zero⟩
    exact lt_of_le_of_ne (le_max' _ _ hem) (fun eq => hnot (eq ▸ hdv))
  have hcμ : μ c = -1 := by
    have h := mu_append hc.ne_zero hq htop
    rw [hcq,moebius_eq_neg_one_pow_omega ha,he.neg_one_pow] at h
    omega
  have hn' : n = c*(q*r) := by rw [← mul_assoc,hcq,hnr]
  have hnI := (mem_filter.mp hn).1
  have hcle : c ≤ 2*X :=
    (Nat.le_mul_of_pos_right c (Nat.mul_pos hq.pos hr.pos)).trans (hn' ▸ (mem_Ioc.mp hnI).2)
  let z := sixthScale X c
  have hz : 0 ≤ z := Real.rpow_nonneg (by positivity) _
  have h6 : z^6 = (X:ℝ)/c := sixthScale_pow X c
  have hzc : z^6 = ((X:ℝ)/a)*q := by
    have hmul : (c:ℝ)*q = a := by exact_mod_cast hcq
    rw [h6,← hmul]; field_simp
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq.pos
  have hVz : V ≤ z := by
    apply (pow_le_pow_iff_left₀ hV0 hz (by decide : 6 ≠ 0)).mp
    rw [hzc]
    exact (hlarge n hn).trans (le_mul_of_one_le_right (by positivity) hq1)
  have hqt : t < (q:ℝ) := hdt.trans_le (by exact_mod_cast le_max' _ d hd)
  have hq2 := pow_lt_pow_left₀ hqt ht0 (by decide : 2 ≠ 0)
  rw [ht2] at hq2
  have hq3 : z^6 < (q:ℝ)^3 := by
    rw [hzc]; nlinarith only [mul_lt_mul_of_pos_right hq2 hq0]
  have hsmall : z^2/2 < (q:ℝ) := by
    have hlt : z^2 < (q:ℝ) := by
      by_contra! h
      have hp := pow_le_pow_left₀ hq0.le h 3
      nlinarith only [hp,hq3]
    linarith only [hlt,sq_nonneg z]
  rw [hn']
  exact hM c (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hc.ne_zero,hcle⟩) hcμ (hVZ.trans hVz)
    q r hq hr hqr htop (hn' ▸ hnI) hsmall

/-- The entire old obstruction of order at least `X/log³ X` is transported,
with zero unmatched vertices from that set on every sufficiently large block. -/
theorem eventually_transported_empty_fibre_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
        C * X / Real.log X ^ 3 ≤
          ((M.targets.filter (fun n => fibrePos X (evenPrefixCofactor n) = ∅)).card : ℝ) ∧
        Disjoint M.unmatchedSet ((negParity (Ioc X (2*X))).filter
          (fun n => fibrePos X (evenPrefixCofactor n) = ∅)) := by
  obtain ⟨C,hC,X₀,hX₀⟩ := eventually_evenPrefixFibre_debt_ge
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_every_empty_fibre_covered,eventually_ge_atTop X₀] with X h hX
  obtain ⟨A,_⟩ := exists_matching_card_eq_sub_hallDeficiency OrderedExchange (Ioc X (2*X))
  obtain ⟨M,_,hM⟩ := h A
  refine ⟨M,(hX₀ X hX).1.trans (by
    exact_mod_cast card_le_card (fun n hn => mem_filter.mpr ⟨hM hn,(mem_filter.mp hn).2⟩)),?_⟩
  exact disjoint_left.mpr fun n hleft hright =>
    (mem_sdiff.mp hleft).2 (mem_union_right _ (hM hright))

end GaloisForLFunctions.RestrictedFactorizationCalculus
