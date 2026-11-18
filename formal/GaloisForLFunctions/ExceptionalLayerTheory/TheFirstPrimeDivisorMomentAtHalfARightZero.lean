import GaloisForLFunctions.RHTower.XiPrimeLogHigherValuationCriticalBoundary
import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyZeroCascade
import GaloisForLFunctions.RHTower.BurnolIntegrand
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# Prime divisors counted once at half the height of a zero

The logarithmic weight of distinct prime divisors has Euler series
ζ times the ordinary prime logarithm. A zeta factor cancels its poles
at right zeros. After removing prime squares and cubes, the remaining
sum is holomorphic right of one quarter. The two scaled residues have
the same sign before multiplication by ζ, and the halving theorem
prevents cancellation by that last factor at every right zero.
-/

noncomputable section

open Complex Set Filter Topology ArithmeticFunction
open _root_.RHTower

namespace GaloisForLFunctions.ExceptionalLayerTheory

private def fourthTerm (s : ℂ) (pk : Nat.Primes × ℕ) :=
  LSeries.term (fun n => (vonMangoldt n:ℂ)) s ((pk.1:ℕ)^(pk.2+4))

private def fourthWeight (u : ℝ) (pk : Nat.Primes × ℕ) :=
  Real.log (pk.1:ℝ)*((pk.1:ℝ)⁻¹)^((pk.2:ℝ)*u+4*u)

private theorem fourth_norm (s : ℂ) (pk : Nat.Primes × ℕ) :
    ‖fourthTerm s pk‖=fourthWeight s.re pk := by
  have hp : 0<((pk.1:ℕ):ℝ) := by exact_mod_cast pk.1.prop.pos
  have hp1 : 1<((pk.1:ℕ):ℝ) := by exact_mod_cast pk.1.prop.one_lt
  rw [fourthTerm,LSeries.norm_term_eq,if_neg (pow_pos pk.1.prop.pos _).ne',
    vonMangoldt_apply_pow (by omega),vonMangoldt_apply_prime pk.1.prop,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.log_pos hp1),fourthWeight,Nat.cast_pow,
    div_eq_mul_inv,← Real.rpow_neg (pow_nonneg hp.le _),← Real.rpow_natCast_mul hp.le,
    Real.inv_rpow hp.le,← Real.rpow_neg hp.le]
  congr 2
  push_cast
  ring

private theorem fourth_summable {s : ℂ} (hs : 1/4<s.re) : Summable (fourthTerm s) :=
  Summable.of_norm ((summable_primeLog_mul_inv_rpow_mul_add s.re (4*s.re)
    (by linarith only [hs]) (by linarith only [hs])).congr (fun pk => (fourth_norm s pk).symm))

private def fourthTail (s : ℂ) := ∑' pk, fourthTerm s pk

private theorem fourth_diff {s : ℂ} (hs : 1/4<s.re) : DifferentiableAt ℂ fourthTail s := by
  obtain ⟨u,hu,hus⟩ := exists_between hs
  let U := {z : ℂ | u<z.re}
  have hop : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hmaj : Summable (fourthWeight u) :=
    summable_primeLog_mul_inv_rpow_mul_add u (4*u) (by linarith only [hu]) (by linarith only [hu])
  have ht (pk : Nat.Primes × ℕ) : DifferentiableOn ℂ (fun z => fourthTerm z pk) U := by
    let n := (pk.1:ℕ)^(pk.2+4)
    have hn : n≠0 := (pow_pos pk.1.prop.pos _).ne'
    have hc : (n:ℂ)≠0 := by exact_mod_cast hn
    have he : (fun z => fourthTerm z pk)=fun z : ℂ => (vonMangoldt n:ℂ)/(n:ℂ)^z :=
      funext fun z => LSeries.term_of_ne_zero hn _ z
    rw [he]
    exact fun z _ => ((differentiableAt_const _).div
      (differentiableAt_id.const_cpow (Or.inl hc)) (Complex.cpow_ne_zero_iff.mpr (Or.inl hc))).differentiableWithinAt
  have hb (pk : Nat.Primes × ℕ) (z : ℂ) (hz : z∈U) : ‖fourthTerm z pk‖≤fourthWeight u pk :=
    (LSeries.norm_term_le_of_re_le_re _ (s := (u:ℂ)) (s' := z) hz.le _).trans_eq (fourth_norm (u:ℂ) pk)
  exact (Complex.differentiableOn_tsum_of_summable_norm hmaj ht hop hb).differentiableAt (hop.mem_nhds hus)

private theorem cube_term (s : ℂ) (p : Nat.Primes) :
    LSeries.term (fun n => (vonMangoldt n:ℂ)) s ((p:ℕ)^3) =
      (Real.log (p:ℝ):ℂ)/(p:ℂ)^(3*s) := by
  have harg := Complex.arg_ofReal_of_nonneg (show 0≤(p:ℝ) by positivity)
  rw [LSeries.term_of_ne_zero (pow_pos p.prop.pos _).ne',vonMangoldt_apply_pow (by norm_num),
    vonMangoldt_apply_prime p.prop,Nat.cast_pow]
  rw [← Complex.cpow_nat_mul' (x := (p:ℂ)) (n := 3) (by simpa [harg] using Real.pi_pos)
    (by simpa [harg] using Real.pi_pos.le)]
  norm_num

private theorem three_split {s : ℂ} (hs : 1/3<s.re) :
    xiPrimeLogHigherValuationThreePlus s=xiPrimeLogDirichlet (3*s)+fourthTail s := by
  let f (pk : Nat.Primes × ℕ) := LSeries.term (fun n => (vonMangoldt n:ℂ)) s ((pk.1:ℕ)^(pk.2+3))
  have hf : Summable f := summable_xiPrimeLogHigherValuationThreePlus_term hs
  have hg := fourth_summable (s := s) (by linarith only [hs])
  have hhead : Summable (fun p : Nat.Primes => f (p,0)) :=
    hf.comp_injective (i := fun p : Nat.Primes => (p,0)) fun _ _ e => congrArg Prod.fst e
  have he (p : Nat.Primes) : (∑' j : ℕ, f (p,j))=f (p,0)+∑' j : ℕ, fourthTerm s (p,j) := by
    have hrow := hf.comp_injective (i := fun j : ℕ => (p,j)) (fun _ _ e => congrArg Prod.snd e)
    exact hrow.tsum_eq_zero_add
  change (∑' pk, f pk)=_
  rw [hf.tsum_prod,tsum_congr he,hhead.tsum_add hg.prod,← hg.tsum_prod]
  congr 1
  rw [xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow (by simp; linarith only [hs])]
  exact tsum_congr fun p => cube_term s p

private def primeMomentTail (s : ℂ) := xiPrimeLogHigherValuation (2*s)+xiPrimeLogHigherValuation (3*s)-fourthTail s

private theorem primeMomentTail_diff {s : ℂ} (hs : 1/4<s.re) : DifferentiableAt ℂ primeMomentTail s := by
  have h2 : 1/2<(2*s).re := by simp; linarith only [hs]
  have h3 : 1/2<(3*s).re := by simp; linarith only [hs]
  exact (((differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re h2).comp s
    (differentiableAt_id.const_mul _)).add
    ((differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re h3).comp s
    (differentiableAt_id.const_mul _))).sub (fourth_diff hs)

/-- Continuation of the jump series of the first distinct-prime-divisor moment. -/
def firstPrimeDivisorMoment (s : ℂ) : ℂ :=
  -deriv riemannZeta s + riemannZeta s*(primeMomentTail s-infinitePrimeFlux (2*s)-infinitePrimeFlux (3*s))

/-- The continued moment is meromorphic on the full quarter half-plane,
including the real poles. -/
theorem firstPrimeDivisorMoment_meromorphicOn :
    MeromorphicOn firstPrimeDivisorMoment {z : ℂ | 1/4 < z.re} := by
  have hop : IsOpen {z : ℂ | 1/4 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ primeMomentTail {z : ℂ | 1/4 < z.re} :=
    fun _ hz => (primeMomentTail_diff hz).differentiableWithinAt
  intro z hz
  have hζ := meromorphicAt_riemannZeta_everywhere z
  have hf (a : ℂ) : MeromorphicAt (fun w : ℂ => infinitePrimeFlux (a*w)) z := by
    have h := meromorphicAt_riemannZeta_everywhere (a*z)
    have hF : MeromorphicAt infinitePrimeFlux (a*z) := (h.deriv.div h).neg
    exact hF.comp_analyticAt (analyticAt_const.mul analyticAt_id)
  exact hζ.deriv.neg.add (hζ.mul ((((hd.analyticOnNhd hop z hz).meromorphicAt.sub (hf 2)).sub (hf 3))))

/-- On the Euler half-plane each distinct prime contributes its logarithm,
and the extra zeta factor sums over its ordinary integer multiples. -/
theorem firstPrimeDivisorMoment_euler {s : ℂ} (hs : 1<s.re) :
    firstPrimeDivisorMoment s = riemannZeta s*xiPrimeLogDirichlet s := by
  have h2 : 1<(2*s).re := by simp; linarith only [hs]
  have h3 : 1<(3*s).re := by simp; linarith only [hs]
  have h := infinitePrimeFlux_eq_primeLog_add_higherValuation hs
  rw [xiPrimeLogHigherValuation_eq_two_add_threePlus (by linarith only [hs]),
    three_split (by linarith only [hs])] at h
  have hζ : riemannZeta s*infinitePrimeFlux s= -deriv riemannZeta s := by
    rw [infinitePrimeFlux,logDeriv_apply]
    field_simp [riemannZeta_ne_zero_of_one_le_re hs.le]
  rw [firstPrimeDivisorMoment,← hζ,primeMomentTail,
    infinitePrimeFlux_eq_primeLog_add_higherValuation h2,infinitePrimeFlux_eq_primeLog_add_higherValuation h3,h]
  ring

private theorem flux_diff {z : ℂ} (h1 : z≠1) (hz : riemannZeta z≠0) :
    DifferentiableAt ℂ infinitePrimeFlux z := by
  have h := HTGeometry.analyticAt_riemannZeta h1
  exact ((h.deriv.differentiableAt.div h.differentiableAt hz).neg)

private theorem residue_of_continuous {f : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z) :
    Tendsto (fun w => (w-z)*f w) (𝓝[≠] z) (𝓝 0) := by
  have hl : Tendsto (fun w : ℂ => w-z) (𝓝[≠] z) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' z 0 (sub_self z)).mono_left nhdsWithin_le_nhds
  have ht : Tendsto f (𝓝[≠] z) (𝓝 (f z)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [zero_mul] using hl.mul ht

private theorem flux_residue {z : ℂ} (h1 : z≠1) :
    ∃ m : ℕ, (riemannZeta z = 0 → 0 < m) ∧
      Tendsto (fun w => (w-z)*infinitePrimeFlux w) (𝓝[≠] z) (𝓝 (-(m:ℂ))) := by
  by_cases hz : riemannZeta z=0
  · obtain ⟨m,hm,h⟩ := neg_logDeriv_zeta_zero_residue hz
    exact ⟨m,fun _ => hm,by simpa only [infinitePrimeFlux,logDeriv_apply,neg_div] using h⟩
  · refine ⟨0,fun he => (hz he).elim,?_⟩
    simpa only [Nat.cast_zero,neg_zero] using residue_of_continuous (flux_diff h1 hz).continuousAt

private theorem scaled_ne_one {z : ℂ} (hi : z.im≠0) {a : ℝ} (ha : a≠0) : (a:ℂ)*z≠1 := by
  intro he
  exact (mul_ne_zero ha hi) (by simpa using congrArg Complex.im he)

private theorem scaled_flux_residue (a : ℝ) (ha : a≠0) {z : ℂ} (hi : z.im≠0) :
    ∃ m : ℕ, (riemannZeta ((a:ℂ)*z) = 0 → 0 < m) ∧
      Tendsto (fun w => (w-z)*infinitePrimeFlux ((a:ℂ)*w)) (𝓝[≠] z) (𝓝 (-(m:ℂ)/(a:ℂ))) := by
  obtain ⟨m,hm,ht⟩ := flux_residue (scaled_ne_one hi ha)
  have hc : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha
  have hmap : Tendsto (fun w : ℂ => (a:ℂ)*w) (𝓝[≠] z) (𝓝[≠] ((a:ℂ)*z)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_const.mul continuous_id).continuousAt.continuousWithinAt.tendsto,?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact fun h => hw (mul_left_cancel₀ hc h)
  refine ⟨m,hm,?_⟩
  apply ((ht.comp hmap).div_const (a:ℂ)).congr
  intro w
  dsimp only [Function.comp_apply]
  field_simp [hc]

/-- A zero at twice the argument and a zero at three times the argument
contribute nonnegative multiplicities to the same residue factor. -/
theorem firstPrimeDivisorMoment_residue {z : ℂ} (hs : 1/4<z.re) (hi : z.im≠0) :
    ∃ m n : ℕ, (riemannZeta (2*z) = 0 → 0 < m) ∧ (riemannZeta (3*z) = 0 → 0 < n) ∧
      Tendsto (fun w => (w-z)*firstPrimeDivisorMoment w) (𝓝[≠] z)
        (𝓝 (riemannZeta z*((m:ℂ)/2+(n:ℂ)/3))) := by
  obtain ⟨m,hm,h₂⟩ := scaled_flux_residue 2 (by norm_num) hi
  obtain ⟨n,hn,h₃⟩ := scaled_flux_residue 3 (by norm_num) hi
  simp only [Complex.ofReal_ofNat] at hm hn h₂ h₃
  have hzne : z≠1 := fun e => hi (by rw [e,Complex.one_im])
  have hζ := HTGeometry.analyticAt_riemannZeta hzne
  let g (w : ℂ) := -deriv riemannZeta w+riemannZeta w*primeMomentTail w
  have hg : ContinuousAt g z := hζ.deriv.continuousAt.neg.add (hζ.continuousAt.mul (primeMomentTail_diff hs).continuousAt)
  have hζt : Tendsto riemannZeta (𝓝[≠] z) (𝓝 (riemannZeta z)) :=
    hζ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := ((residue_of_continuous hg).sub (hζt.mul h₂)).sub (hζt.mul h₃)
  rw [show (0:ℂ)-riemannZeta z*(-(m:ℂ)/2)-riemannZeta z*(-(n:ℂ)/3)=
    riemannZeta z*((m:ℂ)/2+(n:ℂ)/3) by ring] at ht
  refine ⟨m,n,hm,hn,ht.congr fun w => ?_⟩
  change (w-z)*g w-riemannZeta w*((w-z)*infinitePrimeFlux (2*w))-
    riemannZeta w*((w-z)*infinitePrimeFlux (3*w))=(w-z)*firstPrimeDivisorMoment w
  dsimp only [g,firstPrimeDivisorMoment]; ring

/-- Vanishing punctured residues between one quarter and one half
forces every right zero to propagate to half its ordinate. -/
theorem riemannHypothesis_of_firstPrimeDivisorMoment_zero_residues
    (h : ∀ z : ℂ, 1/4 < z.re → z.re < 1/2 → z.im ≠ 0 →
      Tendsto (fun w => (w-z)*firstPrimeDivisorMoment w) (𝓝[≠] z) (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
  intro ρ hρ h1
  refine SquarefreeDiscrepancy.riemannZeta_ne_zero_of_halving (α := 1/4) (by norm_num) ?_ (by linarith only [hρ]) (by linarith only [h1])
  intro v hv hh h1'
  have him : v.im≠0 := by
    intro e
    have he : v=(v.re:ℂ) := Complex.ext rfl (by simpa using e)
    apply riemannZeta_real_strip_ne_zero (by linarith only [hh]) h1'
    rwa [← he]
  let z := v/2
  have he : 2*z=v := by dsimp only [z]; ring
  have hr : z.re=v.re/2 := by simp [z,Complex.div_ofNat_re]
  have hi : z.im≠0 := by simpa [z,Complex.div_ofNat_im] using him
  have hs : 1/4<z.re := by rw [hr]; linarith only [hh]
  obtain ⟨m,n,hm,_,ht⟩ := firstPrimeDivisorMoment_residue hs hi
  have hp := hm (by rwa [he])
  have h₀ := h z hs (by rw [hr]; linarith only [h1']) hi
  have hn : (m:ℂ)/2+(n:ℂ)/3≠0 := by
    intro e
    have hpR : 0 < (m:ℝ) := by exact_mod_cast hp
    have he' := congrArg Complex.re e
    norm_num [Complex.div_re] at he'
    linarith only [he',hpR,Nat.cast_nonneg (α := ℝ) n]
  exact (mul_eq_zero.mp (tendsto_nhds_unique ht h₀)).resolve_right hn

/-- The first ordinary-prime-divisor moment is holomorphic at every
nonreal point right of one quarter exactly under RH. -/
theorem riemannHypothesis_iff_firstPrimeDivisorMoment_quarter :
    RiemannHypothesis ↔ ∀ z : ℂ, 1/4<z.re → z.im≠0 → DifferentiableAt ℂ firstPrimeDivisorMoment z := by
  constructor
  · intro h z hz hi
    have hf {v : ℂ} (hv : 1/2<v.re) : riemannZeta v≠0 := by
      rcases lt_or_ge v.re 1 with hv' | hv'
      · exact riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mp h v hv hv'
      · exact riemannZeta_ne_zero_of_one_le_re hv'
    have hm (a : ℝ) (ha : a≠0) (hs : 1/2<((a:ℂ)*z).re) :
        DifferentiableAt ℂ (fun w : ℂ => infinitePrimeFlux ((a:ℂ)*w)) z :=
      (flux_diff (scaled_ne_one hi ha) (hf hs)).comp z (differentiableAt_id.const_mul _)
    have h2 := hm 2 (by norm_num) (by simp; linarith only [hz])
    have h3 := hm 3 (by norm_num) (by simp; linarith only [hz])
    have ha := HTGeometry.analyticAt_riemannZeta (show z≠1 from fun e => hi (by rw [e,Complex.one_im]))
    exact ha.deriv.differentiableAt.neg.add (ha.differentiableAt.mul (((primeMomentTail_diff hz).sub h2).sub h3))
  · intro h
    exact riemannHypothesis_of_firstPrimeDivisorMoment_zero_residues
      fun z hz _ hi => residue_of_continuous (h z hz hi).continuousAt

#print axioms firstPrimeDivisorMoment_meromorphicOn
#print axioms riemannHypothesis_of_firstPrimeDivisorMoment_zero_residues
#print axioms firstPrimeDivisorMoment_euler
#print axioms firstPrimeDivisorMoment_residue
#print axioms riemannHypothesis_iff_firstPrimeDivisorMoment_quarter

end GaloisForLFunctions.ExceptionalLayerTheory
