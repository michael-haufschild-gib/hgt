import GaloisForLFunctions.ExceptionalLayerTheory.ThePrimeSquareSingularityOfThePositiveFactorialSeries
import GaloisForLFunctions.ExceptionalLayerTheory.ASquareRootBoundFromThePowerfulDivisors
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsContinuePastTheLineReOne
import GaloisForLFunctions.RHTower.Sieve.InghamRightEdgeMeanSquare
import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic

/-!
# Optimality of the square-root exponent

A smaller error in the count continues its centered Dirichlet series
through one half. Division by zeta then gives a meromorphic germ for
the factorial correction. The prime squares exclude this germ.
-/

noncomputable section

open Filter Topology Set Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius LSeries.notation
open _root_.RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev corr := reciprocalFactorial*(μ:ArithmeticFunction ℝ)

private theorem corr_summable {s : ℂ} (hs : 1/2<s.re) :
    LSeriesSummable (complexCoeff corr) s := by
  apply Summable.of_norm
  apply (reciprocalFactorial_correction_summable hs).congr
  intro n
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [if_neg hn,complexCoeff,Complex.norm_real,Real.norm_eq_abs,
      Real.rpow_neg (Nat.cast_nonneg n),div_eq_mul_inv]

private theorem corr_real (x : ℝ) :
    LSeries (complexCoeff corr) (x:ℂ)=(reciprocalFactorialEulerCorrection x:ℂ) := by
  rw [reciprocalFactorialEulerCorrection,Complex.ofReal_tsum,LSeries]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn,Complex.ofReal_mul,Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast,Complex.ofReal_neg,Complex.cpow_neg,div_eq_mul_inv]
    rfl

private theorem reciprocalFactorial_series {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (complexCoeff reciprocalFactorial) s ∧
    LSeries (complexCoeff reciprocalFactorial) s=LSeries (complexCoeff corr) s*riemannZeta s := by
  have hf : corr*(ArithmeticFunction.zeta : ArithmeticFunction ℝ)=reciprocalFactorial := by
    rw [show corr=reciprocalFactorial*(μ:ArithmeticFunction ℝ) from rfl,mul_assoc,coe_moebius_mul_coe_zeta,mul_one]
  have he : complexCoeff reciprocalFactorial=complexCoeff corr ⍟ complexCoeff (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
    exact (congrArg complexCoeff hf).symm.trans (complexCoeff_mul _ _)
  have h := corr_summable (s := s) (by linarith only [hs])
  have hz := LSeriesSummable_complexCoeff_zeta hs
  rw [he,LSeries_convolution' h hz,LSeries_complexCoeff_zeta_eq_riemannZeta hs]
  exact ⟨h.convolution hz,rfl⟩

/-- Every exponent strictly below one half fails for the centered positive
factorial count, including at arbitrarily large integer cutoffs. -/
theorem reciprocalFactorial_sum_has_no_smaller_power {b : ℝ} (hb : 0≤b) (hb' : b<1/2) :
    ¬∃ C : ℝ, ∀ N : ℕ, 1≤N →
      |(∑ n ∈ Finset.Icc 1 N, reciprocalFactorial n)-(N:ℝ)*reciprocalFactorialDensity|≤C*(N:ℝ)^b := by
  rintro ⟨C,hC⟩
  let c := reciprocalFactorialDensity
  let Z : ℕ → ℂ := complexCoeff (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  let f : ℕ → ℂ := complexCoeff reciprocalFactorial-(c:ℂ) • Z
  let A := HeckeLFunctions.growthCont f b
  let H := LSeries (complexCoeff corr)
  let D := fun s : ℂ => (c:ℂ)+A s/riemannZeta s
  have h0 : f 0=0 := by simp [f,Z,complexCoeff]
  have hC0 : 0≤C := by
    simpa only [Nat.cast_one,Real.one_rpow,mul_one] using
      (abs_nonneg _).trans (hC 1 le_rfl)
  have hpre (x : ℝ) (hx : 1≤x) : ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n‖≤C*x^b := by
    let N := ⌊x⌋₊
    have he (n : ℕ) (hn : n∈Finset.Icc 1 N) : f n=((reciprocalFactorial n-c:ℝ):ℂ) := by
      have hp : n≠0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
      simp [f,Z,complexCoeff,natCoe_apply,zeta_apply_ne hp]
    rw [sum_congr rfl he,← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,sum_sub_distrib,
      sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
    exact (hC N ((Nat.one_le_floor_iff x).mpr hx)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (zero_le_one.trans hx)) hb) hC0)
  have hopen (t : ℝ) : IsOpen {s : ℂ | t<s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hA : AnalyticOnNhd ℂ A {s : ℂ | b<s.re} :=
    (HeckeLFunctions.differentiableOn_growthCont h0 hb hpre).analyticOnNhd (hopen _)
  have hH : AnalyticOnNhd ℂ H {s : ℂ | 1/2<s.re} := by
    apply DifferentiableOn.analyticOnNhd _ (hopen _)
    intro s hs
    obtain ⟨u,hu,hu'⟩ := exists_between (show 1/2<s.re from hs)
    have ht := (corr_summable (s := (u:ℂ)) hu).abscissaOfAbsConv_le
    exact (LSeries_hasDerivAt (ht.trans_lt (by exact_mod_cast hu'))).differentiableAt.differentiableWithinAt
  have hD : MeromorphicOn D {s : ℂ | b<s.re} := fun z hz =>
    (MeromorphicAt.const _ _).add ((hA z hz).meromorphicAt.div (HTGeometry.meromorphicOn_riemannZeta z (Set.mem_univ z)))
  have hEq {s : ℂ} (hs : 1<s.re) : D s=H s := by
    have hv := reciprocalFactorial_series hs
    have hz : LSeriesSummable Z s := LSeriesSummable_complexCoeff_zeta hs
    have hf : LSeriesSummable f s := hv.1.sub (hz.smul (c:ℂ))
    have he := HeckeLFunctions.growthCont_eq_LSeries h0 hb hpre (s := s) (by linarith only [hs,hb']) hf
    change (c:ℂ)+A s/riemannZeta s=_
    rw [show A s=LSeries f s from he,f,LSeries_sub hv.1 (hz.smul (c:ℂ)),LSeries_smul,
      show LSeries Z s=riemannZeta s from LSeries_complexCoeff_zeta_eq_riemannZeta hs,hv.2]
    dsimp only [H]
    field_simp [riemannZeta_ne_zero_of_one_le_re hs.le] <;> ring
  let U := {s : ℂ | 1/2<s.re}
  have hW : MeromorphicOn (D-H) U := fun z hz => (hD z (hb'.trans hz)).sub (hH z hz).meromorphicAt
  have h₂ : (2:ℂ)∈U := by change (1:ℝ)/2<(2:ℂ).re; norm_num
  have h₂top : meromorphicOrderAt (D-H) (2:ℂ)=⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have he := (hopen 1).mem_nhds (show (2:ℂ)∈{s:ℂ | 1<s.re} by change (1:ℝ)<(2:ℂ).re; norm_num)
    filter_upwards [nhdsWithin_le_nhds he] with s hs
    exact sub_eq_zero.mpr (hEq hs)
  have hval {x : ℝ} (hx : 1/2<x) (hx1 : x<1) : D x=H x := by
    have htop : meromorphicOrderAt (D-H) (x:ℂ)=⊤ := by
      by_contra hn
      exact (hW.meromorphicOrderAt_ne_top_of_isPreconnected (convex_halfSpace_re_gt _).isPreconnected
        (show (x:ℂ)∈U from hx) h₂ hn) h₂top
    have hz := _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo (by linarith only [hx]) hx1
    have hne : (x:ℂ)≠1 := by exact_mod_cast hx1.ne
    have hcont : ContinuousAt D (x:ℂ) :=
      continuousAt_const.add ((hA _ (hb'.trans hx)).continuousAt.div (differentiableAt_riemannZeta hne).continuousAt hz)
    have hlim : Tendsto (D-H) (𝓝[≠] (x:ℂ)) (𝓝 0) :=
      tendsto_const_nhds.congr' (meromorphicOrderAt_eq_top_iff.mp htop).symm
    exact sub_eq_zero.mp (tendsto_nhds_unique
      ((hcont.sub (hH _ hx).continuousAt).continuousWithinAt.tendsto) hlim)
  let q (w : ℂ) := w/2
  have hq : AnalyticAt ℂ q 1 := analyticAt_id.div_const _
  have hF : MeromorphicAt (D ∘ q) 1 := (hD (q 1) (by simpa [q] using hb')).comp_analyticAt hq
  apply reciprocalFactorialEulerCorrection_no_right_germ _ hF
  have hsmall : Set.Iio (2:ℝ)∈𝓝[>] 1 := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin,hsmall] with w hw hw'
  have hx : 1/2<w/2 := by linarith only [show (1:ℝ)<w from hw]
  have hx' : w/2<1 := by linarith only [show w<(2:ℝ) from hw']
  simpa only [Function.comp_apply,q,Complex.ofReal_div,Complex.ofReal_ofNat] using
    (hval hx hx').trans (corr_real (w/2))

/-- A square-root bounded sequence cannot retain a positive excess above a
smaller power if that excess doubles whenever the argument doubles. -/
private theorem no_positive_doubling {g : ℕ → ℝ} {B : ℝ}
    (hu : ∀ n : ℕ, 1≤n → g n≤B*Real.sqrt n)
    (hd : ∀ n : ℕ, 1≤n → 2*g n≤g (2*n)) {n : ℕ} (hn : 1≤n) : g n≤0 := by
  by_contra! hp
  have hfour (m : ℕ) (hm : 1 ≤ m) : 4*g m≤g (4*m) := by
    have h₁ := hd m hm
    have h₂ := hd (2*m) (by omega)
    rw [show 2*(2*m)=4*m by ring] at h₂
    linarith only [h₁,h₂]
  have hiter (k : ℕ) : (4:ℝ)^k*g n≤g (4^k*n) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',pow_succ',mul_assoc,mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih (by norm_num)).trans (hfour _ (Nat.mul_pos (by positivity) hn))
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (B*Real.sqrt n/g n) (by norm_num : (1:ℝ)<2)
  have he : (4^k:ℝ)=(2^k:ℝ)^2 := by rw [← pow_mul, mul_comm k, pow_mul]; norm_num
  have hroot : Real.sqrt ((4^k*n:ℕ):ℝ)=(2:ℝ)^k*Real.sqrt n := by
    push_cast
    rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
  have hi := (hiter k).trans (hu _ (Nat.mul_pos (by positivity) hn))
  rw [hroot,he] at hi
  have hc : (2:ℝ)^k*g n≤B*Real.sqrt n := by
    refine le_of_mul_le_mul_left ?_ (by positivity : (0:ℝ)<2^k)
    calc
      _ = (2^k:ℝ)^2*g n := by ring
      _ ≤ _ := hi
      _ = _ := by ring
  exact ((div_lt_iff₀ hp).mp hk).not_ge hc

/-- Even cutoffs alone force the exact lower power exponent of the
uncentered ordinary-prime sum of the dyadic positive profile. -/
theorem dyadicPositiveFactorialProfile_prime_has_no_smaller_power {b : ℝ} (hb : 0≤b) (hb' : b<1/2) :
    ¬∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 1≤n →
      |∑ p ∈ Nat.primesLE (2*n), dyadicPositiveFactorialProfile (2*n/p)| ≤ C*(n:ℝ)^b := by
  rintro ⟨C,hC,h⟩
  let c := reciprocalFactorialDensity
  let A (n : ℕ) := (∑ k ∈ Finset.Icc 1 n, reciprocalFactorial k)-1-(n:ℝ)*c
  let t := (2:ℝ)^b
  have ht : t<2 := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
      (by linarith only [hb'] : b<1)
  let K := C/(2-t)
  have hK : 0≤K := div_nonneg hC (sub_pos.mpr ht).le
  have hK' : K*(2-t)=C := div_mul_cancel₀ _ (sub_pos.mpr ht).ne'
  let g (n : ℕ) := |A n|-K*(n:ℝ)^b
  have hroot (n : ℕ) (hn : 1≤n) : 1≤Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hn : (1:ℝ)≤n)
  have hu (n : ℕ) (hn : 1≤n) : g n≤13*Real.sqrt n := by
    have hbnd := reciprocalFactorial_sum_sqrt_error n
    have he : A n=((∑ k ∈ Finset.Icc 1 n, reciprocalFactorial k)-(n:ℝ)*c)-1 := by dsimp only [A]; ring
    apply (sub_le_self _ (mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg n) _))).trans
    rw [he]; apply (abs_sub _ _).trans
    rw [abs_one]
    linarith only [hbnd,hroot n hn]
  have hd (n : ℕ) (hn : 1≤n) : 2*g n≤g (2*n) := by
    have hinc := h n hn
    rw [dyadicPositiveFactorialProfile_prime_sum_even hn] at hinc
    have he : 2*A n=A (2*n)-(((∑ k ∈ Finset.Icc 1 (2*n), reciprocalFactorial k)-1)-
        2*((∑ k ∈ Finset.Icc 1 n, reciprocalFactorial k)-1)) := by dsimp only [A]; push_cast; ring
    have htri := (abs_sub (A (2*n)) _).trans (add_le_add (le_refl |A (2*n)|) hinc)
    rw [← he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at htri
    dsimp only [g]
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)]
    change _≤|A (2*n)|-K*(t*(n:ℝ)^b)
    linarith only [htri,show K*(2-t)*(n:ℝ)^b=C*(n:ℝ)^b by rw [hK']]
  apply reciprocalFactorial_sum_has_no_smaller_power hb hb'
  refine ⟨K+1,fun n hn => ?_⟩
  have ha := no_positive_doubling hu hd hn
  change |A n|-K*(n:ℝ)^b≤0 at ha
  have he : (∑ k ∈ Finset.Icc 1 n, reciprocalFactorial k)-(n:ℝ)*c=A n+1 := by dsimp only [A]; ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hnp : 1≤(n:ℝ)^b := Real.one_le_rpow (by exact_mod_cast hn) hb
  rw [abs_one]
  linarith only [ha,hnp]

end GaloisForLFunctions.ExceptionalLayerTheory
