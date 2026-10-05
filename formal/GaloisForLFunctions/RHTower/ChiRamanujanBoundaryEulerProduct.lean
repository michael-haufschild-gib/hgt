import GaloisForLFunctions.RHTower.DeningerAbelianLimit
import GaloisForLFunctions.HTGeometry.DirichletSeriesBoundedPartialSums
import GaloisForLFunctions.RHTower.ChiRamanujanMixedEulerTilt
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Actual boundary Euler products and logarithmic displacements

The original prime-ordered Euler product on `1 + i*tau` converges to inverse
zeta for every nonzero real frequency. Convergent actual prime partial sums
enter the complex Abel probability average; the entire nonlinear logarithm
remainder is dominated up to the boundary. The right-half-plane Euler formula
then identifies the limit without assuming boundary-product convergence.

Combining this identification with the actual moving Euler ratio gives every
fixed complex displacement at scale `1/log N`, at the original prime cutoff.
The complete mixed labelled source, uniform parameter control, and physical
signed axes cancellation remain separate obligations.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace RHTower.BAGTrace
open GaloisForLFunctions.HTGeometry.BoundedPartialSums

private theorem complex_abel_summable {b : ℕ → ℂ} {C : ℝ}
    (hC : ∀ n, ‖b n‖ ≤ C) {s : ℝ} (hs : 0<s) :
    Summable (fun n => b n*(deningerAbelWeight s n : ℂ)) := by
  apply Summable.of_norm_bounded ((deningerAbelWeight_hasSum_one hs).summable.mul_left C)
  intro n
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (deningerAbelWeight_nonneg hs.le n)]
  exact mul_le_mul_of_nonneg_right (hC n) (deningerAbelWeight_nonneg hs.le n)

private theorem complex_abel_limit {b : ℕ → ℂ} {A : ℂ} (hb : Tendsto b atTop (𝓝 A)) :
    Tendsto (fun s : ℝ => ∑' n, b n*(deningerAbelWeight s n : ℂ)) (𝓝[>] 0) (𝓝 A) := by
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto _ hb).exists_norm_le
  have hbd (n : ℕ) : ‖b n‖≤C := hC _ ⟨n,rfl⟩
  have hr := deningerAbelian_tendsto (Complex.continuous_re.tendsto A |>.comp hb)
  have hi := deningerAbelian_tendsto (Complex.continuous_im.tendsto A |>.comp hb)
  have h := ((Complex.continuous_ofReal.tendsto _).comp hr).add
    (((Complex.continuous_ofReal.tendsto _).comp hi).mul_const Complex.I)
  rw [Complex.re_add_im] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsum := complex_abel_summable hbd hs
  apply Complex.ext <;>
    simp [Complex.re_tsum hsum,Complex.im_tsum hsum]

private theorem powNeg_ofReal (s : ℝ) (n : ℕ) :
    powNeg (s : ℂ) n=((n : ℝ)^(-s) : ℝ) := by
  rw [powNeg]
  simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)).symm

private theorem continuation_abel_eq {a : ℕ → ℂ} {M : ℝ}
    (hM : ∀ n, ‖partialSum a n‖ ≤ M) (ha : a 0=0) {s : ℝ} (hs : 0<s) :
    continuation a (s : ℂ)=∑' n, partialSum a (n+2)*(deningerAbelWeight s n : ℂ) := by
  have hsc : 0<(s : ℂ).re := hs
  have hsum := summable_incr_mul hM hsc
  rw [continuation,← hsum.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one,partialSum,Finset.sum_range_one,ha,mul_zero,zero_add]
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  rw [incr,powNeg_ofReal,powNeg_ofReal,deningerAbelWeight]
  push_cast
  ring

private theorem continuation_boundary {a : ℕ → ℂ} {A : ℂ}
    (ha : a 0=0) (hA : Tendsto (partialSum a) atTop (𝓝 A)) :
    Tendsto (fun s : ℝ => continuation a (s : ℂ)) (𝓝[>] 0) (𝓝 A) := by
  obtain ⟨M,hM⟩ := (Metric.isBounded_range_of_tendsto _ hA).exists_norm_le
  have hbd (n : ℕ) : ‖partialSum a n‖ ≤ M := hM _ ⟨n,rfl⟩
  have h := complex_abel_limit (hA.comp (tendsto_add_atTop_nat 2))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (continuation_abel_eq hbd ha hs).symm

private def primeCoeff (tau : ℝ) (n : ℕ) : ℂ :=
  if n.Prime then criticalPrimeBoundaryCoeff tau n else 0

private theorem primeCoeff_zero (tau : ℝ) : primeCoeff tau 0=0 := by simp [primeCoeff,Nat.not_prime_zero]

private theorem prime_partial_eq (tau : ℝ) (N : ℕ) :
    partialSum (primeCoeff tau) (N+1)=criticalPrimeBoundarySum tau N := by
  simp [partialSum,primeCoeff,criticalPrimeBoundarySum,Nat.primesLE_eq_filter_range,Finset.sum_filter]

private theorem prime_partial_limit (tau : ℝˣ) :
    ∃ A : ℂ, Tendsto (partialSum (primeCoeff tau)) atTop (𝓝 A) := by
  obtain ⟨A,hA⟩ := criticalPrimeBoundarySum_tendsto tau
  have h := hA.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_sub_atTop_nat 1))
  refine ⟨A,h.congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [Function.comp_def]
  rw [← prime_partial_eq, Nat.sub_add_cancel hN]

private def boundaryNome (tau s : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ)^(-1-(tau : ℂ)*Complex.I-(s : ℂ))

private theorem nome_zero (tau : ℝ) (n : ℕ) :
    boundaryNome tau 0 n=criticalPrimeBoundaryCoeff tau n := by
  simp [boundaryNome,criticalPrimeBoundaryCoeff]

private theorem nome_mul (tau s : ℝ) {n : ℕ} (hn : 0<n) :
    boundaryNome tau s n=criticalPrimeBoundaryCoeff tau n*powNeg (s : ℂ) n := by
  rw [boundaryNome,criticalPrimeBoundaryCoeff,powNeg,← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne')]
  congr 1

private theorem nome_bound (tau : ℝ) {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : n.Prime) :
    ‖boundaryNome tau s n‖≤(n : ℝ)⁻¹ := by
  rw [boundaryNome,Complex.norm_natCast_cpow_of_pos hn.pos]
  have he : (-1-(tau : ℂ)*Complex.I-(s : ℂ)).re=(-1-s : ℝ) := by simp
  rw [he,← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.one_lt.le) (by linarith)

private theorem nome_half (tau : ℝ) {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : n.Prime) :
    ‖boundaryNome tau s n‖≤1/2 := by
  apply (nome_bound tau hs hn).trans
  have hn2 : (2 : ℝ)≤n := by exact_mod_cast hn.two_le
  simpa using (inv_anti₀ (by norm_num : (0 : ℝ)<2) hn2)

private theorem nome_complement_ne (tau : ℝ) {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : n.Prime) :
    1-boundaryNome tau s n≠0 := by
  have h := nome_half tau hs hn
  intro he
  have he' : boundaryNome tau s n=1 := (sub_eq_zero.mp he).symm
  rw [he',norm_one] at h
  linarith

private theorem log_error_bound {q : ℂ} (hq : ‖q‖≤1/2) :
    ‖Complex.log (1-q)+q‖≤2*‖q‖^2 := by
  have h := Complex.norm_log_one_add_sub_self_le (z := -q) (by rw [norm_neg]; linarith)
  have hden : 0<1-‖q‖ := by linarith
  have hi : (1-‖q‖)⁻¹≤2 := by
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 1/2) (show (1/2 : ℝ) ≤ 1-‖q‖ by linarith)
    simpa using hi
  simp only [norm_neg,sub_neg_eq_add,show (1 : ℂ)+ -q=1-q by ring] at h
  nlinarith [sq_nonneg ‖q‖,mul_le_mul_of_nonneg_left hi (sq_nonneg ‖q‖)]

private def boundaryRemainder (tau s : ℝ) (n : ℕ) : ℂ :=
  if n.Prime then Complex.log (1-boundaryNome tau s n)+boundaryNome tau s n else 0

private theorem remainder_bound (tau : ℝ) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    ‖boundaryRemainder tau s n‖≤2*(n : ℝ)^(-2 : ℝ) := by
  by_cases hn : n.Prime
  · rw [boundaryRemainder,if_pos hn]
    apply (log_error_bound (nome_half tau hs hn)).trans
    have hp := pow_le_pow_left₀ (norm_nonneg _) (nome_bound tau hs hn) 2
    have he : ((n : ℝ)⁻¹)^2=(n : ℝ)^(-2 : ℝ) := by
      rw [Real.rpow_neg (by positivity),Real.rpow_two,inv_pow]
    rw [he] at hp
    linarith
  · simp only [boundaryRemainder,if_neg hn,norm_zero]
    positivity

private theorem remainder_majorant_summable : Summable (fun n : ℕ => 2*(n : ℝ)^(-2 : ℝ)) :=
  (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).mul_left 2

private theorem remainder_summable (tau : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Summable (boundaryRemainder tau s) :=
  Summable.of_norm_bounded remainder_majorant_summable (remainder_bound tau hs)

private theorem remainder_tendsto (tau : ℝ) (n : ℕ) :
    Tendsto (fun s : ℝ => boundaryRemainder tau s n) (𝓝[>] 0) (𝓝 (boundaryRemainder tau 0 n)) := by
  by_cases hn : n.Prime
  · have hc : Continuous (fun s : ℝ => boundaryNome tau s n) := by
      unfold boundaryNome
      fun_prop (disch := exact Or.inl (Nat.cast_ne_zero.mpr hn.ne_zero))
    have h : Tendsto (fun s : ℝ => boundaryNome tau s n) (𝓝[>] 0)
        (𝓝 (boundaryNome tau 0 n)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hq : ‖-boundaryNome tau 0 n‖<1 := by
      rw [norm_neg]
      exact (nome_half tau (s := 0) le_rfl hn).trans_lt (by norm_num)
    have hl := (tendsto_const_nhds.sub h).clog
      (by simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hq)
    simpa only [boundaryRemainder,if_pos hn] using hl.add h
  · simp only [boundaryRemainder,if_neg hn]
    exact tendsto_const_nhds

private theorem remainder_sum_boundary (tau : ℝ) :
    Tendsto (fun s : ℝ => ∑' n,boundaryRemainder tau s n) (𝓝[>] 0)
      (𝓝 (∑' n,boundaryRemainder tau 0 n)) := by
  apply tendsto_tsum_of_dominated_convergence remainder_majorant_summable (remainder_tendsto tau)
  filter_upwards [self_mem_nhdsWithin] with s hs n
  exact remainder_bound tau hs.le n

private theorem remainder_partial_limit (tau : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N+1),boundaryRemainder tau s n)
      atTop (𝓝 (∑' n,boundaryRemainder tau s n)) :=
  ((remainder_summable tau hs).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

private def boundaryEuler (tau s : ℝ) (N : ℕ) : ℂ :=
  ∏ p ∈ Nat.primesLE N, (1-boundaryNome tau s p)

private theorem product_exp_eq (tau : ℝ) {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    boundaryEuler tau s N=Complex.exp
      (-(∑ n ∈ Finset.range (N+1),primeCoeff tau n*powNeg (s : ℂ) n)+
        ∑ n ∈ Finset.range (N+1),boundaryRemainder tau s n) := by
  rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib,Complex.exp_sum,
    boundaryEuler,Nat.primesLE_eq_filter_range,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro n _
  by_cases hn : n.Prime
  · simp only [primeCoeff,boundaryRemainder,if_pos hn]
    rw [← nome_mul tau s hn.pos]
    have he : -boundaryNome tau s n+(Complex.log (1-boundaryNome tau s n)+boundaryNome tau s n)=
        Complex.log (1-boundaryNome tau s n) := by ring
    rw [he,Complex.exp_log (nome_complement_ne tau hs hn)]
  · simp [primeCoeff,boundaryRemainder,hn]

private theorem product_right_limit (tau : ℝ) {M : ℝ}
    (hM : ∀ n, ‖partialSum (primeCoeff tau) n‖≤M) {s : ℝ} (hs : 0<s) :
    Tendsto (boundaryEuler tau s) atTop
      (𝓝 (Complex.exp (-continuation (primeCoeff tau) (s : ℂ)+∑' n,boundaryRemainder tau s n))) := by
  have hlin := (tendsto_sum_mul_powNeg hM (show 0<(s : ℂ).re from hs)).comp (tendsto_add_atTop_nat 1)
  have h := hlin.neg.add (remainder_partial_limit tau hs.le)
  apply ((Complex.continuous_exp.tendsto _).comp h).congr
  intro N
  exact (product_exp_eq tau hs.le N).symm

private theorem product_boundary_limit {tau : ℝ} {A : ℂ}
    (hA : Tendsto (partialSum (primeCoeff tau)) atTop (𝓝 A)) :
    Tendsto (boundaryEuler tau 0) atTop
      (𝓝 (Complex.exp (-A+∑' n,boundaryRemainder tau 0 n))) := by
  have h := (hA.comp (tendsto_add_atTop_nat 1)).neg.add (remainder_partial_limit tau (s := 0) le_rfl)
  apply ((Complex.continuous_exp.tendsto _).comp h).congr
  intro N
  rw [product_exp_eq tau (s := 0) le_rfl N]
  simp [partialSum,powNeg]

private theorem product_right_zeta (tau : ℝ) {s : ℝ} (hs : 0<s) :
    Tendsto (boundaryEuler tau s) atTop (𝓝 (riemannZeta (1+(s : ℂ)+(tau : ℂ)*Complex.I))⁻¹) := by
  have hreal : 1<(1+(s : ℂ)+(tau : ℂ)*Complex.I).re := by simpa using hs
  have h := ((riemannZeta_eulerProduct hreal).comp (tendsto_add_atTop_nat 1)).inv₀
    (riemannZeta_ne_zero_of_one_lt_re hreal)
  apply h.congr
  intro N
  simp only [Function.comp_def,← Finset.prod_inv_distrib,inv_inv]
  change (∏ p ∈ Nat.primesBelow (N+1), (1-(p : ℂ)^(-(1+(s : ℂ)+(tau : ℂ)*Complex.I)))) = _
  have he : -(1+(s : ℂ)+(tau : ℂ)*Complex.I)= -1-(tau : ℂ)*Complex.I-(s : ℂ) := by ring
  simp only [he,boundaryEuler,boundaryNome,Nat.primesLE]

private theorem exp_continuation_eq_zeta (tau : ℝ) {M : ℝ}
    (hM : ∀ n, ‖partialSum (primeCoeff tau) n‖≤M) {s : ℝ} (hs : 0<s) :
    Complex.exp (-continuation (primeCoeff tau) (s : ℂ)+∑' n,boundaryRemainder tau s n)=
      (riemannZeta (1+(s : ℂ)+(tau : ℂ)*Complex.I))⁻¹ :=
  tendsto_nhds_unique (product_right_limit tau hM hs) (product_right_zeta tau hs)

private theorem inverse_zeta_boundary (tau : ℝˣ) :
    Tendsto (fun s : ℝ => (riemannZeta (1+(s : ℂ)+(tau : ℂ)*Complex.I))⁻¹)
      (𝓝[>] 0) (𝓝 (riemannZeta (1+(tau : ℂ)*Complex.I))⁻¹) := by
  have hne : 1+(tau : ℂ)*Complex.I≠1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im,Complex.one_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hi
    exact tau.ne_zero hi
  have hz := ((differentiableAt_riemannZeta hne).continuousAt.inv₀
    (riemannZeta_ne_zero_of_one_le_re (by simp : 1≤(1+(tau : ℂ)*Complex.I).re))).tendsto
  have hs : Tendsto (fun s : ℝ => 1+(s : ℂ)+(tau : ℂ)*Complex.I) (𝓝[>] 0)
      (𝓝 (1+(tau : ℂ)*Complex.I)) := by
    have h : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 0) (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds.add h).add_const ((tau : ℂ)*Complex.I)
  exact hz.comp hs

private theorem boundary_value_eq (tau : ℝˣ) {A : ℂ}
    (hA : Tendsto (partialSum (primeCoeff tau)) atTop (𝓝 A)) :
    Complex.exp (-A+∑' n,boundaryRemainder tau 0 n)=(riemannZeta (1+(tau : ℂ)*Complex.I))⁻¹ := by
  obtain ⟨M,hM⟩ := (Metric.isBounded_range_of_tendsto _ hA).exists_norm_le
  have hbd (n : ℕ) : ‖partialSum (primeCoeff tau) n‖≤M := hM _ ⟨n,rfl⟩
  have hlin := continuation_boundary (primeCoeff_zero tau) hA
  have h := (Complex.continuous_exp.tendsto _).comp (hlin.neg.add (remainder_sum_boundary tau))
  apply tendsto_nhds_unique h
  apply (inverse_zeta_boundary tau).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (exp_continuation_eq_zeta tau hbd hs).symm

/-- The original prime-ordered Euler product converges to inverse zeta at every
nonzero height on the one-line. No boundary convergence is assumed. -/
theorem criticalBoundaryEulerProduct_tendsto (tau : ℝˣ) :
    Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesLE N,
      (1-(p : ℂ)^(-1-(tau : ℂ)*Complex.I))) atTop
      (𝓝 (riemannZeta (1+(tau : ℂ)*Complex.I))⁻¹) := by
  obtain ⟨A,hA⟩ := prime_partial_limit tau
  have h := product_boundary_limit hA
  rw [boundary_value_eq tau hA] at h
  apply h.congr
  intro N
  simp only [boundaryEuler,boundaryNome,Complex.ofReal_zero,sub_zero]

/-- Every fixed logarithmic displacement of the original off-pole Euler product
converges to inverse zeta at its limiting one-line point. -/
theorem criticalMixedEulerProduct_tendsto (tau : ℝˣ) (u : ℂ) :
    Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesLE N,
      (1-(p : ℂ)^(-1-(tau : ℂ)*Complex.I+u/(Real.log N : ℂ)))) atTop
      (𝓝 (riemannZeta (1+(tau : ℂ)*Complex.I))⁻¹) := by
  have h := (criticalMixedEulerTiltRatio_tendsto tau u).mul
    (criticalBoundaryEulerProduct_tendsto tau)
  simp only [one_mul] at h
  apply h.congr
  intro N
  rw [criticalMixedEulerTiltRatio,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hn := Nat.prime_of_mem_primesLE hp
  have he : 1-criticalPrimeBoundaryCoeff tau p ≠ 0 := by
    simpa only [nome_zero] using nome_complement_ne tau (s := 0) le_rfl hn
  simpa only [criticalPrimeBoundaryCoeff] using div_mul_cancel₀
    (1-(p : ℂ)^(-1-(tau : ℂ)*Complex.I+u/(Real.log N : ℂ))) he

end RHTower.BAGTrace
