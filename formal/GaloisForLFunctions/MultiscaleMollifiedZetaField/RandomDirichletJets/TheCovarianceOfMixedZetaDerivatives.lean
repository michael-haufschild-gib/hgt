import GaloisForLFunctions.RHTower.SteinhausAbscissaSecondMoment
import GaloisForLFunctions.RHTower.ZetaPoleSplit
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Mixed derivatives of the Steinhaus Dirichlet polynomial

For the second moment in Najnudel and Wei's random derivative model,
integrating against the same prime phases selects the common Dirichlet
modes. At frequencies s and t the mixed second moment of two jets
tends to the (a+b)th derivative of ζ at s+conj(t). The sum still
converges whenever Re(s)+Re(t)>1. Scaling both points towards the
critical line leaves the differentiated Cauchy kernel.
-/

noncomputable section
open Finset Filter Topology MeasureTheory Complex
open scoped ComplexConjugate
open _root_.RHTower.SteinhausModel

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets

/-- Holomorphic continuation of the polynomial with a fixed cutoff. -/
def randomDirichletPolynomial (N : ℕ) (ω : Omega) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, X n ω * exp (-(Real.log n:ℂ)*s)

theorem randomDirichletPolynomial_real (N : ℕ) (ω : Omega) (σ : ℝ) :
    randomDirichletPolynomial N ω σ = GaloisForLFunctions.RHTower.steinhausDirichletPoly σ N ω := by
  apply sum_congr rfl
  intro n hn
  have hp : 0 < (n:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn).1
  rw [Real.rpow_def_of_pos hp,Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  rw [mul_neg,neg_mul,mul_comm (X n ω)]

/-- Scalar Fourier amplitude of a horizontal jet. -/
def dirichletJetMode (k n : ℕ) (s : ℂ) : ℂ :=
  (-(Real.log n:ℂ))^k*exp (-(Real.log n:ℂ)*s)

theorem dirichlet_jet_expansion (N k : ℕ) (ω : Omega) (s : ℂ) :
    iteratedDeriv k (randomDirichletPolynomial N ω) s =
      ∑ n ∈ Icc 1 N, dirichletJetMode k n s * X n ω := by
  unfold randomDirichletPolynomial
  rw [iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  apply sum_congr rfl
  intro n _
  rw [iteratedDeriv_const_mul_field (X n ω) (fun z : ℂ => exp (-(Real.log n:ℂ)*z)),
    iteratedDeriv_cexp_const_mul,dirichletJetMode,mul_comm (X n ω)]

private theorem mixed_parseval (A B : ℕ → ℂ) (S : Finset ℕ)
    (hs : ∀ n ∈ S, n ≠ 0) :
    (∫ ω, (∑ n ∈ S, A n*X n ω)*conj (∑ n ∈ S, B n*X n ω) ∂steinhausMeasure) =
      ∑ n ∈ S, A n*conj (B n) := by
  let f (n m : ℕ) (ω : Omega) := (A n*conj (B m))*(X n ω*conj (X m ω))
  have he (ω : Omega) : (∑ n ∈ S, A n*X n ω)*conj (∑ n ∈ S, B n*X n ω) =
      ∑ n ∈ S, ∑ m ∈ S, f n m ω := by
    rw [map_sum,sum_mul_sum]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by rw [map_mul]; dsimp only [f]; ring
  have hi (n m : ℕ) : Integrable (f n m) steinhausMeasure :=
    (integrable_X_mul_conj n m).const_mul _
  rw [integral_congr_ae (Eventually.of_forall he),
    integral_finsetSum _ (fun n _ => integrable_finsetSum _ fun m _ => hi n m)]
  apply sum_congr rfl
  intro n hn
  rw [integral_finsetSum _ fun m _ => hi n m,sum_eq_single n]
  · simp [f,integral_const_mul,integral_X_mul_conj (hs n hn) (hs n hn)]
  · intro m hm hne
    simp only [f,integral_const_mul,integral_X_mul_conj (hs n hn) (hs m hm),if_neg hne.symm,mul_zero]
  · exact fun hh => (hh hn).elim

/-- Mixed second moment of two actual finite Dirichlet jets. -/
def mixedJetMoment (N a b : ℕ) (s t : ℂ) : ℂ :=
  ∫ ω, iteratedDeriv a (randomDirichletPolynomial N ω) s *
    conj (iteratedDeriv b (randomDirichletPolynomial N ω) t) ∂steinhausMeasure

theorem mixed_jet_finite_kernel (N a b : ℕ) (s t : ℂ) :
    mixedJetMoment N a b s t = ∑ n ∈ Icc 1 N, dirichletJetMode (a+b) n (s+conj t) := by
  unfold mixedJetMoment
  simp_rw [dirichlet_jet_expansion]
  rw [mixed_parseval _ _ _ (fun _ hn => Nat.ne_of_gt (mem_Icc.mp hn).1)]
  apply sum_congr rfl
  intro n _
  simp only [dirichletJetMode,map_mul,map_pow,map_neg,←exp_conj,conj_ofReal,
    mul_add,exp_add,pow_add]
  ring

private theorem iterated_log_one (k n : ℕ) :
    (LSeries.logMul^[k] (1 : ℕ → ℂ)) n = (log n)^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',LSeries.logMul,ih,pow_succ,mul_comm]

private theorem mode_eq_term (k : ℕ) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    dirichletJetMode k n s = (-1:ℂ)^k*LSeries.term (LSeries.logMul^[k] 1) s n := by
  have hlog : (Real.log n:ℂ) = log n := by
    simpa only [Complex.ofReal_natCast] using Complex.ofReal_log (Nat.cast_nonneg n)
  rw [dirichletJetMode,LSeries.term_of_ne_zero hn,iterated_log_one,hlog,
    cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),neg_mul,exp_neg,div_eq_mul_inv]
  rw [show -(log n)=(-1:ℂ)*log n by ring,mul_pow]
  ring

/-- Only the sum of real parts has to exceed one for the mixed second
moment to converge, even when one of the individual variances diverges. -/
theorem mixed_jet_zeta_kernel (a b : ℕ) {s t : ℂ} (hst : 1 < s.re+t.re) :
    Tendsto (fun N => mixedJetMoment N a b s t) atTop
      (𝓝 (iteratedDeriv (a+b) riemannZeta (s+conj t))) := by
  let w := s+conj t
  let k := a+b
  have hw : 1 < w.re := by simpa [w] using hst
  have hc : LSeries.abscissaOfAbsConv 1 < w.re := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hw
  let g := LSeries.logMul^[k] (1 : ℕ → ℂ)
  have hg : LSeriesSummable g w := LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (by simpa only [g,LSeries.absicssaOfAbsConv_logPowMul] using hc)
  have hz : riemannZeta =ᶠ[𝓝 w] LSeries 1 := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hw] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  rw [hz.iteratedDeriv_eq k,LSeries_iteratedDeriv k hc]
  have hlim := (hg.hasSum.mul_left ((-1:ℂ)^k)).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  apply hlim.congr
  intro N
  have hi : range (N+1) = insert 0 (Icc 1 N) := by ext n; simp only [mem_range,mem_insert,mem_Icc]; omega
  change (∑ n ∈ range (N+1), (-1:ℂ)^k*LSeries.term g w n) = _
  rw [hi,sum_insert (by simp : 0 ∉ Icc 1 N),LSeries.term_zero,mul_zero,zero_add,mixed_jet_finite_kernel]
  exact sum_congr rfl fun n hn => (mode_eq_term k (Nat.ne_of_gt (mem_Icc.mp hn).1) w).symm

private theorem split_jet (k : ℕ) {w : ℂ} (hw : w ≠ 1) :
    iteratedDeriv k riemannZeta w = iteratedDeriv k _root_.RHTower.zetaRegularized w +
      (-1:ℂ)^k*(k.factorial:ℂ)/(w-1)^(k+1) := by
  have he : riemannZeta =ᶠ[𝓝 w] fun z => _root_.RHTower.zetaRegularized z + (z-1)⁻¹ := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hw] with z hz
    rw [_root_.RHTower.zetaRegularized_of_ne hz,one_div,sub_add_cancel]
  have hr := (_root_.RHTower.differentiable_zetaRegularized.analyticAt w).contDiffAt (n:=k)
  have hp : ContDiffAt ℂ k (fun z : ℂ => (z-1)⁻¹) w :=
    (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr hw)
  rw [he.iteratedDeriv_eq k,iteratedDeriv_fun_add hr hp]
  congr 1
  have hi := congrFun (iter_deriv_inv_linear_sub k (1:ℂ) 1) w
  simp only [one_mul,one_pow,mul_one] at hi
  rw [iteratedDeriv_eq_iterate,hi,show (-1-(k:ℤ)) = -((k+1:ℕ):ℤ) by push_cast; ring,
    zpow_neg,zpow_natCast,div_eq_mul_inv]

/-- At two moving points on the scale ε, all mixed jets approach the
differentiated Cauchy kernel after taking the cutoff limit. -/
theorem critical_mixed_jet_limit (a b : ℕ) {u v : ℂ} (huv : 0 < u.re+v.re) :
    ∃ F : ℝ → ℂ, (∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => mixedJetMoment N a b (1/2+(ε:ℂ)*u) (1/2+(ε:ℂ)*v)) atTop (𝓝 (F ε))) ∧
      Tendsto (fun ε : ℝ => (ε:ℂ)^(a+b+1)*F ε) (𝓝[>] 0)
        (𝓝 ((-1:ℂ)^(a+b)*((a+b).factorial:ℂ)/(u+conj v)^(a+b+1))) := by
  let d := u+conj v
  let k := a+b
  have hd : 0 < d.re := by simpa [d] using huv
  have hd' : d ≠ 0 := fun h => by simp [h] at hd
  let F (ε : ℝ) := iteratedDeriv k riemannZeta (1+(ε:ℂ)*d)
  have hp (ε : ℝ) (hε : 0 < ε) : 1 < (1+(ε:ℂ)*d).re := by
    simp only [add_re,one_re,re_ofReal_mul]; linarith only [mul_pos hε hd]
  refine ⟨F,?_,?_⟩
  · intro ε hε
    have he : (1/2+(ε:ℂ)*u)+conj (1/2+(ε:ℂ)*v)=1+(ε:ℂ)*d := by
      simp only [d,map_add,map_mul,map_div₀,map_one,map_ofNat,conj_ofReal]; ring
    have hh : 1 < (1/2+(ε:ℂ)*u).re+(1/2+(ε:ℂ)*v).re := by
      have h := hp ε hε
      rwa [←he,add_re,conj_re] at h
    simpa only [he,k,F] using mixed_jet_zeta_kernel a b hh
  · let R := iteratedDeriv k _root_.RHTower.zetaRegularized
    have hr : ContDiff ℂ k _root_.RHTower.zetaRegularized := contDiff_iff_contDiffAt.mpr
      fun w => (_root_.RHTower.differentiable_zetaRegularized.analyticAt w).contDiffAt
    have hR : Continuous R := hr.continuous_iteratedDeriv' k
    let C := (-1:ℂ)^k*(k.factorial:ℂ)/d^(k+1)
    have hcont : Continuous (fun ε : ℝ => (ε:ℂ)^(k+1)*R (1+(ε:ℂ)*d)+C) := by fun_prop
    have hlim := (hcont.continuousAt (x:=0)).continuousWithinAt (s:=Set.Ioi 0)
    simp only [ContinuousWithinAt,ofReal_zero,zero_pow (Nat.succ_ne_zero k),zero_mul,
      zero_add] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (ε:ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hε)
    have hne : 1+(ε:ℂ)*d ≠ 1 := fun h => (ne_of_gt (hp ε hε)) (congrArg re h)
    change (ε:ℂ)^(k+1)*R (1+(ε:ℂ)*d)+C = (ε:ℂ)^(k+1)*F ε
    rw [show F ε = R (1+(ε:ℂ)*d)+(-1:ℂ)^k*(k.factorial:ℂ)/((ε:ℂ)*d)^(k+1) by
      dsimp only [F,R]; rw [split_jet k hne,add_sub_cancel_left]]
    rw [mul_pow (ε:ℂ) d,mul_add ((ε:ℂ)^(k+1)) (R _) _]
    congr 1
    dsimp only [C]
    field_simp [hε',hd']

#print axioms mixed_jet_finite_kernel
#print axioms mixed_jet_zeta_kernel
#print axioms critical_mixed_jet_limit

end GaloisForLFunctions.MultiscaleMollifiedZetaField.RandomDirichletJets
