import GaloisForLFunctions.HTGeometry.VolterraConvolutionCalculus
import Mathlib.Analysis.Calculus.SmoothSeries

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower
noncomputable section

def relEvenBorelSeries (d : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑'n, d n*t^(2*n)/((2*n).factorial : ℝ)^2

def relEvenBinomialMoment (d e : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑a∈Finset.range (n+1), (Nat.choose (2*n) (2*a) : ℝ)*d a*e (n-a)

def relEvenBinomialSkew (d e : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑a∈Finset.range (n+1), ((2*a : ℝ)-(2*(n-a) : ℝ))*
    (Nat.choose (2*n) (2*a) : ℝ)*d a*e (n-a)

private def rvTerm (c : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ := c n*t^(2*n)
private def rvSlopeTerm (c : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  c n*(2*n:ℝ)*t^(2*n-1)
private def rvSeries (c : ℕ → ℝ) (t : ℝ) : ℝ := ∑'n, rvTerm c t n
private def rvPrimitiveTerm (c : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  c n*t^(2*n+1)/(2*n+1:ℝ)

private theorem rvTerm_radial (c : ℕ → ℝ) {T t : ℝ} (hT : 0≤T)
    (ht : |t|≤T) (n : ℕ) : ‖rvTerm c t n‖≤‖rvTerm c T n‖ := by
  simp only [rvTerm,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_nonneg hT]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) ht _) (abs_nonneg _)

private theorem rvTerm_bound {c : ℕ→ℝ} {K : ℝ} (hK : 0≤K)
    (hc : ∀n, ‖c n‖≤K^n/(n.factorial:ℝ)) {T t : ℝ} (ht : |t|≤T) (n : ℕ) :
    ‖rvTerm c t n‖≤(K*T^2)^n/(n.factorial:ℝ) := by
  have hT : 0≤T := (abs_nonneg t).trans ht
  rw [rvTerm,norm_mul,norm_pow,Real.norm_eq_abs]
  calc
    ‖c n‖*|t|^(2*n) ≤ (K^n/(n.factorial:ℝ))*T^(2*n) :=
      mul_le_mul (hc n) (pow_le_pow_left₀ (abs_nonneg t) ht _)
        (pow_nonneg (abs_nonneg t) _) (by positivity)
    _ = _ := by rw [mul_pow,←pow_mul]; ring

private theorem rv_degree_summable (q : ℝ) :
    Summable (fun n:ℕ => (2*n:ℝ)*q^n/(n.factorial:ℝ)) := by
  apply (summable_nat_add_iff 1).1
  refine ((Real.summable_pow_div_factorial q).mul_left (2*q)).congr ?_
  intro n
  rw [Nat.factorial_succ,pow_succ]
  push_cast
  have hf : (n.factorial:ℝ)≠0 := by positivity
  have hn : (n+1:ℝ)≠0 := by positivity
  field_simp

private theorem rvSlopeTerm_bound {c : ℕ→ℝ} {K : ℝ} (hK : 0≤K)
    (hc : ∀n, ‖c n‖≤K^n/(n.factorial:ℝ)) {T t : ℝ} (hT : 1≤T)
    (ht : |t|≤T) (n : ℕ) :
    ‖rvSlopeTerm c t n‖≤(2*n:ℝ)*(K*T^2)^n/(n.factorial:ℝ) := by
  have hp : |t|^(2*n-1)≤T^(2*n) :=
    (pow_le_pow_left₀ (abs_nonneg t) ht _).trans
      (pow_le_pow_right₀ hT (Nat.sub_le _ _))
  have hdeg : ‖(2*n:ℝ)‖=(2*n:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [rvSlopeTerm,norm_mul,norm_mul,norm_pow,hdeg]
  change ‖c n‖*(2*n:ℝ)*|t|^(2*n-1)≤_

  calc
    ‖c n‖*(2*n:ℝ)*|t|^(2*n-1)≤(K^n/(n.factorial:ℝ))*(2*n:ℝ)*T^(2*n) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hc n) (by positivity)) hp
        (by positivity) (by positivity)
    _ = (2*n:ℝ)*(K*T^2)^n/(n.factorial:ℝ) := by rw [mul_pow,←pow_mul]; ring

private theorem rvSeries_continuous {c : ℕ→ℝ}
    (hs : ∀T:ℝ, 0≤T → Summable (fun n=>‖rvTerm c T n‖)) :
    Continuous (rvSeries c) := by
  rw [continuous_iff_continuousAt]
  intro x
  let T : ℝ := |x|+1
  have hT : 0≤T := by dsimp [T]; positivity
  have hcont : ContinuousOn (rvSeries c) (Metric.ball 0 T) := by
    apply continuousOn_tsum (fun n => (by unfold rvTerm; fun_prop)) (hs T hT)
    intro n t ht
    exact rvTerm_radial c hT
      (le_of_lt (by simpa [Metric.mem_ball,Real.dist_eq] using ht)) n
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by
    simp [Metric.mem_ball,T]))

private theorem rv_power_admissions {c : ℕ→ℝ} {K : ℝ} (hK : 0≤K)
    (hc : ∀n, ‖c n‖≤K^n/(n.factorial:ℝ)) :
    Continuous (rvSeries c) ∧
    (∀t:ℝ, Summable (fun n=>‖rvTerm c t n‖)) ∧
    (∀t:ℝ, HasDerivAt (rvSeries c) (∑'n,rvSlopeTerm c t n) t) ∧
    Continuous (fun t:ℝ=>∑'n,rvSlopeTerm c t n) := by
  have hs (t:ℝ) : Summable (fun n=>‖rvTerm c t n‖) := by
    apply (Real.summable_pow_div_factorial (K*|t|^2)).of_nonneg_of_le
      (fun _=>norm_nonneg _)
    exact fun n=>rvTerm_bound hK hc (le_refl |t|) n
  refine ⟨rvSeries_continuous (fun T _=>hs T),hs,?_,?_⟩
  · intro t
    let T : ℝ := |t|+1
    have hT : 1≤T := by dsimp [T]; linarith [abs_nonneg t]
    have hg (n:ℕ) (y:ℝ) (_:y∈Metric.ball 0 T) :
        HasDerivAt (fun z=>rvTerm c z n) (rvSlopeTerm c y n) y := by
      simpa only [rvTerm,rvSlopeTerm,Pi.pow_apply,id_eq,mul_one,Nat.cast_mul,
        Nat.cast_ofNat,mul_assoc] using ((hasDerivAt_id y).pow (2*n)).const_mul (c n)
    exact hasDerivAt_tsum_of_isPreconnected (rv_degree_summable (K*T^2))
      Metric.isOpen_ball (convex_ball (0:ℝ) T).isPreconnected hg
      (fun n y hy=>rvSlopeTerm_bound hK hc hT
        (le_of_lt (by simpa [Metric.mem_ball,Real.dist_eq] using hy)) n)
      (by simp [Metric.mem_ball,T]; positivity) (hs 0).of_norm
      (by simp [Metric.mem_ball,T])
  · rw [continuous_iff_continuousAt]
    intro t
    let T : ℝ := |t|+1
    have hT : 1≤T := by dsimp [T]; linarith [abs_nonneg t]
    have hcont : ContinuousOn (fun t:ℝ=>∑'n,rvSlopeTerm c t n) (Metric.ball 0 T) := by
      apply continuousOn_tsum (fun n => (by unfold rvSlopeTerm; fun_prop))
        (rv_degree_summable (K*T^2))
      exact fun n y hy=>rvSlopeTerm_bound hK hc hT
        (le_of_lt (by simpa [Metric.mem_ball,Real.dist_eq] using hy)) n
    exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball,T]))

private theorem rv_normalized_bound {d : ℕ→ℝ} {R : ℝ} (hR : 0≤R)
    (hd : ∀n, ‖d n‖≤R^(2*n)) (n:ℕ) :
    ‖d n/((2*n).factorial:ℝ)^2‖≤(R^2)^n/(n.factorial:ℝ) := by
  have hf : (n.factorial:ℝ)≤((2*n).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le (show n≤2*n by omega)
  have hg : (1:ℝ)≤((2*n).factorial:ℝ) := by
    exact_mod_cast (show 1≤(2*n).factorial from Nat.factorial_pos _)
  have hh : (n.factorial:ℝ)≤((2*n).factorial:ℝ)^2 := by nlinarith
  have hnorm : ‖((2*n).factorial:ℝ)‖=((2*n).factorial:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [norm_div,norm_pow,hnorm]
  calc
    ‖d n‖/((2*n).factorial:ℝ)^2≤R^(2*n)/((2*n).factorial:ℝ)^2 :=
      div_le_div_of_nonneg_right (hd n) (by positivity)
    _ ≤ R^(2*n)/(n.factorial:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hh
    _ = (R^2)^n/(n.factorial:ℝ) := by rw [pow_mul]

theorem relEvenBorelSeries_admissions
    {d : ℕ → ℝ} {R : ℝ} (hR : 0≤R)
    (hd : ∀n, ‖d n‖≤R^(2*n)) :
  Continuous (relEvenBorelSeries d) ∧
  (∀t:ℝ, Summable (fun n => ‖d n*t^(2*n)/((2*n).factorial:ℝ)^2‖)) ∧
  (∀t:ℝ, HasDerivAt (relEvenBorelSeries d)
    (∑'n, d n*(2*n:ℝ)*t^(2*n-1)/((2*n).factorial:ℝ)^2) t) ∧
  Continuous (fun t:ℝ =>
    ∑'n, d n*(2*n:ℝ)*t^(2*n-1)/((2*n).factorial:ℝ)^2) := by
  have h := rv_power_admissions (sq_nonneg R) (rv_normalized_bound hR hd)
  have hfun : rvSeries (fun n=>d n/((2*n).factorial:ℝ)^2)=relEvenBorelSeries d := by
    funext t
    apply tsum_congr
    intro n
    dsimp [rvTerm]
    ring
  rw [hfun] at h
  simpa only [rvTerm,rvSlopeTerm,div_mul_eq_mul_div] using h

private theorem rv_interval_abs {t s : ℝ} (hs : s∈Set.uIcc (0:ℝ) t) :
    |s|≤|t| ∧ |t-s|≤|t| := by
  rcases Set.mem_uIcc.mp hs with hs|hs
  · have ht : 0≤t := hs.1.trans hs.2
    rw [abs_of_nonneg hs.1,abs_of_nonneg ht,abs_of_nonneg (sub_nonneg.mpr hs.2)]
    constructor <;> linarith [hs.1,hs.2]
  · have ht : t≤0 := hs.1.trans hs.2
    rw [abs_of_nonpos hs.2,abs_of_nonpos ht,abs_of_nonpos (sub_nonpos.mpr hs.1)]
    constructor <;> linarith [hs.1,hs.2]

private theorem rvPrimitiveTerm_bound (c : ℕ→ℝ) {T t : ℝ} (hT : 0≤T)
    (ht : |t|≤T) (n : ℕ) :
    ‖rvPrimitiveTerm c t n‖≤T*‖rvTerm c T n‖ := by
  have heq : rvPrimitiveTerm c t n=t*rvTerm c t n/(2*n+1:ℝ) := by
    dsimp [rvPrimitiveTerm,rvTerm]
    rw [pow_succ]
    ring
  have hden : ‖(2*n+1:ℝ)‖=(2*n+1:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [heq,norm_div,norm_mul,hden]
  change |t| * ‖rvTerm c t n‖/(2*n+1:ℝ)≤T*‖rvTerm c T n‖
  calc
    |t| * ‖rvTerm c t n‖/(2*n+1:ℝ)≤|t| * ‖rvTerm c t n‖ := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<2*n+1)).mpr
      nlinarith [mul_nonneg (show (0:ℝ)≤2*n by positivity)
        (mul_nonneg (abs_nonneg t) (norm_nonneg (rvTerm c t n)))]
    _ ≤ T*‖rvTerm c T n‖ :=
      mul_le_mul ht (rvTerm_radial c hT ht n) (norm_nonneg _) hT

private theorem rv_integral_term (c : ℕ→ℝ) (n : ℕ) (t : ℝ) :
    (∫s in (0:ℝ)..t,rvTerm c s n)=rvPrimitiveTerm c t n := by
  unfold rvTerm
  rw [intervalIntegral.integral_const_mul,integral_pow]
  simp only [zero_pow (by omega : 2*n+1≠0),sub_zero]
  dsimp [rvPrimitiveTerm]
  push_cast
  ring

private theorem rv_primitive {c : ℕ→ℝ}
    (hs : ∀T:ℝ,0≤T→Summable (fun n=>‖rvTerm c T n‖)) (t : ℝ) :
    Continuous (rvSeries c) ∧
    Summable (fun n=>‖rvPrimitiveTerm c t n‖) ∧
    (∫s in (0:ℝ)..t,rvSeries c s)=(∑'n,rvPrimitiveTerm c t n) ∧
    HasDerivAt (fun u:ℝ=>∑'n,rvPrimitiveTerm c u n) (rvSeries c t) t := by
  have hp (u:ℝ) : Summable (fun n=>‖rvPrimitiveTerm c u n‖) :=
    ((hs |u| (abs_nonneg _)).mul_left |u|).of_nonneg_of_le
      (fun _=>norm_nonneg _) (fun n=>rvPrimitiveTerm_bound c (abs_nonneg _) (le_refl _) n)
  have hi (u:ℝ) : (∫s in (0:ℝ)..u,rvSeries c s)=∑'n,rvPrimitiveTerm c u n := by
    have hh := intervalIntegral.hasSum_integral_of_dominated_convergence
      (a:=0) (b:=u) (μ:=volume) (F:=fun n s=>rvTerm c s n)
      (f:=rvSeries c) (fun n _=>‖rvTerm c |u| n‖)
      (fun n=>(by unfold rvTerm; fun_prop : Continuous (fun s=>rvTerm c s n)).aestronglyMeasurable)
      (fun n=>Eventually.of_forall fun s hs0=>
        rvTerm_radial c (abs_nonneg _) (rv_interval_abs (Set.uIoc_subset_uIcc hs0)).1 n)
      (Eventually.of_forall fun _ _=>hs |u| (abs_nonneg _)) intervalIntegrable_const
      (Eventually.of_forall fun s hs0=>(Summable.of_norm_bounded
        (hs |u| (abs_nonneg _)) (fun n=>rvTerm_radial c (abs_nonneg _)
          (rv_interval_abs (Set.uIoc_subset_uIcc hs0)).1 n)).hasSum)
    simpa only [rv_integral_term] using hh.tsum_eq.symm
  refine ⟨rvSeries_continuous hs,hp t,hi t,?_⟩
  have heq : (fun u:ℝ=>∑'n,rvPrimitiveTerm c u n)=fun u:ℝ=>∫s in (0:ℝ)..u,rvSeries c s :=
    funext (fun u=>(hi u).symm)
  rw [heq]
  exact ((rvSeries_continuous hs).integral_hasStrictDerivAt 0 t).hasDerivAt

private def rvDividedPower (n : ℕ) (t : ℝ) : ℝ := t^n/(n.factorial:ℝ)
@[fun_prop] private theorem rvDividedPower_continuous (n : ℕ) : Continuous (rvDividedPower n) := by
  unfold rvDividedPower
  fun_prop
private theorem rvDividedPower_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (rvDividedPower (n+1)) (rvDividedPower n t) t := by
  have h := ((hasDerivAt_id t).pow (n+1)).div_const ((n+1).factorial:ℝ)
  convert h using 1 <;> try rfl
  simp only [rvDividedPower, id_eq, Nat.add_sub_cancel, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_one]
  field_simp
private theorem rvDividedPower_beta (p q : ℕ) (t : ℝ) :
    ∫ s in 0..t, rvDividedPower p s * rvDividedPower q (t-s) =
      rvDividedPower (p+q+1) t := by
  induction q generalizing p with
  | zero =>
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a:=0) (b:=t) (fun x _ => rvDividedPower_deriv p x)
      (by exact (by fun_prop : Continuous (rvDividedPower p)).intervalIntegrable 0 t)
    simpa [rvDividedPower] using h
  | succ q ih =>
    have hu : ∀ x, HasDerivAt (fun s => rvDividedPower (q+1) (t-s))
        (-rvDividedPower q (t-x)) x := by
      intro x
      simpa only [Function.comp_def, zero_sub, mul_neg_one] using
        (rvDividedPower_deriv q (t-x)).comp x
          ((hasDerivAt_const x t).sub (hasDerivAt_id x))
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a:=0) (b:=t)
      (u:=fun s => rvDividedPower (q+1) (t-s)) (v:=rvDividedPower (p+1))
      (u':=fun s => -rvDividedPower q (t-s)) (v':=rvDividedPower p)
      (by fun_prop) (by fun_prop) (fun x _ => hu x)
      (fun x _ => rvDividedPower_deriv p x)
      ((by fun_prop : Continuous fun s => -rvDividedPower q (t-s)).intervalIntegrable 0 t)
      ((by fun_prop : Continuous (rvDividedPower p)).intervalIntegrable 0 t)
    simp only [rvDividedPower, sub_self, zero_pow (Nat.succ_ne_zero _), zero_div,
      zero_mul, mul_zero, sub_zero, zero_sub] at h
    have hn : (fun x : ℝ => -(rvDividedPower q (t-x)) * rvDividedPower (p+1) x) =
        (fun x => -(rvDividedPower q (t-x) * rvDividedPower (p+1) x)) := by
      funext x
      ring
    change (∫x in 0..t, rvDividedPower (q+1) (t-x)*rvDividedPower p x) =
      -(∫x in 0..t, -(rvDividedPower q (t-x))*rvDividedPower (p+1) x) at h
    rw [hn, intervalIntegral.integral_neg, neg_neg] at h
    calc
      (∫s in 0..t, rvDividedPower p s * rvDividedPower (q+1) (t-s)) =
          ∫s in 0..t, rvDividedPower (q+1) (t-s)*rvDividedPower p s := by
        congr 1
        funext s
        ring
      _ = ∫s in 0..t, rvDividedPower q (t-s)*rvDividedPower (p+1) s := h
      _ = ∫s in 0..t, rvDividedPower (p+1) s * rvDividedPower q (t-s) := by
        congr 1
        funext s
        ring
      _ = rvDividedPower (p+q+1+1) t := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (p+1)


private def rvCoeff (d : ℕ→ℝ) (n : ℕ) : ℝ := d n/((2*n).factorial:ℝ)^2
private def rvBlock (c b : ℕ→ℝ) (t s : ℝ) (n : ℕ) : ℝ :=
  ∑a∈Finset.range (n+1),rvTerm c s a*rvTerm b (t-s) (n-a)

private theorem rvCoeff_series (d : ℕ→ℝ) : rvSeries (rvCoeff d)=relEvenBorelSeries d := by
  funext t
  apply tsum_congr
  intro n
  dsimp [rvTerm,rvCoeff]
  ring

private theorem rv_normal_summable {c : ℕ→ℝ}
    (hs : ∀T:ℝ,0≤T→Summable (fun n=>‖rvTerm c T n‖)) (t : ℝ) :
    Summable (fun n=>‖rvTerm c t n‖) :=
  (hs |t| (abs_nonneg _)).of_nonneg_of_le (fun _=>norm_nonneg _)
    (fun n=>rvTerm_radial c (abs_nonneg _) (le_refl _) n)

private theorem rv_product_integral {c b : ℕ→ℝ}
    (hc : ∀T:ℝ,0≤T→Summable (fun n=>‖rvTerm c T n‖))
    (hb : ∀T:ℝ,0≤T→Summable (fun n=>‖rvTerm b T n‖)) (t : ℝ) :
    (∫s in (0:ℝ)..t,rvSeries c s*rvSeries b (t-s))=
      ∑'n,∫s in (0:ℝ)..t,rvBlock c b t s n := by
  let Q (n:ℕ) : ℝ := ∑a∈Finset.range (n+1),
    ‖rvTerm c |t| a‖*‖rvTerm b |t| (n-a)‖
  have hQ : Summable Q := (hasSum_sum_range_mul_of_summable_norm
    (hc |t| (abs_nonneg _)).norm (hb |t| (abs_nonneg _)).norm).summable
  have hblock (n:ℕ) : ∀ᵐs:ℝ,s∈Set.uIoc (0:ℝ) t→‖rvBlock c b t s n‖≤Q n := by
    filter_upwards [] with s hs
    have hsabs := rv_interval_abs (Set.uIoc_subset_uIcc hs)
    dsimp only [rvBlock,Q]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    rw [norm_mul]
    exact mul_le_mul (rvTerm_radial c (abs_nonneg _) hsabs.1 a)
      (rvTerm_radial b (abs_nonneg _) hsabs.2 (n-a)) (norm_nonneg _) (norm_nonneg _)
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a:=0) (b:=t) (μ:=volume) (F:=fun n s=>rvBlock c b t s n)
    (f:=fun s=>rvSeries c s*rvSeries b (t-s)) (fun n _=>Q n)
    (fun n=>(by unfold rvBlock rvTerm; fun_prop : Continuous (fun s=>rvBlock c b t s n)).aestronglyMeasurable)
    hblock (Eventually.of_forall fun _ _=>hQ) intervalIntegrable_const
    (Eventually.of_forall fun s _=>hasSum_sum_range_mul_of_summable_norm
      (rv_normal_summable hc s) (rv_normal_summable hb (t-s)))
  exact h.tsum_eq.symm

private theorem rv_even_term_beta (c b : ℕ→ℝ) (a k : ℕ) (t : ℝ) :
    (∫s in (0:ℝ)..t,rvTerm c s a*rvTerm b (t-s) k)=
      c a*b k*((2*a).factorial:ℝ)*((2*k).factorial:ℝ)*rvDividedPower (2*a+2*k+1) t := by
  have heq : (fun s:ℝ=>rvTerm c s a*rvTerm b (t-s) k)=
      (fun s:ℝ=>(c a*b k*((2*a).factorial:ℝ)*((2*k).factorial:ℝ))*
        (rvDividedPower (2*a) s*rvDividedPower (2*k) (t-s))) := by
    funext s
    dsimp [rvTerm,rvDividedPower]
    have ha : ((2*a).factorial:ℝ)≠0 := by positivity
    have hk : ((2*k).factorial:ℝ)≠0 := by positivity
    field_simp
  rw [heq,intervalIntegral.integral_const_mul,rvDividedPower_beta]

private theorem rv_choose_factorial (n a:ℕ) (ha:a≤n) :
    (Nat.choose (2*n) (2*a):ℝ)*((2*a).factorial:ℝ)*((2*(n-a)).factorial:ℝ)=
      ((2*n).factorial:ℝ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show 2*a≤2*n by omega)
  rw [show 2*n-2*a=2*(n-a) by omega] at h
  exact_mod_cast h

private theorem rv_block_integral (d e:ℕ→ℝ) (n:ℕ) (t:ℝ) :
    (∫s in (0:ℝ)..t,rvBlock (rvCoeff d) (rvCoeff e) t s n)=
      relEvenBinomialMoment d e n*t^(2*n+1)/
        (((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ)) := by
  unfold rvBlock
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [rv_even_term_beta]
    unfold relEvenBinomialMoment
    rw [Finset.sum_mul,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a ha
    have han : a≤n := by simpa using Finset.mem_range.mp ha
    rw [show 2*a+2*(n-a)+1=2*n+1 by omega]
    dsimp [rvCoeff,rvDividedPower]
    have hfA : ((2*a).factorial:ℝ)≠0 := by positivity
    have hfB : ((2*(n-a)).factorial:ℝ)≠0 := by positivity
    have hfN : ((2*n).factorial:ℝ)≠0 := by positivity
    have hfS : ((2*n+1).factorial:ℝ)≠0 := by positivity
    have hfac := rv_choose_factorial n a han
    field_simp
    linear_combination -(d a*e (n-a)*t^(2*n+1))*hfac
  · intro a _
    apply Continuous.intervalIntegrable
    unfold rvTerm
    fun_prop

private theorem rv_primitive_normalized {d:ℕ→ℝ}
    (hs : ∀T:ℝ,0≤T→Summable (fun n=>‖rvTerm (rvCoeff d) T n‖)) (t:ℝ) :
    Continuous (relEvenBorelSeries d) ∧
    HasDerivAt (fun u:ℝ=>∑'n,d n*u^(2*n+1)/
      (((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ))) (relEvenBorelSeries d t) t := by
  have h := rv_primitive hs t
  have hp (u:ℝ) (n:ℕ) : rvPrimitiveTerm (rvCoeff d) u n=
      d n*u^(2*n+1)/(((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ)) := by
    dsimp [rvPrimitiveTerm,rvCoeff]
    rw [Nat.factorial_succ]
    push_cast
    have hf : ((2*n).factorial:ℝ)≠0 := by positivity
    have hn : (2*n+1:ℝ)≠0 := by positivity
    field_simp
  rw [rvCoeff_series] at h
  exact ⟨h.1,by simpa only [hp] using h.2.2.2⟩

private theorem relEvenBinomialPositiveSum_le {R S : ℝ}
    (hR : 0≤R) (hS : 0≤S) (n : ℕ) :
    (∑a∈Finset.range (n+1), (Nat.choose (2*n) (2*a) : ℝ)*
      R^(2*a)*S^(2*(n-a))) ≤ (R+S)^(2*n) := by
  let f : ℕ → ℝ := fun k => R^k*S^(2*n-k)*(Nat.choose (2*n) k : ℝ)
  have himg : (Finset.range (n+1)).image (fun a => 2*a) ⊆
      Finset.range (2*n+1) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    simp only [Finset.mem_range] at ha ⊢
    omega
  have heq : (∑a∈Finset.range (n+1), (Nat.choose (2*n) (2*a) : ℝ)*
      R^(2*a)*S^(2*(n-a))) =
      ∑k∈(Finset.range (n+1)).image (fun a => 2*a), f k := by
    rw [Finset.sum_image (by intro a ha b hb hab; dsimp at hab; omega)]
    apply Finset.sum_congr rfl
    intro a ha
    have hsub : 2*(n-a)=2*n-2*a := by omega
    dsimp [f]
    rw [hsub]
    ring
  rw [heq, add_pow]
  apply Finset.sum_le_sum_of_subset_of_nonneg himg
  intro k hk hnot
  dsimp [f]
  positivity

private theorem relEvenBinomialMoment_bound {d e : ℕ → ℝ} {R S : ℝ}
    (hR : 0≤R) (hS : 0≤S)
    (hd : ∀n, ‖d n‖≤R^(2*n)) (he : ∀n, ‖e n‖≤S^(2*n)) (n : ℕ) :
    ‖relEvenBinomialMoment d e n‖≤(R+S)^(2*n) := by
  unfold relEvenBinomialMoment
  calc
    ‖∑a∈Finset.range (n+1), (Nat.choose (2*n) (2*a) : ℝ)*d a*e (n-a)‖
        ≤ ∑a∈Finset.range (n+1), ‖(Nat.choose (2*n) (2*a) : ℝ)*d a*e (n-a)‖ :=
      norm_sum_le _ _
    _ ≤ ∑a∈Finset.range (n+1), (Nat.choose (2*n) (2*a) : ℝ)*
        R^(2*a)*S^(2*(n-a)) := by
      apply Finset.sum_le_sum
      intro a ha
      simp only [norm_mul, Real.norm_of_nonneg (show (0:ℝ)≤(Nat.choose (2*n) (2*a):ℝ) by positivity)]
      gcongr
      · exact hd a
      · exact he (n-a)
    _ ≤ (R+S)^(2*n) := relEvenBinomialPositiveSum_le hR hS n

private theorem relEvenBinomialSkew_bound {d e : ℕ → ℝ} {R S : ℝ}
    (hR : 0≤R) (hS : 0≤S)
    (hd : ∀n, ‖d n‖≤R^(2*n)) (he : ∀n, ‖e n‖≤S^(2*n)) (n : ℕ) :
    ‖relEvenBinomialSkew d e n‖≤(2*n:ℝ)*(R+S)^(2*n) := by
  unfold relEvenBinomialSkew
  calc
    ‖∑a∈Finset.range (n+1), ((2*a:ℝ)-(2*(n-a):ℝ))*
        (Nat.choose (2*n) (2*a) : ℝ)*d a*e (n-a)‖
        ≤ ∑a∈Finset.range (n+1), ‖((2*a:ℝ)-(2*(n-a):ℝ))*
          (Nat.choose (2*n) (2*a) : ℝ)*d a*e (n-a)‖ := norm_sum_le _ _
    _ ≤ ∑a∈Finset.range (n+1), (2*n:ℝ)*
        ((Nat.choose (2*n) (2*a) : ℝ)*R^(2*a)*S^(2*(n-a))) := by
      apply Finset.sum_le_sum
      intro a ha
      have han : a≤n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ha
      have hac : (a:ℝ)≤(n:ℝ) := by exact_mod_cast han
      have hw : ‖((2*a:ℝ)-(2*(n-a):ℝ))‖≤(2*n:ℝ) := by
        rw [Real.norm_eq_abs]
        apply abs_le.mpr
        constructor <;> linarith [show (0:ℝ)≤(a:ℝ) by positivity]
      simp only [norm_mul, Real.norm_of_nonneg (show (0:ℝ)≤(Nat.choose (2*n) (2*a):ℝ) by positivity)]
      calc
        _ ≤ (2*n:ℝ)*(Nat.choose (2*n) (2*a):ℝ)*R^(2*a)*S^(2*(n-a)) := by
          gcongr
          · exact hd a
          · exact he (n-a)
        _ = _ := by ring
    _ = (2*n:ℝ)*(∑a∈Finset.range (n+1), (Nat.choose (2*n) (2*a):ℝ)*
        R^(2*a)*S^(2*(n-a))) := by rw [Finset.mul_sum]
    _ ≤ (2*n:ℝ)*(R+S)^(2*n) := by
      gcongr
      exact relEvenBinomialPositiveSum_le hR hS n


private theorem rvCoeff_normal {d:ℕ→ℝ} {R:ℝ} (hR:0≤R)
    (hd:∀n,‖d n‖≤R^(2*n)) :
    ∀T:ℝ,0≤T→Summable (fun n=>‖rvTerm (rvCoeff d) T n‖) := by
  intro T _
  exact (rv_power_admissions (sq_nonneg R) (rv_normalized_bound hR hd)).2.1 T

private theorem rvPrimitive_normal_summable {d:ℕ→ℝ}
    (hs:∀T:ℝ,0≤T→Summable (fun n=>‖rvTerm (rvCoeff d) T n‖)) (t:ℝ) :
    Summable (fun n=>‖d n*t^(2*n+1)/
      (((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ))‖) := by
  have hp (n:ℕ) : rvPrimitiveTerm (rvCoeff d) t n=
      d n*t^(2*n+1)/(((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ)) := by
    dsimp [rvPrimitiveTerm,rvCoeff]
    rw [Nat.factorial_succ]
    push_cast
    have hf:((2*n).factorial:ℝ)≠0 := by positivity
    have hn:(2*n+1:ℝ)≠0 := by positivity
    field_simp
  simpa only [hp] using (rv_primitive hs t).2.1

theorem relEvenBorelSeries_convolution
    {d e : ℕ→ℝ} {R S : ℝ} (hR : 0≤R) (hS : 0≤S)
    (hd : ∀n, ‖d n‖≤R^(2*n)) (he : ∀n, ‖e n‖≤S^(2*n)) (t : ℝ) :
  IntervalIntegrable
    (fun s => relEvenBorelSeries d (t-s)*relEvenBorelSeries e s) volume 0 t ∧
  volterraConv (relEvenBorelSeries d) (relEvenBorelSeries e) t =
    ∑'n, relEvenBinomialMoment d e n*t^(2*n+1)/
      (((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ)) ∧
  HasDerivAt (volterraConv (relEvenBorelSeries d) (relEvenBorelSeries e))
    (relEvenBorelSeries (relEvenBinomialMoment d e) t) t ∧
  Continuous (relEvenBorelSeries (relEvenBinomialMoment d e)) := by
  have hcontD := (relEvenBorelSeries_admissions hR hd).1
  have hcontE := (relEvenBorelSeries_admissions hS he).1
  have hnormalD := rvCoeff_normal hR hd
  have hnormalE := rvCoeff_normal hS he
  have hnormalM := rvCoeff_normal (add_nonneg hR hS)
    (relEvenBinomialMoment_bound hR hS hd he)
  have hprimitive := rv_primitive_normalized hnormalM t
  have heq (u:ℝ) : volterraConv (relEvenBorelSeries d) (relEvenBorelSeries e) u=
      ∑'n,relEvenBinomialMoment d e n*u^(2*n+1)/
        (((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ)) := by
    rw [volterraConv_comm]
    change (∫s in (0:ℝ)..u,relEvenBorelSeries e (u-s)*relEvenBorelSeries d s)=_
    have hmul : (fun s:ℝ=>relEvenBorelSeries e (u-s)*relEvenBorelSeries d s)=
        (fun s:ℝ=>rvSeries (rvCoeff d) s*rvSeries (rvCoeff e) (u-s)) := by
      rw [rvCoeff_series,rvCoeff_series]
      funext s
      ring
    rw [hmul,rv_product_integral hnormalD hnormalE]
    simp_rw [rv_block_integral]
  refine ⟨(by fun_prop : Continuous (fun s=>relEvenBorelSeries d (t-s)*
    relEvenBorelSeries e s)).intervalIntegrable 0 t,heq t,?_,hprimitive.1⟩
  have hfun := funext heq
  rw [hfun]
  exact hprimitive.2

private def rvWeighted (d:ℕ→ℝ) (n:ℕ) : ℝ := (2*n:ℝ)*d n

private theorem rv_degree_le_fourpow (n:ℕ) : (2*n:ℝ)≤(4:ℝ)^n := by
  have h:∀n:ℕ,(2*n+1:ℝ)≤(4:ℝ)^n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      push_cast
      nlinarith [show (0:ℝ)≤n by positivity]
  linarith [h n]

private theorem rvWeighted_bound {d:ℕ→ℝ} {R:ℝ} (_hR:0≤R)
    (hd:∀n,‖d n‖≤R^(2*n)) (n:ℕ) : ‖rvWeighted d n‖≤(2*R)^(2*n) := by
  have hdeg : ‖(2*n:ℝ)‖=(2*n:ℝ) := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [rvWeighted,norm_mul,hdeg]
  calc
    (2*n:ℝ)*‖d n‖≤(4:ℝ)^n*R^(2*n) :=
      mul_le_mul (rv_degree_le_fourpow n) (hd n) (norm_nonneg _) (by positivity)
    _ = (2*R)^(2*n) := by rw [mul_pow,pow_mul,pow_mul]; norm_num

private theorem rvWeighted_series {d:ℕ→ℝ} {R:ℝ} (hR:0≤R)
    (hd:∀n,‖d n‖≤R^(2*n)) :
    (fun t:ℝ=>t*deriv (relEvenBorelSeries d) t)=relEvenBorelSeries (rvWeighted d) := by
  funext t
  rw [((relEvenBorelSeries_admissions hR hd).2.2.1 t).deriv,←tsum_mul_left]
  unfold relEvenBorelSeries
  apply tsum_congr
  intro n
  by_cases hn:n=0
  · simp [hn,rvWeighted]
  · have hdegree:1≤2*n := by omega
    have hp:t*t^(2*n-1)=t^(2*n) := by rw [←pow_succ',Nat.sub_add_cancel hdegree]
    dsimp [rvWeighted]
    calc
      _ = d n*(2*n:ℝ)*(t*t^(2*n-1))/((2*n).factorial:ℝ)^2 := by ring
      _ = _ := by rw [hp]; ring

private theorem rv_skew_coefficient (d e:ℕ→ℝ) (n:ℕ) :
    relEvenBinomialMoment (rvWeighted d) e n-
      relEvenBinomialMoment d (rvWeighted e) n=relEvenBinomialSkew d e n := by
  unfold relEvenBinomialMoment relEvenBinomialSkew
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have han:a≤n := by simpa using Finset.mem_range.mp ha
  dsimp [rvWeighted]
  rw [Nat.cast_sub han]
  ring

private theorem rv_skew_normal {d e:ℕ→ℝ} {R S:ℝ} (hR:0≤R) (hS:0≤S)
    (hd:∀n,‖d n‖≤R^(2*n)) (he:∀n,‖e n‖≤S^(2*n)) :
    ∀T:ℝ,0≤T→Summable (fun n=>‖rvTerm (rvCoeff (relEvenBinomialSkew d e)) T n‖) := by
  apply rvCoeff_normal (show 0≤2*(R+S) by positivity)
  intro n
  calc
    ‖relEvenBinomialSkew d e n‖≤(2*n:ℝ)*(R+S)^(2*n) :=
      relEvenBinomialSkew_bound hR hS hd he n
    _ ≤ (4:ℝ)^n*(R+S)^(2*n) :=
      mul_le_mul_of_nonneg_right (rv_degree_le_fourpow n) (by positivity)
    _ = (2*(R+S))^(2*n) := by rw [mul_pow,pow_mul,pow_mul]; norm_num

theorem relEvenBorelSeries_skew_convolution
    {d e : ℕ→ℝ} {R S : ℝ} (hR : 0≤R) (hS : 0≤S)
    (hd : ∀n, ‖d n‖≤R^(2*n)) (he : ∀n, ‖e n‖≤S^(2*n)) (t : ℝ) :
  (volterraConv (fun s => s*deriv (relEvenBorelSeries d) s)
      (relEvenBorelSeries e) t -
    volterraConv (relEvenBorelSeries d)
      (fun s => s*deriv (relEvenBorelSeries e) s) t) =
    ∑'n, relEvenBinomialSkew d e n*t^(2*n+1)/
      (((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ)) ∧
  HasDerivAt (fun u =>
    volterraConv (fun s => s*deriv (relEvenBorelSeries d) s)
      (relEvenBorelSeries e) u -
    volterraConv (relEvenBorelSeries d)
      (fun s => s*deriv (relEvenBorelSeries e) s) u)
    (relEvenBorelSeries (relEvenBinomialSkew d e) t) t ∧
  Continuous (relEvenBorelSeries (relEvenBinomialSkew d e)) := by
  have hR2 : 0≤2*R := by positivity
  have hS2 : 0≤2*S := by positivity
  have hwd := rvWeighted_bound hR hd
  have hwe := rvWeighted_bound hS he
  have h1 (u:ℝ) := relEvenBorelSeries_convolution hR2 hS hwd he u
  have h2 (u:ℝ) := relEvenBorelSeries_convolution hR hS2 hd hwe u
  have hm1 := rvCoeff_normal (add_nonneg hR2 hS)
    (relEvenBinomialMoment_bound hR2 hS hwd he)
  have hm2 := rvCoeff_normal (add_nonneg hR hS2)
    (relEvenBinomialMoment_bound hR hS2 hd hwe)
  have hEven (u:ℝ) :
      relEvenBorelSeries (relEvenBinomialMoment (rvWeighted d) e) u-
        relEvenBorelSeries (relEvenBinomialMoment d (rvWeighted e)) u=
      relEvenBorelSeries (relEvenBinomialSkew d e) u := by
    unfold relEvenBorelSeries
    have hs1 : Summable (fun n=>relEvenBinomialMoment (rvWeighted d) e n*
        u^(2*n)/((2*n).factorial:ℝ)^2) := by
      refine (rv_normal_summable hm1 u).of_norm.congr ?_
      intro n
      dsimp [rvTerm,rvCoeff]
      ring
    have hs2 : Summable (fun n=>relEvenBinomialMoment d (rvWeighted e) n*
        u^(2*n)/((2*n).factorial:ℝ)^2) := by
      refine (rv_normal_summable hm2 u).of_norm.congr ?_
      intro n
      dsimp [rvTerm,rvCoeff]
      ring
    rw [←hs1.tsum_sub hs2]
    apply tsum_congr
    intro n
    rw [←rv_skew_coefficient]
    ring
  have hOdd (u:ℝ) :
      (∑'n,relEvenBinomialMoment (rvWeighted d) e n*u^(2*n+1)/
        (((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ)))-
      (∑'n,relEvenBinomialMoment d (rvWeighted e) n*u^(2*n+1)/
        (((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ)))=
      ∑'n,relEvenBinomialSkew d e n*u^(2*n+1)/
        (((2*n).factorial:ℝ)*((2*n+1).factorial:ℝ)) := by
    rw [←(rvPrimitive_normal_summable hm1 u).of_norm.tsum_sub
      (rvPrimitive_normal_summable hm2 u).of_norm]
    apply tsum_congr
    intro n
    rw [←rv_skew_coefficient]
    ring
  rw [rvWeighted_series hR hd,rvWeighted_series hS he]
  refine ⟨?_,?_,?_⟩
  · rw [(h1 t).2.1,(h2 t).2.1]
    exact hOdd t
  · have hder := (h1 t).2.2.1.sub (h2 t).2.2.1
    rw [hEven t] at hder
    exact hder
  · exact (rv_primitive_normalized (rv_skew_normal hR hS hd he) t).1

private theorem rv_skew_at_zero (d e:ℕ→ℝ) :
    relEvenBorelSeries (relEvenBinomialSkew d e) 0=0 := by
  have hz (n:ℕ) : relEvenBinomialSkew d e n*(0:ℝ)^(2*n)/((2*n).factorial:ℝ)^2=0 := by
    by_cases hn:n=0
    · subst n
      simp [relEvenBinomialSkew]
    · have hdeg:2*n≠0 := by omega
      simp [zero_pow hdeg]
  simp only [relEvenBorelSeries,hz,tsum_zero]


private theorem rv_integrated_relative_identity {A B PA PU : ℝ → ℝ}
    (hcA : Continuous A) (hcB : Continuous B)
    (hcPA : Continuous PA) (hcPU : Continuous PU)
    (hA : ∀ t : ℝ, 0 ≤ t → 2 * volterraConv PA A t = t * deriv A t)
    (hU : ∀ t : ℝ, 0 ≤ t → 2 * volterraConv PU B t = t * deriv B t)
    {t : ℝ} (ht : 0 ≤ t) :
    2 * volterraConv (fun s : ℝ => PA s-PU s) (volterraConv A B) t =
      volterraConv (fun s : ℝ => s*deriv A s) B t -
        volterraConv A (fun s : ℝ => s*deriv B s) t := by
  have hPA : 2 * volterraConv PA (volterraConv A B) t =
      volterraConv (fun s : ℝ => s*deriv A s) B t := by
    rw [← volterraConv_assoc hcPA hcA hcB t, ← volterraConv_smul_left]
    change (∫ s in (0 : ℝ)..t, (2*volterraConv PA A (t-s))*B s) =
      ∫ s in (0 : ℝ)..t, ((t-s)*deriv A (t-s))*B s
    apply intervalIntegral.integral_congr
    intro s hs
    have hst : s ≤ t := (Set.uIcc_of_le ht ▸ hs).2
    dsimp only
    rw [hA (t-s) (by linarith)]
  have hPU : 2 * volterraConv PU (volterraConv A B) t =
      volterraConv A (fun s : ℝ => s*deriv B s) t := by
    rw [volterraConv_comm PU (volterraConv A B) t,
      volterraConv_assoc hcA hcB hcPU t, volterraConv_comm' B PU,
      ← volterraConv_smul_right]
    change (∫ s in (0 : ℝ)..t, A (t-s)*(2*volterraConv PU B s)) =
      ∫ s in (0 : ℝ)..t, A (t-s)*(s*deriv B s)
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := (Set.uIcc_of_le ht ▸ hs).1
    dsimp only
    rw [hU s hs0]
  rw [volterraConv_comm (fun s : ℝ => PA s-PU s) (volterraConv A B) t,
    volterraConv_sub_right (continuous_volterraConv hcA hcB) hcPA hcPU t,
    volterraConv_comm (volterraConv A B) PA t,
    volterraConv_comm (volterraConv A B) PU t, mul_sub, hPA, hPU]

/-- Source-free transfer of two nonnegative-clock Volterra laws to the derivative kernel. -/
private theorem rv_calculus_transfer {A B PA PU BW C : ℝ → ℝ}
    (hcA : Continuous A) (hcB : Continuous B)
    (hcPA : Continuous PA) (hcPU : Continuous PU) (hcBW : Continuous BW)
    (hQ : ∀ t : ℝ, HasDerivAt (volterraConv A B) (BW t) t)
    (hG : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ =>
        volterraConv (fun s : ℝ => s*deriv A s) B u -
          volterraConv A (fun s : ℝ => s*deriv B s) u) (C t) t)
    (hC0 : C 0 = 0)
    (hA : ∀ t : ℝ, 0 ≤ t → 2 * volterraConv PA A t = t * deriv A t)
    (hU : ∀ t : ℝ, 0 ≤ t → 2 * volterraConv PU B t = t * deriv B t) :
    ∀ t : ℝ, 0 ≤ t →
      2 * volterraConv (fun s : ℝ => PA s-PU s) BW t = C t := by
  intro t ht
  by_cases ht0 : t=0
  · subst t
    simp only [volterraConv_apply_zero, mul_zero, hC0]
  have htpos : 0<t := lt_of_le_of_ne ht (fun h => ht0 h.symm)
  let H : ℝ → ℝ := fun s => PA s-PU s
  have hcH : Continuous H := hcPA.sub hcPU
  have hd : HasDerivAt (fun u : ℝ => 2*volterraConv H (volterraConv A B) u)
      (2*volterraConv H BW t) t := by
    have h := (hasDerivAt_volterraConv hQ hcBW hcH t).const_mul 2
    rw [volterraConv_apply_zero, zero_mul, zero_add, volterraConv_comm BW H t,
      volterraConv_comm' (volterraConv A B) H] at h
    exact h
  have heq : (fun u : ℝ =>
      volterraConv (fun s : ℝ => s*deriv A s) B u -
        volterraConv A (fun s : ℝ => s*deriv B s) u) =ᶠ[𝓝 t]
      (fun u : ℝ => 2*volterraConv H (volterraConv A B) u) := by
    filter_upwards [eventually_gt_nhds htpos] with u hu
    exact (rv_integrated_relative_identity hcA hcB hcPA hcPU hA hU hu.le).symm
  exact (hd.congr_of_eventuallyEq heq).unique (hG t)


theorem relEvenBorelSeries_relative_volterra
    {d e : ℕ→ℝ} {R S : ℝ} (hR : 0≤R) (hS : 0≤S)
    (hd : ∀n, ‖d n‖≤R^(2*n)) (he : ∀n, ‖e n‖≤S^(2*n))
    (PA PU : ℝ→ℝ) (hPA : Continuous PA) (hPU : Continuous PU)
    (hA : ∀t:ℝ, 0≤t →
      2*volterraConv PA (relEvenBorelSeries d) t =
        t*deriv (relEvenBorelSeries d) t)
    (hU : ∀t:ℝ, 0≤t →
      2*volterraConv PU (relEvenBorelSeries e) t =
        t*deriv (relEvenBorelSeries e) t)
    {t : ℝ} (ht : 0≤t) :
  2*volterraConv (fun s => PA s-PU s)
    (relEvenBorelSeries (relEvenBinomialMoment d e)) t =
      relEvenBorelSeries (relEvenBinomialSkew d e) t := by
  exact rv_calculus_transfer
    (relEvenBorelSeries_admissions hR hd).1 (relEvenBorelSeries_admissions hS he).1
    hPA hPU (relEvenBorelSeries_convolution hR hS hd he 0).2.2.2
    (fun u=>(relEvenBorelSeries_convolution hR hS hd he u).2.2.1)
    (fun u=>(relEvenBorelSeries_skew_convolution hR hS hd he u).2.1)
    (rv_skew_at_zero d e) hA hU t ht

end
end RHTower
