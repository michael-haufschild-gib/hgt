import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheRegularPartOfSquarefreeSections
import GaloisForLFunctions.HTGeometry.MeromorphicPrincipalPart
import GaloisForLFunctions.HTGeometry.ZeroEstimate
import Mathlib.LinearAlgebra.Lagrange

/-!
# Laurent coefficients from nonzero harmonics of squarefree sections

El Kaouni's Mellin integration by parts and the finite Vandermonde argument
of Gabet, Ferreira Da Costa and Lee give an interpolation
formula for each Taylor coefficient
of the pole-subtracted quotient at one. All readings use the same
sharp cutoff. Their positive harmonics cancel the density integral
individually, and the filter cancels every unwanted lower Taylor term.
-/
noncomputable section
open Finset Complex Polynomial Filter MeasureTheory
open scoped Topology Polynomial
open GaloisForLFunctions.HTGeometry (taylorCoeffZero exists_taylor_remainder)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def fundamental (T : ℝ) := (2*(Real.pi:ℂ)*I)/(T:ℂ)
private def location (T : ℝ) (k : ℕ) := 1+(k:ℂ)*fundamental T

/-- A harmonic measurement of the squarefree section through exp(T). -/
def squarefreeGridSample (T : ℝ) (k : ℕ) := squarefreeSection (Real.exp T) (location T k)

/-- Holomorphic germ of the squarefree quotient with its pole removed. -/
def shiftedRegularGerm (w : ℂ) := squarefreeRegularPart (1+w)

private theorem germ_analytic : AnalyticAt ℂ shiftedRegularGerm 0 := by
  have hf : DifferentiableOn ℂ squarefreeRegularPart {s : ℂ | 1/2<s.re} :=
    fun _ hs => (differentiableAt_squarefreeRegularPart hs).differentiableWithinAt
  have hbase := hf.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1:ℂ)∈{s : ℂ | 1/2<s.re} by norm_num))
  have had : AnalyticAt ℂ (fun z : ℂ => 1+z) 0 := analyticAt_const.add analyticAt_id
  exact (show AnalyticAt ℂ squarefreeRegularPart (1+(0:ℂ)) by simpa using hbase).comp had

private theorem fundamental_as_real (T : ℝ) : fundamental T=((2*Real.pi/T:ℝ):ℂ)*I := by
  dsimp only [fundamental]; push_cast; ring

private theorem location_re (T : ℝ) (k : ℕ) : (location T k).re=1 := by
  simp [location,fundamental_as_real,Complex.mul_re,Complex.mul_im]

private theorem fundamental_limit : Tendsto fundamental atTop (𝓝 0) := by
  have hr : Tendsto (fun T : ℝ => 2*Real.pi/T) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).mul_const I
  have hfun : fundamental = fun T : ℝ => ((2*Real.pi/T:ℝ):ℂ)*I := funext fundamental_as_real
  rw [hfun]
  simpa only [Complex.ofReal_zero,zero_mul,Function.comp_apply] using hh

private theorem fundamental_nonzero {T : ℝ} (hT : 0<T) : fundamental T≠0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hT.ne')

private theorem density_primitive_vanishes {T : ℝ} (hT : 0<T) {k : ℕ} (hk : 0<k) :
    (∫ x in Set.Ioc 1 (Real.exp T),(x:ℂ)^(-location T k))=0 := by
  have hX := Real.one_lt_exp_iff.mpr hT
  have h := squarefree_density_primitive hX.le (location T k)
  have hs : 1-location T k= -(k:ℂ)*fundamental T := by dsimp only [location];ring
  rw [hs,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos T).ne'),
    ←Complex.ofReal_log (Real.exp_pos T).le,Real.log_exp] at h
  have he : (T:ℂ)*(-(k:ℂ)*fundamental T)=-((k:ℂ)*(2*(Real.pi:ℂ)*I)) := by
    dsimp only [fundamental];field_simp [Complex.ofReal_ne_zero.mpr hT.ne']
  have hphase : Complex.exp (-((k:ℂ)*(2*(Real.pi:ℂ)*I)))=1 := by
    rw [Complex.exp_neg,Complex.exp_nat_mul_two_pi_mul_I,inv_one]
  rw [he,hphase,sub_self] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hk.ne')) (fundamental_nonzero hT))

private theorem sample_error {T : ℝ} (hT : 1≤T) {k : ℕ} (hk : 0<k) :
    ‖squarefreeGridSample T k-shiftedRegularGerm ((k:ℂ)*fundamental T)‖ ≤
      4*(1+2*(1+(k:ℝ)*(2*Real.pi)))*Real.exp (-(T/2)) := by
  have hp := zero_lt_one.trans_le hT
  have h := squarefree_section_regular_part_error (Real.one_lt_exp_iff.mpr hp).le
    (s:=location T k) (by rw [location_re];norm_num)
  rw [density_primitive_vanishes hp hk,mul_zero,sub_zero,location_re,
    show (1/2:ℝ)-1= -(1/2) by norm_num,←Real.exp_mul,
    show T* -(1/2:ℝ)= -(T/2) by ring] at h
  have hf : ‖fundamental T‖≤2*Real.pi := by
    rw [fundamental_as_real,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (div_pos (mul_pos (by norm_num) Real.pi_pos) hp),Complex.norm_I,mul_one]
    exact div_le_self (by positivity) hT
  have hs : ‖location T k‖≤1+(k:ℝ)*(2*Real.pi) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one,norm_mul,Complex.norm_natCast]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg _)) _
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have h2 : ‖location T k‖/(1-1/2) = 2*‖location T k‖ := by ring
  linarith only [hs,h2]

private theorem exponential_beats_power (m : ℕ) :
    Tendsto (fun T : ℝ => T^m*Real.exp (-(T/2))) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun T : ℝ => T/2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp hhalf).const_mul ((2:ℝ)^m)
  rw [mul_zero] at h
  refine h.congr' (.of_forall fun T => ?_)
  dsimp only [Function.comp_apply]
  rw [←mul_assoc,←mul_pow,show 2*(T/2)=T by ring]

private theorem normalized_sample_error (m k : ℕ) (hk : 0<k) :
    Tendsto (fun T : ℝ => (squarefreeGridSample T k-shiftedRegularGerm ((k:ℂ)*fundamental T))/(fundamental T)^m)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  let B := 4*(1+2*(1+(k:ℝ)*(2*Real.pi)))
  have h := (exponential_beats_power m).const_mul (B/(2*Real.pi)^m)
  rw [mul_zero] at h
  refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_ h
  filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
  have hp := zero_lt_one.trans_le hT
  have hπ : 0<2*Real.pi := by positivity
  rw [norm_div,norm_pow,fundamental_as_real,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (div_pos hπ hp),Complex.norm_I,mul_one]
  apply (div_le_div_of_nonneg_right (by simpa only [fundamental_as_real] using sample_error hT hk)
    (pow_nonneg (div_pos hπ hp).le m)).trans_eq
  dsimp only [B]
  rw [div_pow,div_div_eq_mul_div]
  ring

/-- Coefficient of top degree in a Lagrange cardinal polynomial. -/
def harmonicJetWeight {m : ℕ} (node : Fin (m+1) → ℕ) (i : Fin (m+1)) :=
  (Lagrange.basis univ (fun i => (node i:ℂ)) i).coeff m

/-- A normalized degree-m filter answers every monomial of degree at most m. -/
def harmonicJetExact {n : ℕ} (m : ℕ) (node : Fin n → ℕ) (a : Fin n → ℂ) : Prop :=
  ∀ k ≤ m, (∑ j, a j*(node j:ℂ)^k) = if k=m then 1 else 0

private theorem interpolate_top {m : ℕ} {node : Fin (m+1) → ℕ}
    (hnode : Function.Injective node) (P : Polynomial ℂ) (hP : P.natDegree≤ m) :
    P.coeff m=∑ j, harmonicJetWeight node j*P.eval (node j : ℂ) := by
  have hinj : Function.Injective (fun j => (node j:ℂ)) := fun i j h =>
    hnode (Nat.cast_injective h)
  have hd : P.degree<((univ : Finset (Fin (m+1))).card : WithBot ℕ) := by
    rw [card_univ,Fintype.card_fin]
    exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hP))
  have he := Lagrange.eq_interpolate (s:=univ) (v:=fun j => (node j:ℂ)) hinj.injOn hd
  have hh := congrArg (fun Q : Polynomial ℂ => Q.coeff m) he
  rw [Lagrange.interpolate_apply] at hh
  change P.coeff m=(Polynomial.lcoeff ℂ m) (∑ j, C (P.eval (node j : ℂ))*_) at hh
  rw [map_sum] at hh
  change P.coeff m=∑ j, (C (P.eval (node j : ℂ))*Lagrange.basis univ (fun i => (node i:ℂ)) j).coeff m at hh
  simpa only [harmonicJetWeight,Polynomial.coeff_C_mul,mul_comm] using hh

private theorem exact_lagrange {m : ℕ} {node : Fin (m+1) → ℕ}
    (hnode : Function.Injective node) : harmonicJetExact m node (harmonicJetWeight node) := by
  intro k hk
  have h := interpolate_top hnode (X^k) (by simpa only [natDegree_X_pow] using hk)
  simpa only [coeff_X_pow,Polynomial.eval_pow,Polynomial.eval_X,eq_comm] using h.symm

/-- Distinct readings that kill all lower Taylor terms and preserve degree
m require at least m+1 nodes. The bound concerns polynomial-exact linear rules. -/
theorem harmonic_jet_requires_nodes {m n : ℕ} {node : Fin n → ℕ} {a : Fin n → ℂ}
    (hnode : Function.Injective node) (h : harmonicJetExact m node a) : m+1≤n := by
  by_contra hn
  have hinj : Function.Injective (fun j => (node j:ℂ)) := fun i j he => hnode (Nat.cast_injective he)
  have hzero := GaloisForLFunctions.vandermonde_moments_eq_zero_of_injective hinj (c:=a) (fun k => by
    have hk : (k:ℕ)< m := by have := k.isLt; omega
    simpa only [if_neg hk.ne] using h k hk.le)
  have htop := h m le_rfl
  simp [hzero] at htop

/-- At the minimum sample size the weights are forced, at every choice of
distinct harmonics. -/
theorem harmonic_jet_weights_unique {m : ℕ} {node : Fin (m+1) → ℕ} {a : Fin (m+1) → ℂ}
    (hnode : Function.Injective node) :
    harmonicJetExact m node a ↔ a=harmonicJetWeight node := by
  refine ⟨fun ha => ?_,fun he => he ▸ exact_lagrange hnode⟩
  have hinj : Function.Injective (fun j => (node j:ℂ)) := fun i j he => hnode (Nat.cast_injective he)
  apply sub_eq_zero.mp
  apply GaloisForLFunctions.vandermonde_moments_eq_zero_of_injective hinj
  intro k
  have hk : (k:ℕ)≤ m := Nat.lt_succ_iff.mp k.isLt
  simp only [Pi.sub_apply,sub_mul,sum_sub_distrib,ha k hk,exact_lagrange hnode k hk,sub_self]

private theorem harmonic_taylor_expansion {m n : ℕ} {node : Fin n → ℕ} {a : Fin n → ℂ}
    (ha : harmonicJetExact m node a) (F H : ℂ → ℂ)
    (hH : ∀ z, F z=(∑ k∈range (m+1),taylorCoeffZero F k*z^k)+z^(m+1)*H z) (w : ℂ) :
    (∑ j, a j*F ((node j:ℂ)*w)) = taylorCoeffZero F m*w^m+
      w^(m+1)*∑ j, a j*(node j:ℂ)^(m+1)*H ((node j:ℂ)*w) := by
  have he (j : Fin n) :
      a j*F ((node j:ℂ)*w)=
        (∑ k∈range (m+1),a j*(node j:ℂ)^k*(taylorCoeffZero F k*w^k))+
        w^(m+1)*(a j*(node j:ℂ)^(m+1)*H ((node j:ℂ)*w)) := by
    rw [hH,mul_add,mul_sum,mul_pow]
    congr 1
    · exact sum_congr rfl fun k _ => by rw [mul_pow]; ring
    · ring
  simp_rw [he]
  rw [sum_add_distrib,←mul_sum,sum_comm]
  congr 1
  simp_rw [←sum_mul]
  rw [Finset.sum_range_succ,sum_eq_zero (fun k (hk : k∈range m) => by
    rw [ha k (mem_range.mp hk).le,if_neg (mem_range.mp hk).ne,zero_mul]),zero_add,
    ha m le_rfl,if_pos rfl,one_mul]

/-- The normalized linear reading at a common squarefree cutoff. -/
def harmonicLaurentReading {n : ℕ} (m : ℕ) (node : Fin n → ℕ) (a : Fin n → ℂ) (T : ℝ) :=
  (∑ j, a j*squarefreeGridSample T (node j))/(fundamental T)^m

private theorem recovery_of_exact {m n : ℕ} {node : Fin n → ℕ} {a : Fin n → ℂ}
    (hp : ∀ j, 0<node j) (ha : harmonicJetExact m node a) :
    Tendsto (harmonicLaurentReading m node a) atTop (𝓝 (taylorCoeffZero shiftedRegularGerm m)) := by
  obtain ⟨H,hH,htaylor⟩ := exists_taylor_remainder germ_analytic (m+1)
  have hnorm (j : Fin n) := (normalized_sample_error m (node j) (hp j)).const_mul (a j)
  have herr := tendsto_finsetSum univ (fun j _ => hnorm j)
  simp only [mul_zero,sum_const_zero] at herr
  have hcont (j : Fin n) : Tendsto (fun T => a j*(node j:ℂ)^(m+1)*H ((node j:ℂ)*fundamental T))
      atTop (𝓝 (a j*(node j:ℂ)^(m+1)*H 0)) := by
    apply Filter.Tendsto.const_mul
    apply hH.continuousAt.tendsto.comp
    simpa only [mul_zero] using fundamental_limit.const_mul (node j:ℂ)
  have hh := fundamental_limit.mul (tendsto_finsetSum univ (fun j _ => hcont j))
  rw [zero_mul] at hh
  have h := (herr.add hh).const_add (taylorCoeffZero shiftedRegularGerm m)
  simp only [zero_add,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  let w := fundamental T
  have hw : w≠0 := fundamental_nonzero hT
  have hi := harmonic_taylor_expansion ha shiftedRegularGerm H htaylor w
  let S := ∑ j, a j*squarefreeGridSample T (node j)
  let F := ∑ j, a j*shiftedRegularGerm ((node j:ℂ)*w)
  let J := ∑ j, a j*(node j:ℂ)^(m+1)*H ((node j:ℂ)*w)
  change F=taylorCoeffZero shiftedRegularGerm m*w^m+w^(m+1)*J at hi
  have hd : (∑ j, a j*((squarefreeGridSample T (node j)-
      shiftedRegularGerm ((node j:ℂ)*w))/w^m))=(S-F)/w^m := by
    dsimp only [S,F]
    simp only [←mul_div_assoc,mul_sub,sum_div,sum_sub_distrib,sub_div]
  change taylorCoeffZero shiftedRegularGerm m+((∑ j, a j*((squarefreeGridSample T (node j)-
    shiftedRegularGerm ((node j:ℂ)*w))/w^m))+w*J)=S/w^m
  rw [hd,hi,pow_succ]
  field_simp [hw]
  ring

/-- Any m+1 distinct positive integer harmonics give the m-th regular
Laurent coefficient of the squarefree Dirichlet quotient at one. -/
theorem squarefree_laurent_from_any_harmonics {m : ℕ} {node : Fin (m+1) → ℕ}
    (hnode : Function.Injective node) (hp : ∀ i,0<node i) :
    Tendsto (harmonicLaurentReading m node (harmonicJetWeight node)) atTop
      (𝓝 (taylorCoeffZero shiftedRegularGerm m)) :=
  recovery_of_exact hp (exact_lagrange hnode)

/-- The first m+1 nonzero harmonics suffice, all sampled through exp(T). -/
theorem squarefree_laurent_from_consecutive_harmonics (m : ℕ) :
    Tendsto (harmonicLaurentReading m (fun j : Fin (m+1) => j.val+1)
      (harmonicJetWeight (fun j : Fin (m+1) => j.val+1))) atTop
      (𝓝 (taylorCoeffZero shiftedRegularGerm m)) := by
  apply squarefree_laurent_from_any_harmonics
  · intro i j h
    exact Fin.ext (Nat.add_right_cancel h)
  · exact fun j => Nat.succ_pos _

/-- The polynomial in the dyadic dilation annihilates degrees below m. -/
def harmonicJetFilter (m : ℕ) : Polynomial ℂ :=
  ∏ k∈range m,(X-C ((2:ℂ)^k))

private theorem moments (P : Polynomial ℂ) (k : ℕ) :
    (∑ j∈P.support,P.coeff j*((2^j:ℕ):ℂ)^k)=P.eval ((2:ℂ)^k) := by
  rw [Polynomial.eval_eq_sum,Polynomial.sum]
  refine sum_congr rfl fun j _ => ?_
  push_cast;rw [←pow_mul,←pow_mul,Nat.mul_comm]

private theorem filter_at (m k : ℕ) : (harmonicJetFilter m).eval ((2:ℂ)^k)=
    ∏ j∈range m,((2:ℂ)^k-2^j) := by simp [harmonicJetFilter,Polynomial.eval_prod]

private theorem filter_low {k m : ℕ} (h : k< m) : (harmonicJetFilter m).eval ((2:ℂ)^k)=0 := by
  rw [filter_at]
  exact prod_eq_zero (mem_range.mpr h) (sub_self _)

private theorem filter_top (m : ℕ) : (harmonicJetFilter m).eval ((2:ℂ)^m)≠0 := by
  rw [filter_at]
  apply prod_ne_zero_iff.mpr
  intro j hj
  have hlt : (2:ℕ)^j<2^m := Nat.pow_lt_pow_right (by decide) (mem_range.mp hj)
  apply sub_ne_zero.mpr
  exact_mod_cast hlt.ne'

private theorem filter_expansion (m : ℕ) (F H : ℂ → ℂ)
    (hH : ∀ z, F z=(∑ k∈range (m+1),taylorCoeffZero F k*z^k)+z^(m+1)*H z) (w : ℂ) :
    (∑ j∈(harmonicJetFilter m).support,(harmonicJetFilter m).coeff j*F (((2^j:ℕ):ℂ)*w))=
      (harmonicJetFilter m).eval ((2:ℂ)^m)*taylorCoeffZero F m*w^m+
        w^(m+1)*∑ j∈(harmonicJetFilter m).support,(harmonicJetFilter m).coeff j*
          ((2^j:ℕ):ℂ)^(m+1)*H (((2^j:ℕ):ℂ)*w) := by
  let P := harmonicJetFilter m
  have hs (j : ℕ) :
      P.coeff j*F (((2^j:ℕ):ℂ)*w)=
        (∑ k∈range (m+1),P.coeff j*((2^j:ℕ):ℂ)^k*(taylorCoeffZero F k*w^k))+
          w^(m+1)*(P.coeff j*((2^j:ℕ):ℂ)^(m+1)*H (((2^j:ℕ):ℂ)*w)) := by
    rw [hH,mul_add,mul_sum,mul_pow]
    congr 1
    · exact sum_congr rfl fun k _ => by rw [mul_pow];ring
    · ring
  change (∑ j∈P.support,P.coeff j*F _)=_
  simp_rw [hs]
  rw [sum_add_distrib,←mul_sum,sum_comm]
  suffices hsum : (∑ k∈range (m+1),∑ j∈P.support,
      P.coeff j*((2^j:ℕ):ℂ)^k*(taylorCoeffZero F k*w^k))=P.eval ((2:ℂ)^m)*taylorCoeffZero F m*w^m by
    rw [hsum]
  simp_rw [←sum_mul,moments]
  rw [Finset.sum_range_succ,sum_eq_zero (fun k (hk : k∈range m) => by
    rw [show P.eval ((2:ℂ)^k)=0 from filter_low (mem_range.mp hk),zero_mul]),zero_add,mul_assoc]

/-- The normalized arithmetic reading uses finitely many nonzero positive
harmonics, all observed at the same cutoff exp(T). -/
def squarefreeLaurentReading (m : ℕ) (T : ℝ) : ℂ :=
  (∑ j∈(harmonicJetFilter m).support,(harmonicJetFilter m).coeff j*squarefreeGridSample T (2^j))/
    ((harmonicJetFilter m).eval ((2:ℂ)^m)*(fundamental T)^m)

/-- Every regular Laurent coefficient of ζ(s)/ζ(2s) at one is the limit
of a single linear combination of sharp squarefree harmonic readings.
No preceding coefficient enters the measurements or their normalization. -/
theorem squarefree_laurent_coefficient_from_harmonics (m : ℕ) :
    Tendsto (squarefreeLaurentReading m) atTop (𝓝 (taylorCoeffZero shiftedRegularGerm m)) := by
  let P := harmonicJetFilter m
  let Z := P.eval ((2:ℂ)^m)
  have hZ : Z≠0 := filter_top m
  obtain ⟨H,hH,htaylor⟩ := exists_taylor_remainder germ_analytic (m+1)
  have hnorm (j : ℕ) := (normalized_sample_error m (2^j) (by positivity)).const_mul (P.coeff j)
  have herr := tendsto_finsetSum P.support (fun j _ => hnorm j)
  simp only [mul_zero,sum_const_zero] at herr
  have hcont (j : ℕ) : Tendsto (fun T => P.coeff j*((2^j:ℕ):ℂ)^(m+1)*
      H (((2^j:ℕ):ℂ)*fundamental T)) atTop (𝓝 (P.coeff j*((2^j:ℕ):ℂ)^(m+1)*H 0)) := by
    apply Filter.Tendsto.const_mul
    apply hH.continuousAt.tendsto.comp
    simpa only [mul_zero] using fundamental_limit.const_mul ((2^j:ℕ):ℂ)
  have hh := fundamental_limit.mul (tendsto_finsetSum P.support (fun j _ => hcont j))
  rw [zero_mul] at hh
  have h := ((herr.add hh).div_const Z).const_add (taylorCoeffZero shiftedRegularGerm m)
  simp only [zero_add,zero_div,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  let w := fundamental T
  have hw : w≠0 := fundamental_nonzero hT
  have hident := filter_expansion m shiftedRegularGerm H htaylor w
  let S := ∑ j∈P.support,P.coeff j*squarefreeGridSample T (2^j)
  let F := ∑ j∈P.support,P.coeff j*shiftedRegularGerm (((2^j:ℕ):ℂ)*w)
  let J := ∑ j∈P.support,P.coeff j*((2^j:ℕ):ℂ)^(m+1)*H (((2^j:ℕ):ℂ)*w)
  change F=Z*taylorCoeffZero shiftedRegularGerm m*w^m+w^(m+1)*J at hident
  have he : (∑ j∈P.support,P.coeff j*((squarefreeGridSample T (2^j)-
      shiftedRegularGerm (((2^j:ℕ):ℂ)*w))/w^m))=(S-F)/w^m := by
    dsimp only [S,F]
    simp only [←mul_div_assoc,mul_sub,sum_div,sum_sub_distrib,sub_div]
  change taylorCoeffZero shiftedRegularGerm m+((∑ j∈P.support,P.coeff j*((squarefreeGridSample T (2^j)-
    shiftedRegularGerm (((2^j:ℕ):ℂ)*w))/w^m))+w*J)/Z=S/(Z*w^m)
  rw [he,hident,pow_succ]
  field_simp [hZ,hw]
  ring

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
