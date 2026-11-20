import GaloisForLFunctions.MultiplicativePositivityGeometry.ZetaBoundaryDivisor
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock
import GaloisForLFunctions.HTGeometry.ZeroEstimate
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Strict prime energy and its three-site equilibrium

At any fixed finite set of distinct times all sufficiently large primes separate
the phases. A Vandermonde test on the first prime powers makes the real zeta
Gram energy strictly positive. For three equally spaced sites the splitting
formula of Carrillo–Guimarães–Padilla-Garza–Shu (arXiv:2611.24677, Lemma 25)
then gives an exact energy gap with an explicit price for the middle site.
-/

noncomputable section
open Finset Complex Filter Topology
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- Beyond a single finite cutoff every prime separates all the sites. -/
theorem eventually_prime_clock_separates {m : ℕ} {x : Fin m → ℝ} (hx : Function.Injective x) :
    ∃ N : ℕ, ∀ p ≥ N, p.Prime → Function.Injective (fun i => HTGeometry.phaseClockValue (Real.log p) (x i)) := by
  classical
  let bad (a : Fin m × Fin m) (p : ℕ) : Prop :=
    p.Prime ∧ HTGeometry.phaseClockValue (Real.log p) (x a.1) =
      HTGeometry.phaseClockValue (Real.log p) (x a.2)
  let witness (a : Fin m × Fin m) := if h : ∃ p, bad a p then h.choose else 0
  refine ⟨univ.sup witness+1, fun p hcut hp i j he => ?_⟩
  by_contra hdist
  let a := (i,j)
  have hex : ∃ r, bad a r := ⟨p,hp,he⟩
  have hw : bad a (witness a) := by simp only [witness,dif_pos hex]; exact hex.choose_spec
  have hl : witness a ≤ univ.sup witness := Finset.le_sup (f := witness) (mem_univ a)
  have hne : p ≠ witness a := by omega
  exact hdist (hx ((RHTower.primeLogPhaseClockPair_injective hp hw.1 hne) (Prod.ext he hw.2)))

/-- Complex amplitude observed at the logarithmic frequency of n. -/
def primeSignal {m : ℕ} (x c : Fin m → ℝ) (n : ℕ) : ℂ :=
  ∑ i, (c i:ℂ)*HTGeometry.phaseClockValue (Real.log n) (x i)

private theorem signal_prime_power {m : ℕ} (x c : Fin m → ℝ) (p k : ℕ) :
    primeSignal x c (p^k) =
      ∑ i, (c i:ℂ)*(HTGeometry.phaseClockValue (Real.log p) (x i))^k := by
  apply sum_congr rfl
  intro i _
  unfold HTGeometry.phaseClockValue
  rw [Nat.cast_pow,Real.log_pow,← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- Every sufficiently large prime exhibits a nonzero signal among its first m
positive powers, for every nonzero choice of real amplitudes on m distinct sites. -/
theorem prime_power_detects_all_amplitudes {m : ℕ} {x : Fin m → ℝ} (hx : Function.Injective x) :
    ∃ N : ℕ, ∀ p ≥ N, p.Prime → ∀ c : Fin m → ℝ, c ≠ 0 →
      ∃ k : Fin m, (∑ i, (c i:ℂ)*HTGeometry.phaseClockValue (Real.log ((p^(k.val+1):ℕ):ℝ)) (x i)) ≠ 0 := by
  obtain ⟨N,hN⟩ := eventually_prime_clock_separates hx
  refine ⟨N,fun p hp hprime c hc => ?_⟩
  let z := fun i => HTGeometry.phaseClockValue (Real.log p) (x i)
  have hcz : (fun i => (c i:ℂ)*z i) ≠ 0 := by
    intro hz
    apply hc
    funext i
    have hi := congrFun hz i
    change (c i:ℂ)*z i=0 at hi
    exact_mod_cast (mul_eq_zero.mp hi).resolve_right (Complex.exp_ne_zero _)
  obtain ⟨k,hk⟩ := vandermonde_initial_moment_nonzero_of_nonzero_coeff (hN p hp hprime) hcz
  refine ⟨k,?_⟩
  change primeSignal x c (p^(k.val+1)) ≠ 0
  rw [signal_prime_power]
  convert hk using 1
  apply sum_congr rfl
  intro i _
  dsimp only [z]
  rw [pow_succ]
  ring

private theorem single_prime_energy {m : ℕ} (x c : Fin m → ℝ) (n : ℕ) :
    ∑ i, ∑ j, c i*c j*Real.cos (logFrequency n*(x i-x j)) = Complex.normSq (primeSignal x c n) := by
  rw [gram_cos_eq,Complex.normSq_apply]
  simp only [primeSignal,Complex.re_sum,Complex.im_sum,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,HTGeometry.phaseClockValue,
    Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,logFrequency,sq]

/-- The strict lower bound furnished by an individual prime-power observation. -/
theorem zeta_gram_ge_single_frequency {m : ℕ} (x c : Fin m → ℝ) {h : ℝ} (hh : 0<h) (n : ℕ) :
    zetaBoundaryWeight h n*Complex.normSq (primeSignal x c n) ≤
      ∑ i, ∑ j, c i*c j*zetaRealLogDeriv (1+h) (x i-x j) := by
  let w := zetaBoundaryWeight h
  have hs : HasSum (fun n => ∑ i, ∑ j, c i*c j*(w n*Real.cos (logFrequency n*(x i-x j))))
      (∑ i, ∑ j, c i*c j*zetaRealLogDeriv (1+h) (x i-x j)) := by
    simp_rw [zetaRealLogDeriv_eq_cosineTrace hh]
    exact hasSum_sum fun i _ => hasSum_sum fun j _ =>
      ((summable_cosineTrace_terms (zetaBoundaryWeight_nonneg h) (summable_zetaBoundaryWeight hh)
        logFrequency (x i-x j)).hasSum).mul_left _
  have he (n : ℕ) :
      (∑ i, ∑ j, c i*c j*(w n*Real.cos (logFrequency n*(x i-x j)))) =
      w n*Complex.normSq (primeSignal x c n) := by
    rw [← single_prime_energy,Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact sum_congr rfl fun j _ => by ring
  simp_rw [he] at hs
  rw [← hs.tsum_eq]
  exact hs.summable.le_tsum n (fun j _ => mul_nonneg (zetaBoundaryWeight_nonneg _ _) (Complex.normSq_nonneg _))

/-- Strict positive definiteness at every finite set of distinct sites. -/
theorem zeta_gram_strict {m : ℕ} {x c : Fin m → ℝ} (hx : Function.Injective x) (hc : c ≠ 0)
    {h : ℝ} (hh : 0<h) : 0 < ∑ i, ∑ j, c i*c j*zetaRealLogDeriv (1+h) (x i-x j) := by
  obtain ⟨N,hN⟩ := prime_power_detects_all_amplitudes hx
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes N
  obtain ⟨k,hk⟩ := hN p hp hprime c hc
  have hw : 0 < zetaBoundaryWeight h (p^(k.val+1)) := by
    rw [zetaBoundaryWeight,ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
      ArithmeticFunction.vonMangoldt_apply_prime hprime]
    exact mul_pos (Real.log_pos (by exact_mod_cast hprime.one_lt))
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (pow_pos hprime.pos _)) _)
  exact (mul_pos hw (Complex.normSq_pos.mpr hk)).trans_le (zeta_gram_ge_single_frequency x c hh _)

/-- Energy of masses a,b,c at times 0,t,2t. -/
def threeSiteEnergy (h t a b c : ℝ) : ℝ :=
  let f := zetaRealLogDeriv (1+h)
  f 0*(a^2+b^2+c^2)+2*f t*(a*b+b*c)+2*f (2*t)*a*c

private theorem grid_three_energy (h t a b c : ℝ) (hh : 0<h) :
    let x : Fin 3 → ℝ := ![0,t,2*t]
    let v : Fin 3 → ℝ := ![a,b,c]
    (∑ i, ∑ j, v i*v j*zetaRealLogDeriv (1+h) (x i-x j))=threeSiteEnergy h t a b c := by
  let f := zetaRealLogDeriv (1+h)
  have even (s : ℝ) : f (-s) = f s := by
    simp only [f,zetaRealLogDeriv_eq_cosineTrace hh,cosineTrace_neg]
  simp [Fin.sum_univ_succ,threeSiteEnergy,← show f = zetaRealLogDeriv (1+h) from rfl,
    show t-2*t= -t by ring,show 2*t-t=t by ring,even]
  ring

/-- Strict pair contrasts and the curvature in the symmetric three-site direction. -/
theorem three_site_contrasts_pos {h t : ℝ} (hh : 0<h) (ht : t ≠ 0) :
    let f := zetaRealLogDeriv (1+h)
    0<f 0-f t ∧ 0<f 0-f (2*t) ∧ 0<3*f 0-4*f t+f (2*t) := by
  let x : Fin 3 → ℝ := ![0,t,2*t]
  have hx : Function.Injective x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [x]
  have energy (a b c : ℝ) (ha : a ≠ 0) : 0 < threeSiteEnergy h t a b c := by
    rw [← grid_three_energy h t a b c hh]
    apply zeta_gram_strict hx _ hh
    intro he
    exact ha (congrFun he 0)
  have h1 := energy 1 (-1) 0 one_ne_zero
  have h2 := energy 1 0 (-1) one_ne_zero
  have h3 := energy 1 (-2) 1 one_ne_zero
  simp only [threeSiteEnergy] at h1 h2 h3
  dsimp only
  exact ⟨by linarith only [h1],by linarith only [h2],by linarith only [h3]⟩

/-- Fraction of the equilibrium mass carried by the middle site. -/
def equilibriumMiddle (h t : ℝ) : ℝ :=
  let f := zetaRealLogDeriv (1+h)
  max (f 0-2*f t+f (2*t)) 0/(3*f 0-4*f t+f (2*t))

theorem equilibriumMiddle_mem {h t : ℝ} (hh : 0<h) (ht : t ≠ 0) :
    equilibriumMiddle h t ∈ Set.Ico 0 1 := by
  obtain ⟨h1,_,hd⟩ := three_site_contrasts_pos hh ht
  refine ⟨div_nonneg (le_max_right _ _) hd.le,(div_lt_one hd).mpr ?_⟩
  exact max_lt (by linarith only [h1]) hd

/-- Exact splitting into two positive quadratic modes and the obstacle price.
The middle site is absent precisely when its discrete second difference is nonpositive. -/
theorem three_site_obstacle_split {h t : ℝ} (hh : 0<h) (ht : t ≠ 0) (a b c : ℝ) (hs : a+b+c=1) :
    let f := zetaRealLogDeriv (1+h)
    let v := equilibriumMiddle h t
    threeSiteEnergy h t a b c-threeSiteEnergy h t ((1-v)/2) v ((1-v)/2) =
      (f 0-f (2*t))/2*(a-c)^2 + (3*f 0-4*f t+f (2*t))/2*(b-v)^2 +
        max (-(f 0-2*f t+f (2*t))) 0*b := by
  intro f v
  let F := f 0-2*f t+f (2*t)
  let D := 3*f 0-4*f t+f (2*t)
  have hD : 0<D := (three_site_contrasts_pos hh ht).2.2
  have hE (a b c : ℝ) (hs : a+b+c=1) :
      threeSiteEnergy h t a b c = (f 0+f (2*t))/2-F*b+D/2*b^2+(f 0-f (2*t))/2*(a-c)^2 := by
    rw [show c=1-a-b by linarith only [hs]]
    dsimp [threeSiteEnergy,F,D,f]
    ring
  rw [hE _ _ _ hs,hE _ _ _ (by ring)]
  change _ = (f 0-f (2*t))/2*(a-c)^2+D/2*(b-v)^2+max (-F) 0*b
  rw [show v=max F 0/D from rfl]
  rcases le_total F 0 with hn | hn
  · rw [max_eq_right hn,max_eq_left (neg_nonneg.mpr hn),zero_div]
    ring
  · rw [max_eq_left hn,max_eq_right (neg_nonpos.mpr hn)]
    field_simp [hD.ne']
    ring

/-- The equilibrium is the unique minimizer. If the midpoint is excluded,
every unit of mass placed there pays the linear obstacle price as well. -/
theorem three_site_equilibrium {h t : ℝ} (hh : 0<h) (ht : t ≠ 0)
    (a b c : ℝ) (hb : 0≤b) (hs : a+b+c=1) :
    let v := equilibriumMiddle h t
    let e := threeSiteEnergy h t ((1-v)/2) v ((1-v)/2)
    e ≤ threeSiteEnergy h t a b c ∧
      (threeSiteEnergy h t a b c = e ↔ a=(1-v)/2 ∧ b=v ∧ c=(1-v)/2) := by
  intro v e
  let f := zetaRealLogDeriv (1+h)
  have hsplit := three_site_obstacle_split hh ht a b c hs
  obtain ⟨_,ha,hd⟩ := three_site_contrasts_pos hh ht
  let A := (f 0-f (2*t))/2
  let D := (3*f 0-4*f t+f (2*t))/2
  let F := -(f 0-2*f t+f (2*t))
  change threeSiteEnergy h t a b c-e=A*(a-c)^2+D*(b-v)^2+max F 0*b at hsplit
  have h₁ : 0<A := div_pos ha (by norm_num)
  have h₂ : 0<D := div_pos hd (by norm_num)
  have he₁ := mul_nonneg h₁.le (sq_nonneg (a-c))
  have he₂ := mul_nonneg h₂.le (sq_nonneg (b-v))
  have he₃ := mul_nonneg (le_max_right F 0) hb
  refine ⟨by linarith only [hsplit,he₁,he₂,he₃],?_,?_⟩
  · intro hz
    rw [hz,sub_self] at hsplit
    have hac : a=c := sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp
      (by linarith only [hsplit,he₁,he₂,he₃] : A*(a-c)^2=0)).resolve_left h₁.ne'))
    have hbv : b=v := sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp
      (by linarith only [hsplit,he₁,he₂,he₃] : D*(b-v)^2=0)).resolve_left h₂.ne'))
    exact ⟨by linarith only [hs,hac,hbv],hbv,by linarith only [hs,hac,hbv]⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

private def primeHeightLoss (h u : ℝ) := zetaRealLogDeriv (1+h) 0-zetaRealLogDeriv (1+h) u

private theorem height_loss_slope {h : ℝ} (hh : 0<h) :
    Filter.Tendsto (fun u => primeHeightLoss h u/u) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  let f := zetaRealLogDeriv (1+h)
  have hf : IsEvenPosDef f := by
    rw [show f=cosineTrace (zetaBoundaryWeight h) logFrequency from
      funext (zetaRealLogDeriv_eq_cosineTrace hh)]
    exact isEvenPosDef_cosineTrace (zetaBoundaryWeight_nonneg h) (summable_zetaBoundaryWeight hh) _
  have hm : IsLocalMax f 0 := Filter.Eventually.of_forall fun u => (le_abs_self _).trans (hf.abs_le_apply_zero u)
  let v := fun u : ℝ => ((1+h:ℝ):ℂ)+(u:ℂ)*I
  have hv : DifferentiableAt ℝ v 0 :=
    (differentiableAt_const _).add (Complex.differentiable_ofReal.differentiableAt.mul_const _)
  have hu : 1<(v 0).re := by simp [v]; linarith
  have hd := (RHTower.differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re hu).restrictScalars ℝ
  have hd' : DifferentiableAt ℝ f 0 := Complex.differentiable_re.differentiableAt.comp 0 (hd.comp 0 hv)
  have hder := hd'.hasDerivAt
  rw [hm.deriv_eq_zero] at hder
  have hg : HasDerivAt (primeHeightLoss h) 0 0 := by
    change HasDerivAt (fun u => f 0-f u) 0 0
    simpa only [neg_zero] using hder.const_sub (f 0)
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  simpa only [slope_fun_def_field,sub_zero,primeHeightLoss,sub_self] using hs

/-- Both obstacle regimes occur at each damping. Starting from any positive
scale, some dyadic enlargement puts positive mass on the middle site and
some dyadic contraction makes its obstacle price strictly positive. -/
theorem opposite_three_site_regimes {h : ℝ} (hh : 0<h) {t : ℝ} (ht : 0<t) :
    let f := zetaRealLogDeriv (1+h)
    (∃ k : ℕ, 0 < f 0-2*f (2^k*t)+f (2*(2^k*t))) ∧
    (∃ k : ℕ, f 0-2*f (((1/2:ℝ)^k)*t)+f (2*(((1/2:ℝ)^k)*t)) < 0) := by
  intro f
  let g := primeHeightLoss h
  have hpos : 0<g t := (three_site_contrasts_pos hh ht.ne').1
  let w := fun u => f 0-2*f u+f (2*u)
  have hgap (u : ℝ) : w u=2*g u-g (2*u) := by dsimp [w,g,primeHeightLoss,f]; ring
  change (∃ k : ℕ, 0<w (2^k*t)) ∧ (∃ k : ℕ, w (((1/2:ℝ)^k)*t)<0)
  constructor
  · by_contra! hsmall
    have hg (k : ℕ) : 2^k*g t≤g (2^k*t) := by
      induction k with
      | zero => simp
      | succ k ih =>
        have he := hsmall k
        rw [hgap] at he
        rw [pow_succ',mul_assoc,mul_assoc]
        linarith only [he,ih]
    have hf : IsEvenPosDef f := by
      rw [show f=cosineTrace (zetaBoundaryWeight h) logFrequency from
        funext (zetaRealLogDeriv_eq_cosineTrace hh)]
      exact isEvenPosDef_cosineTrace (zetaBoundaryWeight_nonneg h) (summable_zetaBoundaryWeight hh) _
    have hub (u : ℝ) : g u≤2*f 0 := by
      change f 0-f u≤2*f 0
      linarith only [(neg_le_abs (f u)).trans (hf.abs_le_apply_zero u)]
    have hlim : Filter.Tendsto (fun k : ℕ => (2:ℝ)^k*g t) Filter.atTop Filter.atTop :=
      (tendsto_mul_const_atTop_of_pos hpos).mpr (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    obtain ⟨k,hk⟩ := (hlim.eventually_gt_atTop (2*f 0)).exists
    exact (hg k).not_gt ((hub _).trans_lt hk)
  · by_contra! hnonneg
    let x := fun k : ℕ => (1/2:ℝ)^k*t
    have hx (k : ℕ) : 0<x k := mul_pos (pow_pos (by norm_num) _) ht
    have htwo (k : ℕ) : 2*x (k+1)=x k := by dsimp [x]; rw [pow_succ]; ring
    have hratio (k : ℕ) : g t/t≤g (x k)/(x k) := by
      induction k with
      | zero => simp [x]
      | succ k ih =>
        refine ih.trans ((div_le_div_iff₀ (hx _) (hx _)).mpr ?_)
        have he := hnonneg (k+1)
        change 0≤w (x (k+1)) at he
        rw [hgap,htwo] at he
        calc g (x k)*x (k+1) ≤ (2*g (x (k+1)))*x (k+1) :=
               mul_le_mul_of_nonneg_right (by linarith only [he]) (hx _).le
             _ = g (x (k+1))*x k := by rw [←htwo k]; ring
    have hx₀ : Filter.Tendsto x Filter.atTop (nhds 0) := by
      simpa only [x,zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).mul_const t
    have hx' : Filter.Tendsto x Filter.atTop (nhdsWithin 0 {0}ᶜ) :=
      tendsto_nhdsWithin_iff.mpr ⟨hx₀,Filter.Eventually.of_forall fun k => (hx k).ne'⟩
    exact (div_pos hpos ht).not_ge (ge_of_tendsto' ((height_loss_slope hh).comp hx') hratio)

#print axioms opposite_three_site_regimes

#print axioms eventually_prime_clock_separates
#print axioms prime_power_detects_all_amplitudes
#print axioms zeta_gram_strict
#print axioms three_site_obstacle_split
#print axioms three_site_equilibrium
end GaloisForLFunctions.MultiplicativePositivityGeometry
