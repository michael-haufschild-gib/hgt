import GaloisForLFunctions.RHTower.Sieve.SecondDerivativeTest
import GaloisForLFunctions.RHTower.ArithmeticLogarithmicFourierTail
import GaloisForLFunctions.HTGeometry.SecondCenteredModularAbel
import GaloisForLFunctions.HTGeometry.DiscreteAbelRing

/-!
# Cancellation of the moving terminal modular mean

The literal reciprocal phase has a uniformly controlled second derivative
on every interval away from the small-modulus end. Its partial sums, and
then its modulus-weighted sums, are subquadratic on the square-root scale.
The absolutely summable Bernoulli Fourier series transfers this cancellation
to the complete terminal residue of the centered divisor hyperbola.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma reciprocal_phase_d1 (T x : ℝ) (hx : x≠0) :
    HasDerivAt (fun x : ℝ => T/x) (-T/x^(2 : ℕ)) x := by
  convert! (hasDerivAt_const x T).div (hasDerivAt_id x) hx using 1
  dsimp
  ring

private lemma reciprocal_phase_d2 (T x : ℝ) (hx : x≠0) :
    HasDerivAt (fun x : ℝ => -T/x^(2 : ℕ)) (2*T/x^(3 : ℕ)) x := by
  convert! (hasDerivAt_const x (-T)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx) using 1
  dsimp
  field_simp
  ring

/-- The second derivative test for a shifted reciprocal phase on a sharp integer interval. -/
theorem norm_reciprocal_phase_sum_le
    (T a B : ℝ) (N : ℕ) (hT : 0<T) (ha : 0<a)
    (hN : 1≤N) (hspan : a+(N-1:ℕ)≤B) (hlam : 2*T/B^(3 : ℕ)≤1) :
    ‖∑ n ∈ range N, Complex.exp (((2*Real.pi*(T/(a+n)):ℝ):ℂ)*Complex.I)‖ ≤
      8*N*(B/a)^(3 : ℕ)*Real.sqrt (2*T/B^(3 : ℕ))+12/Real.sqrt (2*T/B^(3 : ℕ)) := by
  have hB : 0<B := ha.trans_le (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) hspan)
  apply Sieve.second_derivative_test' (fun x => T/x) (fun x => -T/x^(2 : ℕ))
    (fun x => 2*T/x^(3 : ℕ)) a N hN (by positivity) hlam
  · intro x hx
    exact reciprocal_phase_d1 T x (ha.trans_le hx.1).ne'
  · intro x hx
    exact reciprocal_phase_d2 T x (ha.trans_le hx.1).ne'
  · intro x hx
    have hx0 : 0<x := ha.trans_le hx.1
    have hxB : x≤B := hx.2.trans hspan
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 3)
      (pow_le_pow_left₀ hx0.le hxB 3)
  · intro x hx
    have hx0 : 0<x := ha.trans_le hx.1
    have heq : (B/a)^(3 : ℕ)*(2*T/B^(3 : ℕ))=2*T/a^(3 : ℕ) := by field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos ha 3)
      (pow_le_pow_left₀ ha.le hx.1 3)

private lemma reciprocal_phase_window_uniform
    (h T : ℝ) (N k A b : ℕ) (hh : 1≤h) (hk : 1≤k) (hN : 1≤N)
    (hTlo : (N:ℝ)^(2 : ℕ)≤T) (hThi : T≤4*(N:ℝ)^(2 : ℕ)) (hlarge : 8*h≤N)
    (hA : A=N/k+1) (hab : A≤b) (hb : b≤N) :
    ‖∑ d ∈ Icc A b, Complex.exp (((2*Real.pi*(h*T/(d:ℝ)):ℝ):ℂ)*Complex.I)‖ ≤
      (24*(k:ℝ)^(3 : ℕ)*h+12)*Real.sqrt N := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ht : 0<T := (sq_pos_of_pos hn).trans_le hTlo
  have hApos : 0<A := by rw [hA]; exact Nat.zero_lt_succ _
  have ha : (0:ℝ)<A := by exact_mod_cast hApos
  have hak : (N:ℝ)≤(k:ℝ)*(A:ℝ) := by
    have he := Nat.div_add_mod N k
    have hm := Nat.mod_lt N (show 0<k by omega)
    have hnA : N≤k*A := by rw [hA]; nlinarith only [he,hm]
    exact_mod_cast hnA
  have hratio : (N:ℝ)/(A:ℝ)≤k := (div_le_iff₀ ha).mpr (by nlinarith only [hak])
  let lam := 2*(h*T)/(N:ℝ)^(3 : ℕ)
  have hl0 : 0<lam := by dsimp [lam]; positivity
  have hlN : 1≤lam*N ∧ lam*N≤8*h := by
    have heq : lam*(N:ℝ)=2*h*T/(N:ℝ)^(2 : ℕ) := by dsimp [lam]; field_simp
    rw [heq]
    constructor
    · rw [le_div_iff₀ (sq_pos_of_pos hn)]
      nlinarith only [hTlo,hh,mul_nonneg (sub_nonneg.mpr hh) ht.le]
    · rw [div_le_iff₀ (sq_pos_of_pos hn)]
      nlinarith only [mul_le_mul_of_nonneg_left hThi (by linarith : 0≤2*h)]
  have hl1 : lam≤1 := by nlinarith only [hlN.2,hlarge,hn]
  have htest := norm_reciprocal_phase_sum_le (h*T) (A:ℝ) (N:ℝ) (b+1-A)
    (by positivity) ha (by omega) (by
      have he : A+(b+1-A-1)=b := by omega
      exact_mod_cast (show A+(b+1-A-1)≤N by omega)) hl1
  have hsum : (∑ d ∈ Icc A b, Complex.exp (((2*Real.pi*(h*T/(d:ℝ)):ℝ):ℂ)*Complex.I)) =
      ∑ n ∈ range (b+1-A), Complex.exp (((2*Real.pi*(h*T/((A:ℝ)+n)):ℝ):ℂ)*Complex.I) := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp only [Nat.cast_add]
  rw [hsum]
  change _ ≤ 8*(b+1-A:ℕ)*((N:ℝ)/A)^(3 : ℕ)*Real.sqrt lam+12/Real.sqrt lam at htest
  have hsN := Real.sq_sqrt hn.le
  have hsL := Real.sq_sqrt hl0.le
  have hsN0 : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hsL0 : 0<Real.sqrt lam := Real.sqrt_pos.mpr hl0
  have hprod : 1≤Real.sqrt lam*Real.sqrt (N:ℝ) ∧
      Real.sqrt lam*Real.sqrt (N:ℝ)≤3*h := by
    have hs : (Real.sqrt lam*Real.sqrt (N:ℝ))^(2 : ℕ)=lam*N := by rw [mul_pow,hsN,hsL]
    constructor <;> nlinarith only [hs,hlN.1,hlN.2,hh,mul_pos hsL0 hsN0, sq_nonneg (h-1)]
  have hinv : 12/Real.sqrt lam≤12*Real.sqrt (N:ℝ) := by
    rw [div_le_iff₀ hsL0]
    nlinarith only [hprod.1]
  have hlen : ((b+1-A:ℕ):ℝ)≤N := by exact_mod_cast (show b+1-A≤N by omega)
  have hrat3 := pow_le_pow_left₀ (by positivity : 0≤(N:ℝ)/A) hratio 3
  have hlead : 8*(b+1-A:ℕ)*((N:ℝ)/A)^(3 : ℕ)*Real.sqrt lam ≤
      24*(k:ℝ)^(3 : ℕ)*h*Real.sqrt (N:ℝ) := by
    have h1 := mul_le_mul hlen hrat3 (by positivity) (Nat.cast_nonneg (α:=ℝ) N)
    have h2 := mul_le_mul_of_nonneg_right h1 hsL0.le
    have h3 := mul_le_mul_of_nonneg_right hprod.2 (by positivity : 0≤(k:ℝ)^(3 : ℕ)*Real.sqrt (N:ℝ))
    have he : Real.sqrt lam*Real.sqrt (N:ℝ)*((k:ℝ)^(3 : ℕ)*Real.sqrt (N:ℝ))=
        (N:ℝ)*(k:ℝ)^(3 : ℕ)*Real.sqrt lam := by
      calc
        _ = (Real.sqrt (N:ℝ))^(2 : ℕ)*(k:ℝ)^(3 : ℕ)*Real.sqrt lam := by ring
        _ = _ := by rw [hsN]
    rw [he] at h3
    linarith only [h2,h3]
  nlinarith only [htest,hlead,hinv]

private lemma norm_reciprocal_phase_prefix_le
    (h T : ℝ) (N k b : ℕ) (hh : 1≤h) (hk : 1≤k) (hN : 1≤N)
    (hTlo : (N:ℝ)^(2 : ℕ)≤T) (hThi : T≤4*(N:ℝ)^(2 : ℕ)) (hlarge : 8*h≤N) (hb : b≤N) :
    ‖∑ d ∈ Icc 1 b, Complex.exp (((2*Real.pi*(h*T/(d:ℝ)):ℝ):ℂ)*Complex.I)‖ ≤
      (N:ℝ)/(k:ℝ)+1+(24*(k:ℝ)^(3 : ℕ)*h+12)*Real.sqrt N := by
  let A := N/k+1
  let f := fun d : ℕ => Complex.exp (((2*Real.pi*(h*T/(d:ℝ)):ℝ):ℂ)*Complex.I)
  have hApos : 0<A := Nat.zero_lt_succ _
  have hnorm (s : Finset ℕ) : ‖∑ d ∈ s,f d‖ ≤ s.card := by
    calc
      _ ≤ ∑ d ∈ s, ‖f d‖ := norm_sum_le _ _
      _ = _ := by
        dsimp only [f]
        simp only [Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one]
  have hAupper : (A:ℝ)≤(N:ℝ)/(k:ℝ)+1 := by
    have hk0 : (0:ℝ)<k := by exact_mod_cast hk
    have hdiv : ((N/k:ℕ):ℝ)*(k:ℝ)≤N := by exact_mod_cast Nat.div_mul_le_self N k
    have h := (le_div_iff₀ hk0).mpr hdiv
    dsimp [A]
    push_cast
    linarith only [h]
  have hC : 0≤(24*(k:ℝ)^(3 : ℕ)*h+12)*Real.sqrt (N:ℝ) := by positivity
  change ‖∑ d ∈ Icc 1 b,f d‖≤_
  by_cases hab : A≤b
  · have htail := reciprocal_phase_window_uniform h T N k A b hh hk hN hTlo hThi hlarge rfl hab hb
    have hsplit : (∑ d ∈ Icc 1 b,f d)=(∑ d ∈ Ico 1 A,f d)+(∑ d ∈ Icc A b,f d) := by
      rw [← Ico_add_one_right_eq_Icc, ← Ico_add_one_right_eq_Icc]
      exact (sum_Ico_consecutive f (by omega) (by omega)).symm
    have hhead := hnorm (Ico 1 A)
    have hcard : ((Ico 1 A).card:ℝ)≤A := by
      exact_mod_cast (show (Ico 1 A).card≤A by simp)
    rw [hsplit]
    have htri := norm_add_le (∑ d ∈ Ico 1 A,f d) (∑ d ∈ Icc A b,f d)
    change ‖∑ d ∈ Icc A b,f d‖≤_ at htail
    linarith only [hhead,hcard,hAupper,htri,htail]
  · have hhead := hnorm (Icc 1 b)
    have hcard : ((Icc 1 b).card:ℝ)≤A := by
      exact_mod_cast (show (Icc 1 b).card≤A by simp; omega)
    linarith only [hhead,hcard,hAupper,hC]

private lemma norm_nat_weighted_sum_le (f : ℕ→ℂ) (N : ℕ) (hN : 1≤N)
    (H : ℝ) (hH : 0≤H) (hpre : ∀ b≤N,‖∑ d ∈ Icc 1 b,f d‖≤H) :
    ‖∑ d ∈ Icc 1 N,(d:ℂ)*f d‖≤3*(N:ℝ)*H := by
  have hid := HTGeometry.sum_mul_eq_partial_mul_diff_ring f (fun d => (d:ℂ)) N
  have hdiff (d : ℕ) : (d:ℂ)-(d+1:ℕ) = -1 := by push_cast; ring
  simp_rw [hdiff] at hid
  have hleft : (∑ d ∈ Icc 1 N,(d:ℂ)*f d)=(∑ d ∈ Icc 1 N,f d*(d:ℂ)) := by
    apply sum_congr rfl; intro d _; ring
  rw [hleft,hid]
  have hsum : ‖∑ d ∈ Icc 1 N,(∑ k ∈ Icc 1 d,f k)*(-1)‖≤(N:ℝ)*H := by
    calc
      _ ≤ ∑ d ∈ Icc 1 N,‖(∑ k ∈ Icc 1 d,f k)*(-1)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Icc 1 N,H := sum_le_sum (fun d hd => by simpa using hpre d (mem_Icc.mp hd).2)
      _ = _ := by simp
  have htail : ‖(∑ d ∈ Icc 1 N,f d)*(N+1:ℕ)‖≤H*((N:ℝ)+1) := by
    rw [norm_mul, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_right (hpre N le_rfl) (by positivity : (0:ℝ)≤N+1)
  have htri := norm_add_le (∑ d ∈ Icc 1 N,(∑ k ∈ Icc 1 d,f k)*(-1))
    ((∑ k ∈ Icc 1 N,f k)*(N+1:ℕ))
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  nlinarith only [hsum,htail,htri,mul_nonneg (sub_nonneg.mpr hn) hH]

/-- Quantitative reciprocal-phase estimate before choosing the moving split. -/
theorem norm_divisor_reciprocal_weighted_sum_le
    (h T : ℝ) (N k : ℕ) (hh : 1≤h) (hk : 1≤k) (hN : 1≤N)
    (hTlo : (N:ℝ)^(2 : ℕ)≤T) (hThi : T≤4*(N:ℝ)^(2 : ℕ)) (hlarge : 8*h≤N) :
    ‖∑ d ∈ Icc 1 N,(d:ℂ)*Complex.exp (((2*Real.pi*(h*T/(d:ℝ)):ℝ):ℂ)*Complex.I)‖ ≤
      3*(N:ℝ)*((N:ℝ)/(k:ℝ)+1+(24*(k:ℝ)^(3 : ℕ)*h+12)*Real.sqrt N) := by
  apply norm_nat_weighted_sum_le _ N hN _ (by positivity)
  exact fun b hb => norm_reciprocal_phase_prefix_le h T N k b hh hk hN hTlo hThi hlarge hb

private theorem eventually_reciprocal_weighted_sum_small (h : ℝ) (hh : 1≤h)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, (N:ℝ)^(2 : ℕ)≤T → T≤4*(N:ℝ)^(2 : ℕ) →
      ‖∑ d ∈ Icc 1 N,(d:ℂ)*Complex.exp (((2*Real.pi*(h*T/(d:ℝ)):ℝ):ℂ)*Complex.I)‖ ≤
        ε*(N:ℝ)^(2 : ℕ) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (6/ε)
  have hk0 : 0<k := by
    have hp : (0:ℝ)<6/ε := by positivity
    exact_mod_cast (hp.trans hk)
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  have hsmallk : 3/(k:ℝ)<ε/2 := by
    have h := (div_lt_iff₀ hε).mp hk
    rw [div_lt_iff₀ hkR]
    nlinarith only [h]
  let C : ℝ := 24*(k:ℝ)^(3 : ℕ)*h+12
  have hC : 0<C := by dsimp [C]; positivity
  have hrec : Tendsto (fun N : ℕ => 3/(N:ℝ)+3*C/Real.sqrt N) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => (Real.sqrt (N:ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [div_eq_mul_inv,mul_zero,zero_add] using (h1.const_mul 3).add (h2.const_mul (3*C))
  have hrecsmall := (tendsto_order.mp hrec).2 (ε/2) (by linarith only [hε])
  have hlarge : ∀ᶠ N : ℕ in atTop, 8*h≤(N:ℝ) :=
    (tendsto_atTop.mp tendsto_natCast_atTop_atTop) (8*h)
  filter_upwards [eventually_ge_atTop (1:ℕ),hlarge,hrecsmall] with N hN hNlarge hrem
  intro T hTlo hThi
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hs2 := Real.sq_sqrt hn.le
  have hquot : (N:ℝ)/Real.sqrt N=Real.sqrt N :=
    (div_eq_iff hs.ne').mpr (by nlinarith only [hs2])
  have hmul := mul_lt_mul_of_pos_right hrem hn
  have he : (3/(N:ℝ)+3*C/Real.sqrt N)*(N:ℝ)=3+3*C*Real.sqrt N := by
    calc
      _ = 3*((N:ℝ)/N)+3*C*((N:ℝ)/Real.sqrt N) := by ring
      _ = _ := by rw [div_self hn.ne',hquot]; ring
  rw [he] at hmul
  have hscaled := mul_le_mul_of_nonneg_right hmul.le hn.le
  have hkbound := mul_le_mul_of_nonneg_right hsmallk.le (sq_nonneg (N:ℝ))
  have hb := norm_divisor_reciprocal_weighted_sum_le h T N k hh hk0 hN hTlo hThi hNlarge
  change _≤3*(N:ℝ)*((N:ℝ)/(k:ℝ)+1+C*Real.sqrt N) at hb
  simp only [div_eq_mul_inv] at hb hkbound ⊢
  nlinarith only [hb,hscaled,hkbound]

private lemma nat_sqrt_tendsto : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b*b)] with M hM
  exact Nat.le_sqrt.mpr hM

private lemma sqrt_window {M : ℕ} (hM : 1≤M) :
    1≤Nat.sqrt M ∧ ((Nat.sqrt M:ℕ):ℝ)^(2 : ℕ)≤M ∧
      (M:ℝ)≤4*((Nat.sqrt M:ℕ):ℝ)^(2 : ℕ) := by
  have hN : 1≤Nat.sqrt M := Nat.le_sqrt.mpr (by simpa using hM)
  refine ⟨hN,?_,?_⟩
  · exact_mod_cast Nat.sqrt_le' M
  · have h := Nat.lt_succ_sqrt' M
    exact_mod_cast (show M≤4*(Nat.sqrt M)^(2 : ℕ) by nlinarith only [h,hN])

/-- Normalized Fourier mode of the literal modulus-weighted terminal source. -/
def divisorTerminalReciprocalMode (M : ℕ) (k : ℤ) : ℂ :=
  (∑ d ∈ Icc 1 (Nat.sqrt M),(d:ℂ)*fourier k (((M:ℝ)/(d:ℝ)):AddCircle (1:ℝ)))/(M:ℂ)

private lemma fourier_reciprocal_eq (M d : ℕ) (k : ℤ) :
    fourier k (((M:ℝ)/(d:ℝ)):AddCircle (1:ℝ))=
      Complex.exp (((2*Real.pi*((k:ℝ)*(M:ℝ)/(d:ℝ)):ℝ):ℂ)*Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

private lemma divisorTerminalReciprocalMode_tendsto_pos (k : ℤ) (hk : 0<k) :
    Tendsto (fun M => divisorTerminalReciprocalMode M k) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hsmall := nat_sqrt_tendsto.eventually
    (eventually_reciprocal_weighted_sum_small (k:ℝ) hkR (ε/2) (by positivity))
  have he : ∀ᶠ M : ℕ in atTop, dist (divisorTerminalReciprocalMode M k) 0<ε := by
    filter_upwards [eventually_ge_atTop (1:ℕ),hsmall] with M hM hMsmall
    obtain ⟨hN,hlo,hhi⟩ := sqrt_window hM
    have hb := hMsmall M hlo hhi
    have hpos : (0:ℝ)<M := by exact_mod_cast hM
    rw [dist_zero_right, divisorTerminalReciprocalMode, norm_div, Complex.norm_natCast]
    simp_rw [fourier_reciprocal_eq]
    rw [div_lt_iff₀ hpos]
    nlinarith only [hb,mul_le_mul_of_nonneg_left hlo (by positivity : 0≤ε/2),mul_pos hε hpos]
  exact eventually_atTop.mp he

/-- Negative terminal modes are exact conjugates. -/
lemma divisorTerminalReciprocalMode_neg (M : ℕ) (k : ℤ) :
    divisorTerminalReciprocalMode M (-k)=star (divisorTerminalReciprocalMode M k) := by
  simp only [divisorTerminalReciprocalMode, fourier_neg, star_div₀, star_sum, star_mul, star_natCast]
  congr 1
  apply sum_congr rfl
  intro d _
  exact mul_comm _ _

private lemma divisorTerminalReciprocalMode_tendsto {k : ℤ} (hk : k≠0) :
    Tendsto (fun M => divisorTerminalReciprocalMode M k) atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hk with hneg|hpos
  · have h := (divisorTerminalReciprocalMode_tendsto_pos (-k) (by omega)).star
    simpa only [divisorTerminalReciprocalMode_neg,star_star,star_zero] using h
  · exact divisorTerminalReciprocalMode_tendsto_pos k hpos

/-- All terminal modes have the same unconditional unit envelope. -/
lemma divisorTerminalReciprocalMode_norm_le (M : ℕ) (k : ℤ) :
    ‖divisorTerminalReciprocalMode M k‖≤1 := by
  by_cases hz : M=0
  · subst M; simp [divisorTerminalReciprocalMode]
  have hM : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hnorm : ‖∑ d ∈ Icc 1 (Nat.sqrt M),(d:ℂ)*fourier k (((M:ℝ)/(d:ℝ)):AddCircle (1:ℝ))‖≤
      ((Nat.sqrt M:ℕ):ℝ)^(2 : ℕ) := by
    calc
      _ ≤ ∑ d ∈ Icc 1 (Nat.sqrt M),‖(d:ℂ)*fourier k (((M:ℝ)/(d:ℝ)):AddCircle (1:ℝ))‖ := norm_sum_le _ _
      _ = ∑ d ∈ Icc 1 (Nat.sqrt M),(d:ℝ) := by
        simp only [norm_mul,Complex.norm_natCast,DeletionMixedRefinement.norm_fourier_real,mul_one]
      _ ≤ ∑ _ ∈ Icc 1 (Nat.sqrt M),((Nat.sqrt M:ℕ):ℝ) := by
        apply sum_le_sum
        intro d hd
        exact_mod_cast (mem_Icc.mp hd).2
      _ = _ := by simp; ring
  have hN : ((Nat.sqrt M:ℕ):ℝ)^(2 : ℕ)≤M := by exact_mod_cast Nat.sqrt_le' M
  rw [divisorTerminalReciprocalMode,norm_div,Complex.norm_natCast,div_le_one hM]
  exact hnorm.trans hN

/-- The absolutely admitted Fourier series retains the full signed terminal mean. -/
lemma hasSum_divisor_terminal_bernoulli_mean (M : ℕ) :
    HasSum (fun k : ℤ => (DeletionMixedRefinement.bernoulliModeWeight k:ℂ)*divisorTerminalReciprocalMode M k)
      (((∑ d ∈ Icc 1 (Nat.sqrt M),(d:ℝ)*(bernoulliPeriodic ((M:ℝ)/(d:ℝ))+1/12))/(M:ℝ) : ℝ) : ℂ) := by
  have hs := hasSum_sum (s:=Icc 1 (Nat.sqrt M)) (fun d _ =>
    (DeletionMixedRefinement.hasSum_bernoulliModeWeight_fourier ((M:ℝ)/(d:ℝ))).mul_left (d:ℂ))
  have h := hs.mul_right ((M:ℂ)⁻¹)
  have hf (k : ℤ) : (DeletionMixedRefinement.bernoulliModeWeight k:ℂ)*divisorTerminalReciprocalMode M k =
      (∑ d ∈ Icc 1 (Nat.sqrt M),(d:ℂ)*((DeletionMixedRefinement.bernoulliModeWeight k:ℂ)*
        fourier k (((M:ℝ)/(d:ℝ)):AddCircle (1:ℝ))))*(M:ℂ)⁻¹ := by
    simp only [divisorTerminalReciprocalMode,div_eq_mul_inv,← mul_assoc,mul_sum]
    congr 1
    apply sum_congr rfl
    intro d _
    ring
  have hv : (((∑ d ∈ Icc 1 (Nat.sqrt M),(d:ℝ)*(bernoulliPeriodic ((M:ℝ)/(d:ℝ))+1/12))/(M:ℝ) : ℝ) : ℂ) =
      (∑ d ∈ Icc 1 (Nat.sqrt M),(d:ℂ)*((bernoulliPeriodic ((M:ℝ)/(d:ℝ))+1/12:ℝ):ℂ))*(M:ℂ)⁻¹ := by
    push_cast
    ring
  simp_rw [hf]
  rw [hv]
  exact h

/-- The complete modulus-weighted reciprocal Bernoulli mean is sublinear in the cutoff. -/
theorem tendsto_terminal_reciprocal_bernoulli_mean :
    Tendsto (fun M : ℕ =>
      (∑ d ∈ Icc 1 (Nat.sqrt M),(d:ℝ)*(bernoulliPeriodic ((M:ℝ)/(d:ℝ))+1/12))/(M:ℝ))
      atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f:=fun M k => (DeletionMixedRefinement.bernoulliModeWeight k:ℂ)*divisorTerminalReciprocalMode M k)
    (g:=fun _ : ℤ => (0:ℂ)) DeletionMixedRefinement.hasSum_bernoulliModeWeight.summable
    (fun k => by
      by_cases hk : k=0
      · subst k
        simpa only [DeletionMixedRefinement.bernoulliModeWeight_zero,Complex.ofReal_zero,zero_mul]
          using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))
      · simpa only [mul_zero] using (divisorTerminalReciprocalMode_tendsto hk).const_mul
          (DeletionMixedRefinement.bernoulliModeWeight k:ℂ))
    (Eventually.of_forall (fun M k => by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (DeletionMixedRefinement.bernoulliModeWeight_nonneg k)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (divisorTerminalReciprocalMode_norm_le M k)
        (DeletionMixedRefinement.bernoulliModeWeight_nonneg k)))
  simp_rw [(hasSum_divisor_terminal_bernoulli_mean _).tsum_eq] at h
  have hre := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa only [tsum_zero,Complex.zero_re,Complex.ofReal_re,Function.comp_def] using hre

private lemma terminal_reciprocal_correction_tendsto :
    Tendsto (fun M : ℕ => (∑ d ∈ Icc 1 (Nat.sqrt M),1/(d:ℝ))/(M:ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun M : ℕ => 1/((Nat.sqrt M:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp nat_sqrt_tendsto)
  apply squeeze_zero' (Eventually.of_forall (fun M => by positivity)) _ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
  obtain ⟨hN,hNsq,_⟩ := sqrt_window hM
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have hn : (0:ℝ)<Nat.sqrt M := by exact_mod_cast hN
  have hsum : (∑ d ∈ Icc 1 (Nat.sqrt M),1/(d:ℝ))≤Nat.sqrt M := by
    calc
      _ ≤ ∑ _ ∈ Icc 1 (Nat.sqrt M),(1:ℝ) := by
        apply sum_le_sum
        intro d hd
        have hdR : (1:ℝ)≤d := by exact_mod_cast (mem_Icc.mp hd).1
        simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hdR
      _ = _ := by simp
  have hfirst := div_le_div_of_nonneg_right hsum hm.le
  have hsecond : ((Nat.sqrt M:ℕ):ℝ)/(M:ℝ)≤1/((Nat.sqrt M:ℕ):ℝ) := by
    rw [div_le_div_iff₀ hm hn]
    nlinarith only [hNsq]
  exact hfirst.trans hsecond

private lemma terminal_modular_bernoulli_identity (M d : ℕ) :
    HTGeometry.centeredModularMeanMagnitude d+HTGeometry.centeredModularPrimitive d M =
      (d:ℝ)*(bernoulliPeriodic ((M:ℝ)/(d:ℝ))+1/12)-1/(12*(d:ℝ)) := by
  by_cases hd : d=0
  · subst d
    simp [HTGeometry.centeredModularMeanMagnitude,HTGeometry.centeredModularPrimitive,bernoulliPeriodic]
  unfold HTGeometry.centeredModularMeanMagnitude HTGeometry.centeredModularPrimitive bernoulliPeriodic
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hdr : (d:ℝ)≠0 := by exact_mod_cast hd
  field_simp
  ring

/-- Signed cancellation removes the leading terminal residue of the actual modular primitives. -/
theorem tendsto_terminal_modular_mean :
    Tendsto (fun M : ℕ => (∑ d ∈ Icc 1 (Nat.sqrt M),
      (HTGeometry.centeredModularMeanMagnitude d+HTGeometry.centeredModularPrimitive d M))/(M:ℝ))
      atTop (𝓝 0) := by
  have h := tendsto_terminal_reciprocal_bernoulli_mean.sub
    (terminal_reciprocal_correction_tendsto.div_const 12)
  convert h using 1
  · ext M
    simp_rw [terminal_modular_bernoulli_identity]
    rw [sum_sub_distrib]
    simp_rw [show ∀ d : ℕ,1/(12*(d:ℝ))=(1/(d:ℝ))/12 by intro d; ring]
    rw [← sum_div]
    ring
  · norm_num

end RHTower
