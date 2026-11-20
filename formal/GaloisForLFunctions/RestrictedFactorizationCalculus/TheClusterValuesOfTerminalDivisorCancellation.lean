import GaloisForLFunctions.RestrictedFactorizationCalculus.TheRelativeCancellationOfTheTerminalDivisorRow
import GaloisForLFunctions.PrimeExponentialSums.DyadicPrimeSums
import GaloisForLFunctions.RHTower.ZetaZeroDensityExponentLemmas
import GaloisForLFunctions.RHTower.SpurRescale

/-!
# All limiting cancellation ratios below the square-root threshold

Choose a small subset of the primes between m² and 2m². With total
logarithm at most m/4 all these primes survive the wall attached to their
own product. Below half power their reciprocal weights can have arbitrarily
large sum although each individual weight tends to zero. Stopping a partial
product gives every relative cancellation ratio in the unit interval.
-/
noncomputable section
open Finset Filter
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev upper (m : ℕ) := 2*m^2
private abbrev band (m : ℕ) := (Ioc (m^2) (upper m)).filter Nat.Prime
private abbrev val (P : Finset ℕ) := ∏ p∈P,p
private abbrev prodRatio (u : ℝ) (P : Finset ℕ) := ∏ p∈P,terminalPrimeFactor u p

private theorem upper_grows : Tendsto (fun m : ℕ => (upper m:ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' _ ?_ (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  exact_mod_cast (show m ≤ 2*m^2 by nlinarith only [Nat.le_self_pow (by decide : 2≠0) m])

/-- A prescribed mass of reciprocal prime powers fits inside a squarefree
integer whose logarithm occupies at most one quarter of the prime scale m. -/
private theorem available_primes {u A : ℝ} (up : 0 < u) (half : u < 1/2) (ap : 0 < A) :
    ∀ᶠ m : ℕ in atTop,∃ P ⊆ band m,
      (P.card:ℝ)*Real.log (upper m) ≤ (m:ℝ)/4 ∧ A ≤ ∑ p∈P,(p:ℝ)^(-u) := by
  have price := upper_grows.eventually
    (_root_.RHTower.eventually_const_mul_polylog_le_rpow 1 (sub_pos.mpr half) (8*(A+1)))
  have many := (tendsto_pow_atTop (α:=ℕ) (by decide : 2 ≠ 0)).eventually
    GaloisForLFunctions.PrimeExponentialSums.eventually_card_primes_ge
  filter_upwards [price,many,eventually_ge_atTop (2:ℕ)] with m bound inventory hm
  let V := (upper m:ℝ)
  let k := ⌈A*V^u⌉₊
  have m1 : (1:ℝ) ≤ m := Nat.one_le_cast.mpr (by omega)
  have vr : V = 2*(m:ℝ)^2 := by dsimp only [V,upper];push_cast;ring
  have v1 : 1 < V := by nlinarith only [vr,m1,sq_nonneg ((m:ℝ)-1)]
  have vp := zero_lt_one.trans v1
  have weight := Real.one_le_rpow v1.le up.le
  have cap : (k:ℝ) ≤ (A+1)*V^u :=
    (Nat.ceil_lt_add_one (mul_nonneg ap.le (Real.rpow_nonneg vp.le u))).le.trans (by linarith only [weight])
  have lp := Real.log_pos v1
  have kcost : 4*(k:ℝ)*Real.log V ≤ m := by
    have prod := mul_le_mul cap (le_add_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num) :
      Real.log V ≤ 1+Real.log V) lp.le (by positivity)
    change 8*(A+1)*(1+Real.log V)^1 ≤ V^(1/2-u) at bound
    rw [pow_one] at bound
    have norm := mul_le_mul_of_nonneg_right bound (Real.rpow_nonneg vp.le u)
    rw [←Real.rpow_add vp,sub_add_cancel,←Real.sqrt_eq_rpow] at norm
    have rt : Real.sqrt V ≤ 2*(m:ℝ) := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [vr,sq_nonneg (m:ℝ)]⟩
    linarith only [prod,norm,rt]
  have m2 : 1 < (m^2:ℕ) := by nlinarith only [hm]
  have logp := Real.log_pos (show (1:ℝ) < (m^2:ℕ) by exact_mod_cast m2)
  have logmono := Real.log_le_log (by positivity : 0 < ((m^2:ℕ):ℝ))
    (Nat.cast_le.mpr (show m^2 ≤ upper m by unfold upper; omega) : ((m^2:ℕ):ℝ) ≤ V)
  have enough : k ≤ (band m).card := by
    have h₁ := mul_le_mul_of_nonneg_left logmono (show 0 ≤ 4*(k:ℝ) by positivity)
    have h₂ := (h₁.trans kcost).trans (Nat.cast_le.mpr (Nat.le_self_pow (by decide : 2≠0) m))
    change ((m^2:ℕ):ℝ) ≤ 4*Real.log (m^2:ℕ)*((band m).card:ℝ) at inventory
    exact_mod_cast (le_of_not_gt (fun lt' => by
      have bad := mul_lt_mul_of_pos_right lt' (show 0 < 4*Real.log (m^2:ℕ) by positivity)
      linarith only [bad,h₂,inventory]) : (k:ℝ) ≤ (band m).card)
  obtain ⟨P,sub,card⟩ := exists_subset_card_eq enough
  refine ⟨P,sub,by rw [card];linarith only [kcost],?_⟩
  have lower := card_nsmul_le_sum P (fun p : ℕ => (p:ℝ)^(-u)) (V^(-u)) (fun p hp =>
    Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr ((mem_filter.mp (sub hp)).2).pos)
      (Nat.cast_le.mpr (mem_Ioc.mp (mem_filter.mp (sub hp)).1).2) (neg_nonpos.mpr up.le))
  simp only [nsmul_eq_mul,card] at lower
  have unit := mul_le_mul_of_nonneg_right (Nat.le_ceil (A*V^u)) (Real.rpow_nonneg vp.le (-u))
  rw [mul_assoc,←Real.rpow_add vp,add_neg_cancel,Real.rpow_zero,mul_one] at unit
  exact unit.trans lower

private theorem members_survive {m : ℕ} (hm : 2 ≤ m) {P : Finset ℕ}
    (sub : P ⊆ band m) (room : (P.card:ℝ)*Real.log (upper m) ≤ (m:ℝ)/4) :
    (val P).primeFactors.filter (logSquareCutoff (val P) < ·)=P := by
  have prime (p : ℕ) (hp : p∈P) := (mem_filter.mp (sub hp)).2
  have np : 0 < val P := prod_pos (fun p hp => (prime p hp).pos)
  have atMost := sum_le_sum (fun p (hp : p∈P) => Real.log_le_log (Nat.cast_pos.mpr (prime p hp).pos)
    (Nat.cast_le.mpr (mem_Ioc.mp (mem_filter.mp (sub hp)).1).2))
  have sumLog : Real.log (val P) ≤ (P.card:ℝ)*Real.log (upper m) := by
    change Real.log ((∏ p∈P,p:ℕ):ℝ) ≤ _
    rw [Nat.cast_prod,Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (prime p hp).ne_zero)]
    simpa only [sum_const,nsmul_eq_mul] using atMost
  have one : 1 ≤ (val P:ℝ) := Nat.one_le_cast.mpr np
  have log1 := Real.log_le_log (by positivity : 0 < (val P:ℝ)+1)
    (show (val P:ℝ)+1 ≤ 2*val P by linarith only [one])
  rw [Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr np.ne')] at log1
  have log2 : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)).trans_eq (by norm_num)
  have low := Nat.floor_le_of_le (show Real.log ((val P:ℝ)+1) ≤ (m:ℝ) by
    linarith only [log2,log1,sumLog,room,(show (2:ℝ) ≤ m by exact_mod_cast hm)])
  have wall : logSquareCutoff (val P) ≤ m^2 := Nat.pow_le_pow_left low _
  rw [Nat.primeFactors_prod prime,filter_eq_self]
  exact fun p hp => wall.trans_lt (mem_Ioc.mp (mem_filter.mp (sub hp)).1).1

/-- Crossing a target by inserting one factor overshoots by at most the
largest individual loss. -/
private theorem stopping_product (P : Finset ℕ) (f : ℕ → ℝ) {δ t : ℝ}
    (dp : 0 ≤ δ) (t1 : t ≤ 1)
    (unit : ∀ p∈P,0 ≤ f p ∧ f p ≤ 1 ∧ 1-f p ≤ δ)
    (cross : ∏ p∈P,f p ≤ t) :
    ∃ S ⊆ P,t-δ ≤ ∏ p∈S,f p ∧ ∏ p∈S,f p ≤ t := by
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨∅,Subset.rfl,?_⟩
    simpa only [prod_empty] using And.intro (sub_le_self t dp |>.trans t1) cross
  | @insert p P hp ih =>
    have prior (q : ℕ) (hq : q∈P) := unit q (mem_insert_of_mem hq)
    by_cases already : ∏ q∈P,f q ≤ t
    · obtain ⟨S,sub,ends⟩ := ih prior already
      exact ⟨S,sub.trans (subset_insert ..),ends⟩
    · have pbd := unit p (mem_insert_self ..)
      have before := Finset.prod_le_one (fun _ hq => (prior _ hq).1) (fun _ hq => (prior _ hq).2.1)
      have small := mul_le_mul_of_nonneg_left before (sub_nonneg.mpr pbd.2.1)
      refine ⟨insert p P,Subset.rfl,?_,cross⟩
      rw [prod_insert hp]
      linarith only [small,pbd.2.2,lt_of_not_ge already]

private theorem full_product {P : Finset ℕ} {u : ℝ} (up : 0 < u) (prime : ∀ p∈P,1 ≤ p) :
    prodRatio u P ≤ Real.exp (-∑ p∈P,(p:ℝ)^(-u)) := by
  refine (prod_le_prod (fun p hp => (terminal_prime_factor_bounds up.le (prime p hp)).1) (fun p hp => ?_)).trans
    (_root_.RHTower.prod_one_sub_le_exp_neg_sum P (fun p => (p:ℝ)^(-u)) (fun p hp =>
      Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr (prime p hp)) (neg_nonpos.mpr up.le)))
  apply div_le_self
  · exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr (prime p hp)) (neg_nonpos.mpr up.le))
  · exact le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private theorem approximate_ratio {s t : ℝ} (up : 0 < |s|) (half : |s| < 1/2)
    (t0 : 0 ≤ t) (t1 : t ≤ 1) {ε : ℝ} (ep : 0 < ε) (N : ℕ) :
    ∃ n : ℕ,N ≤ n ∧ |terminalCancellationRatio (logSquareCutoff n) n s-t| < ε := by
  let δ := min (ε/4) (1/4)
  have dp : 0 < δ := lt_min (by positivity) (by norm_num)
  have dε : δ ≤ ε/4 := min_le_left .. 
  have d1 : δ ≤ 1/4 := min_le_right ..
  let w := (1-δ)*t+δ/2
  have dsmall : 0 ≤ 1-δ := by linarith only [d1]
  have wp : 0 < w := add_pos_of_nonneg_of_pos (mul_nonneg dsmall t0) (half_pos dp)
  have wb : w < 1 := by
    dsimp only [w]
    linarith only [mul_le_mul_of_nonneg_left t1 dsmall,dp]
  obtain ⟨A,expA,ap⟩ := ((Real.tendsto_exp_neg_atTop_nhds_zero.eventually_lt_const wp).and
    (eventually_gt_atTop (0:ℝ))).exists
  have tiny := (tendsto_rpow_neg_atTop up).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨m,⟨P,inside,room,mass⟩,small,large,mN⟩ := ((available_primes up half ap).and
    ((tiny.eventually_lt_const (half_pos dp)).and ((eventually_ge_atTop (2:ℕ)).and (eventually_ge_atTop N)))).exists
  have mpos : 0 < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  have sq : m ≤ m^2 := Nat.le_self_pow (by decide : 2≠0) m
  have prime (p : ℕ) (hp : p∈P) := (mem_filter.mp (inside hp)).2
  have cross := (full_product (P:=P) up (fun p hp => (prime p hp).pos)).trans
    ((Real.exp_le_exp.mpr (neg_le_neg mass)).trans expA.le)
  obtain ⟨S,sub,below,above⟩ := stopping_product P (terminalPrimeFactor |s|) dp.le wb.le (fun p hp => by
    obtain ⟨nn,le,loss⟩ := terminal_prime_factor_bounds up.le (prime p hp).pos
    have mp := sq.trans (mem_Ioc.mp (mem_filter.mp (inside hp)).1).1.le
    have one := Real.rpow_le_rpow_of_nonpos mpos (Nat.cast_le.mpr mp) (neg_nonpos.mpr up.le)
    refine ⟨nn,le,loss.trans ?_⟩
    change (m:ℝ)^(-|s|) < δ/2 at small
    linarith only [one,small]) cross
  have inhabited : S.Nonempty := by
    by_contra empty
    rw [Finset.not_nonempty_iff_eq_empty.mp empty,prod_empty] at above
    exact wb.not_ge above
  obtain ⟨p,hp⟩ := inhabited
  have np : 0 < val S := prod_pos fun q hq => (prime q (sub hq)).pos
  have pn : p ≤ val S := Nat.le_of_dvd np (dvd_prod_of_mem id hp)
  have nN := mN.trans (sq.trans ((mem_Ioc.mp (mem_filter.mp (inside (sub hp))).1).1.le.trans pn))
  have log0 := Real.log_nonneg (show 1 ≤ (upper m:ℝ) by exact_mod_cast
    (show 1 ≤ upper m by unfold upper;nlinarith only [sq,large]))
  have roomS := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card sub)) log0).trans room
  refine ⟨val S,nN,?_⟩
  rw [terminal_cancellation_euler_product _ np,members_survive large (sub.trans inside) roomS,abs_lt]
  dsimp only [w] at below above
  constructor <;> nlinarith only [below,above,dε,ep,mul_nonneg dp.le t0,mul_le_mul_of_nonneg_left t1 dp.le]

/-- For every nonzero weight exponent strictly below half in magnitude,
the subsequential limits of the cancellation ratio are the whole unit interval. -/
theorem terminal_cancellation_cluster_set {s : ℝ} (up : 0 < |s|) (half : |s| < 1/2) (t : ℝ) :
    (∃ n : ℕ → ℕ,Tendsto n atTop atTop ∧
      Tendsto (fun i => terminalCancellationRatio (logSquareCutoff (n i)) (n i) s) atTop (𝓝 t)) ↔
      t ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · rintro ⟨n,diverges,limit⟩
    have good : ∀ᶠ i : ℕ in atTop,terminalCancellationRatio (logSquareCutoff (n i)) (n i) s ∈ Set.Icc (0:ℝ) 1 := by
      filter_upwards [diverges.eventually_ge_atTop 1] with i hi
      rw [terminal_cancellation_euler_product _ hi]
      have base (p : ℕ) (hp : p ∈ (n i).primeFactors.filter (logSquareCutoff (n i) < ·)) :=
        terminal_prime_factor_bounds up.le (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos
      exact ⟨prod_nonneg (fun p hp => (base p hp).1),
        prod_le_one (fun p hp => (base p hp).1) (fun p hp => (base p hp).2.1)⟩
    exact isClosed_Icc.mem_of_tendsto limit good
  · rintro ⟨t0,t1⟩
    choose n hn near using fun i : ℕ => approximate_ratio up half t0 t1
      (show 0 < 1/((i:ℝ)+1) by positivity) i
    refine ⟨n,tendsto_atTop_mono hn tendsto_id,Metric.tendsto_nhds.mpr (fun ε ep => ?_)⟩
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually_lt_const ep] with i hi
    simpa only [Real.dist_eq] using (near i).trans hi

end GaloisForLFunctions.RestrictedFactorizationCalculus
