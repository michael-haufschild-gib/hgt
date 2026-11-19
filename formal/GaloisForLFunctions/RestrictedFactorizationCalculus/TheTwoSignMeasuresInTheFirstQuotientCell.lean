import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCommonMainTermOfBothRoughSignCounts
import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeReadingsBeyondTheHyperbola
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMobiusSignAndEvenDilationMeans
import GaloisForLFunctions.RHTower.RobinLcmCriterion
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The distribution of both rough signs in the first quotient cell

Finite Euler deletion controls the discrepancy of each sign on every
subinterval of the cofactor coordinate. On the first cell inversion of
that coordinate gives the density du/(2u²) in the quotient coordinate.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical Topology ArithmeticFunction.Moebius
namespace GaloisForLFunctions.RestrictedFactorizationCalculus
open private sign_count_split from
  GaloisForLFunctions.BezoutValuationIncidence.CoprimeMobiusSignAndEvenDilationMeans

private abbrev density (y : ℕ) := coprimeSquarefreeDensity (primorial y)
private abbrev y (X : ℕ) := logSquareCutoff X
private abbrev Z (X : ℕ) := (X:ℝ)/(y X:ℝ)
private abbrev rankAt (b : Bool) (X N : ℕ) := (coprimeMoebiusSignCount (primorial (y X)) N b:ℝ)
private abbrev denom (X : ℕ) := Z X*density (y X)
private abbrev exponent := (7/8:ℝ)

private theorem density_lower (n : ℕ) : density 0 ≤ density n*((n:ℝ)+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let p := n+1
    have p0 : (0:ℝ)<p := Nat.cast_pos.mpr (Nat.succ_pos _)
    have step : density 0 ≤ density n*(p:ℝ) := by simpa only [p,Nat.cast_add_one] using ih
    rw [show n+1=p from rfl]
    by_cases prime : p.Prime
    · have nd : ¬p ∣ primorial n := fun h => (Nat.not_succ_le_self n) (prime.dvd_primorial_iff.mp h)
      have prod : primorial p=p*primorial n := by
        rw [RHTower.DeletionResidueMartingale.primorial_succ_eq,if_pos prime]
      change _ ≤ coprimeSquarefreeDensity (primorial p)*_
      rw [prod,coprimeSquarefreeDensity_prime_mul prime nd (primorial_ne_zero n)]
      exact step.trans_eq (by field_simp)
    · have eq : primorial p=primorial n := by
        rw [RHTower.DeletionResidueMartingale.primorial_succ_eq,if_neg prime]
      change _ ≤ coprimeSquarefreeDensity (primorial p)*_
      rw [eq]
      exact step.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (coprimeSquarefreeDensity_pos _).le)

/-- Both signs have a uniform frozen-prefix discrepancy up to the
real endpoint. The same Euler product controls the signed and unsigned parts. -/
private theorem each_frozen_sign :
    ∃ C : ℝ,0<C ∧ ∀ (b : Bool) (w : ℕ) (t : ℝ),0 ≤ t →
      |(coprimeMoebiusSignCount (primorial w) ⌊t⌋₊ b:ℝ)-density w*t/2| ≤
        C*deletionPrice exponent w*t^exponent := by
  have strip : RHTower.zetaZeroAbscissa<exponent :=
    ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths.trans_lt (by norm_num [exponent])
  obtain ⟨K,kn,bd⟩ := exists_moebius_power_bound_of_abscissa_lt strip
  have sp : 0<exponent := by norm_num [exponent]
  have full (n : ℕ) : |coprimeMoebiusSum 1 n| ≤ K*(n:ℝ)^exponent := by
    rcases Nat.eq_zero_or_pos n with rfl | np
    · simp [coprimeMoebiusSum,Real.zero_rpow sp.ne']
    simpa [coprimeMoebiusSum,coprimeMoebiusIndicator,moebiusReal] using bd n np
  refine ⟨2+K,by linarith only [kn],?_⟩
  intro b w t tp
  let E := deletionPrice exponent w
  have ep : 0 ≤ E := zero_le_one.trans (deletionPrice_one_le sp w)
  have u := primorial_squarefree_discrepancy (s := exponent) (by norm_num [exponent]) (by norm_num [exponent]) w t tp
  have f := all_frozen_rows_from_full_prefix sp kn full ⌊t⌋₊ w
  have floor := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le tp) sp.le
  have v := f.trans (mul_le_mul_of_nonneg_left floor (mul_nonneg (by positivity : 0 ≤ 2*K) ep))
  let Q := coprimeSquarefreeCount (primorial w) ⌊t⌋₊
  let M := coprimeMoebiusSum (primorial w) ⌊t⌋₊
  change |Q-density w*t| ≤ 4*E*t^exponent at u
  change |M| ≤ 2*K*E*t^exponent at v
  rw [sign_count_split]
  cases b
  · simp only [Bool.false_eq_true,if_false,neg_one_mul]
    change |(Q+ -M)/2-density w*t/2| ≤ _
    rw [show (Q+ -M)/2-density w*t/2=((Q-density w*t)-M)/2 by ring,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [u,v,abs_sub (Q-density w*t) M]
  · simp only [if_true,one_mul]
    change |(Q+M)/2-density w*t/2| ≤ _
    rw [show (Q+M)/2-density w*t/2=((Q-density w*t)+M)/2 by ring,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [u,v,abs_add_le (Q-density w*t) M]

private theorem uniform_cofactor_discrepancy {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ X : ℕ in atTop,∀ (t : ℝ),0 ≤ t → t ≤ Z X → ∀ b,
      |rankAt b X ⌊t⌋₊-density (y X)*t/2| ≤ ε*denom X := by
  obtain ⟨C,cp,estimate⟩ := each_frozen_sign
  let d := density 0
  have dp : 0<d := coprimeSquarefreeDensity_pos _
  let q := (1/32:ℝ)
  have qp : 0<q := by norm_num [q]
  have growing := (tendsto_rpow_atTop (show (0:ℝ)<1/16 by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [log_square_deletion_cost (s := exponent) (by norm_num [exponent]) qp,
    logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,growing.eventually_ge_atTop (C/(ε*d)),
    eventually_ge_atTop (1:ℕ)] with X cutoff yp grow xp
  let w := y X
  let E := deletionPrice exponent w
  let x := (X:ℝ)
  have x0 : 0<x := Nat.cast_pos.mpr xp
  have wp : 0<(w:ℝ) := Nat.cast_pos.mpr yp
  have ep1 : 1 ≤ E := deletionPrice_one_le (by norm_num [exponent]) w
  have ed := zero_lt_one.trans_le ep1
  have budget : ((w:ℝ)+1)*E ≤ x^q :=
    (mul_le_mul_of_nonneg_left (by nlinarith only [ep1,sq_nonneg (E-1)] : E ≤ E^2) (by positivity)).trans cutoff
  have wle : (w:ℝ) ≤ x^q := (le_add_of_nonneg_right zero_le_one).trans
    ((le_mul_of_one_le_right (by positivity : 0 ≤ (w:ℝ)+1) ep1).trans budget)
  have w1 : 1 ≤ (w:ℝ) := Nat.one_le_cast.mpr yp
  have fac : (w:ℝ)^(1-exponent) ≤ x^q := by
    apply le_trans _ wle
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le w1
      (show 1-exponent ≤ 1 by norm_num [exponent])
  have sq := mul_le_mul budget fac (Real.rpow_nonneg wp.le _) (Real.rpow_nonneg x0.le q)
  have fees := mul_le_mul_of_nonneg_right sq (Real.rpow_nonneg x0.le exponent)
  rw [←Real.rpow_add x0,←Real.rpow_add x0] at fees
  change _ ≤ x^(q+q+exponent) at fees
  have exponent_sum : q+q+exponent=1-1/16 := by norm_num [q,exponent]
  rw [exponent_sum,Real.rpow_sub x0,Real.rpow_one] at fees
  have all := mul_le_mul_of_nonneg_left fees cp.le
  have c : C ≤ ε*d*x^(1/16:ℝ) := by
    change C/(ε*d) ≤ x^(1/16:ℝ) at grow
    exact ((div_le_iff₀ (mul_pos ep dp)).mp grow).trans_eq (mul_comm ..)
  have fre : C*(x/x^(1/16:ℝ)) ≤ ε*d*x := by
    rw [←mul_div_assoc,div_le_iff₀ (Real.rpow_pos_of_pos x0 _)]
    linarith only [mul_le_mul_of_nonneg_right c x0.le]
  have densityBound : d ≤ density w*((w:ℝ)+1) := density_lower _
  intro t t0 tz b
  have cash := (estimate b w t t0).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow t0 tz
    (by norm_num [exponent])) (mul_nonneg cp.le ed.le))
  apply cash.trans
  have pscale : 0<((w:ℝ)+1)*(w:ℝ) := mul_pos (by positivity) wp
  apply le_of_mul_le_mul_right (a := ((w:ℝ)+1)*(w:ℝ)) _ pscale
  have fraction : (x/(w:ℝ))^exponent*w=x^exponent*(w:ℝ)^(1-exponent) := by
    rw [Real.div_rpow x0.le wp.le,Real.rpow_sub wp,Real.rpow_one]; ring
  change C*E*(x/(w:ℝ))^exponent*(((w:ℝ)+1)*w) ≤ ε*(x/(w:ℝ)*density w)*(((w:ℝ)+1)*w)
  calc _ = C*((((w:ℝ)+1)*E*(w:ℝ)^(1-exponent))*x^exponent) := by linear_combination C*E*((w:ℝ)+1)*fraction
       _ ≤ ε*d*x := all.trans fre
       _ ≤ ε*(x/(w:ℝ)*density w)*(((w:ℝ)+1)*w) := by
        have h := mul_le_mul_of_nonneg_left densityBound (mul_nonneg ep.le x0.le)
        calc _ ≤ (ε*x)*(density w*((w:ℝ)+1)) := by linarith only [h]
             _ = _ := by field_simp [wp.ne']

private theorem cofactor_scale_grows : Tendsto Z atTop atTop := by
  have rt := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop_mono' atTop _ rt
  filter_upwards [log_square_deletion_cost (s := 1) (by norm_num) (by norm_num : (0:ℝ)<1/2),
    logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1] with X paid yp
  let E := deletionPrice 1 (y X)
  have E1 : 1 ≤ E^2 := one_le_pow₀ (deletionPrice_one_le zero_lt_one _)
  have upper := (le_mul_of_one_le_right (by positivity : 0 ≤ (y X:ℝ)+1) E1).trans paid
  rw [←Real.sqrt_eq_rpow] at upper
  apply (le_div_iff₀ (Nat.cast_pos.mpr yp : (0:ℝ)<y X)).mpr
  exact (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right zero_le_one).trans upper) (Real.sqrt_nonneg _)).trans_eq
    (Real.mul_self_sqrt (Nat.cast_nonneg _))

private def mark (b : Bool) (X n : ℕ) : ℝ :=
  if (primorial (y X)).Coprime n ∧ μ n=(if b then (1:ℤ) else -1) then 1 else 0

private theorem mark_nonneg (b : Bool) (X n : ℕ) : 0 ≤ mark b X n := by
  by_cases h : (primorial (y X)).Coprime n ∧ μ n = (if b then (1:ℤ) else -1)
  · simp [mark,h]
  · simp [mark,h]

private theorem rank_step (b : Bool) (X k : ℕ) :
    rankAt b X (k+1)=rankAt b X k+mark b X (k+1) := by
  have expand (k : ℕ) : rankAt b X k=∑ n ∈ Icc 1 k,mark b X n := by
    simp [mark,coprimeMoebiusSignCount,rankAt]
  rw [expand,expand,sum_Icc_succ_top (Nat.succ_pos _)]

private theorem sum_mark (b : Bool) (X A B : ℕ) (order : A ≤ B) :
    (∑ n ∈ Ioc A B,mark b X n)=rankAt b X B-rankAt b X A := by
  induction B,order using Nat.le_induction with
  | base => simp
  | succ B h ih => rw [sum_Ioc_succ_top h,rank_step,ih]; ring

private abbrev atFraction (t : ℝ) (X : ℕ) := ⌊t*Z X⌋₊
private abbrev cell (a b : ℝ) (X : ℕ) := Ioc (atFraction a X) (atFraction b X)
private abbrev signedMass (b : Bool) (X : ℕ) (S : Finset ℕ) (f : ℕ → ℝ) := ∑ n ∈ S,mark b X n*f n

private theorem denominator_pos {X : ℕ} (xp : 0<X) (yp : 0<y X) : 0<denom X :=
  mul_pos (div_pos (Nat.cast_pos.mpr xp) (Nat.cast_pos.mpr yp)) (coprimeSquarefreeDensity_pos _)

private theorem rank_at_fraction (b : Bool) {r : ℝ} (lo : 0 ≤ r) (hi : r ≤ 1) :
    Tendsto (fun X => rankAt b X (atFraction r X)/denom X) atTop (𝓝 (r/2)) := by
  rw [Metric.tendsto_nhds]
  intro ε ep
  filter_upwards [uniform_cofactor_discrepancy (half_pos ep),logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1:ℕ)] with X cost yp xp
  have dz := denominator_pos xp yp
  have zp : 0<Z X := div_pos (Nat.cast_pos.mpr xp) (Nat.cast_pos.mpr yp)
  have h := cost (r*Z X) (mul_nonneg lo zp.le) ((mul_le_mul_of_nonneg_right hi zp.le).trans_eq (one_mul _)) b
  change dist (rankAt b X (atFraction r X)/denom X) (r/2)<ε
  -- Normalize the centered rank by the density of the entire cofactor interval.
  have eq : rankAt b X (atFraction r X)/denom X-r/2=
      (rankAt b X (atFraction r X)-density (y X)*(r*Z X)/2)/denom X := by
    have normalize (s z d : ℝ) (hz : z ≠ 0) (hd : d ≠ 0) :
        s/(z*d)-r/2=(s-d*(r*z)/2)/(z*d) := by field_simp [hz,hd]
    exact normalize _ _ _ zp.ne' (coprimeSquarefreeDensity_pos _).ne'
  rw [Real.dist_eq,eq,abs_div,abs_of_pos dz,div_lt_iff₀ dz]
  exact h.trans_lt (mul_lt_mul_of_pos_right (half_lt_self ep) dz)

/-- Each rough sign has density one half in the physical cofactor coordinate,
uniformly on every fixed subinterval of the first quotient cell. -/
theorem sign_mass_on_a_terminal_cofactor_interval (b : Bool) {a v : ℝ} (a0 : 0 ≤ a) (av : a ≤ v) (v1 : v ≤ 1) :
    Tendsto (fun X => signedMass b X (cell a v X) (fun _ => 1)/denom X) atTop (𝓝 ((v-a)/2)) := by
  have h := (rank_at_fraction b (a0.trans av) v1).sub (rank_at_fraction b a0 (av.trans v1))
  rw [←sub_div] at h
  apply h.congr
  intro X
  have zp : 0 ≤ Z X := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  simp only [signedMass,mul_one,cell,sum_mark _ _ _ _ (Nat.floor_mono (mul_le_mul_of_nonneg_right av zp)),sub_div]

/-- Normalized mass of a specified rough squarefree sign when m/(X/y)
lies in (a,v]. The denominator is (X/y) times the frozen local density. -/
def normalizedFirstCellSignMass (b : Bool) (a v : ℝ) (X : ℕ) :=
  signedMass b X (cell a v X) (fun _ => 1)/denom X

/-- In the quotient coordinate u=X/(my), the mass of [u,v) is the
integral of 1/(2u²) over that interval for each sign. -/
theorem sign_measure_in_the_first_quotient_cell (b : Bool) {u v : ℝ} (hu : 1 ≤ u) (uv : u ≤ v) (hv : v ≤ 2) :
    Tendsto (normalizedFirstCellSignMass b (1/v) (1/u))
      atTop (𝓝 ((1/u-1/v)/2)) :=
  sign_mass_on_a_terminal_cofactor_interval b (one_div_nonneg.mpr (zero_le_one.trans (hu.trans uv)))
    (one_div_le_one_div_of_le (zero_lt_one.trans_le hu) uv) ((div_le_one (zero_lt_one.trans_le hu)).mpr hu)

/-- Discrete partial summation, retaining both endpoints. -/
private theorem sum_increments (F g : ℕ → ℝ) {A B : ℕ} (order : A ≤ B) :
    (∑ n ∈ Ioc A B,(F n-F (n-1))*g n)=F B*g B-F A*g A+∑ n ∈ Ico A B,F n*(g n-g (n+1)) := by
  induction B,order using Nat.le_induction with
  | base => simp
  | succ B h ih => rw [sum_Ioc_succ_top h,sum_Ico_succ_top h,ih,Nat.add_sub_cancel]; ring

private theorem decreasing_test_error (F g : ℕ → ℝ) {A B : ℕ} (order : A ≤ B) {D : ℝ}
    (bounded : ∀ k ∈ Icc A B,|F k| ≤ D) (nn : ∀ k ∈ Icc A B,0 ≤ g k)
    (decr : ∀ k ∈ Ico A B,g (k+1) ≤ g k) :
    |∑ n ∈ Ioc A B,(F n-F (n-1))*g n| ≤ 2*D*g A := by
  have mA := mem_Icc.mpr ⟨le_rfl,order⟩
  have mB := mem_Icc.mpr ⟨order,le_rfl⟩
  have t (n : ℕ) (h : n∈Icc A B) : |F n*g n| ≤ D*g n := by
    rw [abs_mul,abs_of_nonneg (nn n h)]
    exact mul_le_mul_of_nonneg_right (bounded n h) (nn n h)
  have variation : (∑ n ∈ Ico A B,(g n-g (n+1)))=g A-g B := by
    clear t mA mB decr nn bounded
    induction B,order using Nat.le_induction with
    | base => simp
    | succ B h ih => rw [sum_Ico_succ_top h,ih]; ring
  have inc : |∑ n ∈ Ico A B,F n*(g n-g (n+1))| ≤ D*(g A-g B) := by
    apply (abs_sum_le_sum_abs ..).trans
    rw [←variation,mul_sum]
    apply sum_le_sum
    intro n hn
    have good := sub_nonneg.mpr (decr n hn)
    rw [abs_mul,abs_of_nonneg good]
    exact mul_le_mul_of_nonneg_right (bounded _ (mem_Icc.mpr ⟨(mem_Ico.mp hn).1,(mem_Ico.mp hn).2.le⟩)) good
  rw [sum_increments _ _ order]
  exact (abs_add_le ..).trans (by linarith only [abs_sub (F B*g B) (F A*g A),inc,t A mA,t B mB])

private theorem harmonic_window {a v : ℝ} (ap : 0<a) (av : a ≤ v) :
    Tendsto (fun X => ∑ n ∈ cell a v X,((n:ℝ)⁻¹)) atTop (𝓝 (Real.log (v/a))) := by
  have cut (r : ℝ) (rp : 0<r) : Tendsto (atFraction r) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_const_mul_atTop_of_pos rp).mpr cofactor_scale_grows)
  have ratio (r : ℝ) (rp : 0<r) : Tendsto (fun X => (atFraction r X:ℝ)/Z X) atTop (𝓝 r) :=
    (tendsto_nat_floor_mul_div_atTop rp.le).comp cofactor_scale_grows
  have rat := (ratio v (ap.trans_le av)).div (ratio a ap) ap.ne'
  have phase := (Real.continuousAt_log (div_pos (ap.trans_le av) ap).ne').tendsto.comp rat
  have diff := (Real.tendsto_harmonic_sub_log.comp (cut v (ap.trans_le av))).sub
    (Real.tendsto_harmonic_sub_log.comp (cut a ap))
  rw [sub_self] at diff
  have result := diff.add phase
  rw [zero_add] at result
  apply result.congr'
  filter_upwards [(cut a ap).eventually_ge_atTop 1,(cut v (ap.trans_le av)).eventually_ge_atTop 1,
    cofactor_scale_grows.eventually_gt_atTop 0] with X aa vv zp
  let A := atFraction a X
  let B := atFraction v X
  have h : A ≤ B := Nat.floor_mono (mul_le_mul_of_nonneg_right av zp.le)
  have an : (A:ℝ) ≠ 0 := (Nat.cast_pos.mpr aa).ne'
  have bn : (B:ℝ) ≠ 0 := (Nat.cast_pos.mpr vv).ne'
  change ((harmonic B:ℝ)-Real.log B-((harmonic A:ℝ)-Real.log A))+Real.log ((B:ℝ)/Z X/((A:ℝ)/Z X))=_
  have cancel (a b z : ℝ) (ha : a ≠ 0) (hz : z ≠ 0) : b/z/(a/z)=b/a := by
    field_simp [ha,hz]
  rw [cancel _ _ _ an zp.ne',Real.log_div bn an]
  have union : Icc 1 A ∪ Ioc A B=Icc 1 B := by ext; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  have dis : Disjoint (Icc 1 A) (Ioc A B) := disjoint_left.mpr (fun _ ha hb => (mem_Ioc.mp hb).1.not_ge (mem_Icc.mp ha).2)
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [←union,sum_union dis]; change _=∑ n ∈ Ioc A B,(n:ℝ)⁻¹; ring

private theorem harmonic_sign_window (sign : Bool) {a v : ℝ} (ap : 0<a) (av : a ≤ v) (v1 : v ≤ 1) :
    Tendsto (fun X => signedMass sign X (cell a v X) (fun n => (n:ℝ)⁻¹)/density (y X))
      atTop (𝓝 (Real.log (v/a)/2)) := by
  let P := fun X => signedMass sign X (cell a v X) (fun n => (n:ℝ)⁻¹)/density (y X)
  let Q := fun X => (∑ n ∈ cell a v X,(n:ℝ)⁻¹)/2
  have vanish : Tendsto (fun X => P X-Q X) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε ep
    let η := ε*a/8
    have eta : 0<η := div_pos (mul_pos ep ap) (by norm_num)
    filter_upwards [uniform_cofactor_discrepancy eta,cofactor_scale_grows.eventually_gt_atTop (2/a),
      logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with X uni large yp xp
    let A := atFraction a X
    let B := atFraction v X
    let d := density (y X)
    let F := fun k : ℕ => rankAt sign X k-d*k/2
    have zp : 0<Z X := div_pos (Nat.cast_pos.mpr xp) (Nat.cast_pos.mpr yp)
    have dp : 0<d := coprimeSquarefreeDensity_pos _
    have order : A ≤ B := Nat.floor_mono (mul_le_mul_of_nonneg_right av zp.le)
    have big := (div_lt_iff₀ ap).mp large
    have round : a*Z X<(A:ℝ)+1 := Nat.lt_floor_add_one _
    have floor : a*Z X ≤ 2*(A:ℝ) := by linarith only [round,big]
    have An : 0<(A:ℝ) := by linarith only [big,floor]
    have endB : (B:ℝ) ≤ Z X := (Nat.floor_le (mul_nonneg (ap.le.trans av) zp.le)).trans
      ((mul_le_mul_of_nonneg_right v1 zp.le).trans_eq (one_mul _))
    have inc (n : ℕ) (np : 0<n) : F n-F (n-1)=mark sign X n-d/2 := by
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero np.ne'
      dsimp only [F]; rw [rank_step,Nat.succ_sub_one,Nat.cast_succ]; ring
    have bd := decreasing_test_error F (fun k : ℕ => (k:ℝ)⁻¹) order (D := η*denom X)
      (fun k hk => by simpa only [Nat.floor_natCast,F,d] using
        (uni k (Nat.cast_nonneg _) ((Nat.cast_le.mpr (mem_Icc.mp hk).2).trans endB) sign))
      (fun k _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      (fun k hk => inv_anti₀ (An.trans_le (Nat.cast_le.mpr (mem_Ico.mp hk).1))
        (Nat.cast_le.mpr (Nat.le_succ k)))
    rw [sum_congr (s₁ := Ioc A B) rfl (fun k hk => congrArg (· * (k:ℝ)⁻¹) (inc k ((Nat.zero_le A).trans_lt (mem_Ioc.mp hk).1)))] at bd
    have eq : (P X-Q X)*d=∑ k ∈ cell a v X,(mark sign X k-d/2)*(k:ℝ)⁻¹ := by
      have normalize (s h d : ℝ) (hd : d ≠ 0) :
          (s/d-h/2)*d=s-(d/2)*h := by field_simp [hd] <;> ring
      calc
        _ = (∑ k ∈ cell a v X,mark sign X k*(k:ℝ)⁻¹)-d/2*(∑ k ∈ cell a v X,(k:ℝ)⁻¹) :=
          normalize _ _ _ dp.ne'
        _ = _ := by simp only [sub_mul,sum_sub_distrib,←mul_sum]
    have h := bd
    change |∑ k ∈ cell a v X,(mark sign X k-d/2)*(k:ℝ)⁻¹| ≤ 2*(η*denom X)*(A:ℝ)⁻¹ at h
    rw [←eq,abs_mul,abs_of_pos dp] at h
    rw [Real.dist_eq,sub_zero]
    apply lt_of_mul_lt_mul_right (a := d) _ dp.le
    apply h.trans_lt
    rw [←div_eq_mul_inv,div_lt_iff₀ An]
    dsimp only [η,denom,d]
    have ready := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left floor ep.le) dp.le
    nlinarith only [ready,mul_pos (mul_pos ep An) dp]
  have h := vanish.add ((harmonic_window ap av).div_const 2)
  rw [zero_add] at h
  exact h.congr (fun n => sub_add_cancel (P n) (Q n))

private abbrev fractionTest (X : ℕ) (c : ℝ) (n : ℕ) := Z X/(n:ℝ)-(1+c)
private abbrev modelCost (b : Bool) (X : ℕ) (c a v : ℝ) :=
  signedMass b X (cell a v X) (fun n => |fractionTest X c n|)/denom X

private theorem signed_readout (b : Bool) {a v : ℝ} (ap : 0<a) (av : a ≤ v) (v1 : v ≤ 1) (c : ℝ) :
    Tendsto (fun X => signedMass b X (cell a v X) (fractionTest X c)/denom X) atTop
      (𝓝 ((Real.log (v/a)-(1+c)*(v-a))/2)) := by
  have out := (harmonic_sign_window b ap av v1).sub
    ((sign_mass_on_a_terminal_cofactor_interval b ap.le av v1).const_mul (1+c))
  rw [show Real.log (v/a)/2-(1+c)*((v-a)/2)=(Real.log (v/a)-(1+c)*(v-a))/2 by ring] at out
  apply out.congr'
  filter_upwards [cofactor_scale_grows.eventually_gt_atTop 0] with X zp
  have dp := coprimeSquarefreeDensity_pos (primorial (y X))
  have atom (n : ℕ) : mark b X n*fractionTest X c n=
      Z X*(mark b X n*(n:ℝ)⁻¹)-(1+c)*mark b X n := by dsimp only [fractionTest]; ring
  simp only [signedMass,mul_one,sum_congr rfl (fun n _ => atom n),sum_sub_distrib,←mul_sum]
  have normalize (a m z d k : ℝ) (hz : z ≠ 0) (hd : d ≠ 0) :
      a/d-k*(m/(z*d))=(z*a-k*m)/(z*d) := by field_simp [hz,hd]
  exact normalize _ _ _ _ _ zp.ne' dp.ne'

private theorem cell_union {a d v : ℝ} (ad : a ≤ d) (dv : d ≤ v) (X : ℕ) :
    Disjoint (cell a d X) (cell d v X) ∧ cell a d X ∪ cell d v X=cell a v X := by
  have z0 : 0 ≤ Z X := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have ab : atFraction a X ≤ atFraction d X := Nat.floor_mono (mul_le_mul_of_nonneg_right ad z0)
  have bc : atFraction d X ≤ atFraction v X := Nat.floor_mono (mul_le_mul_of_nonneg_right dv z0)
  refine ⟨disjoint_left.mpr (fun _ hm hn => (mem_Ioc.mp hn).1.not_ge (mem_Ioc.mp hm).2),?_⟩
  ext; simp only [cell,mem_union,mem_Ioc]; omega

private abbrev psi := (1/2:ℝ)
private abbrev median := (3/4:ℝ)
private abbrev boundaryLog := Real.log (9/8:ℝ)/2

private theorem median_lower_signal (b : Bool) (c : ℝ) :
    Tendsto (fun X => (signedMass b X (cell psi median X) (fractionTest X c)-
      signedMass b X (cell median 1 X) (fractionTest X c))/denom X) atTop (𝓝 boundaryLog) := by
  have left := signed_readout b (by norm_num : 0<psi) (by norm_num : psi ≤ median) (by norm_num : median ≤ 1) c
  have right := signed_readout b (by norm_num : 0 < median) (by norm_num : median ≤ 1) le_rfl c
  have res := left.sub right
  have parts : Real.log (median/psi)-Real.log (1/median)=Real.log (9/8:ℝ) := by
    rw [←Real.log_div (by norm_num [median,psi]) (by norm_num [median])]; congr 1; norm_num [median,psi]
  have eq : (Real.log (median/psi)-(1+c)*(median-psi))/2-
      (Real.log (1/median)-(1+c)*(1-median))/2=boundaryLog := by
    dsimp only [boundaryLog]; rw [←parts]; dsimp only [psi,median]; ring
  rw [eq] at res
  exact res.congr (fun X => (sub_div ..).symm)

private theorem lower_for_the_model (b : Bool) (c : ℝ) (X : ℕ) :
    (signedMass b X (cell psi median X) (fractionTest X c)-
      signedMass b X (cell median 1 X) (fractionTest X c))/denom X ≤ modelCost b X c psi 1 := by
  obtain ⟨dis,un⟩ := cell_union (by norm_num : psi ≤ median) (by norm_num : median ≤ 1) X
  apply div_le_div_of_nonneg_right _ (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (coprimeSquarefreeDensity_pos _).le)
  change _ ≤ ∑ n ∈ cell psi 1 X,mark b X n*|fractionTest X c n|
  rw [←un,sum_union dis,sub_eq_add_neg]
  apply add_le_add
  · exact sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left (le_abs_self _) (mark_nonneg b X n))
  · dsimp only [signedMass]
    rw [←sum_neg_distrib]
    exact sum_le_sum (fun n _ => by rw [←mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) (mark_nonneg b X n))

private def modelLimit (t : ℝ) :=
  (Real.log (t/psi)-Real.log (1/t)-(1/t)*(t-psi)+(1/t)*(1-t))/2

private theorem model_limit_at_cut (b : Bool) {t : ℝ} (low : psi ≤ t) (high : t ≤ 1) :
    Tendsto (fun X => modelCost b X (1/t-1) psi 1) atTop (𝓝 (modelLimit t)) := by
  have tp := (by norm_num : 0<psi).trans_le low
  let c := 1/t-1
  have eq : 1+c=1/t := by dsimp only [c]; ring
  have left := signed_readout b (by norm_num : 0<psi) low high c
  have right := signed_readout b tp high le_rfl c
  have result := left.sub right
  rw [eq,show (Real.log (t/psi)-(1/t)*(t-psi))/2-
      (Real.log (1/t)-(1/t)*(1-t))/2=modelLimit t by dsimp only [modelLimit]; ring] at result
  apply result.congr'
  filter_upwards [cofactor_scale_grows.eventually_gt_atTop 0] with X pos
  obtain ⟨dis,un⟩ := cell_union low high X
  change _ = modelCost b X c psi 1
  rw [←sub_div]
  apply congrArg (· / denom X)
  dsimp only [signedMass]
  rw [←un,sum_union dis,sub_eq_add_neg,←sum_neg_distrib]
  congr 1
  · apply sum_congr rfl
    intro n hn
    have h := mem_Ioc.mp hn
    have np : (0:ℝ)<n := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt h.1)
    have hi := (Nat.cast_le.mpr h.2).trans (Nat.floor_le (mul_nonneg tp.le pos.le))
    have paid : 1/t ≤ Z X/(n:ℝ) := (div_le_div_iff₀ tp np).mpr (by linarith only [hi])
    rw [abs_of_nonneg (show 0 ≤ fractionTest X c n by dsimp only [fractionTest]; rw [eq]; exact sub_nonneg.mpr paid)]
  · apply sum_congr rfl
    intro n hn
    have h := mem_Ioc.mp hn
    have lo := Nat.lt_of_floor_lt h.1
    have np : (0:ℝ)<n := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt h.1)
    have paid : Z X/(n:ℝ) ≤ 1/t := (div_le_div_iff₀ np tp).mpr (by linarith only [lo])
    rw [abs_of_nonpos (show fractionTest X c n ≤ 0 by dsimp only [fractionTest]; rw [eq]; exact sub_nonpos.mpr paid),mul_neg]

/-- Raw prime reading on the first quotient cell, after subtracting a
constant multiple of the prime wall and taking absolute values per cofactor.
The normalization is X times the local squarefree rough density. -/
def absoluteFirstCellPrice (b : Bool) (c : ℝ) (X : ℕ) :=
  signedMass b X (cell psi 1 X) (fun n =>
    |(Chebyshev.theta ((X:ℝ)/n)-Chebyshev.theta (y X))/(y X:ℝ)-c|)/denom X

private theorem actual_minus_model (b : Bool) (c : ℝ) :
    Tendsto (fun X => absoluteFirstCellPrice b c X-modelCost b X c psi 1) atTop (𝓝 0) := by
  have count := sign_mass_on_a_terminal_cofactor_interval b (by norm_num : 0 ≤ psi) (by norm_num : psi ≤ 1) le_rfl
  rw [Metric.tendsto_nhds]
  intro ε ep
  let η := ε/6
  have hp : 0<η := div_pos ep (by norm_num)
  have pnt := (Metric.tendsto_nhds.mp RHTower.tendsto_theta_div_self) η hp
  obtain ⟨N,above⟩ := eventually_atTop.1 pnt
  filter_upwards [(tendsto_natCast_atTop_atTop.comp logSquareCutoff_tendsto_atTop).eventually_ge_atTop N,
    logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ),
    count.eventually_lt_const (by norm_num [psi] : (1-psi)/2<1)] with X late yp xp small
  have wp : 0<(y X:ℝ) := Nat.cast_pos.mpr yp
  have zp : 0<Z X := div_pos (Nat.cast_pos.mpr xp) wp
  have dz := denominator_pos xp yp
  have error (t : ℝ) (wt : (y X:ℝ) ≤ t) : |Chebyshev.theta t-t| ≤ η*t := by
    have h := above t (late.trans wt)
    change dist (Chebyshev.theta t/t) 1 < η at h
    have tp := wp.trans_le wt
    rw [Real.dist_eq,show Chebyshev.theta t/t-1=(Chebyshev.theta t-t)/t by field_simp,
      abs_div,abs_of_pos tp,div_lt_iff₀ tp] at h
    exact h.le
  let P := fun m : ℕ => (Chebyshev.theta ((X:ℝ)/m)-Chebyshev.theta (y X))/(y X:ℝ)-c
  have atom (n : ℕ) (hn : n∈cell psi 1 X) : |P n-fractionTest X c n| ≤ 3*η := by
    have h := mem_Ioc.mp hn
    have np : (0:ℝ)<n := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt h.1)
    have lo := Nat.lt_of_floor_lt h.1
    have hi := (Nat.cast_le.mpr h.2).trans (Nat.floor_le (show 0 ≤ 1*Z X by positivity))
    rw [one_mul] at hi
    let t := (X:ℝ)/(n:ℝ)
    have wt : (y X:ℝ) ≤ t := (le_div_iff₀ np).mpr (by linarith only [(le_div_iff₀ wp).mp hi])
    have tw : t ≤ 2*(y X:ℝ) := by
      apply (div_le_iff₀ np).mpr
      change (1/2:ℝ)*((X:ℝ)/(y X:ℝ)) < n at lo
      rw [←mul_div_assoc,div_lt_iff₀ wp] at lo
      linarith only [lo]
    have eq : P n-fractionTest X c n=((Chebyshev.theta t-t)-(Chebyshev.theta (y X)-y X))/(y X:ℝ) := by
      dsimp only [P,t,fractionTest,Z]; field_simp [np.ne',wp.ne']; ring
    rw [eq,abs_div,abs_of_pos wp,div_le_iff₀ wp]
    exact (abs_sub ..).trans (by linarith only [error t wt,error (y X) le_rfl,mul_le_mul_of_nonneg_left tw hp.le])
  have sum := abs_sum_le_sum_abs (fun n => mark b X n*(|P n|-|fractionTest X c n|)) (cell psi 1 X)
  have fee (n : ℕ) (hn : n∈cell psi 1 X) :
      |mark b X n*(|P n|-|fractionTest X c n|)| ≤ mark b X n*(3*η) := by
    have m0 := mark_nonneg b X n
    rw [abs_mul,abs_of_nonneg m0]
    exact mul_le_mul_of_nonneg_left ((abs_abs_sub_abs_le_abs_sub ..).trans (atom n hn)) m0
  have total := sum.trans (sum_le_sum fee)
  simp only [mul_sub,sum_sub_distrib,←sum_mul] at total
  change signedMass b X (cell psi 1 X) (fun _ => 1)/denom X<1 at small
  simp only [signedMass,mul_one,div_lt_one dz] at small
  rw [Real.dist_eq,sub_zero]
  change |(∑ n ∈ cell psi 1 X,mark b X n*|P n|)/denom X-
    (∑ n ∈ cell psi 1 X,mark b X n*|fractionTest X c n|)/denom X|<ε
  rw [←sub_div,abs_div,abs_of_pos dz,div_lt_iff₀ dz]
  apply total.trans_lt
  dsimp only [η]
  linarith only [mul_lt_mul_of_pos_right small ep,mul_pos ep dz]

private theorem transfer_price (b : Bool) (c : ℝ) {k : ℝ}
    (model : Tendsto (fun X => modelCost b X c psi 1) atTop (𝓝 k)) :
    Tendsto (absoluteFirstCellPrice b c) atTop (𝓝 k) := by
  have h := (actual_minus_model b c).add model
  rw [zero_add] at h
  exact h.congr (fun X => sub_add_cancel ..)

/-- No constant center makes the leading absolute cost of either sign
smaller than one half of log(9/8). -/
theorem lower_price_of_every_constant_center (b : Bool) (c : ℝ) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ X in atTop,Real.log (9/8:ℝ)/2-ε ≤ absoluteFirstCellPrice b c X := by
  have h := (median_lower_signal b c).add (actual_minus_model b c)
  rw [add_zero] at h
  filter_upwards [h.eventually_const_lt (sub_lt_self boundaryLog ep)] with X large
  have bound := lower_for_the_model b c X
  exact large.le.trans (by linarith only [bound])

/-- The optimal center is y/3. The original floor center y has the larger
leading absolute price (1−log 2)/2 for each rough sign. -/
theorem optimal_and_floor_centers_of_the_first_quotient_cell (b : Bool) :
    Tendsto (absoluteFirstCellPrice b (1/3)) atTop (𝓝 (Real.log (9/8:ℝ)/2)) ∧
    Tendsto (absoluteFirstCellPrice b 1) atTop (𝓝 ((1-Real.log 2)/2)) := by
  have mid := model_limit_at_cut b (by norm_num : psi ≤ median) (by norm_num : median ≤ 1)
  have far := model_limit_at_cut b (t := psi) le_rfl (by norm_num : psi ≤ 1)
  have val : modelLimit median=boundaryLog := by
    have pair : Real.log (median/psi)-Real.log (1/median)=Real.log (9/8:ℝ) := by
      rw [←Real.log_div (by norm_num [psi,median]) (by norm_num [median])]
      congr 1; norm_num [psi,median]
    dsimp only [modelLimit,boundaryLog]; rw [←pair]; dsimp only [median,psi]; ring
  have floor : modelLimit psi=(1-Real.log 2)/2 := by
    norm_num [modelLimit,psi] <;> ring
  rw [val,show 1/median-1=1/3 by norm_num [median]] at mid
  rw [floor,show 1/psi-1=1 by norm_num [psi]] at far
  exact ⟨transfer_price _ _ mid,transfer_price _ _ far⟩

private theorem unique_optimum_of_the_model {t : ℝ} (tp : 0<t) (ne : t ≠ median) :
    boundaryLog < modelLimit t := by
  have pp : 0<psi := by norm_num [psi]
  have mp : 0 < median := by norm_num [median]
  have novel : median/t ≠ 1 := fun h => ne (by simpa only [one_mul] using ((div_eq_iff tp.ne').mp h).symm)
  have strict := Real.log_lt_sub_one_of_pos (div_pos mp tp) novel
  have value : Real.log (9/8:ℝ)=2*Real.log median-Real.log psi := by
    rw [show (9/8:ℝ)=median^2/psi by norm_num [median,psi],Real.log_div (pow_ne_zero _ mp.ne') pp.ne',Real.log_pow]
    norm_num
  rw [Real.log_div mp.ne' tp.ne'] at strict
  dsimp only [boundaryLog,modelLimit]
  rw [value,Real.log_div tp.ne' pp.ne',Real.log_div one_ne_zero tp.ne',Real.log_one,zero_sub]
  have algebra : (1/t)*(1-t)-(1/t)*(t-psi)=2*(median/t-1) := by
    dsimp only [median,psi]; field_simp [tp.ne']; ring
  linarith only [strict,algebra]

private theorem project_model_center (b : Bool) (c : ℝ) (X : ℕ) :
    (c<0 → modelCost b X 0 psi 1 ≤ modelCost b X c psi 1) ∧
    (1<c → modelCost b X 1 psi 1 ≤ modelCost b X c psi 1) := by
  have z0 : 0 ≤ Z X := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have dd : 0 ≤ denom X := mul_nonneg z0 (coprimeSquarefreeDensity_pos _).le
  have inRange (n : ℕ) (hn : n∈cell psi 1 X) : 1 ≤ Z X/(n:ℝ) ∧ Z X/(n:ℝ) ≤ 2 := by
    obtain ⟨lo,hi⟩ := mem_Ioc.mp hn
    have np : (0:ℝ)<n := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt lo)
    have lower := Nat.lt_of_floor_lt lo
    have upper := (Nat.cast_le.mpr hi).trans (Nat.floor_le (mul_nonneg zero_le_one z0))
    exact ⟨(le_div_iff₀ np).mpr (by linarith only [upper]),(div_le_iff₀ np).mpr (by dsimp only [psi] at lower; linarith only [lower])⟩
  constructor
  · intro left
    apply div_le_div_of_nonneg_right (sum_le_sum ?_) dd
    intro n hn
    have w := (inRange n hn).1
    apply mul_le_mul_of_nonneg_left _ (mark_nonneg b X n)
    dsimp only [fractionTest]
    rw [abs_of_nonneg (by linarith only [w]),abs_of_nonneg (by linarith only [w,left])]
    linarith only [left]
  · intro right
    apply div_le_div_of_nonneg_right (sum_le_sum ?_) dd
    intro n hn
    have w := (inRange n hn).2
    apply mul_le_mul_of_nonneg_left _ (mark_nonneg b X n)
    dsimp only [fractionTest]
    rw [abs_of_nonpos (by linarith only [w]),abs_of_nonpos (by linarith only [w,right])]
    linarith only [right]

/-- The leading lower bound is attained by exactly one constant center. -/
theorem unique_constant_center_in_the_first_quotient_cell (b : Bool) (c : ℝ) :
    Tendsto (absoluteFirstCellPrice b c) atTop (𝓝 (Real.log (9/8:ℝ)/2)) ↔ c=1/3 := by
  refine ⟨?_,fun h => h ▸ (optimal_and_floor_centers_of_the_first_quotient_cell b).1⟩
  intro optimal
  have model : Tendsto (fun X => modelCost b X c psi 1) atTop (𝓝 boundaryLog) := by
    have h := optimal.sub (actual_minus_model b c)
    rw [sub_zero] at h
    exact h.congr (fun _ => sub_sub_cancel ..)
  have low : 0 ≤ c := by
    by_contra! bad
    have h := model_limit_at_cut b (t := 1) (by norm_num [psi]) le_rfl
    rw [show (1:ℝ)/1-1=0 by norm_num] at h
    exact (unique_optimum_of_the_model zero_lt_one (by norm_num [median])).not_ge
      (le_of_tendsto_of_tendsto h model (Eventually.of_forall (fun X => (project_model_center b c X).1 bad)))
  have high : c ≤ 1 := by
    by_contra! bad
    have h := model_limit_at_cut b (t := psi) le_rfl (by norm_num [psi])
    rw [show 1/psi-1=1 by norm_num [psi]] at h
    exact (unique_optimum_of_the_model (by norm_num : 0<psi) (by norm_num [psi,median])).not_ge
      (le_of_tendsto_of_tendsto h model (Eventually.of_forall (fun X => (project_model_center b c X).2 bad)))
  let t := 1/(1+c)
  have pos : 0<1+c := by linarith only [low]
  have t0 : 0<t := one_div_pos.mpr pos
  have lo : psi ≤ t := (le_div_iff₀ pos).mpr (by dsimp only [psi]; linarith only [high])
  have hi : t ≤ 1 := (div_le_one pos).mpr (by linarith only [low])
  have pick : 1/t-1=c := by dsimp only [t]; field_simp; ring
  have paid := model_limit_at_cut b lo hi
  rw [pick] at paid
  have eq := tendsto_nhds_unique model paid
  have tt : t=median := by
    by_contra ne; exact (unique_optimum_of_the_model t0 ne).ne eq
  rw [←pick,tt]; norm_num [median]

end GaloisForLFunctions.RestrictedFactorizationCalculus
