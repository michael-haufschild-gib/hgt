import GaloisForLFunctions.ExceptionalLayerTheory.PairedCofactorBoundsForOrdinaryPrimeCounts
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldZetaPoleCarrier
import GaloisForLFunctions.HTGeometry.JacobiThetaDefectMeromorphicOrder
import GaloisForLFunctions.RHTower.BaezDuarteSmoothZeroDual
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Every nonzero finite cofactor detects the ordinary prime count

Count each prime once and subtract the reciprocal-logarithm density of
the integers. A power bound for a finite convolution continues its
Dirichlet series. Division by the finite cofactor would give a meromorphic
primitive of a current with a nonzero simple-pole residue at a right zero.
Zeros of the cofactor of any finite order leave this obstruction intact.
-/

noncomputable section

open Complex Filter Topology Finset ArithmeticFunction
open scoped LSeries.notation
open RHTower.Sieve hiding dirPoly
open RHTower.WeilFiniteType

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Indicator of ordinary primes with the discrete logarithmic density removed. -/
def ordinaryPrimeCountWeight : ArithmeticFunction ℝ where
  toFun n := (if n.Prime then 1 else 0) - (Real.log n)⁻¹
  map_zero' := by simp [Nat.not_prime_zero]

private theorem ordinaryPrimeCountWeight_apply (n : ℕ) :
    ordinaryPrimeCountWeight n = (if n.Prime then 1 else 0) - (Real.log n)⁻¹ := rfl

/-- Cumulative count convolved with a cofactor of width `W`. -/
def filteredOrdinaryPrimes (W : ℕ) (f : ArithmeticFunction ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (truncAF f W * ordinaryPrimeCountWeight) n

private theorem prefix_count_weight (N : ℕ) :
    (∑ n ∈ Icc 1 N, ordinaryPrimeCountWeight n) =
      (Nat.primeCounting N : ℝ) - ∑ n ∈ Icc 1 N, (Real.log n)⁻¹ := by
  simp_rw [ordinaryPrimeCountWeight_apply]
  rw [sum_sub_distrib, ← sum_filter, ← Nat.primesLE_eq_filter_Icc_one]
  simp [Nat.primesLE_card_eq_primeCounting]

/-- A finite sum of actual prime counts at divided integer cutoffs. -/
theorem filteredOrdinaryPrimes_eq (W : ℕ) (f : ArithmeticFunction ℝ) (N : ℕ) :
    filteredOrdinaryPrimes W f N = ∑ d ∈ Icc 1 (min N W), f d *
      ((Nat.primeCounting (N/d) : ℝ) - ∑ n ∈ Icc 1 (N/d), (Real.log n)⁻¹) := by
  rw [filteredOrdinaryPrimes, RHTower.sum_Icc_mul_apply]
  simp_rw [prefix_count_weight, truncAF_apply, ite_mul, zero_mul, ← sum_filter]
  congr 1
  ext d
  simp only [mem_filter, mem_Icc, le_min_iff]
  tauto

private abbrev a (n : ℕ) : ℂ := (ordinaryPrimeCountWeight n : ℂ)

private theorem base_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable a s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1+(Real.log 2)⁻¹) _ hs
  intro n hn
  rw [Complex.norm_real, Real.norm_eq_abs]
  change |(if n.Prime then (1:ℝ) else 0) - (Real.log n)⁻¹| ≤ _
  rcases eq_or_ne n 1 with rfl | hn1
  · simp only [Nat.not_prime_one, if_false, Nat.cast_one, Real.log_one, inv_zero, sub_zero, abs_zero]
    positivity
  have hn2 : 2 ≤ n := by omega
  have hlog := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by exact_mod_cast hn2 : (2:ℝ) ≤ n)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · split_ifs <;> norm_num
  · rw [abs_of_nonneg (inv_nonneg.mpr (htwo.le.trans hlog))]
    exact inv_anti₀ htwo hlog

private def primeLogWeight (n : ℕ) : ℂ := if n.Prime then (Real.log n : ℝ) else 0

private theorem primeLog_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable primeLogWeight s := by
  let v := fun n : ℕ => (vonMangoldt n : ℂ)
  have h : LSeriesSummable v s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  apply Summable.of_norm_bounded (h.norm)
  intro n
  by_cases hp : n.Prime
  · have he : LSeries.term primeLogWeight s n = LSeries.term v s n := by
      rw [LSeries.term_of_ne_zero hp.ne_zero, LSeries.term_of_ne_zero hp.ne_zero]
      simp [primeLogWeight, v, hp, vonMangoldt_apply_prime hp]
    rw [he]
  · have he : LSeries.term primeLogWeight s n = 0 := by simp [LSeries.term,primeLogWeight,hp]
    rw [he,norm_zero]
    exact norm_nonneg _

private theorem primeLog_series {s : ℂ} (hs : 1 < s.re) :
    LSeries primeLogWeight s = RHTower.xiPrimeLogDirichlet s := by
  rw [RHTower.xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow hs]
  unfold LSeries
  let g := fun n : ℕ => (Real.log n : ℂ) / (n : ℂ)^s
  have he : LSeries.term primeLogWeight s = {n : ℕ | n.Prime}.indicator g := by
    funext n
    by_cases hp : n.Prime
    · rw [LSeries.term_of_ne_zero hp.ne_zero,
        Set.indicator_of_mem (show n ∈ {k : ℕ | k.Prime} from hp)]
      simp [primeLogWeight,hp,g]
    · simp [LSeries.term,primeLogWeight,hp,g,Set.indicator]
  rw [he, ← _root_.tsum_subtype]
  change (∑' p : Nat.Primes, g (p : ℕ)) = _
  exact tsum_congr (fun p => by simp [g])

/-- Meromorphic continuation of the derivative of the centred prime series. -/
private def primeCountDerivative (s : ℂ) : ℂ := riemannZeta s - 1 - RHTower.xiPrimeLogDirichletContinuation s

private theorem base_deriv {s : ℂ} (hs : 1 < s.re) :
    deriv (LSeries a) s = primeCountDerivative s := by
  let x : ℝ := (1+s.re)/2
  have hx : 1 < x := by dsimp only [x]; linarith only [hs]
  have hxs : x < s.re := by dsimp only [x]; linarith only [hs]
  have hab := (base_summable (s := (x:ℂ)) (by simpa using hx)).abscissaOfAbsConv_le
  have hlog {n : ℕ} (hn : n ≠ 0) :
      LSeries.logMul a n = (primeLogWeight - ((1 : ℕ → ℂ) - LSeries.delta)) n := by
    by_cases hn1 : n = 1
    · subst n
      simp [LSeries.logMul,primeLogWeight,LSeries.delta]
    · have hp : (0:ℝ) < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hpc : (Real.log n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
      have hclog : Complex.log (n : ℂ) ≠ 0 := by rwa [← Complex.natCast_log]
      change Complex.log n * (((if n.Prime then (1:ℝ) else 0) - (Real.log n)⁻¹ : ℝ) : ℂ) = _
      rw [← Complex.natCast_log]
      simp only [primeLogWeight, Pi.sub_apply, Pi.one_apply, LSeries.delta, if_neg hn1]
      split_ifs <;> push_cast <;> field_simp [hclog] <;> ring
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_of_bounded_of_one_lt_re
    (m := 1) (fun n _ => by simp) hs
  have hδ : LSeriesSummable LSeries.delta s := by
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn
    simp only [mem_singleton] at hn
    simp [LSeries.term_delta,hn]
  rw [LSeries_deriv (hab.trans_lt (by exact_mod_cast hxs)), LSeries_congr hlog s,
    LSeries_sub (primeLog_summable hs) (h1.sub hδ), LSeries_sub h1 hδ,
    LSeries_one_eq_riemannZeta hs, LSeries_delta, primeLog_series hs, primeCountDerivative,
    RHTower.xiPrimeLogDirichletContinuation_eq hs, Pi.one_apply]
  ring

private theorem derivative_meromorphic {s : ℂ} (hs : 1/2 < s.re) : MeromorphicAt primeCountDerivative s := by
  have hζ := RHTower.meromorphicAt_riemannZeta_everywhere s
  have hh := (RHTower.differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re) s hs).meromorphicAt
  have hflux : MeromorphicAt RHTower.infinitePrimeFlux s := by
    change MeromorphicAt (-(deriv riemannZeta / riemannZeta)) s
    exact (hζ.deriv.div hζ).neg
  have h1 : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) s := analyticAt_const.meromorphicAt
  exact (hζ.sub h1).sub (hflux.sub hh)

/-- A derivative of a meromorphic germ cannot have a simple pole. -/
theorem meromorphic_deriv_order_ne_neg_one {G : ℂ → ℂ} {p : ℂ} (hG : MeromorphicAt G p) :
    meromorphicOrderAt (deriv G) p ≠ ((-1 : ℤ) : WithTop ℤ) := by
  intro h
  by_cases hnon : 0 ≤ meromorphicOrderAt G p
  · obtain ⟨H,hH,he⟩ := hG.meromorphicOrderAt_nonneg_iff.mp hnon
    have ho := hH.deriv.meromorphicOrderAt_nonneg
    rw [← meromorphicOrderAt_congr he.nhdsNE_deriv, h] at ho
    have hi : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp ho
    omega
  · cases hk : meromorphicOrderAt G p with
    | top => exact hnon (hk ▸ le_top)
    | coe k =>
      have hk0 : k ≠ 0 := fun he => hnon (by simp [hk,he])
      have hd := meromorphicOrderAt_deriv_eq_sub_one (show (k : ℂ) ≠ 0 by exact_mod_cast hk0) hk
      have e : k - 1 = -1 := by exact_mod_cast hd.symm.trans h
      omega

private theorem derivative_pole {ρ : ℂ} (hρ : 1/2 < ρ.re) (hz : riemannZeta ρ = 0) :
    meromorphicOrderAt primeCountDerivative ρ = ((-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨m,hm,hres⟩ := RHTower.xiPrimeLogDirichletContinuation_zero_residue hρ hz
  have hreg := ((differentiableAt_riemannZeta (RHTower.riemannZeta_zero_ne_one hz)).continuousAt.sub
    (continuousAt_const (y := (1:ℂ)))).tendsto.mono_left (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hlin : Tendsto (fun s : ℂ => s-ρ) (𝓝[≠] ρ) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' ρ 0 (sub_self ρ)).mono_left nhdsWithin_le_nhds
  apply meromorphicOrderAt_eq_neg_one_of_tendsto_mul_sub (derivative_meromorphic hρ) (c := (m:ℂ))
    (Nat.cast_ne_zero.mpr (by omega))
  convert (hlin.mul hreg).sub hres using 1
  · funext s
    change (s-ρ) * (riemannZeta s - 1 - RHTower.xiPrimeLogDirichletContinuation s) =
      (s-ρ) * (riemannZeta s - 1) - (s-ρ) * RHTower.xiPrimeLogDirichletContinuation s
    ring
  · rw [zero_mul, zero_sub, neg_neg]

private theorem exists_euler_point {W : ℕ} {g : ArithmeticFunction ℝ} (hsupp : SupportedIn W g)
    (hne : ∃ n, g n ≠ 0) : ∃ x : ℝ, 1 < x ∧ dirPoly W g x ≠ 0 := by
  by_contra! h
  have hz : (fun x : ℝ => LSeries (fun n => (g n : ℂ)) x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    rw [LSeries_eq_dirPoly hsupp]
    exact h x hx
  have htop := (LSeriesSummable_of_supportedIn hsupp 2).abscissaOfAbsConv_le
  have hall := (LSeries_eventually_eq_zero_iff'.mp hz).resolve_right
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) htop)
  obtain ⟨n,hn⟩ := hne
  exact hn (Complex.ofReal_eq_zero.mp (hall n (fun e => hn (e ▸ ArithmeticFunction.map_zero))))

/-- A bound below any right zero is impossible for every nonzero finite cofactor,
including a cofactor whose Dirichlet polynomial vanishes at that very zero. -/
theorem ordinaryPrime_count_bound_excludes_right_zero (W : ℕ) (f : ArithmeticFunction ℝ)
    (hnz : ∃ d ∈ Icc 1 W, f d ≠ 0) {b K : ℝ} (hb : 1/2 ≤ b) (hb1 : b < 1)
    (hcount : ∀ N : ℕ, 1 ≤ N → |filteredOrdinaryPrimes W f N| ≤ K*(N:ℝ)^b)
    {ρ : ℂ} (hρ : b < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro hz
  let g := truncAF f W
  let c := fun n => (((g * ordinaryPrimeCountWeight) n : ℝ) : ℂ)
  let D := dirPoly W g
  let U := {s : ℂ | b < s.re}
  let H := HeckeLFunctions.growthCont c b
  let G := H / D
  have hsup : SupportedIn W g := ⟨ArithmeticFunction.map_zero, fun n hn => truncAF_apply_of_gt hn⟩
  have hc0 : c 0 = 0 := by simp [c]
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hcount 1 le_rfl)
  have hb0 : 0 ≤ b := by linarith only [hb]
  have hreal (x : ℝ) (hx : 1 ≤ x) : ‖∑ n ∈ Icc 1 ⌊x⌋₊, c n‖ ≤ K*x^b := by
    change ‖∑ n ∈ Icc 1 ⌊x⌋₊, (((g * ordinaryPrimeCountWeight) n : ℝ) : ℂ)‖ ≤ _
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact (hcount _ ((Nat.one_le_floor_iff x).mpr hx)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) hb0) hK)
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hH : DifferentiableOn ℂ H U := HeckeLFunctions.differentiableOn_growthCont hc0 hb0 hreal
  have hD : Differentiable ℂ D := differentiable_dirPoly W g
  have hG : MeromorphicOn G U := fun z hz => ((hH.analyticOnNhd hU z hz).meromorphicAt).div
    ((hD.analyticAt z).meromorphicAt)
  have hconv : c = ((fun n => (g n : ℂ)) ⍟ a) := by
    funext n
    rw [LSeries.convolution_def]
    exact coe_mul_apply _ _ _
  have hE (s : ℂ) (hs : 1 < s.re) (hDs : D s ≠ 0) : G s = LSeries a s := by
    have hg := LSeriesSummable_of_supportedIn hsup s
    have ha := base_summable hs
    have hcs : LSeriesSummable c s := by rw [hconv]; exact hg.convolution ha
    change H s / D s = _
    rw [div_eq_iff hDs, show H s = LSeries c s from HeckeLFunctions.growthCont_eq_LSeries
      hc0 hb0 hreal (hb1.trans hs) hcs, hconv, LSeries_convolution' hg ha, LSeries_eq_dirPoly hsup, mul_comm]
  obtain ⟨d,hd,hfd⟩ := hnz
  obtain ⟨x,hx,hxD⟩ := exists_euler_point hsup ⟨d, by simpa only [g,truncAF_apply,if_pos (mem_Icc.mp hd).2] using hfd⟩
  let V := {s : ℂ | 1 < s.re ∧ D s ≠ 0}
  have hop : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isClosed_eq hD.continuous (continuous_const : Continuous (fun _ : ℂ => (0:ℂ)))).isOpen_compl
  have heq (s : ℂ) (hs : s ∈ V) : deriv G s = primeCountDerivative s := by
    have hlocal : G =ᶠ[𝓝 s] LSeries a := by
      filter_upwards [hop.mem_nhds hs] with z hz
      exact hE z hz.1 hz.2
    exact hlocal.deriv_eq.trans (base_deriv hs.1)
  let F := deriv G - primeCountDerivative
  have hmero : MeromorphicOn F U := fun z hzu => (hG z hzu).deriv.sub (derivative_meromorphic (hb.trans_lt hzu))
  have h0 : meromorphicOrderAt F (x:ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [nhdsWithin_le_nhds (hop.mem_nhds (show (x:ℂ) ∈ V from ⟨hx,hxD⟩))] with s hs
    exact sub_eq_zero.mpr (heq s hs)
  have hp : meromorphicOrderAt F ρ = ⊤ := by
    by_contra h
    exact (hmero.meromorphicOrderAt_ne_top_of_isPreconnected (convex_halfSpace_re_gt b).isPreconnected
      hρ (show (x:ℂ) ∈ U from hb1.trans hx) h) h0
  have he : deriv G =ᶠ[𝓝[≠] ρ] primeCountDerivative := (meromorphicOrderAt_eq_top_iff.mp hp).mono
    fun s hs => sub_eq_zero.mp hs
  exact meromorphic_deriv_order_ne_neg_one (hG ρ hρ)
    ((meromorphicOrderAt_congr he).trans (derivative_pole (hb.trans_lt hρ) hz))

/-- Below a right zero every nonzero finite combination of ordinary prime counts
exceeds each constant multiple of the proposed power at arbitrarily large integers. -/
theorem filteredOrdinaryPrimes_frequently_large_at_right_zero (W : ℕ) (f : ArithmeticFunction ℝ)
    (hnz : ∃ d ∈ Icc 1 W, f d ≠ 0) {b : ℝ} (hb : 1/2 ≤ b) (hb1 : b < 1)
    {ρ : ℂ} (hρ : b < ρ.re) (hz : riemannZeta ρ = 0) (K : ℝ) :
    ∃ᶠ N : ℕ in atTop, K*(N:ℝ)^b < |filteredOrdinaryPrimes W f N| := by
  by_contra h
  obtain ⟨T,hT⟩ := eventually_atTop.mp (Filter.not_frequently.mp h)
  let S := ∑ j ∈ range T, |filteredOrdinaryPrimes W f j|
  have hS : 0 ≤ S := sum_nonneg fun j _ => abs_nonneg _
  refine (ordinaryPrime_count_bound_excludes_right_zero W f hnz hb hb1
    (K := |K|+S) ?_ hρ) hz
  intro N hN
  have hpow : 1 ≤ (N:ℝ)^b := Real.one_le_rpow (by exact_mod_cast hN) (by linarith only [hb])
  rcases lt_or_ge N T with hsmall | hlarge
  · have hNle : |filteredOrdinaryPrimes W f N| ≤ S :=
      single_le_sum (fun j _ => abs_nonneg (filteredOrdinaryPrimes W f j)) (mem_range.mpr hsmall)
    exact (hNle.trans (le_add_of_nonneg_left (abs_nonneg K))).trans
      (le_mul_of_one_le_right (add_nonneg (abs_nonneg K) hS) hpow)
  · exact (not_lt.mp (hT N hlarge)).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self K).trans (le_add_of_nonneg_right hS)) (zero_le_one.trans hpow))

private def logExcess (n : ℕ) : ℝ :=
  (if n.Prime then Real.log n else 0) - 1 + (if n = 1 then 1 else 0)

private theorem logExcess_sum {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, logExcess n) = Chebyshev.theta N - N + 1 := by
  simp only [logExcess, sum_add_distrib, sum_sub_distrib, ← sum_filter,
    ← Nat.primesLE_eq_filter_Icc_one, ← Chebyshev.theta_eq_sum_primesLE_log]
  simp [Finset.filter_eq', hN]

/-- Above the zero abscissa, Abel summation removes the prime logarithm
without changing the power bound. -/
private theorem ordinary_prefix_power {b : ℝ} (hb : RHTower.zeroReSup < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ordinaryPrimeCountWeight n| ≤ K*(N:ℝ)^b := by
  obtain ⟨A,hA,hψ⟩ := RHTower.exists_abs_chebyshevPsi_sub_le_rpow hb
  obtain ⟨B,hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hb2 := RHTower.half_le_zeroReSup.trans hb.le
  have hb0 : 0 ≤ b := by linarith only [hb2]
  let C := A + |B| + 1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let w := fun n : ℕ => (Real.log (max n 2 : ℕ))⁻¹
  have hw (n : ℕ) : 0 < Real.log (max n 2 : ℕ) := Real.log_pos
    (by exact_mod_cast (show 1 < max n 2 from (by decide : 1 < 2).trans_le (le_max_right _ _)))
  refine ⟨C*w 1, mul_nonneg hC (inv_nonneg.mpr (hw 1).le), fun N hN => ?_⟩
  have hprefix (j : ℕ) (hj : j ≤ N) : |∑ n ∈ Icc 1 j, logExcess n| ≤ C*(N:ℝ)^b := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg N) b)
    have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj0
    have hpow : (j:ℝ)^b ≤ (N:ℝ)^b := Real.rpow_le_rpow (Nat.cast_nonneg j) (by exact_mod_cast hj) hb0
    have hs : Real.sqrt j ≤ (j:ℝ)^b := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hj1 hb2
    have hB' := (hB j).trans ((mul_le_mul_of_nonneg_right (le_abs_self B) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hs (abs_nonneg B)))
    have hone := Real.one_le_rpow hj1 hb0
    obtain ⟨hlo,hhi⟩ := abs_le.mp (hψ j hj1)
    rw [logExcess_sum hj0]
    apply le_trans _ (mul_le_mul_of_nonneg_left hpow hC)
    dsimp only [C]
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi,hB',Chebyshev.theta_le_psi j,hone,
      mul_nonneg (abs_nonneg B) (Real.rpow_nonneg (Nat.cast_nonneg j) b)]
  have hab := RHTower.abs_sum_mul_le_of_antitone (a := logExcess) (w := w) hN hprefix
    (fun k _ _ => inv_nonneg.mpr (hw k).le) (fun k _ _ => inv_anti₀ (hw k)
      (Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (le_max_right k 2)))
        (by exact_mod_cast max_le_max_right 2 (Nat.le_succ k))))
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) : ordinaryPrimeCountWeight n = logExcess n*w n := by
    by_cases h : n = 1
    · simp [h,ordinaryPrimeCountWeight_apply,logExcess,Nat.not_prime_one]
    have hn2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
    rw [ordinaryPrimeCountWeight_apply]
    dsimp only [logExcess,w]
    rw [max_eq_left hn2, if_neg h]
    split_ifs <;> field_simp [hlog] <;> ring
  rw [sum_congr rfl hterm]
  exact hab.trans_eq (by ring)

theorem filteredOrdinaryPrimes_power_above_abscissa {b : ℝ} (hb : RHTower.zeroReSup < b)
    (W : ℕ) (f : ArithmeticFunction ℝ) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → |filteredOrdinaryPrimes W f N| ≤ K*(N:ℝ)^b := by
  obtain ⟨A,hA,ha⟩ := ordinary_prefix_power hb
  have hb0 : 0 ≤ b := by linarith only [RHTower.half_le_zeroReSup,hb]
  refine ⟨(∑ d ∈ Icc 1 W, |f d|)*A, fun N _ => ?_⟩
  simp only [filteredOrdinaryPrimes_eq, ← prefix_count_weight, mul_assoc]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Icc 1 (min N W), |f d| * (A*(N:ℝ)^b) := by
      apply sum_le_sum
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hdN := (mem_Icc.mp hd).2.trans (min_le_left N W)
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (ha _ ((Nat.one_le_div_iff hd0).mpr hdN)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self N d) hb0) hA)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg
        (Icc_subset_Icc_right (min_le_right N W)) (fun d _ _ => abs_nonneg (f d))) (by positivity)

/-- Every fixed, nonzero finite cofactor gives an RH criterion using the
ordinary prime-counting function. The cutoff and the coefficients are fixed
before the exponent is chosen. -/
theorem riemannHypothesis_iff_one_filtered_ordinary_prime_count (W : ℕ) (f : ArithmeticFunction ℝ)
    (hnz : ∃ d ∈ Icc 1 W, f d ≠ 0) :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/2 < b → b < 1 → ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |filteredOrdinaryPrimes W f N| ≤ K*(N:ℝ)^b := by
  constructor
  · intro hRH b hb _
    have hΘ := RHTower.zeroReSup_le_of_forall_re_le fun q =>
      (RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q).le
    exact filteredOrdinaryPrimes_power_above_abscissa (hΘ.trans_lt hb) W f
  · intro h
    apply RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro ρ hρ hhi
    obtain ⟨b,hb,hbρ⟩ := exists_between hρ
    obtain ⟨K,hK⟩ := h b hb (hbρ.trans hhi)
    exact ordinaryPrime_count_bound_excludes_right_zero W f hnz hb.le (hbρ.trans hhi) hK hbρ

#print axioms ordinaryPrime_count_bound_excludes_right_zero
#print axioms filteredOrdinaryPrimes_frequently_large_at_right_zero
#print axioms riemannHypothesis_iff_one_filtered_ordinary_prime_count

end GaloisForLFunctions.ExceptionalLayerTheory
