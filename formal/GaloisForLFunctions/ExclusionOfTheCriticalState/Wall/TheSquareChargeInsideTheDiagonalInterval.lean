import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.APositiveCompletePrefixInTheOriginalTest
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheUnchargedMiddleIntegralOfTheOriginalTest

/-!
# The square charge in the central integer interval

The proper prime powers sample half the state density. In the original
moving-edge test their log displacement from the test center has a limiting
distribution. Integer cutoffs receding on both sides retain its whole mass.
-/

noncomputable section
open scoped Classical
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry
  CriticalArithmeticCorrelationTheory _root_.RHTower

private abbrev Powers := Nat.Primes × ℕ
private abbrev idx (j : Powers) := properPrimePowerIndex j
private abbrev weight (j : Powers) := vonMangoldtAtom (idx j)
private abbrev wave (f : ℝ → ℝ) (t : ℝ) := ∑' j : Powers, weight j*f (t-Real.log (idx j))
private abbrev kept (k L n : ℕ) (t : ℝ) := k<n ∧ n≤L ∧ pastCriticalEdge n t

/-- Proper prime powers inside an integer band beyond the moving wall.
The function b reads their logarithmic displacement from the test center. -/
def properPowerBandReading (Φ b : ℝ → ℝ) (k L : ℕ) (T t : ℝ) : ℝ :=
  ∑' j : Nat.Primes × ℕ, if kept k L (idx j) t then
    weight j*(Φ (t-Real.log (idx j))*b (Real.log (idx j)-T)) else 0

private theorem weight_nonneg (j : Powers) : 0 ≤ weight j := by
  unfold weight vonMangoldtAtom
  split_ifs <;> first | exact le_rfl | exact div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)

private theorem relative_edge_tends_to_zero :
    Tendsto (fun t : ℝ => Real.exp (-t/2)*Real.sqrt t) atTop (𝓝 0) := by
  have hlim := Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/4:ℝ)<0))
  apply squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  have hroot : Real.sqrt t ≤ Real.exp (t/4) := by
    have h : t ≤ (1+t/4)^2 := by nlinarith only [sq_nonneg (1-t/4)]
    exact (Real.sqrt_le_sqrt h).trans (by
      rw [Real.sqrt_sq (by linarith only [ht] : 0 ≤ 1+t/4)]
      linarith only [Real.add_one_le_exp (t/4)])
  apply (mul_le_mul_of_nonneg_left hroot (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]; change Real.exp _ = Real.exp ((-1/4)*t); congr 1; ring

/-- Every fixed nonzero level of the continuous state is eventually inside
both integer cutoffs and strictly beyond the moving wall. -/
private theorem high_values_kept {Φ : ℝ → ℝ} (hc : Continuous Φ) (hs : ∀ v, 0 ≤ v → Φ v=0)
    {C : ℝ} (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v)) {T : ℕ → ℝ} {k L : ℕ → ℕ}
    (hT : Tendsto T atTop atTop) (hk : Tendsto (fun i => T i-Real.log (k i)) atTop atTop)
    (hL : Tendsto (fun i => Real.log (L i)-T i) atTop atTop) (r : ℝ) {z : ℝ} (hz : 0<z) :
    ∀ᶠ i in atTop, ∀ j : Powers, z < |Φ (T i-r-Real.log (idx j))| → kept (k i) (L i) (idx j) (T i-r) := by
  have hsmall : ∀ᶠ v : ℝ in 𝓝 0, |Φ v| < z := hc.abs.continuousAt.eventually_lt_const
    (by simpa only [hs 0 le_rfl,abs_zero] using hz)
  obtain ⟨D,hD,hball⟩ := Metric.mem_nhds_iff.mp hsmall
  have hdec := ((Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atBot (by norm_num : (0:ℝ)<2))).const_mul C)
  obtain ⟨A,hA⟩ := eventually_atBot.mp (hdec.eventually_lt_const (by simpa only [mul_zero] using hz))
  have ht : Tendsto (fun i => T i-r) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-r) hT
  have hw := (relative_edge_tends_to_zero.comp ht).eventually_lt_const
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr hD))
  filter_upwards [hk.eventually_ge_atTop (r+1),hL.eventually_ge_atTop (1-r-A),
      hT.eventually_ge_atTop (r+A+2),hw] with i hiK hiL hiT hwidth
  intro j hj
  let t := T i-r
  let n := idx j
  let u := t-Real.log n
  change z < |Φ u| at hj
  have hu : u<0 := lt_of_not_ge fun h => by rw [hs _ h,abs_zero] at hj; linarith only [hz,hj]
  have hleft : A<u := lt_of_not_ge fun h => by
    have hx := (hb u).trans_lt (hA u h)
    exact (not_lt_of_ge hj.le) hx
  have hnear : u ≤ -D := by
    by_contra! h
    have hm : u ∈ Metric.ball (0:ℝ) D := by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_neg hu]; linarith only [h]
    exact (not_lt_of_ge hj.le) (hball hm)
  have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr (pow_pos j.1.property.pos _)
  have hklog : Real.log (k i) < Real.log n := by
    change r+1 ≤ T i-Real.log (k i) at hiK
    dsimp only [u,t] at hu; linarith only [hu,hiK]
  have hlogL : Real.log n ≤ Real.log (L i) := by
    change 1-r-A ≤ Real.log (L i)-T i at hiL
    dsimp only [u,t] at hleft; linarith only [hleft,hiL]
  have hL0 : 0 < L i := by
    by_contra! h
    have hzero := Nat.eq_zero_of_le_zero h
    change 1-r-A ≤ Real.log (L i)-T i at hiL
    rw [hzero,Nat.cast_zero,Real.log_zero] at hiL
    linarith only [hiT,hiL]
  refine ⟨?_,?_,?_⟩
  · rcases Nat.eq_zero_or_pos (k i) with h | h
    · rw [h]; exact Nat.cast_pos.mp hn0
    · exact Nat.cast_lt.mp ((Real.log_lt_log_iff (Nat.cast_pos.mpr h) hn0).mp hklog)
  · exact Nat.cast_le.mp ((Real.log_le_log_iff hn0 (Nat.cast_pos.mpr hL0)).mp hlogL)
  · change Real.exp t+Real.exp (t/2)*Real.sqrt t < (n:ℝ)
    change Real.exp (-t/2)*Real.sqrt t < Real.exp D-1 at hwidth
    have hfact : Real.exp t*Real.exp (-t/2)=Real.exp (t/2) := by rw [← Real.exp_add]; congr 1; ring
    have hfar : Real.exp t*Real.exp D ≤ n := by
      rw [← Real.exp_add,← Real.le_log_iff_exp_le hn0]; dsimp only [u] at hnear; linarith only [hnear]
    rw [← hfact]
    linarith only [mul_lt_mul_of_pos_left hwidth (Real.exp_pos t),hfar]

private theorem measurable_reading {Φ b : ℝ → ℝ} (hc : Continuous Φ) (k L : ℕ) (T : ℝ) :
    Measurable (properPowerBandReading Φ b k L T) := by
  apply Measurable.tsum
  intro j
  have hedge : MeasurableSet {t : ℝ | pastCriticalEdge (idx j) t} :=
    measurableSet_lt (by fun_prop : Measurable fun t : ℝ => Real.exp t+Real.exp (t/2)*Real.sqrt t)
      measurable_const
  apply Measurable.ite ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter hedge))
  · exact measurable_const.mul ((hc.measurable.comp (measurable_id.sub measurable_const)).mul_const _)
  · exact measurable_const

private theorem abs_tsum_majorized {a q : Powers → ℝ} (hq : Summable q)
    (h : ∀ j, |a j| ≤ q j) : |∑' j, a j| ≤ ∑' j, q j := by
  have hs := Summable.of_nonneg_of_le (fun j => abs_nonneg (a j)) h hq
  have hn : Summable (fun j => ‖a j‖) := by simpa only [Real.norm_eq_abs] using hs
  exact (show |∑' j, a j| ≤ ∑' j, |a j| by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn).trans (hs.tsum_le_tsum h hq)

/-- A bounded continuous reading of the displacement is a fixed profile test
at each translated time. Clipping the absolute profile controls all atoms
that the varying band or wall removes. -/
private theorem translated_band_limit {Φ b : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (hs : ∀ v, 0 ≤ v → Φ v=0) {C : ℝ} (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v))
    (hsum : ∀ t, Summable (fun j : Powers => weight j*|Φ (t-Real.log (idx j))|))
    (hp : ∀ f : ℝ → ℝ, Continuous f → (∀ u, |f u| ≤ |Φ u|) →
      Tendsto (wave f) atTop (𝓝 ((∫ v, f v)/2))) (hbc : Continuous b) (hb1 : ∀ s, |b s| ≤ 1)
    {T : ℕ → ℝ} {k L : ℕ → ℕ} (hT : Tendsto T atTop atTop)
    (hk : Tendsto (fun i => T i-Real.log (k i)) atTop atTop)
    (hL : Tendsto (fun i => Real.log (L i)-T i) atTop atTop) (r : ℝ) :
    Tendsto (fun i => properPowerBandReading Φ b (k i) (L i) (T i) (T i-r))
      atTop (𝓝 ((∫ v, Φ v*b (-r-v))/2)) := by
  let g := fun v => Φ v*b (-r-v)
  have hgc : Continuous g := hc.mul (hbc.comp (continuous_const.sub continuous_id))
  have hg (v : ℝ) : |g v| ≤ |Φ v| := by
    rw [show |g v|=|Φ v| *|b (-r-v)| from abs_mul ..]
    exact mul_le_of_le_one_right (abs_nonneg _) (hb1 _)
  let z := fun j : ℕ => Real.exp (-(j:ℝ))
  let cut := fun (j : ℕ) (v : ℝ) => min |Φ v| (z j)
  have hc₁ (j : ℕ) : Continuous (cut j) := hc.abs.min continuous_const
  have hn (j : ℕ) (v : ℝ) : 0 ≤ cut j v := le_min (abs_nonneg _) (Real.exp_pos _).le
  have hdom (j : ℕ) (v : ℝ) : |cut j v| ≤ |Φ v| := (abs_of_nonneg (hn j v)).le.trans (min_le_left ..)
  have hz : Tendsto z atTop (𝓝 0) := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hcut : Tendsto (fun j => ∫ v, cut j v) atTop (𝓝 0) := by
    have hpt (v : ℝ) : Tendsto (fun j => cut j v) atTop (𝓝 0) := by
      simpa only [min_eq_right (abs_nonneg (Φ v))] using
        (tendsto_const_nhds (x := |Φ v|)).min hz
    simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence (fun v => |Φ v|)
      (Eventually.of_forall fun j => (hc₁ j).aestronglyMeasurable)
      (Eventually.of_forall fun j => Eventually.of_forall fun v => (Real.norm_eq_abs _).le.trans (hdom j v))
      hi.abs (Eventually.of_forall hpt)
  have ht : Tendsto (fun i => T i-r) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-r) hT
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨j,hj⟩ := (hcut.eventually_lt_const hε).exists
  have hclip := (hp (cut j) (hc₁ j) (hdom j)).comp ht
  have hfull := (hp g hgc hg).comp ht
  filter_upwards [hclip.eventually_lt_const (show (∫ v, cut j v)/2 < ε/2 by linarith only [hj]),
    hfull.eventually (Metric.ball_mem_nhds _ (half_pos hε)),
    high_values_kept hc hs hb hT hk hL r (Real.exp_pos (-(j:ℝ)))] with i hclipi hfulli hkeep
  let t := T i-r
  let a := fun p : Powers => weight p*g (t-Real.log (idx p))
  let mask := fun p : Powers => kept (k i) (L i) (idx p) t
  let q := fun p : Powers => weight p*|Φ (t-Real.log (idx p))|
  have ha (p : Powers) : |a p| ≤ q p := by
    rw [show |a p|=|weight p| *|g (t-Real.log (idx p))| from abs_mul ..,abs_of_nonneg (weight_nonneg p)]
    exact mul_le_mul_of_nonneg_left (hg _) (weight_nonneg _)
  have ham (p : Powers) : |(if mask p then a p else 0)| ≤ q p := by
    split_ifs; exact ha p; exact (abs_zero.le.trans ((abs_nonneg _).trans (ha p)))
  have hasum : Summable a := Summable.of_norm_bounded (hsum t) fun p => (Real.norm_eq_abs _).le.trans (ha p)
  have hmsum : Summable (fun p => if mask p then a p else 0) :=
    Summable.of_norm_bounded (hsum t) fun p => (Real.norm_eq_abs _).le.trans (ham p)
  have hcsum : Summable (fun p => weight p*cut j (t-Real.log (idx p))) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (weight_nonneg _) (hn _ _))
      (fun p => mul_le_mul_of_nonneg_left (min_le_left ..) (weight_nonneg p)) (hsum t)
  have hid : properPowerBandReading Φ b (k i) (L i) (T i) t =
      ∑' p, if mask p then a p else 0 := by
    apply tsum_congr
    intro p
    have he : -r-(t-Real.log (idx p))=Real.log (idx p)-T i := by dsimp only [t]; ring
    simp only [mask,a,g,he]
  have herr : |properPowerBandReading Φ b (k i) (L i) (T i) t-wave g t| ≤ wave (cut j) t := by
    rw [hid,← hmsum.tsum_sub hasum]
    apply abs_tsum_majorized hcsum
    intro p
    by_cases hm : mask p
    · rw [if_pos hm,sub_self,abs_zero]; exact mul_nonneg (weight_nonneg _) (hn _ _)
    · rw [if_neg hm,zero_sub,abs_neg]
      have h : |Φ (t-Real.log (idx p))| ≤ z j := le_of_not_gt fun hv => hm (hkeep p hv)
      dsimp only [cut]; rw [min_eq_left h]; exact ha p
  change wave (cut j) t < ε/2 at hclipi
  change dist (wave g t) ((∫ v, g v)/2) < ε/2 at hfulli
  change dist (properPowerBandReading Φ b (k i) (L i) (T i) t) ((∫ v, g v)/2) < ε
  have htri := dist_triangle (properPowerBandReading Φ b (k i) (L i) (T i) t)
    (wave g t) ((∫ v, g v)/2)
  rw [Real.dist_eq] at hfulli ⊢
  simp only [Real.dist_eq] at htri
  linarith only [herr,hclipi,hfulli,htri]

/-- Against every bounded continuous displacement test, the limiting
proper-power density in the original integral is the convolution of the
state with the original fractional-part kernel, with coefficient one half. -/
theorem criticalState_properPowerBand_displacement_limit {W : ℝ} (hW : 0<W)
    (ht : (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {b : ℝ → ℝ} (hbc : Continuous b) (hb1 : ∀ s, |b s| ≤ 1)
    {T : ℕ → ℝ} {k L : ℕ → ℕ} (hT : Tendsto T atTop atTop)
    (hk : Tendsto (fun i => T i-Real.log (k i)) atTop atTop)
    (hL : Tendsto (fun i => Real.log (L i)-T i) atTop atTop) :
    Tendsto (fun i => (∫ t in Ioc (T i/6) (6*T i),
      properPowerBandReading Φ b (k i) (L i) (T i) t*fractionalPrimeTest (T i-t))) atTop
      (𝓝 (∫ r, ((∫ v, Φ v*b (-r-v))/2)*fractionalPrimeTest r)) := by
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  obtain ⟨Ψ,hΨ,heΨ,hp⟩ := criticalState_tendsto_dominated_properPowerWave hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  have hi := (criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he
  obtain ⟨M,hM,habs⟩ := properPowerWave_absolute_envelope (by norm_num : (0:ℝ)<2) hC hb
  let Q := wave (fun v => |Φ v|)
  have hQ := hp (fun v => |Φ v|) hc.abs (fun v => (abs_abs _).le)
  obtain ⟨U,hU⟩ := eventually_atTop.mp (hQ.eventually_lt_const (lt_add_one ((∫ v, |Φ v|)/2)))
  let B := max ((∫ v, |Φ v|)/2+1) (M*Real.exp (2*U))
  have hB (t : ℝ) : Q t ≤ B := by
    rcases le_or_gt U t with h | h
    · exact (hU _ h).le.trans (le_max_left ..)
    · exact (habs t).2.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (by linarith only [h] : 2*t≤2*U)) hM).trans (le_max_right ..))
  let A := fun i => Ioc (T i/6) (6*T i)
  let row := fun i => properPowerBandReading Φ b (k i) (L i) (T i)
  have hrow (i : ℕ) (t : ℝ) : |row i t| ≤ B := by
    apply le_trans _ (hB t)
    apply abs_tsum_majorized (habs t).1
    intro j
    by_cases hj : kept (k i) (L i) (idx j) t
    · rw [if_pos hj,abs_mul,abs_mul,abs_of_nonneg (weight_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg _)
      exact mul_le_of_le_one_right (abs_nonneg _) (hb1 _)
    · rw [if_neg hj,abs_zero]; exact mul_nonneg (weight_nonneg _) (abs_nonneg _)
  let f := fun i (r : ℝ) => (A i).indicator (row i) (T i-r)*fractionalPrimeTest r
  have hmeas (i : ℕ) : Measurable (f i) :=
    (((measurable_reading hc _ _ _).indicator measurableSet_Ioc).comp
      (measurable_const.sub measurable_id)).mul measurable_fractionalPrimeTest
  have hbn : 0 ≤ B := (abs_nonneg _).trans (hrow 0 0)
  have hbound (i : ℕ) (r : ℝ) : ‖f i r‖ ≤ B*|fractionalPrimeTest r| := by
    dsimp only [f]; rw [Real.norm_eq_abs,abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    by_cases h : T i-r ∈ A i
    · rw [indicator_of_mem h]; exact hrow _ _
    · rw [indicator_of_notMem h,abs_zero]; exact hbn
  have hpt (r : ℝ) : Tendsto (fun i => f i r) atTop
      (𝓝 (((∫ v, Φ v*b (-r-v))/2)*fractionalPrimeTest r)) := by
    apply ((translated_band_limit hc hi hs hb (fun t => (habs t).1) hp hbc hb1 hT hk hL r).mul_const
      (fractionalPrimeTest r)).congr'
    filter_upwards [hT.eventually_ge_atTop (2*|r|+1)] with i h
    have hm : T i-r ∈ A i := ⟨by linarith only [h,le_abs_self r,abs_nonneg r],
      by linarith only [h,neg_abs_le r,abs_nonneg r]⟩
    dsimp only [f]; rw [indicator_of_mem hm]
  have hconv := tendsto_integral_filter_of_dominated_convergence (fun r => B*|fractionalPrimeTest r|)
    (Eventually.of_forall fun i => (hmeas i).aestronglyMeasurable)
    (Eventually.of_forall fun i => Eventually.of_forall (hbound i))
    (fractionalPrimeTest_mass.1.abs.const_mul B) (Eventually.of_forall hpt)
  apply hconv.congr
  intro i
  have hchange := integral_sub_left_eq_self (fun t => (A i).indicator (row i) t*
    fractionalPrimeTest (T i-t)) volume (T i)
  simp only [sub_sub_cancel] at hchange
  change (∫ r, (A i).indicator (row i) (T i-r)*fractionalPrimeTest r) = _
  rw [hchange]
  have heq (t : ℝ) : (A i).indicator (row i) t*fractionalPrimeTest (T i-t)=
      (A i).indicator (fun t => row i t*fractionalPrimeTest (T i-t)) t := by
    by_cases h : t ∈ A i <;> simp [h]
  simp_rw [heq]
  rw [integral_indicator measurableSet_Ioc]

/-- The ordinary primes in the same moving band, with one reference atom
at every integer. At a prime the Mangoldt coefficient is its logarithm. -/
def ordinaryPrimeComplementBand (Φ : ℝ → ℝ) (k L : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc k L, if pastCriticalEdge n t then
    ((if n.Prime then vonMangoldt n else 0)-1)*continuousIntegerAtom Φ n t else 0

private theorem band_difference (Φ : ℝ → ℝ) (k L : ℕ) (T t : ℝ) :
    finiteCriticalComplementBand Φ k L t-ordinaryPrimeComplementBand Φ k L t =
      properPowerBandReading Φ (fun _ => 1) k L T t := by
  classical
  let I := Finset.Ioc k L
  let a := fun n : ℕ => if ¬n.Prime ∧ pastCriticalEdge n t then vonMangoldt n*continuousIntegerAtom Φ n t else 0
  let f := fun n : ℕ => if n ∈ I then (a n:ℂ) else 0
  have hfz (n : ℕ) (hn : n ∉ I) : f n=0 := if_neg hn
  have hf : Summable f := summable_of_ne_finset_zero (s := I) hfz
  have hsp := tsum_eq_ordinary_primes_add_proper_powers hf (fun n hn => by
    by_contra hp
    apply hn
    simp only [f,a,vonMangoldt_eq_zero_iff.mpr hp,zero_mul,ite_self,Complex.ofReal_zero])
  have hpr (p : Nat.Primes) : f p=0 := by simp [f,a,p.property]
  simp_rw [hpr] at hsp
  rw [tsum_zero,zero_add,tsum_eq_sum hfz] at hsp
  have hleft : (∑ n ∈ I, f n)=((finiteCriticalComplementBand Φ k L t-ordinaryPrimeComplementBand Φ k L t:ℝ):ℂ) := by
    rw [finiteCriticalComplementBand,ordinaryPrimeComplementBand,← Finset.sum_sub_distrib,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [f]; rw [if_pos hn]
    by_cases hp : n.Prime <;> by_cases h : pastCriticalEdge n t <;> simp [a,hp,h]
    ring
  have he (j : Powers) : (vonMangoldt (idx j)*continuousIntegerAtom Φ (idx j) t) =
      weight j*Φ (t-Real.log (idx j)) := by
    have htwo : 2 ≤ idx j := j.1.property.two_le.trans
      (Nat.le_pow (by omega : 0<j.2+2))
    simp only [continuousIntegerAtom,weight,vonMangoldtAtom,if_pos htwo,div_eq_mul_inv,mul_assoc]
  have hright : (∑' j : Powers, f (idx j)) = (properPowerBandReading Φ (fun _ => 1) k L T t:ℂ) := by
    rw [properPowerBandReading,Complex.ofReal_tsum]
    apply tsum_congr
    intro j
    have hnp : ¬(idx j).Prime := Nat.Prime.not_prime_pow (by omega : 2≤j.2+2)
    dsimp only [f,a]
    by_cases hI : idx j ∈ I
    · obtain ⟨h₁,h₂⟩ := Finset.mem_Ioc.mp hI
      by_cases hE : pastCriticalEdge (idx j) t
      · have hboth : ¬(idx j).Prime ∧ pastCriticalEdge (idx j) t := ⟨hnp,hE⟩
        have hkept : kept k L (idx j) t := ⟨h₁,h₂,hE⟩
        rw [if_pos hI,if_pos hboth,if_pos hkept,mul_one,he j]
      · have hout : ¬kept k L (idx j) t := fun h => hE h.2.2
        have hmiss : ¬(¬(idx j).Prime ∧ pastCriticalEdge (idx j) t) := fun h => hE h.2
        rw [if_pos hI,if_neg hmiss,if_neg hout]
    · have hout : ¬kept k L (idx j) t := fun h => hI (Finset.mem_Ioc.mpr ⟨h.1,h.2.1⟩)
      simp only [if_neg hI,if_neg hout,Complex.ofReal_zero]
  rw [hleft,hright] at hsp
  exact Complex.ofReal_injective hsp

private theorem integrable_band {Φ : ℝ → ℝ} (hi : Integrable Φ)
    (c : ℕ → ℝ) (k L : ℕ) (T : ℝ) :
    Integrable (fun t => (∑ n ∈ Finset.Ioc k L, if pastCriticalEdge n t then
      c n*continuousIntegerAtom Φ n t else 0)*fractionalPrimeTest (T-t)) := by
  let K := fun t => fractionalPrimeTest (T-t)
  let g := fun (n : ℕ) (t : ℝ) => c n*continuousIntegerAtom Φ n t*K t
  let E := fun n : ℕ => {t : ℝ | pastCriticalEdge n t}
  have hE (n : ℕ) : MeasurableSet (E n) := measurableSet_lt
    (by fun_prop : Measurable fun t : ℝ => Real.exp t+Real.exp (t/2)*Real.sqrt t) measurable_const
  have hgi (n : ℕ) : Integrable (g n) := by
    let a := fun t => c n*continuousIntegerAtom Φ n t
    have hai : Integrable a := ((hi.comp_sub_right (Real.log n)).const_mul _).const_mul _
    have hm : Measurable K := measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id)
    apply hai.abs.mono' (hai.aestronglyMeasurable.mul hm.aestronglyMeasurable)
    apply Eventually.of_forall
    intro t
    change |a t*K t| ≤ |a t|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (fractionalPrimeTest_bounds _).1
  apply (integrable_finsetSum (Finset.Ioc k L) (fun n _ => (hgi n).indicator (hE n))).congr
  apply Eventually.of_forall
  intro t
  dsimp only []
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : pastCriticalEdge n t
  · rw [indicator_of_mem (show t∈E n from h),if_pos h]
  · rw [indicator_of_notMem (show t∉E n from h),if_neg h,zero_mul]

/-- In every expanding log window the whole proper-power correction, including
the moving edge and the middle time cut, tends to the opposite of the
ordinary-prime square charge. -/
theorem criticalState_charge_inside_integer_band {W : ℝ} (hW : 0<W)
    (ht : (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {T : ℕ → ℝ} {k L : ℕ → ℕ} (hT : Tendsto T atTop atTop)
    (hk : Tendsto (fun i => T i-Real.log (k i)) atTop atTop)
    (hL : Tendsto (fun i => Real.log (L i)-T i) atTop atTop) :
    let m := ∫ v, Φ v
    Tendsto (fun i => m*(∫ t in Ioc (T i/6) (6*T i),
      finiteCriticalComplementBand Φ (k i) (L i) t*fractionalPrimeTest (T i-t))-
      m*(∫ t in Ioc (T i/6) (6*T i),
      ordinaryPrimeComplementBand Φ (k i) (L i) t*fractionalPrimeTest (T i-t)))
      atTop (𝓝 (-(riemannZeta (1/2)).re*m^2)) := by
  let m := ∫ v, Φ v
  have hi := (criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he
  have hlim := (criticalState_properPowerBand_displacement_limit hW ht hF hc he
    (b := fun _ => 1) continuous_const (fun _ => abs_one.le) hT hk hL).const_mul m
  simp only [mul_one,integral_const_mul,fractionalPrimeTest_mass.2] at hlim
  have hval : m*((m/2)*(-2*(riemannZeta (1/2)).re))= -(riemannZeta (1/2)).re*m^2 := by ring
  change Tendsto _ atTop (𝓝 (-(riemannZeta (1/2)).re*m^2))
  rw [← hval]
  apply hlim.congr
  intro i
  let S := Ioc (T i/6) (6*T i)
  let K := fun t => fractionalPrimeTest (T i-t)
  have hA : IntegrableOn (fun t => finiteCriticalComplementBand Φ (k i) (L i) t*K t) S :=
    (integrable_band hi (fun n => vonMangoldt n-1) (k i) (L i) (T i)).integrableOn
  have hB : IntegrableOn (fun t => ordinaryPrimeComplementBand Φ (k i) (L i) t*K t) S :=
    (integrable_band hi (fun n => (if n.Prime then vonMangoldt n else 0)-1) (k i) (L i) (T i)).integrableOn
  rw [← mul_sub]
  apply congrArg (m*·)
  rw [← integral_sub hA hB]
  apply integral_congr_ae (Eventually.of_forall fun t => ?_)
  rw [← sub_mul,band_difference Φ (k i) (L i) (T i) t]

/-- On the same tests with a positive exterior gain, all proper powers inside
the isolated interval supply their full limiting charge. The ordinary primes
against the unit reference must incur a power-sized deficit in that interval. -/
theorem riemannHypothesis_or_ordinary_prime_diagonal_band : RiemannHypothesis ∨
    ∃ (W : ℝ) (F Φ : ℝ → ℝ) (c g : ℝ), 0<W ∧
      (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W:EReal) ∧ IsCriticalHalfLineGroundState W F ∧
      Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0<c ∧ 0<g ∧ ∀ η : ℝ, 0<η → η≤1 →
      ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η) ≤ Real.log (k i) ∧ Real.log (k i) ≤ T i) ∧
        let m := ∫ v, Φ v
        let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
        let total := fun i => m*(∫ t in Ioc (T i/6) (6*T i),
          criticalComplementBand Φ 0 t*fractionalPrimeTest (T i-t))
        let band := fun i => m*(∫ t in Ioc (T i/6) (6*T i),
          finiteCriticalComplementBand Φ (k i) (L i) t*fractionalPrimeTest (T i-t))
        let ordinary := fun i => m*(∫ t in Ioc (T i/6) (6*T i),
          ordinaryPrimeComplementBand Φ (k i) (L i) t*fractionalPrimeTest (T i-t))
        (∀ i, c*Real.exp (g*T i) ≤ total i-band i) ∧
        Tendsto (fun i => band i-ordinary i) atTop (𝓝 (-(riemannZeta (1/2)).re*m^2)) ∧
        Tendsto (fun i => ordinary i+(total i-band i)) atTop (𝓝 ((riemannZeta (1/2)).re*m^2)) ∧
        ∀ ε : ℝ, 0<ε → ∀ᶠ i in atTop,
          ordinary i ≤ (riemannZeta (1/2)).re*m^2-c*Real.exp (g*T i)+ε := by
  rcases riemannHypothesis_or_uncharged_middle_tends_to_zero with hRH | hzero
  · exact Or.inl hRH
  rcases riemannHypothesis_or_diagonal_positive_prefix with hr | ⟨W,F,Φ,c,g,hW,ht,hF,hc,he,hc₀,hg,h⟩
  · exact Or.inl hr
  refine Or.inr ⟨W,F,Φ,c,g/2,hW,ht,hF,hc,he,hc₀,by positivity,fun η hη hη1 => ?_⟩
  obtain ⟨δ₀,hδ₀,hh⟩ := h η hη hη1
  let δ := min (δ₀/2) (η/2)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  have hsmall : δ<δ₀ := (min_le_left _ _).trans_lt (by linarith only [hδ₀])
  have hgap : 0<η-δ := by dsimp only [δ]; linarith only [min_le_right (δ₀/2) (η/2),hη]
  let m := ∫ v, Φ v
  let L := fun t : ℝ => ⌈Real.exp ((1+η)*t)⌉₊
  let total := fun T => m*(∫ t in Ioc (T/6) (6*T), criticalComplementBand Φ 0 t*fractionalPrimeTest (T-t))
  let band := fun (T : ℝ) (N : ℕ) => m*(∫ t in Ioc (T/6) (6*T),
    finiteCriticalComplementBand Φ N (L T) t*fractionalPrimeTest (T-t))
  let ordinary := fun (T : ℝ) (N : ℕ) => m*(∫ t in Ioc (T/6) (6*T),
    ordinaryPrimeComplementBand Φ N (L T) t*fractionalPrimeTest (T-t))
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hex (j : ℕ) : ∃ (N : ℕ) (T : ℝ), (j:ℝ) ≤ Real.log N ∧
      (1+δ)*Real.log N ≤ T ∧ T ≤ (1+η)*Real.log N ∧ c*Real.exp (g/2*T) ≤ total T-band T N := by
    obtain ⟨N,hN,hj,hd,hN0⟩ := ((hh δ hδ hsmall).and_eventually
      ((hlog.eventually_ge_atTop (j:ℝ)).and (((hlog.const_mul_atTop hgap).eventually_ge_atTop 1).and
        (eventually_ge_atTop (1:ℕ))))).exists
    obtain ⟨T,hT,_,hpay⟩ := hN
    change 1 ≤ (η-δ)*Real.log N at hd
    have hhi : T ≤ (1+η)*Real.log N := by linarith only [hT.2,hd]
    refine ⟨N,T,hj,hT.1,hhi,le_trans ?_ hpay⟩
    apply mul_le_mul_of_nonneg_left _ hc₀.le
    rw [Real.rpow_def_of_pos (by exact_mod_cast hN0 : 0<(N:ℝ)),Real.exp_le_exp]
    have h₂ : T ≤ 2*Real.log N := by linarith only [hhi,mul_le_mul_of_nonneg_right hη1 (Real.log_natCast_nonneg N)]
    linarith only [mul_le_mul_of_nonneg_left h₂ hg.le]
  choose k T hj hlo hhi hgain using hex
  have hq : Tendsto (fun i => Real.log (k i)) atTop atTop :=
    tendsto_atTop_mono hj (tendsto_natCast_atTop_atTop (R := ℝ))
  have hqT (i : ℕ) : Real.log (k i) ≤ T i := by
    linarith only [hlo i,mul_nonneg hδ.le (Real.log_natCast_nonneg (k i))]
  have hT := tendsto_atTop_mono hqT hq
  have hk : Tendsto (fun i => T i-Real.log (k i)) atTop atTop :=
    tendsto_atTop_mono (fun i => by linarith only [hlo i]) (hq.const_mul_atTop hδ)
  have hL : Tendsto (fun i => Real.log (L (T i))-T i) atTop atTop := by
    apply tendsto_atTop_mono _ (hT.const_mul_atTop hη)
    intro i
    have hx : Real.exp ((1+η)*T i) ≤ L (T i) := Nat.le_ceil _
    have hp := (Real.exp_pos _).trans_le hx
    linarith only [(Real.le_log_iff_exp_le hp).mpr hx]
  refine ⟨T,k,hT,fun i => ⟨(div_le_iff₀ (by linarith only [hη] : 0<1+η)).mpr
    (by linarith only [hhi i]),hqT i⟩,?_⟩
  have hcharge : Tendsto (fun i => band (T i) (k i)-ordinary (T i) (k i)) atTop
      (𝓝 (-(riemannZeta (1/2)).re*m^2)) := criticalState_charge_inside_integer_band hW ht hF hc he hT hk hL
  have hz : Tendsto (fun i => total (T i)) atTop (𝓝 0) := (hzero hW ht hF hc he).comp hT
  have hnet : Tendsto (fun i => ordinary (T i) (k i)+(total (T i)-band (T i) (k i)))
      atTop (𝓝 ((riemannZeta (1/2)).re*m^2)) := by
    have hval : (0:ℝ)-(-(riemannZeta (1/2)).re*m^2)=(riemannZeta (1/2)).re*m^2 := by ring
    rw [← hval]
    apply (hz.sub hcharge).congr
    intro i
    ring
  refine ⟨hgain,hcharge,hnet,fun ε hε => ?_⟩
  filter_upwards [hnet.eventually_lt_const (lt_add_of_pos_right ((riemannZeta (1/2)).re*m^2) hε)] with i hi
  change ordinary (T i) (k i) ≤ (riemannZeta (1/2)).re*m^2-c*Real.exp (g/2*T i)+ε
  linarith only [hi,hgain i]

#print axioms criticalState_properPowerBand_displacement_limit
#print axioms criticalState_charge_inside_integer_band
#print axioms riemannHypothesis_or_ordinary_prime_diagonal_band
end GaloisForLFunctions.ExclusionOfTheCriticalState
