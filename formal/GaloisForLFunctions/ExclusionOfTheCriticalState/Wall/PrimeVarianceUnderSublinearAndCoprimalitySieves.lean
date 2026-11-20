import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.AdaptiveCoprimalityModuliPreservePrimeVariance
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.QuadraticHeightSievesInPrimeSquareMean
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# Sublinear sieves, coprimality moduli and the quadratic horizon

A common sieve by a finite prime set `P` changes the late weighted variance of
the ordinary-prime wave by at most `M 16^{|P|} e^{-rU}` on `[U, ∞)`.

* Every sieve with `|P| ≤ κT` primes, of arbitrary size, changes the variance on
  the whole ray `[ηT, ∞)` by an exponentially small amount; this covers every
  set of primes up to `T` by Chebyshev's bound `π(T) ≪ T / log T`.
* Weighting each sieve by `(∏_{p ∈ P} p)^{-s}`, `s > 1`, makes the total
  discrepancy of all finite sieves summable and integrable at once (Tonelli,
  the weights sum to `∏_p (1 + 16 p^{-s})`). Hence sieving by coprimality to any
  measurable integer modulus `q(t) ≤ e^{γt}` keeps an integrable variance error
  at every rate `b < 1 − Θ − γ`.
* For every prime set below `T²` the deleted primes cost `O(T²)` in `L²`, and on
  every scale where one of the two variances on `(0, T]` exceeds `e^{2δT}` their
  ratio tends to one, uniformly in the sieve.
-/

noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

theorem measurable_ordinaryPrimePolarError {Φ : ℝ → ℝ} (hc : Continuous Φ) :
    Measurable (ordinaryPrimePolarError Φ) := by
  have hmW : Measurable (ordinaryPrimeWave Φ) := Measurable.tsum fun q : Nat.Primes =>
    measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hc.measurable.comp (by fun_prop)))
  exact (Complex.continuous_re.measurable.comp hmW).sub (by fun_prop)

theorem measurable_commonSievedPrimeError {Φ : ℝ → ℝ} (hc : Continuous Φ) (P : Finset Nat.Primes) :
    Measurable (commonSievedPrimeError P Φ) := by
  have hΦ := hc.measurable
  have hmW : Measurable (ordinaryPrimeWave Φ) := Measurable.tsum fun q : Nat.Primes =>
    measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hΦ.comp (by fun_prop)))
  have hatom (x : ℝ) : Measurable (fun t => continuousIntegerAtom Φ x t) := by
    unfold continuousIntegerAtom; fun_prop
  have hrem : Measurable (removedPrimeWave P Φ) := by
    unfold removedPrimeWave
    exact Finset.measurable_sum _ fun p _ => measurable_const.mul (hatom _)
  have href : Measurable (sievedIntegerReference P Φ) := by
    unfold sievedIntegerReference sievedSum
    refine (Measurable.tsum fun n => ?_).div_const _
    by_cases hn : n ∈ {n : ℕ | Nat.Coprime n (sievePrimorial P)}
    · simp only [Set.indicator_of_mem hn]; exact hatom _
    · simp only [Set.indicator_of_notMem hn]; exact measurable_const
  unfold commonSievedPrimeError
  exact ((Complex.continuous_re.measurable.comp hmW).sub hrem).sub href

/-- Every common sieve with at most `κT` primes, of arbitrary size, changes the
variance on the ray `[ηT, ∞)` by at most `e^{-δT}`. The positive rate comes from
the unconditional zero-abscissa bound `Θ < 1`. -/
theorem criticalState_commonSieve_sublinear_tail {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {η : ℝ} (hη : 0 < η) :
    ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧ ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes, (P.card:ℝ) ≤ κ*T →
      IntegrableOn (fun t => |(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) (Ioi (η*T)) ∧
      (∫ t in Ioi (η*T), |(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) ≤
        Real.exp (-(δ*T)) := by
  let r : ℝ := 1/16
  have hr' : r < 1-zetaZeroAbscissa := by
    have h := ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths
    dsimp only [r]; linarith only [h]
  obtain ⟨M,hM,hmom⟩ := criticalState_commonSieve_variance_bound hW ht hF hc he hC hb
    (by norm_num : (0:ℝ) ≤ r) hr'
  let L := Real.log 16
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hL0 : L ≠ 0 := hL.ne'
  have hL16 : Real.exp L = 16 := Real.exp_log (by norm_num)
  have hrη : 0 < r*η := mul_pos (by norm_num) hη
  refine ⟨r*η/(4*L),r*η/2,div_pos hrη (mul_pos four_pos hL),half_pos hrη,?_⟩
  have hgrow : Tendsto (fun T : ℝ => Real.exp ((r*η/4)*T)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (div_pos hrη four_pos))
  filter_upwards [eventually_ge_atTop (0:ℝ),hgrow.eventually_ge_atTop M] with T hT hMT
  intro P hP
  let V := fun t => |(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|
  have hV : Measurable V := ((measurable_commonSievedPrimeError hc P).pow_const 2).sub
    ((measurable_ordinaryPrimePolarError hc).pow_const 2) |>.abs
  obtain ⟨hi,hbd⟩ := hmom P
  have hU : 0 ≤ η*T := mul_nonneg hη.le hT
  have hint : IntegrableOn V (Ioi (η*T)) := by
    refine (hi.mono_set (Set.Ioi_subset_Ioi hU)).mono' hV.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := η*T))] with t htt
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    exact le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (mul_nonneg (by norm_num)
      (hU.trans htt.le)))
  refine ⟨hint,?_⟩
  have htail := (abs_tail_le_exp_neg_mul (by norm_num : (0:ℝ) ≤ r) hU hi).trans
    (mul_le_mul_of_nonneg_left hbd (Real.exp_pos _).le)
  have h16 : (16:ℝ)^P.card ≤ Real.exp ((r*η/4)*T) := by
    calc (16:ℝ)^P.card = Real.exp (P.card*L) := by rw [Real.exp_nat_mul,hL16]
      _ ≤ _ := Real.exp_le_exp.2 (by
            have h := mul_le_mul_of_nonneg_right hP hL.le
            calc (P.card:ℝ)*L ≤ r*η/(4*L)*T*L := h
              _ = (r*η/4)*T := by
                  rw [show r*η/(4*L)*T*L = (r*η/4)*T*(L/L) by ring,div_self hL0,mul_one])
  calc (∫ t in Ioi (η*T), V t) ≤ Real.exp (-(r*(η*T)))*(M*(16:ℝ)^P.card) := htail
    _ ≤ Real.exp (-(r*(η*T)))*(Real.exp ((r*η/4)*T)*Real.exp ((r*η/4)*T)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul hMT h16 (pow_nonneg (by norm_num) _) (Real.exp_pos _).le
    _ = Real.exp (-(r*η/2*T)) := by
        rw [← Real.exp_add,← Real.exp_add]; congr 1; ring

/-- A family of sieves with `o(T)` primes has exponentially small variance
change on the whole ray `[ηT, ∞)`. -/
theorem criticalState_commonSieve_tail_of_sublinear_family {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {P : ℝ → Finset Nat.Primes}
    (hP : Tendsto (fun T => ((P T).card:ℝ)/T) atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in Ioi (η*T), |(commonSievedPrimeError (P T) Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) ≤
        Real.exp (-(δ*T)) := by
  obtain ⟨κ,δ,hκ,hδ,h⟩ := criticalState_commonSieve_sublinear_tail hW ht hF hc he hC hb hη
  refine ⟨δ,hδ,?_⟩
  filter_upwards [h,hP.eventually_lt_const hκ,eventually_gt_atTop (0:ℝ)] with T hT hPT hT0
  exact (hT (P T) ((div_lt_iff₀ hT0).1 hPT).le).2

/-- A set of primes up to `T` has at most `π(T)` elements. -/
theorem card_le_primeCounting_floor {T : ℝ} (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, ((p:ℕ):ℝ) ≤ T) : (P.card:ℝ) ≤ (Nat.primeCounting ⌊T⌋₊:ℝ) := by
  let e : Nat.Primes ↪ ℕ := ⟨Subtype.val,Subtype.coe_injective⟩
  have hsub : P.map e ⊆ Nat.primesBelow (⌊T⌋₊+1) := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.1 hn
    exact Nat.mem_primesBelow.2 ⟨Nat.lt_succ_of_le (Nat.le_floor (hP p hp)),p.2⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_map,Nat.primesBelow_card_eq_primeCounting'] at h
  exact_mod_cast h

/-- All subsets of the primes up to `T` at once: the variance change on
`[ηT, ∞)` is exponentially small, uniformly over the subset. -/
theorem criticalState_commonSieve_tail_below_horizon {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes, (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T) →
      IntegrableOn (fun t => |(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) (Ioi (η*T)) ∧
      (∫ t in Ioi (η*T), |(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) ≤
        Real.exp (-(δ*T)) := by
  obtain ⟨κ,δ,hκ,hδ,h⟩ := criticalState_commonSieve_sublinear_tail hW ht hF hc he hC hb hη
  refine ⟨δ,hδ,?_⟩
  have hlog : Tendsto (fun T : ℝ => (Real.log 4+1)/Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  filter_upwards [h,Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ) < 1),
    hlog.eventually_le_const hκ,eventually_gt_atTop (1:ℝ)] with T hT hπ hsmall hT1
  intro P hP
  apply hT P
  have hT0 : 0 < T := zero_lt_one.trans hT1
  have hl : 0 < Real.log T := Real.log_pos hT1
  calc (P.card:ℝ) ≤ (Nat.primeCounting ⌊T⌋₊:ℝ) := card_le_primeCounting_floor P hP
    _ ≤ (Real.log 4+1)*T/Real.log T := hπ
    _ = ((Real.log 4+1)/Real.log T)*T := by ring
    _ ≤ κ*T := mul_le_mul_of_nonneg_right hsmall hT0.le

/-- The tilted `L²` cost `4^{|P|}` of a common sieve is `e^{o(T)}` over every sieve
with at most `κT` primes. -/
theorem criticalState_commonSieve_sublinear_tilted_cost {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1/2) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes, (P.card:ℝ) ≤ κ*T →
      let g := fun t : ℝ => Real.exp (β*t)*(ordinaryPrimePolarError Φ t-commonSievedPrimeError P Φ t)
      MemLp g 2 ∧ lpNorm g 2 volume ≤ Real.exp (ε*T) := by
  obtain ⟨B,hB,hbound⟩ := criticalState_commonSieve_tilted_error hW ht hF hc he hC hb hβ hβ'
  let L := Real.log 4
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hL0 : L ≠ 0 := hL.ne'
  have hL4 : Real.exp L = 4 := Real.exp_log (by norm_num)
  refine ⟨ε/(2*L),div_pos hε (mul_pos two_pos hL),?_⟩
  have hgrow : Tendsto (fun T : ℝ => Real.exp ((ε/2)*T)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  filter_upwards [hgrow.eventually_ge_atTop B] with T hBT
  intro P hP
  obtain ⟨hg,hn⟩ := hbound P
  refine ⟨hg,hn.trans ?_⟩
  have h4 : (4:ℝ)^P.card ≤ Real.exp ((ε/2)*T) := by
    calc (4:ℝ)^P.card = Real.exp (P.card*L) := by rw [Real.exp_nat_mul,hL4]
      _ ≤ _ := Real.exp_le_exp.2 (by
            calc (P.card:ℝ)*L ≤ ε/(2*L)*T*L := mul_le_mul_of_nonneg_right hP hL.le
              _ = (ε/2)*T := by
                  rw [show ε/(2*L)*T*L = (ε/2)*T*(L/L) by ring,div_self hL0,mul_one])
  calc (4:ℝ)^P.card*B ≤ Real.exp ((ε/2)*T)*Real.exp ((ε/2)*T) := mul_le_mul h4 hBT hB (Real.exp_pos _).le
    _ = Real.exp (ε*T) := by rw [← Real.exp_add]; congr 1; ring

private theorem primorial_rpow_neg_eq {s : ℝ} (P : Finset Nat.Primes) :
    ((sievePrimorial P:ℕ):ℝ)^(-s) = Real.exp (-(s*sieveLogSize P)) := by
  have hpos : (0:ℝ) < (sievePrimorial P:ℕ) := by
    unfold sievePrimorial
    exact_mod_cast Finset.prod_pos fun (p : Nat.Primes) _ => p.2.pos
  rw [Real.rpow_def_of_pos hpos,← sieveLogSize_eq_log_primorial]; congr 1; ring

/-- Tonelli over all finite sieves: with weight `(∏_{p ∈ P} p)^{-s}`, `s > 1`, the
weighted variance discrepancies of all common sieves are summable, and their
pointwise sum is integrable on the positive ray. -/
theorem criticalState_primorial_weighted_total_variance {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {s r : ℝ} (hs : 1 < s) (hr : 0 ≤ r) (hr' : r < 1-zetaZeroAbscissa) :
    let v := fun (P : Finset Nat.Primes) (t : ℝ) => ((sievePrimorial P:ℕ):ℝ)^(-s)*
      (Real.exp (r*t)*|(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|)
    Summable (fun P => ∫ t in Ioi (0:ℝ), v P t) ∧
      (∫⁻ t in Ioi (0:ℝ), ∑' P, ENNReal.ofReal (v P t)) < ⊤ := by
  intro v
  obtain ⟨M,hM,hmom⟩ := criticalState_commonSieve_variance_bound hW ht hF hc he hC hb hr hr'
  have hn (P : Finset Nat.Primes) (t : ℝ) : 0 ≤ v P t :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
  have hi (P : Finset Nat.Primes) : IntegrableOn (v P) (Ioi 0) := (hmom P).1.const_mul _
  have hsum : Summable (fun P => ∫ t in Ioi (0:ℝ), v P t) := by
    refine Summable.of_nonneg_of_le (fun P => integral_nonneg (hn P)) (fun P => ?_)
      ((summable_primorial_variance_cost hs).mul_left M)
    change (∫ t in Ioi (0:ℝ), ((sievePrimorial P:ℕ):ℝ)^(-s)*_) ≤ _
    rw [integral_const_mul,primorial_rpow_neg_eq]
    calc Real.exp (-(s*sieveLogSize P))*(∫ t in Ioi (0:ℝ), _) ≤ Real.exp (-(s*sieveLogSize P))*(M*(16:ℝ)^P.card) :=
          mul_le_mul_of_nonneg_left (hmom P).2 (Real.exp_pos _).le
      _ = M*((16:ℝ)^P.card*Real.exp (-(s*sieveLogSize P))) := by ring
  refine ⟨hsum,?_⟩
  rw [lintegral_tsum (fun P => (hi P).aemeasurable.ennreal_ofReal)]
  have heq (P : Finset Nat.Primes) : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (v P t)) =
      ENNReal.ofReal (∫ t in Ioi (0:ℝ), v P t) :=
    (ofReal_integral_eq_lintegral_ofReal (hi P) (Eventually.of_forall (hn P))).symm
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun P => integral_nonneg (hn P)) hsum]
  exact ENNReal.ofReal_lt_top

/-- The primes dividing `q`, as a sieve: coprimality to `q`. -/
def coprimalitySieve (q : ℕ) : Finset Nat.Primes :=
  q.primeFactors.attach.map ⟨fun p => ⟨p.1,Nat.prime_of_mem_primeFactors p.2⟩,
    fun a b h => Subtype.ext (by simpa using congrArg (fun r : Nat.Primes => (r:ℕ)) h)⟩

theorem sievePrimorial_coprimalitySieve (q : ℕ) :
    sievePrimorial (coprimalitySieve q) = ∏ p ∈ q.primeFactors, p := by
  unfold sievePrimorial coprimalitySieve
  rw [Finset.prod_map]
  exact Finset.prod_attach q.primeFactors (fun p => p)

theorem sieveLogSize_coprimalitySieve_le {q : ℕ} (hq : q ≠ 0) :
    sieveLogSize (coprimalitySieve q) ≤ Real.log q := by
  have hd : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
  have hpos : 0 < ∏ p ∈ q.primeFactors, p := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  rw [sieveLogSize_eq_log_primorial,sievePrimorial_coprimalitySieve]
  exact Real.log_le_log (Nat.cast_pos.2 hpos) (Nat.cast_le.2 hd)

/-- Sieving by coprimality to a measurable modulus `1 ≤ q(t) ≤ e^{γt}`, which may
depend on the observed wave, keeps an exponentially integrable variance error
at every rate `b < 1 − Θ − γ`. -/
theorem criticalState_coprimality_modulus_variance {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {b γ : ℝ}
    (hb0 : 0 ≤ b) (hγ : 0 ≤ γ) (hroom : b+γ < 1-zetaZeroAbscissa)
    {q : ℝ → ℕ} (hq : Measurable q) (hq0 : ∀ t, 0 < t → q t ≠ 0)
    (hqγ : ∀ t, 0 < t → ((q t:ℕ):ℝ) ≤ Real.exp (γ*t)) :
    IntegrableOn (fun t => Real.exp (b*t)*
      |(commonSievedPrimeError (coprimalitySieve (q t)) Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) (Ioi 0) := by
  obtain ⟨A,hA,hmaj⟩ := criticalState_adaptive_prime_variance_envelope hW ht hF hc he hC hb hb0 hγ hroom
  have hm : Measurable (fun t => Real.exp (b*t)*
      |(commonSievedPrimeError (coprimalitySieve (q t)) Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) := by
    have hG : Measurable (fun p : ℝ × ℕ => Real.exp (b*p.1)*
        |(commonSievedPrimeError (coprimalitySieve p.2) Φ p.1)^2-(ordinaryPrimePolarError Φ p.1)^2|) := by
      refine measurable_from_prod_countable_left fun n => ?_
      exact (by fun_prop : Measurable fun t : ℝ => Real.exp (b*t)).mul
        ((((measurable_commonSievedPrimeError hc (coprimalitySieve n)).pow_const 2).sub
          ((measurable_ordinaryPrimePolarError hc).pow_const 2)).abs)
    exact hG.comp (measurable_id.prodMk hq)
  refine Integrable.mono' hA hm.aestronglyMeasurable ?_
  filter_upwards [hmaj,ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with t ht ht0
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
  apply ht
  have hqpos : (0:ℝ) < (q t:ℕ) := by exact_mod_cast Nat.pos_of_ne_zero (hq0 t ht0)
  calc sieveLogSize (coprimalitySieve (q t)) ≤ Real.log (q t) := sieveLogSize_coprimalitySieve_le (hq0 t ht0)
    _ ≤ Real.log (Real.exp (γ*t)) := Real.log_le_log hqpos (hqγ t ht0)
    _ = γ*t := Real.log_exp _

/-- The integral of the square of a real `L²` function is its squared norm. -/
theorem integral_sq_eq_lpNorm_sq_of_measure {f : ℝ → ℝ} {ν : Measure ℝ} (hf : MemLp f 2 ν) :
    (∫ t, f t^2 ∂ν)=(lpNorm f 2 ν)^2 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.1]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs]
  rw [show (2:ℝ)⁻¹=1/2 by norm_num,← Real.sqrt_eq_rpow,Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

/-- Deleting the true primes below `T²` costs `O(T²)` in `L²`: each deleted prime is
a translate of the state with a bounded coefficient. -/
theorem criticalState_quadratic_removed_primes {W₀ : ℝ}
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (he : F =ᵐ[volume] Φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ) (P : Finset Nat.Primes), (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) →
      MemLp (removedPrimeWave P Φ) 2 ∧ lpNorm (removedPrimeWave P Φ) 2 volume ≤ K*T^2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hF2 : MemLp F 2 := (memLp_two_iff_integrable_sq_norm hd.integrable.aestronglyMeasurable).2
    (by simpa only [Real.norm_eq_abs,sq_abs] using hd.sq)
  have hΦ2 : MemLp Φ 2 := hF2.ae_eq he
  have hψ : MemLp (fun t : ℝ => Real.exp (0*t)*Φ t) 2 := by
    simpa only [zero_mul,Real.exp_zero,one_mul] using hΦ2
  refine ⟨2*lpNorm Φ 2 volume,mul_nonneg (by norm_num) lpNorm_nonneg,fun T P hP => ?_⟩
  have h := removedPrimeWave_tilted_norm (by norm_num : (0:ℝ) < 1/2) hψ P
  simp only [zero_mul,Real.exp_zero,one_mul,sub_zero] at h
  refine ⟨h.1,h.2.trans ?_⟩
  have hc := card_sieving_primes_le P hP
  calc (P.card:ℝ)*((1/2)⁻¹*lpNorm Φ 2 volume) ≤ T^2*((1/2)⁻¹*lpNorm Φ 2 volume) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg (by norm_num) lpNorm_nonneg)
    _ = 2*lpNorm Φ 2 volume*T^2 := by ring

/-- On every scale where one of the two variances on `(0, T]` exceeds `e^{2δT}`,
their ratio is within `η` of one, uniformly over all sieves below `T²`. -/
theorem criticalState_quadratic_sieve_variance_ratio {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes, (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) →
      let a := ∫ t in Ioc 0 T, (commonSievedPrimeError P Φ t)^2
      let b := ∫ t in Ioc 0 T, (ordinaryPrimePolarError Φ t)^2
      (Real.exp (2*δ*T) ≤ a ∨ Real.exp (2*δ*T) ≤ b) → |a/b-1| ≤ η := by
  let K := 2+3/η
  have hgrow : Tendsto (fun T : ℝ => Real.exp ((δ/2)*T)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
  filter_upwards [criticalState_quadratic_sieve_square_perturbation hW ht hF hc he hC hb (half_pos hδ),
    criticalState_quadratic_sieve_sqrt_variance hW ht hF hc he hC hb (half_pos hδ),
    hgrow.eventually_ge_atTop K] with T hpert hsqrt hK
  intro P hP
  let ν := (volume : Measure ℝ).restrict (Ioc 0 T)
  have hE : MemLp (ordinaryPrimePolarError Φ) 2 ν := memLp_ordinaryPolar_on_window hW ht hF he T
  have hdiff : MemLp (fun t => ordinaryPrimePolarError Φ t-commonSievedPrimeError P Φ t) 2 ν :=
    (hpert P hP).1.mono_measure Measure.restrict_le_self
  have hEP : MemLp (commonSievedPrimeError P Φ) 2 ν := by
    refine MemLp.ae_eq ?_ (hE.sub hdiff)
    exact Eventually.of_forall fun t => by simp
  have hAB := hsqrt P hP ν Measure.restrict_le_self hE
  set A := lpNorm (commonSievedPrimeError P Φ) 2 ν with hAdef
  set B := lpNorm (ordinaryPrimePolarError Φ) 2 ν with hBdef
  have ha : (∫ t in Ioc 0 T, (commonSievedPrimeError P Φ t)^2) = A^2 := integral_sq_eq_lpNorm_sq_of_measure hEP
  have hb' : (∫ t in Ioc 0 T, (ordinaryPrimePolarError Φ t)^2) = B^2 := integral_sq_eq_lpNorm_sq_of_measure hE
  dsimp only
  rw [ha,hb']
  intro hcase
  have hu : 0 < Real.exp ((δ/2)*T) := Real.exp_pos _
  set u := Real.exp ((δ/2)*T) with hudef
  have hA0 : 0 ≤ A := lpNorm_nonneg
  have hB0 : 0 ≤ B := lpNorm_nonneg
  have hD : Real.exp (δ*T) = u*u := by rw [hudef,← Real.exp_add]; congr 1; ring
  have hDK : K*u ≤ Real.exp (δ*T) := by rw [hD]; exact mul_le_mul_of_nonneg_right hK hu.le
  have h2 : Real.exp (2*δ*T) = (Real.exp (δ*T))^2 := by rw [sq,← Real.exp_add]; congr 1; ring
  have hab := abs_le.1 hAB
  have hBlow : (K-1)*u ≤ B := by
    rcases hcase with h | h
    · rw [h2] at h
      have hAD := (pow_le_pow_iff_left₀ (Real.exp_pos _).le hA0 two_ne_zero).1 h
      linarith only [hAD,hDK,hab.2]
    · rw [h2] at h
      have hBD := (pow_le_pow_iff_left₀ (Real.exp_pos _).le hB0 two_ne_zero).1 h
      linarith only [hBD,hDK,hu]
  have h3η : 0 < 3/η := div_pos (by norm_num) hη
  have hK1 : 0 < K-1 := by simp only [K]; linarith
  have hBpos : 0 < B := (mul_pos hK1 hu).trans_le hBlow
  have hx : |A/B-1| ≤ 1/(K-1) := by
    rw [div_sub_one hBpos.ne',abs_div,abs_of_pos hBpos,div_le_div_iff₀ hBpos hK1,one_mul]
    calc |A-B| *(K-1) ≤ u*(K-1) := mul_le_mul_of_nonneg_right hAB hK1.le
      _ ≤ B := by linarith only [hBlow]
  have hx1 : 1/(K-1) ≤ 1 := by
    rw [div_le_one hK1]; simp only [K]; linarith
  have hxη : 1/(K-1) ≤ η/3 := by
    rw [div_le_div_iff₀ hK1 (by norm_num : (0:ℝ) < 3)]
    simp only [K]
    have hη0 : η ≠ 0 := hη.ne'
    have h3 : η*(3/η) = 3 := by field_simp
    have : η*(2+3/η-1) = η+3 := by linear_combination h3
    linarith only [this,hη]
  have hB0' : B ≠ 0 := hBpos.ne'
  have hsq : A^2/B^2-1 = (A/B-1)*(A/B+1) := by rw [← div_pow]; ring
  rw [hsq,abs_mul]
  have hy : |A/B+1| ≤ |A/B-1|+2 := by
    calc |A/B+1| = |(A/B-1)+2| := by ring_nf
      _ ≤ |A/B-1|+|(2:ℝ)| := abs_add_le _ _
      _ = |A/B-1|+2 := by norm_num
  have hxle : |A/B-1| ≤ 1 := hx.trans hx1
  calc |A/B-1| *|A/B+1| ≤ |A/B-1| *(|A/B-1|+2) := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    _ ≤ |A/B-1| *3 := mul_le_mul_of_nonneg_left (by linarith only [hxle]) (abs_nonneg _)
    _ ≤ (η/3)*3 := mul_le_mul_of_nonneg_right (hx.trans hxη) (by norm_num)
    _ = η := by ring

/-- One state forced by failure of RH carries the sublinear, coprimality-modulus
and quadratic-horizon laws of the common-sieve variance. -/
theorem riemannHypothesis_or_sublinear_and_modular_sieves : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      (∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes,
        (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T) →
        (∫ t in Ioi (η*T), |(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) ≤
          Real.exp (-(δ*T))) ∧
      (∀ b γ : ℝ, 0 ≤ b → 0 ≤ γ → b+γ < 1-zetaZeroAbscissa → ∀ q : ℝ → ℕ, Measurable q →
        (∀ t, 0 < t → q t ≠ 0) → (∀ t, 0 < t → ((q t:ℕ):ℝ) ≤ Real.exp (γ*t)) →
        IntegrableOn (fun t => Real.exp (b*t)*
          |(commonSievedPrimeError (coprimalitySieve (q t)) Φ t)^2-(ordinaryPrimePolarError Φ t)^2|) (Ioi 0)) ∧
      (∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ) (P : Finset Nat.Primes), (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) →
        lpNorm (removedPrimeWave P Φ) 2 volume ≤ K*T^2) ∧
      (∀ δ η : ℝ, 0 < δ → 0 < η → ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes,
        (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) →
        let a := ∫ t in Ioc 0 T, (commonSievedPrimeError P Φ t)^2
        let b := ∫ t in Ioc 0 T, (ordinaryPrimePolarError Φ t)^2
        (Real.exp (2*δ*T) ≤ a ∨ Real.exp (2*δ*T) ≤ b) → |a/b-1| ≤ η) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨K,hK,hrem⟩ := criticalState_quadratic_removed_primes hF he
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun η hη => ?_,
    fun b γ hb0 hγ hroom q hq hq0 hqγ =>
      criticalState_coprimality_modulus_variance hW ht hF hc he hC hb hb0 hγ hroom hq hq0 hqγ,
    ⟨K,hK,fun T P hP => (hrem T P hP).2⟩,
    fun δ η hδ hη => criticalState_quadratic_sieve_variance_ratio hW ht hF hc he hC hb hδ hη⟩
  obtain ⟨δ,hδ,h⟩ := criticalState_commonSieve_tail_below_horizon hW ht hF hc he hC hb hη
  exact ⟨δ,hδ,h.mono fun T hT P hP => (hT P hP).2⟩

#print axioms riemannHypothesis_or_sublinear_and_modular_sieves
#print axioms criticalState_commonSieve_sublinear_tail
#print axioms criticalState_commonSieve_tail_of_sublinear_family
#print axioms criticalState_commonSieve_sublinear_tilted_cost
#print axioms criticalState_primorial_weighted_total_variance
end GaloisForLFunctions.ExclusionOfTheCriticalState
