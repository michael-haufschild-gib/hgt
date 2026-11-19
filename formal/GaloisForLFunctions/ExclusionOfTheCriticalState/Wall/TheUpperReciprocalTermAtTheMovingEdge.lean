import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SplittingTheTestedIntegerBands
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SmallValuesOfTheReciprocalPrimeDiscrepancy
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheUpperIntegerTailOfTheOriginalPrimeTest

/-!
# The upper reciprocal term at the moving edge

The first-window strips through k and L agree below log k minus one. Their
difference is tested only against the decaying right tail of the time kernel.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri

private def stripEnvelope (C : ℝ) (N : ℕ) : ℝ :=
  C*(Real.log N+1)*(Real.sqrt (Real.log N)+1)

private theorem stripEnvelope_nonneg {C : ℝ} (hC : 0 ≤ C) (N : ℕ) : 0 ≤ stripEnvelope C N :=
  mul_nonneg (mul_nonneg hC (by linarith only [Real.log_natCast_nonneg N]))
    (by linarith only [Real.sqrt_nonneg (Real.log N)])

/-- An integer past k cannot lie in the first window before log k minus one. -/
private theorem first_window_ends_before_k {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : t ≤ Real.log k-1) :
    Real.exp t+Real.exp (t/2)*Real.sqrt t ≤ k := by
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  have hroot : Real.sqrt t ≤ Real.exp (t/2) := by
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt (by linarith only [Real.add_one_le_exp t])
  have hsq : Real.exp (t/2)*Real.exp (t/2)=Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ Real.exp t+Real.exp (t/2)*Real.exp (t/2) :=
           add_le_add le_rfl (mul_le_mul_of_nonneg_left hroot (Real.exp_pos _).le)
       _ ≤ Real.exp t*Real.exp 1 := by
           rw [hsq,← two_mul,mul_comm (Real.exp t)]
           exact mul_le_mul_of_nonneg_right (by linarith only [Real.add_one_le_exp 1]) (Real.exp_pos _).le
       _ ≤ k := by
           rw [← Real.exp_add,← Real.exp_log hk0]; exact Real.exp_le_exp.mpr (by linarith only [ht])

private theorem prefix_strips_agree {Φ : ℝ → ℝ} {k L : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L)
    {t : ℝ} (ht : t ≤ Real.log k-1) : prefixWallStrip Φ L t=prefixWallStrip Φ k t := by
  classical
  let w := fun n : ℕ => if pastCriticalEdge n t then 0 else
    (vonMangoldt n-1)*continuousIntegerAtom Φ n t
  have hzero : ∑ n ∈ Finset.Ioc k L, w n=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hkn : (k:ℝ)<n := Nat.cast_lt.mpr (Finset.mem_Ioc.mp hn).1
    exact if_pos ((first_window_ends_before_k hk ht).trans_lt hkn)
  change (∑ n ∈ Finset.Ioc 0 L, w n)=∑ n ∈ Finset.Ioc 0 k, w n
  rw [← Finset.sum_Ioc_consecutive w (Nat.zero_le k) hkL,hzero,add_zero]

private theorem upper_first_window_cost {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (hs : ∀ v, 0 ≤ v → Φ v=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v))
    {k L : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L) (T : ℝ) :
    |(∫ t, prefixWallStrip Φ L t*fractionalPrimeTest (T-t))-
      (∫ t, prefixWallStrip Φ k t*fractionalPrimeTest (T-t))| ≤
        2*(stripEnvelope C L+stripEnvelope C k)*Real.exp ((T+1-Real.log k)/2) := by
  let r := Real.log k-1
  let K := fun t => fractionalPrimeTest (T-t)
  let D := stripEnvelope C L+stripEnvelope C k
  have hD : 0 ≤ D := add_nonneg (stripEnvelope_nonneg hC L) (stripEnvelope_nonneg hC k)
  have hwin (N : ℕ) (t : ℝ) : |prefixWallStrip Φ N t| ≤ stripEnvelope C N := by
    have h := prefixWallStrip_bound hs hC hb N t
    apply h.trans
    by_cases ht : t ∈ Iic (Real.log N)
    · exact le_of_eq (indicator_of_mem ht _)
    · rw [indicator_of_notMem ht]; exact stripEnvelope_nonneg hC N
  have hkern (t : ℝ) : |K t| ≤ Real.exp ((T-t)/2) := by
    let z := Real.exp (T-t)
    have hp : Int.fract z ≤ z := by
      rw [Int.fract]; apply sub_le_self; exact_mod_cast (Int.floor_nonneg.mpr (Real.exp_pos (T-t)).le)
    change |Real.exp (-(T-t)/2)*Int.fract z| ≤ _
    rw [abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (Int.fract_nonneg _)]
    apply (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans_eq
    dsimp only [z]; rw [← Real.exp_add]; congr 1; ring
  let f := fun t => prefixWallStrip Φ L t*K t-prefixWallStrip Φ k t*K t
  let B := fun t : ℝ => (D*Real.exp (T/2))*Real.exp ((-1/2)*t)
  have hBi : IntegrableOn B (Ioi r) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-1/2:ℝ)<0) r).const_mul _
  have hp (t : ℝ) : ‖f t‖ ≤ B t := by
    dsimp only [f,B]
    rw [Real.norm_eq_abs,← sub_mul,abs_mul]
    have hsub := (abs_sub _ _).trans (add_le_add (hwin L t) (hwin k t))
    apply (mul_le_mul hsub (hkern t) (abs_nonneg _) hD).trans_eq
    rw [show (T-t)/2=T/2+(-1/2)*t by ring,Real.exp_add]; ring
  have hstrip (N : ℕ) := (tested_prefix_split_at_moving_edge hc hi N T).2.1
  rw [← integral_sub (hstrip L) (hstrip k)]
  change |∫ t, f t| ≤ _
  have heq : (∫ t in Ioi r, f t)=∫ t, f t := setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => by dsimp only [f]; rw [prefix_strips_agree hk hkL (le_of_not_gt ht),sub_self])
  rw [← heq,← Real.norm_eq_abs]
  apply (norm_integral_le_of_norm_le (f := f) (g := B) hBi (Eventually.of_forall hp)).trans_eq
  dsimp only [B]
  rw [integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-1/2:ℝ)<0),
    show (T+1-Real.log k)/2=T/2+(-1/2)*r by dsimp only [r]; ring,Real.exp_add]
  dsimp only [D]; ring

/-- The signed band integral differs from its whole tested weights by an
early-time cost uniform in the integer endpoint and a first-window cost
supported above log k minus one. -/
theorem moving_upper_band_sub_whole {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (hs : ∀ v, 0 ≤ v → Φ v=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (k L : ℕ) (U M T : ℝ), 1 ≤ k → k ≤ L → U ≤ M → Real.log L ≤ M →
      |(∫ v, Φ v)*(∫ t in Ioc U M, finiteCriticalComplementBand Φ k L t*fractionalPrimeTest (T-t))-
        (∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n))| ≤
        |∫ v, Φ v| *(2*D*Real.exp ((5*U-T)/2)+2*
          (C*(Real.log L+1)*(Real.sqrt (Real.log L)+1)+C*(Real.log k+1)*(Real.sqrt (Real.log k)+1))*
          Real.exp ((T+1-Real.log k)/2)) := by
  obtain ⟨D,hD,htime⟩ := finite_complement_prefix_time_cut hc hs hC hb
  refine ⟨D,hD,fun k L U M T hk hkL hUM hLM => ?_⟩
  let m := ∫ v, Φ v
  let K := fun t => fractionalPrimeTest (T-t)
  let row := fun N t => finiteCriticalComplementRow Φ N t*K t
  let strip := fun N t => prefixWallStrip Φ N t*K t
  let cut := fun N => ∫ t in Ioc U M, row N t
  let c := fun n : ℕ => (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  have hcband : (∫ t in Ioc U M, finiteCriticalComplementBand Φ k L t*K t)=cut L-cut k :=
    finite_band_integral_sub hc hi hkL U M T
  have hrec (N : ℕ) : (∑ n ∈ Finset.Ioc 0 N, c n)-m*(∫ t, row N t)=m*(∫ t, strip N t) :=
    (tested_prefix_split_at_moving_edge hc hi N T).2.2
  have hfull := Finset.sum_Ioc_consecutive c (Nat.zero_le k) hkL
  have hdiff : m*(cut L-cut k)-(∑ n ∈ Finset.Ioc k L, c n)=
      m*((cut L-(∫ t, row L t))-(cut k-(∫ t, row k t))-
        ((∫ t, strip L t)-(∫ t, strip k t))) := by
    linear_combination -(hrec L) + hrec k - hfull
  change |m*(∫ t in Ioc U M, finiteCriticalComplementBand Φ k L t*K t)-(∑ n ∈ Finset.Ioc k L, c n)| ≤ _
  rw [hcband,hdiff,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg m)
  apply (abs_sub _ _).trans
  apply add_le_add _ (upper_first_window_cost hc hi hs hC hb hk hkL T)
  apply (abs_sub _ _).trans
  rw [abs_sub_comm (cut L),abs_sub_comm (cut k)]
  have h := htime k U M T hUM ((Real.log_le_log hk0 (Nat.cast_le.mpr hkL)).trans hLM)
  exact (add_le_add (htime L U M T hUM hLM) h).trans_eq (by ring)

private theorem reciprocalPrimeRemainder_eighth_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k → |reciprocalPrimeRemainder k| ≤ B*(k:ℝ)^(-(1/8:ℝ)) := by
  obtain ⟨B,hB,h⟩ := centered_reciprocal_prime_intervals (d := 1/8) (by norm_num) (by norm_num)
  exact ⟨B,hB,fun k hk => le_of_tendsto (tendsto_reciprocalPrimeBand k).abs
    ((eventually_ge_atTop k).mono fun L hL => h k L hk hL)⟩

private theorem fifth_power_envelope {C q : ℝ} (hC : 0 ≤ C) {v : ℝ}
    (hv0 : 0 ≤ v) (hv : v ≤ 5*q) :
    C*(v+1)*(Real.sqrt v+1) ≤ C*320^2*Real.exp (q/32) := by
  have he := Real.add_one_le_exp (q/64)
  have h1 : v+1 ≤ 320*Real.exp (q/64) := by linarith only [hv,he]
  have h2 : Real.sqrt v+1 ≤ 320*Real.exp (q/64) := by
    have hs : Real.sqrt v ≤ v+1 := by nlinarith only [Real.sq_sqrt hv0,sq_nonneg (Real.sqrt v-1)]
    linarith only [hs,hv,he]
  have h12 := mul_le_mul h1 h2 (by linarith only [Real.sqrt_nonneg v]) (by positivity)
  have hx : Real.exp (q/64)*Real.exp (q/64)=Real.exp (q/32) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ = C*((v+1)*(Real.sqrt v+1)) := by ring
       _ ≤ C*((320*Real.exp (q/64))*(320*Real.exp (q/64))) := mul_le_mul_of_nonneg_left h12 hC
       _ = _ := by linear_combination (C*320^2)*hx

/-- The actual upper complementary row on the original middle interval reads
the centred reciprocal prime discrepancy at k, with an additive error tending
to zero. The time integral includes every favorable and exceptional center. -/
theorem criticalState_upper_moving_reciprocal {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    let T := fun k : ℕ => (7/8)*Real.log k
    let m := ∫ v, Φ v
    let A := ∫ v, Real.exp (-v/2)*Φ v
    Tendsto (fun k : ℕ => m*(∫ t in Ioc (T k/6) (6*T k),
      criticalComplementBand Φ k t*fractionalPrimeTest (T k-t))-
      m*A*(k:ℝ)^(7/16:ℝ)*reciprocalPrimeRemainder k) atTop (𝓝 0) := by
  let q := fun k : ℕ => Real.log k
  let T := fun k : ℕ => (7/8)*q k
  let m := ∫ v, Φ v
  let A := ∫ v, Real.exp (-v/2)*Φ v
  let H := 2 ^ (7/2:ℝ)*_root_.RHTower.vonMangoldtRpowTailConstant (7/2)+1
  change Tendsto (fun k : ℕ => m*(∫ t in Ioc (T k/6) (6*T k),
    criticalComplementBand Φ k t*fractionalPrimeTest (T k-t))-
    m*A*(k:ℝ)^(7/16:ℝ)*reciprocalPrimeRemainder k) atTop (𝓝 0)
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hi := hd.integrable.congr he
  have hmass : Integrable fun v => Φ v ^ 2 * Real.exp (-(8*v)) :=
    hd.exponential.congr (he.mono fun v hv => congrArg (fun x : ℝ => x^2*Real.exp (-(8*v))) hv)
  have htilt : Integrable fun v => Real.exp (-v/2)*Φ v := by
    apply (integrable_mul_exp_of_domain hd (by norm_num : (-4:ℝ)< -1/2)).congr
    filter_upwards [he] with v hv
    rw [hv,mul_comm]; congr 2; ring
  obtain ⟨D,_,hcut⟩ := moving_upper_band_sub_whole hc hi hs hC hb
  obtain ⟨B,_,hR⟩ := reciprocalPrimeRemainder_eighth_bound
  obtain ⟨J,_,hfar⟩ := criticalState_upper_integer_tail hW ht hF hc he
  have hq : Tendsto q atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  let E := fun (d : ℝ) (k : ℕ) => Real.exp (d*q k)
  have decay (c d : ℝ) (hd : d < 0) : Tendsto (fun k => c*E d k) atTop (𝓝 0) := by
    simpa only [E,Function.comp_apply,mul_zero] using
      (Real.tendsto_exp_atBot.comp (hq.const_mul_atTop_of_neg hd)).const_mul c
  have hmasslim := ((leftEighthNorm_atBot hmass).comp
    (hq.const_mul_atTop_of_neg (by norm_num : (-1/8:ℝ)<0))).const_mul (|m| *H)
  let S := 4*|m| *(C*320^2)*Real.exp (1/2)
  have hlim := ((((decay J (-7/64) (by norm_num)).add (decay (|m| *2*D) (-7/96) (by norm_num))).add
    (decay S (-1/32) (by norm_num))).add hmasslim).add (decay (|m*A| *B) (-3/16) (by norm_num))
  simp only [add_zero,mul_zero,Function.comp_apply] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1,hq.eventually_ge_atTop 2] with k hk hq2
  let L := k^5
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  have hkL : k ≤ L := Nat.le_pow (by decide : 0<5)
  have hL := hk.trans hkL
  have hq0 : 0 ≤ q k := Real.log_natCast_nonneg k
  have hLlog : Real.log L=5*q k := by dsimp only [L,q]; rw [Nat.cast_pow,Real.log_pow]; norm_num
  have htime : 1 ≤ T k := by dsimp only [T]; linarith only [hq2]
  have hU : T k/6 ≤ T k := by linarith only [htime]
  have hM : T k ≤ 6*T k := by linarith only [htime]
  have hLM : Real.log L ≤ 6*T k := by rw [hLlog]; dsimp only [T]; linarith only [hq0]
  have hfarcut : Real.exp (4*T k+T k) ≤ L := by
    rw [← Real.exp_log (show 0<(L:ℝ) by exact_mod_cast hL),hLlog]
    apply Real.exp_le_exp.mpr; dsimp only [T]; linarith only [hq0]
  let upper := fun j => m*(∫ t in Ioc (T k/6) (6*T k),
    criticalComplementBand Φ j t*fractionalPrimeTest (T k-t))
  let mid := m*(∫ t in Ioc (T k/6) (6*T k), finiteCriticalComplementBand Φ k L t*
    fractionalPrimeTest (T k-t))
  let full := ∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)*testedIntegerWeight Φ (T k) (Real.log n)
  let P := m*A*(k:ℝ)^(7/16:ℝ)
  have hsplit : upper k=mid+upper L := by
    dsimp only [upper,mid]
    rw [upper_band_integral_split hc hi hC hb hkL,mul_add]
  have hJ : |upper L| ≤ J*E (-7/64) k := by
    have h := hfar (T k/6) (T k) (6*T k) (T k) L hU hM htime (by linarith only [htime]) hfarcut
    simpa only [upper,E,T,show ∀ x : ℝ, -((7/8)*x)/8=(-7/64)*x by intro x; ring] using h
  have hD := hcut k L (T k/6) (6*T k) (T k) hk hkL (hU.trans hM) hLM
  have henv1 := fifth_power_envelope (q := q k) hC (v := q k) hq0 (by linarith only [hq0])
  have henv2 := fifth_power_envelope (q := q k) hC (v := 5*q k) (by linarith only [hq0]) le_rfl
  have hedge : Real.exp (q k/32)*Real.exp ((T k+1-q k)/2)=Real.exp (1/2)*E (-1/32) k := by
    dsimp only [E,T]; rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  have hmid : |mid-full| ≤ |m| *2*D*E (-7/96) k + S*E (-1/32) k := by
    rw [hLlog] at hD
    change |mid-full| ≤ |m| *(2*D*Real.exp ((5*(T k/6)-T k)/2)+2*
      (C*(5*q k+1)*(Real.sqrt (5*q k)+1)+C*(q k+1)*(Real.sqrt (q k)+1))*
      Real.exp ((T k+1-q k)/2)) at hD
    apply hD.trans
    have hearly : Real.exp ((5*(T k/6)-T k)/2)=E (-7/96) k := by dsimp only [E,T]; congr 1; ring
    rw [hearly]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add henv2 henv1)
      (by norm_num : (0:ℝ)≤2)) (Real.exp_pos ((T k+1-q k)/2)).le
    dsimp only [S]
    calc _ ≤ |m| *(2*D*E (-7/96) k+2*
             (C*320^2*Real.exp (q k/32)+C*320^2*Real.exp (q k/32))*Real.exp ((T k+1-q k)/2)) :=
             mul_le_mul_of_nonneg_left (add_le_add le_rfl hh) (abs_nonneg _)
         _ = _ := by linear_combination (4*|m| *(C*320^2))*hedge
  have hP : (k:ℝ)^(7/16:ℝ)=Real.exp (T k/2) := by
    rw [Real.rpow_def_of_pos hk0]; dsimp only [T,q]; congr 1; ring
  have hx : Real.exp (4*T k)*(k:ℝ)^(-(7/2:ℝ))=1 := by
    rw [Real.rpow_def_of_pos hk0,← Real.exp_add,show 4*T k+Real.log k * -(7/2:ℝ)=0 by dsimp [T,q]; ring,
      Real.exp_zero]
  have herr : |full-P*(reciprocalPrimeRemainder k-reciprocalPrimeRemainder L)| ≤
      (|m| *H)*leftEighthNorm Φ ((-1/8)*q k) := by
    have h := upper_finite_reciprocal_difference hc hmass htilt (T k) hk hkL
    dsimp only [P]; rw [hP]
    apply h.trans_eq
    change (|m| *leftEighthNorm Φ (T k-q k)*Real.exp (4*T k))*(H*(k:ℝ)^(-(7/2:ℝ)))=_
    rw [show T k-q k = (-1/8)*q k by dsimp only [T]; ring]
    linear_combination (|m| *H*leftEighthNorm Φ ((-1/8)*q k))*hx
  have hendpoint : |P*reciprocalPrimeRemainder L| ≤ (|m*A| *B)*E (-3/16) k := by
    have hpow : (k:ℝ)^(7/16:ℝ)*(L:ℝ)^(-(1/8:ℝ))=E (-3/16) k := by
      rw [Real.rpow_def_of_pos hk0,Real.rpow_def_of_pos (show 0<(L:ℝ) by exact_mod_cast hL),
        hLlog,← Real.exp_add]; dsimp only [E,q]; congr 1; ring
    dsimp only [P]; rw [abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg hk0.le _)]
    apply (mul_le_mul_of_nonneg_left (hR L hL) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hk0.le _))).trans_eq
    linear_combination (|m*A| *B)*hpow
  change ‖upper k-P*reciprocalPrimeRemainder k‖ ≤ _
  rw [Real.norm_eq_abs,hsplit,show mid+upper L-P*reciprocalPrimeRemainder k =
    ((upper L+(mid-full))+(full-P*(reciprocalPrimeRemainder k-reciprocalPrimeRemainder L)))-
    P*reciprocalPrimeRemainder L by ring]
  apply (abs_sub _ _).trans
  apply (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add hJ hmid)) herr)) hendpoint).trans_eq
  ring

/-- Failure of RH supplies a single state whose oriented upper contribution
on the full middle interval is asymptotic to its signed reciprocal tail. -/
theorem riemannHypothesis_or_upper_moving_reciprocal : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      let T := fun k : ℕ => (7/8)*Real.log k
      let m := ∫ v, Φ v
      let A := ∫ v, Real.exp (-v/2)*Φ v
      Tendsto (fun k : ℕ => m*(∫ t in Ioc (T k/6) (6*T k),
        criticalComplementBand Φ k t*fractionalPrimeTest (T k-t))-
        m*A*(k:ℝ)^(7/16:ℝ)*reciprocalPrimeRemainder k) atTop (𝓝 0) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl h
  obtain ⟨_,_,Φ,hc,he,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,criticalState_upper_moving_reciprocal hW ht hF hc he⟩

/-- An increasing sequence of arithmetic cutoffs eliminates the entire
upper contribution in the original test with its moving edge. -/
theorem exists_vanishing_upper_moving_sequence :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      Tendsto (fun j => (k j:ℝ)^(7/16:ℝ)*reciprocalPrimeRemainder (k j)) atTop (𝓝 0) ∧
      (RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
        let T := fun j : ℕ => (7/8)*Real.log (k j)
        Tendsto (fun j => (∫ v, Φ v)*(∫ t in Ioc (T j/6) (6*T j),
          criticalComplementBand Φ (k j) t*fractionalPrimeTest (T j-t))) atTop (𝓝 0)) := by
  obtain ⟨k,hk,hR⟩ := exists_vanishing_scaled_reciprocalPrimeRemainder
  refine ⟨k,hk,hR,?_⟩
  rcases riemannHypothesis_or_upper_moving_reciprocal with h | ⟨W₀,F,Φ,hW,ht,hF,hc,he,hw⟩
  · exact Or.inl h
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,?_⟩
  let a := (∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v)
  let T := fun j : ℕ => (7/8)*Real.log (k j)
  let band := fun j => (∫ v, Φ v)*(∫ t in Ioc (T j/6) (6*T j),
    criticalComplementBand Φ (k j) t*fractionalPrimeTest (T j-t))
  have hs : Tendsto (fun j => band j-a*(k j:ℝ)^(7/16:ℝ)*reciprocalPrimeRemainder (k j))
      atTop (𝓝 0) := hw.comp hk.tendsto_atTop
  have h := hs.add (hR.const_mul a)
  simp only [mul_zero,add_zero] at h
  apply h.congr
  intro j
  change band j-a*(k j:ℝ)^(7/16:ℝ)*reciprocalPrimeRemainder (k j)+
    a*((k j:ℝ)^(7/16:ℝ)*reciprocalPrimeRemainder (k j))=band j
  ring

open _root_.RHTower in
/-- At the square-root endpoint the Chebyshev discrepancy and the error in
the moving-prefix formula both vanish after the original normalization. -/
private theorem lower_sqrt_prefix_tendsto_zero {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    Tendsto (fun T : ℝ => (∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
      finiteCriticalComplementRow Φ ⌊Real.exp (T/2)⌋₊ t*fractionalPrimeTest (T-t))) atTop (𝓝 0) := by
  let N := fun T : ℝ => ⌊Real.exp (T/2)⌋₊
  let a := (∫ v, Φ v)*(∫ v, Real.exp (v/2)*Φ v)/2
  have hΘ : zeroReSup ≤ 20999/24000 := zeroReSup_le_of_forall_re_le fun q => by
    by_contra! hq
    exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hq
      (riemannZeta_eq_zero_of_xiZeroCopy q)
  obtain ⟨C,hC,hE⟩ := exists_abs_chebyshevPsi_sub_le_rpow (by linarith only [hΘ] : zeroReSup < 7/8)
  have hneg : Tendsto (fun T : ℝ => (-1/16)*T) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/16:ℝ)<0)
  have hdec : Tendsto (fun T : ℝ => (|a| *C)*Real.exp ((-1/16)*T)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using (Real.tendsto_exp_atBot.comp hneg).const_mul (|a| *C)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [criticalState_middle_lower_moving_prefix hW ht hF hc he 0 (ε/2) (half_pos hε),
    hdec.eventually_lt_const (half_pos hε),eventually_ge_atTop (0:ℝ)] with T herr hd hT
  have hN : 1 ≤ N T := Nat.le_floor (by
    simpa only [Nat.cast_one] using Real.one_le_exp (by linarith only [hT] : 0 ≤ T/2))
  have hx : (N T:ℝ) ≤ Real.exp (T/2) := Nat.floor_le (Real.exp_pos _).le
  have hlog := Real.log_le_log (show 0 < (N T:ℝ) by exact_mod_cast hN) hx
  rw [Real.log_exp] at hlog
  have hpow : (N T:ℝ)^(7/8:ℝ) ≤ Real.exp ((T/2)*(7/8)) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hx (by norm_num : (0:ℝ)≤7/8)).trans_eq
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  have hmain : |a*Real.exp (-T/2)*(Chebyshev.psi (N T)-(N T:ℝ))| ≤
      (|a| *C)*Real.exp ((-1/16)*T) := by
    rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_left ((hE (N T) (by exact_mod_cast hN)).trans
      (mul_le_mul_of_nonneg_left hpow hC)) (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)).trans_eq
    rw [show (-1/16)*T = -T/2+(T/2)*(7/8) by ring,Real.exp_add]; ring
  let b := (∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
    finiteCriticalComplementRow Φ (N T) t*fractionalPrimeTest (T-t))
  let e := a*Real.exp (-T/2)*(Chebyshev.psi (N T)-(N T:ℝ))
  have heps : |b-e| ≤ ε/2 := herr (N T) hN (by linarith only [hlog,hT])
  have htri := abs_sub_le b e 0
  simp only [sub_zero] at htri
  rw [Real.dist_eq,sub_zero]
  exact htri.trans_lt ((add_lt_add_of_le_of_lt heps (hmain.trans_lt hd)).trans_eq (add_halves ε))

/-- On one increasing arithmetic sequence the entire signed moving complement
differs by a vanishing amount from its integer band between √X and X^(8/7).
The time integral retains all centers in the original middle interval. -/
theorem exists_localized_middle_integer_sequence :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      (RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
        let T := fun j : ℕ => (7/8)*Real.log (k j)
        let N := fun j : ℕ => ⌊Real.exp (T j/2)⌋₊
        let m := ∫ v, Φ v
        Tendsto (fun j => m*(∫ t in Ioc (T j/6) (6*T j),
          criticalComplementBand Φ 0 t*fractionalPrimeTest (T j-t))-
          m*(∫ t in Ioc (T j/6) (6*T j),
          finiteCriticalComplementBand Φ (N j) (k j) t*fractionalPrimeTest (T j-t))) atTop (𝓝 0)) := by
  obtain ⟨k,hk,_,h⟩ := exists_vanishing_upper_moving_sequence
  refine ⟨k,hk,?_⟩
  rcases h with h | ⟨W₀,F,Φ,hW,ht,hF,hc,he,hu⟩
  · exact Or.inl h
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,?_⟩
  obtain ⟨_,_,Ψ,hΨ,heΨ,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  have hi := (criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he
  let T := fun j : ℕ => (7/8)*Real.log (k j)
  let N := fun j : ℕ => ⌊Real.exp (T j/2)⌋₊
  let m := ∫ v, Φ v
  let upper := fun j n => m*(∫ t in Ioc (T j/6) (6*T j), criticalComplementBand Φ n t*fractionalPrimeTest (T j-t))
  let row := fun j n => m*(∫ t in Ioc (T j/6) (6*T j), finiteCriticalComplementRow Φ n t*fractionalPrimeTest (T j-t))
  let band := fun j => m*(∫ t in Ioc (T j/6) (6*T j),
    finiteCriticalComplementBand Φ (N j) (k j) t*fractionalPrimeTest (T j-t))
  have hT : Tendsto T atTop atTop := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hk.tendsto_atTop)).const_mul_atTop (by norm_num : (0:ℝ)<7/8)
  have hlo : Tendsto (fun j => row j (N j)) atTop (𝓝 0) :=
    (lower_sqrt_prefix_tendsto_zero hW ht hF hc he).comp hT
  change Tendsto (fun j => upper j (k j)) atTop (𝓝 0) at hu
  change Tendsto (fun j => upper j 0-band j) atTop (𝓝 0)
  apply (show Tendsto (fun j => upper j (k j)+row j (N j)) atTop (𝓝 0) by
    simpa only [add_zero] using hu.add hlo).congr'
  filter_upwards [hk.tendsto_atTop.eventually_ge_atTop 1] with j hj
  have hkj : 0 < (k j:ℝ) := by exact_mod_cast hj
  have hjN : N j ≤ k j := by
    apply (Nat.cast_le (α := ℝ)).mp
    apply (Nat.floor_le (Real.exp_pos (T j/2)).le).trans
    conv_rhs => rw [← Real.exp_log hkj]
    exact Real.exp_le_exp.mpr (by dsimp only [T]; linarith only [Real.log_natCast_nonneg (k j)])
  have hsplit : upper j 0=row j (k j)+upper j (k j) := by
    dsimp only [upper,row,finiteCriticalComplementRow]
    rw [upper_band_integral_split hc hi hC hb (Nat.zero_le (k j)),mul_add]
  have hband : band j=row j (k j)-row j (N j) := by
    dsimp only [band,row]
    rw [finite_band_integral_sub hc hi hjN,mul_sub]
  rw [hsplit,hband]; ring

#print axioms exists_localized_middle_integer_sequence
#print axioms exists_vanishing_upper_moving_sequence
#print axioms moving_upper_band_sub_whole
#print axioms riemannHypothesis_or_upper_moving_reciprocal
end GaloisForLFunctions.ExclusionOfTheCriticalState
