import GaloisForLFunctions.RHTower.SoninPrimePolarSignedEnergy
import GaloisForLFunctions.RHTower.BurnolSoninDividedShift
import GaloisForLFunctions.RHTower.MellinHeadChart

/-!
# Exact critical energy of the native prime–polar ground source

The original prime coefficient cancels the ground dilation normalization.
The original polar density becomes `(exp u + 1) / u`. Finite-set L2
pairings and scalar Fubini identify the actual strong integral with this
cumulative arithmetic profile, without a representation assumption.

The physical head chart gives its exact exponentially weighted square
energy. Synchronizing the finite prime cutoff with the upper polar
endpoint retains the constant terminal tail as an explicit square.
Finite integrability is proved; uniform bounds and cofinal decay are not.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower

private theorem integral_field_ae {μ : Measure ℝ} [SFinite μ]
    (F : ℝ → SoninL2) (k : ℝ → ℝ → ℂ) (g : ℝ → ℝ)
    (hF : Integrable F μ) (hk : StronglyMeasurable (Function.uncurry k))
    (hg : Integrable g μ) (hb : ∀ u x, ‖k u x‖ ≤ g u)
    (hrep : ∀ u, (F u : ℝ → ℂ) =ᵐ[volume] k u) :
    ((∫ u, F u ∂μ : SoninL2) : ℝ → ℂ) =ᵐ[volume] fun x => ∫ u, k u x ∂μ := by
  have hp (s : Set ℝ) (hsfin : volume s ≠ ⊤) :
      Integrable (fun p : ℝ × ℝ => k p.2 p.1) ((volume.restrict s).prod μ) := by
    letI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hsfin
    have hdom : Integrable (fun p : ℝ × ℝ => g p.2)
        ((volume.restrict s).prod μ) := hg.comp_snd (volume.restrict s)
    apply hdom.mono' (hk.comp_measurable measurable_swap).aestronglyMeasurable
    filter_upwards [] with p
    change ‖k p.2 p.1‖ ≤ g p.2
    exact hb p.2 p.1
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hsfin
    letI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hsfin.ne
    exact ((Lp.memLp (∫ u, F u ∂μ)).restrict s).integrable (by norm_num)
  · intro s hs hsfin
    exact (hp s hsfin.ne).integral_prod_left
  · intro s hs hsfin
    rw [← inner_indicatorConstLp_eq_setIntegral hs hsfin.ne, ← integral_inner hF]
    calc
      _ = ∫ u, (∫ x in s, k u x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with u
        rw [inner_indicatorConstLp_eq_setIntegral hs hsfin.ne]
        exact integral_congr_ae (hrep u).restrict
      _ = _ := (integral_integral_swap (hp s hsfin.ne)).symm

private theorem sqrt_exp_half (u : ℝ) : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
  rw [Real.sq_sqrt (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 1
  ring

private def groundIndicator (a x : ℝ) : ℂ :=
  (centralInterval a).indicator (fun _ => (1:ℂ)) x

private theorem groundIndicator_norm_le (a x : ℝ) : ‖groundIndicator a x‖ ≤ 1 := by
  unfold groundIndicator
  by_cases hx : x ∈ centralInterval a
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

private theorem log_dilation_ground_ae (a u : ℝ) :
    (rayDilate (Real.exp u) (soninCutoffMonomial a 0) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp (u/2):ℂ) * groundIndicator a (Real.exp u*x) := by
  rw [rayDilate_of_pos (Real.exp_pos u)]
  have hcut := (realMul_quasiMeasurePreserving (Real.exp u) (Real.exp_ne_zero u)).ae_eq_comp
    (soninCutoffMonomial_ae a 0)
  filter_upwards [dilation_ae (Real.exp u) (Real.exp_pos u) (soninCutoffMonomial a 0), hcut]
    with x hd hc
  rw [hd, sqrt_exp_half]
  change soninCutoffMonomial a 0 (Real.exp u*x) = _ at hc
  rw [hc]
  simp only [pow_zero, groundIndicator, Function.comp_apply]

private theorem polar_density_continuousOn (b R : ℝ) (hb : 0 < b) :
    ContinuousOn soninLogPolarDensity (Icc b R) := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le hb hu.1)
  unfold soninLogPolarDensity
  fun_prop

private theorem polar_density_ground (u : ℝ) :
    soninLogPolarDensity u * (Real.exp (u/2):ℂ) =
      (((Real.exp u+1)/u : ℝ):ℂ) := by
  rw [soninLogPolarDensity, ← Complex.ofReal_mul]
  congr 1
  rw [Real.cosh_eq]
  have h1 : Real.exp (u/2)*Real.exp (u/2) = Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(u/2))*Real.exp (u/2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = (Real.exp (u/2)*Real.exp (u/2)+Real.exp (-(u/2))*Real.exp (u/2))/u := by ring
    _ = _ := by rw [h1, h2]

private theorem polar_ground_integral_ae (a b R : ℝ) (hb : 0 < b) :
    ((∫ u in Icc b R, soninLogPolarDensity u •
      rayDilate (Real.exp u) (soninCutoffMonomial a 0) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ u in Icc b R, (((Real.exp u+1)/u : ℝ):ℂ) *
        groundIndicator a (Real.exp u*x) := by
  let F : ℝ → SoninL2 := fun u => soninLogPolarDensity u •
    rayDilate (Real.exp u) (soninCutoffMonomial a 0)
  let k : ℝ → ℝ → ℂ := fun u x => soninLogPolarDensity u *
    (Real.exp (u/2):ℂ) * groundIndicator a (Real.exp u*x)
  have hk : StronglyMeasurable (Function.uncurry k) := by
    apply Measurable.stronglyMeasurable
    have hi : Measurable (fun p : ℝ × ℝ => groundIndicator a (Real.exp p.1*p.2)) :=
      ((measurable_const.indicator (measurableSet_centralInterval a)).comp
        ((Real.measurable_exp.comp measurable_fst).mul measurable_snd))
    dsimp only [k, Function.uncurry]
    apply Measurable.mul _ hi
    unfold soninLogPolarDensity
    fun_prop
  have hF : IntegrableOn F (Icc b R) :=
    ((polar_density_continuousOn b R hb).smul
      (continuous_dilationOrbit (soninCutoffMonomial a 0)).continuousOn).integrableOn_Icc
  have hg : IntegrableOn (fun u => ‖soninLogPolarDensity u‖*Real.exp (u/2)) (Icc b R) :=
    ((polar_density_continuousOn b R hb).norm.mul
      (by fun_prop : ContinuousOn (fun u : ℝ => Real.exp (u/2)) (Icc b R))).integrableOn_Icc
  have hrep (u : ℝ) : (F u : ℝ → ℂ) =ᵐ[volume] k u := by
    filter_upwards [Lp.coeFn_smul (soninLogPolarDensity u)
      (rayDilate (Real.exp u) (soninCutoffMonomial a 0)), log_dilation_ground_ae a u]
      with x hs hd
    rw [show F u = soninLogPolarDensity u • rayDilate (Real.exp u) (soninCutoffMonomial a 0) from rfl,
      hs]
    change soninLogPolarDensity u * (rayDilate (Real.exp u) (soninCutoffMonomial a 0)) x = _
    rw [hd]
    simp only [k, mul_assoc]
  have h := integral_field_ae F k _ hF hk hg (fun u x => by
    dsimp only [k]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (by positivity) (groundIndicator_norm_le a _)) hrep
  apply h.trans
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with u
  dsimp only [k]
  rw [polar_density_ground]

private theorem prime_ground_ae (a : ℝ) (p : Nat.Primes) :
    ((((Real.sqrt (p:ℝ))⁻¹ : ℂ) • rayDilate (Real.exp (Real.log (p:ℝ)))
      (soninCutoffMonomial a 0) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => groundIndicator a ((p:ℝ)*x) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast p.prop.pos
  filter_upwards [Lp.coeFn_smul ((Real.sqrt (p:ℝ))⁻¹ : ℂ)
    (rayDilate (Real.exp (Real.log (p:ℝ))) (soninCutoffMonomial a 0)),
    log_dilation_ground_ae a (Real.log (p:ℝ))] with x hs hd
  rw [hs]
  change ((Real.sqrt (p:ℝ))⁻¹ : ℂ) * _ = _
  rw [hd, ← sqrt_exp_half, Real.exp_log hp, ← mul_assoc]
  have hne : (Real.sqrt (p:ℝ):ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
  rw [inv_mul_cancel₀ hne, one_mul]

private def nativeGroundProfile (a : ℝ) (P : Finset Nat.Primes) (b R x : ℝ) : ℂ :=
  (∑ p ∈ P, groundIndicator a ((p:ℝ)*x)) -
    ∫ u in Icc b R, (((Real.exp u+1)/u : ℝ):ℂ) * groundIndicator a (Real.exp u*x)

private theorem native_ground_ae (a : ℝ) (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) :
    (soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0) : ℝ → ℂ) =ᵐ[volume]
      nativeGroundProfile a P b R := by
  classical
  have hsum : ((∑ p ∈ P, ((Real.sqrt (p:ℝ))⁻¹ : ℂ) •
      rayDilate (Real.exp (Real.log (p:ℝ))) (soninCutoffMonomial a 0) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ p ∈ P, groundIndicator a ((p:ℝ)*x) := by
    induction P using Finset.induction_on with
    | empty =>
      filter_upwards [Lp.coeFn_zero ℂ 2 volume] with x hx
      simpa only [Finset.sum_empty, Pi.zero_apply] using hx
    | @insert p P hp ih =>
      simp only [Finset.sum_insert hp]
      filter_upwards [Lp.coeFn_add
        (((Real.sqrt (p:ℝ))⁻¹ : ℂ) • rayDilate (Real.exp (Real.log (p:ℝ))) (soninCutoffMonomial a 0))
        (∑ q ∈ P, ((Real.sqrt (q:ℝ))⁻¹ : ℂ) • rayDilate (Real.exp (Real.log (q:ℝ))) (soninCutoffMonomial a 0)),
        prime_ground_ae a p, ih] with x hadd hp' hi
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hp', hi]
  rw [soninPrimePolarSourceOperator_apply]
  simp only [one_mul]
  filter_upwards [hsum, polar_ground_integral_ae a b R hb,
    Lp.coeFn_sub
      (∑ p ∈ P, ((Real.sqrt (p:ℝ))⁻¹ : ℂ) • rayDilate (Real.exp (Real.log (p:ℝ))) (soninCutoffMonomial a 0))
      (∫ u in Icc b R, soninLogPolarDensity u • rayDilate (Real.exp u) (soninCutoffMonomial a 0))]
    with x hp hc hs
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hp, hc]
  rfl

/-- Literal cumulative prime count minus the original polar source after
its ground-vector normalization. No asymptotic admission is part of this definition. -/
def soninPrimePolarGroundCumulative (P : Finset Nat.Primes) (b R t : ℝ) : ℝ :=
  (∑ p ∈ P, if Real.log (p:ℝ) ≤ t then (1:ℝ) else 0) -
    ∫ u in Icc b R, if u ≤ t then (Real.exp u+1)/u else 0

private theorem groundIndicator_log (a : ℝ) (ha : 0 < a) (u t : ℝ) :
    groundIndicator a (Real.exp u*(a*Real.exp (-t))) =
      if u ≤ t then (1:ℂ) else 0 := by
  have hx : Real.exp u*(a*Real.exp (-t)) = a*Real.exp (u-t) := by
    rw [Real.exp_sub, Real.exp_neg]
    ring
  rw [hx]
  have hm : a*Real.exp (u-t) ∈ centralInterval a ↔ u ≤ t := by
    change (-a ≤ a*Real.exp (u-t) ∧ a*Real.exp (u-t) ≤ a) ↔ u ≤ t
    have hlo : -a ≤ a*Real.exp (u-t) :=
      (neg_nonpos.mpr ha.le).trans (mul_nonneg ha.le (Real.exp_pos _).le)
    have hhi : a*Real.exp (u-t) ≤ a ↔ Real.exp (u-t) ≤ 1 := by
      simpa only [mul_one] using (mul_le_mul_iff_right₀ ha : a*Real.exp (u-t) ≤ a*1 ↔ _)
    rw [and_iff_right hlo, hhi, Real.exp_le_one_iff, sub_nonpos]
  unfold groundIndicator
  by_cases hut : u ≤ t
  · rw [Set.indicator_of_mem (hm.mpr hut), if_pos hut]
  · rw [Set.indicator_of_notMem (mt hm.mp hut), if_neg hut]

private theorem nativeGroundProfile_log (a : ℝ) (ha : 0 < a)
    (P : Finset Nat.Primes) (b R t : ℝ) :
    nativeGroundProfile a P b R (a*Real.exp (-t)) =
      (soninPrimePolarGroundCumulative P b R t : ℂ) := by
  classical
  unfold nativeGroundProfile soninPrimePolarGroundCumulative
  push_cast
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    have hp0 : 0 < (p:ℝ) := by exact_mod_cast p.prop.pos
    simpa only [Real.exp_log hp0, apply_ite Complex.ofReal, Complex.ofReal_one,
      Complex.ofReal_zero] using groundIndicator_log a ha (Real.log (p:ℝ)) t
  · rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [groundIndicator_log a ha u t]
    split_ifs <;> simp

/-- Exact arithmetic coordinates of the original principal prime–polar
source on its physical ground vector, throughout the logarithmic head. -/
theorem soninPrimePolarSourceOperator_ground_log_ae (a : ℝ) (ha : 0 < a)
    (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) :
    (fun t => soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0)
      (a*Real.exp (-t))) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      fun t => (soninPrimePolarGroundCumulative P b R t : ℂ) := by
  have h := (quasiMeasurePreserving_expScaleNeg ha).ae_eq_comp
    (native_ground_ae a P b R hb).restrict
  apply h.trans
  filter_upwards [] with t
  exact nativeGroundProfile_log a ha P b R t

private theorem groundIndicator_neg (a x : ℝ) : groundIndicator a (-x) = groundIndicator a x := by
  have hm : -x ∈ centralInterval a ↔ x ∈ centralInterval a := by
    change (-a ≤ -x ∧ -x ≤ a) ↔ (-a ≤ x ∧ x ≤ a)
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  unfold groundIndicator
  by_cases hx : x ∈ centralInterval a
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hm.mpr hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hm.mp hx)]

private theorem nativeGroundProfile_neg (a : ℝ) (P : Finset Nat.Primes) (b R x : ℝ) :
    nativeGroundProfile a P b R (-x) = nativeGroundProfile a P b R x := by
  simp only [nativeGroundProfile, mul_neg, groundIndicator_neg]

private theorem native_ground_even (a : ℝ) (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) :
    soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0) ∈ evenSubspace := by
  apply (mem_evenSubspace_iff _).mpr
  apply Lp.ext
  have h := native_ground_ae a P b R hb
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [l2Reflection_ae (soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0)),
    h, hn] with x hr hx hn
  rw [hr, hx]
  change soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0) (-x) =
    nativeGroundProfile a P b R (-x) at hn
  rw [hn, nativeGroundProfile_neg]

private theorem groundIndicator_zero_of_scaled (a x q : ℝ) (ha : 0 < a)
    (hx : a ≤ x) (hq : 1 < q) : groundIndicator a (q*x) = 0 := by
  apply Set.indicator_of_notMem
  intro hm
  have hm2 : q*x ≤ a := hm.2
  nlinarith

private theorem nativeGroundProfile_zero (a : ℝ) (ha : 0 < a) (P : Finset Nat.Primes)
    (b R x : ℝ) (hb : 0 < b) (hx : a ≤ x) : nativeGroundProfile a P b R x = 0 := by
  unfold nativeGroundProfile
  have hp : (∑ p ∈ P, groundIndicator a ((p:ℝ)*x)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    exact groundIndicator_zero_of_scaled a x _ ha hx (by exact_mod_cast p.prop.one_lt)
  rw [hp]
  have hi : (∫ u in Icc b R, (((Real.exp u+1)/u : ℝ):ℂ) *
      groundIndicator a (Real.exp u*x)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [groundIndicator_zero_of_scaled a x _ ha hx
      (Real.one_lt_exp_iff.mpr (lt_of_lt_of_le hb hu.1)), mul_zero]
    rfl
  rw [hi, sub_self]

/-- Exact critical cumulative energy of the original one-direction source.
The cumulative function includes its constant terminal tail. -/
theorem soninPrimePolarSourceOperator_ground_energy (a : ℝ) (ha : 0 < a)
    (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) :
    ‖soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0)‖^2 =
      2*a*(∫ t in Ioi (0:ℝ), Real.exp (-t)*soninPrimePolarGroundCumulative P b R t ^ 2) := by
  let f := soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0)
  have hhalf : ‖f‖^2 = 2*(∫ x in Ioi (0:ℝ), ‖f x‖^2) := by
    have h := norm_sq_soninHalfLine (native_ground_even a P b R hb)
    have hh : ‖soninHalfLine f‖^2 = ∫ x in Ioi (0:ℝ), ‖f x‖^2 :=
      norm_sq_toLp_eq_integral_norm_sq (memLp_restrict_Ioi f)
    change ‖soninHalfLine f‖^2*2=‖f‖^2 at h
    rw [hh] at h
    linarith
  have hsupp : (∫ x in Ioi (0:ℝ), ‖f x‖^2) = ∫ x in Ioo (0:ℝ) a, ‖f x‖^2 := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [native_ground_ae a P b R hb] with x hx
    by_cases hx0 : 0 < x
    · by_cases hxa : x < a
      · rw [Set.indicator_of_mem (show x ∈ Ioi (0:ℝ) from hx0), Set.indicator_of_mem (show x ∈ Ioo (0:ℝ) a from ⟨hx0,hxa⟩)]
      · have hf0 : f x = 0 := hx.trans (nativeGroundProfile_zero a ha P b R x hb (le_of_not_gt hxa))
        simp only [Set.indicator_of_mem (show x ∈ Ioi (0:ℝ) from hx0), Set.indicator_of_notMem
          (show x ∉ Ioo (0:ℝ) a by simpa only [mem_Ioo, not_and] using fun _ => hxa), hf0,
          norm_zero, zero_pow (by decide : 2≠0)]
    · rw [Set.indicator_of_notMem (show x ∉ Ioi (0:ℝ) from hx0), Set.indicator_of_notMem
        (show x ∉ Ioo (0:ℝ) a from fun h => hx0 h.1)]
  have hhead : (∫ x in Ioo (0:ℝ) a, ‖f x‖^2) =
      a*(∫ t in Ioi (0:ℝ), Real.exp (-t)*soninPrimePolarGroundCumulative P b R t ^ 2) := by
    rw [← integral_norm_sq_logChartHead ha, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [soninPrimePolarSourceOperator_ground_log_ae a ha P b R hb] with t ht
    rw [norm_sq_logChartHead ha.le]
    rw [ht, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  change ‖f‖^2 = _
  rw [hhalf, hsupp, hhead]
  ring

/-- Every finite native cumulative profile has a genuine critical square
integral. This does not assert a bound uniform in the source cutoff. -/
theorem integrable_soninPrimePolarGroundCumulative_energy
    (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) :
    IntegrableOn (fun t => Real.exp (-t)*soninPrimePolarGroundCumulative P b R t ^ 2)
      (Ioi (0:ℝ)) := by
  let f := soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial 1 0)
  have hm := memLp_two_logChartHead zero_lt_one ((Lp.memLp f).restrict (Ioo (0:ℝ) 1))
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  apply hi.congr
  filter_upwards [soninPrimePolarSourceOperator_ground_log_ae 1 zero_lt_one P b R hb] with t ht
  rw [norm_sq_logChartHead zero_le_one]
  rw [ht, Complex.norm_real, Real.norm_eq_abs, sq_abs, one_mul]

private theorem cumulative_terminal (P : Finset Nat.Primes) (b R t : ℝ)
    (hP : ∀ p ∈ P, Real.log (p:ℝ) ≤ R) (ht : R ≤ t) :
    soninPrimePolarGroundCumulative P b R t = soninPrimePolarGroundCumulative P b R R := by
  unfold soninPrimePolarGroundCumulative
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    rw [if_pos (le_trans (hP p hp) ht), if_pos (hP p hp)]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [if_pos (le_trans hu.2 ht), if_pos hu.2]

/-- The finite native source retains its terminal square exactly. The
prime cutoff is synchronized with its actual logarithmic polar endpoint. -/
theorem soninPrimePolarSourceOperator_ground_energy_endpoint (a : ℝ) (ha : 0 < a)
    (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) (hR : 0 ≤ R)
    (hP : ∀ p ∈ P, Real.log (p:ℝ) ≤ R) :
    ‖soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a 0)‖^2 =
      2*a*((∫ t in Ioc (0:ℝ) R, Real.exp (-t)*soninPrimePolarGroundCumulative P b R t ^ 2) +
        Real.exp (-R)*soninPrimePolarGroundCumulative P b R R ^ 2) := by
  have hi := integrable_soninPrimePolarGroundCumulative_energy P b R hb
  have hs := integral_add_compl (s := Iic R) (μ := volume.restrict (Ioi (0:ℝ))) measurableSet_Iic hi
  have hleft : Iic R ∩ Ioi (0:ℝ) = Ioc (0:ℝ) R := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc, and_comm]
  have hright : Ioi R ∩ Ioi (0:ℝ) = Ioi R := by
    apply inter_eq_left.mpr
    exact Ioi_subset_Ioi hR
  change (∫ t in Iic R, Real.exp (-t)*soninPrimePolarGroundCumulative P b R t ^ 2
      ∂(volume.restrict (Ioi (0:ℝ)))) +
    (∫ t in (Iic R)ᶜ, Real.exp (-t)*soninPrimePolarGroundCumulative P b R t ^ 2
      ∂(volume.restrict (Ioi (0:ℝ)))) = _ at hs
  rw [compl_Iic, Measure.restrict_restrict measurableSet_Iic, hleft,
    Measure.restrict_restrict measurableSet_Ioi, hright] at hs
  have ht : (∫ t in Ioi R, Real.exp (-t)*soninPrimePolarGroundCumulative P b R t ^ 2) =
      Real.exp (-R)*soninPrimePolarGroundCumulative P b R R ^ 2 := by
    calc
      _ = ∫ t in Ioi R, Real.exp (-t)*soninPrimePolarGroundCumulative P b R R ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [cumulative_terminal P b R t hP ht.le]
      _ = _ := by
        rw [integral_mul_const]
        have he : (∫ t in Ioi R, Real.exp (-t)) = Real.exp (-R) := by
          simpa using integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) R
        rw [he]
  rw [ht] at hs
  rw [soninPrimePolarSourceOperator_ground_energy a ha P b R hb, ← hs]

end RHTower
