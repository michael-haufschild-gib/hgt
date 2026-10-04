import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeSquareSign
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeCurrent
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCenteredEnergy

/-!
# Escape of the negative mixed prime current

The actual finite-prime core is negative on its square slab while its prime
dilate is positive. Their product forces a power-sized negative part of the
complete mixed current. This separated-part obstruction leaves complete
signed compensation open.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

/-- The actual signed density in a canonical prime update. -/
def pmPrimeMixedDensity (ε : ℝ) (P : ℕ) (t : ℝ) : ℝ :=
  (P : ℝ)^(-ε)*
    (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε t*
      (starRingEnd ℂ) (pmFinitePrimePowerDampedFermiSource
        (mobiusFinitePrimeAperture (P-1)) ε ((P : ℝ)*t))).re

private theorem pmqm_core_im (S : Finset ℕ) (ε t : ℝ) :
    (pmFinitePrimePowerDampedFermiSource S ε t).im = 0 := by
  classical
  have hg (a t : ℝ) : (fermiNymanGen a t).im = 0 := by
    simp [fermiNymanGen,GaloisForLFunctions.NymanMellin.nymanGen,Complex.mul_im]
  have hc (d : ℕ) : (finitePrimeApertureMobiusCoefficient S d).im = 0 := by
    unfold finitePrimeApertureMobiusCoefficient
    split_ifs <;> simp [mobiusComplexCoefficient]
  simp only [pmFinitePrimePowerDampedFermiSource,Complex.neg_im,Complex.im_sum,
    Complex.mul_im,hc,Complex.ofReal_im,hg,mul_zero,zero_mul,add_zero,
    Finset.sum_const_zero,neg_zero]

private theorem pmqm_core_measurable (S : Finset ℕ) (ε : ℝ) :
    Measurable (pmFinitePrimePowerDampedFermiSource S ε) := by
  exact (Finset.measurable_sum _ (fun d _ =>
    measurable_const.mul (measurable_fermiNymanGen _))).neg

/-- Every finite update has an integrable mixed density. -/
theorem integrableOn_pmPrimeMixedDensity (ε : ℝ) {P : ℕ} (hP : 0 < P) :
    IntegrableOn (pmPrimeMixedDensity ε P) (Ioi (0 : ℝ)) := by
  let f := pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε
  have hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))) :=
    memLp_pmFinitePrimePowerDampedFermiSource _ _
  have hd := pm_memLp_pos_dilate (pmqm_core_measurable _ _) hf (by exact_mod_cast hP : (0 : ℝ) < P)
  have hi : IntegrableOn (fun t => f t*(starRingEnd ℂ) (f ((P : ℝ)*t))) (Ioi (0 : ℝ)) :=
    hf.integrable_mul hd.star
  exact hi.re.const_mul ((P : ℝ)^(-ε))

private theorem pmqm_negative_core :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ P : ℕ in atTop, ∀ y : ℝ, 3/2 ≤ y → y ≤ 7/4 →
        c*(P : ℝ)^(2-2*ε)/Real.log (P : ℝ)^2 ≤
          -(pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε
            (1/(y*(P : ℝ)^2))).re := by
  filter_upwards [pmFinitePrimePowerDampedFermiSource_prime_square_negative,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)] with ε he hε
  obtain ⟨c,hc,he⟩ := he
  refine ⟨c/9,by positivity,?_⟩
  filter_upwards [he,eventually_ge_atTop (2 : ℕ)] with P heP hP
  intro y hy hyhi
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith only [hPr]
  have hlP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith only [hPr])
  let X : ℝ := y*(P : ℝ)^2
  have hPX : (P : ℝ)^2 ≤ X := by
    have hh := mul_le_mul_of_nonneg_right (by linarith only [hy] : 1 ≤ y) (sq_nonneg (P : ℝ))
    simpa only [one_mul] using hh
  have hX1 : 1 < X := by nlinarith only [hPX,hPr]
  have hX0 : 0 < X := by linarith only [hX1]
  have hXcube : X ≤ (P : ℝ)^3 := by
    have hh := mul_le_mul_of_nonneg_right (by linarith only [hyhi,hPr] : y ≤ (P : ℝ)) (sq_nonneg (P : ℝ))
    dsimp only [X]
    nlinarith only [hh]
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hlog : Real.log X ≤ 3*Real.log P := by
    have hh := Real.log_le_log hX0 hXcube
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hpow : (P : ℝ)^(2-2*ε) ≤ X^(1-ε) := by
    have hh := Real.rpow_le_rpow (sq_nonneg (P : ℝ)) hPX (by linarith only [hε.2] : 0 ≤ 1-ε)
    rw [← Real.rpow_natCast_mul hP0.le] at hh
    norm_num only [Nat.cast_ofNat] at hh
    rw [show (2 : ℝ)*(1-ε) = 2-2*ε by ring] at hh
    exact hh
  have hquot : (P : ℝ)^(2-2*ε)/(9*Real.log (P : ℝ)^2) ≤ X^(1-ε)/Real.log X^2 := by
    apply div_le_div₀ (by positivity) hpow (sq_pos_of_pos hlX)
    have hh := pow_le_pow_left₀ hlX.le hlog 2
    nlinarith only [hh]
  have hs := heP y hy hyhi
  change (pmFinitePrimePowerDampedFermiSource _ ε (1/X)).re ≤ -c*X^(1-ε)/Real.log X^2 at hs
  calc
    _ = c*((P : ℝ)^(2-2*ε)/(9*Real.log (P : ℝ)^2)) := by ring
    _ ≤ c*(X^(1-ε)/Real.log X^2) := mul_le_mul_of_nonneg_left hquot hc.le
    _ = -(-c*X^(1-ε)/Real.log X^2) := by ring
    _ ≤ _ := neg_le_neg hs

/-- The two actual coupled factors force a negative mixed-current density
throughout the prime-square slab. -/
theorem pmPrimeMixedDensity_prime_square_negative :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ P : ℕ in atTop, ∀ t ∈ Ioc (4/(7*(P : ℝ)^2)) (2/(3*(P : ℝ)^2)),
        c*(P : ℝ)^(3-4*ε)/Real.log (P : ℝ)^3 ≤ -pmPrimeMixedDensity ε P t := by
  filter_upwards [pmqm_negative_core,Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)]
    with ε hn hε
  obtain ⟨c,hc,hn⟩ := hn
  obtain ⟨d,hd,hpos⟩ := pmFinitePrimePowerDampedFermiSource_prime_slab_eventually_lower hε.1 hε.2
  refine ⟨c*d,by positivity,?_⟩
  filter_upwards [hn,hpos,eventually_ge_atTop (2 : ℕ)] with P hnP hpP hP
  intro t ht
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith only [hPr]
  have hlP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith only [hPr])
  have ht0 : 0 < t := (by positivity : (0 : ℝ) < 4/(7*(P : ℝ)^2)).trans ht.1
  let y : ℝ := 1/(t*(P : ℝ)^2)
  have hy : 3/2 ≤ y := by
    apply (le_div_iff₀ (by positivity : 0 < t*(P : ℝ)^2)).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 3*(P : ℝ)^2)).mp ht.2
    nlinarith only [hh]
  have hyhi : y ≤ 7/4 := by
    apply (div_le_iff₀ (by positivity : 0 < t*(P : ℝ)^2)).mpr
    have hh := (div_lt_iff₀ (by positivity : 0 < 7*(P : ℝ)^2)).mp ht.1
    nlinarith only [hh]
  have heq : 1/(y*(P : ℝ)^2) = t := by dsimp [y]; field_simp
  have hpeq : 1/(y*(P : ℝ)) = (P : ℝ)*t := by dsimp [y]; field_simp
  have hn := hnP y hy hyhi
  rw [heq] at hn
  have hp := hpP (y*(P : ℝ))
    (by nlinarith only [mul_le_mul_of_nonneg_right hy hP0.le])
    (by nlinarith only [mul_le_mul_of_nonneg_right hyhi hP0.le])
  rw [hpeq] at hp
  let f := pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε
  have hn0 : 0 ≤ -(f t).re := (by positivity : (0 : ℝ) ≤ c*(P : ℝ)^(2-2*ε)/Real.log (P : ℝ)^2).trans hn
  have hmul := mul_le_mul hn hp
    (by positivity : (0 : ℝ) ≤ d*(P : ℝ)^(1-ε)/Real.log (P : ℝ)) hn0
  have hw := mul_le_mul_of_nonneg_left hmul (Real.rpow_nonneg hP0.le (-ε))
  have hpower : (P : ℝ)^(-ε)*(P : ℝ)^(2-2*ε)*(P : ℝ)^(1-ε) = (P : ℝ)^(3-4*ε) := by
    rw [← Real.rpow_add hP0,← Real.rpow_add hP0]
    congr 1
    ring
  have hid : (P : ℝ)^(-ε)*
      ((c*(P : ℝ)^(2-2*ε)/Real.log (P : ℝ)^2)*
        (d*(P : ℝ)^(1-ε)/Real.log (P : ℝ))) =
      (c*d)*(P : ℝ)^(3-4*ε)/Real.log (P : ℝ)^3 := by
    rw [← hpower]
    ring
  rw [hid] at hw
  unfold pmPrimeMixedDensity
  rw [Complex.mul_re,Complex.conj_re,pmqm_core_im,zero_mul,sub_zero]
  nlinarith only [hw]

/-- Negative part of the actual mixed prime update above the reciprocal horizon. -/
def pmPrimeNegativeMixedMass (ε : ℝ) (P : ℕ) (X : ℝ) : ℝ :=
  ∫ t in Ioi (1/X), max (-pmPrimeMixedDensity ε P t) 0

theorem pmPrimeNegativeMixedMass_nonneg (ε : ℝ) (P : ℕ) (X : ℝ) :
    0 ≤ pmPrimeNegativeMixedMass ε P X := integral_nonneg fun _ => le_max_right _ _

theorem pmPrimeNegativeMixedMass_mono (ε : ℝ) {P : ℕ} (hP : 0 < P)
    {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    pmPrimeNegativeMixedMass ε P X ≤ pmPrimeNegativeMixedMass ε P Y := by
  have hY : 0 < Y := hX.trans_le hXY
  have hi : IntegrableOn (fun t => max (-pmPrimeMixedDensity ε P t) 0) (Ioi (0 : ℝ)) :=
    by
      have hn : Integrable (fun t => -pmPrimeMixedDensity ε P t) (volume.restrict (Ioi (0 : ℝ))) :=
        (integrableOn_pmPrimeMixedDensity ε hP).neg
      exact hn.sup (integrable_zero _ _ _)
  apply setIntegral_mono_set
    (hi.mono_set (fun t ht => (by positivity : (0 : ℝ) < 1/Y).trans ht))
    (Eventually.of_forall fun t => le_max_right _ _)
  exact Eventually.of_forall fun t ht => (one_div_le_one_div_of_le hX hXY).trans_lt ht

/-- Integrating the literal negative square slab gives a power-sized negative
part for each sufficiently large prime threshold. -/
theorem pmPrimeNegativeMixedMass_eventually_lower :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∃ c : ℝ, 0 < c ∧ ∀ᶠ P : ℕ in atTop,
      c*(P : ℝ)^(1-4*ε)/Real.log (P : ℝ)^3 ≤
        pmPrimeNegativeMixedMass ε P (2*(P : ℝ)^2) := by
  filter_upwards [pmPrimeMixedDensity_prime_square_negative] with ε he
  obtain ⟨c,hc,he⟩ := he
  refine ⟨2*c/21,by positivity,?_⟩
  filter_upwards [he,eventually_ge_atTop (2 : ℕ)] with P heP hP
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith only [hPr]
  have hlP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith only [hPr])
  let a : ℝ := 4/(7*(P : ℝ)^2)
  let b : ℝ := 2/(3*(P : ℝ)^2)
  let m : ℝ := c*(P : ℝ)^(3-4*ε)/Real.log (P : ℝ)^3
  have hab : a ≤ b := by
    apply (div_le_div_iff₀ (by positivity : 0 < 7*(P : ℝ)^2) (by positivity : 0 < 3*(P : ℝ)^2)).mpr
    nlinarith only [sq_nonneg (P : ℝ)]
  have hcut : 1/(2*(P : ℝ)^2) ≤ a := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2*(P : ℝ)^2) (by positivity : 0 < 7*(P : ℝ)^2)).mpr
    nlinarith only [sq_nonneg (P : ℝ)]
  have hi : IntegrableOn (fun t => max (-pmPrimeMixedDensity ε P t) 0) (Ioi (0 : ℝ)) :=
    by
      have hn : Integrable (fun t => -pmPrimeMixedDensity ε P t) (volume.restrict (Ioi (0 : ℝ))) :=
        (integrableOn_pmPrimeMixedDensity ε (P := P) (by omega)).neg
      exact hn.sup (integrable_zero _ _ _)
  have his : IntegrableOn (fun t => max (-pmPrimeMixedDensity ε P t) 0) (Ioc a b) :=
    hi.mono_set fun t ht => (by dsimp [a]; positivity : (0 : ℝ) < a).trans ht.1
  have hlocal : ∀ t ∈ Ioc a b, m ≤ max (-pmPrimeMixedDensity ε P t) 0 :=
    fun t ht => (heP t ht).trans (le_max_left _ _)
  have hf := setIntegral_mono_on (integrableOn_const measure_Ioc_lt_top.ne) his measurableSet_Ioc hlocal
  have hconst : (∫ _t in Ioc a b, m) = (b-a)*m := by
    rw [← intervalIntegral.integral_of_le hab,intervalIntegral.integral_const]
    rfl
  rw [hconst] at hf
  have hset := setIntegral_mono_set
    (s := Ioc a b) (hi.mono_set fun t ht =>
      (by positivity : (0 : ℝ) < 1/(2*(P : ℝ)^2)).trans ht)
    (Eventually.of_forall fun t => le_max_right (-pmPrimeMixedDensity ε P t) 0)
    (Eventually.of_forall fun t ht => hcut.trans_lt ht.1)
  have hid : (b-a)*m = (2*c/21)*(P : ℝ)^(1-4*ε)/Real.log (P : ℝ)^3 := by
    have hp : (P : ℝ)^(3-4*ε) = (P : ℝ)^2*(P : ℝ)^(1-4*ε) := by
      rw [show 3-4*ε = (2 : ℝ)+(1-4*ε) by ring,Real.rpow_add hP0,Real.rpow_two]
    dsimp only [a,b,m]
    rw [hp]
    field_simp
    ring
  rw [hid] at hf
  exact hf.trans hset

/-- The complete negative part of the literal mixed prime-update current. -/
def pmPrimeUpdateNegativeMixedCurrent (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ mobiusFinitePrimeAperture N, pmPrimeNegativeMixedMass ε p (N : ℝ)

theorem pmPrimeUpdateNegativeMixedCurrent_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ pmPrimeUpdateNegativeMixedCurrent ε N :=
  Finset.sum_nonneg fun p _ => pmPrimeNegativeMixedMass_nonneg ε p N

/-- A whole prime shell contributes a power-sized negative part to the actual
mixed current. This term must be retained by any complete compensation bound. -/
theorem pmPrimeUpdateNegativeMixedCurrent_eventually_lower :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∃ c : ℝ, 0 < c ∧ ∀ᶠ P : ℕ in atTop,
      c*(2*(P : ℝ))^(2-4*ε)/Real.log (2*(P : ℝ))^4 ≤
        pmPrimeUpdateNegativeMixedCurrent ε (8*P^2) := by
  filter_upwards [pmPrimeNegativeMixedMass_eventually_lower,
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)] with ε he hε
  obtain ⟨c,hc,he⟩ := he
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  have htop : Tendsto (fun P : ℕ => 2*P) atTop atTop :=
    tendsto_atTop_mono (fun P => by dsimp only [id]; omega) tendsto_id
  refine ⟨c/65536,by positivity,?_⟩
  filter_upwards [htop.eventually DeletionPrimePacket.upperPrime_card_eventually_lower,
    eventually_ge_atTop (max K 2)] with P hcard hP
  have hPK : K ≤ P := (le_max_left _ _).trans hP
  have hP2 : 2 ≤ P := (le_max_right _ _).trans hP
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP2
  have hP0 : (0 : ℝ) < P := by linarith only [hPr]
  have hlog : 0 < Real.log (2*(P : ℝ)) := Real.log_pos (by linarith only [hPr])
  let S := DeletionPeriodGrowth.upperPrimes (2*P)
  let b : ℝ := c*(P : ℝ)*(2*(P : ℝ))^(-4*ε)/Real.log (2*(P : ℝ))^3
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hmem (p : ℕ) (hp : p ∈ S) : p.Prime ∧ P < p ∧ p ≤ 2*P := by
    obtain ⟨hpi,hprime,hbig⟩ := Finset.mem_filter.mp hp
    exact ⟨hprime,by have := (Finset.mem_Icc.mp hpi).2; omega,(Finset.mem_Icc.mp hpi).2⟩
  have hsub : S ⊆ mobiusFinitePrimeAperture (8*P^2) := by
    intro p hp
    obtain ⟨hprime,_,hple⟩ := hmem p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,hprime⟩
    nlinarith only [hple,hP2]
  have hterm (p : ℕ) (hp : p ∈ S) :
      b ≤ pmPrimeNegativeMixedMass ε p ((8*P^2 : ℕ) : ℝ) := by
    obtain ⟨hprime,hPp,hpP⟩ := hmem p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpR : (p : ℝ) ≤ 2*(P : ℝ) := by exact_mod_cast hpP
    have hPpR : (P : ℝ) ≤ p := by exact_mod_cast hPp.le
    have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    have hX : 2*(p : ℝ)^2 ≤ ((8*P^2 : ℕ) : ℝ) := by
      push_cast
      nlinarith only [hpR,hp0,hP0]
    have hmass := (hK p (hPK.trans hPp.le)).trans
      (pmPrimeNegativeMixedMass_mono ε hprime.pos (by positivity) hX)
    have hpow := Real.rpow_le_rpow_of_nonpos hp0 hpR (show -4*ε ≤ 0 by linarith only [hε.1])
    have hlg := Real.log_le_log hp0 hpR
    have hnum : (P : ℝ)*(2*(P : ℝ))^(-4*ε) ≤ (p : ℝ)^(1-4*ε) := by
      rw [show 1-4*ε = (1 : ℝ)+(-4*ε) by ring,Real.rpow_add hp0,Real.rpow_one]
      exact mul_le_mul hPpR hpow (Real.rpow_nonneg (by positivity) _) hp0.le
    calc
      b ≤ c*(p : ℝ)^(1-4*ε)/Real.log (p : ℝ)^3 := by
        exact div_le_div₀ (by positivity)
          (by nlinarith only [mul_le_mul_of_nonneg_left hnum hc.le])
          (by positivity) (pow_le_pow_left₀ hlp.le hlg 3)
      _ ≤ _ := hmass
  have hsum : (S.card : ℝ)*b ≤ pmPrimeUpdateNegativeMixedCurrent ε (8*P^2) := by
    calc
      _ = ∑ _p ∈ S,b := by simp
      _ ≤ ∑ p ∈ S,pmPrimeNegativeMixedMass ε p ((8*P^2 : ℕ) : ℝ) := Finset.sum_le_sum hterm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => pmPrimeNegativeMixedMass_nonneg _ _ _)
  have hcard' : 2*(P : ℝ)/(32768*Real.log (2*(P : ℝ))) ≤ (S.card : ℝ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hcard
  calc
    _ = (2*(P : ℝ)/(32768*Real.log (2*(P : ℝ))))*b := by
      rw [show 2-4*ε = (2 : ℝ)+(-4*ε) by ring,
        Real.rpow_add (by positivity : 0 < 2*(P : ℝ)),Real.rpow_two]
      dsimp only [b]
      field_simp
      ring
    _ ≤ (S.card : ℝ)*b := mul_le_mul_of_nonneg_right hcard' hb
    _ ≤ _ := hsum

/-- Every power below the negative-current exponent is exceeded. A separate
subpower bound for this negative part cannot close the PM energy argument. -/
theorem pmPrimeUpdateNegativeMixedCurrent_div_rpow_tendsto_atTop :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ κ : ℝ, κ < 1-2*ε →
      Tendsto (fun P : ℕ => pmPrimeUpdateNegativeMixedCurrent ε (8*P^2) /
        (((8*P^2 : ℕ) : ℝ)^κ)) atTop atTop := by
  filter_upwards [pmPrimeUpdateNegativeMixedCurrent_eventually_lower] with ε he
  intro κ hκ
  obtain ⟨c,hc,he⟩ := he
  let β : ℝ := 2-4*ε-2*κ
  have hβ : 0 < β := by dsimp only [β]; linarith only [hκ]
  let d : ℝ := c/(2 : ℝ)^κ
  have hd : 0 < d := by dsimp only [d]; positivity
  have htop : Tendsto (fun P : ℕ => 2*(P : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
  apply tendsto_atTop.mpr
  intro b
  have hB : 0 < |b|+1 := by positivity
  have hs := ((isLittleO_log_rpow_rpow_atTop (4 : ℝ) hβ).comp_tendsto htop).bound
    (c := d/(|b|+1)) (by positivity)
  filter_upwards [he,hs,eventually_ge_atTop 2] with P heP hsP hP
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hY : 0 < 2*(P : ℝ) := by positivity
  have hl : 0 < Real.log (2*(P : ℝ)) := Real.log_pos (by linarith only [hPr])
  have hden : 0 < ((8*P^2 : ℕ) : ℝ)^κ := Real.rpow_pos_of_pos (by positivity) _
  change ‖Real.log (2*(P : ℝ))^(4 : ℝ)‖ ≤ d/(|b|+1)*‖(2*(P : ℝ))^β‖ at hsP
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hY.le _),
    show Real.log (2*(P : ℝ))^(4 : ℝ) = Real.log (2*(P : ℝ))^(4 : ℕ)
      from Real.rpow_natCast _ 4] at hsP
  have hsmall : |b|+1 ≤ d*(2*(P : ℝ))^β/Real.log (2*(P : ℝ))^4 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hsP hB.le
    calc
      _ ≤ (|b|+1)*(d/(|b|+1)*(2*(P : ℝ))^β) := hh
      _ = _ := by field_simp
  have hN : ((8*P^2 : ℕ) : ℝ) = 2*(2*(P : ℝ))^2 := by push_cast; ring
  have hpow : (2*(P : ℝ))^(2-4*ε) / (((8*P^2 : ℕ) : ℝ)^κ) =
      (2*(P : ℝ))^β/(2 : ℝ)^κ := by
    rw [hN,Real.mul_rpow (by norm_num) (sq_nonneg _),
      ← Real.rpow_natCast_mul hY.le 2 κ,
      show 2-4*ε = β+2*κ by dsimp only [β]; ring,Real.rpow_add hY]
    field_simp
    congr 1
    norm_num [mul_comm]
  have hscaled := div_le_div_of_nonneg_right heP hden.le
  calc
    b ≤ |b|+1 := by linarith only [le_abs_self b]
    _ ≤ d*(2*(P : ℝ))^β/Real.log (2*(P : ℝ))^4 := hsmall
    _ = (c*(2*(P : ℝ))^(2-4*ε)/Real.log (2*(P : ℝ))^4) /
        (((8*P^2 : ℕ) : ℝ)^κ) := by
      calc
        _ = c*((2*(P : ℝ))^β/(2 : ℝ)^κ)/Real.log (2*(P : ℝ))^4 := by dsimp only [d]; ring
        _ = _ := by rw [← hpow]; ring
    _ ≤ _ := hscaled

end RHTower
