import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeSlabBounds
import GaloisForLFunctions.RHTower.EulerDeletionWeightedPrimeCancellation
import GaloisForLFunctions.RHTower.PMRamanujanCompleteAperture

/-!
# The positive quadratic current of the actual prime updates

The canonical prime core carries a positive first slab. Its truncated energy
therefore gives a lower bound on the positive quadratic terms in the complete
prime-update energy identity.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Inserting one fresh prime gives the literal dilation update, with no
discarded physical boundary term. -/
theorem pmFinitePrimePowerDampedFermiSource_insert (ε : ℝ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime) (hpS : p ∉ S)
    {t : ℝ} (ht : 0 < t) :
    pmFinitePrimePowerDampedFermiSource (insert p S) ε t =
      pmFinitePrimePowerDampedFermiSource S ε t -
        (((p : ℝ)^(-ε) : ℝ) : ℂ)*pmFinitePrimePowerDampedFermiSource S ε ((p : ℝ)*t) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hSp : ∀ q ∈ insert p S, q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hS q hq
  rw [pmFinitePrimePowerDampedFermiSource_eq_floor_difference ε _ hSp ht,
    pmFinitePrimePowerDampedFermiSource_eq_floor_difference ε _ hS ht,
    pmFinitePrimePowerDampedFermiSource_eq_floor_difference ε _ hS (mul_pos hp0 ht),
    pmCompleteMobiusFloor_insert ε S hS hp hpS,
    pmCompleteMobiusFloor_insert ε S hS hp hpS]
  rw [show 1/((p : ℝ)*t) = (1/t)/(p : ℝ) by ring,
    show 1/(2*((p : ℝ)*t)) = (1/(2*t))/(p : ℝ) by ring,
    Nat.floor_div_natCast,Nat.floor_div_natCast]
  ring

/-- Physical energy of the canonical core retaining precisely the primes below
`P`, above reciprocal horizon `1/X`. -/
def pmPrimeCoreTruncatedEnergy (ε : ℝ) (P : ℕ) (X : ℝ) : ℝ :=
  ∫ t in Ioi (1/X),
    ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε t‖^2

theorem pmPrimeCoreTruncatedEnergy_nonneg (ε : ℝ) (P : ℕ) (X : ℝ) :
    0 ≤ pmPrimeCoreTruncatedEnergy ε P X :=
  integral_nonneg fun _ => sq_nonneg _

theorem pmPrimeCoreTruncatedEnergy_mono (ε : ℝ) (P : ℕ)
    {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    pmPrimeCoreTruncatedEnergy ε P X ≤ pmPrimeCoreTruncatedEnergy ε P Y := by
  have hY : 0 < Y := hX.trans_le hXY
  have hint : IntegrableOn
      (fun t => ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε t‖^2)
      (Ioi (0 : ℝ)) := (memLp_pmFinitePrimePowerDampedFermiSource
        (mobiusFinitePrimeAperture (P-1)) ε).norm.integrable_sq
  apply setIntegral_mono_set (hint.mono_set (fun t ht => (by positivity : (0 : ℝ) < 1/Y).trans ht))
    (Eventually.of_forall fun t => sq_nonneg _)
  exact Eventually.of_forall fun t ht =>
    (one_div_le_one_div_of_le hX hXY).trans_lt ht

/-- The first slab forces power-sized energy in the actual prime core at twice
its aperture threshold. -/
theorem pmPrimeCoreTruncatedEnergy_eventually_lower {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ P : ℕ in atTop,
      c*(P : ℝ)^(1-2*ε)/Real.log (P : ℝ)^2 ≤
        pmPrimeCoreTruncatedEnergy ε P (2*(P : ℝ)) := by
  obtain ⟨c,hc,he⟩ := pmFinitePrimePowerDampedFermiSource_prime_slab_eventually_lower hε hεhalf
  refine ⟨2*c^2/21,by positivity,?_⟩
  filter_upwards [he,eventually_ge_atTop 2] with P heP hP
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  let m : ℝ := c*(P : ℝ)^(1-ε)/Real.log (P : ℝ)
  have hm : 0 ≤ m := by dsimp only [m]; positivity
  let f := pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε
  have hband : 4/(7*(P : ℝ)) ≤ 2/(3*(P : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  have hcut : 1/(2*(P : ℝ)) ≤ 4/(7*(P : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  have hlocal (t : ℝ) (ht : t ∈ Ioc (4/(7*(P : ℝ))) (2/(3*(P : ℝ)))) :
      m^2 ≤ ‖f t‖^2 := by
    have ht0 : 0 < t := (by positivity : (0 : ℝ) < 4/(7*(P : ℝ))).trans ht.1
    have hxlo : 3*(P : ℝ)/2 ≤ 1/t := by
      apply (le_div_iff₀ ht0).mpr
      have hh := (le_div_iff₀ (by positivity : 0 < 3*(P : ℝ))).mp ht.2
      nlinarith
    have hxhi : 1/t ≤ 7*(P : ℝ)/4 := by
      apply (div_le_iff₀ ht0).mpr
      have hh := (div_lt_iff₀ (by positivity : 0 < 7*(P : ℝ))).mp ht.1
      nlinarith
    have hv := heP (1/t) hxlo hxhi
    rw [one_div_one_div] at hv
    exact pow_le_pow_left₀ hm (hv.trans (Complex.re_le_norm (f t))) 2
  have hint : IntegrableOn (fun t => ‖f t‖^2) (Ioi (0 : ℝ)) :=
    (memLp_pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε).norm.integrable_sq
  have hintslab : IntegrableOn (fun t => ‖f t‖^2)
      (Ioc (4/(7*(P : ℝ))) (2/(3*(P : ℝ)))) :=
    hint.mono_set fun t ht => (by positivity : (0 : ℝ) < 4/(7*(P : ℝ))).trans ht.1
  have hconst : (∫ _t in Ioc (4/(7*(P : ℝ))) (2/(3*(P : ℝ))), m^2) =
      (2/(3*(P : ℝ))-4/(7*(P : ℝ)))*m^2 := by
    rw [← intervalIntegral.integral_of_le hband,intervalIntegral.integral_const]
    rfl
  have hfloor := setIntegral_mono_on (integrableOn_const measure_Ioc_lt_top.ne)
    hintslab measurableSet_Ioc hlocal
  rw [hconst] at hfloor
  have hset := setIntegral_mono_set
    (s := Ioc (4/(7*(P : ℝ))) (2/(3*(P : ℝ))))
    (hint.mono_set (fun t ht => (by positivity : (0 : ℝ) < 1/(2*(P : ℝ))).trans ht))
    (Eventually.of_forall fun t => sq_nonneg ‖f t‖)
    (Eventually.of_forall fun t ht => hcut.trans_lt ht.1)
  have hid : (2/(3*(P : ℝ))-4/(7*(P : ℝ)))*m^2 =
      (2*c^2/21)*(P : ℝ)^(1-2*ε)/Real.log (P : ℝ)^2 := by
    have hp : ((P : ℝ)^(1-ε))^2 = (P : ℝ)*(P : ℝ)^(1-2*ε) := by
      calc
        _ = (P : ℝ)^((1-ε)*(2 : ℝ)) := (Real.rpow_mul_natCast hP0.le _ 2).symm
        _ = (P : ℝ)^((1 : ℝ)+(1-2*ε)) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hP0,Real.rpow_one]
    dsimp only [m]
    rw [div_pow,mul_pow,hp]
    field_simp
    ring
  rw [hid] at hfloor
  exact hfloor.trans hset

/-- The positive square terms in successive literal prime insertions. -/
def pmPrimeUpdateQuadraticCurrent (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ mobiusFinitePrimeAperture N, (p : ℝ)^(-2*ε) *
    ∫ t in Ioi (1/(N : ℝ)),
      ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (p-1)) ε ((p : ℝ)*t)‖^2

theorem pmPrimeUpdateQuadraticCurrent_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ pmPrimeUpdateQuadraticCurrent ε N := by
  exact Finset.sum_nonneg fun p _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    (integral_nonneg fun _ => sq_nonneg _)

/-- Dilation places the same canonical prime core at the cofactor horizon. -/
theorem pmPrimeUpdateQuadraticCurrent_eq_scaled_energy (ε : ℝ) (N : ℕ) :
    pmPrimeUpdateQuadraticCurrent ε N =
      ∑ p ∈ mobiusFinitePrimeAperture N,
        (p : ℝ)^(-1-2*ε)*pmPrimeCoreTruncatedEnergy ε p ((N : ℝ)/p) := by
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  rw [integral_comp_mul_left_Ioi
    (fun u : ℝ => ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (p-1)) ε u‖^2)
    (1/(N : ℝ)) hp0]
  simp only [smul_eq_mul,pmPrimeCoreTruncatedEnergy]
  rw [show (p : ℝ)*(1/(N : ℝ)) = 1/((N : ℝ)/p) by simp [div_eq_mul_inv,mul_comm]]
  have hpow : (p : ℝ)^(-1-2*ε) = (p : ℝ)^(-2*ε)*(p : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hp0]
    congr 1
    ring
  rw [hpow,mul_assoc]

/-- A first-band energy floor at every large prime forces a power lower bound
for the complete positive quadratic prime-update current. -/
theorem pmPrimeUpdateQuadraticCurrent_eventually_lower {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ P : ℕ in atTop,
      c*(2*(P : ℝ))^(1-4*ε)/Real.log (2*(P : ℝ))^3 ≤
        pmPrimeUpdateQuadraticCurrent ε (8*P^2) := by
  obtain ⟨c,hc,he⟩ := pmPrimeCoreTruncatedEnergy_eventually_lower hε hεhalf
  obtain ⟨K,hK⟩ := eventually_atTop.mp he
  have htop : Tendsto (fun P : ℕ => 2*P) atTop atTop :=
    tendsto_atTop_mono (fun P => by dsimp only [id]; omega) tendsto_id
  refine ⟨c/32768,by positivity,?_⟩
  filter_upwards [htop.eventually DeletionPrimePacket.upperPrime_card_eventually_lower,
    eventually_ge_atTop (max K 2)] with P hcard hP
  have hPK : K ≤ P := (le_max_left _ _).trans hP
  have hP2 : 2 ≤ P := (le_max_right _ _).trans hP
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP2
  have hP0 : (0 : ℝ) < P := by linarith
  have hlog : 0 < Real.log (2*(P : ℝ)) := Real.log_pos (by linarith)
  let S := DeletionPeriodGrowth.upperPrimes (2*P)
  let b : ℝ := c*(2*(P : ℝ))^(-4*ε)/Real.log (2*(P : ℝ))^2
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hmem (p : ℕ) (hp : p ∈ S) : p.Prime ∧ P < p ∧ p ≤ 2*P := by
    obtain ⟨hpi,hprime,hbig⟩ := Finset.mem_filter.mp hp
    have hple := (Finset.mem_Icc.mp hpi).2
    exact ⟨hprime,by omega,hple⟩
  have hsub : S ⊆ mobiusFinitePrimeAperture (8*P^2) := by
    intro p hp
    obtain ⟨hprime,_,hple⟩ := hmem p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,hprime⟩
    nlinarith
  have hterm (p : ℕ) (hp : p ∈ S) :
      b ≤ (p : ℝ)^(-1-2*ε)*pmPrimeCoreTruncatedEnergy ε p (((8*P^2 : ℕ) : ℝ)/p) := by
    obtain ⟨hprime,hPp,hpP⟩ := hmem p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpR : (p : ℝ) ≤ 2*(P : ℝ) := by exact_mod_cast hpP
    have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    have hX : 2*(p : ℝ) ≤ (((8*P^2 : ℕ) : ℝ)/p) := by
      apply (le_div_iff₀ hp0).mpr
      push_cast
      nlinarith
    have henergy := (hK p (hPK.trans hPp.le)).trans
      (pmPrimeCoreTruncatedEnergy_mono ε p (by positivity) hX)
    have hpow := Real.rpow_le_rpow_of_nonpos hp0 hpR (show -4*ε ≤ 0 by linarith)
    have hlg := Real.log_le_log hp0 hpR
    calc
      _ ≤ c*(p : ℝ)^(-4*ε)/Real.log (p : ℝ)^2 := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpow hc.le) (by positivity)
        exact pow_le_pow_left₀ hlp.le hlg 2
      _ = (p : ℝ)^(-1-2*ε)*(c*(p : ℝ)^(1-2*ε)/Real.log (p : ℝ)^2) := by
        have hi : (p : ℝ)^(-4*ε) = (p : ℝ)^(-1-2*ε)*(p : ℝ)^(1-2*ε) := by
          rw [← Real.rpow_add hp0]
          congr 1
          ring
        rw [hi]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left henergy (by positivity)
  have hsum : (S.card : ℝ)*b ≤ pmPrimeUpdateQuadraticCurrent ε (8*P^2) := by
    rw [pmPrimeUpdateQuadraticCurrent_eq_scaled_energy]
    calc
      _ = ∑ _p ∈ S, b := by simp
      _ ≤ ∑ p ∈ S, (p : ℝ)^(-1-2*ε)*
          pmPrimeCoreTruncatedEnergy ε p (((8*P^2 : ℕ) : ℝ)/p) := Finset.sum_le_sum hterm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)
          (pmPrimeCoreTruncatedEnergy_nonneg _ _ _))
  have hcard' : (2*(P : ℝ))/(32768*Real.log (2*(P : ℝ))) ≤ (S.card : ℝ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hcard
  calc
    _ = ((2*(P : ℝ))/(32768*Real.log (2*(P : ℝ))))*b := by
      have hi : (2*(P : ℝ))^(1-4*ε) =
          (2*(P : ℝ))*(2*(P : ℝ))^(-4*ε) := by
        rw [show 1-4*ε = (1 : ℝ)+(-4*ε) by ring,
          Real.rpow_add (by positivity),Real.rpow_one]
      rw [hi]
      dsimp only [b]
      field_simp
    _ ≤ (S.card : ℝ)*b := mul_le_mul_of_nonneg_right hcard' hb
    _ ≤ _ := hsum

/-- Every power below the intrinsic first-band exponent is exceeded by the
positive current. The mixed current has not been discarded from the RH target. -/
theorem pmPrimeUpdateQuadraticCurrent_div_rpow_tendsto_atTop {ε κ : ℝ}
    (hε : 0 < ε) (hκ0 : 0 ≤ κ) (hκ : κ < 1/2-2*ε) :
    Tendsto (fun P : ℕ => pmPrimeUpdateQuadraticCurrent ε (8*P^2) /
      (((8*P^2 : ℕ) : ℝ)^κ)) atTop atTop := by
  obtain ⟨c,hc,he⟩ := pmPrimeUpdateQuadraticCurrent_eventually_lower hε (by linarith)
  let β : ℝ := 1-4*ε-2*κ
  have hβ : 0 < β := by dsimp only [β]; linarith
  let d : ℝ := c/(2 : ℝ)^κ
  have hd : 0 < d := by dsimp only [d]; positivity
  have htop : Tendsto (fun P : ℕ => 2*(P : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
  apply tendsto_atTop.mpr
  intro b
  have hB : 0 < |b|+1 := by positivity
  have hs := ((isLittleO_log_rpow_rpow_atTop (3 : ℝ) hβ).comp_tendsto htop).bound
    (c := d/(|b|+1)) (by positivity)
  filter_upwards [he,hs,eventually_ge_atTop 2] with P heP hsP hP
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hY : 0 < 2*(P : ℝ) := by positivity
  have hl : 0 < Real.log (2*(P : ℝ)) := Real.log_pos (by linarith)
  have hden : 0 < ((8*P^2 : ℕ) : ℝ)^κ := Real.rpow_pos_of_pos (by positivity) _
  change ‖Real.log (2*(P : ℝ))^(3 : ℝ)‖ ≤ d/(|b|+1)*‖(2*(P : ℝ))^β‖ at hsP
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hY.le _),
    show Real.log (2*(P : ℝ))^(3 : ℝ) = Real.log (2*(P : ℝ))^(3 : ℕ)
      from Real.rpow_natCast _ 3] at hsP
  have hsmall : |b|+1 ≤ d*(2*(P : ℝ))^β/Real.log (2*(P : ℝ))^3 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hsP hB.le
    calc
      _ ≤ (|b|+1)*(d/(|b|+1)*(2*(P : ℝ))^β) := hh
      _ = _ := by field_simp
  have hN : ((8*P^2 : ℕ) : ℝ) = 2*(2*(P : ℝ))^2 := by push_cast; ring
  have hpow : (2*(P : ℝ))^(1-4*ε) / (((8*P^2 : ℕ) : ℝ)^κ) =
      (2*(P : ℝ))^β/(2 : ℝ)^κ := by
    rw [hN,Real.mul_rpow (by norm_num) (sq_nonneg _),
      ← Real.rpow_natCast_mul hY.le 2 κ,
      show 1-4*ε = β+2*κ by dsimp only [β]; ring,
      Real.rpow_add hY]
    field_simp
    congr 1
    norm_num [mul_comm]
  have hscaled := div_le_div_of_nonneg_right heP hden.le
  calc
    b ≤ |b|+1 := by linarith [le_abs_self b]
    _ ≤ d*(2*(P : ℝ))^β/Real.log (2*(P : ℝ))^3 := hsmall
    _ = (c*(2*(P : ℝ))^(1-4*ε)/Real.log (2*(P : ℝ))^3) /
        (((8*P^2 : ℕ) : ℝ)^κ) := by
      calc
        _ = c*((2*(P : ℝ))^β/(2 : ℝ)^κ)/Real.log (2*(P : ℝ))^3 := by dsimp only [d]; ring
        _ = _ := by rw [← hpow]; ring
    _ ≤ _ := hscaled

end RHTower
