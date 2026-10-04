import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeSlab
import GaloisForLFunctions.RHTower.PMRamanujanComplementarySourceBounds
import GaloisForLFunctions.RHTower.Sieve.ShortIntervalThetaEveryWindow
import GaloisForLFunctions.RHTower.PrimeCountShell

/-!
# Uniform cancellation on the first prime-aperture slab

The actual full source has logarithmic cancellation uniformly on the first band
of a prime aperture. The missing positive prime mass dominates this remainder.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

private theorem pms_remainder_floor_bound (ε : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖pmPowerDampedDivisorRemainder ε x‖ ≤
      ‖pmPowerDampedDivisorRemainder ε (⌊x⌋₊ : ℕ)‖ + ‖pmPowerDampedDivisorDensity ε‖ := by
  have hid : pmPowerDampedDivisorRemainder ε x =
      pmPowerDampedDivisorRemainder ε (⌊x⌋₊ : ℕ) -
        pmPowerDampedDivisorDensity ε * ((x - (⌊x⌋₊ : ℝ) : ℝ) : ℂ) := by
    simp only [pmPowerDampedDivisorRemainder, pmPowerDampedDivisorSum, Nat.floor_natCast]
    push_cast
    ring
  have hnorm : ‖((x - (⌊x⌋₊ : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le hx))]
    have := Nat.lt_floor_add_one x
    linarith
  rw [hid]
  calc
    _ ≤ ‖pmPowerDampedDivisorRemainder ε (⌊x⌋₊ : ℕ)‖ +
        ‖pmPowerDampedDivisorDensity ε * ((x - (⌊x⌋₊ : ℝ) : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_mul]
      have hb := mul_le_mul_of_nonneg_left hnorm (norm_nonneg (pmPowerDampedDivisorDensity ε))
      rw [mul_one] at hb
      exact add_le_add le_rfl hb

private theorem pms_remainder_slab_bound {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ᶠ P : ℕ in atTop,
      ∀ x : ℝ, (P : ℝ)/2 ≤ x → x ≤ 2*(P : ℝ) →
        ‖pmPowerDampedDivisorRemainder ε x‖ ≤
          A + D*(P : ℝ)^(1-ε)/Real.log (P : ℝ)^4 := by
  obtain ⟨C, hC, he⟩ := pmPowerDampedDivisorRemainder_eventually_log_four hε hεhalf
  obtain ⟨K, hK⟩ := eventually_atTop.mp he
  refine ⟨1 + ‖pmPowerDampedDivisorDensity ε‖, 16*C*(2 : ℝ)^(1-ε),
    by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (4*K+16)] with P hP x hxlo hxhi
  have hPR : (16 : ℝ) ≤ P := by exact_mod_cast (by omega : 16 ≤ P)
  have hP0 : (0 : ℝ) < P := by linarith
  have hx0 : 0 ≤ x := by linarith
  let n := ⌊x⌋₊
  have hnlo : (P : ℝ)/4 ≤ n := by
    have := Nat.lt_floor_add_one x
    dsimp only [n]
    linarith
  have hnhi : (n : ℝ) ≤ 2*(P : ℝ) := (Nat.floor_le hx0).trans hxhi
  have hn0 : (0 : ℝ) < n := by linarith
  have hKn : K ≤ n := by
    have hKPR : (4 : ℝ)*K+16 ≤ P := by exact_mod_cast hP
    have : (K : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hlP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hln : Real.log (P : ℝ)/2 ≤ Real.log (n : ℝ) := by
    have hsq : (P : ℝ) ≤ (n : ℝ)^2 := by nlinarith
    have hh := Real.log_le_log hP0 hsq
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hp : (n : ℝ)^(1-ε) ≤ (2*(P : ℝ))^(1-ε) :=
    Real.rpow_le_rpow hn0.le hnhi (by linarith)
  have hb := pms_remainder_floor_bound ε hx0
  have hc := hK n hKn
  have hmain : C*(n : ℝ)^(1-ε)/Real.log (n : ℝ)^4 ≤
      16*C*(2 : ℝ)^(1-ε)*(P : ℝ)^(1-ε)/Real.log (P : ℝ)^4 := by
    calc
      _ ≤ C*(2*(P : ℝ))^(1-ε)/(Real.log (P : ℝ)/2)^4 := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hp hC) (by positivity)
        exact pow_le_pow_left₀ (by positivity) hln 4
      _ = _ := by rw [Real.mul_rpow (by norm_num) hP0.le, div_pow]; ring
  change ‖pmPowerDampedDivisorRemainder ε x‖ ≤
    1 + ‖pmPowerDampedDivisorDensity ε‖ +
      16*C*(2 : ℝ)^(1-ε)*(P : ℝ)^(1-ε)/Real.log (P : ℝ)^4
  linarith

/-- Uniform unconditional logarithmic cancellation of the full source on the
physical first slab, before extracting any prime-current terms. -/
theorem pmPowerDampedFermiSource_prime_slab_bound {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ᶠ P : ℕ in atTop,
      ∀ x : ℝ, 3*(P : ℝ)/2 ≤ x → x ≤ 7*(P : ℝ)/4 →
        ‖pmPowerDampedFermiSource ε (1/x)‖ ≤
          A + D*(P : ℝ)^(1-ε)/Real.log (P : ℝ)^4 := by
  obtain ⟨A,D,hA,hD,he⟩ := pms_remainder_slab_bound hε hεhalf
  refine ⟨3*A,3*D,by positivity,by positivity,?_⟩
  filter_upwards [he,eventually_ge_atTop 1] with P hP hP1 x hxlo hxhi
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP1
  have hx0 : 0 < x := by linarith
  have h1 := hP x (by linarith) (by linarith)
  have h2 := hP (x/2) (by linarith) (by linarith)
  have hid : pmPowerDampedFermiSource ε (1/x) =
      pmPowerDampedDivisorRemainder ε x - 2*pmPowerDampedDivisorRemainder ε (x/2) := by
    rw [pmPowerDampedFermiSource_eq_centered_difference ε (by positivity)]
    simp only [pmPowerDampedCenteredSource, one_div_one_div]
    congr 2
    field_simp
  rw [hid]
  have hb := norm_sub_le (pmPowerDampedDivisorRemainder ε x)
    (2*pmPowerDampedDivisorRemainder ε (x/2))
  rw [norm_mul, norm_ofNat] at hb
  calc
    _ ≤ (A+D*(P : ℝ)^(1-ε)/Real.log (P : ℝ)^4) +
        2*(A+D*(P : ℝ)^(1-ε)/Real.log (P : ℝ)^4) :=
      hb.trans (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num)))
    _ = _ := by ring

private theorem pms_prime_shell_count :
    ∀ᶠ P : ℕ in atTop,
      (P : ℝ)/(65536*Real.log (P : ℝ)) ≤
        (primeShellCard (P : ℝ) (3*(P : ℝ)/2) : ℝ) := by
  obtain ⟨X,_,hwin⟩ := Sieve.exists_theta_window_lower
    (α := (3 : ℝ)/4) (by norm_num) (by norm_num)
  have htop : Tendsto (fun P : ℕ => 3*(P : ℝ)/2) atTop atTop :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)).atTop_div_const
      (by norm_num)
  have hs := ((tendsto_rpow_neg_atTop (y := (1 : ℝ)/4) (by norm_num)).comp htop).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/6))
  have hx := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop X
  filter_upwards [hs,hx,eventually_ge_atTop 2] with P hsP hPX hP
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hy0 : 0 < 3*(P : ℝ)/2 := by positivity
  have hlP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hly : 0 < Real.log (3*(P : ℝ)/2) := Real.log_pos (by linarith)
  have hpow : (3*(P : ℝ)/2)^((3 : ℝ)/4) ≤ (P : ℝ)/4 := by
    have hid : (3*(P : ℝ)/2)^((3 : ℝ)/4) =
        (3*(P : ℝ)/2)*(3*(P : ℝ)/2)^(-((1 : ℝ)/4)) := by
      calc
        _ = (3*(P : ℝ)/2)^((1 : ℝ)+-((1 : ℝ)/4)) := by congr 1; norm_num
        _ = _ := by rw [Real.rpow_add hy0,Real.rpow_one]
    rw [hid]
    change (3*(P : ℝ)/2)^(-((1 : ℝ)/4)) ≤ 1/6 at hsP
    have hh := mul_le_mul_of_nonneg_left hsP hy0.le
    linarith
  have hw := hwin (P : ℝ) ((P : ℝ)/2) hPX (by positivity)
  rw [show (P : ℝ)+(P : ℝ)/2 = 3*(P : ℝ)/2 by ring] at hw
  have hm : (P : ℝ)/32768 ≤ Chebyshev.theta (3*(P : ℝ)/2)-Chebyshev.theta P := by
    linarith
  have hl : Real.log (3*(P : ℝ)/2) ≤ 2*Real.log (P : ℝ) := by
    have hh := Real.log_le_log hy0 (show 3*(P : ℝ)/2 ≤ (P : ℝ)^2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  calc
    _ = ((P : ℝ)/32768)/(2*Real.log (P : ℝ)) := by ring
    _ ≤ ((P : ℝ)/32768)/Real.log (3*(P : ℝ)/2) :=
      div_le_div_of_nonneg_left (by positivity) hly hl
    _ ≤ (Chebyshev.theta (3*(P : ℝ)/2)-Chebyshev.theta P)/Real.log (3*(P : ℝ)/2) :=
      div_le_div_of_nonneg_right hm hly.le
    _ ≤ _ := (primeShellCard_bounds (by linarith : (1 : ℝ) < P) (by linarith)).1

/-- The literal missing primes supply a uniform positive mass on the slab. -/
theorem pmPrimeSlabMass_eventually_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ P : ℕ in atTop,
      ∀ x : ℝ, 3*(P : ℝ)/2 ≤ x →
        c*(P : ℝ)^(1-ε)/Real.log (P : ℝ) ≤ pmPrimeSlabMass ε P x := by
  refine ⟨(2 : ℝ)^(-ε)/65536, by positivity, ?_⟩
  filter_upwards [pms_prime_shell_count,eventually_ge_atTop 2] with P hc hP x hx
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hl : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  let S := (Finset.Ioc P ⌊3*(P : ℝ)/2⌋₊).filter Nat.Prime
  have hsub : S ⊆ (Finset.Icc P ⌊x⌋₊).filter Nat.Prime := by
    intro q hq
    obtain ⟨hqi,hp⟩ := Finset.mem_filter.mp hq
    obtain ⟨hPq,hqy⟩ := Finset.mem_Ioc.mp hqi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hPq.le, hqy.trans (Nat.floor_mono hx)⟩, hp⟩
  have hs : (S.card : ℝ)*(2*(P : ℝ))^(-ε) ≤ pmPrimeSlabMass ε P x := by
    calc
      _ = ∑ _q ∈ S, (2*(P : ℝ))^(-ε) := by simp
      _ ≤ ∑ q ∈ S, (q : ℝ)^(-ε) := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hqi,hprime⟩ := Finset.mem_filter.mp hq
        have hqy : (q : ℝ) ≤ 3*(P : ℝ)/2 :=
          (show (q : ℝ) ≤ ⌊3*(P : ℝ)/2⌋₊ by exact_mod_cast (Finset.mem_Ioc.mp hqi).2).trans
            (Nat.floor_le (by positivity))
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hprime.pos)
          (by linarith) (by linarith)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun q _ _ => Real.rpow_nonneg (Nat.cast_nonneg q) _)
  have hcard : (P : ℝ)/(65536*Real.log (P : ℝ)) ≤ (S.card : ℝ) := by
    simpa only [primeShellCard,Nat.floor_natCast] using hc
  calc
    _ = ((P : ℝ)/(65536*Real.log (P : ℝ)))*(2*(P : ℝ))^(-ε) := by
      rw [Real.mul_rpow (by norm_num) hP0.le, Real.rpow_sub hP0, Real.rpow_one,
        Real.rpow_neg hP0.le]
      ring
    _ ≤ (S.card : ℝ)*(2*(P : ℝ))^(-ε) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ _ := hs

/-- The full source is uniformly negligible compared with the actual missing
prime mass. No norm-admission premise is used. -/
theorem pmPowerDampedFermiSource_prime_slab_relative_small {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ P : ℕ in atTop, ∀ x : ℝ,
      3*(P : ℝ)/2 ≤ x → x ≤ 7*(P : ℝ)/4 →
        ‖pmPowerDampedFermiSource ε (1/x)‖ ≤ δ*pmPrimeSlabMass ε P x := by
  obtain ⟨A,D,_,_,hb⟩ := pmPowerDampedFermiSource_prime_slab_bound hε hεhalf
  obtain ⟨c,hc,hm⟩ := pmPrimeSlabMass_eventually_lower hε
  have ha : 0 < 1-ε := by linarith
  have h1 : Tendsto (fun P : ℕ => A*Real.log (P : ℝ)/(P : ℝ)^(1-ε)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc, Function.comp_def] using
      ((isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul A
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)^3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h2 : Tendsto (fun P : ℕ => D/Real.log (P : ℝ)^3) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hlog).const_mul D
  have hs := (h1.add h2).eventually (eventually_lt_nhds
    (show (0 : ℝ)+0 < δ*c by simpa only [zero_add] using mul_pos hδ hc))
  filter_upwards [hb,hm,hs,eventually_ge_atTop 2] with P hbP hmP hsP hP x hxlo hxhi
  have hPR : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hl : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hp : 0 < (P : ℝ)^(1-ε) := Real.rpow_pos_of_pos hP0 _
  calc
    _ ≤ A+D*(P : ℝ)^(1-ε)/Real.log (P : ℝ)^4 := hbP x hxlo hxhi
    _ = (A*Real.log (P : ℝ)/(P : ℝ)^(1-ε)+D/Real.log (P : ℝ)^3)*
        ((P : ℝ)^(1-ε)/Real.log (P : ℝ)) := by
      field_simp [ne_of_gt hl, ne_of_gt hp]
    _ ≤ (δ*c)*((P : ℝ)^(1-ε)/Real.log (P : ℝ)) :=
      mul_le_mul_of_nonneg_right hsP.le (by positivity)
    _ = δ*(c*(P : ℝ)^(1-ε)/Real.log (P : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmP x hxlo) hδ.le

/-- The actual finite prime core approaches its explicit positive prime slab
uniformly in relative error. The error is the full signed source itself. -/
theorem pmFinitePrimePowerDampedFermiSource_prime_slab_relative {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ P : ℕ in atTop, ∀ x : ℝ,
      3*(P : ℝ)/2 ≤ x → x ≤ 7*(P : ℝ)/4 →
        ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε (1/x) -
          (pmPrimeSlabMass ε P x : ℂ)‖ ≤ δ*pmPrimeSlabMass ε P x := by
  filter_upwards [pmPowerDampedFermiSource_prime_slab_relative_small hε hεhalf hδ,
    eventually_ge_atTop 1] with P hP hP1 x hxlo hxhi
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP1
  have hx0 : 0 < x := by linarith
  have hb : 1/(1/x) < 2*(P : ℝ) := by rw [one_div_one_div]; linarith
  rw [pmFinitePrimePowerDampedFermiSource_first_band ε hP1 (by positivity) hb,
    one_div_one_div, add_sub_cancel_right]
  exact hP x hxlo hxhi

/-- A positive power-sized slab is forced inside the literal canonical prime
core, despite cancellation of that slab in the full source. -/
theorem pmFinitePrimePowerDampedFermiSource_prime_slab_eventually_lower {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ P : ℕ in atTop, ∀ x : ℝ,
      3*(P : ℝ)/2 ≤ x → x ≤ 7*(P : ℝ)/4 →
        c*(P : ℝ)^(1-ε)/Real.log (P : ℝ) ≤
          (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε (1/x)).re := by
  obtain ⟨c,hc,hm⟩ := pmPrimeSlabMass_eventually_lower hε
  refine ⟨c/2,by positivity,?_⟩
  filter_upwards [hm,pmFinitePrimePowerDampedFermiSource_prime_slab_relative hε hεhalf
    (by norm_num : (0 : ℝ) < 1/2)] with P hmP hsP x hxlo hxhi
  have hs := hsP x hxlo hxhi
  have hr := Complex.abs_re_le_norm
    (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε (1/x) -
      (pmPrimeSlabMass ε P x : ℂ))
  rw [Complex.sub_re,Complex.ofReal_re] at hr
  have habs := neg_abs_le
    ((pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε (1/x)).re -
      pmPrimeSlabMass ε P x)
  have hm' := hmP x hxlo
  calc
    _ = (c*(P : ℝ)^(1-ε)/Real.log (P : ℝ))/2 := by ring
    _ ≤ pmPrimeSlabMass ε P x/2 := div_le_div_of_nonneg_right hm' (by norm_num)
    _ ≤ _ := by linarith

end RHTower
