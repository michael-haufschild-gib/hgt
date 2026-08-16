import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinHoheiselPrimeSupply
import GaloisForLFunctions.RHTower.Sieve.MaynardUpperPhasePrimeSupplyHandoff

open Complex Filter Topology Set Finset
open MeasureTheory ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

def routeTHoheiselEveryBaseExponent : ℝ := 71 / 100

theorem routeTHoheiselEveryBaseExponent_lt_handoff :
    routeTHoheiselEveryBaseExponent < routeTPhysicalSliceHandoffTheta := by
  have hd := maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  simp only [routeTHoheiselEveryBaseExponent, routeTPhysicalSliceHandoffTheta]
  linarith

theorem inghamRouteTMellinPhysicalCenter_succ_sub_le
    {X : ℕ} (hX : 1 ≤ X) :
    inghamRouteTMellinPhysicalCenter (X + 1) -
        inghamRouteTMellinPhysicalCenter X ≤
      15 * (X : ℝ) ^ (inghamRouteTPhysicalScaleExponent - 1) := by
  let x : ℝ := X
  let q : ℝ := inghamRouteTPhysicalScaleExponent
  let t : ℝ := x⁻¹
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast hX
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp only [t]
    exact inv_le_one_of_one_le₀ hx1
  have hbase1 : 1 ≤ 1 + t := by linarith
  have hq4 : q ≤ 4 := by
    dsimp only [q, inghamRouteTPhysicalScaleExponent]
    norm_num
  have hpowle : (1 + t) ^ q ≤ (1 + t) ^ (4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase1 hq4
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hpowle
  have ht2 : t ^ 2 ≤ t := by
    have h := pow_le_one₀ ht0 ht1 (n := 1)
    calc
      t ^ 2 = t * t ^ 1 := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left h ht0
      _ = t := by ring
  have ht3 : t ^ 3 ≤ t := by
    have h := pow_le_one₀ ht0 ht1 (n := 2)
    calc
      t ^ 3 = t * t ^ 2 := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left h ht0
      _ = t := by ring
  have ht4 : t ^ 4 ≤ t := by
    have h := pow_le_one₀ ht0 ht1 (n := 3)
    calc
      t ^ 4 = t * t ^ 3 := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left h ht0
      _ = t := by ring
  have hpoly : (1 + t) ^ 4 - 1 ≤ 15 * t := by
    nlinarith
  have hbracket : (1 + t) ^ q - 1 ≤ 15 * t := by
    linarith
  have hfactor : x + 1 = x * (1 + t) := by
    dsimp only [t]
    field_simp
  have hpowFactor : (x + 1) ^ q = x ^ q * (1 + t) ^ q := by
    rw [hfactor, Real.mul_rpow hx0.le (by linarith : 0 ≤ 1 + t)]
  unfold inghamRouteTMellinPhysicalCenter
  push_cast
  change (x + 1) ^ q - x ^ q ≤ 15 * x ^ (q - 1)
  rw [hpowFactor]
  calc
    x ^ q * (1 + t) ^ q - x ^ q = x ^ q * ((1 + t) ^ q - 1) := by ring
    _ ≤ x ^ q * (15 * t) :=
      mul_le_mul_of_nonneg_left hbracket (Real.rpow_nonneg hx0.le _)
    _ = 15 * x ^ (q - 1) := by
      dsimp only [t]
      rw [Real.rpow_sub hx0, Real.rpow_one]
      field_simp

private theorem tendsto_routeT_densification_ratio_zero :
    Tendsto (fun x : ℝ =>
      15 * x ^ (-(9 / 299 : ℝ)) +
        2 * 2 ^ (701299 / 299000 : ℝ) *
          x ^ (-(8701 / 299000 : ℝ))) atTop (nhds 0) := by
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 299)).const_mul 15
  have h2 := (tendsto_rpow_neg_atTop
    (by norm_num : (0 : ℝ) < 8701 / 299000)).const_mul
      (2 * 2 ^ (701299 / 299000 : ℝ))
  simpa only [mul_zero, zero_add] using h1.add h2

theorem eventually_inghamRouteT_center_gap_add_two_bufferedWidth_le :
    ∀ᶠ X : ℕ in atTop,
      inghamRouteTMellinPhysicalCenter (X + 1) -
          inghamRouteTMellinPhysicalCenter X +
          2 * inghamRouteTMellinBufferedPhysicalWidth (X + 1) ≤
        inghamRouteTMellinPhysicalCenter X ^ routeTHoheiselEveryBaseExponent := by
  have hratioT := tendsto_routeT_densification_ratio_zero.comp
    tendsto_natCast_atTop_atTop
  have hratio := Filter.Tendsto.eventually_lt hratioT
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hratio, eventually_ge_atTop (1 : ℕ)] with X hsmall hX
  simp only [Function.comp_apply] at hsmall
  let x : ℝ := X
  let q : ℝ := inghamRouteTPhysicalScaleExponent
  let b : ℝ := 701299 / 299000
  let e : ℝ := 710 / 299
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast hX
  have hx0 : 0 < x := by linarith
  have hgap := inghamRouteTMellinPhysicalCenter_succ_sub_le hX
  have hY : 1 ≤ X + 1 := by omega
  have hb0 : 0 ≤ b := by dsimp only [b]; norm_num
  have hwidthExact :
      inghamRouteTMellinBufferedPhysicalWidth (X + 1) =
        ((X + 1 : ℕ) : ℝ) ^ b := by
    rw [inghamRouteTMellinBufferedPhysicalWidth_eq_center_rpow hY]
    unfold inghamRouteTMellinPhysicalCenter
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ ((X + 1 : ℕ) : ℝ))]
    congr 1
    dsimp only [b, inghamRouteTPhysicalScaleExponent]
    norm_num
  have hYle : (((X + 1 : ℕ) : ℝ)) ≤ 2 * x := by
    dsimp only [x]
    push_cast
    linarith
  have hwidth :
      inghamRouteTMellinBufferedPhysicalWidth (X + 1) ≤
        2 ^ b * x ^ b := by
    calc
      inghamRouteTMellinBufferedPhysicalWidth (X + 1) =
          (((X + 1 : ℕ) : ℝ)) ^ b := hwidthExact
      _ ≤ (2 * x) ^ b := Real.rpow_le_rpow (by positivity) hYle hb0
      _ = 2 ^ b * x ^ b := by rw [Real.mul_rpow (by norm_num) hx0.le]
  have hgapPow : x ^ (q - 1) = x ^ e * x ^ (-(9 / 299 : ℝ)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    dsimp only [q, e, inghamRouteTPhysicalScaleExponent]
    norm_num
  have hwidthPow : x ^ b = x ^ e * x ^ (-(8701 / 299000 : ℝ)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    dsimp only [b, e]
    norm_num
  have htarget :
      inghamRouteTMellinPhysicalCenter X ^ routeTHoheiselEveryBaseExponent =
        x ^ e := by
    unfold inghamRouteTMellinPhysicalCenter
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ X)]
    congr 1
    dsimp only [x, e, routeTHoheiselEveryBaseExponent,
      inghamRouteTPhysicalScaleExponent]
    norm_num
  calc
    inghamRouteTMellinPhysicalCenter (X + 1) -
          inghamRouteTMellinPhysicalCenter X +
          2 * inghamRouteTMellinBufferedPhysicalWidth (X + 1) ≤
        15 * x ^ (q - 1) + 2 * (2 ^ b * x ^ b) := by
      exact add_le_add hgap (mul_le_mul_of_nonneg_left hwidth (by norm_num))
    _ = x ^ e * (15 * x ^ (-(9 / 299 : ℝ)) +
        2 * 2 ^ b * x ^ (-(8701 / 299000 : ℝ))) := by
      rw [hgapPow, hwidthPow]
      ring
    _ ≤ x ^ e := mul_le_of_le_one_right (Real.rpow_nonneg hx0.le _) hsmall.le
    _ = inghamRouteTMellinPhysicalCenter X ^ routeTHoheiselEveryBaseExponent :=
      htarget.symm

theorem exists_eventually_routeT_prime_in_every_base_window :
    ∀ᶠ z : ℝ in atTop,
      ∃ p : ℕ, p.Prime ∧ z < (p : ℝ) ∧
        (p : ℝ) ≤ z + z ^ routeTHoheiselEveryBaseExponent := by
  rcases (eventually_atTop.1 exists_eventually_inghamRouteTBuffered_prime) with
    ⟨S, hS⟩
  rcases (eventually_atTop.1
    eventually_inghamRouteT_center_gap_add_two_bufferedWidth_le) with
    ⟨C, hC⟩
  let M : ℕ := max 1 (max S C)
  let q : ℝ := inghamRouteTPhysicalScaleExponent
  let r : ℝ := 299 / 1000
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMS : S ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMC : C ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hq0 : 0 < q := inghamRouteTPhysicalScaleExponent_pos
  have hr0 : 0 < r := by dsimp only [r]; norm_num
  have hMq1 : (1 : ℝ) ≤ (M : ℝ) ^ q :=
    Real.one_le_rpow (by exact_mod_cast hM1) hq0.le
  filter_upwards [eventually_ge_atTop ((M : ℝ) ^ q)] with z hz
  have hz1 : 1 ≤ z := hMq1.trans hz
  have hz0 : 0 < z := by linarith
  let u : ℝ := z ^ r
  let X : ℕ := ⌊u⌋₊
  have hMr : ((M : ℝ) ^ q) ^ r = (M : ℝ) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (M : ℝ))]
    have hqr : q * r = 1 := by
      dsimp only [q, r, inghamRouteTPhysicalScaleExponent]
      norm_num
    rw [hqr, Real.rpow_one]
  have hMu : (M : ℝ) ≤ u := by
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) q) hz hr0.le
    rw [hMr] at hpow
    exact hpow
  have hMX : M ≤ X := by
    dsimp only [X]
    exact Nat.le_floor hMu
  have hX1 : 1 ≤ X := hM1.trans hMX
  have hXS : S ≤ X + 1 := hMS.trans (hMX.trans (Nat.le_add_right X 1))
  have hXC : C ≤ X := hMC.trans hMX
  have hXu : (X : ℝ) ≤ u := by
    dsimp only [X]
    exact Nat.floor_le (Real.rpow_nonneg hz0.le r)
  have huXsucc : u < (X : ℝ) + 1 := by
    dsimp only [X]
    exact Nat.lt_floor_add_one u
  have huq : u ^ q = z := by
    dsimp only [u]
    rw [← Real.rpow_mul hz0.le]
    have hrq : r * q = 1 := by
      dsimp only [q, r, inghamRouteTPhysicalScaleExponent]
      norm_num
    rw [hrq, Real.rpow_one]
  have hcenterLower : inghamRouteTMellinPhysicalCenter X ≤ z := by
    unfold inghamRouteTMellinPhysicalCenter
    have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (X : ℝ)) hXu hq0.le
    rwa [huq] at hpow
  have hzCenterSucc : z < inghamRouteTMellinPhysicalCenter (X + 1) := by
    unfold inghamRouteTMellinPhysicalCenter
    have hpow := Real.rpow_lt_rpow (Real.rpow_nonneg hz0.le r) huXsucc hq0
    rw [huq] at hpow
    simpa only [Nat.cast_add, Nat.cast_one] using hpow
  obtain ⟨p, hp, hpLower, hpUpper⟩ := hS (X + 1) hXS
  have hcover := hC X hXC
  have halpha0 : 0 ≤ routeTHoheiselEveryBaseExponent := by
    unfold routeTHoheiselEveryBaseExponent
    norm_num
  have htargetMono :
      inghamRouteTMellinPhysicalCenter X ^ routeTHoheiselEveryBaseExponent ≤
        z ^ routeTHoheiselEveryBaseExponent :=
    Real.rpow_le_rpow
      (by unfold inghamRouteTMellinPhysicalCenter; positivity) hcenterLower halpha0
  refine ⟨p, hp, hzCenterSucc.trans hpLower, ?_⟩
  have hdistance : (p : ℝ) - z ≤ z ^ routeTHoheiselEveryBaseExponent := by
    calc
      (p : ℝ) - z ≤
          (inghamRouteTMellinPhysicalCenter (X + 1) - z) +
            2 * inghamRouteTMellinBufferedPhysicalWidth (X + 1) := by
        linarith
      _ ≤ (inghamRouteTMellinPhysicalCenter (X + 1) -
            inghamRouteTMellinPhysicalCenter X) +
            2 * inghamRouteTMellinBufferedPhysicalWidth (X + 1) := by
        linarith
      _ ≤ inghamRouteTMellinPhysicalCenter X ^
          routeTHoheiselEveryBaseExponent := hcover
      _ ≤ z ^ routeTHoheiselEveryBaseExponent := htargetMono
  linarith

theorem routeTHoheiselEveryBaseExponent_lt_widthExponent
    {mu : ℝ} (hmu : routeTPhysicalSliceHandoffMu ≤ mu) :
    routeTHoheiselEveryBaseExponent < 1 - 1 / mu := by
  exact routeTHoheiselEveryBaseExponent_lt_handoff.trans_le
    (routeTPhysicalSliceHandoffTheta_le_widthExponent hmu)

theorem exists_eventually_routeT_prime_in_every_upperPhase_window
    {mu : ℝ} (hmu : routeTPhysicalSliceHandoffMu ≤ mu) :
    ∀ᶠ z : ℝ in atTop,
      ∃ p : ℕ, p.Prime ∧ z < (p : ℝ) ∧
        (p : ℝ) ≤ z + z ^ (1 - 1 / mu) := by
  filter_upwards [exists_eventually_routeT_prime_in_every_base_window,
      eventually_ge_atTop (1 : ℝ)] with z hzprime hz1
  obtain ⟨p, hp, hpLower, hpUpper⟩ := hzprime
  refine ⟨p, hp, hpLower, hpUpper.trans ?_⟩
  gcongr
  exact (routeTHoheiselEveryBaseExponent_lt_widthExponent hmu).le

end

end RHTower.Sieve

namespace RHTower.Sieve

noncomputable section

/-- One actual prime in a real interval makes its Chebyshev-theta mass strictly positive. -/
theorem chebyshevTheta_window_pos_of_prime
    {a b : ℝ} (ha : 0 ≤ a) {p : ℕ} (hp : p.Prime)
    (hpLower : a < (p : ℝ)) (hpUpper : (p : ℝ) ≤ b) :
    0 < Chebyshev.theta b - Chebyshev.theta a := by
  have hb0 : 0 ≤ b := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    linarith
  have hfloorLower : ⌊a⌋₊ < p := by
    have hcast : ((⌊a⌋₊ : ℕ) : ℝ) < (p : ℝ) :=
      (Nat.floor_le ha).trans_lt hpLower
    exact_mod_cast hcast
  have hfloorUpper : p ≤ ⌊b⌋₊ := Nat.le_floor hpUpper
  have hfloors : ⌊a⌋₊ ≤ ⌊b⌋₊ := by omega
  let P : Finset ℕ := (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime
  have hpP : p ∈ P := by
    simp only [P, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hfloorLower, hfloorUpper⟩, hp⟩
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hsum : Real.log (p : ℝ) ≤ ∑ q ∈ P, Real.log q := by
    apply Finset.single_le_sum (s := P) (f := fun q : ℕ => Real.log (q : ℝ))
    · intro q hq
      have hqprime : q.Prime := (Finset.mem_filter.mp hq).2
      exact Real.log_nonneg (by exact_mod_cast hqprime.one_le)
    · exact hpP
  have htheta := RHTower.theta_window_eq hfloors
  have hthetaFloor (x : ℝ) (hx : 0 ≤ x) :
      Chebyshev.theta x = Chebyshev.theta (⌊x⌋₊ : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast]
  have htheta' : Chebyshev.theta b - Chebyshev.theta a =
      ∑ q ∈ P, Real.log q := by
    rw [hthetaFloor _ hb0, hthetaFloor _ ha]
    simpa only [P] using htheta
  rw [htheta']
  exact hlogp.trans_le hsum

/-- Above Route T's physical-slice handoff, every sufficiently large exact physical window has
strictly positive prime mass. -/
theorem eventually_routeT_upperPhase_theta_window_pos
    {mu : ℝ} (hmu : routeTPhysicalSliceHandoffMu ≤ mu) :
    ∀ᶠ z : ℝ in atTop,
      0 < Chebyshev.theta (z + z ^ (1 - 1 / mu)) - Chebyshev.theta z := by
  filter_upwards [exists_eventually_routeT_prime_in_every_upperPhase_window hmu,
      eventually_ge_atTop (1 : ℝ)] with z hzprime hz1
  obtain ⟨p, hp, hpLower, hpUpper⟩ := hzprime
  exact chebyshevTheta_window_pos_of_prime (by linarith) hp hpLower hpUpper

/-- Source-faithful upper-phase handoff: any Route T target at least as wide as the physical
window eventually contradicts the exact prime-free premise used by the Maynard producer. -/
theorem eventually_routeT_upperPhase_theta_wide_window_pos
    {mu : ℝ} (hmu : routeTPhysicalSliceHandoffMu ≤ mu) :
    ∀ᶠ z : ℝ in atTop, ∀ H : ℝ,
      z ^ (1 - 1 / mu) ≤ 2 * H →
        0 < Chebyshev.theta (z + 2 * H) - Chebyshev.theta z := by
  filter_upwards [exists_eventually_routeT_prime_in_every_upperPhase_window hmu,
      eventually_ge_atTop (1 : ℝ)] with z hzprime hz1
  intro H hwidth
  obtain ⟨p, hp, hpLower, hpUpper⟩ := hzprime
  apply chebyshevTheta_window_pos_of_prime (by linarith) hp hpLower
  exact hpUpper.trans (by linarith)

end


end RHTower.Sieve
