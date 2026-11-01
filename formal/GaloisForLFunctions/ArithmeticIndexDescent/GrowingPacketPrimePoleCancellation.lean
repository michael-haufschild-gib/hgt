import GaloisForLFunctions.ArithmeticIndexDescent.QuantitativePrimeHinges
import GaloisForLFunctions.ArithmeticIndexDescent.PrimeWindowHingeIdentities
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellPoleBound

/-!
# Uniform prime–pole cancellation on growing packets

The explicit Chebyshev rate controls every endpoint of a growing logarithmic
packet. Exact hinge differences cancel the first pole before summation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
open RHTower
open GaloisForLFunctions.RHTower
namespace GaloisForLFunctions.ArithmeticIndexDescent

private theorem abs_haar_exp_pos_le_two {a : ℕ} (ha : 1 ≤ a) :
    |∫ u, haarProfile a u * Real.exp (u / 2)| ≤ 2 := by
  have hM : haarMass a ≤ 1 := by
    refine (haarMass_bounds ha).2.trans ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (a : ℝ) + 1)]
    have ha0 := Nat.cast_nonneg (α := ℝ) a
    linarith only [ha0]
  have hs : 1 ≤ Real.sqrt ((2 * a : ℕ) : ℝ) := by
    rw [Real.le_sqrt zero_le_one (by positivity)]
    norm_num only [one_pow]
    exact_mod_cast (show 1 ≤ 2 * a by omega)
  refine (abs_haarProfile_exp_pos_le ha).trans ?_
  rw [div_le_iff₀ (zero_lt_one.trans_le hs)]
  linarith only [hM, hs]

private theorem abs_coarse_exp_neg_le_two {b : ℕ} (hb : 1 ≤ b) :
    |∫ u, coarseProfile b u * Real.exp (-u / 2)| ≤ 2 := by
  simp_rw [coarseProfile, add_mul]
  rw [integral_add (integrable_rawCell_mul_exp _) (integrable_rawCell_mul_exp _)]
  change |cellExpMass (2 * b) + cellExpMass (2 * b + 1)| ≤ 2
  rw [cellExpMass_eq (by omega), cellExpMass_eq (by omega),
    show 2 * b + 1 + 1 = 2 * b + 2 by omega]
  have hlo : 0 ≤ Real.log (((2 * b : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * b by omega))
  have horder : Real.log (((2 * b : ℕ) : ℝ)) ≤ Real.log (((2 * b + 2 : ℕ) : ℝ)) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * b ≤ 2 * b + 2 by omega))
  have he1 : Real.exp (-Real.log (((2 * b : ℕ) : ℝ)) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith only [hlo])
  have he2 : Real.exp (-Real.log (((2 * b + 2 : ℕ) : ℝ)) / 2) ≤
      Real.exp (-Real.log (((2 * b : ℕ) : ℝ)) / 2) :=
    Real.exp_le_exp.mpr (by linarith only [horder])
  rw [abs_of_nonneg (by linarith only [he2])]
  have he0 := (Real.exp_pos (-Real.log (((2 * b + 2 : ℕ) : ℝ)) / 2)).le
  linarith only [he1, he0]

private theorem abs_second_mixed_pole_le {Y a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |(2 * (∫ u, haarProfile a u * Real.exp (u / 2)) *
        (∫ u, coarseProfile b u * Real.exp (-u / 2))) / (Y : ℝ)| ≤ 8 / (Y : ℝ) := by
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg Y
  rw [abs_div, abs_of_nonneg hY0]
  apply div_le_div_of_nonneg_right _ hY0
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ (2 * 2) * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (abs_haar_exp_pos_le_two ha) (by norm_num))
        (abs_coarse_exp_neg_le_two hb) (abs_nonneg _) (by norm_num)
    _ = 8 := by norm_num

private theorem prime_corner_log_bounds {M i j : ℕ}
    (hi : 2 ≤ i) (hj : 2 ≤ j) (hiM : i ≤ 2 * (M + 1)) (hjM : j ≤ 2 * (M + 1)) :
    -Real.log ((M : ℝ) + 1) ≤ Real.log (j : ℝ) - Real.log (i : ℝ) ∧
      Real.log (j : ℝ) - Real.log (i : ℝ) ≤ Real.log ((M : ℝ) + 1) := by
  have hlogs (n : ℕ) (hn : 2 ≤ n) (hnM : n ≤ 2 * (M + 1)) :
      Real.log 2 ≤ Real.log (n : ℝ) ∧
        Real.log (n : ℝ) ≤ Real.log 2 + Real.log ((M : ℝ) + 1) := by
    constructor
    · exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    · rw [← Real.log_mul (by norm_num) (by positivity)]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hnM)
  obtain ⟨hil, hiu⟩ := hlogs i hi hiM
  obtain ⟨hjl, hju⟩ := hlogs j hj hjM
  constructor <;> linarith only [hil, hiu, hjl, hju]

private theorem prime_hinge_error_on_symmetric_window {L H t C : ℝ}
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hHL : H ≤ L / 2)
    (htl : L - H ≤ t) (htu : t ≤ L + H) (hC : 0 ≤ C)
    (hrate : |screwPrimeSum t - 4 * Real.exp (t / 2)| ≤
      C * Real.exp (t / 2 - (1 / 1920000 : ℝ) * Real.sqrt t)) :
    |screwPrimeSum t - 4 * Real.exp (t / 2)| ≤
      C * Real.exp (L / 2) * Real.exp H *
        Real.exp (-(1 / 3840000 : ℝ) * Real.sqrt L) := by
  have ht : 0 ≤ t := by linarith only [hL, hHL, htl]
  have hs : Real.sqrt L / 2 ≤ Real.sqrt t := by
    rw [Real.le_sqrt (by positivity) ht]
    have hsq := Real.sq_sqrt hL
    nlinarith only [hsq, hL, hHL, htl]
  have hexp : t / 2 - (1 / 1920000 : ℝ) * Real.sqrt t ≤
      L / 2 + H + (-(1 / 3840000 : ℝ) * Real.sqrt L) := by
    linarith only [htu, hH, hs]
  calc
    _ ≤ C * Real.exp (t / 2 - (1 / 1920000 : ℝ) * Real.sqrt t) := hrate
    _ ≤ C * Real.exp (L / 2 + H + (-(1 / 3840000 : ℝ) * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

/-- The literal remainder has a uniform classical rate whenever the packet log-width is at most half the horizon. -/
theorem exists_fullPrimeWindowRemainder_uniform_pair_rate :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℕ in atTop,
      ∀ M a b : ℕ, 1 ≤ a → 1 ≤ b → a ≤ M → b ≤ M →
        Real.log ((M : ℝ) + 1) ≤ Real.log (Y : ℝ) / 2 →
        |fullPrimeWindowRemainder Y a b| ≤
          C * ((M : ℝ) + 1) *
            Real.exp (-(1 / 3840000 : ℝ) * Real.sqrt (Real.log Y)) + 8 / (Y : ℝ) := by
  obtain ⟨C, hC, hrate⟩ := exists_screwPrimeSum_explicit_classical_rate
  obtain ⟨t₀, ht₀⟩ := hrate.exists_forall_of_atTop
  refine ⟨8 * C, by positivity, ?_⟩
  have hlog : Tendsto (fun Y : ℕ => Real.log (Y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_ge_atTop (2 * t₀)] with Y hY hYt
  intro M a b ha hb haM hbM hwidth
  let E := C * Real.sqrt Y * ((M : ℝ) + 1) *
    Real.exp (-(1 / 3840000 : ℝ) * Real.sqrt (Real.log Y))
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hsY : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.mpr hYpos
  have hL : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  have hH : 0 ≤ Real.log ((M : ℝ) + 1) := by
    apply Real.log_nonneg
    have hM0 := Nat.cast_nonneg (α := ℝ) M
    linarith only [hM0]
  have hcorner (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
      (hiM : i ≤ 2 * (M + 1)) (hjM : j ≤ 2 * (M + 1)) :
      |screwPrimeSum (Real.log Y + (Real.log j - Real.log i)) -
        4 * Real.exp ((Real.log Y + (Real.log j - Real.log i)) / 2)| ≤ E := by
    obtain ⟨hlo, hhi⟩ := prime_corner_log_bounds hi hj hiM hjM
    have htl : Real.log (Y : ℝ) - Real.log ((M : ℝ) + 1) ≤
        Real.log Y + (Real.log j - Real.log i) := by linarith only [hlo]
    have htu : Real.log Y + (Real.log j - Real.log i) ≤
        Real.log (Y : ℝ) + Real.log ((M : ℝ) + 1) := by linarith only [hhi]
    have ht : t₀ ≤ Real.log Y + (Real.log j - Real.log i) := by
      linarith only [hYt, hwidth, htl]
    have he := prime_hinge_error_on_symmetric_window hL hH hwidth htl htu hC.le (ht₀ _ ht)
    rw [exp_half_log_eq_sqrt hY, Real.exp_log (by positivity : (0 : ℝ) < (M : ℝ) + 1)] at he
    exact he
  let F : ℝ → ℝ := fun z => screwPrimeSum (Real.log Y + z) -
    4 * Real.exp ((Real.log Y + z) / 2)
  have hd (k : ℕ) (hk : 2 ≤ k) (hkM : k + 1 ≤ 2 * (M + 1)) :
      |intervalMixedDifference F (Real.log k) (Real.log ((k + 1 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ))| ≤ 4 * E := by
    exact abs_intervalMixedDifference_le
      (hcorner (k + 1) (2 * b) (by omega) (by omega) hkM (by omega))
      (hcorner k (2 * b) hk (by omega) (by omega) (by omega))
      (hcorner (k + 1) (2 * b + 2) (by omega) (by omega) hkM (by omega))
      (hcorner k (2 * b + 2) hk (by omega) (by omega) (by omega))
  have hdl := hd (2 * a) (by omega) (by omega)
  have hdr := hd (2 * a + 1) (by omega) (by omega)
  have hn := haarCoeff_nonneg ha
  have herr : |fullPrimeWindowCoupling (haarProfile a) Y b -
      4 * Real.sqrt Y * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) *
        (∫ u, haarProfile a u * Real.exp (-u / 2))| ≤ 8 * E := by
    rw [fullPrimeWindowCoupling_haar_sub_main_eq hY ha hb]
    change |2 * (haarLeftCoeff a * intervalMixedDifference F
      (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 1 : ℕ) : ℝ))
      (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)) -
      haarRightCoeff a * intervalMixedDifference F
      (Real.log ((2 * a + 1 : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
      (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)))| ≤ _
    rw [show 2 * a + 2 = (2 * a + 1) + 1 by omega]
    have hsub := abs_sub
      (haarLeftCoeff a * intervalMixedDifference F
        (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 1 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)))
      (haarRightCoeff a * intervalMixedDifference F
        (Real.log ((2 * a + 1 : ℕ) : ℝ)) (Real.log (((2 * a + 1) + 1 : ℕ) : ℝ))
        (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ)))
    rw [abs_mul, abs_mul, abs_of_nonneg hn.1, abs_of_nonneg hn.2] at hsub
    have hl := mul_le_mul_of_nonneg_left hdl hn.1
    have hr := mul_le_mul_of_nonneg_left hdr hn.2
    have he : haarLeftCoeff a * (4 * E) + haarRightCoeff a * (4 * E) = 4 * E := by
      rw [← add_mul, haarCoeff_sum ha, one_mul]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ 2 * (4 * E) := mul_le_mul_of_nonneg_left
        (hsub.trans ((add_le_add hl hr).trans_eq he)) (by norm_num)
      _ = 8 * E := by ring
  have hnormalized :
      |(fullPrimeWindowCoupling (haarProfile a) Y b -
        4 * Real.sqrt Y * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) *
          (∫ u, haarProfile a u * Real.exp (-u / 2))) / Real.sqrt Y| ≤
        (8 * C) * ((M : ℝ) + 1) *
          Real.exp (-(1 / 3840000 : ℝ) * Real.sqrt (Real.log Y)) := by
    rw [abs_div, abs_of_nonneg hsY.le, div_le_iff₀ hsY]
    calc
      _ ≤ 8 * E := herr
      _ = _ := by dsimp only [E]; ring
  have heq : fullPrimeWindowRemainder Y a b =
      (fullPrimeWindowCoupling (haarProfile a) Y b -
        4 * Real.sqrt Y * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) *
          (∫ u, haarProfile a u * Real.exp (-u / 2))) / Real.sqrt Y -
      (2 * (∫ u, haarProfile a u * Real.exp (u / 2)) *
        (∫ u, coarseProfile b u * Real.exp (-u / 2))) / (Y : ℝ) := by
    rw [fullPrimeWindowRemainder,
      ← fullPrimeWindowCoupling_eq_tsum_euler (X := a + (b + 1) * Y)
        hY ha hb (by omega) (by nlinarith only [Nat.zero_le a]),
      sub_div, fullPrimeWindowMixedPole_div_sqrt hY hb]
    field_simp [hYpos.ne', hsY.ne']
    ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add hnormalized (abs_second_mixed_pole_le ha hb))

private theorem growing_packet_log_width {L : ℝ} {M : ℕ}
    (hL : 16 ≤ L) (hlogtwo : 4 * Real.log 2 ≤ L)
    (hM : (M : ℝ) ≤ Real.exp ((1 / 23040000 : ℝ) * Real.sqrt L)) :
    Real.log ((M : ℝ) + 1) ≤ L / 2 ∧
      ((M : ℝ) + 1) ^ 3 * Real.exp (-(1 / 3840000 : ℝ) * Real.sqrt L) ≤
        8 * Real.exp (-(1 / 7680000 : ℝ) * Real.sqrt L) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hs : 4 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) hL0]
    norm_num
    exact hL
  have hs0 := Real.sqrt_nonneg L
  have hs2 := Real.sq_sqrt hL0
  have hsL : Real.sqrt L ≤ L / 4 := by
    have hm := mul_le_mul_of_nonneg_right hs hs0
    nlinarith only [hm, hs2]
  have he : 1 ≤ Real.exp ((1 / 23040000 : ℝ) * Real.sqrt L) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hplus : (M : ℝ) + 1 ≤ 2 * Real.exp ((1 / 23040000 : ℝ) * Real.sqrt L) := by
    linarith only [hM, he]
  constructor
  · have hlogs := Real.log_le_log (by positivity : (0 : ℝ) < (M : ℝ) + 1) hplus
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hlogs
    linarith only [hlogs, hlogtwo, hsL, hs0]
  · have hcub : ((M : ℝ) + 1) ^ 3 ≤
        (2 * Real.exp ((1 / 23040000 : ℝ) * Real.sqrt L)) ^ 3 := by
      gcongr
    calc
      _ ≤ (2 * Real.exp ((1 / 23040000 : ℝ) * Real.sqrt L)) ^ 3 *
          Real.exp (-(1 / 3840000 : ℝ) * Real.sqrt L) :=
        mul_le_mul_of_nonneg_right hcub (Real.exp_pos _).le
      _ = 8 * ((Real.exp ((1 / 23040000 : ℝ) * Real.sqrt L) *
          Real.exp ((1 / 23040000 : ℝ) * Real.sqrt L) *
          Real.exp ((1 / 23040000 : ℝ) * Real.sqrt L)) *
          Real.exp (-(1 / 3840000 : ℝ) * Real.sqrt L)) := by ring
      _ = 8 * Real.exp (-(1 / 7680000 : ℝ) * Real.sqrt L) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

private theorem reciprocal_le_prime_window_rate {Y : ℕ} (hY : 1 ≤ Y)
    (hL : 16 ≤ Real.log (Y : ℝ)) :
    1 / (Y : ℝ) ≤ Real.exp (-(1 / 3840000 : ℝ) * Real.sqrt (Real.log Y)) := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hL0 : 0 ≤ Real.log (Y : ℝ) := by linarith only [hL]
  have hs : 4 ≤ Real.sqrt (Real.log (Y : ℝ)) := by
    rw [Real.le_sqrt (by norm_num) hL0]
    norm_num
    exact hL
  have hs0 := Real.sqrt_nonneg (Real.log (Y : ℝ))
  have hs2 := Real.sq_sqrt hL0
  have hm := mul_le_mul_of_nonneg_right hs hs0
  have hexp : -Real.log (Y : ℝ) ≤
      -(1 / 3840000 : ℝ) * Real.sqrt (Real.log Y) := by
    nlinarith only [hm, hs2, hs0]
  calc
    1 / (Y : ℝ) = Real.exp (-Real.log (Y : ℝ)) := by rw [Real.exp_neg, Real.exp_log hY0, one_div]
    _ ≤ _ := Real.exp_le_exp.mpr hexp

/-- Bounded coefficients on arbitrary packets grow to an explicit square-root logarithmic exponential scale. -/
theorem exists_fullPrimeWindowRemainder_growing_packet_rate :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℕ in atTop,
      ∀ M : ℕ, (M : ℝ) ≤ Real.exp ((1 / 23040000 : ℝ) * Real.sqrt (Real.log Y)) →
      ∀ S : Finset (ℕ × ℕ),
        (∀ p ∈ S, 1 ≤ p.1 ∧ p.1 ≤ M ∧ 1 ≤ p.2 ∧ p.2 ≤ M) →
      ∀ (B : ℝ) (c : ℕ × ℕ → ℝ), (∀ p ∈ S, |c p| ≤ B) →
        |∑ p ∈ S, c p * fullPrimeWindowRemainder Y p.1 p.2| ≤
          C * |B| * Real.exp (-(1 / 7680000 : ℝ) * Real.sqrt (Real.log Y)) := by
  obtain ⟨C, hC, hpairs⟩ := exists_fullPrimeWindowRemainder_uniform_pair_rate
  refine ⟨8 * (C + 8), by positivity, ?_⟩
  have hlog : Tendsto (fun Y : ℕ => Real.log (Y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpairs, eventually_ge_atTop 1, hlog.eventually_ge_atTop 16,
    hlog.eventually_ge_atTop (4 * Real.log 2)] with Y hpair hY hL hlogtwo
  intro M hM S hS B c hc
  obtain ⟨hwidth, hcube⟩ := growing_packet_log_width hL hlogtwo hM
  have hrecip := reciprocal_le_prime_window_rate hY hL
  let e := Real.exp (-(1 / 3840000 : ℝ) * Real.sqrt (Real.log Y))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hpoint (p : ℕ × ℕ) (hp : p ∈ S) :
      |fullPrimeWindowRemainder Y p.1 p.2| ≤ (C + 8) * ((M : ℝ) + 1) * e := by
    obtain ⟨ha, haM, hb, hbM⟩ := hS p hp
    have h := hpair M p.1 p.2 ha hb haM hbM hwidth
    have htail : 8 / (Y : ℝ) ≤ 8 * ((M : ℝ) + 1) * e := by
      calc
        8 / (Y : ℝ) = 8 * (1 / (Y : ℝ)) := by ring
        _ ≤ 8 * e := mul_le_mul_of_nonneg_left hrecip (by norm_num)
        _ ≤ 8 * ((M : ℝ) + 1) * e := by
          have hM0 := Nat.cast_nonneg (α := ℝ) M
          exact mul_le_mul_of_nonneg_right (by linarith only [hM0]) he
    change |fullPrimeWindowRemainder Y p.1 p.2| ≤ (C + 8) * ((M : ℝ) + 1) * e
    change |fullPrimeWindowRemainder Y p.1 p.2| ≤ C * ((M : ℝ) + 1) * e + 8 / (Y : ℝ) at h
    calc
      _ ≤ C * ((M : ℝ) + 1) * e + 8 / (Y : ℝ) := h
      _ ≤ C * ((M : ℝ) + 1) * e + 8 * ((M : ℝ) + 1) * e :=
        _root_.add_le_add (le_refl (C * ((M : ℝ) + 1) * e)) htail
      _ = (C + 8) * ((M : ℝ) + 1) * e := by ring
  have hsub : S ⊆ ((Icc 1 M) ×ˢ (Icc 1 M)) := by
    intro p hp
    obtain ⟨ha, haM, hb, hbM⟩ := hS p hp
    exact _root_.Finset.mem_product.mpr
      ⟨mem_Icc.mpr ⟨ha, haM⟩, mem_Icc.mpr ⟨hb, hbM⟩⟩
  have hcardNat : S.card ≤ M * M := by
    simpa only [_root_.Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel] using
      _root_.Finset.card_le_card hsub
  have hcard : (S.card : ℝ) ≤ ((M : ℝ) + 1) ^ 2 := by
    have hc' : (S.card : ℝ) ≤ (M : ℝ) * M := by exact_mod_cast hcardNat
    have hM0 := Nat.cast_nonneg (α := ℝ) M
    nlinarith only [hc', hM0]
  calc
    |∑ p ∈ S, c p * fullPrimeWindowRemainder Y p.1 p.2| ≤
        ∑ p ∈ S, |c p * fullPrimeWindowRemainder Y p.1 p.2| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, |B| * ((C + 8) * ((M : ℝ) + 1) * e) := by
      apply sum_le_sum
      intro p hp
      rw [abs_mul]
      exact mul_le_mul ((hc p hp).trans (le_abs_self B)) (hpoint p hp)
        (abs_nonneg _) (abs_nonneg B)
    _ = (S.card : ℝ) * |B| * (C + 8) * ((M : ℝ) + 1) * e := by
      rw [sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((M : ℝ) + 1) ^ 2 * |B| * (C + 8) * ((M : ℝ) + 1) * e := by
      gcongr
    _ = (|B| * (C + 8)) * (((M : ℝ) + 1) ^ 3 * e) := by ring
    _ ≤ (|B| * (C + 8)) *
        (8 * Real.exp (-(1 / 7680000 : ℝ) * Real.sqrt (Real.log Y))) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = (8 * (C + 8)) * |B| *
        Real.exp (-(1 / 7680000 : ℝ) * Real.sqrt (Real.log Y)) := by ring

/-- Full prime–pole cancellation is uniform over all bounded-coefficient packets in the explicit growing square. -/
theorem fullPrimeWindowRemainder_uniform_growing_packets (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ M : ℕ, (M : ℝ) ≤ Real.exp ((1 / 23040000 : ℝ) * Real.sqrt (Real.log Y)) →
      ∀ S : Finset (ℕ × ℕ),
        (∀ p ∈ S, 1 ≤ p.1 ∧ p.1 ≤ M ∧ 1 ≤ p.2 ∧ p.2 ≤ M) →
      ∀ c : ℕ × ℕ → ℝ, (∀ p ∈ S, |c p| ≤ B) →
        |∑ p ∈ S, c p * fullPrimeWindowRemainder Y p.1 p.2| < ε := by
  obtain ⟨C, _hC, hbound⟩ := exists_fullPrimeWindowRemainder_growing_packet_rate
  have hsqrt : Tendsto (fun Y : ℕ => Real.sqrt (Real.log (Y : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hscaled := hsqrt.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 7680000)
  have hexp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hscaled)
  have hdecay : Tendsto (fun Y : ℕ => C * |B| *
      Real.exp (-(1 / 7680000 : ℝ) * Real.sqrt (Real.log Y))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, neg_mul, mul_zero] using hexp.const_mul (C * |B|)
  filter_upwards [hbound, hdecay.eventually (gt_mem_nhds hε)] with Y hY hsmall
  intro M hM S hS c hc
  exact (hY M hM S hS B c hc).trans_lt hsmall

/-- The same uniform cancellation holds for the literal all-prime source at every common capturing horizon. -/
theorem allPrimesMixedSource_uniform_growing_packets (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ M : ℕ, (M : ℝ) ≤ Real.exp ((1 / 23040000 : ℝ) * Real.sqrt (Real.log Y)) →
      ∀ X : ℕ, M ≤ X → Y * (M + 1) ≤ X + 1 →
      ∀ S : Finset (ℕ × ℕ),
        (∀ p ∈ S, 1 ≤ p.1 ∧ p.1 ≤ M ∧ 1 ≤ p.2 ∧ p.2 ≤ M) →
      ∀ c : ℕ × ℕ → ℝ, (∀ p ∈ S, |c p| ≤ B) →
        |∑ p ∈ S, c p *
          (((∑' q : Nat.Primes, primeEulerMixedSource q
              (detailUnit p.1) (coarseWindow Y p.2) X) -
            fullPrimeWindowMixedPole Y p.1 p.2) / Real.sqrt Y)| < ε := by
  filter_upwards [fullPrimeWindowRemainder_uniform_growing_packets B hε,
    eventually_ge_atTop 1] with Y hbound hY
  intro M hM X hMX hXY S hS c hc
  have hsum : (∑ p ∈ S, c p *
      (((∑' q : Nat.Primes, primeEulerMixedSource q
          (detailUnit p.1) (coarseWindow Y p.2) X) -
        fullPrimeWindowMixedPole Y p.1 p.2) / Real.sqrt Y)) =
      ∑ p ∈ S, c p * fullPrimeWindowRemainder Y p.1 p.2 := by
    apply sum_congr rfl
    intro p hp
    obtain ⟨ha, haM, hb, hbM⟩ := hS p hp
    have hpX : Y * (p.2 + 1) ≤ X + 1 :=
      (Nat.mul_le_mul_left Y (Nat.add_le_add_right hbM 1)).trans hXY
    rw [fullPrimeWindowRemainder,
      ← fullPrimeWindowCoupling_eq_tsum_euler (X := X) hY ha hb (haM.trans hMX) hpX,
      ← fullPrimeWindowCoupling_eq_tsum_euler (X := p.1 + (p.2 + 1) * Y)
        hY ha hb (by omega) (by nlinarith only [Nat.zero_le p.1])]
  rw [hsum]
  exact hbound M hM S hS c hc

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_fullPrimeWindowRemainder_uniform_pair_rate

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_fullPrimeWindowRemainder_growing_packet_rate
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.fullPrimeWindowRemainder_uniform_growing_packets
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.allPrimesMixedSource_uniform_growing_packets
