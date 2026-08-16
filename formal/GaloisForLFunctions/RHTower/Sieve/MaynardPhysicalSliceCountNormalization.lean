import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceOuterCellReceiver
import GaloisForLFunctions.HTGeometry.WindowRpowIntegral

set_option maxHeartbeats 800000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

theorem card_largeValues_routeT_physicalSlice_le
    {N R delta Tord V : ℝ}
    (hN : 2 ≤ N) (hR : 1 ≤ R) (hRN : R ≤ N)
    (hdelta : 1 ≤ delta) (hTord : 0 ≤ Tord) (hTordN : Tord ≤ N)
    {S : Finset ℕ} {lam : ℕ → ℝ}
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ Tord)
    (hbig : ∀ r ∈ S,
      V ≤ ‖dirPoly ⌊N + 2 * R⌋₊
        (routeTVonMangoldtSliceCoeff ⌊N⌋₊ ⌊N + 2 * R⌋₊) (lam r)‖)
    (hV : 0 < V) :
    (S.card : ℝ) * V ^ 2 ≤
      312 * (R / N) * (1 + Real.log (3 * N)) ^ 4 := by
  let A : ℕ := ⌊N⌋₊
  let B : ℕ := ⌊N + 2 * R⌋₊
  let L : ℝ := Real.log (3 * N)
  have hN0 : 0 < N := by linarith
  have hR0 : 0 < R := by linarith
  have hNnonneg : 0 ≤ N := hN0.le
  have hNRnonneg : 0 ≤ N + 2 * R := by positivity
  have hAcastUpper : (A : ℝ) ≤ N := by
    dsimp only [A]
    exact Nat.floor_le hNnonneg
  have hAcastLower : N / 2 ≤ (A : ℝ) := by
    have hfloor : N < (A : ℝ) + 1 := by
      dsimp only [A]
      exact Nat.lt_floor_add_one N
    linarith
  have hAposR : 0 < (A : ℝ) := by linarith
  have hA : 1 ≤ A := by exact_mod_cast hAposR
  have hBcastUpper : (B : ℝ) ≤ N + 2 * R := by
    dsimp only [B]
    exact Nat.floor_le hNRnonneg
  have hBcastThree : (B : ℝ) ≤ 3 * N := by linarith
  have hBfloorLower : N + 2 * R < (B : ℝ) + 1 := by
    dsimp only [B]
    exact Nat.lt_floor_add_one (N + 2 * R)
  have hBposR : 0 < (B : ℝ) := by linarith
  have hB : 2 ≤ B := by
    exact_mod_cast (show (2 : ℝ) ≤ (B : ℝ) by linarith)
  have hAB : A ≤ B := by
    dsimp only [A, B]
    exact Nat.floor_mono (by linarith)
  have hslice : (((B - A : ℕ) : ℝ)) ≤ 3 * R := by
    rw [Nat.cast_sub hAB]
    have hAfloor : N < (A : ℝ) + 1 := by
      dsimp only [A]
      exact Nat.lt_floor_add_one N
    linarith
  have hthreeN : 1 ≤ 3 * N := by linarith
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact Real.log_nonneg hthreeN
  have hlogB0 : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hlogB : Real.log (B : ℝ) ≤ L := by
    dsimp only [L]
    exact Real.log_le_log hBposR hBcastThree
  have hfirst :
      Tord + 4 * (B : ℝ) * (1 + Real.log B) ≤
        13 * N * (1 + L) := by
    have hlogOne : 1 + Real.log (B : ℝ) ≤ 1 + L := by linarith
    have hmul :
        4 * (B : ℝ) * (1 + Real.log B) ≤
          12 * N * (1 + L) := by
      have hB4 : 4 * (B : ℝ) ≤ 12 * N := by linarith
      exact mul_le_mul hB4 hlogOne (by positivity) (by positivity)
    nlinarith
  have hdelta0 : 0 < delta := by linarith
  have hdeltaInv : 1 / delta ≤ 1 := by
    exact (div_le_one hdelta0).2 hdelta
  have hsecond :
      1 / delta + 2 * Real.log B ≤ 2 * (1 + L) := by
    linarith
  have hratio : Real.log B / (A : ℝ) ≤ 2 * L / N := by
    rw [div_le_iff₀ hAposR]
    have hbase : L ≤ (2 * L / N) * (A : ℝ) := by
      have hcoef : 1 ≤ 2 * (A : ℝ) / N := by
        rw [le_div_iff₀ hN0]
        linarith
      calc
        L = 1 * L := by ring
        _ ≤ (2 * (A : ℝ) / N) * L :=
          mul_le_mul_of_nonneg_right hcoef hL0
        _ = (2 * L / N) * (A : ℝ) := by ring
    exact hlogB.trans hbase
  have hratio0 : 0 ≤ Real.log B / (A : ℝ) :=
    div_nonneg hlogB0 hAposR.le
  have hratioTarget0 : 0 ≤ 2 * L / N := by positivity
  have hratioSq :
      (Real.log B / (A : ℝ)) ^ 2 ≤ (2 * L / N) ^ 2 :=
    pow_le_pow_left₀ hratio0 hratio 2
  have hthird :
      (((B - A : ℕ) : ℝ)) * (Real.log B / A) ^ 2 ≤
        12 * R * L ^ 2 / N ^ 2 := by
    calc
      (((B - A : ℕ) : ℝ)) * (Real.log B / A) ^ 2 ≤
          (3 * R) * (2 * L / N) ^ 2 :=
        mul_le_mul hslice hratioSq (sq_nonneg _) (by positivity)
      _ = 12 * R * L ^ 2 / N ^ 2 := by field_simp; ring
  have hraw := card_largeValues_routeTVonMangoldtSlice_finset
    hA hB hAB hdelta0 hTord hV hgap hband hbig
  calc
    (S.card : ℝ) * V ^ 2 ≤
        (Tord + 4 * (B : ℝ) * (1 + Real.log B)) *
          (1 / delta + 2 * Real.log B) *
            (((B - A : ℕ) : ℝ) * (Real.log B / A) ^ 2) := by
      simpa only [A, B] using hraw
    _ ≤ (13 * N * (1 + L)) * (2 * (1 + L)) *
          (12 * R * L ^ 2 / N ^ 2) := by
      exact mul_le_mul
        (mul_le_mul hfirst hsecond (by positivity) (by positivity))
        hthird (by positivity) (by positivity)
    _ = 312 * (R / N) * ((1 + L) ^ 2 * L ^ 2) := by
      field_simp
      ring
    _ ≤ 312 * (R / N) * (1 + L) ^ 4 := by
      have hLsq : L ^ 2 ≤ (1 + L) ^ 2 := by nlinarith
      have hinner : (1 + L) ^ 2 * L ^ 2 ≤ (1 + L) ^ 4 := by
        calc
          (1 + L) ^ 2 * L ^ 2 ≤
              (1 + L) ^ 2 * (1 + L) ^ 2 :=
            mul_le_mul_of_nonneg_left hLsq (sq_nonneg (1 + L))
          _ = (1 + L) ^ 4 := by ring
      exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 312 * (R / N) * (1 + Real.log (3 * N)) ^ 4 := by rfl

/-- The normalized physical-slice mean square reaches Route T's second alternative once the
literal logarithmic packet is paid from the available height reserve. -/
theorem card_largeValues_routeT_physicalSlice_secondAlternative
    {T N mu alpha eta R delta Tord V : ℝ}
    (hT : 2 ≤ T) (hNscale : N = T ^ mu) (hN : 2 ≤ N)
    (hR : 1 ≤ R) (hwidth : R ≤ 2 * N / T)
    (hdelta : 1 ≤ delta) (hTord : 0 ≤ Tord) (hTordN : Tord ≤ N)
    (hamp : N ^ (alpha - 1) ≤ V)
    (hpolylog : 624 * (1 + Real.log (3 * N)) ^ 4 ≤ T ^ eta)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2)
    {S : Finset ℕ} {lam : ℕ → ℝ}
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ Tord)
    (hbig : ∀ r ∈ S,
      V ≤ ‖dirPoly ⌊N + 2 * R⌋₊
        (routeTVonMangoldtSliceCoeff ⌊N⌋₊ ⌊N + 2 * R⌋₊) (lam r)‖) :
    (S.card : ℝ) ≤ T * N ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hRN : R ≤ N := by
    calc
      R ≤ 2 * N / T := hwidth
      _ ≤ N := by
        rw [div_le_iff₀ hT0]
        nlinarith
  have hamp0 : 0 < N ^ (alpha - 1) := Real.rpow_pos_of_pos hN0 _
  have hV : 0 < V := hamp0.trans_le hamp
  have henergy := card_largeValues_routeT_physicalSlice_le hN hR hRN
    hdelta hTord hTordN hgap hband hbig hV
  have hratio : R / N ≤ 2 / T := by
    rw [div_le_iff₀ hN0]
    calc
      R ≤ 2 * N / T := hwidth
      _ = (2 / T) * N := by ring
  have hlog0 : 0 ≤ (1 + Real.log (3 * N)) ^ 4 := by positivity
  have henergyHeight :
      (S.card : ℝ) * V ^ 2 ≤ T ^ eta * T⁻¹ := by
    calc
      (S.card : ℝ) * V ^ 2 ≤
          312 * (R / N) * (1 + Real.log (3 * N)) ^ 4 := henergy
      _ ≤ 312 * (2 / T) * (1 + Real.log (3 * N)) ^ 4 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio (by norm_num)) hlog0
      _ = T⁻¹ * (624 * (1 + Real.log (3 * N)) ^ 4) := by
        rw [inv_eq_one_div]
        ring
      _ ≤ T⁻¹ * T ^ eta :=
        mul_le_mul_of_nonneg_left hpolylog (inv_nonneg.mpr hT0.le)
      _ = T ^ eta * T⁻¹ := by ring
  have hampSq : N ^ (2 * alpha - 2) ≤ V ^ 2 := by
    calc
      N ^ (2 * alpha - 2) = (N ^ (alpha - 1)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        norm_num
        congr 1
        ring
      _ ≤ V ^ 2 := pow_le_pow_left₀ hamp0.le hamp 2
  have henergyAmp :
      (S.card : ℝ) * N ^ (2 * alpha - 2) ≤ T ^ eta * T⁻¹ :=
    (mul_le_mul_of_nonneg_left hampSq (Nat.cast_nonneg S.card)).trans henergyHeight
  have hnormalize :
      (S.card : ℝ) ≤ T ^ eta * (T⁻¹ * N ^ (2 - 2 * alpha)) := by
    have hcancel : N ^ (2 - 2 * alpha) * N ^ (2 * alpha - 2) = 1 := by
      rw [← Real.rpow_add hN0]
      norm_num
    refine le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hN0 (2 * alpha - 2))
    calc
      (S.card : ℝ) * N ^ (2 * alpha - 2) ≤ T ^ eta * T⁻¹ := henergyAmp
      _ = (T ^ eta * (T⁻¹ * N ^ (2 - 2 * alpha))) *
          N ^ (2 * alpha - 2) := by
        calc
          T ^ eta * T⁻¹ = T ^ eta * T⁻¹ * 1 := by ring
          _ = T ^ eta * T⁻¹ *
              (N ^ (2 - 2 * alpha) * N ^ (2 * alpha - 2)) := by rw [hcancel]
          _ = _ := by ring
  exact hnormalize.trans
    (routeT_physicalSlice_power_le_secondAlternative (by linarith) hNscale hbudget)

/-- Every fixed Route-T physical-slice logarithmic packet is absorbed by an arbitrary positive
height reserve. -/
theorem eventually_routeT_physicalSlice_polylog_absorption
    {mu eta : ℝ} (hmu : 0 ≤ mu) (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      624 * (1 + Real.log (3 * T ^ mu)) ^ 4 ≤ T ^ eta := by
  let C : ℝ := 1 + Real.log 3 + mu
  have hlogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp only [C]; linarith
  have hlim : Filter.Tendsto
      (fun T : ℝ => (624 * C ^ 4) * ((Real.log T) ^ 4 / T ^ eta))
      Filter.atTop (nhds 0) := by
    simpa using (HTGeometry.tendsto_logPow_div_rpow heta 4).const_mul
      (624 * C ^ 4)
  have hsmall : ∀ᶠ T : ℝ in Filter.atTop,
      (624 * C ^ 4) * ((Real.log T) ^ 4 / T ^ eta) < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, Filter.eventually_ge_atTop (Real.exp 1)] with T hsmallT hT
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hT0 hT
  have hTmu : 0 < T ^ mu := Real.rpow_pos_of_pos hT0 _
  have hlogShape : Real.log (3 * T ^ mu) = Real.log 3 + mu * Real.log T := by
    rw [Real.log_mul (by norm_num) hTmu.ne', Real.log_rpow hT0]
  have hbase0 : 0 ≤ 1 + Real.log (3 * T ^ mu) := by
    rw [hlogShape]
    positivity
  have hbase : 1 + Real.log (3 * T ^ mu) ≤ C * Real.log T := by
    rw [hlogShape]
    dsimp only [C]
    nlinarith
  have hpow : (1 + Real.log (3 * T ^ mu)) ^ 4 ≤
      (C * Real.log T) ^ 4 := pow_le_pow_left₀ hbase0 hbase 4
  have hden : 0 < T ^ eta := Real.rpow_pos_of_pos hT0 _
  have hnum : 624 * C ^ 4 * (Real.log T) ^ 4 < T ^ eta := by
    apply (div_lt_one hden).mp
    calc
      (624 * C ^ 4 * (Real.log T) ^ 4) / T ^ eta =
          (624 * C ^ 4) * ((Real.log T) ^ 4 / T ^ eta) := by ring
      _ < 1 := hsmallT
  calc
    624 * (1 + Real.log (3 * T ^ mu)) ^ 4 ≤
        624 * (C * Real.log T) ^ 4 :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 624 * C ^ 4 * (Real.log T) ^ 4 := by ring
    _ ≤ T ^ eta := hnum.le

/-- Eventual closed Route-T receiver for the actual floor-truncated von-Mangoldt slice.  No raw
floor, logarithmic, width, or amplitude factor remains in the conclusion. -/
theorem eventually_card_largeValues_routeT_physicalSlice_secondAlternative
    {mu alpha eta : ℝ} (hmu : 0 < mu) (heta : 0 < eta)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {R delta Tord V : ℝ} {S : Finset ℕ} {lam : ℕ → ℝ},
        1 ≤ R → R ≤ 2 * T ^ mu / T →
        1 ≤ delta → 0 ≤ Tord → Tord ≤ T ^ mu →
        (T ^ mu) ^ (alpha - 1) ≤ V →
        (∀ i, lam i + delta ≤ lam (i + 1)) →
        (∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ Tord) →
        (∀ r ∈ S,
          V ≤ ‖dirPoly ⌊T ^ mu + 2 * R⌋₊
            (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
              ⌊T ^ mu + 2 * R⌋₊) (lam r)‖) →
        (S.card : ℝ) ≤
          T * (T ^ mu) ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  have hpoly := eventually_routeT_physicalSlice_polylog_absorption hmu.le heta
  have hTtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T := Filter.eventually_ge_atTop 2
  have hNtop : Filter.Tendsto (fun T : ℝ => T ^ mu) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hmu
  have hNtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T ^ mu :=
    (Filter.tendsto_atTop.1 hNtop) 2
  filter_upwards [hpoly, hTtwo, hNtwo] with T hpolyT hTtwoT hNtwoT
  intro R delta Tord V S lam hR hwidth hdelta hTord hTordN hamp hgap hband hbig
  exact card_largeValues_routeT_physicalSlice_secondAlternative
    hTtwoT rfl hNtwoT hR hwidth hdelta hTord hTordN hamp hpolyT hbudget
      hgap hband hbig

/-- Complete central physical-slice dichotomy at Route-T scale: either the low-amplitude layer
already carries the signed defect, or the extracted literal von-Mangoldt superlevel satisfies
Maynard's exact second count alternative. -/
theorem eventually_physicalSlice_central_base_or_secondAlternative_of_adjacent_defect
    {mu alpha eta : ℝ} (hmu : 0 < mu) (heta : 0 < eta)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {H R a delta D Tord : ℝ} {Q n : ℕ},
        0 < H → 1 ≤ R → H ≤ R → R ≤ 2 * T ^ mu / T →
        1 ≤ delta → 0 < D → 0 < Q →
        (∀ y ∈ Set.Icc a (a + ((2 * n : ℕ) : ℝ) * delta),
          |y| ≤ T ^ mu / (2 * R)) →
        D ≤ ‖∫ y in a..(a + ((2 * n : ℕ) : ℝ) * delta),
          dirPoly ⌊T ^ mu + 2 * R⌋₊
              (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
                ⌊T ^ mu + 2 * R⌋₊) (-y) *
            (routeTNormalizedSmoothWindowMellin (T ^ mu) R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin (T ^ mu) H
                ((1 : ℂ) + (y : ℝ) * I))‖ →
        (⌊T ^ mu + 2 * R⌋₊ : ℝ) *
            (Real.log ⌊T ^ mu + 2 * R⌋₊ / ⌊T ^ mu⌋₊) ≤
          (((2 ^ Q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) →
        delta / 2 ≤ a →
        a + ((2 * n : ℕ) : ℝ) * delta + delta / 2 ≤ Tord →
        0 ≤ Tord → Tord ≤ T ^ mu →
        D / (16 * delta) ≤ (n : ℝ) * (T ^ mu) ^ (alpha - 1) ∨
          ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
            (∀ i, lam i + delta ≤ lam (i + 1)) ∧
            S ⊆ Finset.range n ∧ q < Q ∧
            (∀ j < n,
              lam j ∈ Set.Icc (a + ((2 * j : ℕ) : ℝ) * delta)
                  (a + (((2 * j : ℕ) : ℝ) + 1) * delta) ∨
              lam j ∈ Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * delta)
                  (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * delta)) ∧
            (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) ≤
              ‖dirPoly ⌊T ^ mu + 2 * R⌋₊
                (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
                  ⌊T ^ mu + 2 * R⌋₊) (lam r)‖) ∧
            D / (16 * delta * (Q : ℝ)) ≤
              (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) *
                (S.card : ℝ) ∧
            (S.card : ℝ) ≤
              T * (T ^ mu) ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  have hsecond :=
    eventually_card_largeValues_routeT_physicalSlice_secondAlternative
      (alpha := alpha) hmu heta hbudget
  have hTtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T := Filter.eventually_ge_atTop 2
  have hNtop : Filter.Tendsto (fun T : ℝ => T ^ mu) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hmu
  have hNtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T ^ mu :=
    (Filter.tendsto_atTop.1 hNtop) 2
  filter_upwards [hsecond, hTtwo, hNtwo] with T hsecondT hTtwoT hNtwoT
  intro H R a delta D Tord Q n hH hR hHR hwidth hdelta hD hQ hcentral
    hdefect hP ha hTband hTord hTordN
  let N : ℝ := T ^ mu
  let A : ℕ := ⌊N⌋₊
  let B : ℕ := ⌊N + 2 * R⌋₊
  let v : ℝ := N ^ (alpha - 1)
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hNtwoN : 2 ≤ N := by simpa only [N] using hNtwoT
  have hR0 : 0 < R := by linarith
  have hdelta0 : 0 < delta := by linarith
  have hv : 0 < v := Real.rpow_pos_of_pos hN0 _
  have hA : 1 ≤ A := by
    have hfloor : N < (A : ℝ) + 1 := by
      dsimp only [A]
      exact Nat.lt_floor_add_one N
    have hAcast : (1 : ℝ) ≤ (A : ℝ) := by
      linarith
    exact_mod_cast hAcast
  have hB : 2 ≤ B := by
    have hBcast : (2 : ℝ) ≤ (B : ℝ) := by
      have hfloor : N + 2 * R < (B : ℝ) + 1 := by
        dsimp only [B]
        exact Nat.lt_floor_add_one (N + 2 * R)
      linarith
    exact_mod_cast hBcast
  have hAB : A ≤ B := by
    dsimp only [A, B]
    exact Nat.floor_mono (by linarith)
  have hcell :=
    physicalSlice_base_or_exists_dyadic_superlevel_energy_of_adjacent_defect_central
      hA hB hAB hN0 hH hR0 hHR hdelta0 hD hv hQ
        (by simpa only [N] using hcentral)
        (by simpa only [A, B, N] using hdefect)
        (by simpa only [A, B, N, v] using hP)
        ha hTband
  rcases hcell with hbase | hhigh
  · exact Or.inl (by simpa only [N, v] using hbase)
  · right
    obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmass, _henergy⟩ := hhigh
    have hband : ∀ r ∈ S,
        delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ Tord := by
      intro r hr
      have hrn : r < n := Finset.mem_range.mp (hS hr)
      rcases hmem r hrn with heven | hodd
      · constructor
        · have har : a ≤ lam r := by
            have hr0 : (0 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by positivity
            nlinarith [heven.1]
          exact ha.trans har
        · have hcast : ((2 * r : ℕ) : ℝ) + 1 ≤ (2 * n : ℕ) := by
            norm_cast
            omega
          nlinarith [heven.2]
      · constructor
        · have har : a ≤ lam r := by
            have hr0 : (0 : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) := by positivity
            nlinarith [hodd.1]
          exact ha.trans har
        · have hcast : ((2 * r + 1 : ℕ) : ℝ) + 1 ≤ (2 * n : ℕ) := by
            norm_cast
            omega
          nlinarith [hodd.2]
    have hamp : N ^ (alpha - 1) ≤ (((2 ^ q : ℕ) : ℝ) * v) := by
      have hpow : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
      dsimp only [v]
      calc
        N ^ (alpha - 1) = 1 * N ^ (alpha - 1) := by ring
        _ ≤ ((2 ^ q : ℕ) : ℝ) * N ^ (alpha - 1) :=
          mul_le_mul_of_nonneg_right hpow hv.le
    have hcount : (S.card : ℝ) ≤
        T * N ^ (1 + routeTGapMomentNu - 2 * alpha) := by
      exact hsecondT hR hwidth hdelta hTord hTordN hamp hgap hband
        (by simpa only [A, B, N, v] using hlarge)
    refine ⟨lam, S, q, hgap, hS, hq, hmem, ?_, ?_, ?_⟩
    · simpa only [A, B, N, v] using hlarge
    · simpa only [N, v] using hmass
    · simpa only [N] using hcount

/-- Outer-wing analogue of the complete physical-slice dichotomy.  The only extra base-layer
cost is the exact quadratic Mellin-decay factor. -/
theorem exists_eventually_physicalSlice_tail_base_or_secondAlternative_of_adjacent_defect
    {mu alpha eta : ℝ} (hmu : 0 < mu) (heta : 0 < eta)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        ∀ {H R U a delta D Tord : ℝ} {Q n : ℕ},
          0 < H → 1 ≤ R → H ≤ R → R ≤ 2 * H →
          R ≤ 2 * T ^ mu / T → 0 < U →
          1 ≤ delta → 0 < D → 0 < Q →
          (∀ y ∈ Set.Icc a (a + ((2 * n : ℕ) : ℝ) * delta), U ≤ |y|) →
          D ≤ ‖∫ y in a..(a + ((2 * n : ℕ) : ℝ) * delta),
            dirPoly ⌊T ^ mu + 2 * R⌋₊
                (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
                  ⌊T ^ mu + 2 * R⌋₊) (-y) *
              (routeTNormalizedSmoothWindowMellin (T ^ mu) R
                  ((1 : ℂ) + (y : ℝ) * I) -
                routeTNormalizedSmoothWindowMellin (T ^ mu) H
                  ((1 : ℂ) + (y : ℝ) * I))‖ →
          (⌊T ^ mu + 2 * R⌋₊ : ℝ) *
              (Real.log ⌊T ^ mu + 2 * R⌋₊ / ⌊T ^ mu⌋₊) ≤
            (((2 ^ Q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) →
          delta / 2 ≤ a →
          a + ((2 * n : ℕ) : ℝ) * delta + delta / 2 ≤ Tord →
          0 ≤ Tord → Tord ≤ T ^ mu →
          D /
                (4 * delta *
                  (65 * C * ((T ^ mu) / R) ^ 2 / U ^ 2)) ≤
              (n : ℝ) * (T ^ mu) ^ (alpha - 1) ∨
            ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
              (∀ i, lam i + delta ≤ lam (i + 1)) ∧
              S ⊆ Finset.range n ∧ q < Q ∧
              (∀ j < n,
                lam j ∈ Set.Icc (a + ((2 * j : ℕ) : ℝ) * delta)
                    (a + (((2 * j : ℕ) : ℝ) + 1) * delta) ∨
                lam j ∈ Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * delta)
                    (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * delta)) ∧
              (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) ≤
                ‖dirPoly ⌊T ^ mu + 2 * R⌋₊
                  (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
                    ⌊T ^ mu + 2 * R⌋₊) (lam r)‖) ∧
              D /
                  (4 * delta *
                    (65 * C * ((T ^ mu) / R) ^ 2 / U ^ 2) * (Q : ℝ)) ≤
                (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) *
                  (S.card : ℝ) ∧
              (S.card : ℝ) ≤
                T * (T ^ mu) ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  obtain ⟨C, hC, houter⟩ :=
    physicalSlice_base_or_exists_dyadic_superlevel_energy_of_adjacent_defect_tail
  refine ⟨C, hC, ?_⟩
  have hsecond :=
    eventually_card_largeValues_routeT_physicalSlice_secondAlternative
      (alpha := alpha) hmu heta hbudget
  have hTtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T := Filter.eventually_ge_atTop 2
  have hNtop : Filter.Tendsto (fun T : ℝ => T ^ mu) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hmu
  have hNtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T ^ mu :=
    (Filter.tendsto_atTop.1 hNtop) 2
  filter_upwards [hsecond, hTtwo, hNtwo] with T hsecondT hTtwoT hNtwoT
  intro H R U a delta D Tord Q n hH hR hHR hRH hwidth hU hdelta hD hQ
    haway hdefect hP ha hTband hTord hTordN
  let N : ℝ := T ^ mu
  let A : ℕ := ⌊N⌋₊
  let B : ℕ := ⌊N + 2 * R⌋₊
  let v : ℝ := N ^ (alpha - 1)
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hNtwoN : 2 ≤ N := by simpa only [N] using hNtwoT
  have hR0 : 0 < R := by linarith
  have hdelta0 : 0 < delta := by linarith
  have hv : 0 < v := Real.rpow_pos_of_pos hN0 _
  have hRN : R ≤ N := by
    calc
      R ≤ 2 * N / T := by simpa only [N] using hwidth
      _ ≤ N := by
        rw [div_le_iff₀ (by linarith : 0 < T)]
        nlinarith
  have hA : 1 ≤ A := by
    have hfloor : N < (A : ℝ) + 1 := by
      dsimp only [A]
      exact Nat.lt_floor_add_one N
    have hAcast : (1 : ℝ) ≤ (A : ℝ) := by linarith
    exact_mod_cast hAcast
  have hB : 2 ≤ B := by
    have hBcast : (2 : ℝ) ≤ (B : ℝ) := by
      have hfloor : N + 2 * R < (B : ℝ) + 1 := by
        dsimp only [B]
        exact Nat.lt_floor_add_one (N + 2 * R)
      linarith
    exact_mod_cast hBcast
  have hAB : A ≤ B := by
    dsimp only [A, B]
    exact Nat.floor_mono (by linarith)
  have hcell := houter hA hB hAB hN0 hH hR0 hHR hRH hRN hU hdelta0 hD hv hQ
    (by simpa only [N] using haway)
    (by simpa only [A, B, N] using hdefect)
    (by simpa only [A, B, N, v] using hP)
    ha hTband
  rcases hcell with hbase | hhigh
  · exact Or.inl (by simpa only [N, v] using hbase)
  · right
    obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmass, _henergy⟩ := hhigh
    have hband : ∀ r ∈ S,
        delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ Tord := by
      intro r hr
      have hrn : r < n := Finset.mem_range.mp (hS hr)
      rcases hmem r hrn with heven | hodd
      · constructor
        · have har : a ≤ lam r := by
            have hr0 : (0 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by positivity
            nlinarith [heven.1]
          exact ha.trans har
        · have hcast : ((2 * r : ℕ) : ℝ) + 1 ≤ (2 * n : ℕ) := by
            norm_cast
            omega
          nlinarith [heven.2]
      · constructor
        · have har : a ≤ lam r := by
            have hr0 : (0 : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) := by positivity
            nlinarith [hodd.1]
          exact ha.trans har
        · have hcast : ((2 * r + 1 : ℕ) : ℝ) + 1 ≤ (2 * n : ℕ) := by
            norm_cast
            omega
          nlinarith [hodd.2]
    have hamp : N ^ (alpha - 1) ≤ (((2 ^ q : ℕ) : ℝ) * v) := by
      have hpow : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
      dsimp only [v]
      calc
        N ^ (alpha - 1) = 1 * N ^ (alpha - 1) := by ring
        _ ≤ ((2 ^ q : ℕ) : ℝ) * N ^ (alpha - 1) :=
          mul_le_mul_of_nonneg_right hpow hv.le
    have hcount : (S.card : ℝ) ≤
        T * N ^ (1 + routeTGapMomentNu - 2 * alpha) := by
      exact hsecondT hR hwidth hdelta hTord hTordN hamp hgap hband
        (by simpa only [A, B, N, v] using hlarge)
    refine ⟨lam, S, q, hgap, hS, hq, hmem, ?_, ?_, ?_⟩
    · simpa only [A, B, N, v] using hlarge
    · simpa only [N, v] using hmass
    · simpa only [N] using hcount

end RHTower.Sieve
