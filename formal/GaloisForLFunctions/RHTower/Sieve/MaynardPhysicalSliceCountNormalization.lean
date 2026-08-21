import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceOuterCellReceiver
import GaloisForLFunctions.HTGeometry.WindowRpowIntegral

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

private theorem selectedCell_mem_physicalSlice_band
    {a delta Tord : ℝ} {n : ℕ} {S : Finset ℕ} {lam : ℕ → ℝ}
    (hdelta : 0 ≤ delta) (hS : S ⊆ Finset.range n)
    (hmem : ∀ j < n,
      lam j ∈ Set.Icc (a + ((2 * j : ℕ) : ℝ) * delta)
          (a + (((2 * j : ℕ) : ℝ) + 1) * delta) ∨
      lam j ∈ Set.Icc (a + ((2 * j + 1 : ℕ) : ℝ) * delta)
          (a + (((2 * j + 1 : ℕ) : ℝ) + 1) * delta))
    (ha : delta / 2 ≤ a)
    (hTband : a + ((2 * n : ℕ) : ℝ) * delta + delta / 2 ≤ Tord) :
    ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ Tord := by
  intro r hr
  have hrn : r < n := Finset.mem_range.mp (hS hr)
  rcases hmem r hrn with heven | hodd
  · have hindex : (((2 * r : ℕ) : ℝ) + 1) ≤ ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * r + 1 ≤ 2 * n by omega)
    constructor
    · have hnonneg : 0 ≤ ((2 * r : ℕ) : ℝ) * delta :=
        mul_nonneg (Nat.cast_nonneg _) hdelta
      linarith [heven.1]
    · nlinarith [heven.2]
  · have hindex : (((2 * r + 1 : ℕ) : ℝ) + 1) ≤ ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * r + 1 + 1 ≤ 2 * n by omega)
    constructor
    · have hnonneg : 0 ≤ ((2 * r + 1 : ℕ) : ℝ) * delta :=
        mul_nonneg (Nat.cast_nonneg _) hdelta
      linarith [hodd.1]
    · nlinarith [hodd.2]

private theorem rpow_le_two_pow_mul_rpow
    {N alpha : ℝ} (hN : 0 ≤ N) (q : ℕ) :
    N ^ (alpha - 1) ≤ (((2 ^ q : ℕ) : ℝ) * N ^ (alpha - 1)) := by
  have hpow : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_two_pow
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hN _)

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
        delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ Tord :=
      selectedCell_mem_physicalSlice_band (by positivity) hS hmem ha hTband
    have hamp : N ^ (alpha - 1) ≤ (((2 ^ q : ℕ) : ℝ) * v) := by
      simpa only [v] using rpow_le_two_pow_mul_rpow hN0.le q
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
        delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ Tord :=
      selectedCell_mem_physicalSlice_band (by positivity) hS hmem ha hTband
    have hamp : N ^ (alpha - 1) ≤ (((2 ^ q : ℕ) : ℝ) * v) := by
      simpa only [v] using rpow_le_two_pow_mul_rpow hN0.le q
    have hcount : (S.card : ℝ) ≤
        T * N ^ (1 + routeTGapMomentNu - 2 * alpha) := by
      exact hsecondT hR hwidth hdelta hTord hTordN hamp hgap hband
        (by simpa only [A, B, N, v] using hlarge)
    refine ⟨lam, S, q, hgap, hS, hq, hmem, ?_, ?_, ?_⟩
    · simpa only [A, B, N, v] using hlarge
    · simpa only [N, v] using hmass
    · simpa only [N] using hcount

/-- Arbitrary central interval, with exact even partition hidden after use.  The surviving sequence
has unit spacing, retains a fixed fraction of signed mass, and already satisfies Route T's second
count alternative. -/
theorem eventually_physicalSlice_centralInterval_base_or_secondAlternative
    {mu alpha eta : ℝ} (hmu : 0 < mu) (heta : 0 < eta)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {H R a b D Tord : ℝ} {Q : ℕ},
        0 < H → 1 ≤ R → H ≤ R → R ≤ 2 * T ^ mu / T →
        0 < D → 0 < Q → a + 2 ≤ b → 1 ≤ a → b + 1 ≤ Tord →
        0 ≤ Tord → Tord ≤ T ^ mu →
        (∀ y ∈ Set.Icc a b, |y| ≤ T ^ mu / (2 * R)) →
        D ≤ ‖∫ y in a..b,
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
        D ≤ 8 * (b - a) * (T ^ mu) ^ (alpha - 1) ∨
          ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
            (∀ i, lam i + 1 ≤ lam (i + 1)) ∧ q < Q ∧
            (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) ≤
              ‖dirPoly ⌊T ^ mu + 2 * R⌋₊
                (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
                  ⌊T ^ mu + 2 * R⌋₊) (lam r)‖) ∧
            D / (32 * (Q : ℝ)) ≤
              (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) *
                (S.card : ℝ) ∧
            (S.card : ℝ) ≤
              T * (T ^ mu) ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  have hexact :=
    eventually_physicalSlice_central_base_or_secondAlternative_of_adjacent_defect
      (alpha := alpha) hmu heta hbudget
  filter_upwards [hexact] with T hexactT
  intro H R a b D Tord Q hH hR hHR hwidth hD hQ hab ha hbandTop hTord hTordN
    hcentral hdefect hP
  obtain ⟨n, delta, hn, hdelta, hdeltaTwo, hb⟩ :=
    exists_even_cells_unit_two_of_two_le_length hab
  have hTband : a + ((2 * n : ℕ) : ℝ) * delta + delta / 2 ≤ Tord := by
    rw [← hb]
    linarith
  have hcentral' : ∀ y ∈ Set.Icc a
      (a + ((2 * n : ℕ) : ℝ) * delta),
      |y| ≤ T ^ mu / (2 * R) := by
    simpa only [← hb] using hcentral
  have hdefect' : D ≤ ‖∫ y in a..(a + ((2 * n : ℕ) : ℝ) * delta),
      dirPoly ⌊T ^ mu + 2 * R⌋₊
          (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
            ⌊T ^ mu + 2 * R⌋₊) (-y) *
        (routeTNormalizedSmoothWindowMellin (T ^ mu) R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin (T ^ mu) H
            ((1 : ℂ) + (y : ℝ) * I))‖ := by
    simpa only [← hb] using hdefect
  have hout := hexactT hH hR hHR hwidth hdelta hD hQ hcentral' hdefect' hP
    (by linarith) hTband hTord hTordN
  rcases hout with hbase | hhigh
  · left
    have hscale : 0 < 16 * delta := by positivity
    have hraw : D ≤ (n : ℝ) * (T ^ mu) ^ (alpha - 1) * (16 * delta) :=
      (div_le_iff₀ hscale).mp hbase
    calc
      D ≤ (n : ℝ) * (T ^ mu) ^ (alpha - 1) * (16 * delta) := hraw
      _ = 8 * (b - a) * (T ^ mu) ^ (alpha - 1) := by
        rw [hb]
        push_cast
        ring
  · right
    obtain ⟨lam, S, q, hgap, _hS, hq, _hmem, hlarge, hmass, hcount⟩ := hhigh
    have hgapOne : ∀ i, lam i + 1 ≤ lam (i + 1) := by
      intro i
      nlinarith [hgap i]
    have hdenSmall : 0 < 16 * delta * (Q : ℝ) := by positivity
    have hdenLarge : 16 * delta * (Q : ℝ) ≤ 32 * (Q : ℝ) := by
      have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
      nlinarith
    have hmassWeak : D / (32 * (Q : ℝ)) ≤
        (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) * (S.card : ℝ) := by
      exact (div_le_div_of_nonneg_left hD.le hdenSmall hdenLarge).trans hmass
    exact ⟨lam, S, q, hgapOne, hq, hlarge, hmassWeak, hcount⟩

/-- Arbitrary outer interval.  The quadratic transition cost is retained exactly; no endpoint
trimming or logarithmic loss survives. -/
theorem exists_eventually_physicalSlice_tailInterval_base_or_secondAlternative
    {mu alpha eta : ℝ} (hmu : 0 < mu) (heta : 0 < eta)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        ∀ {H R U a b D Tord : ℝ} {Q : ℕ},
          0 < H → 1 ≤ R → H ≤ R → R ≤ 2 * H →
          R ≤ 2 * T ^ mu / T → 0 < U →
          0 < D → 0 < Q → a + 2 ≤ b → 1 ≤ a → b + 1 ≤ Tord →
          0 ≤ Tord → Tord ≤ T ^ mu →
          (∀ y ∈ Set.Icc a b, U ≤ |y|) →
          D ≤ ‖∫ y in a..b,
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
          D ≤ 2 * (b - a) *
                (65 * C * ((T ^ mu) / R) ^ 2 / U ^ 2) *
                  (T ^ mu) ^ (alpha - 1) ∨
            ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
              (∀ i, lam i + 1 ≤ lam (i + 1)) ∧ q < Q ∧
              (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) ≤
                ‖dirPoly ⌊T ^ mu + 2 * R⌋₊
                  (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
                    ⌊T ^ mu + 2 * R⌋₊) (lam r)‖) ∧
              D /
                  (8 * (65 * C * ((T ^ mu) / R) ^ 2 / U ^ 2) * (Q : ℝ)) ≤
                (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) *
                  (S.card : ℝ) ∧
              (S.card : ℝ) ≤
                T * (T ^ mu) ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  obtain ⟨C, hC, hexact⟩ :=
    exists_eventually_physicalSlice_tail_base_or_secondAlternative_of_adjacent_defect
      (alpha := alpha) hmu heta hbudget
  refine ⟨C, hC, ?_⟩
  have hTtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T := Filter.eventually_ge_atTop 2
  filter_upwards [hexact, hTtwo] with T hexactT hTtwoT
  intro H R U a b D Tord Q hH hR hHR hRH hwidth hU hD hQ hab ha hbandTop
    hTord hTordN haway hdefect hP
  obtain ⟨n, delta, hn, hdelta, hdeltaTwo, hb⟩ :=
    exists_even_cells_unit_two_of_two_le_length hab
  have hNpos : 0 < T ^ mu := Real.rpow_pos_of_pos (by linarith) _
  have hRpos : 0 < R := by linarith
  have hTband : a + ((2 * n : ℕ) : ℝ) * delta + delta / 2 ≤ Tord := by
    rw [← hb]
    linarith
  have haway' : ∀ y ∈ Set.Icc a
      (a + ((2 * n : ℕ) : ℝ) * delta), U ≤ |y| := by
    simpa only [← hb] using haway
  have hdefect' : D ≤ ‖∫ y in a..(a + ((2 * n : ℕ) : ℝ) * delta),
      dirPoly ⌊T ^ mu + 2 * R⌋₊
          (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
            ⌊T ^ mu + 2 * R⌋₊) (-y) *
        (routeTNormalizedSmoothWindowMellin (T ^ mu) R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin (T ^ mu) H
            ((1 : ℂ) + (y : ℝ) * I))‖ := by
    simpa only [← hb] using hdefect
  have hout := hexactT hH hR hHR hRH hwidth hU hdelta hD hQ haway' hdefect' hP
    (by linarith) hTband hTord hTordN
  rcases hout with hbase | hhigh
  · left
    let M : ℝ := 65 * C * ((T ^ mu) / R) ^ 2 / U ^ 2
    have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
    have hM : 0 < M := by dsimp only [M]; positivity
    have hscale : 0 < 4 * delta * M := by positivity
    have hraw : D ≤ (n : ℝ) * (T ^ mu) ^ (alpha - 1) * (4 * delta * M) := by
      exact (div_le_iff₀ hscale).mp (by simpa only [M] using hbase)
    calc
      D ≤ (n : ℝ) * (T ^ mu) ^ (alpha - 1) * (4 * delta * M) := hraw
      _ = 2 * (b - a) * M * (T ^ mu) ^ (alpha - 1) := by
        rw [hb]
        push_cast
        ring
      _ = 2 * (b - a) *
            (65 * C * ((T ^ mu) / R) ^ 2 / U ^ 2) *
              (T ^ mu) ^ (alpha - 1) := by rfl
  · right
    obtain ⟨lam, S, q, hgap, _hS, hq, _hmem, hlarge, hmass, hcount⟩ := hhigh
    let M : ℝ := 65 * C * ((T ^ mu) / R) ^ 2 / U ^ 2
    have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
    have hM : 0 < M := by dsimp only [M]; positivity
    have hgapOne : ∀ i, lam i + 1 ≤ lam (i + 1) := by
      intro i
      nlinarith [hgap i]
    have hdenSmall : 0 < 4 * delta * M * (Q : ℝ) := by positivity
    have hdenLarge : 4 * delta * M * (Q : ℝ) ≤ 8 * M * (Q : ℝ) := by
      have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
      nlinarith
    have hmassWeak : D / (8 * M * (Q : ℝ)) ≤
        (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) * (S.card : ℝ) := by
      exact (div_le_div_of_nonneg_left hD.le hdenSmall hdenLarge).trans
        (by simpa only [M] using hmass)
    refine ⟨lam, S, q, hgapOne, hq, hlarge, ?_, hcount⟩
    simpa only [M] using hmassWeak

/-- Pointwise envelope of the actual floor-truncated physical von-Mangoldt slice. -/
def routeTPhysicalSliceEnvelope (N R : ℝ) : ℝ :=
  (⌊N + 2 * R⌋₊ : ℝ) *
    (Real.log ⌊N + 2 * R⌋₊ / ⌊N⌋₊)

/-- Signed mass surviving the exact central and far-tail localization costs. -/
def routeTPhysicalSliceLocalizationSurplus
    (C N R U V D : ℝ) : ℝ :=
  D - 16 * routeTPhysicalSliceEnvelope N R * (R / N) * U ^ 2 -
    routeTPhysicalSliceEnvelope N R * (130 * C * (N / R) ^ 2 / V)

/-- Full physical-slice receiver at the universal transition `N/(2R)`.  Central and outer wings
share one conclusion because quadratic Mellin decay is exactly constant at that transition. -/
theorem exists_eventually_physicalSlice_annulus_base_or_secondAlternative
    {mu alpha eta : ℝ} (hmu : 0 < mu) (heta : 0 < eta)
    (hbudget : mu * (1 - routeTGapMomentNu) + eta ≤ 2) :
    ∃ Cloc Ccell : ℝ, 1 ≤ Cloc ∧ 1 ≤ Ccell ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        ∀ {H R U V D Tord : ℝ} {Q : ℕ},
          0 < H → 1 ≤ R → H ≤ R → R ≤ 2 * H →
          R ≤ 2 * T ^ mu / T → 1 ≤ U →
          U + 2 ≤ (T ^ mu) / (2 * R) →
          (T ^ mu) / (2 * R) + 2 ≤ V →
          V + 1 ≤ Tord → 0 ≤ Tord → Tord ≤ T ^ mu →
          0 < routeTPhysicalSliceLocalizationSurplus
            Cloc (T ^ mu) R U V D →
          D ≤ ‖∫ y : ℝ,
            dirPoly ⌊T ^ mu + 2 * R⌋₊
                (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
                  ⌊T ^ mu + 2 * R⌋₊) (-y) *
              (routeTNormalizedSmoothWindowMellin (T ^ mu) R
                  ((1 : ℂ) + (y : ℝ) * I) -
                routeTNormalizedSmoothWindowMellin (T ^ mu) H
                  ((1 : ℂ) + (y : ℝ) * I))‖ →
          routeTPhysicalSliceEnvelope (T ^ mu) R ≤
            (((2 ^ Q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) →
          0 < Q →
          routeTPhysicalSliceLocalizationSurplus
                Cloc (T ^ mu) R U V D ≤
              32 * ((T ^ mu) / (2 * R) - U) *
                (T ^ mu) ^ (alpha - 1) ∨
            routeTPhysicalSliceLocalizationSurplus
                Cloc (T ^ mu) R U V D ≤
              2080 * Ccell * (V - (T ^ mu) / (2 * R)) *
                (T ^ mu) ^ (alpha - 1) ∨
            ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
              (∀ i, lam i + 1 ≤ lam (i + 1)) ∧ q < Q ∧
              (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) ≤
                ‖dirPoly ⌊T ^ mu + 2 * R⌋₊
                  (routeTVonMangoldtSliceCoeff ⌊T ^ mu⌋₊
                    ⌊T ^ mu + 2 * R⌋₊) (lam r)‖) ∧
              routeTPhysicalSliceLocalizationSurplus
                    Cloc (T ^ mu) R U V D /
                  (8320 * Ccell * (Q : ℝ)) ≤
                (((2 ^ q : ℕ) : ℝ) * (T ^ mu) ^ (alpha - 1)) *
                  (S.card : ℝ) ∧
              (S.card : ℝ) ≤
                T * (T ^ mu) ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  obtain ⟨Cloc, hCloc, hlocalize⟩ :=
    exists_positive_interval_norm_ge_quarter_of_physicalSlice_annulus
  obtain ⟨Ccell, hCcell, houter⟩ :=
    exists_eventually_physicalSlice_tailInterval_base_or_secondAlternative
      (alpha := alpha) hmu heta hbudget
  have hcentral := eventually_physicalSlice_centralInterval_base_or_secondAlternative
    (alpha := alpha) hmu heta hbudget
  refine ⟨Cloc, Ccell, hCloc, hCcell, ?_⟩
  have hTtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T := Filter.eventually_ge_atTop 2
  have hNtop : Filter.Tendsto (fun T : ℝ => T ^ mu) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hmu
  have hNtwo : ∀ᶠ T : ℝ in Filter.atTop, 2 ≤ T ^ mu :=
    (Filter.tendsto_atTop.1 hNtop) 2
  filter_upwards [houter, hcentral, hTtwo, hNtwo] with T houterT hcentralT hTtwoT hNtwoT
  intro H R U V D Tord Q hH hR hHR hRH hwidth hU hcentralLen houterLen
    hTordTop hTord hTordN hsurplus hfull hP hQ
  let N : ℝ := T ^ mu
  let A : ℕ := ⌊N⌋₊
  let B : ℕ := ⌊N + 2 * R⌋₊
  let W : ℝ := N / (2 * R)
  let E : ℝ := routeTPhysicalSliceLocalizationSurplus Cloc N R U V D
  let v : ℝ := N ^ (alpha - 1)
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hNtwoN : 2 ≤ N := by simpa only [N] using hNtwoT
  have hR0 : 0 < R := by linarith
  have hU0 : 0 < U := by linarith
  have hW0 : 0 < W := by dsimp only [W]; positivity
  have hV0 : 0 < V := by
    change W + 2 ≤ V at houterLen
    linarith
  have hRN : R ≤ N := by
    calc
      R ≤ 2 * N / T := by simpa only [N] using hwidth
      _ ≤ N := by
        rw [div_le_iff₀ hT0]
        nlinarith
  have hUW : U ≤ W := by
    dsimp only [W, N]
    linarith
  have hWV : W ≤ V := by
    dsimp only [W, N]
    linarith
  have hWone : 1 ≤ W := hU.trans hUW
  have hA : 1 ≤ A := by
    have hfloor : N < (A : ℝ) + 1 := by
      dsimp only [A]
      exact Nat.lt_floor_add_one N
    have hAcast : (1 : ℝ) ≤ (A : ℝ) := by linarith
    exact_mod_cast hAcast
  have hsmall : U * (2 * R / N) ≤ 1 := by
    have hfac : 0 < 2 * R / N := by positivity
    calc
      U * (2 * R / N) ≤ W * (2 * R / N) :=
        mul_le_mul_of_nonneg_right hUW hfac.le
      _ = 1 := by
        dsimp only [W]
        field_simp
  have hwingRaw := hlocalize (A := A) (B := B) hA hN0 hH hR0 hHR hRH hRN
    (by linarith) hUW hWV hV0 hsmall (by simpa only [A, B, N] using hfull)
  have hwing : E / 4 ≤ ‖∫ y in U..W,
        dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I))‖ ∨
      E / 4 ≤ ‖∫ y in W..V,
        dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I))‖ := by
    simpa only [E, routeTPhysicalSliceLocalizationSurplus,
      routeTPhysicalSliceEnvelope, A, B, N, W] using hwingRaw
  have hE : 0 < E := by simpa only [E, N] using hsurplus
  have hEQ : (0 : ℝ) < Q := by exact_mod_cast hQ
  rcases hwing with hcentralWing | houterWing
  · have hcentralBand : ∀ y ∈ Set.Icc U W, |y| ≤ N / (2 * R) := by
      intro y hy
      have hy0 : 0 ≤ y := hU0.le.trans hy.1
      rw [abs_of_nonneg hy0]
      simpa only [W] using hy.2
    have hcentralOut := hcentralT (D := E / 4) hH hR hHR
      (by simpa only [N] using hwidth) (by positivity) hQ
      (by simpa only [W, N] using hcentralLen) hU
      (by dsimp only [W, N]; linarith) hTord
      (by simpa only [N] using hTordN) hcentralBand
      (by simpa only [A, B, N, W] using hcentralWing)
      (by simpa only [routeTPhysicalSliceEnvelope, A, B, N, v] using hP)
    rcases hcentralOut with hbase | hhigh
    · left
      dsimp only [E, v, W, N] at hbase ⊢
      linarith
    · right; right
      obtain ⟨lam, S, q, hgap, hq, hlarge, hmass, hcount⟩ := hhigh
      have hdenSmall : 0 < 128 * (Q : ℝ) := by positivity
      have hdenLarge : 128 * (Q : ℝ) ≤ 8320 * Ccell * (Q : ℝ) := by
        nlinarith
      have hmassWeak : E / (8320 * Ccell * (Q : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
        have hmass' : E / (128 * (Q : ℝ)) ≤
            (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
          convert hmass using 1 <;> ring
        exact (div_le_div_of_nonneg_left hE.le hdenSmall hdenLarge).trans hmass'
      refine ⟨lam, S, q, hgap, hq, ?_, ?_, ?_⟩
      · simpa only [A, B, N, v] using hlarge
      · simpa only [E, N, v] using hmassWeak
      · simpa only [N] using hcount
  · have haway : ∀ y ∈ Set.Icc W V, W ≤ |y| := by
      intro y hy
      have hy0 : 0 ≤ y := hW0.le.trans hy.1
      rw [abs_of_nonneg hy0]
      exact hy.1
    have houterOut := houterT (D := E / 4) (U := W) (a := W) (b := V)
      hH hR hHR hRH
      (by simpa only [N] using hwidth) hW0 (by positivity) hQ
      (by simpa only [W, N] using houterLen) hWone hTordTop hTord
      (by simpa only [N] using hTordN) haway
      (by simpa only [A, B, N, W] using houterWing)
      (by simpa only [routeTPhysicalSliceEnvelope, A, B, N, v] using hP)
    have htransition :
        65 * Ccell * (N / R) ^ 2 / W ^ 2 = 260 * Ccell := by
      dsimp only [W]
      field_simp
      ring
    rcases houterOut with hbase | hhigh
    · right; left
      dsimp only [E, v, N] at hbase ⊢
      rw [htransition] at hbase
      linarith
    · right; right
      obtain ⟨lam, S, q, hgap, hq, hlarge, hmass, hcount⟩ := hhigh
      have hmass' : E / (8320 * Ccell * (Q : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) * v) * (S.card : ℝ) := by
        rw [htransition] at hmass
        convert hmass using 1 <;> ring
      refine ⟨lam, S, q, hgap, hq, ?_, ?_, ?_⟩
      · simpa only [A, B, N, v] using hlarge
      · simpa only [E, N, v] using hmass'
      · simpa only [N] using hcount

end RHTower.Sieve
