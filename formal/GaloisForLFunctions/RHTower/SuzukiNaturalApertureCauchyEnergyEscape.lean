import GaloisForLFunctions.RHTower.SuzukiCauchyReporterSecantWardCapacity
import GaloisForLFunctions.RHTower.DyadicVonMangoldtSqrtMass
import GaloisForLFunctions.HTGeometry.InverseSqrtEndpointIntegral

/-!
# Escape of the raw natural Suzuki Cauchy energy

The finite Cauchy Ward-capacity inequality becomes arithmetic after padding Suzuki's literal
Mangoldt packet at indices zero and one.  On the dyadic block `(2n,4n]` inside aperture `8n`, the
reporter anchor is at least `1/8`.  The PNT lower bound for square-root von Mangoldt mass therefore
forces the raw energy to grow at least as `n/288` along `8n`.

This is a closure theorem for one interpretation of the reflected-wall Ward target: the raw
unrenormalized natural energy cannot have a uniform cofinal upper bound.  Any viable cofinal SP-E
assembly must expose and compensate this anchor-visible prime mass before passage to the limit.
-/

open Complex MeasureTheory Filter
open scoped BigOperators ComplexConjugate NNReal ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Natural packet coefficient, padded by zero at indices zero and one. -/
def suzukiNaturalAperturePaddedWeight (N : ℕ) (i : Fin (N + 1)) : ℝ :=
  if 2 ≤ (i : ℕ) then (suzukiNaturalAperturePrimeWeight N i : ℝ) else 0

/-- Natural packet lag on the full finite aperture. -/
def suzukiNaturalAperturePaddedLag (N : ℕ) (i : Fin (N + 1)) : ℝ≥0 :=
  suzukiNaturalApertureLag N i

/-- Cauchy energy of the zero-padded natural packet. -/
def suzukiNaturalAperturePaddedCauchyEnergy (N : ℕ) : ℝ :=
  suzukiReporterSecantPacketCauchyEnergy
    (suzukiNaturalAperturePaddedLag N)
    (suzukiNaturalAperturePaddedWeight N)

/-- Lower-Hardy anchor amplitude of the zero-padded natural packet. -/
def suzukiNaturalApertureLowerHardyAmplitude (N : ℕ) : ℝ :=
  suzukiReporterSecantPacketLowerHardyAmplitude
    (suzukiNaturalAperturePaddedLag N)
    (suzukiNaturalAperturePaddedWeight N)

private theorem sum_fin_if_two_le_eq_sum_Icc
    {A : Type*} [AddCommMonoid A] (N : ℕ) (f : ℕ → A) :
    (∑ i : Fin (N + 1), if 2 ≤ (i : ℕ) then f i else 0) =
      ∑ k ∈ Finset.Icc 2 N, f k := by
  change (∑ i : Fin (N + 1),
      (fun k : ℕ => if 2 ≤ k then f k else 0) i) = _
  have hs := Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if 2 ≤ k then f k else 0) (N + 1)
  rw [hs, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k
    simp
    omega
  · intro k hk
    rfl

private theorem sum_fin_if_two_le_two_eq_sum_Icc
    {A : Type*} [AddCommMonoid A] (N : ℕ) (f : ℕ → ℕ → A) :
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        if 2 ≤ (j : ℕ) then if 2 ≤ (i : ℕ) then f i j else 0 else 0) =
      ∑ i ∈ Finset.Icc 2 N, ∑ j ∈ Finset.Icc 2 N, f i j := by
  calc
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        if 2 ≤ (j : ℕ) then if 2 ≤ (i : ℕ) then f i j else 0 else 0) =
        ∑ i : Fin (N + 1), if 2 ≤ (i : ℕ) then
          (∑ j : Fin (N + 1), if 2 ≤ (j : ℕ) then f i j else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : 2 ≤ (i : ℕ) <;> simp [h]
    _ = ∑ i ∈ Finset.Icc 2 N,
          (∑ j : Fin (N + 1), if 2 ≤ (j : ℕ) then f i j else 0) := by
      simpa using (sum_fin_if_two_le_eq_sum_Icc N
        (fun i => ∑ j : Fin (N + 1), if 2 ≤ (j : ℕ) then f i j else 0))
    _ = ∑ i ∈ Finset.Icc 2 N, ∑ j ∈ Finset.Icc 2 N, f i j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_fin_if_two_le_eq_sum_Icc N (f i)

theorem suzukiNaturalApertureLowerHardyAmplitude_sq_le_paddedEnergy (N : ℕ) :
    suzukiNaturalApertureLowerHardyAmplitude N ^ 2 ≤
      suzukiNaturalAperturePaddedCauchyEnergy N := by
  exact suzukiReporterSecantPacket_lowerHardy_sq_le_cauchyEnergy
    (suzukiNaturalAperturePaddedLag N)
    (suzukiNaturalAperturePaddedWeight N)

theorem suzukiNaturalAperturePaddedCauchyEnergy_eq (N : ℕ) :
    suzukiNaturalAperturePaddedCauchyEnergy N =
      suzukiNaturalApertureCauchyEnergy N := by
  rw [suzukiNaturalAperturePaddedCauchyEnergy,
    suzukiReporterSecantPacketCauchyEnergy_eq_sum_gram,
    suzukiNaturalApertureCauchyEnergy,
    suzukiNaturalAperturePairSet]
  rw [Finset.sum_product]
  change
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
      (if 2 ≤ (i : ℕ) then (suzukiNaturalAperturePrimeWeight N i : ℝ) else 0) *
        suzukiReporterSecantCauchyGram
          (suzukiNaturalApertureLag N i) (suzukiNaturalApertureLag N j) *
        (if 2 ≤ (j : ℕ) then (suzukiNaturalAperturePrimeWeight N j : ℝ) else 0)) =
      ∑ i ∈ Finset.Icc 2 N, ∑ j ∈ Finset.Icc 2 N,
        (suzukiNaturalAperturePrimeWeight N i : ℝ) *
          suzukiReporterSecantCauchyGram
            (suzukiNaturalApertureLag N i) (suzukiNaturalApertureLag N j) *
          (suzukiNaturalAperturePrimeWeight N j : ℝ)
  simpa [ite_mul, mul_ite] using sum_fin_if_two_le_two_eq_sum_Icc N (fun i j =>
    (suzukiNaturalAperturePrimeWeight N i : ℝ) *
      suzukiReporterSecantCauchyGram
        (suzukiNaturalApertureLag N i) (suzukiNaturalApertureLag N j) *
      (suzukiNaturalAperturePrimeWeight N j : ℝ))

/-- The literal natural Suzuki source energy controls its lower-Hardy anchor amplitude. -/
theorem suzukiNaturalApertureLowerHardyAmplitude_sq_le_energy (N : ℕ) :
    suzukiNaturalApertureLowerHardyAmplitude N ^ 2 ≤
      suzukiNaturalApertureCauchyEnergy N := by
  rw [← suzukiNaturalAperturePaddedCauchyEnergy_eq]
  exact suzukiNaturalApertureLowerHardyAmplitude_sq_le_paddedEnergy N

theorem suzukiNaturalApertureLowerHardyAmplitude_eq_sum (N : ℕ) :
    suzukiNaturalApertureLowerHardyAmplitude N =
      ∑ k ∈ Finset.Icc 2 N,
        _root_.RHTower.criticalMellinAtomWeight k *
          _root_.RHTower.unitRieszSuzukiReporter 0
            (-(suzukiNaturalApertureLag N k : ℝ)) := by
  rw [suzukiNaturalApertureLowerHardyAmplitude,
    suzukiReporterSecantPacketLowerHardyAmplitude]
  simp only [suzukiNaturalAperturePaddedWeight,
    suzukiNaturalAperturePaddedLag, suzukiNaturalAperturePrimeWeight,
    ite_mul, zero_mul]
  change (∑ i : Fin (N + 1), if 2 ≤ (i : ℕ) then
      _root_.RHTower.criticalMellinAtomWeight i *
        _root_.RHTower.unitRieszSuzukiReporter 0
          (-(suzukiNaturalApertureLag N i : ℝ)) else 0) = _
  exact sum_fin_if_two_le_eq_sum_Icc N (fun k =>
    _root_.RHTower.criticalMellinAtomWeight k *
      _root_.RHTower.unitRieszSuzukiReporter 0
        (-(suzukiNaturalApertureLag N k : ℝ)))

theorem unitRieszSuzukiReporter_neg_naturalLag_eq
    {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    _root_.RHTower.unitRieszSuzukiReporter 0
        (-(suzukiNaturalApertureLag N k : ℝ)) =
      Real.sqrt ((k : ℝ) / N) - (k : ℝ) / N := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hk hkN
  have hkNR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hlog : 0 ≤ Real.log N - Real.log k :=
    sub_nonneg.mpr (Real.log_le_log hkR hkNR)
  rw [suzukiNaturalApertureLag]
  simp only [Real.coe_toNNReal _ hlog]
  have hfull : Real.exp (-(Real.log N - Real.log k)) = (k : ℝ) / N := by
    rw [neg_sub, Real.exp_sub, Real.exp_log hkR, Real.exp_log hNR]
  have hhalfSq : Real.exp (-(Real.log N - Real.log k) / 2) ^ 2 =
      (k : ℝ) / N := by
    rw [pow_two, ← Real.exp_add]
    convert hfull using 1
    ring
  have hratio : 0 ≤ (k : ℝ) / N := div_nonneg hkR.le hNR.le
  have hsqrtSq : Real.sqrt ((k : ℝ) / N) ^ 2 = (k : ℝ) / N :=
    Real.sq_sqrt hratio
  have hhalf : Real.exp (-(Real.log N - Real.log k) / 2) =
      Real.sqrt ((k : ℝ) / N) := by
    nlinarith [Real.exp_pos (-(Real.log N - Real.log k) / 2),
      Real.sqrt_nonneg ((k : ℝ) / N)]
  rw [_root_.RHTower.unitRieszSuzukiReporter]
  rw [show (-((Real.log N - Real.log k)) - 0) / 2 =
      -(Real.log N - Real.log k) / 2 by ring,
    show -((Real.log N - Real.log k)) - 0 =
      -(Real.log N - Real.log k) by ring,
    hhalf, hfull]

/-- On the dyadic block `(2n,4n]` inside aperture `8n`, every Suzuki reporter has a
uniformly positive anchor value. -/
theorem one_eighth_le_unitRieszSuzukiReporter_neg_naturalLag
    {n k : ℕ} (hn : 1 ≤ n) (hk : k ∈ Finset.Ioc (2 * n) (4 * n)) :
    (1 : ℝ) / 8 ≤ _root_.RHTower.unitRieszSuzukiReporter 0
      (-(suzukiNaturalApertureLag (8 * n) k : ℝ)) := by
  rw [unitRieszSuzukiReporter_neg_naturalLag_eq
    (by have := (Finset.mem_Ioc.mp hk).1; omega)
    (by have := (Finset.mem_Ioc.mp hk).2; omega)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hden : (0 : ℝ) < (8 * n : ℕ) := by positivity
  have hkIoc := Finset.mem_Ioc.mp hk
  have hklo : (2 : ℝ) * n < k := by exact_mod_cast hkIoc.1
  have hkhi : (k : ℝ) ≤ 4 * n := by exact_mod_cast hkIoc.2
  have hrlo : (1 : ℝ) / 4 ≤ (k : ℝ) / (8 * n : ℕ) := by
    rw [le_div_iff₀ hden]
    push_cast
    linarith
  have hrhi : (k : ℝ) / (8 * n : ℕ) ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ hden]
    push_cast
    linarith
  have hratio : 0 ≤ (k : ℝ) / (8 * n : ℕ) := le_trans (by norm_num) hrlo
  have hsquare : Real.sqrt ((k : ℝ) / (8 * n : ℕ)) ^ 2 =
      (k : ℝ) / (8 * n : ℕ) := Real.sq_sqrt hratio
  have hsqrt0 : 0 ≤ Real.sqrt ((k : ℝ) / (8 * n : ℕ)) := Real.sqrt_nonneg _
  have hsqrtlo : (1 : ℝ) / 2 ≤ Real.sqrt ((k : ℝ) / (8 * n : ℕ)) := by
    nlinarith
  have hsqrthi : Real.sqrt ((k : ℝ) / (8 * n : ℕ)) ≤ (3 : ℝ) / 4 := by
    nlinarith
  have hproduct : 0 ≤
      (Real.sqrt ((k : ℝ) / (8 * n : ℕ)) - (1 : ℝ) / 2) *
        ((3 : ℝ) / 4 - Real.sqrt ((k : ℝ) / (8 * n : ℕ))) :=
    mul_nonneg (sub_nonneg.mpr hsqrtlo) (sub_nonneg.mpr hsqrthi)
  nlinarith

theorem criticalMellinAtomWeight_eq_vonMangoldt_div_sqrt (k : ℕ) :
    _root_.RHTower.criticalMellinAtomWeight k =
      (ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k := by
  rw [_root_.RHTower.criticalMellinAtomWeight,
    rpow_neg_half_eq_inv_sqrt
      (Nat.cast_nonneg k)]
  rw [div_eq_mul_inv, mul_comm]

/-- A dyadic square-root von Mangoldt block injects into the natural Suzuki anchor with no
cancellation. -/
theorem dyadicSqrtVonMangoldtMass_div_eight_le_naturalAmplitude
    {n : ℕ} (hn : 1 ≤ n) :
    _root_.RHTower.dyadicSqrtVonMangoldtMass (2 * (n : ℝ)) / 8 ≤
      suzukiNaturalApertureLowerHardyAmplitude (8 * n) := by
  rw [suzukiNaturalApertureLowerHardyAmplitude_eq_sum]
  have hmass : _root_.RHTower.dyadicSqrtVonMangoldtMass (2 * (n : ℝ)) =
      ∑ k ∈ Finset.Ioc (2 * n) (4 * n),
        (ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k := by
    have hfloorTwo : ⌊2 * (n : ℝ)⌋₊ = 2 * n := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (Nat.floor_natCast (2 * n) : ⌊((2 * n : ℕ) : ℝ)⌋₊ = 2 * n)
    have hfloorFour : ⌊2 * (2 * (n : ℝ))⌋₊ = 4 * n := by
      calc
        ⌊2 * (2 * (n : ℝ))⌋₊ = 2 * (2 * n) := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using
            (Nat.floor_natCast (2 * (2 * n)) :
              ⌊((2 * (2 * n) : ℕ) : ℝ)⌋₊ = 2 * (2 * n))
        _ = 4 * n := by omega
    rw [_root_.RHTower.dyadicSqrtVonMangoldtMass]
    rw [hfloorTwo, hfloorFour]
  rw [hmass, Finset.sum_div]
  refine le_trans (Finset.sum_le_sum fun k hk => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · rw [← criticalMellinAtomWeight_eq_vonMangoldt_div_sqrt]
    have hrep := one_eighth_le_unitRieszSuzukiReporter_neg_naturalLag hn hk
    have hrep' : (8 : ℝ)⁻¹ ≤ _root_.RHTower.unitRieszSuzukiReporter 0
        (-(suzukiNaturalApertureLag (8 * n) k : ℝ)) := by
      simpa only [one_div] using hrep
    exact mul_le_mul_of_nonneg_left hrep'
      (_root_.RHTower.criticalMellinAtomWeight_nonneg k)
  · intro k hk
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
    omega
  · intro k hkIcc hkBlock
    exact mul_nonneg (_root_.RHTower.criticalMellinAtomWeight_nonneg k)
      (_root_.RHTower.unitRieszSuzukiReporter_nonneg_of_mem
        (neg_nonpos.mpr (suzukiNaturalApertureLag (8 * n) k).property))

/-- The PNT-sized dyadic block forces a linear lower bound for the literal natural Cauchy energy. -/
theorem suzukiNaturalApertureCauchyEnergy_ge_of_dyadicMass
    {n : ℕ} (hn : 1 ≤ n)
    (hmass : Real.sqrt (2 * (n : ℝ)) / 3 ≤
      _root_.RHTower.dyadicSqrtVonMangoldtMass (2 * (n : ℝ))) :
    (n : ℝ) / 288 ≤ suzukiNaturalApertureCauchyEnergy (8 * n) := by
  have hampMass := dyadicSqrtVonMangoldtMass_div_eight_le_naturalAmplitude hn
  have hamp : Real.sqrt (2 * (n : ℝ)) / 24 ≤
      suzukiNaturalApertureLowerHardyAmplitude (8 * n) := by
    calc
      Real.sqrt (2 * (n : ℝ)) / 24 =
          (Real.sqrt (2 * (n : ℝ)) / 3) / 8 := by ring
      _ ≤ _root_.RHTower.dyadicSqrtVonMangoldtMass (2 * (n : ℝ)) / 8 :=
        div_le_div_of_nonneg_right hmass (by norm_num)
      _ ≤ suzukiNaturalApertureLowerHardyAmplitude (8 * n) := hampMass
  have hroot0 : 0 ≤ Real.sqrt (2 * (n : ℝ)) / 24 := by positivity
  have hamp0 : 0 ≤ suzukiNaturalApertureLowerHardyAmplitude (8 * n) :=
    hroot0.trans hamp
  have hrootSq : Real.sqrt (2 * (n : ℝ)) ^ 2 = 2 * (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsq : (Real.sqrt (2 * (n : ℝ)) / 24) ^ 2 ≤
      suzukiNaturalApertureLowerHardyAmplitude (8 * n) ^ 2 := by
    have hproduct : 0 ≤
        (suzukiNaturalApertureLowerHardyAmplitude (8 * n) -
          Real.sqrt (2 * (n : ℝ)) / 24) *
        (suzukiNaturalApertureLowerHardyAmplitude (8 * n) +
          Real.sqrt (2 * (n : ℝ)) / 24) :=
      mul_nonneg (sub_nonneg.mpr hamp) (add_nonneg hamp0 hroot0)
    nlinarith
  calc
    (n : ℝ) / 288 = (Real.sqrt (2 * (n : ℝ)) / 24) ^ 2 := by
      nlinarith
    _ ≤ suzukiNaturalApertureLowerHardyAmplitude (8 * n) ^ 2 := hsq
    _ ≤ suzukiNaturalApertureCauchyEnergy (8 * n) :=
      suzukiNaturalApertureLowerHardyAmplitude_sq_le_energy (8 * n)

/-- The raw natural Suzuki Cauchy wall energy has a linear lower bound along apertures `8n`. -/
theorem eventually_suzukiNaturalApertureCauchyEnergy_ge_linear :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / 288 ≤ suzukiNaturalApertureCauchyEnergy (8 * n) := by
  have hscale : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
  have hmass : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (2 * (n : ℝ)) / 3 ≤
        _root_.RHTower.dyadicSqrtVonMangoldtMass (2 * (n : ℝ)) :=
    hscale.eventually _root_.RHTower.eventually_dyadicSqrtVonMangoldtMass_ge
  filter_upwards [eventually_ge_atTop (1 : ℕ), hmass] with n hn hmassn
  exact suzukiNaturalApertureCauchyEnergy_ge_of_dyadicMass hn hmassn

/-- **Raw-wall escape.** The unrenormalized natural Suzuki reporter-secant energy diverges along
the cofinal aperture subsequence `8n`; hence it cannot satisfy a uniform cofinal upper bound. -/
theorem tendsto_suzukiNaturalApertureCauchyEnergy_eight_mul_atTop :
    Tendsto (fun n : ℕ => suzukiNaturalApertureCauchyEnergy (8 * n)) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_suzukiNaturalApertureCauchyEnergy_ge_linear,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (288 * B)] with n henergy hn
  calc
    B ≤ (n : ℝ) / 288 := by linarith
    _ ≤ suzukiNaturalApertureCauchyEnergy (8 * n) := henergy

end

end GaloisForLFunctions.RHTower
