import GaloisForLFunctions.RHTower.CCMUnitRieszApertureResolventWeld
import GaloisForLFunctions.RHTower.CCMCriticalMellinRieszMobiusRenewal
import GaloisForLFunctions.RHTower.CCMUnitRieszQuadratureDefect

/-!
# Exponential coherent trace of the literal unit-Riesz source

The normalized half-line translates

`v_x(s) = 1_{x < s} exp (-(s-x)/2)`

have overlap `exp (-|x-y|/2)`. Consequently the physical unit-Riesz weight at `n ≤ X` is exactly
the squared `L²` distance between `v_(log X)` and `v_(log n)`, divided by `sqrt X`. The finite
von-Mangoldt renewal is therefore a positive coherent energy.

This lift retains off-diagonal information: increments based at one endpoint have an explicit Gram
kernel, and its two-lag determinant is strictly positive with an exact crowding factor. At integer
apertures the literal Chebyshev resolvent is exactly coherent prime energy minus the continuum
energy of the same increment frame:

`R₁(log N) = E_prime(N) - (2/3) sqrt N`.

These are unconditional source identities and source-side separation laws. They do not compare the
coherent frame with the CCM ground-state field, prove the required arithmetic bound, or prove RH.
-/

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

def unitExponentialCoherentState (x s : ℝ) : ℝ :=
  if x < s then Real.exp (-(s - x) / 2) else 0

theorem integrable_unitExponentialCoherentState_mul
    (x y : ℝ) :
    Integrable (fun s : ℝ => unitExponentialCoherentState x s *
      unitExponentialCoherentState y s) := by
  wlog hxy : x ≤ y generalizing x y
  · rw [show (fun s : ℝ => unitExponentialCoherentState x s *
        unitExponentialCoherentState y s) =
      fun s : ℝ => unitExponentialCoherentState y s *
        unitExponentialCoherentState x s by funext s; ring]
    exact this y x (le_of_not_ge hxy)
  have hfun :
      (fun s : ℝ => unitExponentialCoherentState x s *
        unitExponentialCoherentState y s) =
      (Ioi y).indicator (fun s : ℝ =>
        Real.exp ((x + y) / 2) * Real.exp (-s)) := by
    funext s
    by_cases hys : y < s
    · have hxs : x < s := lt_of_le_of_lt hxy hys
      simp [unitExponentialCoherentState, hxs, hys, Set.indicator]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    · have hnotmem : s ∉ Ioi y := hys
      simp [unitExponentialCoherentState, hys, Set.indicator, hnotmem]
  rw [hfun]
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioi
  change Integrable (fun s : ℝ =>
    Real.exp ((x + y) / 2) * Real.exp (-s)) (volume.restrict (Ioi y))
  convert (exp_neg_integrableOn_Ioi y (b := (1 : ℝ)) one_pos).const_mul
    (Real.exp ((x + y) / 2)) using 1
  ring

theorem integral_unitExponentialCoherentState_mul
    (x y : ℝ) :
    (∫ s : ℝ, unitExponentialCoherentState x s *
      unitExponentialCoherentState y s) =
        Real.exp (-|x - y| / 2) := by
  wlog hxy : x ≤ y generalizing x y
  · rw [show (fun s : ℝ => unitExponentialCoherentState x s *
        unitExponentialCoherentState y s) =
      fun s : ℝ => unitExponentialCoherentState y s *
        unitExponentialCoherentState x s by funext s; ring]
    have hyx : y ≤ x := le_of_not_ge hxy
    simpa only [abs_sub_comm] using this y x hyx
  have hfun :
      (fun s : ℝ => unitExponentialCoherentState x s *
        unitExponentialCoherentState y s) =
      (Ioi y).indicator (fun s : ℝ =>
        Real.exp ((x + y) / 2) * Real.exp (-s)) := by
    funext s
    by_cases hys : y < s
    · have hxs : x < s := lt_of_le_of_lt hxy hys
      simp [unitExponentialCoherentState, hxs, hys, Set.indicator]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    · have hnotmem : s ∉ Ioi y := hys
      simp [unitExponentialCoherentState, hys, Set.indicator, hnotmem]
  rw [hfun, integral_indicator measurableSet_Ioi, integral_const_mul]
  have hi := integral_Ioi_rexp_neg_mul_shift (b := (1 : ℝ)) (by norm_num) y
  have hi' : (∫ a in Ioi y, Real.exp (-a)) = Real.exp (-y) := by
    convert hi using 1 <;> norm_num
  rw [hi']
  have habs : |x - y| = y - x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring
  rw [habs]
  norm_num
  rw [← Real.exp_add]
  congr 1
  ring

def unitExponentialCoherentDistanceSq (x y : ℝ) : ℝ :=
  ∫ s : ℝ, (unitExponentialCoherentState x s -
    unitExponentialCoherentState y s) ^ 2

theorem unitExponentialCoherentDistanceSq_eq
    (x y : ℝ) :
    unitExponentialCoherentDistanceSq x y =
      2 * (1 - Real.exp (-|x - y| / 2)) := by
  have hxx := integrable_unitExponentialCoherentState_mul x x
  have hyy := integrable_unitExponentialCoherentState_mul y y
  have hxy := integrable_unitExponentialCoherentState_mul x y
  have hsum : Integrable (fun s : ℝ =>
      unitExponentialCoherentState x s * unitExponentialCoherentState x s +
      unitExponentialCoherentState y s * unitExponentialCoherentState y s) :=
    hxx.add hyy
  have htwoxy : Integrable (fun s : ℝ =>
      2 * (unitExponentialCoherentState x s *
        unitExponentialCoherentState y s)) := hxy.const_mul 2
  calc
    unitExponentialCoherentDistanceSq x y =
        ∫ s : ℝ,
          (unitExponentialCoherentState x s * unitExponentialCoherentState x s +
          unitExponentialCoherentState y s * unitExponentialCoherentState y s) -
          2 * (unitExponentialCoherentState x s *
            unitExponentialCoherentState y s) := by
      rw [unitExponentialCoherentDistanceSq]
      apply integral_congr_ae
      filter_upwards with s
      ring
    _ = (∫ s : ℝ, unitExponentialCoherentState x s *
          unitExponentialCoherentState x s) +
        (∫ s : ℝ, unitExponentialCoherentState y s *
          unitExponentialCoherentState y s) -
        2 * (∫ s : ℝ, unitExponentialCoherentState x s *
          unitExponentialCoherentState y s) := by
      rw [integral_sub hsum htwoxy, integral_add hxx hyy,
        integral_const_mul]
    _ = 2 * (1 - Real.exp (-|x - y| / 2)) := by
      rw [integral_unitExponentialCoherentState_mul,
        integral_unitExponentialCoherentState_mul,
        integral_unitExponentialCoherentState_mul]
      simp
      ring

def unitExponentialCoherentIncrementGram (a x y : ℝ) : ℝ :=
  ∫ s : ℝ, (unitExponentialCoherentState a s - unitExponentialCoherentState x s) *
    (unitExponentialCoherentState a s - unitExponentialCoherentState y s)

theorem unitExponentialCoherentIncrementGram_eq
    (a x y : ℝ) :
    unitExponentialCoherentIncrementGram a x y =
      1 - Real.exp (-|a - y| / 2) - Real.exp (-|x - a| / 2) +
        Real.exp (-|x - y| / 2) := by
  have haa := integrable_unitExponentialCoherentState_mul a a
  have hay := integrable_unitExponentialCoherentState_mul a y
  have hxa := integrable_unitExponentialCoherentState_mul x a
  have hxy := integrable_unitExponentialCoherentState_mul x y
  have hsum : Integrable (fun s : ℝ =>
      ((unitExponentialCoherentState a s * unitExponentialCoherentState a s -
        unitExponentialCoherentState a s * unitExponentialCoherentState y s) -
        unitExponentialCoherentState x s * unitExponentialCoherentState a s) +
        unitExponentialCoherentState x s * unitExponentialCoherentState y s) :=
    ((haa.sub hay).sub hxa).add hxy
  calc
    unitExponentialCoherentIncrementGram a x y =
        ∫ s : ℝ,
          ((unitExponentialCoherentState a s * unitExponentialCoherentState a s -
            unitExponentialCoherentState a s * unitExponentialCoherentState y s) -
            unitExponentialCoherentState x s * unitExponentialCoherentState a s) +
            unitExponentialCoherentState x s * unitExponentialCoherentState y s := by
      rw [unitExponentialCoherentIncrementGram]
      apply integral_congr_ae
      filter_upwards with s
      ring
    _ = (∫ s : ℝ, unitExponentialCoherentState a s * unitExponentialCoherentState a s) -
        (∫ s : ℝ, unitExponentialCoherentState a s * unitExponentialCoherentState y s) -
        (∫ s : ℝ, unitExponentialCoherentState x s * unitExponentialCoherentState a s) +
        ∫ s : ℝ, unitExponentialCoherentState x s * unitExponentialCoherentState y s := by
      calc
        (∫ s : ℝ,
            ((unitExponentialCoherentState a s * unitExponentialCoherentState a s -
              unitExponentialCoherentState a s * unitExponentialCoherentState y s) -
              unitExponentialCoherentState x s * unitExponentialCoherentState a s) +
              unitExponentialCoherentState x s * unitExponentialCoherentState y s) =
          (∫ s : ℝ,
            (unitExponentialCoherentState a s * unitExponentialCoherentState a s -
              unitExponentialCoherentState a s * unitExponentialCoherentState y s) -
              unitExponentialCoherentState x s * unitExponentialCoherentState a s) +
            ∫ s : ℝ, unitExponentialCoherentState x s *
              unitExponentialCoherentState y s :=
            integral_add ((haa.sub hay).sub hxa) hxy
        _ = ((∫ s : ℝ,
              unitExponentialCoherentState a s * unitExponentialCoherentState a s -
                unitExponentialCoherentState a s * unitExponentialCoherentState y s) -
              ∫ s : ℝ, unitExponentialCoherentState x s *
                unitExponentialCoherentState a s) +
            ∫ s : ℝ, unitExponentialCoherentState x s *
              unitExponentialCoherentState y s := by
            congr 1
            exact integral_sub (haa.sub hay) hxa
        _ = _ := by
          congr 2
          exact integral_sub haa hay
    _ = _ := by
      rw [integral_unitExponentialCoherentState_mul,
        integral_unitExponentialCoherentState_mul,
        integral_unitExponentialCoherentState_mul,
        integral_unitExponentialCoherentState_mul]
      simp

def unitExponentialIncrementKernel (u v : ℝ) : ℝ :=
  1 - Real.exp (-u / 2) - Real.exp (-v / 2) +
    Real.exp (-|u - v| / 2)

theorem unitExponentialIncrementKernel_eq_gram
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    unitExponentialIncrementKernel u v =
      unitExponentialCoherentIncrementGram 0 (-u) (-v) := by
  rw [unitExponentialCoherentIncrementGram_eq]
  simp only [unitExponentialIncrementKernel, sub_neg_eq_add, zero_add]
  have habsv : |v| = v := abs_of_nonneg hv
  have habsu : |-u - 0| = u := by rw [sub_zero, abs_neg, abs_of_nonneg hu]
  have habsuv : |-u + v| = |u - v| := by
    rw [show -u + v = -(u - v) by ring, abs_neg]
  rw [habsv, habsu, habsuv]
  ring

theorem unitExponentialIncrementKernel_twoByTwoDet_eq
    {u v : ℝ} (huv : u ≤ v) :
    unitExponentialIncrementKernel u u * unitExponentialIncrementKernel v v -
        unitExponentialIncrementKernel u v ^ 2 =
      (1 - Real.exp (-u / 2)) *
        (1 - Real.exp (-(v - u) / 2)) *
          (3 + Real.exp (-(v - u) / 2) +
            Real.exp (-u / 2) * (1 - Real.exp (-(v - u) / 2))) := by
  have habs : |u - v| = v - u := by
    rw [abs_of_nonpos (sub_nonpos.mpr huv)]
    ring
  have hvsplit :
      Real.exp (-v / 2) =
        Real.exp (-u / 2) * Real.exp (-(v - u) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [unitExponentialIncrementKernel, sub_self, abs_zero, neg_zero, zero_div,
    Real.exp_zero, habs, hvsplit]
  ring

theorem unitExponentialIncrementKernel_twoByTwoDet_pos
    {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    0 < unitExponentialIncrementKernel u u * unitExponentialIncrementKernel v v -
      unitExponentialIncrementKernel u v ^ 2 := by
  rw [unitExponentialIncrementKernel_twoByTwoDet_eq huv.le]
  have hau : Real.exp (-u / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have huvexp : Real.exp (-(v - u) / 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hthird : 0 < 3 + Real.exp (-(v - u) / 2) +
      Real.exp (-u / 2) * (1 - Real.exp (-(v - u) / 2)) := by
    have hnonneg : 0 ≤ Real.exp (-u / 2) *
        (1 - Real.exp (-(v - u) / 2)) :=
      mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr huvexp.le)
    linarith [Real.exp_pos (-(v - u) / 2)]
  exact mul_pos (mul_pos (sub_pos.mpr hau) (sub_pos.mpr huvexp)) hthird

theorem unitApertureCriticalPrimeWeight_eq_coherentDistance
    {X n : ℝ} (hX : 0 < X) (hn : 0 < n) (hnX : n ≤ X) :
    unitApertureCriticalPrimeWeight X n =
      unitExponentialCoherentDistanceSq (Real.log X) (Real.log n) /
        Real.sqrt X := by
  have hlog : Real.log n ≤ Real.log X := Real.strictMonoOn_log.monotoneOn hn hX hnX
  have habs : |Real.log X - Real.log n| = Real.log X - Real.log n :=
    abs_of_nonneg (sub_nonneg.mpr hlog)
  have hratio : 0 < n / X := div_pos hn hX
  have hexp :
      Real.exp (-(Real.log X - Real.log n) / 2) = Real.sqrt (n / X) := by
    rw [show -(Real.log X - Real.log n) = Real.log (n / X) by
      rw [Real.log_div hn.ne' hX.ne']; ring]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hratio]
    congr 1
    ring
  rw [unitApertureCriticalPrimeWeight_eq_riesz hX hn,
    unitExponentialCoherentDistanceSq_eq, habs, hexp]
  ring

def unitRieszCoherentPrimeEnergy (X : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    ArithmeticFunction.vonMangoldt k *
      (unitExponentialCoherentDistanceSq (Real.log X) (Real.log k) /
        Real.sqrt X)

theorem unitRieszVonMangoldtRenewal_eq_coherentPrimeEnergy
    {X : ℝ} {K : ℕ} (hX : 0 < X) (hKX : (K : ℝ) ≤ X) :
    unitRieszVonMangoldtRenewal X K = unitRieszCoherentPrimeEnergy X K := by
  simp only [unitRieszVonMangoldtRenewal, unitRieszCoherentPrimeEnergy]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk' : k ∈ Finset.Icc 2 K := hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk').1
  have hkK : k ≤ K := (Finset.mem_Icc.mp hk').2
  rw [unitApertureCriticalPrimeWeight_eq_coherentDistance hX
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2))
    (le_trans (by exact_mod_cast hkK) hKX)]

theorem chebyshevPsi_scaled_eq_vonMangoldt_indicator
    {N : ℕ} (hN : 1 ≤ N) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Chebyshev.psi ((N : ℝ) * v) =
      ∑ k ∈ Finset.Icc 0 N,
        if (k : ℝ) / N ≤ v then ArithmeticFunction.vonMangoldt k else 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNv0 : (0 : ℝ) ≤ (N : ℝ) * v := mul_nonneg hNR.le hv0
  have hfilter :
      (Finset.Icc 0 N).filter (fun k : ℕ => (k : ℝ) / N ≤ v) =
        Finset.Icc 0 ⌊(N : ℝ) * v⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk0, hkN⟩, hkv⟩
      have hkle : (k : ℝ) ≤ (N : ℝ) * v := by
        rw [div_le_iff₀ hNR] at hkv
        nlinarith
      exact ⟨hk0, Nat.le_floor hkle⟩
    · rintro ⟨hk0, hkfloor⟩
      have hkcast : (k : ℝ) ≤ (⌊(N : ℝ) * v⌋₊ : ℝ) := by exact_mod_cast hkfloor
      have hkNv : (k : ℝ) ≤ (N : ℝ) * v :=
        hkcast.trans (Nat.floor_le hNv0)
      have hfloorN : ⌊(N : ℝ) * v⌋₊ ≤ N := by
        have hmono : ⌊(N : ℝ) * v⌋₊ ≤ ⌊(N : ℝ)⌋₊ :=
          Nat.floor_le_floor (by nlinarith)
        simpa using hmono
      exact ⟨⟨hk0, hkfloor.trans hfloorN⟩,
        (div_le_iff₀ hNR).2 (by nlinarith)⟩
  rw [Chebyshev.psi_eq_sum_Icc, ← hfilter, Finset.sum_filter]

theorem integral_scaledChebyshevPsi_layerWeight
    {N : ℕ} (hN : 1 ≤ N) :
    (∫ v in (0 : ℝ)..1,
        Chebyshev.psi ((N : ℝ) * v) * layerWeight v) =
      ∑ k ∈ Finset.Icc 0 N,
        ArithmeticFunction.vonMangoldt k *
          (1 - Real.sqrt ((k : ℝ) / N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hcongr :
      (∫ v in (0 : ℝ)..1,
          Chebyshev.psi ((N : ℝ) * v) * layerWeight v) =
        ∫ v in (0 : ℝ)..1, ∑ k ∈ Finset.Icc 0 N,
          ArithmeticFunction.vonMangoldt k *
            (if (k : ℝ) / N ≤ v then layerWeight v else 0) := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv0 : 0 ≤ v := by
      rcases Set.mem_uIcc.1 hv with h | h
      · exact h.1
      · linarith [h.2]
    have hv1 : v ≤ 1 := by
      rcases Set.mem_uIcc.1 hv with h | h
      · exact h.2
      · linarith [h.1]
    change Chebyshev.psi ((N : ℝ) * v) * layerWeight v =
      ∑ k ∈ Finset.Icc 0 N,
        ArithmeticFunction.vonMangoldt k *
          (if (k : ℝ) / N ≤ v then layerWeight v else 0)
    rw [chebyshevPsi_scaled_eq_vonMangoldt_indicator hN hv0 hv1,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hkv : (k : ℝ) / N ≤ v
    · rw [if_pos hkv, if_pos hkv]
    · rw [if_neg hkv, if_neg hkv]
      ring
  rw [hcongr, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul]
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk0)
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      have hratio : (0 : ℝ) < (k : ℝ) / N := div_pos hkpos hNR
      have hratioOne : (k : ℝ) / N ≤ 1 := (div_le_one hNR).2 (by exact_mod_cast hkN)
      rw [integral_indicatorLayer hratio hratioOne]
  · intro k _hk
    exact (intervalIntegrable_indicatorLayer ((k : ℝ) / N)).const_mul _

theorem intervalIntegrable_scaledChebyshevPsi_layerWeight
    {N : ℕ} (hN : 1 ≤ N) :
    IntervalIntegrable
      (fun v : ℝ => Chebyshev.psi ((N : ℝ) * v) * layerWeight v)
      volume 0 1 := by
  have hsum : IntervalIntegrable
      (fun v : ℝ => ∑ k ∈ Finset.Icc 0 N,
        ArithmeticFunction.vonMangoldt k *
          (if (k : ℝ) / N ≤ v then layerWeight v else 0))
      volume 0 1 := by
    have h := IntervalIntegrable.sum (Finset.Icc 0 N)
      (f := fun k : ℕ => fun v : ℝ => ArithmeticFunction.vonMangoldt k *
        (if (k : ℝ) / N ≤ v then layerWeight v else 0))
      (fun k _hk => (intervalIntegrable_indicatorLayer ((k : ℝ) / N)).const_mul _)
    have hfun :
        (∑ k ∈ Finset.Icc 0 N, fun v : ℝ => ArithmeticFunction.vonMangoldt k *
          (if (k : ℝ) / N ≤ v then layerWeight v else 0)) =
        fun v : ℝ => ∑ k ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt k *
          (if (k : ℝ) / N ≤ v then layerWeight v else 0) := by
      funext v
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  refine hsum.congr fun v hv => ?_
  have hv0 : 0 ≤ v := le_of_lt (by simpa using hv.1)
  have hv1 : v ≤ 1 := by simpa using hv.2
  rw [chebyshevPsi_scaled_eq_vonMangoldt_indicator hN hv0 hv1,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hkv : (k : ℝ) / N ≤ v
  · rw [if_pos hkv, if_pos hkv]
  · rw [if_neg hkv, if_neg hkv]
    ring

theorem unitRieszVonMangoldtRenewal_eq_scaledPsiLayerEnergy
    {N : ℕ} (hN : 1 ≤ N) :
    unitRieszVonMangoldtRenewal (N : ℝ) N =
      2 / Real.sqrt N *
        ∫ v in (0 : ℝ)..1,
          Chebyshev.psi ((N : ℝ) * v) * layerWeight v := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  let f : ℕ → ℝ := fun k => ArithmeticFunction.vonMangoldt k *
    (1 - Real.sqrt ((k : ℝ) / N))
  have hsubset : Finset.Icc 2 N ⊆ Finset.Icc 0 N := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le k, (Finset.mem_Icc.mp hk).2⟩
  have hsum : (∑ k ∈ Finset.Icc 0 N, f k) = ∑ k ∈ Finset.Icc 2 N, f k := by
    symm
    apply Finset.sum_subset hsubset
    intro k hk hnot
    have hklt : k < 2 := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨Nat.le_of_not_gt h, (Finset.mem_Icc.mp hk).2⟩)
    interval_cases k <;> simp [f]
  rw [integral_scaledChebyshevPsi_layerWeight hN]
  change unitRieszVonMangoldtRenewal (N : ℝ) N =
    2 / Real.sqrt N * ∑ k ∈ Finset.Icc 0 N, f k
  rw [hsum, Finset.mul_sum]
  rw [unitRieszVonMangoldtRenewal]
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2)
  rw [unitApertureCriticalPrimeWeight_eq_riesz hNR hkpos]
  dsimp only [f]
  ring

theorem integral_chebyshevPsi_halfWeight_eq_scaledLayerEnergy
    {N : ℕ} (hN : 1 ≤ N) :
    (∫ y in (0 : ℝ)..N,
        Chebyshev.psi y * y ^ (-(1 / 2 : ℝ))) =
      2 * Real.sqrt N *
        ∫ v in (0 : ℝ)..1,
          Chebyshev.psi ((N : ℝ) * v) * layerWeight v := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  let f : ℝ → ℝ := fun v => (N : ℝ) * v
  let f' : ℝ → ℝ := fun _v => (N : ℝ)
  let G : ℝ → ℝ := fun y => Chebyshev.psi y * y ^ (-(1 / 2 : ℝ))
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := (1 : ℝ)) (f := f) (f' := f') (g := G)
    (by fun_prop)
    (fun v _hv => by
      dsimp only [f, f']
      simpa using (hasDerivAt_id v).const_mul (N : ℝ))
    (fun _v _hv => hNR.le)
  have hleft :
      (∫ v in (0 : ℝ)..1, (G ∘ f) v * f' v) =
        2 * Real.sqrt N *
          ∫ v in (0 : ℝ)..1,
            Chebyshev.psi ((N : ℝ) * v) * layerWeight v := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    have hv0 : 0 ≤ v := by
      rcases Set.mem_uIcc.1 hv with h | h
      · exact h.1
      · linarith [h.2]
    change Chebyshev.psi ((N : ℝ) * v) *
        ((N : ℝ) * v) ^ (-(1 / 2 : ℝ)) * (N : ℝ) =
      2 * Real.sqrt N *
        (Chebyshev.psi ((N : ℝ) * v) * layerWeight v)
    rw [Real.mul_rpow hNR.le hv0, layerWeight_eq_rpow hv0]
    have hscale :
        (N : ℝ) ^ (-(1 / 2 : ℝ)) * N = Real.sqrt N := by
      nth_rewrite 2 [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hNR]
      rw [Real.sqrt_eq_rpow]
      congr 1
      ring
    calc
      Chebyshev.psi ((N : ℝ) * v) *
          ((N : ℝ) ^ (-(1 / 2 : ℝ)) * v ^ (-(1 / 2 : ℝ))) * (N : ℝ) =
        Chebyshev.psi ((N : ℝ) * v) * v ^ (-(1 / 2 : ℝ)) *
          ((N : ℝ) ^ (-(1 / 2 : ℝ)) * N) := by ring
      _ = _ := by rw [hscale]; ring
  rw [hleft] at hsub
  convert hsub.symm using 1
  all_goals norm_num [f, G]

theorem criticalMellinChebyshevResolventSource_log_nat_eq_coherentDefect
    {N : ℕ} (hN : 1 ≤ N) :
    criticalMellinChebyshevResolventSource (Real.log N) =
      unitRieszCoherentPrimeEnergy (N : ℝ) N -
        (2 / 3) * Real.sqrt N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hsqrtN : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNR).ne'
  have hsqrtSq : Real.sqrt (N : ℝ) * Real.sqrt N = N :=
    Real.mul_self_sqrt hNR.le
  let f : ℝ → ℝ := fun v => (N : ℝ) * v
  let f' : ℝ → ℝ := fun _v => (N : ℝ)
  let G : ℝ → ℝ := fun y =>
    (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := (1 : ℝ)) (f := f) (f' := f') (g := G)
    (by fun_prop)
    (fun v _hv => by
      dsimp only [f, f']
      simpa using (hasDerivAt_id v).const_mul (N : ℝ))
    (fun _v _hv => hNR.le)
  have hleft :
      (∫ v in (0 : ℝ)..1, (G ∘ f) v * f' v) =
        2 * Real.sqrt N *
          ∫ v in (0 : ℝ)..1,
            (Chebyshev.psi ((N : ℝ) * v) - (N : ℝ) * v) *
              layerWeight v := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    have hv0 : 0 ≤ v := by
      rcases Set.mem_uIcc.1 hv with h | h
      · exact h.1
      · linarith [h.2]
    change (Chebyshev.psi ((N : ℝ) * v) - (N : ℝ) * v) *
        ((N : ℝ) * v) ^ (-(1 / 2 : ℝ)) * (N : ℝ) =
      2 * Real.sqrt N *
        ((Chebyshev.psi ((N : ℝ) * v) - (N : ℝ) * v) * layerWeight v)
    rw [Real.mul_rpow hNR.le hv0, layerWeight_eq_rpow hv0]
    have hscale :
        (N : ℝ) ^ (-(1 / 2 : ℝ)) * N = Real.sqrt N := by
      nth_rewrite 2 [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hNR, Real.sqrt_eq_rpow]
      congr 1
      ring
    calc
      (Chebyshev.psi ((N : ℝ) * v) - (N : ℝ) * v) *
          ((N : ℝ) ^ (-(1 / 2 : ℝ)) * v ^ (-(1 / 2 : ℝ))) * (N : ℝ) =
        (Chebyshev.psi ((N : ℝ) * v) - (N : ℝ) * v) *
          v ^ (-(1 / 2 : ℝ)) *
            ((N : ℝ) ^ (-(1 / 2 : ℝ)) * N) := by ring
      _ = _ := by rw [hscale]; ring
  rw [hleft] at hsub
  have hsub' :
      (∫ y in (0 : ℝ)..N,
          (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))) =
        2 * Real.sqrt N *
          ∫ v in (0 : ℝ)..1,
            (Chebyshev.psi ((N : ℝ) * v) - (N : ℝ) * v) *
              layerWeight v := by
    convert hsub.symm using 1
    all_goals norm_num [f, G]
  have hsplit :
      (∫ v in (0 : ℝ)..1,
          (Chebyshev.psi ((N : ℝ) * v) - (N : ℝ) * v) * layerWeight v) =
        (∫ v in (0 : ℝ)..1,
          Chebyshev.psi ((N : ℝ) * v) * layerWeight v) -
        ∫ v in (0 : ℝ)..1, (N : ℝ) * v * layerWeight v := by
    rw [← intervalIntegral.integral_sub
      (intervalIntegrable_scaledChebyshevPsi_layerWeight hN)
      (intervalIntegrable_polar (N : ℝ))]
    apply intervalIntegral.integral_congr
    intro v _hv
    ring
  have hsource := criticalMellinChebyshevResolventSource_log_eq hNR
  have hrenewal := unitRieszVonMangoldtRenewal_eq_scaledPsiLayerEnergy hN
  have hcoherent := unitRieszVonMangoldtRenewal_eq_coherentPrimeEnergy
    hNR (le_refl (N : ℝ))
  rw [hsub', hsplit, integral_polar_layerWeight] at hsource
  rw [← hcoherent, hrenewal]
  rw [hsource]
  have hsqrtPow : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hNR.le
  field_simp [hsqrtN, hNR.ne']
  rw [hsqrtPow]

def unitRieszCoherentPolarEnergy (X : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..X,
    unitExponentialCoherentDistanceSq (Real.log X) (Real.log y) /
      Real.sqrt X

theorem unitRieszCoherentPolarEnergy_eq
    {X : ℝ} (hX : 0 < X) :
    unitRieszCoherentPolarEnergy X = (2 / 3) * Real.sqrt X := by
  have hsqrtX : Real.sqrt X ≠ 0 := (Real.sqrt_pos.2 hX).ne'
  have hsqrtPow : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX.le
  let f : ℝ → ℝ := fun v => X * v
  let f' : ℝ → ℝ := fun _v => X
  let G : ℝ → ℝ := fun y =>
    unitExponentialCoherentDistanceSq (Real.log X) (Real.log y) /
      Real.sqrt X
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := (1 : ℝ)) (f := f) (f' := f') (g := G)
    (by fun_prop)
    (fun v _hv => by
      dsimp only [f, f']
      simpa using (hasDerivAt_id v).const_mul X)
    (fun _v _hv => hX.le)
  have hleft :
      (∫ v in (0 : ℝ)..1, (G ∘ f) v * f' v) =
        2 * Real.sqrt X * ∫ v in (0 : ℝ)..1, (1 - Real.sqrt v) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    have hnull : volume ({0} : Set ℝ) = 0 := Real.volume_singleton
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with v hv hmem
    have hv' : v ∈ Set.uIoc (0 : ℝ) 1 := hmem
    rw [Set.uIoc_of_le zero_le_one] at hv'
    have hvpos : 0 < v := hv'.1
    have hvone : v ≤ 1 := hv'.2
    have hXv : 0 < X * v := mul_pos hX hvpos
    have hXvX : X * v ≤ X := by nlinarith
    change unitExponentialCoherentDistanceSq (Real.log X) (Real.log (X * v)) /
        Real.sqrt X * X = 2 * Real.sqrt X * (1 - Real.sqrt v)
    rw [← unitApertureCriticalPrimeWeight_eq_coherentDistance hX hXv hXvX,
      unitApertureCriticalPrimeWeight_eq_riesz hX hXv]
    rw [show X * v / X = v by field_simp [hX.ne']]
    field_simp [hsqrtX, hX.ne']
    rw [hsqrtPow]
    ring
  have hsqrtInt : (∫ v in (0 : ℝ)..1, Real.sqrt v) = 2 / 3 := by
    have hfun : (fun v : ℝ => Real.sqrt v) = fun v : ℝ => v ^ (1 / 2 : ℝ) := by
      funext v
      rw [Real.sqrt_eq_rpow]
    rw [hfun, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
    norm_num
  have honeMinus : (∫ v in (0 : ℝ)..1, (1 - Real.sqrt v)) = 1 / 3 := by
    rw [intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable 0 1)
      (Real.continuous_sqrt.intervalIntegrable 0 1),
      intervalIntegral.integral_const, hsqrtInt]
    norm_num
  rw [hleft, honeMinus] at hsub
  change unitRieszCoherentPolarEnergy X = _
  rw [unitRieszCoherentPolarEnergy]
  convert hsub.symm using 1
  all_goals norm_num [f, G]
  all_goals ring

theorem criticalMellinChebyshevResolventSource_log_nat_eq_coherentPrime_sub_polar
    {N : ℕ} (hN : 1 ≤ N) :
    criticalMellinChebyshevResolventSource (Real.log N) =
      unitRieszCoherentPrimeEnergy (N : ℝ) N -
        unitRieszCoherentPolarEnergy N := by
  rw [criticalMellinChebyshevResolventSource_log_nat_eq_coherentDefect hN,
    unitRieszCoherentPolarEnergy_eq
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN) : (0 : ℝ) < N)]


end GaloisForLFunctions.RHTower
