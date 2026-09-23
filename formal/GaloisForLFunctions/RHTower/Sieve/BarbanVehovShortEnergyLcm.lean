import GaloisForLFunctions.RHTower.Sieve.BarbanVehovShortWindowKernels
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorEnergy

/-!
# The short-range mollified detector energy as an lcm quadratic form

Below the detector head length the mollified critical detector coefficient is the *unrestricted*
divisor sum `∑_{d ∣ k} w_d (1 - λ log (k/d))`, `w_d` the linear Barban--Vehov weight.  Squaring and
exchanging the order of summation turns the harmonic energy `∑_{k ≤ X} |c_k|²` into a quadratic form
in the three lcm kernels of the window `(0, X]`.

This is the exact counterpart of the long-range included lcm expansion, and it is exact: no error
term appears here, only a change in the order of summation.
-/

open Finset

noncomputable section

namespace RHTower.Sieve

/-- Divisor-pair exchange on a window reaching the origin. -/
theorem sum_Ioc_zeroStart_divisorPair_eq_lcmKernel
    {R : Type*} [AddCommMonoid R] {U : ℕ} (F : ℕ → ℕ × ℕ → R) :
    (∑ k ∈ Finset.Ioc 0 U, ∑ p ∈ k.divisors ×ˢ k.divisors, F k p) =
      ∑ p ∈ (Finset.Icc 1 U) ×ˢ (Finset.Icc 1 U),
        ∑ k ∈ (Finset.Ioc 0 U).filter (fun k => Nat.lcm p.1 p.2 ∣ k), F k p := by
  classical
  have hmem : ∀ (k : ℕ) (p : ℕ × ℕ),
      k ∈ Finset.Ioc 0 U ∧ p ∈ k.divisors ×ˢ k.divisors ↔
        k ∈ (Finset.Ioc 0 U).filter (fun k => Nat.lcm p.1 p.2 ∣ k) ∧
          p ∈ (Finset.Icc 1 U) ×ˢ (Finset.Icc 1 U) := by
    intro k p
    constructor
    · rintro ⟨hk, hp⟩
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have hkpos : 0 < k := (Finset.mem_Ioc.mp hk).1
      have hd1 : p.1 ∣ k := Nat.dvd_of_mem_divisors hp1
      have hd2 : p.2 ∣ k := Nat.dvd_of_mem_divisors hp2
      refine ⟨Finset.mem_filter.mpr ⟨hk, Nat.lcm_dvd hd1 hd2⟩,
        Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hp1,
          (Nat.le_of_dvd hkpos hd1).trans (Finset.mem_Ioc.mp hk).2⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hp2,
          (Nat.le_of_dvd hkpos hd2).trans (Finset.mem_Ioc.mp hk).2⟩
    · rintro ⟨hkf, hp⟩
      obtain ⟨hk, hlcm⟩ := Finset.mem_filter.mp hkf
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have hk0 : k ≠ 0 := (Finset.mem_Ioc.mp hk).1.ne'
      refine ⟨hk, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Nat.mem_divisors.mpr ⟨(Nat.dvd_lcm_left _ _).trans hlcm, hk0⟩
      · exact Nat.mem_divisors.mpr ⟨(Nat.dvd_lcm_right _ _).trans hlcm, hk0⟩
  exact Finset.sum_comm' hmem

/-- The differentiated detector bracket is the unrestricted weighted divisor sum. -/
theorem levinsonDetectorBracket_eq_divisorSum (lam : ℝ) (M : ℕ) {k : ℕ} (hk : 0 < k) :
    (1 - lam * Real.log k) * barbanVehovCoeff M k + lam * barbanVehovLogMomentCoeff M k =
      ∑ d ∈ k.divisors, barbanVehovWeight M d *
        (1 - lam * Real.log (((k / d : ℕ) : ℝ))) := by
  rw [barbanVehovCoeff, barbanVehovLogMomentCoeff, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [log_natDiv_eq_sub_log_of_dvd hk (Nat.dvd_of_mem_divisors hd)]
  ring

/-- Splitting a quadratic combination of four pointwise families under one sum. -/
private theorem sum_pointwise_quad_combination {ι : Type*} (S : Finset ι) (lam : ℝ)
    (c f0 f1 f2 f3 : ι → ℝ) :
    (∑ i ∈ S, c i * (f0 i - lam * (f1 i + f2 i) + lam ^ (2 : ℕ) * f3 i)) =
      (∑ i ∈ S, c i * f0 i) - lam * ((∑ i ∈ S, c i * f1 i) + (∑ i ∈ S, c i * f2 i)) +
        lam ^ (2 : ℕ) * (∑ i ∈ S, c i * f3 i) := by
  have h : ∀ i, c i * (f0 i - lam * (f1 i + f2 i) + lam ^ (2 : ℕ) * f3 i)
      = c i * f0 i - (lam * (c i * f1 i) + lam * (c i * f2 i)) + lam ^ (2 : ℕ) * (c i * f3 i) :=
    fun i => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Base lcm form of the short-range energy. -/
def barbanVehovShortBaseLcm (X M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongHarmonicKernel 0 X p.1 p.2

/-- Cross lcm form of the short-range energy. -/
def barbanVehovShortCrossLcm (X M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      (-(barbanVehovLongFirstLogKernel 0 X p.1 p.2))

/-- Differentiated-square lcm form of the short-range energy. -/
def barbanVehovShortDerivativeLcm (X M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovLongSecondLogKernel 0 X p.1 p.2

/-- The short-range mollified detector energy in lcm form. -/
def barbanVehovShortEnergyLcm (lam : ℝ) (X M : ℕ) : ℝ :=
  (barbanVehovShortBaseLcm X M + 2 * lam * barbanVehovShortCrossLcm X M +
      lam ^ (2 : ℕ) * barbanVehovShortDerivativeLcm X M) /
    Real.log M ^ (2 : ℕ)

/-- The two orientations of the first log kernel have the same weighted lcm form. -/
theorem sum_barbanVehovWeight_firstLogKernel_swap (X M : ℕ) :
    (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
          barbanVehovLongFirstLogKernel 0 X p.2 p.1) =
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
          barbanVehovLongFirstLogKernel 0 X p.1 p.2 := by
  classical
  rw [Finset.sum_product, Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro q _
  refine Finset.sum_congr rfl ?_
  intro r _
  ring

/-- **The short-range mollified detector energy is exactly its lcm quadratic form.** -/
theorem sum_norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq_eq_shortEnergyLcm
    (lam : ℝ) {X M : ℕ} (hM : 1 < M) (hMX : M ≤ X) :
    (∑ k ∈ Finset.Icc 1 X,
        ‖levinsonLinearMollifiedCriticalDetectorCoeff lam M k‖ ^ (2 : ℕ)) =
      barbanVehovShortEnergyLcm lam X M := by
  classical
  rw [sum_norm_levinsonLinearMollifiedCriticalDetectorCoeff_sq lam (M := M) (N := X) hM,
    barbanVehovShortEnergyLcm]
  congr 1
  have hIcc : Finset.Icc 1 X = Finset.Ioc 0 X := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc]
  have hexpand : ∀ k ∈ Finset.Ioc 0 X,
      ((1 - lam * Real.log k) * barbanVehovCoeff M k +
          lam * barbanVehovLogMomentCoeff M k) ^ (2 : ℕ) / (k : ℝ) =
        ∑ p ∈ k.divisors ×ˢ k.divisors,
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            ((1 - lam * Real.log (((k / p.1 : ℕ) : ℝ))) *
              (1 - lam * Real.log (((k / p.2 : ℕ) : ℝ)))) / (k : ℝ) := by
    intro k hk
    have hkpos : 0 < k := (Finset.mem_Ioc.mp hk).1
    rw [levinsonDetectorBracket_eq_divisorSum lam M hkpos, sq, Finset.sum_mul_sum,
      Finset.sum_product, Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro r _
    ring
  rw [Finset.sum_congr rfl hexpand]
  rw [sum_Ioc_zeroStart_divisorPair_eq_lcmKernel]
  have hinner : ∀ p ∈ (Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X),
      (∑ k ∈ (Finset.Ioc 0 X).filter (fun k => Nat.lcm p.1 p.2 ∣ k),
          barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
            ((1 - lam * Real.log (((k / p.1 : ℕ) : ℝ))) *
              (1 - lam * Real.log (((k / p.2 : ℕ) : ℝ)))) / (k : ℝ)) =
        barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
          (barbanVehovLongHarmonicKernel 0 X p.1 p.2 -
              lam * (barbanVehovLongFirstLogKernel 0 X p.2 p.1 +
                barbanVehovLongFirstLogKernel 0 X p.1 p.2) +
            lam ^ (2 : ℕ) * barbanVehovLongSecondLogKernel 0 X p.1 p.2) := by
    intro p _
    have hT : (Finset.Ioc 0 X).filter (fun k => Nat.lcm p.2 p.1 ∣ k)
        = (Finset.Ioc 0 X).filter (fun k => Nat.lcm p.1 p.2 ∣ k) := by
      rw [Nat.lcm_comm]
    have hcongr : ∀ k ∈ (Finset.Ioc 0 X).filter (fun k => Nat.lcm p.1 p.2 ∣ k),
        barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
              ((1 - lam * Real.log (((k / p.1 : ℕ) : ℝ))) *
                (1 - lam * Real.log (((k / p.2 : ℕ) : ℝ)))) / (k : ℝ)
          = (barbanVehovWeight M p.1 * barbanVehovWeight M p.2) *
            ((1 : ℝ) / (k : ℝ) -
                lam * (Real.log (((k / p.1 : ℕ) : ℝ)) / (k : ℝ) +
                  Real.log (((k / p.2 : ℕ) : ℝ)) / (k : ℝ)) +
              lam ^ (2 : ℕ) * (Real.log (((k / p.1 : ℕ) : ℝ)) *
                Real.log (((k / p.2 : ℕ) : ℝ)) / (k : ℝ))) := by
      intro k _
      ring
    rw [Finset.sum_congr rfl hcongr, sum_pointwise_quad_combination]
    rw [barbanVehovLongHarmonicKernel, barbanVehovLongSecondLogKernel,
      barbanVehovLongFirstLogKernel, barbanVehovLongFirstLogKernel, hT]
    simp only [← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl hinner]
  rw [sum_barbanVehovWeight_pair_support hMX
    (fun p => barbanVehovLongHarmonicKernel 0 X p.1 p.2 -
        lam * (barbanVehovLongFirstLogKernel 0 X p.2 p.1 +
          barbanVehovLongFirstLogKernel 0 X p.1 p.2) +
      lam ^ (2 : ℕ) * barbanVehovLongSecondLogKernel 0 X p.1 p.2)]
  rw [sum_pointwise_quad_combination]
  rw [barbanVehovShortBaseLcm, barbanVehovShortCrossLcm, barbanVehovShortDerivativeLcm]
  have hswap := sum_barbanVehovWeight_firstLogKernel_swap X M
  have hneg : (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
        (-(barbanVehovLongFirstLogKernel 0 X p.1 p.2))) =
      -(∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
          barbanVehovLongFirstLogKernel 0 X p.1 p.2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  rw [hneg, hswap]
  ring

end RHTower.Sieve

end
