import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadder
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCofactorHM
import GaloisForLFunctions.RHTower.Sieve.SetIntegralBlockSplit

/-!
# Menon's harmonic Ramare ladder on measurable frequency sets

The harmonic geometric block replacement is restricted to a measurable frequency set, then the
prime factor is paid pointwise and the harmonic cofactor by reciprocal Halasz--Montgomery.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- One harmonic geometric block on a measurable part of the frequency window. -/
theorem setIntegral_normSq_harmonicRamareBlock_geom_le
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (j : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) /
      ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E,
      ‖harmonicRamareBlock P (Finset.Icc A₀ B₀)
        (geomBlock P Q (1 + eta) j) w‖ ^ (2 : ℕ))
      ≤ 2 * (∫ w in E,
          ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
            logPoly (harmonicRamareCofactorCoeff P)
              (harmonicGeomCofactorBlock A₀ B₀ Q eta j) w‖ ^ (2 : ℕ))
        + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) ^ (2 : ℕ) *
            harmonicCofactorSupportError A₀ B₀ Q eta W j := by
  classical
  let B : Finset ℕ := geomBlock P Q (1 + eta) j
  let Qj : ℝ := Q * (1 + eta) ^ j
  let C : Finset ℕ := harmonicGeomCofactorBlock A₀ B₀ Q eta j
  let R : ℝ := harmonicCofactorSupportError A₀ B₀ Q eta W j
  have hBprime : ∀ p ∈ B, p.Prime := by
    intro p hp
    exact hPprime p (geomBlock_subset P Q (1 + eta) j hp)
  have hQj : 0 < Qj := by
    dsimp only [Qj]
    have : 0 < 1 + eta := by linarith
    positivity
  have hdisc : ∀ p ∈ B,
      (∫ w in E,
        ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
          logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ)) ≤ R := by
    intro p hp
    have hpB := Finset.mem_filter.1 hp
    have hp0 := (hBprime p hp).pos
    have hphi : (p : ℝ) ≤ Qj * (1 + eta) := by
      calc
        (p : ℝ) ≤ Q * (1 + eta) ^ (j + 1) := hpB.2.2
        _ = Qj * (1 + eta) := by rw [pow_succ]; dsimp only [Qj]; ring
    have hfull := integral_Icc_normSq_harmonicRamareCofactor_sub_common_le
      (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Qj) (eta := eta) (W := W) (p := p)
      hA₀ hQj heta hW hp0 hpB.2.1 hphi hleft
    have hcont : Continuous fun w : ℝ =>
        ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
          logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ) :=
      (((continuous_harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p).sub
        (continuous_logPoly _ _)).norm).pow 2
    have hmono :
        (∫ w in E,
          ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
            logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ))
          ≤ ∫ w in Set.Icc (-W) W,
            ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
              logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ) := by
      refine MeasureTheory.setIntegral_mono_set
        (hcont.integrableOn_Icc (a := -W) (b := W))
        (Filter.Eventually.of_forall fun _ => by positivity)
        (Filter.Eventually.of_forall hEs)
    exact hmono.trans (by
      simpa [Qj, C, R, harmonicGeomCofactorBlock, harmonicCofactorSupportError] using hfull)
  have hsum :
      (∑ p ∈ B, (1 / (p : ℝ)) *
        (∫ w in E,
          ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
            logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ)))
        ≤ harmonicPrimeMass B * R := by
    calc
      (∑ p ∈ B, (1 / (p : ℝ)) *
          (∫ w in E,
            ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
              logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ)))
          ≤ ∑ p ∈ B, (1 / (p : ℝ)) * R := by
            refine Finset.sum_le_sum fun p hp => ?_
            exact mul_le_mul_of_nonneg_left (hdisc p hp) (by positivity)
      _ = harmonicPrimeMass B * R := by
        rw [harmonicPrimeMass, Finset.sum_mul]
  have hbase := setIntegral_normSq_harmonicRamareBlock_le_product
    (P := P) (s := Finset.Icc A₀ B₀) (B := B) (W := W)
      hBprime C hEm hEs
  have hmass0 : 0 ≤ harmonicPrimeMass B := by
    rw [harmonicPrimeMass]
    positivity
  have hsecond :
      2 * harmonicPrimeMass B *
          (∑ p ∈ B, (1 / (p : ℝ)) *
            (∫ w in E,
              ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
                logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ)))
        ≤ 2 * harmonicPrimeMass B ^ (2 : ℕ) * R := by
    calc
      2 * harmonicPrimeMass B *
          (∑ p ∈ B, (1 / (p : ℝ)) *
            (∫ w in E,
              ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
                logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ)))
          ≤ 2 * harmonicPrimeMass B * (harmonicPrimeMass B * R) :=
            mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hmass0)
      _ = 2 * harmonicPrimeMass B ^ (2 : ℕ) * R := by ring
  dsimp only [B, C, R] at hbase hsecond ⊢
  exact hbase.trans (add_le_add le_rfl hsecond)

/-- Product integral from a harmonic-prime supremum and a cofactor mean square. -/
theorem setIntegral_normSq_harmonicBlockProduct_le_supMeanSquare
    (a : ℕ → ℂ) (B D : Finset ℕ) {W V I : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hbound : ∀ w ∈ E, ‖harmonicPrimeBlockPoly B w‖ ≤ V)
    (hI : (∫ w in E, ‖logPoly a D w‖ ^ (2 : ℕ)) ≤ I) :
    (∫ w in E, ‖harmonicPrimeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      ≤ V ^ (2 : ℕ) * I := by
  have hrw : (∫ w in E, ‖harmonicPrimeBlockPoly B w * logPoly a D w‖ ^ (2 : ℕ))
      = ∫ w in E, ‖harmonicPrimeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly a D w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_congr_fun hEm fun w _ => ?_
    rw [norm_mul, mul_pow]
  rw [hrw]
  refine le_trans (setIntegral_normSq_mul_le_of_bound
    (continuous_harmonicPrimeBlockPoly B) (continuous_logPoly a D)
    hEm hEs hbound) ?_
  exact mul_le_mul_of_nonneg_left hI (by positivity)

/-- One harmonic geometric block, with prime supremum and reciprocal HM cofactor inserted. -/
theorem setIntegral_normSq_harmonicRamareBlock_geom_le_HM
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W V : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (j : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) /
      ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : 1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hprime : ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V) :
    (∫ w in E,
      ‖harmonicRamareBlock P (Finset.Icc A₀ B₀)
        (geomBlock P Q (1 + eta) j) w‖ ^ (2 : ℕ))
      ≤ 2 * V ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
          (hmMassRecip ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
            (2 * Real.pi * W) (2 * Real.pi * volume.real E) *
              ((1 / (⌈(A₀ : ℝ) /
                ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ (2 : ℕ) *
                ((harmonicGeomCofactorBlock A₀ B₀ Q eta j).card : ℝ))))
        + 2 * harmonicPrimeMass (geomBlock P Q (1 + eta) j) ^ (2 : ℕ) *
            harmonicCofactorSupportError A₀ B₀ Q eta W j := by
  let D : Finset ℕ := harmonicGeomCofactorBlock A₀ B₀ Q eta j
  let L : ℕ := ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊
  let N : ℕ := ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
  have hD : D ⊆ Finset.Icc L N := by
    intro n hn
    simpa [D, L, N, harmonicGeomCofactorBlock] using hn
  have hcof := setIntegral_normSq_harmonicRamareCofactor_le_HM_recip
    P D (L := L) (N := N) hleft hright hD hEm hW hEs
  have hprod := setIntegral_normSq_harmonicBlockProduct_le_supMeanSquare
    (harmonicRamareCofactorCoeff P) (geomBlock P Q (1 + eta) j) D
      hEm hEs hprime hcof
  have hblock := setIntegral_normSq_harmonicRamareBlock_geom_le
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    hA₀ hQ heta hW j hPprime hleft hEm hEs
  dsimp only [D, L, N] at hcof hprod
  exact hblock.trans (by linarith)

end

end RHTower.Sieve
