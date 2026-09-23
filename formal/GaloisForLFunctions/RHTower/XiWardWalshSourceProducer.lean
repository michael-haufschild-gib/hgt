import GaloisForLFunctions.RHTower.XiWardTriangularSourceRectangle

/-!
# Walsh-fibre source producer for the Xi Ward annulus

The completed prime--polar--Gamma source is lifted through every finite Walsh marking before
realification. Normalized fibre energy is exactly its marked diagonal, so cell interference is
removed source-side without selecting signs from a divisor packet.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

noncomputable local instance xiWardWalshFintypeForallBool
    {κ : Type*} [Fintype κ] : Fintype (κ → Bool) :=
  Fintype.ofFinite _

/-- The completed source response lifted to every Walsh sign in a finite marking fibre. -/
def xiWardWalshSourceResponse
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → ℝ → ℂ) (epsilon : κ → Bool) (t : ℝ) : ℂ :=
  ∑ c : κ, (wardCellSign epsilon c : ℂ) * R c t

theorem xiWardWalshSourceResponse_re
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → ℝ → ℂ) (epsilon : κ → Bool) (t : ℝ) :
    (xiWardWalshSourceResponse R epsilon t).re =
      ∑ c : κ, wardCellSign epsilon c * (R c t).re := by
  unfold xiWardWalshSourceResponse
  simp [Complex.mul_re]

/-- Normalized Walsh-fibre energy of a marked completed source response. -/
def xiWardWalshSourceMeanEnergy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → ℝ → ℂ) : ℝ :=
  ((2 : ℝ) ^ Fintype.card κ)⁻¹ *
    ∑ epsilon : κ → Bool, ∫ t : ℝ, (xiWardWalshSourceResponse R epsilon t).re ^ (2 : ℕ)

theorem xiWardWalshSourceMeanEnergy_eq_diagonal
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : κ → ℝ → ℂ)
    (hR : ∀ c d : κ, Integrable (fun t : ℝ => (R c t).re * (R d t).re)) :
    xiWardWalshSourceMeanEnergy R =
      ∑ c : κ, ∫ t : ℝ, (R c t).re ^ (2 : ℕ) := by
  classical
  have hwalsh (c d : κ) :
      (∑ epsilon : κ → Bool,
        wardCellSign epsilon c * wardCellSign epsilon d) =
        if c = d then (2 : ℝ) ^ Fintype.card κ else 0 := by
    simpa only [wardCellSign, Finset.singleton_inj] using
      (GaloisForLFunctions.HTGeometry.sum_lbitWalshCharacterReal_mul
        ({c} : Finset κ) ({d} : Finset κ))
  have hterm (epsilon : κ → Bool) (c d : κ) :
      Integrable (fun t : ℝ =>
        wardCellSign epsilon c * wardCellSign epsilon d *
          ((R c t).re * (R d t).re)) := by
    exact (hR c d).const_mul _
  have hexpand (epsilon : κ → Bool) (t : ℝ) :
      (xiWardWalshSourceResponse R epsilon t).re ^ (2 : ℕ) =
        ∑ c : κ, ∑ d : κ,
          wardCellSign epsilon c * wardCellSign epsilon d *
            ((R c t).re * (R d t).re) := by
    rw [xiWardWalshSourceResponse_re, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hsum :
      (∑ epsilon : κ → Bool,
        ∫ t : ℝ, (xiWardWalshSourceResponse R epsilon t).re ^ (2 : ℕ)) =
        (2 : ℝ) ^ Fintype.card κ *
          ∑ c : κ, ∫ t : ℝ, (R c t).re ^ (2 : ℕ) := by
    calc
      (∑ epsilon : κ → Bool,
        ∫ t : ℝ, (xiWardWalshSourceResponse R epsilon t).re ^ (2 : ℕ)) =
          ∑ epsilon : κ → Bool, ∑ c : κ, ∑ d : κ,
            ∫ t : ℝ,
              wardCellSign epsilon c * wardCellSign epsilon d *
                ((R c t).re * (R d t).re) := by
          apply Finset.sum_congr rfl
          intro epsilon hepsilon
          calc
            ∫ t : ℝ, (xiWardWalshSourceResponse R epsilon t).re ^ (2 : ℕ) =
                ∫ t : ℝ, ∑ c : κ, ∑ d : κ,
                  wardCellSign epsilon c * wardCellSign epsilon d *
                    ((R c t).re * (R d t).re) := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall (hexpand epsilon)
            _ = ∑ c : κ, ∫ t : ℝ, ∑ d : κ,
                wardCellSign epsilon c * wardCellSign epsilon d *
                  ((R c t).re * (R d t).re) := by
              rw [MeasureTheory.integral_finsetSum]
              intro c hc
              exact MeasureTheory.integrable_finsetSum _ (fun d hd => hterm epsilon c d)
            _ = ∑ c : κ, ∑ d : κ,
                ∫ t : ℝ,
                  wardCellSign epsilon c * wardCellSign epsilon d *
                    ((R c t).re * (R d t).re) := by
              apply Finset.sum_congr rfl
              intro c hc
              rw [MeasureTheory.integral_finsetSum]
              intro d hd
              exact hterm epsilon c d
      _ = ∑ c : κ, ∑ d : κ, ∑ epsilon : κ → Bool,
            ∫ t : ℝ,
              wardCellSign epsilon c * wardCellSign epsilon d *
                ((R c t).re * (R d t).re) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.sum_comm]
      _ = ∑ c : κ, ∑ d : κ,
          (∑ epsilon : κ → Bool,
            wardCellSign epsilon c * wardCellSign epsilon d) *
              ∫ t : ℝ, (R c t).re * (R d t).re := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          calc
            ∑ epsilon : κ → Bool,
                ∫ t : ℝ, wardCellSign epsilon c * wardCellSign epsilon d *
                  ((R c t).re * (R d t).re) =
                ∑ epsilon : κ → Bool,
                  (wardCellSign epsilon c * wardCellSign epsilon d) *
                    ∫ t : ℝ, (R c t).re * (R d t).re := by
              apply Finset.sum_congr rfl
              intro epsilon hepsilon
              rw [show (fun t : ℝ =>
                  wardCellSign epsilon c * wardCellSign epsilon d *
                    ((R c t).re * (R d t).re)) =
                  fun t => (wardCellSign epsilon c * wardCellSign epsilon d) *
                    ((R c t).re * (R d t).re) by
                  funext t
                  ring]
              rw [MeasureTheory.integral_const_mul]
            _ = (∑ epsilon : κ → Bool,
                wardCellSign epsilon c * wardCellSign epsilon d) *
                  ∫ t : ℝ, (R c t).re * (R d t).re := by
              rw [← Finset.sum_mul]
      _ = (2 : ℝ) ^ Fintype.card κ *
          ∑ c : κ, ∫ t : ℝ, (R c t).re ^ (2 : ℕ) := by
          calc
            ∑ c : κ, ∑ d : κ,
                (∑ epsilon : κ → Bool,
                  wardCellSign epsilon c * wardCellSign epsilon d) *
                    ∫ t : ℝ, (R c t).re * (R d t).re =
                ∑ c : κ, ∑ d : κ,
                  (if c = d then (2 : ℝ) ^ Fintype.card κ else 0) *
                    ∫ t : ℝ, (R c t).re * (R d t).re := by
              apply Finset.sum_congr rfl
              intro c hc
              apply Finset.sum_congr rfl
              intro d hd
              exact congrArg (fun x : ℝ => x *
                ∫ t : ℝ, (R c t).re * (R d t).re)
                (hwalsh c d)
            _ = (2 : ℝ) ^ Fintype.card κ *
                ∑ c : κ, ∫ t : ℝ, (R c t).re ^ (2 : ℕ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro c hc
              rw [show (fun d : κ =>
                  (if c = d then (2 : ℝ) ^ Fintype.card κ else 0) *
                    ∫ t : ℝ, (R c t).re * (R d t).re) =
                  fun d => if c = d then
                    (2 : ℝ) ^ Fintype.card κ *
                      ∫ t : ℝ, (R c t).re * (R d t).re else 0 by
                  funext d
                  split_ifs <;> ring]
              rw [Finset.sum_ite_eq]
              simp only [Finset.mem_univ, if_true]
              congr 2
              funext t
              ring
  unfold xiWardWalshSourceMeanEnergy
  rw [hsum]
  have hpow : (2 : ℝ) ^ Fintype.card κ ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hpow]

/-- A literal paired prime--Gamma source rectangle, lifted to the full Walsh fibre before its
real part or energy is formed. -/
def xiWardWalshSourceRectangleResponseAtLine
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (sigma : ℝ) (z₁ z₂ z₁' z₂' : κ → ℂ)
    (epsilon : κ → Bool) (t : ℝ) : ℂ :=
  xiWardWalshSourceResponse
    (fun c u => xiWardPairedSourceRectangleResponse
      (((sigma : ℂ) + I * (u : ℂ))) (z₁ c) (z₂ c) (z₁' c) (z₂' c)) epsilon t

/-- Normalized pre-scalar source energy at one Ward line. -/
def xiWardWalshSourceRectangleMeanEnergyAtLine
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (sigma : ℝ) (z₁ z₂ z₁' z₂' : κ → ℂ) : ℝ :=
  xiWardWalshSourceMeanEnergy
    (fun c u => xiWardPairedSourceRectangleResponse
      (((sigma : ℂ) + I * (u : ℂ))) (z₁ c) (z₂ c) (z₁' c) (z₂' c))

/-- Walsh orthogonality removes all cross-cell terms while retaining each literal completed
source rectangle energy unchanged. -/
theorem xiWardWalshSourceRectangleMeanEnergyAtLine_eq_sum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (sigma : ℝ) (z₁ z₂ z₁' z₂' : κ → ℂ)
    (hR : ∀ c d : κ, Integrable (fun t : ℝ =>
      (xiWardPairedSourceRectangleResponse
        (((sigma : ℂ) + I * (t : ℂ))) (z₁ c) (z₂ c) (z₁' c) (z₂' c)).re *
      (xiWardPairedSourceRectangleResponse
        (((sigma : ℂ) + I * (t : ℂ))) (z₁ d) (z₂ d) (z₁' d) (z₂' d)).re)) :
    xiWardWalshSourceRectangleMeanEnergyAtLine sigma z₁ z₂ z₁' z₂' =
      ∑ c : κ, xiWardPairedSourceRectangleRealEnergyAtLine
        sigma (z₁ c) (z₂ c) (z₁' c) (z₂' c) := by
  exact xiWardWalshSourceMeanEnergy_eq_diagonal _ hR

/-- The source-faithful Walsh producer: narrow-line mean energy minus wide-line mean energy. -/
def xiWardWalshSourceRectangleAnnulusMeanEnergy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z₁ z₂ z₁' z₂' : κ → ℂ) : ℝ :=
  xiWardWalshSourceRectangleMeanEnergyAtLine (51 / 100) z₁ z₂ z₁' z₂' -
    xiWardWalshSourceRectangleMeanEnergyAtLine (1051 / 100) z₁ z₂ z₁' z₂'

/-- The full Walsh-fibre producer is exactly the sum of its marked completed source annuli.
Thus source-side marking removes inter-cell interference without choosing a sign from any divisor
packet and without separating prime, polar, or Gamma contributions. -/
theorem xiWardWalshSourceRectangleAnnulusMeanEnergy_eq_sum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z₁ z₂ z₁' z₂' : κ → ℂ)
    (hnarrow : ∀ c d : κ, Integrable (fun t : ℝ =>
      (xiWardPairedSourceRectangleResponse
        (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ)) (z₁ c) (z₂ c) (z₁' c) (z₂' c)).re *
      (xiWardPairedSourceRectangleResponse
        (((51 / 100 : ℝ) : ℂ) + I * (t : ℂ)) (z₁ d) (z₂ d) (z₁' d) (z₂' d)).re))
    (hwide : ∀ c d : κ, Integrable (fun t : ℝ =>
      (xiWardPairedSourceRectangleResponse
        (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ)) (z₁ c) (z₂ c) (z₁' c) (z₂' c)).re *
      (xiWardPairedSourceRectangleResponse
        (((1051 / 100 : ℝ) : ℂ) + I * (t : ℂ)) (z₁ d) (z₂ d) (z₁' d) (z₂' d)).re)) :
    xiWardWalshSourceRectangleAnnulusMeanEnergy z₁ z₂ z₁' z₂' =
      ∑ c : κ, xiWardPairedSourceRectangleAnnulusEnergy
        (z₁ c) (z₂ c) (z₁' c) (z₂' c) := by
  rw [xiWardWalshSourceRectangleAnnulusMeanEnergy,
    xiWardWalshSourceRectangleMeanEnergyAtLine_eq_sum (51 / 100) z₁ z₂ z₁' z₂' hnarrow,
    xiWardWalshSourceRectangleMeanEnergyAtLine_eq_sum (1051 / 100) z₁ z₂ z₁' z₂' hwide,
    ← Finset.sum_sub_distrib]
  rfl

end

end RHTower
