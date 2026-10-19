import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiMultiBankPrimeCube
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiPrimeCapacityBanks

/-!
# Normalized Gram of one-hot parity packets on disjoint prime banks

On each bank the constant and parity sectors have masses `A = ∏ (1 + 1/p)` and
`D = ∏ (1 - 1/p)`. Their quotient is the bank parity ratio `θ = ∏ (p-1)/(p+1)`,
and the two parity classes have common mass `E = 2^|T| (A + D)/4` and
correlation `ρ = (A - D)/(A + D) = (1 - θ)/(1 + θ)`.

The packet with odd parity in bank `j` and even parity in every other bank
is a nonempty zero-one packet. After division by `H = ∏ E`, the Gram matrix of
these packets is exactly `1` on the diagonal and `ρ_j ρ_k` off the diagonal.
With the native odd reciprocal-square mass included once, this is the literal
Gram matrix of the corresponding native odd-divisor packets. If every ratio is
below `1/(4L)`, every normalized entry lies in `[1 - 1/L, 1]`.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- Constant-sector eigenmass of one prime bank. -/
def fermiBankConstantMass (T : Finset ℕ) : ℝ := ∏ p ∈ T, (1 + 1 / (p : ℝ))

/-- Parity-sector eigenmass of one prime bank. -/
def fermiBankParityMass (T : Finset ℕ) : ℝ := ∏ p ∈ T, (1 - 1 / (p : ℝ))

/-- Common squared mass of the two parity classes of one prime bank. -/
def fermiBankParityClassMass (T : Finset ℕ) : ℝ :=
  (2 : ℝ) ^ T.card / 4 * (fermiBankConstantMass T + fermiBankParityMass T)

/-- Normalized correlation between the two parity classes of one prime bank. -/
def fermiBankParityCorrelation (T : Finset ℕ) : ℝ :=
  (fermiBankConstantMass T - fermiBankParityMass T) /
    (fermiBankConstantMass T + fermiBankParityMass T)

section Bank

variable (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
include hT

omit hT in
theorem fermiBankConstantMass_pos : 0 < fermiBankConstantMass T :=
  Finset.prod_pos (fun p _ => by positivity)

theorem fermiBankParityMass_pos : 0 < fermiBankParityMass T := by
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hT p hp).two_le
  have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  linarith

theorem fermiBankParityClassMass_pos : 0 < fermiBankParityClassMass T := by
  unfold fermiBankParityClassMass
  have := fermiBankConstantMass_pos T
  have := fermiBankParityMass_pos T hT
  positivity

/-- The parity-sector mass is the bank parity ratio times the constant-sector mass. -/
theorem fermiBankParityMass_eq_ratio_mul :
    fermiBankParityMass T = fermiPrimeBankParityRatio T * fermiBankConstantMass T := by
  unfold fermiBankParityMass fermiPrimeBankParityRatio fermiBankConstantMass
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hT p hp).two_le
  field_simp [show (p : ℝ) + 1 ≠ 0 by linarith]

/-- The normalized parity correlation is `(1 - θ)/(1 + θ)`. -/
theorem fermiBankParityCorrelation_eq :
    fermiBankParityCorrelation T =
      (1 - fermiPrimeBankParityRatio T) / (1 + fermiPrimeBankParityRatio T) := by
  have hA := fermiBankConstantMass_pos T
  have hθ := fermiPrimeBankParityRatio_pos T hT
  unfold fermiBankParityCorrelation
  rw [fermiBankParityMass_eq_ratio_mul T hT]
  field_simp

/-- A parity ratio below `1/(4L)` gives a correlation in `(1 - 1/(2L), 1)`. -/
theorem fermiBankParityCorrelation_bounds {L : ℝ} (hL : 0 < L)
    (hθ : fermiPrimeBankParityRatio T < 1 / (4 * L)) :
    1 - 1 / (2 * L) < fermiBankParityCorrelation T ∧ fermiBankParityCorrelation T < 1 := by
  have h0 := fermiPrimeBankParityRatio_pos T hT
  rw [fermiBankParityCorrelation_eq T hT]
  set θ := fermiPrimeBankParityRatio T
  have h1 : 0 < 1 + θ := by linarith
  have h2 : 2 * θ < 1 / (2 * L) := by
    have : 1 / (2 * L) = 2 * (1 / (4 * L)) := by field_simp; ring
    linarith
  constructor
  · rw [lt_div_iff₀ h1]
    nlinarith
  · rw [div_lt_one h1]
    linarith

end Bank

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Indicator of odd parity in bank `j` and even parity in every other bank. -/
def fermiOneHotBankPacket (T : I → Finset ℕ) (j : I) (x : ∀ i, T i → Bool) : ℝ :=
  fermiBankParityPacket (fun i => decide (i = j)) x

/-- Normalized Gram matrix of the one-hot packets: `1` diagonal, `ρ_j ρ_k` off it. -/
def fermiBankNormalizedGram (T : I → Finset ℕ) (j k : I) : ℝ :=
  if j = k then 1 else fermiBankParityCorrelation (T j) * fermiBankParityCorrelation (T k)

private theorem bank_factor (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (q : Prop) [Decidable q] :
    (Fintype.card (T → Bool) : ℝ) / 4 *
      ((∏ p : T, (1 + 1 / (p : ℝ))) + (if q then 1 else -1) * ∏ p : T, (1 - 1 / (p : ℝ))) =
      fermiBankParityClassMass T * (if q then 1 else fermiBankParityCorrelation T) := by
  have hA := fermiBankConstantMass_pos T
  have hD := fermiBankParityMass_pos T hT
  have hcard : (Fintype.card (T → Bool) : ℝ) = (2 : ℝ) ^ T.card := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    push_cast
    rfl
  rw [hcard, Finset.prod_coe_sort T (fun p => 1 + 1 / (p : ℝ)),
    Finset.prod_coe_sort T (fun p => 1 - 1 / (p : ℝ))]
  unfold fermiBankParityClassMass fermiBankParityCorrelation
  unfold fermiBankConstantMass fermiBankParityMass at *
  by_cases hq : q
  · simp only [hq, if_true, one_mul, mul_one]
  · simp only [hq, if_false]
    field_simp
    ring

/-- Exact one-hot Gram law: `fermiBankParityGram = (∏ E) * normalized Gram`. -/
theorem fermiOneHotBankPacket_gram (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hne : ∀ i, (T i).Nonempty) (j k : I) :
    fermiBankParityGram (fun i (p : T i) => 1 / (p : ℝ))
        (fun i => decide (i = j)) (fun i => decide (i = k)) =
      (∏ i, fermiBankParityClassMass (T i)) * fermiBankNormalizedGram T j k := by
  haveI : ∀ i, Nonempty (T i) := fun i => (hne i).to_subtype
  rw [fermiBankParityGram_formula]
  calc
    _ = ∏ i, (fermiBankParityClassMass (T i) *
        (if decide (i = j) = decide (i = k) then 1 else fermiBankParityCorrelation (T i))) :=
      Finset.prod_congr rfl (fun i _ => bank_factor (T i) (hT i) _)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      congr 1
      unfold fermiBankNormalizedGram
      split_ifs with hjk
      · subst hjk
        simp
      · have hg (i : I) : (if decide (i = j) = decide (i = k) then (1 : ℝ)
            else fermiBankParityCorrelation (T i)) =
            (if i = j then fermiBankParityCorrelation (T i) else 1) *
              (if i = k then fermiBankParityCorrelation (T i) else 1) := by
          by_cases hij : i = j
          · subst hij
            simp [hjk]
          · by_cases hik : i = k
            · subst hik
              simp [hij]
            · simp [hij, hik]
        simp only [hg, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

/-- The one-hot packets are zero-one indicators. -/
theorem fermiOneHotBankPacket_zero_or_one (T : I → Finset ℕ) (j : I) (x : ∀ i, T i → Bool) :
    fermiOneHotBankPacket T j x = 0 ∨ fermiOneHotBankPacket T j x = 1 :=
  fermiBankParityPacket_zero_or_one _ x

/-- Distinct one-hot packets have disjoint supports. -/
theorem fermiOneHotBankPacket_disjoint (T : I → Finset ℕ) {j k : I} (hjk : j ≠ k)
    (x : ∀ i, T i → Bool) :
    fermiOneHotBankPacket T j x * fermiOneHotBankPacket T k x = 0 :=
  fermiBankParityPacket_oneHot_disjoint j k hjk x

/-- Every one-hot packet has a point of its support. -/
theorem fermiOneHotBankPacket_nonempty (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hne : ∀ i, (T i).Nonempty) (j : I) :
    ∃ x, fermiOneHotBankPacket T j x = 1 := by
  by_contra hno
  have hzero (x : ∀ i, T i → Bool) : fermiOneHotBankPacket T j x = 0 :=
    (fermiOneHotBankPacket_zero_or_one T j x).resolve_right (fun h => hno ⟨x, h⟩)
  have hg := fermiOneHotBankPacket_gram T hT hne j j
  have hpos : 0 < (∏ i, fermiBankParityClassMass (T i)) * fermiBankNormalizedGram T j j := by
    simp only [fermiBankNormalizedGram, if_true, mul_one]
    exact Finset.prod_pos (fun i _ => fermiBankParityClassMass_pos (T i) (hT i))
  rw [← hg] at hpos
  unfold fermiBankParityGram at hpos
  simp only [fermiOneHotBankPacket] at hzero
  simp [hzero] at hpos

omit [Fintype I] in
/-- The normalized one-hot Gram is symmetric. -/
theorem fermiBankNormalizedGram_symm (T : I → Finset ℕ) (j k : I) :
    fermiBankNormalizedGram T j k = fermiBankNormalizedGram T k j := by
  unfold fermiBankNormalizedGram
  by_cases h : j = k
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), mul_comm]

omit [Fintype I] in
/-- Parity ratios below `1/(4L)` place every normalized Gram entry in `[1 - 1/L, 1]`. -/
theorem fermiBankNormalizedGram_bounds (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    {L : ℝ} (hL : 1 ≤ L) (hθ : ∀ i, fermiPrimeBankParityRatio (T i) < 1 / (4 * L))
    (j k : I) :
    1 - 1 / L ≤ fermiBankNormalizedGram T j k ∧ fermiBankNormalizedGram T j k ≤ 1 := by
  unfold fermiBankNormalizedGram
  split_ifs
  · constructor
    · have : 0 ≤ 1 / L := by positivity
      linarith
    · exact le_rfl
  · have hL0 : 0 < L := by linarith
    obtain ⟨hj1, hj2⟩ := fermiBankParityCorrelation_bounds (T j) (hT j) hL0 (hθ j)
    obtain ⟨hk1, hk2⟩ := fermiBankParityCorrelation_bounds (T k) (hT k) hL0 (hθ k)
    have hh : 1 / (2 * L) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hsq : 1 - 1 / L ≤ (1 - 1 / (2 * L)) * (1 - 1 / (2 * L)) := by
      have : 1 / L = 2 * (1 / (2 * L)) := by field_simp
      nlinarith [sq_nonneg (1 / (2 * L))]
    constructor
    · exact hsq.trans (mul_le_mul hj1.le hk1.le (by linarith) (by linarith))
    · nlinarith

/-- Normalized one-hot native odd-divisor packets have exactly the Gram matrix `G`. -/
theorem fermiOneHotBank_native_gram (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hodd : ∀ i, ∀ p ∈ T i, Odd p) (hdisj : Pairwise (fun i k => Disjoint (T i) (T k)))
    (hne : ∀ i, (T i).Nonempty) (γ : I → ℝ) :
    Summable (fun m : ℕ => (fermiOddDivisorPacket (fermiBankCubeSupport T)
      (fun d => (Real.sqrt (fermiOddHomogeneousMass * ∏ i, fermiBankParityClassMass (T i)))⁻¹ *
        ∑ j, γ j * fermiOneHotBankPacket T j ((fermiBankCubeEquiv T hT hdisj).symm d)) m)^2) ∧
    (∑' m : ℕ, (fermiOddDivisorPacket (fermiBankCubeSupport T)
      (fun d => (Real.sqrt (fermiOddHomogeneousMass * ∏ i, fermiBankParityClassMass (T i)))⁻¹ *
        ∑ j, γ j * fermiOneHotBankPacket T j ((fermiBankCubeEquiv T hT hdisj).symm d)) m)^2) =
      ∑ j, ∑ k, γ j * γ k * fermiBankNormalizedGram T j k := by
  set E := ∏ i, fermiBankParityClassMass (T i)
  have hE : 0 < E := Finset.prod_pos (fun i _ => fermiBankParityClassMass_pos (T i) (hT i))
  have hH : 0 < fermiOddHomogeneousMass * E := mul_pos fermiOddHomogeneousMass_pos hE
  set s := (Real.sqrt (fermiOddHomogeneousMass * E))⁻¹
  have hs : fermiOddHomogeneousMass * (s * s) * E = 1 := by
    have hsq := Real.sq_sqrt hH.le
    have hr : Real.sqrt (fermiOddHomogeneousMass * E) ≠ 0 := (Real.sqrt_pos.mpr hH).ne'
    simp only [s]
    field_simp
    rw [hsq]
  obtain ⟨hsum, heq⟩ := fermiBankCubePacket_energy T hT hodd hdisj
    (fun x => s * ∑ j, γ j * fermiOneHotBankPacket T j x)
  refine ⟨hsum, heq.trans ?_⟩
  let K : (∀ i, T i → Bool) → (∀ i, T i → Bool) → ℝ :=
    fun x y => ∏ i, fermiBooleanGram (fun p : T i => 1 / (p : ℝ)) (x i) (y i)
  have hexp (x y : ∀ i, T i → Bool) :
      (s * ∑ j, γ j * fermiOneHotBankPacket T j x) * K x y *
        (s * ∑ k, γ k * fermiOneHotBankPacket T k y) =
      ∑ j, ∑ k, (s * s * (γ j * γ k)) *
        (fermiOneHotBankPacket T j x * K x y * fermiOneHotBankPacket T k y) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ = fermiOddHomogeneousMass * ∑ x : ∀ i, T i → Bool, ∑ y : ∀ i, T i → Bool,
        ∑ j, ∑ k, (s * s * (γ j * γ k)) *
          (fermiOneHotBankPacket T j x * K x y * fermiOneHotBankPacket T k y) := by
      congr 1
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hexp x y))
    _ = fermiOddHomogeneousMass * ∑ j, ∑ k, (s * s * (γ j * γ k)) *
        fermiBankParityGram (fun i (p : T i) => 1 / (p : ℝ))
          (fun i => decide (i = j)) (fun i => decide (i = k)) := by
      congr 1
      unfold fermiBankParityGram
      simp only [Finset.mul_sum]
      calc
        _ = ∑ x : ∀ i, T i → Bool, ∑ j, ∑ y : ∀ i, T i → Bool, ∑ k,
            (s * s * (γ j * γ k)) *
              (fermiOneHotBankPacket T j x * K x y * fermiOneHotBankPacket T k y) :=
          Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
        _ = ∑ j, ∑ x : ∀ i, T i → Bool, ∑ y : ∀ i, T i → Bool, ∑ k,
            (s * s * (γ j * γ k)) *
              (fermiOneHotBankPacket T j x * K x y * fermiOneHotBankPacket T k y) :=
          Finset.sum_comm
        _ = ∑ j, ∑ x : ∀ i, T i → Bool, ∑ k, ∑ y : ∀ i, T i → Bool,
            (s * s * (γ j * γ k)) *
              (fermiOneHotBankPacket T j x * K x y * fermiOneHotBankPacket T k y) :=
          Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun x _ => Finset.sum_comm))
        _ = _ := Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = ∑ j, ∑ k, γ j * γ k * fermiBankNormalizedGram T j k := by
      simp only [fermiOneHotBankPacket_gram T hT hne, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      calc
        _ = (fermiOddHomogeneousMass * (s * s) * E) * (γ j * γ k * fermiBankNormalizedGram T j k) := by
          ring
        _ = _ := by rw [hs, one_mul]

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
