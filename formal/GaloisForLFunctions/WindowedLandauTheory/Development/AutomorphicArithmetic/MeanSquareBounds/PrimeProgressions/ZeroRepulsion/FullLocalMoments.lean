import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.RepulsionPositivity
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.ShiftedPoleCancellation

/-! Signed moments of the four local divisors after removing the exceptional copies. -/

open Finset Complex Classical

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

def DHFullMoments : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β T η : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → χ₁.LFunction (β : ℂ) = 0 →
    19 / 20 ≤ β → β < 1 → IsLZero χ ρ → 22 / 25 ≤ ρ.re → |ρ.im| ≤ T →
    (χ, ρ) ≠ (χ₁, (β : ℂ)) → 0 < η → η ≤ 2 / 25 →
    ∃ S : Multiset ℂ, ((η + (1 - ρ.re) : ℝ) : ℂ) ∈ S ∧
      (S.card : ℝ) ≤ C * Real.log ((M : ℝ) * T) ∧
      ∀ j : ℕ, 1 ≤ j →
        ((S.map (fun w => 1 / w ^ j)).sum).re ≤
          2 * j * (1 - β) / η ^ (j + 1) + C * Real.log ((M : ℝ) * T) * 25 ^ j

/-- Euler positivity bounds the real moments of the remaining denominators. -/
theorem deuring_heilbronn_full_moments (hPos : DHPos) (hLoc : DHLocal) : DHFullMoments := by
  obtain ⟨CL, hCL, hL⟩ := hLoc
  refine ⟨8 * CL + 1, by linarith, ?_⟩
  intro M _ χ₁ χ β₁ T η ρ hM hT hχ₁2 hχ₁1 hβ hβ1 hβ2 hρ hρre hρim hne hη hη2
  have hlog0 : Real.log ((M : ℝ) * (|(0 : ℝ)| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) :=
    logMulAbsAddTwoLeTwoMulLog M T 0 hM hT (by rw [abs_zero]; linarith)
  have hlogγ := logMulAbsAddTwoLeTwoMulLog M T ρ.im hM hT hρim
  have hlog1 := dhLogOne M T hM hT
  obtain ⟨Z1, m1, hZ1, hm1, -, hr1, hN1, hE1⟩ := hL M 1 0
  obtain ⟨Z2, m2, hZ2, hm2, -, hr2, hN2, hE2⟩ := hL M χ₁ 0
  obtain ⟨Z3, m3, hZ3, hm3, -, hr3, hN3, hE3⟩ := hL M χ ρ.im
  obtain ⟨Z4, m4, hZ4, hm4, -, hr4, hN4, hE4⟩ := hL M (χ * χ₁) ρ.im
  obtain ⟨s₀, hs₀⟩ : ∃ s : ℂ, s = ((1 + η : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s : ℂ, s = ((1 + η : ℝ) : ℂ) + ρ.im * I := ⟨_, rfl⟩
  have hs₀' : s₀ = ((1 + η : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by rw [hs₀]; simp
  have hs₀re : s₀.re = 1 + η := by rw [hs₀]; simp
  have hs₁re : s₁.re = 1 + η := by rw [hs₁]; simp
  have hd₀ : ‖s₀ - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ≤ 1 / 25 := by
    rw [hs₀, show ((1 + η : ℝ) : ℂ) - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((η - 1 / 25 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hd₁ : ‖s₁ - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I)‖ ≤ 1 / 25 := by
    rw [hs₁, show ((1 + η : ℝ) : ℂ) + ρ.im * I - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I) = ((η - 1 / 25 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h1s₀ : 1 < s₀.re := by rw [hs₀re]; linarith
  have h1s₁ : 1 < s₁.re := by rw [hs₁re]; linarith
  have hβZ : (β₁ : ℂ) ∈ Z2 := by
    refine (hZ2 β₁).2 ⟨?_, Or.inl hχ₁1, hβ⟩
    rw [show (β₁ : ℂ) - ((26 / 25 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((β₁ - 26 / 25 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hρZ : ρ ∈ Z3 := by
    refine (hZ3 ρ).2 ⟨?_, hρ⟩
    rw [show ρ - ((26 / 25 : ℂ) + (ρ.im : ℂ) * I) = ((ρ.re - 26 / 25 : ℝ) : ℂ) by
        apply Complex.ext <;> simp,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hρ1 : ρ.re < 1 := by
      by_contra h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hρ.1 (le_of_not_gt h) hρ.2
    constructor <;> linarith
  have hb2 : s₀ - β₁ ∈ dhFam Z2 m2 s₀ := dhFam_mem _ _ _ _ hβZ (hm2 _ hβZ)
  have hb3 : χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 → s₁ - β₁ ∈ dhFam Z3 m3 s₁ :=
    fun h => dhFam_mem _ _ _ _ h.2 (hm3 _ h.2)
  have hb4 : χ = 1 ∧ (β₁ : ℂ) ∈ Z4 → s₁ - β₁ ∈ dhFam Z4 m4 s₁ :=
    fun h => dhFam_mem _ _ _ _ h.2 (hm4 _ h.2)

  have big : ∀ k : ℕ, (((dhFam Z1 m1 s₀ + (dhFam Z2 m2 s₀).erase (s₀ - β₁)
      + (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁) else dhFam Z3 m3 s₁)
      + (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁) else dhFam Z4 m4 s₁)).map
        (fun x : ℂ => 1 / x ^ (k + 1))).sum).re ≤
      2 * (((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2)) + (8 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1))
        + 8 * 0 + Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) := by
    intro k
    have key := dhAssemble (dhFam Z1 m1 s₀) (dhFam Z2 m2 s₀) (dhFam Z3 m3 s₁) (dhFam Z4 m4 s₁)
      (s₀ - β₁) (s₁ - β₁) (s₁ - β₁) _ _ hb2 hb3 hb4 (fun x : ℂ => 1 / x ^ (k + 1))
    rw [dhFamPow, dhFamPow, dhFamPow, dhFamPow] at key
    rw [key]
    have l1 := dhReBound _ _ _ _ (hE1 k s₀ h1s₀ hd₀)
    have l2 := dhReBound _ _ _ _ (hE2 k s₀ h1s₀ hd₀)
    have l3 := dhReBound _ _ _ _ (hE3 k s₁ h1s₁ hd₁)
    have l4 := dhReBound _ _ _ _ (hE4 k s₁ h1s₁ hd₁)
    rw [if_pos rfl] at l1
    rw [if_neg hχ₁1, Complex.zero_re] at l2
    have hp := hPos M χ₁ χ ρ.im (1 + η) k hχ₁2 (by linarith)
    rw [← hs₁, ← hs₀] at hp
    have hA : 0 ≤ ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) s₀).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD χ₁) s₀).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD χ) s₁).re
        + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (χ * χ₁)) s₁).re := by
      have e : ∀ a b c d : ℂ, ((-1 : ℂ) ^ k / (k.factorial : ℂ) * a).re
          + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * b).re
          + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * c).re + ((-1 : ℂ) ^ k / (k.factorial : ℂ) * d).re
          = ((k.factorial : ℝ))⁻¹ * ((-1 : ℂ) ^ k * (a + b + c + d)).re := by
        intro a b c d
        rw [← Complex.re_ofReal_mul]
        simp only [← Complex.add_re]
        congr 1
        push_cast
        ring
      rw [e]
      exact mul_nonneg (by positivity) hp
    have hpair := dhPair η 0 β₁ hη hβ2 k s₀ hs₀'
    have hshift : ((if χ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        + (if χ * χ₁ = 1 then 1 / (s₁ - 1) ^ (k + 1) else 0)
        - (if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then 1 / (s₁ - β₁) ^ (k + 1) else 0)
        - (if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then 1 / (s₁ - β₁) ^ (k + 1) else 0)).re
        ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
      refine le_trans (Complex.re_le_norm _) ?_
      refine dhfPoles χ₁ χ hχ₁2 hχ₁1 η ρ.im β₁ hη hβ1 hβ2 k s₁ hs₁ (χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3) (χ = 1 ∧ (β₁ : ℂ) ∈ Z4) ?_ ?_
        (fun h => h.1) (fun h => h.1)
      · intro h2 hc hd
        apply hc
        refine ⟨h2, (hZ3 β₁).2 ⟨hd, ?_⟩⟩
        rw [h2]
        exact ⟨Or.inl hχ₁1, hβ⟩
      · intro h1 hc hd
        apply hc
        refine ⟨h1, (hZ4 β₁).2 ⟨hd, ?_⟩⟩
        rw [h1, one_mul]
        exact ⟨Or.inl hχ₁1, hβ⟩
    simp only [Complex.add_re, Complex.sub_re] at hpair hshift ⊢
    have ee0 : CL * Real.log ((M : ℝ) * (|(0 : ℝ)| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog0 hCL.le) (by positivity)
    have eeγ : CL * Real.log ((M : ℝ) * (|ρ.im| + 2)) * 25 ^ k ≤ CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogγ hCL.le) (by positivity)
    have h8 : (8 : ℝ) ^ (k + 1) ≤ 25 ^ (k + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have h25 : (25 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) :=
      le_mul_of_one_le_left (by positivity) hlog1
    have t1 := add_le_add (add_le_add (add_le_add l1 l2) l3) l4
    have t2 : (8 : ℝ) ^ (k + 1) ≤ Real.log ((M : ℝ) * T) * 25 ^ (k + 1) := le_trans h8 h25
    have t3 : CL * (2 * Real.log ((M : ℝ) * T)) * 25 ^ k ≤
        2 * (CL * Real.log ((M : ℝ) * T) * 25 ^ (k + 1)) := by
      rw [pow_succ]
      have h := mul_nonneg hCL.le
        (mul_nonneg (zero_le_one.trans hlog1) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 25) k))
      nlinarith only [h]
    exact dhFinalArith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t1 hA hpair hshift ee0 eeγ t3 t2 le_rfl
  let W₀ := dhFam Z1 m1 s₀
  let W₁ := (dhFam Z2 m2 s₀).erase (s₀ - β₁)
  let W₂ := if χ = χ₁ ∧ (β₁ : ℂ) ∈ Z3 then (dhFam Z3 m3 s₁).erase (s₁ - β₁) else dhFam Z3 m3 s₁
  let W₃ := if χ = 1 ∧ (β₁ : ℂ) ∈ Z4 then (dhFam Z4 m4 s₁).erase (s₁ - β₁) else dhFam Z4 m4 s₁
  let S := W₀ + W₁ + W₂ + W₃
  refine ⟨S, ?_, ?_, ?_⟩
  · have hpoint : s₁ - ρ = ((η + (1 - ρ.re) : ℝ) : ℂ) := by
      rw [hs₁]
      apply Complex.ext <;> simp <;> ring
    have hmem : s₁ - ρ ∈ dhFam Z3 m3 s₁ := dhFam_mem _ _ _ _ hρZ (hm3 _ hρZ)
    have hretained : s₁ - ρ ∈ W₂ := by
      dsimp only [W₂]
      split_ifs with h
      · refine (Multiset.mem_erase_of_ne ?_).2 hmem
        intro he
        apply hne
        exact Prod.ext h.1 (sub_right_inj.mp he)
      · exact hmem
    rw [← hpoint]
    exact Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inr hretained)))
  · have hcard₁ : W₁.card ≤ (dhFam Z2 m2 s₀).card := Multiset.card_erase_le
    have hcard₂ : W₂.card ≤ (dhFam Z3 m3 s₁).card := by
      dsimp only [W₂]
      split_ifs <;> first | exact Multiset.card_erase_le | exact le_rfl
    have hcard₃ : W₃.card ≤ (dhFam Z4 m4 s₁).card := by
      dsimp only [W₃]
      split_ifs <;> first | exact Multiset.card_erase_le | exact le_rfl
    have h₀ : (W₀.card : ℝ) ≤ CL * (2 * Real.log ((M : ℝ) * T)) := by
      dsimp only [W₀]
      rw [dhFam_card]
      exact hN1.trans (mul_le_mul_of_nonneg_left hlog0 hCL.le)
    have bound (W : Multiset ℂ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (a : ℝ)
        (hc : W.card ≤ (dhFam Z m s).card) (hN : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ CL * a)
        (ha : a ≤ 2 * Real.log ((M : ℝ) * T)) :
        (W.card : ℝ) ≤ CL * (2 * Real.log ((M : ℝ) * T)) := by
      rw [dhFam_card] at hc
      exact (show (W.card : ℝ) ≤ ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) by exact_mod_cast hc).trans
        (hN.trans (mul_le_mul_of_nonneg_left ha hCL.le))
    have h₁ := bound W₁ Z2 m2 s₀ _ hcard₁ hN2 hlog0
    have h₂ := bound W₂ Z3 m3 s₁ _ hcard₂ hN3 hlogγ
    have h₃ := bound W₃ Z4 m4 s₁ _ hcard₃ hN4 hlogγ
    simp only [S, Multiset.card_add, Nat.cast_add]
    linarith only [h₀, h₁, h₂, h₃, hlog1]
  · intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h := big k
    change ((S.map (fun w : ℂ => 1 / w ^ (k + 1))).sum).re ≤ _ at h
    push_cast
    convert h using 1 <;> ring

end QH.PrimeProgressions
