import GaloisForLFunctions.RHTower.RootOfUnityIntervalCompletion

/-!
# Finite Fourier extraction of a top multilinear coefficient

A product of `r` affine factors has degrees between zero and `r`. Averaging over
`r + 1` roots of unity extracts its top coefficient. The extraction weights have
absolute sum one. This uses the corpus's existing additive-character orthogonality.

Applied to the local factors in Lemma 18.2 of *Ordinary two-point correlations of
multiplicative functions*, the identity yields a shorter complex phase expansion
of dilation. It is a finite Fourier identity, with no analytic input.
-/


open Finset
namespace GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.HyperKloostermanSecondMoment
open GaloisForLFunctions.RHTower.RootOfUnityCompletion
noncomputable section

private theorem topPhaseAverage_power (r k : ℕ) (hk : k ≤ r) :
    ((r + 1 : ℕ) : ℂ)⁻¹ *
        (∑ h : ZMod (r + 1), ZMod.stdAddChar (-(h * (r : ZMod (r + 1)))) *
          ZMod.stdAddChar h ^ k) = if k = r then 1 else 0 := by
  have hterm (h : ZMod (r + 1)) :
      ZMod.stdAddChar (-(h * (r : ZMod (r + 1)))) * ZMod.stdAddChar h ^ k =
        ZMod.stdAddChar (h * ((k : ZMod (r + 1)) - (r : ZMod (r + 1)))) := by
    rw [← stdAddChar_mul_natCast_pow, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hterm]
  rw [sum_stdAddChar_mul]
  have hcast : ((k : ZMod (r + 1)) = (r : ZMod (r + 1))) ↔ k = r := by
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      simpa only [ZMod.val_natCast_of_lt (lt_of_le_of_lt hk (Nat.lt_succ_self r)),
        ZMod.val_natCast_of_lt (Nat.lt_succ_self r)] using hv
    · intro h; subst k; rfl
  simp only [sub_eq_zero, hcast]
  by_cases hkr : k = r
  · simp only [if_pos hkr]
    exact inv_mul_cancel₀ (show ((r + 1 : ℕ) : ℂ) ≠ 0 by
      exact_mod_cast Nat.succ_ne_zero r)
  · simp [hkr]

/-- The top multilinear coefficient is extracted by exactly cardinality-plus-one phases. -/
theorem prod_eq_topFourier_average {I : Type*} [DecidableEq I]
    (S : Finset I) (C D : I → ℂ) :
    (∏ i ∈ S, D i) = ((S.card + 1 : ℕ) : ℂ)⁻¹ *
      ∑ h : ZMod (S.card + 1),
        ZMod.stdAddChar (-(h * (S.card : ZMod (S.card + 1)))) *
          ∏ i ∈ S, (C i + ZMod.stdAddChar h * D i) := by
  have hexp (h : ZMod (S.card + 1)) :
      (∏ i ∈ S, (C i + ZMod.stdAddChar h * D i)) =
        ∑ T ∈ S.powerset, ZMod.stdAddChar h ^ T.card *
          (∏ i ∈ T, D i) * ∏ i ∈ S \ T, C i := by
    calc
      _ = ∏ i ∈ S, (ZMod.stdAddChar h * D i + C i) := by
        apply prod_congr rfl
        intro i _
        exact add_comm _ _
      _ = _ := by
        rw [prod_add]
        simp only [prod_mul_distrib, prod_const]
  symm
  calc
    _ = ∑ T ∈ S.powerset, ((∏ i ∈ T, D i) * ∏ i ∈ S \ T, C i) *
        (((S.card + 1 : ℕ) : ℂ)⁻¹ *
          ∑ h : ZMod (S.card + 1),
            ZMod.stdAddChar (-(h * (S.card : ZMod (S.card + 1)))) *
              ZMod.stdAddChar h ^ T.card) := by
      simp_rw [hexp, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro T _
      apply sum_congr rfl
      intro h _
      ring
    _ = ∑ T ∈ S.powerset, ((∏ i ∈ T, D i) * ∏ i ∈ S \ T, C i) *
        (if T.card = S.card then 1 else 0) := by
      apply sum_congr rfl
      intro T hT
      rw [topPhaseAverage_power _ _ (card_le_card (mem_powerset.mp hT))]
    _ = ∏ i ∈ S, D i := by
      rw [sum_eq_single S]
      · simp
      · intro T hT hne
        have hlt : T.card < S.card := card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hT, hne⟩)
        simp [ne_of_lt hlt]
      · simp

/-- Fourier weights used to select the top interaction degree. -/
def topFourierWeight (r : ℕ) (h : ZMod (r + 1)) : ℂ :=
  ((r + 1 : ℕ) : ℂ)⁻¹ * ZMod.stdAddChar (-(h * (r : ZMod (r + 1))))

/-- The selection weights have absolute mass one, independently of the degree. -/
theorem sum_norm_topFourierWeight (r : ℕ) :
    (∑ h : ZMod (r + 1), ‖topFourierWeight r h‖) = 1 := by
  simp only [topFourierWeight, norm_mul, norm_inv, Complex.norm_natCast,
    ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
  simp [show (r : ℝ) + 1 ≠ 0 by positivity]

end
end GaloisForLFunctions.HTGeometry
