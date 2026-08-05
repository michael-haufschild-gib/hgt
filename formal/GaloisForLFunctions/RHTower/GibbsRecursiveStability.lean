import Mathlib
import GaloisForLFunctions.RHTower.GibbsWeakCouplingConfinement

/-!
# Recursive stability of the squarefree Gibbs gas

The cutoff recursion controls the deviation of the gas from the free gas.  Writing
`E_S(z,x) = P_S(z,x) - (1+z)^{|S|}`, the recursion is exact,

  `E_{S∪p}(z,x) = E_S(z,x) + z·E_S(z,px)`,

and the dilated scale `px` is absorbed by the elementary geometry
`1 + p‖z‖ ≤ (1+p)‖1+z‖`, valid whenever `1 ≤ ‖1+z‖` and `‖z‖ ≤ ‖1+z‖` — in particular on
the whole closed right half-plane.  Induction therefore gives the **relative** estimate

  `‖P_S(z,x) - (1+z)^k‖ ≤ x·σ(m)·‖1+z‖^k`,   `σ(m) = ∏_{p∈S}(1+p)`,

with no exponential loss, since no modulus is taken inside the product.  Consequently the
gas is Hurwitz stable for every `k` as soon as `x·σ(m) < 1`, and its zero set splits into
the parity cluster `‖z+1‖ < 1` and a far-left region `Re z < -1/2`.
-/

namespace RHTower.GibbsGas

open Real

theorem gibbsDiagC_empty (x : ℝ) (z : ℂ) :
    gibbsDiagC ∅ x z = ((Real.exp (-x) : ℝ) : ℂ) := by
  simp [gibbsDiagC]

/-- **The cutoff recursion at complex activity.** -/
theorem gibbsDiagC_insert (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ) (z : ℂ) :
    gibbsDiagC (insert p S) x z
      = gibbsDiagC S x z + z * gibbsDiagC S ((p : ℝ) * x) z := by
  classical
  have hdisj : Disjoint S.powerset (S.powerset.image (insert p)) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    rw [Finset.mem_powerset] at hT
    obtain ⟨T', _, rfl⟩ := Finset.mem_image.mp hT'
    exact hp (hT (Finset.mem_insert_self p T'))
  have hinj : ∀ T₁ ∈ S.powerset, ∀ T₂ ∈ S.powerset,
      insert p T₁ = insert p T₂ → T₁ = T₂ := by
    intro T₁ h₁ T₂ h₂ h
    rw [Finset.mem_powerset] at h₁ h₂
    have e₁ : (insert p T₁).erase p = T₁ :=
      Finset.erase_insert (fun hmem => hp (h₁ hmem))
    have e₂ : (insert p T₂).erase p = T₂ :=
      Finset.erase_insert (fun hmem => hp (h₂ hmem))
    rw [← e₁, ← e₂, h]
  rw [gibbsDiagC, Finset.powerset_insert, Finset.sum_union hdisj,
    Finset.sum_image hinj]
  have hterm : ∀ T ∈ S.powerset,
      z ^ (insert p T).card
          * ((Real.exp (-(x * ∏ q ∈ insert p T, (q : ℝ))) : ℝ) : ℂ)
        = z * (z ^ T.card
          * ((Real.exp (-((p : ℝ) * x * ∏ q ∈ T, (q : ℝ))) : ℝ) : ℂ)) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hpT : p ∉ T := fun hmem => hp (hT hmem)
    have harg : -(x * ∏ q ∈ insert p T, (q : ℝ))
        = -((p : ℝ) * x * ∏ q ∈ T, (q : ℝ)) := by
      rw [Finset.prod_insert hpT]
      ring
    rw [Finset.card_insert_of_notMem hpT, harg, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rfl

/-- On the closed right half-plane the shifted point is at distance at least one. -/
theorem one_le_norm_one_add_of_re_nonneg (z : ℂ) (h : 0 ≤ z.re) : 1 ≤ ‖1 + z‖ := by
  have hsq : (1 : ℝ) ≤ Complex.normSq (1 + z) := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith [h, sq_nonneg z.im, sq_nonneg z.re]
  have e := Complex.normSq_eq_norm_sq (1 + z)
  nlinarith [norm_nonneg (1 + z), hsq, e]

/-- Right of the line `Re z = -1/2` the shift moves points away from the origin. -/
theorem norm_le_norm_one_add_of_re (z : ℂ) (h : -(1/2 : ℝ) ≤ z.re) : ‖z‖ ≤ ‖1 + z‖ := by
  have hsq : Complex.normSq z ≤ Complex.normSq (1 + z) := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith [h]
  have e1 := Complex.normSq_eq_norm_sq z
  have e2 := Complex.normSq_eq_norm_sq (1 + z)
  nlinarith [norm_nonneg z, norm_nonneg (1 + z), hsq, e1, e2]

/-- **The relative estimate.**  The gas deviates from the free gas by at most
`x·σ(m)·‖1+z‖^k`, with no exponential loss: the dilated scale of the cutoff recursion is
absorbed by `1 + p‖z‖ ≤ (1+p)‖1+z‖`. -/
theorem norm_gibbsDiagC_sub_free_le (S : Finset ℕ) :
    ∀ (x : ℝ), 0 ≤ x → ∀ z : ℂ, 1 ≤ ‖1 + z‖ → ‖z‖ ≤ ‖1 + z‖ →
      ‖gibbsDiagC S x z - (1 + z) ^ S.card‖
        ≤ x * (∏ p ∈ S, (1 + (p : ℝ))) * ‖1 + z‖ ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro x hx z _ _
    rw [gibbsDiagC_empty]
    simp only [Finset.card_empty, pow_zero, Finset.prod_empty, mul_one]
    have hrw : ((Real.exp (-x) : ℝ) : ℂ) - 1 = ((Real.exp (-x) - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hrw, Complex.norm_real, Real.norm_eq_abs]
    have h3 : Real.exp (-x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have h4 : 1 - x ≤ Real.exp (-x) := by
      have h5 := Real.add_one_le_exp (-x)
      linarith
    rw [abs_le]
    constructor <;> linarith
  | insert p S hp ih =>
    intro x hx z h1 h2
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hpx : 0 ≤ (p : ℝ) * x := mul_nonneg hp0 hx
    have hE : gibbsDiagC (insert p S) x z - (1 + z) ^ (insert p S).card
        = (gibbsDiagC S x z - (1 + z) ^ S.card)
          + z * (gibbsDiagC S ((p : ℝ) * x) z - (1 + z) ^ S.card) := by
      rw [gibbsDiagC_insert p S hp, Finset.card_insert_of_notMem hp, pow_succ]
      ring
    rw [hE, Finset.prod_insert hp, Finset.card_insert_of_notMem hp, pow_succ]
    have hb1 := ih x hx z h1 h2
    have hb2 := ih ((p : ℝ) * x) hpx z h1 h2
    have hb2' : ‖z‖ * ‖gibbsDiagC S ((p : ℝ) * x) z - (1 + z) ^ S.card‖
        ≤ ‖z‖ * ((p : ℝ) * x * (∏ q ∈ S, (1 + (q : ℝ))) * ‖1 + z‖ ^ S.card) :=
      mul_le_mul_of_nonneg_left hb2 (norm_nonneg z)
    have hkey : 1 + (p : ℝ) * ‖z‖ ≤ (1 + (p : ℝ)) * ‖1 + z‖ := by
      have hd : 0 ≤ (p : ℝ) * (‖1 + z‖ - ‖z‖) := mul_nonneg hp0 (by linarith)
      nlinarith [hd, h1]
    have hcoef : (0 : ℝ) ≤ x * (∏ q ∈ S, (1 + (q : ℝ))) * ‖1 + z‖ ^ S.card := by
      have hG : (0 : ℝ) ≤ ∏ q ∈ S, (1 + (q : ℝ)) :=
        Finset.prod_nonneg fun q _ => by positivity
      have hN : (0 : ℝ) ≤ ‖1 + z‖ ^ S.card := by positivity
      exact mul_nonneg (mul_nonneg hx hG) hN
    have hmul := mul_le_mul_of_nonneg_left hkey hcoef
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul]
    refine le_trans (add_le_add hb1 hb2') ?_
    calc x * (∏ q ∈ S, (1 + (q : ℝ))) * ‖1 + z‖ ^ S.card
            + ‖z‖ * ((p : ℝ) * x * (∏ q ∈ S, (1 + (q : ℝ))) * ‖1 + z‖ ^ S.card)
        = (x * (∏ q ∈ S, (1 + (q : ℝ))) * ‖1 + z‖ ^ S.card)
            * (1 + (p : ℝ) * ‖z‖) := by ring
      _ ≤ (x * (∏ q ∈ S, (1 + (q : ℝ))) * ‖1 + z‖ ^ S.card)
            * ((1 + (p : ℝ)) * ‖1 + z‖) := hmul
      _ = x * ((1 + (p : ℝ)) * ∏ q ∈ S, (1 + (q : ℝ)))
            * (‖1 + z‖ ^ S.card * ‖1 + z‖) := by ring

/-- **Hurwitz stability of the gas for every `k`.**  If `x·σ(m) < 1`, where
`σ(m) = ∏(1+p)`, the gas has no zero in the closed right half-plane. -/
theorem gibbsDiagC_ne_zero_of_sigma (S : Finset ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hσ : x * (∏ p ∈ S, (1 + (p : ℝ))) < 1)
    (z : ℂ) (hz : 0 ≤ z.re) :
    gibbsDiagC S x z ≠ 0 := by
  intro hzero
  have h1 : 1 ≤ ‖1 + z‖ := one_le_norm_one_add_of_re_nonneg z hz
  have h2 : ‖z‖ ≤ ‖1 + z‖ := norm_le_norm_one_add_of_re z (by linarith)
  have hb := norm_gibbsDiagC_sub_free_le S x hx z h1 h2
  rw [hzero, zero_sub, norm_neg, norm_pow] at hb
  have hNk : (0 : ℝ) < ‖1 + z‖ ^ S.card := by
    have : (0 : ℝ) < ‖1 + z‖ := by linarith
    positivity
  nlinarith [hb, hNk, hσ, mul_pos hNk (sub_pos.mpr hσ)]

/-- **The localization dichotomy.**  Under `x·σ(m) < 1` every zero of the gas either lies
in the parity cluster `‖z+1‖ < 1` or strictly left of the line `Re z = -1/2`: the
intervening strip is zero-free. -/
theorem gibbs_zero_localization (S : Finset ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hσ : x * (∏ p ∈ S, (1 + (p : ℝ))) < 1)
    (z : ℂ) (hzero : gibbsDiagC S x z = 0) :
    ‖1 + z‖ < 1 ∨ z.re < -(1/2 : ℝ) := by
  by_contra hcon
  rw [not_or, not_lt, not_lt] at hcon
  obtain ⟨h1, hre⟩ := hcon
  have h2 : ‖z‖ ≤ ‖1 + z‖ := norm_le_norm_one_add_of_re z hre
  have hb := norm_gibbsDiagC_sub_free_le S x hx z h1 h2
  rw [hzero, zero_sub, norm_neg, norm_pow] at hb
  have hNk : (0 : ℝ) < ‖1 + z‖ ^ S.card := by
    have : (0 : ℝ) < ‖1 + z‖ := by linarith
    positivity
  nlinarith [hb, hNk, hσ, mul_pos hNk (sub_pos.mpr hσ)]

end RHTower.GibbsGas
