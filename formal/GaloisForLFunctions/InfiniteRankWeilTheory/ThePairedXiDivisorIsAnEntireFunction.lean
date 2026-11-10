import GaloisForLFunctions.InfiniteRankWeilTheory.ThePairedXiDivisorApproachesTheLine
import GaloisForLFunctions.HTGeometry.CanonicalProductSubquadraticType

/-!
# Entire realization of the paired Xi divisor

The genus-one product of the paired quartets is real and even. Every
prescribed zero is simple, and there are no other zeros. Reciprocal-power
summability bounds its growth by `exp(Cₚ |z|ᵖ)` for every `1<p≤2`.
-/

noncomputable section
open Complex Set Filter Topology
open scoped ComplexConjugate
open _root_.RHTower

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The normalized centered entire function of the paired Xi divisor. -/
def pairedXiProduct : ℂ → ℂ := canonicalProductE1Indexed pairedXiPoint

theorem analytic_pairedXiProduct : AnalyticOnNhd ℂ pairedXiProduct univ :=
  canonicalProductE1Indexed_analytic pairedXiPoint pairedXiPoint_ne_zero
    summable_pairedXiPoint_inv_sq

theorem pairedXiProduct_zero : pairedXiProduct 0 = 1 :=
  canonicalProductE1Indexed_zero

theorem pairedXiProduct_eq_zero_iff (w : ℂ) :
    pairedXiProduct w = 0 ↔ ∃ q : ℕ × Bool × Bool, pairedXiPoint q = w := by
  constructor
  · intro hw
    by_contra hnone
    exact (canonicalProductE1Indexed_ne_zero pairedXiPoint pairedXiPoint_ne_zero
      summable_pairedXiPoint_inv_sq (fun q h => hnone ⟨q, h.symm⟩)) hw
  · rintro ⟨q, rfl⟩
    unfold pairedXiProduct canonicalProductE1Indexed
    exact tprod_of_exists_eq_zero ⟨q, by
      rw [div_self (pairedXiPoint_ne_zero q), weierstrassE1_one]⟩

/-- Negation exchanges both signs of a quartet. -/
def pairedXiNegEquiv : (ℕ × Bool × Bool) ≃ (ℕ × Bool × Bool) where
  toFun q := (q.1, !q.2.1, !q.2.2)
  invFun q := (q.1, !q.2.1, !q.2.2)
  left_inv q := by rcases q with ⟨n, b, c⟩; cases b <;> cases c <;> rfl
  right_inv q := by rcases q with ⟨n, b, c⟩; cases b <;> cases c <;> rfl

/-- Conjugation exchanges only the vertical sign. -/
def pairedXiConjEquiv : (ℕ × Bool × Bool) ≃ (ℕ × Bool × Bool) where
  toFun q := (q.1, q.2.1, !q.2.2)
  invFun q := (q.1, q.2.1, !q.2.2)
  left_inv q := by rcases q with ⟨n, b, c⟩; cases c <;> rfl
  right_inv q := by rcases q with ⟨n, b, c⟩; cases c <;> rfl

theorem pairedXiPoint_neg (q : ℕ × Bool × Bool) :
    pairedXiPoint (pairedXiNegEquiv q) = -pairedXiPoint q := by
  rcases q with ⟨n, b, c⟩
  cases b <;> cases c <;> simp [pairedXiPoint, pairedXiNegEquiv, quartetSign] <;> ring

theorem pairedXiPoint_conj (q : ℕ × Bool × Bool) :
    pairedXiPoint (pairedXiConjEquiv q) = conj (pairedXiPoint q) := by
  rcases q with ⟨n, b, c⟩
  cases b <;> cases c <;> simp [pairedXiPoint, pairedXiConjEquiv, quartetSign] <;> ring

theorem pairedXiProduct_neg (w : ℂ) : pairedXiProduct (-w) = pairedXiProduct w := by
  unfold pairedXiProduct canonicalProductE1Indexed
  calc
    _ = ∏' q, weierstrassE1 (w / pairedXiPoint (pairedXiNegEquiv q)) := by
      apply tprod_congr
      intro q
      rw [pairedXiPoint_neg]
      congr 1
      ring
    _ = _ := pairedXiNegEquiv.tprod_eq
      (fun q : ℕ × Bool × Bool => weierstrassE1 (w / pairedXiPoint q))

theorem pairedXiProduct_conj (w : ℂ) : pairedXiProduct (conj w) = conj (pairedXiProduct w) := by
  have h := (multipliable_canonicalProductE1Indexed pairedXiPoint_ne_zero
    summable_pairedXiPoint_inv_sq w).hasProd.map (starRingEnd ℂ) Complex.continuous_conj
  change HasProd (fun q => conj (weierstrassE1 (w / pairedXiPoint q)))
    (conj (pairedXiProduct w)) at h
  rw [← h.tprod_eq]
  unfold pairedXiProduct canonicalProductE1Indexed
  calc
    _ = ∏' q, weierstrassE1 (conj w / pairedXiPoint (pairedXiConjEquiv q)) :=
      (pairedXiConjEquiv.tprod_eq
        (fun q : ℕ × Bool × Bool => weierstrassE1 (conj w / pairedXiPoint q))).symm
    _ = _ := by
      apply tprod_congr
      intro q
      rw [pairedXiPoint_conj]
      simp only [weierstrassE1, map_mul, map_sub, map_one, map_div₀, Complex.exp_conj]

/-- The construction separates every multiplicity copy into a simple zero. -/
theorem analyticOrderAt_pairedXiProduct (q : ℕ × Bool × Bool) :
    analyticOrderAt pairedXiProduct (pairedXiPoint q) = 1 := by
  rw [pairedXiProduct, analyticOrderAt_canonicalProductE1Indexed
    pairedXiPoint_ne_zero locallyFinite_pairedXiPoint summable_pairedXiPoint_inv_sq
    (pairedXiPoint_ne_zero q)]
  have heq : {r : ℕ × Bool × Bool | pairedXiPoint r = pairedXiPoint q} = {q} := by
    ext r
    exact pairedXiPoint_injective.eq_iff
  rw [heq, Set.ncard_singleton]
  rfl

/-- Order at most one, expressed by its full family of power envelopes. -/
theorem pairedXiProduct_growth {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖pairedXiProduct w‖ ≤ Real.exp (C * ‖w‖ ^ p) := by
  refine ⟨2 * ∑' q : ℕ × Bool × Bool, ‖pairedXiPoint q‖ ^ (-p), by positivity, fun w => ?_⟩
  exact canonicalProduct_norm_le_exp_rpow pairedXiPoint pairedXiPoint_ne_zero
    summable_pairedXiPoint_inv_sq hp.le hp₂ (summable_pairedXiPoint_rpow_neg hp) w

/-- The paired entire function in the usual functional-equation coordinate. -/
def pairedXiModel (s : ℂ) : ℂ := pairedXiProduct (s - 1 / 2)

theorem differentiable_pairedXiModel : Differentiable ℂ pairedXiModel := by
  intro s
  exact ((analytic_pairedXiProduct _ (mem_univ _)).differentiableAt.comp s
    (differentiableAt_id.sub_const (1 / 2)))

theorem pairedXiModel_one_sub (s : ℂ) : pairedXiModel (1 - s) = pairedXiModel s := by
  unfold pairedXiModel
  rw [show (1 : ℂ) - s - 1 / 2 = -(s - 1 / 2) by ring, pairedXiProduct_neg]

theorem pairedXiModel_conj (s : ℂ) : pairedXiModel (conj s) = conj (pairedXiModel s) := by
  unfold pairedXiModel
  rw [show conj s - 1 / 2 = conj (s - 1 / 2) by simp, pairedXiProduct_conj]

theorem pairedXiModel_half : pairedXiModel (1 / 2) = 1 := by
  rw [pairedXiModel, sub_self, pairedXiProduct_zero]

theorem pairedXiModel_eq_zero_iff (s : ℂ) :
    pairedXiModel s = 0 ↔ ∃ q : ℕ × Bool × Bool, (1 / 2 : ℂ) + pairedXiPoint q = s := by
  rw [pairedXiModel, pairedXiProduct_eq_zero_iff]
  constructor
  · rintro ⟨q, h⟩
    exact ⟨q, by rw [h]; ring⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, by ring⟩

theorem analyticOrderAt_pairedXiModel (q : ℕ × Bool × Bool) :
    analyticOrderAt pairedXiModel ((1 / 2 : ℂ) + pairedXiPoint q) = 1 := by
  have hd : deriv (fun s : ℂ => s - 1 / 2) ((1 / 2 : ℂ) + pairedXiPoint q) ≠ 0 := by
    rw [((hasDerivAt_id' _).sub_const (1 / 2)).deriv]
    exact one_ne_zero
  change analyticOrderAt (pairedXiProduct ∘ (fun s : ℂ => s - 1 / 2))
    ((1 / 2 : ℂ) + pairedXiPoint q) = 1
  rw [analyticOrderAt_comp_of_deriv_ne_zero (f := pairedXiProduct)
    (by fun_prop) hd, add_sub_cancel_left, analyticOrderAt_pairedXiProduct]

#print axioms pairedXiProduct_conj
#print axioms pairedXiProduct_growth
#print axioms pairedXiModel_eq_zero_iff
#print axioms analyticOrderAt_pairedXiModel

end GaloisForLFunctions.InfiniteRankWeilTheory
