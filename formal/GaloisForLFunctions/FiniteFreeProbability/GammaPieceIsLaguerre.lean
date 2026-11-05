import GaloisForLFunctions.FiniteFreeProbability.GammaThetaSzegoFactorization
import GaloisForLFunctions.HTGeometry.PoleUnitGammaBase
import GaloisForLFunctions.HTGeometry.MomentRealRootedness
import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentCollapse

/-!
# The Gamma piece is a Laguerre polynomial: its roots are real and negative

The Gamma piece of the source-faithful factorization `J^{d,n} = κ Γ_{n,d} ⊠_d Θ_{n,d}` is
`Γ_{n,d}(X) = Σ_j C(d,j) X^j/(4^j (n+1/2)_j) = P_{d,c}(−X/4)` with `c = n + 1/2`, where

`P_{d,c}(x) = Σ_j (−1)^j C(d,j) x^j/(c)_j`

is the Laguerre polynomial `L_d^{(c−1)}` up to normalization. Against the Gamma moments
`s_m = (c)_m` (the moments of `x^{c−1}e^{−x}/Γ(c)` on `(0, ∞)`),

`⟪P_{d,c}, X^k⟫ = Σ_j (−1)^j C(d,j) (c + j)_k = 0`  for `k < d`,

since alternating binomial sums annihilate polynomials in `j` of degree `< d`. So `P_{d,c}` is a
multiple of the monic orthogonal polynomial of a positive definite moment form, whose roots are
real.

**Theorem.** `Γ_{n,d}` splits over `ℝ` and is positive on `[0, ∞)`, so all its roots are negative:
the Gamma piece is admissible for Szegő's composition theorem, and the obstruction to certifying
`J^{d,n}` through the ⊠ split lies entirely in the theta piece.
-/

open Polynomial

namespace FiniteFreeProbability

noncomputable section

local notation "ρ" => GaloisForLFunctions.HTGeometry.gammaShapeMoment

/-- The orthogonal polynomial `P_{d,c}(x) = Σ_j (−1)^j C(d,j) x^j/(c)_j`. -/
def laguerreOrtho (c : ℝ) (d : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1), C ((-1) ^ j * (d.choose j : ℝ) / ρ c j) * X ^ j

/-- **Alternating binomial sums annihilate polynomials of degree `< d`.** -/
theorem sum_neg_one_pow_choose_mul_eval {d : ℕ} {Q : ℝ[X]} (hQ : Q.natDegree < d) :
    ∑ j ∈ Finset.range (d + 1), (-1 : ℝ) ^ j * (d.choose j : ℝ) * Q.eval (j : ℝ) = 0 := by
  have hpow : ∀ m < d,
      ∑ j ∈ Finset.range (d + 1), (-1 : ℝ) ^ j * (d.choose j : ℝ) * (j : ℝ) ^ m = 0 := by
    intro m hm
    have h := GaloisForLFunctions.HTGeometry.alternating_binomial_sum_pow_eq_zero (R := ℝ) hm
    have hre : ∑ j ∈ Finset.range (d + 1), (-1 : ℝ) ^ j * (d.choose j : ℝ) * (j : ℝ) ^ m =
        (-1) ^ d * ∑ j ∈ Finset.range (d + 1),
          ((-1 : ℝ) ^ (d - j) * (d.choose j : ℝ)) * (j : ℝ) ^ m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hs : (-1 : ℝ) ^ d * (-1) ^ (d - j) = (-1) ^ j := by
        rw [← pow_add, show d + (d - j) = 2 * (d - j) + j by omega, pow_add, pow_mul, neg_one_sq,
          one_pow, one_mul]
      rw [← hs]; ring
    rw [hre, h, mul_zero]
  simp_rw [eval_eq_sum_range' hQ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [show ∑ j ∈ Finset.range (d + 1), (-1 : ℝ) ^ j * (d.choose j : ℝ) * (Q.coeff m * (j : ℝ) ^ m)
      = Q.coeff m * ∑ j ∈ Finset.range (d + 1), (-1 : ℝ) ^ j * (d.choose j : ℝ) * (j : ℝ) ^ m by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring,
    hpow m (Finset.mem_range.1 hm), mul_zero]

/-- `(c)_{j+k} = (c)_j · Q_k(j)` with `Q_k = Π_{i<k} (X + c + i)`. -/
theorem gammaShapeMoment_add (c : ℝ) (j k : ℕ) :
    ρ c (j + k) = ρ c j *
      (∏ i ∈ Finset.range k, (X + C (c + i))).eval (j : ℝ) := by
  simp only [GaloisForLFunctions.HTGeometry.gammaShapeMoment, Finset.prod_range_add, eval_prod,
    eval_add, eval_X, eval_C]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast; ring

theorem natDegree_prod_X_add_C_le (c : ℝ) (k : ℕ) :
    (∏ i ∈ Finset.range k, (X + C (c + i))).natDegree ≤ k := by
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum fun (i : ℕ) _ => (natDegree_X_add_C (c + (i : ℝ))).le).trans ?_
  simp

/-- **Orthogonality.** `⟪P_{d,c}, X^k⟫ = 0` for `k < d`. -/
theorem momentInner_laguerreOrtho_X_pow {c : ℝ} (hc : 0 < c) {d k : ℕ} (hk : k < d) :
    HTGeometry.momentInner (ρ c) (laguerreOrtho c d) (X ^ k) = 0 := by
  rw [HTGeometry.momentInner_def, laguerreOrtho, Finset.sum_mul,
    HTGeometry.momentFunctional_finset_sum]
  have hterm : ∀ j ∈ Finset.range (d + 1),
      HTGeometry.momentFunctional (ρ c) (C ((-1) ^ j * (d.choose j : ℝ) / ρ c j) * X ^ j * X ^ k) =
        (-1 : ℝ) ^ j * (d.choose j : ℝ) *
          (∏ i ∈ Finset.range k, (X + C (c + i))).eval (j : ℝ) := fun j _ => by
    rw [mul_assoc, ← pow_add, C_mul_X_pow_eq_monomial, HTGeometry.momentFunctional_monomial,
      gammaShapeMoment_add]
    have hρ : ρ c j ≠ 0 := (Finset.prod_pos fun i _ => by positivity).ne'
    field_simp
  rw [Finset.sum_congr rfl hterm]
  exact sum_neg_one_pow_choose_mul_eval
    (lt_of_le_of_lt (natDegree_prod_X_add_C_le c k) hk)

/-- `P_{d,c}` is orthogonal to every polynomial of degree `< d`. -/
theorem momentInner_laguerreOrtho_eq_zero {c : ℝ} (hc : 0 < c) {d : ℕ} {g : ℝ[X]}
    (hg : g.degree < d) : HTGeometry.momentInner (ρ c) (laguerreOrtho c d) g = 0 := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  have hgd : g.natDegree < d := by
    rw [degree_eq_natDegree hg0] at hg; exact_mod_cast hg
  rw [g.as_sum_range' d hgd, HTGeometry.momentInner_sum_right]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, HTGeometry.momentInner_smul_right,
    momentInner_laguerreOrtho_X_pow hc (Finset.mem_range.1 hk), mul_zero]

theorem coeff_laguerreOrtho (c : ℝ) {d k : ℕ} (hk : k ≤ d) :
    (laguerreOrtho c d).coeff k = (-1) ^ k * (d.choose k : ℝ) / ρ c k :=
  coeff_sum_range_C_mul_X_pow _ hk

theorem degree_laguerreOrtho {c : ℝ} (hc : 0 < c) (d : ℕ) :
    (laguerreOrtho c d).degree = d := by
  refine degree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · refine (degree_sum_le _ _).trans (Finset.sup_le fun j hj => ?_)
    exact (degree_C_mul_X_pow_le _ _).trans
      (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  · rw [coeff_laguerreOrtho c le_rfl, Nat.choose_self, Nat.cast_one, mul_one]
    exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Finset.prod_pos fun i _ => by positivity).ne'

/-- **`P_{d,c}` is a multiple of the monic orthogonal polynomial.** -/
theorem laguerreOrtho_eq {c : ℝ} (hc : 0 < c) (d : ℕ) :
    laguerreOrtho c d = C ((laguerreOrtho c d).leadingCoeff) *
      HTGeometry.monicOrtho (ρ c) d := by
  have h := GaloisForLFunctions.HTGeometry.gammaShapeMoment_positiveMomentForm hc
  have hP0 : laguerreOrtho c d ≠ 0 := by
    intro h0; have := degree_laguerreOrtho hc d; rw [h0, degree_zero] at this
    exact WithBot.bot_ne_coe this
  set P := laguerreOrtho c d
  set M := HTGeometry.monicOrtho (ρ c) d
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hP0
  have hMdeg : M.degree = d := HTGeometry.monicOrtho_degree _ d
  have hMm : M.Monic := HTGeometry.monicOrtho_monic _ d
  have hdeg : P.degree = (C P.leadingCoeff * M).degree := by
    rw [degree_C_mul hlc, hMdeg, degree_laguerreOrtho hc]
  have hlead : P.leadingCoeff = (C P.leadingCoeff * M).leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C, hMm.leadingCoeff, mul_one]
  set R := P - C P.leadingCoeff * M
  have hR : R.degree < d := by
    rw [← degree_laguerreOrtho hc d]
    exact degree_sub_lt hdeg hP0 hlead
  have horth : ∀ g : ℝ[X], g.degree < d → HTGeometry.momentInner (ρ c) R g = 0 := fun g hg => by
    rw [HTGeometry.momentInner_sub_left, ← smul_eq_C_mul, HTGeometry.momentInner_smul_left,
      momentInner_laguerreOrtho_eq_zero hc hg,
      HTGeometry.monicOrtho_inner_eq_zero_of_degree_lt h d d le_rfl g hg, mul_zero, sub_zero]
  by_contra hne
  have hR0 : R ≠ 0 := sub_ne_zero.2 hne
  have := h.pos_of_ne_zero R hR0
  rw [horth R hR] at this
  exact lt_irrefl _ this

/-- Every complex root of `P_{d,c}` is real. -/
theorem laguerreOrtho_root_im_eq_zero {c : ℝ} (hc : 0 < c) (d : ℕ) {z : ℂ}
    (hz : aeval z (laguerreOrtho c d) = 0) : z.im = 0 := by
  rcases d with _ | m
  · simp [laguerreOrtho] at hz
  rw [laguerreOrtho_eq hc, map_mul, aeval_C] at hz
  have hlc : (laguerreOrtho c (m + 1)).leadingCoeff ≠ 0 := by
    rw [Ne, leadingCoeff_eq_zero]; intro h0
    have := degree_laguerreOrtho hc (m + 1); rw [h0, degree_zero] at this
    exact WithBot.bot_ne_coe this
  rcases mul_eq_zero.1 hz with h0 | h0
  · exact absurd h0 (by simpa using hlc)
  · exact HTGeometry.monicOrtho_root_im_eq_zero
      (GaloisForLFunctions.HTGeometry.gammaShapeMoment_positiveMomentForm hc) m h0

/-! ## The Gamma piece -/

/-- `Γ_{n,d}(z) = P_{d,n+1/2}(−z/4)`. -/
theorem aeval_gammaPiece (n d : ℕ) (z : ℂ) :
    aeval z (gammaPiece n d) = aeval (-z / 4) (laguerreOrtho ((n : ℝ) + 1 / 2) d) := by
  simp only [gammaPiece, laguerreOrtho, map_sum, map_mul, aeval_C, map_pow, aeval_X,
    Complex.coe_algebraMap]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hr : RHTower.ScaledHypergeometric.rising ((n : ℝ) + 1 / 2) j = ρ ((n : ℝ) + 1 / 2) j := rfl
  rw [hr]
  have hsq : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  calc _ = ((-1 : ℂ) ^ j * (-1) ^ j) *
        ((d.choose j : ℂ) * z ^ j / (4 ^ j * (ρ ((n : ℝ) + 1 / 2) j : ℂ))) := by
        rw [hsq]; push_cast; ring
    _ = _ := by
        rw [show (-z / 4) ^ j = (-1) ^ j * (z ^ j / 4 ^ j) by rw [neg_div, neg_pow, div_pow]]
        push_cast; ring

/-- **The Gamma piece is real-rooted.** -/
theorem splits_gammaPiece (n d : ℕ) : (gammaPiece n d).Splits := by
  refine HTGeometry.splits_of_forall_aeval_im_eq_zero d _ ?_ fun z hz => ?_
  · refine (natDegree_sum_le_of_forall_le _ _ fun j hj => ?_)
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  rw [aeval_gammaPiece] at hz
  have := laguerreOrtho_root_im_eq_zero (by positivity) d hz
  simp only [Complex.div_ofNat_im, Complex.neg_im] at this
  linarith

/-- **The Gamma piece is positive on `[0, ∞)`**: all its roots are negative. -/
theorem eval_gammaPiece_pos (n d : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 < (gammaPiece n d).eval x := by
  rw [gammaPiece, eval_finsetSum, Finset.sum_range_succ']
  simp only [eval_mul, eval_C, eval_pow, eval_X, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one, RHTower.ScaledHypergeometric.rising_zero]
  have hrest : 0 ≤ ∑ j ∈ Finset.range d, (d.choose (j + 1) : ℝ) /
      (4 ^ (j + 1) * RHTower.ScaledHypergeometric.rising ((n : ℝ) + 1 / 2) (j + 1)) * x ^ (j + 1) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (by positivity)
      (mul_nonneg (by positivity) (RHTower.ScaledHypergeometric.rising_pos (by positivity) _).le))
      (pow_nonneg hx _)
  linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.splits_gammaPiece
#print axioms FiniteFreeProbability.eval_gammaPiece_pos
