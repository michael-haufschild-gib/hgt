import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationAbsolute
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationTwist

/-!
# Absolute convergence and exact regrouping of valuation twists

Square energy pays convergence in the square-root disk. Regrouping itself
requires only absolute convergence of the twisted series, so the convolution
exponential can supply it directly for the actual source.
-/

open Complex
noncomputable section
namespace RHTower.WeilSingularArithmetic

private theorem weighted_valuation_term {p : ℕ} (hp : p.Prime) (z : ℂ)
    (f : ℕ → ℂ) (s : ℂ) (n k : ℕ) :
    z ^ k * LSeries.term (valuationPart p k f) s n =
      if k = n.factorization p then LSeries.term (valuationTwist p z f) s n else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · by_cases hk : k = n.factorization p
    · subst k
      simp [LSeries.term_of_ne_zero hn, valuationPart, valuationMask_eq_factorization hp hn,
        valuationTwist, mul_div_assoc]
    · simp [LSeries.term_of_ne_zero hn, valuationPart,
        valuationMask_eq_factorization hp hn, hk, Ne.symm hk]

private theorem valuation_column_hasSum {p : ℕ} (hp : p.Prime) (z : ℂ)
    (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    HasSum (fun k => z ^ k * LSeries.term (valuationPart p k f) s n)
      (LSeries.term (valuationTwist p z f) s n) := by
  simp_rw [weighted_valuation_term hp]
  exact hasSum_ite_eq _ _

private theorem valuation_column_norm_hasSum {p : ℕ} (hp : p.Prime) (z : ℂ)
    (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    HasSum (fun k => ‖z ^ k * LSeries.term (valuationPart p k f) s n‖)
      ‖LSeries.term (valuationTwist p z f) s n‖ := by
  simp_rw [weighted_valuation_term hp, apply_ite norm, norm_zero]
  exact hasSum_ite_eq _ _

theorem summable_valuationTwist_of_square {p : ℕ} (hp : p.Prime)
    {f : ℕ → ℂ} {s : ℝ} (hs : 1 < s) (hf : LSeriesSummable f (s : ℂ))
    (he : Summable (fun n : ℕ => ‖f n‖ ^ 2 / (n : ℝ) ^ s))
    {z : ℂ} (hz : ‖z‖ < Real.sqrt (p : ℝ)) :
    LSeriesSummable (valuationTwist p z f) (s : ℂ) := by
  let C := Real.sqrt ((∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
    ∑' n : ℕ, 1 / (n : ℝ) ^ s)
  let rho := (Real.sqrt (p : ℝ))⁻¹
  have hrho : 0 ≤ rho := by dsimp [rho]; positivity
  have hr : ‖z‖ * rho < 1 := by
    dsimp [rho]
    rw [← div_eq_mul_inv, div_lt_one (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos))]
    exact hz
  let g : ℕ × ℕ → ℂ := fun kn => z ^ kn.1 *
    LSeries.term (valuationPart p kn.1 f) (s : ℂ) kn.2
  have hnorm (k n : ℕ) : ‖g (k, n)‖ = ‖z‖ ^ k *
      ‖LSeries.term (valuationPart p k f) (s : ℂ) n‖ := by
    simp only [g, norm_mul, norm_pow]
  have hrow (k : ℕ) : Summable (fun n => ‖g (k, n)‖) := by
    simp_rw [hnorm]
    exact (summable_valuationPart p k hf).norm.mul_left _
  have hrows : Summable (fun k => ∑' n, ‖g (k, n)‖) := by
    have hgeom := (summable_geometric_of_lt_one (mul_nonneg (norm_nonneg z) hrho) hr).mul_left C
    refine hgeom.of_nonneg_of_le (fun k => tsum_nonneg fun n => norm_nonneg _) fun k => ?_
    simp_rw [hnorm]
    rw [tsum_mul_left]
    calc
      _ ≤ ‖z‖ ^ k * (C * rho ^ k) :=
        mul_le_mul_of_nonneg_left (absolute_valuation_LSeries_le hp hs hf he k) (by positivity)
      _ = C * (‖z‖ * rho) ^ k := by rw [mul_pow]; ring
  have hgs : Summable g := Summable.of_norm
    ((summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨hrow, hrows⟩)
  exact hgs.prod_symm.prod.congr fun n => (valuation_column_hasSum hp z f (s : ℂ) n).tsum_eq

theorem LSeries_valuationTwist_eq_tsum {p : ℕ} (hp : p.Prime) (z : ℂ)
    {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable (valuationTwist p z f) s) :
    LSeries (valuationTwist p z f) s =
      ∑' k : ℕ, z ^ k * LSeries (valuationPart p k f) s := by
  let g : ℕ × ℕ → ℂ := fun kn => z ^ kn.1 * LSeries.term (valuationPart p kn.1 f) s kn.2
  have hnorm : Summable (fun nk : ℕ × ℕ => ‖g (nk.2, nk.1)‖) := by
    refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨?_, ?_⟩
    · exact fun n => (valuation_column_norm_hasSum hp z f s n).summable
    · exact hf.norm.congr fun n => (valuation_column_norm_hasSum hp z f s n).tsum_eq.symm
  have hgs : Summable g := Summable.of_norm hnorm.prod_symm
  have hterm (n : ℕ) : LSeries.term (valuationTwist p z f) s n = ∑' k, g (k, n) :=
    (valuation_column_hasSum hp z f s n).tsum_eq.symm
  unfold LSeries
  rw [funext hterm]
  rw [Summable.tsum_comm' (f := fun k n => g (k, n)) hgs
    (fun k => hgs.prod_factor k) (fun n => hgs.prod_symm.prod_factor n)]
  exact tsum_congr fun k => by dsimp only [g]; exact tsum_mul_left

end RHTower.WeilSingularArithmetic
