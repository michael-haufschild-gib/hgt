import GaloisForLFunctions.HTGeometry.TopSymbolReduction
import GaloisForLFunctions.HTGeometry.WimanValironSmallDefect

/-!
# The top symbol is small at a Wiman--Valiron point

Combining the algebraic division identity with the analytic supply: if a transcendental entire
function satisfies an algebraic differential relation of total degree at most `d` with polynomial
coefficients, then at suitable radii — beyond every bound — the top symbol evaluated at
`T = f'(z)/f(z)` is arbitrarily small, while `z f'/f` is within a prescribed relative error of the
central index.

Both dominance statements are needed and both are available: the modulus of the function at the
selected point beats any prescribed power of the radius *and* any prescribed power of the central
index, and the coefficient weight is bounded by the larger of the two raised to the total degree.
-/

open Finset Complex Set

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- **The top symbol vanishes in the limit along Wiman--Valiron radii.**  For a transcendental
entire solution of an algebraic differential relation of total degree at most `d`, every `η > 0` and
`ε > 0` and every bound `R` admit a radius `e^y` past `R` and a point `z` on that circle at which the
top symbol has modulus at most `η` and the logarithmic derivative is within `ε` relative error of the
central index. -/
theorem exists_radius_norm_topSymbol_le
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (R : ℝ) :
    ∃ y, R ≤ y ∧ ∃ z : ℂ, ‖z‖ = Real.exp y ∧
      ‖∑ p ∈ S.filter (fun p => p.1 + p.2 = d),
          (A p).eval z * (deriv (coeffFun a) z / coeffFun a z) ^ p.2‖ ≤ η ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp y) : ℂ)‖
        ≤ ε * (centralIndex a (Real.exp y) : ℝ) := by
  classical
  set D : ℕ := S.sup (fun p => (A p).natDegree) with hDdef
  set K : ℝ := 1 + ∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖ with hKdef
  have hKsum : (0 : ℝ) ≤ ∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖ := by
    refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun i _ => norm_nonneg _
  have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; linarith
  have hKpos : (0 : ℝ) < K := by linarith
  set n : ℕ := D + d with hndef
  have hε2 : (0 : ℝ) < η / (K * (1 + ε) ^ n) := by positivity
  obtain ⟨y, hy, z, hz, hdom, hpow, hbound⟩ :=
    exists_radius_dominates_and_defect_le_eps ha hn₀ htrans hε hε2 n n (K / η + 1) (max R 0)
  have hy0 : (0 : ℝ) ≤ y := le_trans (le_max_right R 0) hy
  have hz1 : (1 : ℝ) ≤ ‖z‖ := by
    rw [hz]
    exact Real.one_le_exp hy0
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hzn : (0 : ℝ) < ‖z‖ ^ n := pow_pos hzpos n
  -- the function is large at the selected point
  have hfpos : (0 : ℝ) < ‖coeffFun a z‖ := by
    have h1 : (0 : ℝ) < (K / η + 1) * ‖z‖ ^ n := by positivity
    linarith
  have hfne : coeffFun a z ≠ 0 := norm_pos_iff.mp hfpos
  have hf1 : (1 : ℝ) ≤ ‖coeffFun a z‖ := by
    have h1 : (1 : ℝ) ≤ ‖z‖ ^ n := one_le_pow₀ hz1
    have h2 : (K / η + 1) * 1 ≤ (K / η + 1) * ‖z‖ ^ n := by
      have hc : (0 : ℝ) ≤ K / η + 1 := by positivity
      exact mul_le_mul_of_nonneg_left h1 hc
    have h3 : (1 : ℝ) ≤ K / η + 1 := by
      have hq : (0 : ℝ) < K / η := by positivity
      linarith
    linarith
  -- the two dominance facts in usable form
  have hνnn : (0 : ℝ) ≤ ((centralIndex a (Real.exp y) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdomz : ‖z‖ ^ n ≤ η / K * ‖coeffFun a z‖ := by
    have hstep : (K / η) * ‖z‖ ^ n ≤ ‖coeffFun a z‖ := by nlinarith [hdom, hzn]
    have hc : (0 : ℝ) < η / K := by positivity
    have h1 := mul_le_mul_of_nonneg_left hstep (le_of_lt hc)
    have h2 : (η / K) * (K / η * ‖z‖ ^ n) = ‖z‖ ^ n := by field_simp
    linarith [h1, h2.le, h2.ge]
  have hdomν : ((1 + ε) * ((centralIndex a (Real.exp y) : ℝ))) ^ n
      ≤ η / K * ‖coeffFun a z‖ := by
    have hexp : ((1 + ε) * ((centralIndex a (Real.exp y) : ℝ))) ^ n
        = (1 + ε) ^ n * ((centralIndex a (Real.exp y) : ℝ)) ^ n := by rw [mul_pow]
    have hpow' : (1 + ε) ^ n * ((centralIndex a (Real.exp y) : ℝ)) ^ n
        ≤ (1 + ε) ^ n * (η / (K * (1 + ε) ^ n) * ‖coeffFun a z‖) := by
      have hc : (0 : ℝ) ≤ (1 + ε) ^ n := by positivity
      exact mul_le_mul_of_nonneg_left hpow hc
    have hval : (1 + ε) ^ n * (η / (K * (1 + ε) ^ n) * ‖coeffFun a z‖)
        = η / K * ‖coeffFun a z‖ := by
      have hne : ((1 : ℝ) + ε) ^ n ≠ 0 := by positivity
      field_simp
    rw [hexp, ← hval]
    exact hpow'
  -- the logarithmic derivative is bounded
  have hT : ‖deriv (coeffFun a) z / coeffFun a z‖
      ≤ (1 + ε) * ((centralIndex a (Real.exp y) : ℝ)) := by
    have hsplit : z * deriv (coeffFun a) z / coeffFun a z
        = z * (deriv (coeffFun a) z / coeffFun a z) := by
      rw [mul_div_assoc]
    have hnorm : ‖z * deriv (coeffFun a) z / coeffFun a z‖
        ≤ (1 + ε) * ((centralIndex a (Real.exp y) : ℝ)) := by
      have h1 := norm_sub_norm_le (z * deriv (coeffFun a) z / coeffFun a z)
        ((centralIndex a (Real.exp y) : ℂ))
      have h2 : ‖((centralIndex a (Real.exp y) : ℕ) : ℂ)‖
          = ((centralIndex a (Real.exp y) : ℕ) : ℝ) := by
        simp
      rw [h2] at h1
      linarith [hbound, h1]
    rw [hsplit, norm_mul] at hnorm
    have hge : ‖deriv (coeffFun a) z / coeffFun a z‖
        ≤ ‖z‖ * ‖deriv (coeffFun a) z / coeffFun a z‖ := by
      have hnn : (0 : ℝ) ≤ ‖deriv (coeffFun a) z / coeffFun a z‖ := norm_nonneg _
      nlinarith [hz1, hnn]
    linarith
  -- the coefficient weight
  set Λ : ℝ := max ‖z‖ ((1 + ε) * ((centralIndex a (Real.exp y) : ℝ))) with hΛdef
  have hΛ1 : (1 : ℝ) ≤ Λ := le_trans hz1 (le_max_left _ _)
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have hΛz : ‖z‖ ≤ Λ := le_max_left _ _
  have hΛν : (1 + ε) * ((centralIndex a (Real.exp y) : ℝ)) ≤ Λ := le_max_right _ _
  have hΛn : Λ ^ n ≤ η / K * ‖coeffFun a z‖ := by
    rcases le_total ‖z‖ ((1 + ε) * ((centralIndex a (Real.exp y) : ℝ))) with hcase | hcase
    · have : Λ = (1 + ε) * ((centralIndex a (Real.exp y) : ℝ)) := max_eq_right hcase
      rw [this]
      exact hdomν
    · have : Λ = ‖z‖ := max_eq_left hcase
      rw [this]
      exact hdomz
  have hweight : ∀ p ∈ S, ‖(A p).eval z‖ * ‖deriv (coeffFun a) z / coeffFun a z‖ ^ p.2
      ≤ (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) * Λ ^ n := by
    intro p hp
    have h1 : ‖(A p).eval z‖
        ≤ (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) * ‖z‖ ^ (A p).natDegree :=
      norm_eval_le_of_one_le hz1
    have hdegp : (A p).natDegree ≤ D := Finset.le_sup (f := fun p => (A p).natDegree) hp
    have h2 : ‖z‖ ^ (A p).natDegree ≤ Λ ^ D := by
      calc ‖z‖ ^ (A p).natDegree ≤ Λ ^ (A p).natDegree := by
            exact pow_le_pow_left₀ (norm_nonneg _) hΛz _
        _ ≤ Λ ^ D := pow_le_pow_right₀ hΛ1 hdegp
    have hp2 : p.2 ≤ d := by
      have := hdeg p hp
      omega
    have h3 : ‖deriv (coeffFun a) z / coeffFun a z‖ ^ p.2 ≤ Λ ^ d := by
      calc ‖deriv (coeffFun a) z / coeffFun a z‖ ^ p.2 ≤ Λ ^ p.2 := by
            exact pow_le_pow_left₀ (norm_nonneg _) (le_trans hT hΛν) _
        _ ≤ Λ ^ d := pow_le_pow_right₀ hΛ1 hp2
    have hcs : (0 : ℝ) ≤ ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    have hsplitn : Λ ^ n = Λ ^ D * Λ ^ d := by rw [hndef, pow_add]
    calc ‖(A p).eval z‖ * ‖deriv (coeffFun a) z / coeffFun a z‖ ^ p.2
        ≤ ((∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) * ‖z‖ ^ (A p).natDegree)
            * Λ ^ d := by
          refine mul_le_mul h1 h3 (by positivity) (by positivity)
      _ ≤ ((∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) * Λ ^ D) * Λ ^ d := by
          have hmul : (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖)
              * ‖z‖ ^ (A p).natDegree
              ≤ (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) * Λ ^ D :=
            mul_le_mul_of_nonneg_left h2 hcs
          exact mul_le_mul_of_nonneg_right hmul (by positivity)
      _ = (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) * Λ ^ n := by
          rw [hsplitn]
          ring
  -- assemble
  refine ⟨y, le_trans (le_max_left R 0) hy, z, hz, ?_, hbound⟩
  have hmain := norm_topSymbol_le (A := fun p => (A p).eval z) (F := coeffFun a z)
    (W := deriv (coeffFun a) z) (d := d) hfne hf1 hdeg (hrel z)
  refine le_trans hmain ?_
  have hsub : ∑ p ∈ S.filter (fun p => ¬ p.1 + p.2 = d),
        ‖(A p).eval z‖ * ‖deriv (coeffFun a) z / coeffFun a z‖ ^ p.2
      ≤ K * Λ ^ n := by
    have hstep : ∑ p ∈ S.filter (fun p => ¬ p.1 + p.2 = d),
          ‖(A p).eval z‖ * ‖deriv (coeffFun a) z / coeffFun a z‖ ^ p.2
        ≤ ∑ p ∈ S, ‖(A p).eval z‖ * ‖deriv (coeffFun a) z / coeffFun a z‖ ^ p.2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro p _ _
      positivity
    have hstep2 : ∑ p ∈ S, ‖(A p).eval z‖ * ‖deriv (coeffFun a) z / coeffFun a z‖ ^ p.2
        ≤ ∑ p ∈ S, (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) * Λ ^ n :=
      Finset.sum_le_sum hweight
    have hstep3 : ∑ p ∈ S, (∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) * Λ ^ n
        = (∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) * Λ ^ n := by
      rw [Finset.sum_mul]
    have hstep4 : (∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) * Λ ^ n
        ≤ K * Λ ^ n := by
      have hΛn0 : (0 : ℝ) ≤ Λ ^ n := by positivity
      have : (∑ p ∈ S, ∑ i ∈ Finset.range ((A p).natDegree + 1), ‖(A p).coeff i‖) ≤ K := by
        rw [hKdef]; linarith
      exact mul_le_mul_of_nonneg_right this hΛn0
    linarith
  have hfinal : K * Λ ^ n / ‖coeffFun a z‖ ≤ η := by
    rw [div_le_iff₀ hfpos]
    have h1 : K * Λ ^ n ≤ K * (η / K * ‖coeffFun a z‖) :=
      mul_le_mul_of_nonneg_left hΛn (le_of_lt hKpos)
    have h2 : K * (η / K * ‖coeffFun a z‖) = η * ‖coeffFun a z‖ := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hdivmono : (∑ p ∈ S.filter (fun p => ¬ p.1 + p.2 = d),
        ‖(A p).eval z‖ * ‖deriv (coeffFun a) z / coeffFun a z‖ ^ p.2) / ‖coeffFun a z‖
      ≤ K * Λ ^ n / ‖coeffFun a z‖ := by
    gcongr
  linarith

end GaloisForLFunctions.HTGeometry
