import GaloisForLFunctions.SelbergClass.SubcriticalEulerRigidity
import GaloisForLFunctions.SelbergClass.GammaIndependentEulerRigidity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Finite-prime rigidity in the full Selberg class

The strict Euler bound makes any discrepancy supported on finitely many
prime-power sequences converge to the left of the critical line. With the
same bare Gamma product, reflection forces equality of all coefficients,
the positive exponential parameter, and the root number.
-/

noncomputable section
open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

private def primePowerTerm (b : ℕ → ℂ) (σ : ℝ) (p : ℕ) : ℕ → ℂ :=
  Function.extend (fun k : ℕ => p ^ k) (fun k => LSeries.term b σ (p ^ k)) 0

private theorem primePowerTerm_summable {b : ℕ → ℂ} {C θ σ : ℝ}
    (hbound : ∀ n : ℕ, n ≠ 0 → ‖b n‖ ≤ C * (n : ℝ) ^ θ)
    (hσ : θ < σ) {p : ℕ} (hp : p.Prime) : Summable (primePowerTerm b σ p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr0 : 0 ≤ (p : ℝ) ^ (θ - σ) := Real.rpow_nonneg hp0.le _
  have hr1 : (p : ℝ) ^ (θ - σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hterms : Summable (fun k : ℕ => LSeries.term b σ (p ^ k)) := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
    intro k
    have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hpk0 : (0 : ℝ) < (p ^ k : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hpk
    rw [LSeries.norm_term_eq, if_neg hpk, ofReal_re]
    calc ‖b (p ^ k)‖ / (p ^ k : ℕ) ^ σ
        ≤ C * ((p ^ k : ℕ) : ℝ) ^ θ / ((p ^ k : ℕ) : ℝ) ^ σ :=
          div_le_div_of_nonneg_right (hbound _ hpk) (Real.rpow_nonneg hpk0.le _)
      _ = C * ((p ^ k : ℕ) : ℝ) ^ (θ - σ) := by
        rw [Real.rpow_sub hpk0]
        ring
      _ = C * ((p : ℝ) ^ (θ - σ)) ^ k := by
        congr 1
        rw [Nat.cast_pow, Real.rpow_def_of_pos (pow_pos hp0 k), Real.log_pow,
          Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]
        congr 1
        ring
  exact ((hasSum_extend_zero (pow_right_strictMono₀ hp.one_lt).injective).mpr hterms.hasSum).summable

/-- A finite union of prime-power sequences has absolute-convergence exponent
at most the exponent of its coefficients, with no additional density cost. -/
theorem lSeriesSummable_of_finite_prime_support {b : ℕ → ℂ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {C θ σ : ℝ}
    (hbound : ∀ n : ℕ, n ≠ 0 → ‖b n‖ ≤ C * (n : ℝ) ^ θ)
    (hsupport : ∀ n : ℕ, b n ≠ 0 → ∃ p ∈ P, ∃ k : ℕ, n = p ^ k)
    (hσ : θ < σ) : LSeriesSummable b σ := by
  classical
  have hsum : Summable (fun n => ∑ p ∈ P, ‖primePowerTerm b σ p n‖) := by
    clear hsupport
    revert hP
    induction P using Finset.induction_on with
    | empty =>
        intro _
        simpa only [Finset.sum_empty] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    | @insert p P hp ih =>
        intro hP
        simp only [Finset.sum_insert hp]
        exact (primePowerTerm_summable hbound hσ (hP p (Finset.mem_insert_self p P))).norm.add
          (ih fun q hq => hP q (Finset.mem_insert_of_mem hq))
  apply Summable.of_norm_bounded hsum
  intro n
  by_cases hzero : LSeries.term b σ n = 0
  · rw [hzero, norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  · have hb : b n ≠ 0 := by
      intro hb
      exact hzero (by simp only [LSeries.term, hb, zero_div, ite_self])
    obtain ⟨p, hp, k, rfl⟩ := hsupport n hb
    have heq : primePowerTerm b σ p (p ^ k) = LSeries.term b σ (p ^ k) :=
      (pow_right_strictMono₀ (hP p hp).one_lt).injective.extend_apply _ _ k
    rw [← heq]
    exact Finset.single_le_sum (fun q _ => norm_nonneg (primePowerTerm b σ q (p ^ k))) hp

/-- The strict Euler bounds give subcritical absolute convergence for any
discrepancy supported on finitely many primes. -/
theorem exists_subcritical_of_finite_prime_discrepancy (F G : RHTower.SelbergClass)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hagree : ∀ p : ℕ, p.Prime → p ∉ P → ∀ k : ℕ, 0 < k →
      F.eulerLogCoeff (p ^ k) = G.eulerLogCoeff (p ^ k)) :
    ∃ σ : ℝ, σ < 1 / 2 ∧
      LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ := by
  obtain ⟨CF, hCF, hF⟩ := F.eulerLogBound
  obtain ⟨CG, hCG, hG⟩ := G.eulerLogBound
  let θ := max F.eulerTheta G.eulerTheta
  have hθ : θ < 1 / 2 := max_lt F.eulerTheta_lt_half G.eulerTheta_lt_half
  obtain ⟨σ, hθσ, hσ⟩ := exists_between hθ
  refine ⟨σ, hσ, ?_⟩
  apply lSeriesSummable_of_finite_prime_support P hP (C := CF + CG) (θ := θ)
    _ _ hθσ
  · intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    calc ‖F.eulerLogCoeff n - G.eulerLogCoeff n‖
        ≤ ‖F.eulerLogCoeff n‖ + ‖G.eulerLogCoeff n‖ := norm_sub_le _ _
      _ ≤ CF * (n : ℝ) ^ F.eulerTheta + CG * (n : ℝ) ^ G.eulerTheta :=
        add_le_add (hF n hn) (hG n hn)
      _ ≤ CF * (n : ℝ) ^ θ + CG * (n : ℝ) ^ θ := add_le_add
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _)) hCF.le)
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)) hCG.le)
      _ = (CF + CG) * (n : ℝ) ^ θ := by ring
  · intro n hn
    have hex : ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k := by
      by_cases hfn : F.eulerLogCoeff n = 0
      · apply G.eulerLogCoeff_primePower
        intro hgn
        exact hn (by rw [hfn, hgn, sub_self])
      · exact F.eulerLogCoeff_primePower hfn
    obtain ⟨p, k, hp, hk, rfl⟩ := hex
    have hpP : p ∈ P := by
      by_contra hpP
      exact hn (sub_eq_zero.mpr (hagree p hp hpP k hk))
    exact ⟨p, hpP, k, rfl⟩

/-- Removing finitely many Euler factors cannot distinguish two normalized
full Selberg functions with the same gamma factor. -/
theorem coeff_eq_of_finite_prime_discrepancy (F G : RHTower.SelbergClass)
    (hgamma : F.gammaData.gammaFactor = G.gammaData.gammaFactor)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hagree : ∀ p : ℕ, p.Prime → p ∉ P → ∀ k : ℕ, 0 < k →
      F.eulerLogCoeff (p ^ k) = G.eulerLogCoeff (p ^ k)) :
    F.coeff = G.coeff := by
  obtain ⟨σ, hσ, hb⟩ := exists_subcritical_of_finite_prime_discrepancy F G P hP hagree
  exact coeff_eq_of_subcritical_euler_discrepancy F G hgamma hσ hb

/-- Finite-prime changes cannot alter coefficients, the positive exponential
parameter, or the root number while preserving the bare Gamma product. -/
theorem rigidity_of_finite_prime_discrepancy (F G : RHTower.SelbergClass)
    (hgamma : archGammaFactor F.gammaData = archGammaFactor G.gammaData)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hagree : ∀ p : ℕ, p.Prime → p ∉ P → ∀ k : ℕ, 0 < k →
      F.eulerLogCoeff (p ^ k) = G.eulerLogCoeff (p ^ k)) :
    F.coeff = G.coeff ∧ F.gammaData.Q = G.gammaData.Q ∧
      F.gammaData.rootNumber = G.gammaData.rootNumber := by
  obtain ⟨σ, hσ, hb⟩ := exists_subcritical_of_finite_prime_discrepancy F G P hP hagree
  exact rigidity_of_subcritical_euler_discrepancy F G hgamma hσ hb

/-- Full Selberg functions agreeing outside finitely many Euler factors have
identical coefficients, independently of their Gamma presentations. -/
theorem coeff_eq_of_finite_prime_discrepancy_arbitrary_gamma (F G : RHTower.SelbergClass)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hagree : ∀ p : ℕ, p.Prime → p ∉ P → ∀ k : ℕ, 0 < k →
      F.eulerLogCoeff (p ^ k) = G.eulerLogCoeff (p ^ k)) :
    F.coeff = G.coeff := by
  obtain ⟨σ, hσ, hb⟩ := exists_subcritical_of_finite_prime_discrepancy F G P hP hagree
  exact coeff_eq_of_subcritical_discrepancy F G hσ hb

end GaloisForLFunctions.SelbergClass
