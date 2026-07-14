import GaloisForLFunctions.RHTower.HeatApertureEchoTomography
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.HTGeometry.DiscreteMomentHankel

/-!
# Strict positivity of real heat-aperture log-echo Hankel matrices

On the real strip, the canonical logarithmic echo is a positive moment sequence on reciprocal
prime powers. This module identifies the sequence exactly, packages its Hankel matrices, and proves
strict positive definiteness and positive determinant in every finite order by the discrete
infinite-support moment theorem.
-/

namespace GaloisForLFunctions

open Complex LSeries
open scoped BigOperators

noncomputable section

private theorem canonicalEulerLogZeta_ofReal_eq_primePower_tsum
    {β : ℝ} (hβ : 1 < β) :
    RHTower.canonicalEulerLogZeta (β : ℂ) =
      ((∑' z : Nat.Primes × ℕ, RHTower.eulerPrimePowerWeight β z : ℝ) : ℂ) := by
  rw [RHTower.canonicalEulerLogZeta, LSeries]
  have hsum : Summable (LSeries.term RHTower.eulerLogDirichletCoeff (β : ℂ)) :=
    RHTower.canonicalEulerLogZeta_summable (by exact_mod_cast hβ)
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hsum]
  · have hsabs := RHTower.summable_abs_eulerPrimePower_moment 0 β hβ
    have hsreal : Summable (fun z : Nat.Primes × ℕ ↦
        RHTower.eulerPrimePowerWeight β z) := by
      apply Summable.of_norm
      simpa [Real.norm_eq_abs] using hsabs
    have hsc : Summable (fun z : Nat.Primes × ℕ ↦
        (RHTower.eulerPrimePowerWeight β z : ℂ)) :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).summable hsreal
    rw [Complex.ofReal_tsum, hsc.tsum_prod]
    apply tsum_congr
    intro p
    apply tsum_congr
    intro k
    rw [LSeries.term_of_ne_zero (pow_ne_zero (k + 1) p.property.ne_zero),
      RHTower.eulerLogDirichletCoeff_prime_pow_succ p k p.property]
    change 1 / (k + 1 : ℂ) /
      ((((p : ℕ) ^ (k + 1) : ℕ) : ℝ) : ℂ) ^ (β : ℂ) = _
    rw [← Complex.ofReal_cpow
      (by positivity : 0 ≤ (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)) β]
    have hreal :
        (1 : ℝ) / (k + 1 : ℝ) /
            ((((p : ℕ) ^ (k + 1) : ℕ) : ℝ) ^ β) =
          RHTower.eulerPrimePowerWeight β (p, k) := by
      rw [RHTower.eulerPrimePowerWeight]
      simp only [RHTower.eulerPrimePowerNat]
      rw [Real.rpow_neg
        (by positivity : 0 ≤ (((p : ℕ) ^ (k + 1) : ℕ) : ℝ))]
      ring
    simpa using congrArg Complex.ofReal hreal
  · intro n hn
    by_contra hpp
    apply hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0,
        RHTower.eulerLogDirichletCoeff_eq_zero_of_not_primePower hpp]
      simp

/-- Reciprocal-integer node attached to a prime-power parameter. -/
def heatAperturePrimePowerNode (z : Nat.Primes × ℕ) : ℝ :=
  (RHTower.eulerPrimePowerNat z : ℝ)⁻¹

/-- Positive prime-power weight underlying the real log echo starting at depth `q`. -/
def heatAperturePrimePowerBaseWeight (σ : ℝ) (q : ℕ)
    (z : Nat.Primes × ℕ) : ℝ :=
  RHTower.eulerPrimePowerWeight (1 - σ + q) z

/-- Real-axis canonical logarithmic echo. -/
def heatApertureRealLogEchoValue (σ : ℝ) (k : ℕ) : ℝ :=
  (heatApertureLogEchoValue (σ : ℂ) k).re

/-- The real canonical log echo is the positive prime-power Dirichlet sum. -/
theorem heatApertureRealLogEchoValue_eq_primePower_tsum
    {σ : ℝ} {k : ℕ} (hβ : 1 < 1 - σ + k) :
    heatApertureRealLogEchoValue σ k =
      ∑' z : Nat.Primes × ℕ,
        RHTower.eulerPrimePowerWeight (1 - σ + k) z := by
  have h := canonicalEulerLogZeta_ofReal_eq_primePower_tsum hβ
  have hre := congrArg Complex.re h
  simpa [heatApertureRealLogEchoValue, heatApertureLogEchoValue] using hre

/-- Additive depth is multiplication by the reciprocal prime-power node. -/
theorem heatApertureRealLogEchoValue_add_eq_moment
    {σ : ℝ} {q : ℕ} (hβ : 1 < 1 - σ + q) (k : ℕ) :
    heatApertureRealLogEchoValue σ (q + k) =
      ∑' z : Nat.Primes × ℕ,
        heatAperturePrimePowerBaseWeight σ q z *
          heatAperturePrimePowerNode z ^ k := by
  rw [heatApertureRealLogEchoValue_eq_primePower_tsum (by
    have hqk : (q : ℝ) ≤ (q + k : ℕ) := by
      exact_mod_cast Nat.le_add_right q k
    linarith)]
  apply tsum_congr
  intro z
  have hN : 0 < (RHTower.eulerPrimePowerNat z : ℝ) := by
    exact_mod_cast (show 0 < RHTower.eulerPrimePowerNat z by
      dsimp [RHTower.eulerPrimePowerNat]
      exact pow_pos z.1.property.pos _)
  rw [heatAperturePrimePowerBaseWeight, heatAperturePrimePowerNode,
    RHTower.eulerPrimePowerWeight]
  have hexp : -(1 - σ + (q + k : ℕ) : ℝ) =
      -(1 - σ + (q : ℝ)) + -(k : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_add hN]
  have hkpow : (RHTower.eulerPrimePowerNat z : ℝ) ^ (-(k : ℝ)) =
      (RHTower.eulerPrimePowerNat z : ℝ)⁻¹ ^ k := by
    rw [Real.rpow_neg hN.le, Real.rpow_natCast, inv_pow]
  rw [hkpow]
  rw [RHTower.eulerPrimePowerWeight]
  ring

/-- The real log-echo Hankel matrix indexed by `0 ≤ i,j ≤ r`. -/
def heatApertureLogEchoHankel (σ : ℝ) (q r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  HTGeometry.momentHankelMatrix
    (fun k ↦ heatApertureRealLogEchoValue σ (q + k)) (r + 1)

@[simp]
theorem heatApertureLogEchoHankel_apply (σ : ℝ) (q r : ℕ)
    (i j : Fin (r + 1)) :
    heatApertureLogEchoHankel σ q r i j =
      heatApertureRealLogEchoValue σ (q + (i : ℕ) + (j : ℕ)) := by
  simp [heatApertureLogEchoHankel, HTGeometry.momentHankelMatrix, add_assoc]

private theorem heatAperturePrimePowerBaseWeight_nonneg (σ : ℝ) (q : ℕ) :
    ∀ z, 0 ≤ heatAperturePrimePowerBaseWeight σ q z := by
  intro z
  dsimp [heatAperturePrimePowerBaseWeight, RHTower.eulerPrimePowerWeight]
  positivity

private theorem summable_heatAperturePrimePowerBaseWeight_node
    {σ : ℝ} {q : ℕ} (hβ : 1 < 1 - σ + q) (k : ℕ) :
    Summable (fun z : Nat.Primes × ℕ ↦
      heatAperturePrimePowerBaseWeight σ q z *
        |heatAperturePrimePowerNode z| ^ k) := by
  have hsabs := RHTower.summable_abs_eulerPrimePower_moment 0 (1 - σ + q) hβ
  have hs : Summable (fun z : Nat.Primes × ℕ ↦
      heatAperturePrimePowerBaseWeight σ q z) := by
    apply Summable.of_norm
    simpa [heatAperturePrimePowerBaseWeight, Real.norm_eq_abs] using hsabs
  apply Summable.of_nonneg_of_le
  · intro z
    exact mul_nonneg (heatAperturePrimePowerBaseWeight_nonneg σ q z)
      (pow_nonneg (abs_nonneg _) k)
  · intro z
    have hN : 1 ≤ (RHTower.eulerPrimePowerNat z : ℝ) := by
      exact_mod_cast (show 1 ≤ RHTower.eulerPrimePowerNat z by
        dsimp [RHTower.eulerPrimePowerNat]
        exact one_le_pow₀ (by exact z.1.property.one_lt.le))
    have hnode : |heatAperturePrimePowerNode z| ≤ 1 := by
      rw [abs_of_nonneg (by
        rw [heatAperturePrimePowerNode]
        exact inv_nonneg.mpr (Nat.cast_nonneg _))]
      exact inv_le_one_of_one_le₀ hN
    exact mul_le_of_le_one_right
      (heatAperturePrimePowerBaseWeight_nonneg σ q z)
      (pow_le_one₀ (abs_nonneg _) hnode)
  · exact hs

private theorem infinite_heatAperturePrimePowerNodes (σ : ℝ) (q : ℕ) :
    ∀ F : Finset ℝ, ∃ z : Nat.Primes × ℕ,
      heatAperturePrimePowerNode z ∉ F ∧
        0 < heatAperturePrimePowerBaseWeight σ q z := by
  intro F
  let node : Nat.Primes → ℝ := fun p ↦ heatAperturePrimePowerNode (p, 0)
  have hnode : Function.Injective node := by
    intro p r hpr
    apply Subtype.ext
    dsimp [node, heatAperturePrimePowerNode, RHTower.eulerPrimePowerNat] at hpr
    have hpr' : (p : ℝ)⁻¹ = (r : ℝ)⁻¹ := by simpa using hpr
    have hcast : (p : ℝ) = (r : ℝ) := inv_injective hpr'
    exact_mod_cast hcast
  have hrange : (Set.range node).Infinite := Set.infinite_range_of_injective hnode
  have hex : ∃ p : Nat.Primes, node p ∉ F := by
    by_contra h
    apply hrange
    apply F.finite_toSet.subset
    rintro y ⟨p, rfl⟩
    exact not_not.mp (not_exists.mp h p)
  obtain ⟨p, hp⟩ := hex
  refine ⟨(p, 0), hp, ?_⟩
  dsimp [heatAperturePrimePowerBaseWeight, RHTower.eulerPrimePowerWeight,
    RHTower.eulerPrimePowerNat]
  exact div_pos (Real.rpow_pos_of_pos (by
    exact_mod_cast (pow_pos p.property.pos 1)) _) (by norm_num)

/-- Every real-strip log-echo Hankel matrix is strictly positive definite. -/
theorem heatApertureLogEchoHankel_posDef
    {σ : ℝ} (_hσlo : 1 / 2 < σ) (hσhi : σ < 1)
    {q : ℕ} (hq : 1 ≤ q) (r : ℕ) :
    (heatApertureLogEchoHankel σ q r).PosDef := by
  have hβ : 1 < 1 - σ + q := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hseq : (fun k ↦ heatApertureRealLogEchoValue σ (q + k)) =
      fun k ↦ ∑' z : Nat.Primes × ℕ,
        heatAperturePrimePowerBaseWeight σ q z *
          heatAperturePrimePowerNode z ^ k := by
    funext k
    exact heatApertureRealLogEchoValue_add_eq_moment hβ k
  rw [heatApertureLogEchoHankel, hseq]
  exact HTGeometry.discreteMomentHankel_posDef
    (heatAperturePrimePowerBaseWeight σ q) heatAperturePrimePowerNode
    (heatAperturePrimePowerBaseWeight_nonneg σ q)
    (summable_heatAperturePrimePowerBaseWeight_node hβ)
    (infinite_heatAperturePrimePowerNodes σ q) (r + 1)

/-- Every real-strip log-echo Hankel determinant is strictly positive. -/
theorem heatApertureLogEchoHankel_det_pos
    {σ : ℝ} (hσlo : 1 / 2 < σ) (hσhi : σ < 1)
    {q : ℕ} (hq : 1 ≤ q) (r : ℕ) :
    0 < (heatApertureLogEchoHankel σ q r).det :=
  (heatApertureLogEchoHankel_posDef hσlo hσhi hq r).det_pos

end
end GaloisForLFunctions
