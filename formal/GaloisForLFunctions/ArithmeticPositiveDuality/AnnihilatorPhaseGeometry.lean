import GaloisForLFunctions.ArithmeticPositiveDuality.AnnihilatorPhaseMoments
import GaloisForLFunctions.ArithmeticPositiveDuality.NegativeContractionConvexity

/-!
# Relative interior of arbitrary finite annihilator phase hulls

One exact positive annihilator supplies a negative homothety of the phase
convex hull: multiply its zero moment by any monomial phase. Consequently,
nonzero ordinates give exact radial correction throughout the closed convex
hull, including families with odd integer relations.
-/

noncomputable section
set_option autoImplicit false
open Set Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- Multiplication of arithmetic monomials multiplies their unit phases. -/
theorem monomialPhase_add (γ : ℝ) (d e : Fin 2 →₀ ℕ) :
    monomialPhase γ (d + e) = monomialPhase γ d * monomialPhase γ e := by
  have hL : monomialLog (d + e) = monomialLog d + monomialLog e := by
    simp only [monomialLog, Finsupp.add_apply, Nat.cast_add]
    ring
  rw [monomialPhase, hL, Complex.ofReal_add, neg_add, add_mul, add_mul, Complex.exp_add]
  rfl

variable {ι : Type*}

/-- The simultaneous phase at an arbitrary real logarithmic frequency. -/
def annihilatorPhaseLine (γ : ι → ℝ) (t : ℝ) : ι → ℂ :=
  fun i => Complex.exp (-(t : ℂ) * (γ i : ℂ) * Complex.I)

theorem norm_annihilatorPhaseLine (γ : ι → ℝ) (t : ℝ) (i : ι) :
    ‖annihilatorPhaseLine γ t i‖ = 1 := by
  simp [annihilatorPhaseLine, Complex.norm_exp]

theorem monomialPhaseSet_nonempty (γ : ι → ℝ) : (monomialPhaseSet γ).Nonempty := by
  refine ⟨fun i => monomialPhase (γ i) (Finsupp.single 0 1), Finsupp.single 0 1, ?_, rfl⟩
  simp

variable [Fintype ι]

/-- Every continuous phase lies in the closure of actual nonconstant two-prime phases. -/
theorem phaseLine_mem_phaseHull (γ : ι → ℝ) (t : ℝ) :
    annihilatorPhaseLine γ t ∈ closure (monomialPhaseSet γ) := by
  rw [closure_monomialPhaseSet]
  refine ⟨screwPhase (fun i => -γ i) t, screwPhase_mem_screwHull _ _, ?_⟩
  funext i
  change fourier 1 (screwPhase (fun i => -γ i) t i) =
    Complex.exp (-(t : ℂ) * (γ i : ℂ) * Complex.I)
  have h := infiniteTorusFourier_screwPhase (Finsupp.single i 1) (fun i => -γ i) t
  simp only [infiniteTorusFourier_single, infiniteTorusCharacterDetuning,
    Finsupp.sum_single_index, Int.cast_one, one_mul, Int.cast_zero, zero_mul] at h
  rw [h]
  congr 1
  push_cast
  ring

/-- A finite family of nonzero ordinates has one exact positive annihilator
on the imaginary axis, with normalized constant coefficient. -/
theorem exists_joint_zero_abscissa_annihilator (γ : ι → ℝ) (hγ : ∀ i, γ i ≠ 0) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      ∀ i, dirichletEval (harmonicPacketPoint 0 (γ i) 1) P = 0 := by
  classical
  have hex : ∀ i, ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧ dirichletEval (harmonicPacketPoint 0 (γ i) 1) P = 0 := by
    intro i
    obtain ⟨P, hc, he, _⟩ := exists_single_annihilator (harmonicPacketPoint 0 (γ i) 1)
      (by simp [harmonicPacketPoint]) (by simpa [harmonicPacketPoint] using hγ i)
      (by norm_num : (0 : ℝ) < 1)
    exact ⟨P, hc, he⟩
  choose P hc he using hex
  refine ⟨∏ i, P i, ?_, ?_⟩
  · simp only [map_prod, hc, Finset.prod_const_one]
  · intro i
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (he i)

variable [Nonempty ι]

/-- Translating one positive zero moment gives a fixed negative homothety
preserving the entire phase convex hull. -/
theorem exists_phaseConvexHull_negative_contraction (γ : ι → ℝ) (hγ : ∀ i, γ i ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ convexHull ℝ (monomialPhaseSet γ),
      (-a) • x ∈ convexHull ℝ (monomialPhaseSet γ) := by
  classical
  obtain ⟨P, hc, he⟩ := exists_joint_zero_abscissa_annihilator γ hγ
  let S := P.support.erase 0
  let H := dirichletTailMass P 0
  have hone : 1 ≤ H := by
    have h := one_le_dirichletTailMass_of_zero hc (he (Classical.choice ‹Nonempty ι›))
    simpa [H, harmonicPacketPoint] using h
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hone
  have hsum : ∑ e ∈ S, ((P.coeff e : ℝ≥0) : ℝ) = H := by
    simp only [H, dirichletTailMass, S, mul_zero, Real.exp_zero, mul_one]
  have hraw : (∑ e ∈ S, ((P.coeff e : ℝ≥0) : ℝ) •
      (fun i => monomialPhase (γ i) e)) = (fun _ : ι => (-1 : ℂ)) := by
    simpa only [mul_zero, Real.exp_zero, mul_one] using annihilator_phase_sum hc 0 γ he
  have hD : ∀ x ∈ monomialPhaseSet γ,
      (-(1 / H : ℝ)) • x ∈ convexHull ℝ (monomialPhaseSet γ) := by
    rintro _ ⟨d, hd, rfl⟩
    have hm : (∑ e ∈ S, (((P.coeff e : ℝ≥0) : ℝ) / H) •
        (fun i => monomialPhase (γ i) (d + e))) ∈ convexHull ℝ (monomialPhaseSet γ) := by
      apply (convex_convexHull ℝ (monomialPhaseSet γ)).sum_mem
      · intro e _
        exact div_nonneg (P.coeff e).coe_nonneg hH.le
      · rw [← Finset.sum_div, hsum, div_self hH.ne']
      · intro e _
        apply subset_convexHull ℝ _
        refine ⟨d + e, ?_, rfl⟩
        intro hzero
        apply hd
        ext i
        have hi := congrArg (fun f : Fin 2 →₀ ℕ => f i) hzero
        simp only [Finsupp.add_apply, Finsupp.zero_apply] at hi
        exact (Nat.add_eq_zero.mp hi).1
    have hval : (∑ e ∈ S, (((P.coeff e : ℝ≥0) : ℝ) / H) •
        (fun i => monomialPhase (γ i) (d + e))) =
        (-(1 / H : ℝ)) • (fun i => monomialPhase (γ i) d) := by
      funext i
      have hs := congrFun hraw i
      simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul] at hs ⊢
      calc
        _ = (monomialPhase (γ i) d / (H : ℂ)) *
            (∑ e ∈ S, (((P.coeff e : ℝ≥0) : ℝ) : ℂ) * monomialPhase (γ i) e) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          rw [Complex.ofReal_div, monomialPhase_add]
          ring
        _ = _ := by
          rw [hs]
          simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one]
          ring
    rwa [hval] at hm
  refine ⟨1 / H, one_div_pos.mpr hH, ?_⟩
  exact convexHull_min hD ((convex_convexHull ℝ (monomialPhaseSet γ)).smul_preimage (-(1 / H)))

/-- Nonzero ordinates place zero in the actual monomial phase convex hull. -/
theorem zero_mem_phaseConvexHull (γ : ι → ℝ) (hγ : ∀ i, γ i ≠ 0) :
    (0 : ι → ℂ) ∈ convexHull ℝ (monomialPhaseSet γ) := by
  obtain ⟨a, ha, hneg⟩ := exists_phaseConvexHull_negative_contraction γ hγ
  exact zero_mem_of_negative_contraction (convex_convexHull ℝ _)
    ((monomialPhaseSet_nonempty γ).mono (subset_convexHull ℝ _)) ha hneg

/-- Every strict radial contraction of a closed phase-convex point has an
exact finite representation by actual nonconstant monomial phases. -/
theorem phaseHull_radial_exactness (γ : ι → ℝ) (hγ : ∀ i, γ i ≠ 0)
    {z : ι → ℂ} (hz : z ∈ closure (convexHull ℝ (monomialPhaseSet γ)))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    r • z ∈ convexHull ℝ (monomialPhaseSet γ) := by
  obtain ⟨a, ha, hneg⟩ := exists_phaseConvexHull_negative_contraction γ hγ
  exact smul_mem_of_negative_contraction (convex_convexHull ℝ _)
    ((monomialPhaseSet_nonempty γ).mono (subset_convexHull ℝ _)) ha hneg hz hr0 hr1

#print axioms phaseHull_radial_exactness

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
