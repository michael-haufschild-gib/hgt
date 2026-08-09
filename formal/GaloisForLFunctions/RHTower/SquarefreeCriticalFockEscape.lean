import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift
import GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscape
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Critical Fock escape of the squarefree source

The normalized signed squarefree source is a unit vector of `ℓ²` for every `σ > 1`.  Its
empty-occupation (vacuum) overlap has squared modulus exactly `Z(σ)⁻¹`, and every fixed
coordinate vanishes as `σ ↓ 1` because the squarefree partition diverges at the Euler pole.
Density of the coordinate Hilbert basis upgrades coordinate decay to weak nullity, so the
source escapes every fixed continuous linear functional while keeping unit norm.  Hence the
source family has no strong `ℓ²` limit at the critical boundary: the ordinary vacuum Fock
completion loses the critical source.  At the same time the critically rescaled Fisher
tangent retains squared norm four there, which is the surviving metric residue.
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Coordinates of the normalized signed squarefree source. -/
theorem infiniteMobiusSignedWeightLp_apply {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    infiniteMobiusSignedWeightLp sigma hsigma n = infiniteMobiusSignedWeight sigma n := rfl

/-- The occupation probability of the empty configuration is exactly `Z(σ)⁻¹`. -/
theorem squarefreeMobiusProbability_one (sigma : ℝ) :
    squarefreeMobiusProbability sigma 1 = (squarefreeMobiusTotal sigma)⁻¹ := by
  rw [squarefreeMobiusProbability, squarefreeMobiusMass]
  simp [one_div]

/-- **Vacuum overlap law.**  The squared modulus of the pairing of the squarefree source with
the empty-occupation basis state is exactly the reciprocal partition `Z(σ)⁻¹`. -/
theorem norm_inner_vacuum_infiniteMobiusSignedWeightLp_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖inner ℂ ((HilbertSchmidt.lpBasis ℕ) 1) (infiniteMobiusSignedWeightLp sigma hsigma)‖ ^ 2 =
      (squarefreeMobiusTotal sigma)⁻¹ := by
  rw [HilbertSchmidt.lpBasis_apply, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, one_mul, infiniteMobiusSignedWeightLp_apply]
  rw [norm_infiniteMobiusSignedWeight_sq hsigma, squarefreeMobiusProbability_one]

/-- Every fixed coordinate modulus of the squarefree source vanishes at the Euler boundary. -/
theorem tendsto_norm_infiniteMobiusSignedWeight_zero (n : ℕ) :
    Tendsto (fun sigma : ℝ => ‖infiniteMobiusSignedWeight sigma n‖)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hsqrt : Tendsto (fun sigma : ℝ =>
      Real.sqrt (squarefreeMobiusProbability sigma n)) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_squarefreeMobiusProbability_zero n)
  apply hsqrt.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hs
  change 1 < sigma at hs
  rw [← Real.sqrt_sq (norm_nonneg (infiniteMobiusSignedWeight sigma n)),
    norm_infiniteMobiusSignedWeight_sq hs]

/-- Every fixed coordinate of the squarefree source vanishes at the Euler boundary. -/
theorem tendsto_infiniteMobiusSignedWeight_zero (n : ℕ) :
    Tendsto (fun sigma : ℝ => infiniteMobiusSignedWeight sigma n)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact tendsto_norm_infiniteMobiusSignedWeight_zero n

/-- The critical squarefree source family, with junk value `0` outside the Euler half-line. -/
def criticalSquarefreeSourceFamily (sigma : ℝ) : lp (fun _ : ℕ => ℂ) 2 :=
  if hsigma : 1 < sigma then infiniteMobiusSignedWeightLp sigma hsigma else 0

/-- The critical source family consists of unit vectors on the Euler half-line. -/
theorem norm_criticalSquarefreeSourceFamily {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖criticalSquarefreeSourceFamily sigma‖ = 1 := by
  rw [criticalSquarefreeSourceFamily, dif_pos hsigma]
  exact norm_infiniteMobiusSignedWeightLp hsigma

/-- Weak escape against every fixed Hilbert vector: each inner pairing with the critical
source family vanishes at the Euler boundary. -/
theorem tendsto_inner_criticalSquarefreeSourceFamily_zero
    (y : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun sigma : ℝ => inner ℂ y (criticalSquarefreeSourceFamily sigma))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hbasis : ∀ k : ℕ,
      Tendsto (fun sigma : ℝ =>
        inner ℂ ((HilbertSchmidt.lpBasis ℕ) k) (criticalSquarefreeSourceFamily sigma))
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    intro k
    apply (tendsto_infiniteMobiusSignedWeight_zero k).congr'
    filter_upwards [self_mem_nhdsWithin] with sigma hs
    change 1 < sigma at hs
    rw [criticalSquarefreeSourceFamily, dif_pos hs, HilbertSchmidt.lpBasis_apply,
      lp.inner_single_left]
    simp [infiniteMobiusSignedWeightLp_apply]
  have hspan : ∀ z ∈ Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ℕ)),
      Tendsto (fun sigma : ℝ => inner ℂ z (criticalSquarefreeSourceFamily sigma))
        (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact hbasis k
    | zero => simp
    | add x y hx hy hxt hyt =>
        simpa only [inner_add_left, zero_add] using hxt.add hyt
    | smul a x hx hxt =>
        simpa only [inner_smul_left, mul_zero] using
          hxt.const_mul (starRingEnd ℂ a)
  have hdense : Dense (Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ℕ)) :
      Set (lp (fun _ : ℕ => ℂ) 2)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (HilbertSchmidt.lpBasis ℕ).dense_span
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨z, hz, hyz⟩ := hdense.exists_dist_lt y (half_pos hε)
  have hz0 := hspan z hz
  rw [NormedAddGroup.tendsto_nhds_zero] at hz0
  filter_upwards [hz0 (ε / 2) (half_pos hε), self_mem_nhdsWithin] with sigma hn hs
  change 1 < sigma at hs
  have hvnorm : ‖criticalSquarefreeSourceFamily sigma‖ = 1 :=
    norm_criticalSquarefreeSourceFamily hs
  calc
    ‖inner ℂ y (criticalSquarefreeSourceFamily sigma)‖ =
        ‖inner ℂ (y - z) (criticalSquarefreeSourceFamily sigma) +
          inner ℂ z (criticalSquarefreeSourceFamily sigma)‖ := by
      rw [← inner_add_left, sub_add_cancel]
    _ ≤ ‖inner ℂ (y - z) (criticalSquarefreeSourceFamily sigma)‖ +
        ‖inner ℂ z (criticalSquarefreeSourceFamily sigma)‖ := norm_add_le _ _
    _ ≤ ‖y - z‖ * ‖criticalSquarefreeSourceFamily sigma‖ +
        ‖inner ℂ z (criticalSquarefreeSourceFamily sigma)‖ := by
      gcongr
      exact norm_inner_le_norm _ _
    _ = dist y z + ‖inner ℂ z (criticalSquarefreeSourceFamily sigma)‖ := by
      rw [hvnorm, mul_one, dist_eq_norm]
    _ < ε / 2 + ε / 2 := add_lt_add hyz hn
    _ = ε := by ring

/-- **Weak nullity of the critical source.**  Every continuous linear functional of the
squarefree source family vanishes at the Euler boundary. -/
theorem criticalSquarefreeSourceFamily_weakly_tendsto_zero
    (ℓ : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] ℂ) :
    Tendsto (fun sigma : ℝ => ℓ (criticalSquarefreeSourceFamily sigma))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  let y : lp (fun _ : ℕ => ℂ) 2 :=
    (InnerProductSpace.toDual ℂ (lp (fun _ : ℕ => ℂ) 2)).symm ℓ
  simpa [y, InnerProductSpace.toDual_symm_apply] using
    tendsto_inner_criticalSquarefreeSourceFamily_zero y

/-- **No-go: the critical source has no strong Fock limit.**  The unit squarefree source
family admits no norm limit in `ℓ²` at the Euler boundary. -/
theorem not_exists_strong_limit_criticalSquarefreeSourceFamily :
    ¬ ∃ v : lp (fun _ : ℕ => ℂ) 2,
      Tendsto criticalSquarefreeSourceFamily (𝓝[>] (1 : ℝ)) (𝓝 v) := by
  rintro ⟨v, hv⟩
  have hnorm : Tendsto (fun sigma : ℝ => ‖criticalSquarefreeSourceFamily sigma‖)
      (𝓝[>] (1 : ℝ)) (𝓝 ‖v‖) := hv.norm
  have hone : Tendsto (fun sigma : ℝ => ‖criticalSquarefreeSourceFamily sigma‖)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) _ _).congr'
    filter_upwards [self_mem_nhdsWithin] with sigma hs
    change 1 < sigma at hs
    exact (norm_criticalSquarefreeSourceFamily hs).symm
  have hvone : ‖v‖ = 1 := tendsto_nhds_unique hnorm hone
  have hstrong : Tendsto (fun sigma : ℝ => inner ℂ v (criticalSquarefreeSourceFamily sigma))
      (𝓝[>] (1 : ℝ)) (𝓝 (inner ℂ v v)) :=
    ((innerSL ℂ v).continuous.continuousAt.tendsto).comp hv
  have hzero : inner ℂ v v = (0 : ℂ) :=
    tendsto_nhds_unique hstrong (tendsto_inner_criticalSquarefreeSourceFamily_zero v)
  have hv0 : v = 0 := inner_self_eq_zero.mp hzero
  rw [hv0, norm_zero] at hvone
  norm_num at hvone

/-- **Critical Fock escape with surviving tangent residue.**  The unit squarefree source has
no strong `ℓ²` limit at the Euler boundary, while the squared norm of its critically rescaled
Fisher tangent tends to four. -/
theorem squarefreeCriticalFockEscape :
    (¬ ∃ v : lp (fun _ : ℕ => ℂ) 2,
        Tendsto criticalSquarefreeSourceFamily (𝓝[>] (1 : ℝ)) (𝓝 v)) ∧
      Tendsto (fun sigma : ℝ =>
          if hsigma : 1 < sigma then
            ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2
          else 0)
        (𝓝[>] (1 : ℝ)) (𝓝 4) :=
  ⟨not_exists_strong_limit_criticalSquarefreeSourceFamily,
    tendsto_norm_infiniteMobiusCriticalFisherTangentLp_sq⟩

end RHTower
