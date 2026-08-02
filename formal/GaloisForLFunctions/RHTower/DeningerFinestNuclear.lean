import GaloisForLFunctions.RHTower.DeningerNuclearCompletedInvariance
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# A countable-dimensional space with the finest locally convex topology is nuclear

On a space with a basis indexed by the naturals, a positive weight sequence defines a weighted
`ℓ¹` seminorm through the coordinates of the basis expansion.  Given any seminorm `p`, weighting
by `2^n (p (b n) + 1)` produces a seminorm dominating `p` whose comparison map is the series of
rank one maps given by the coordinate functionals and the basis classes: the coordinate functional
has norm at most the inverse weight, so the norms multiply to at most `2^{-n}`.

Hence every seminorm is dominated by one with nuclear comparison map — the space is nuclear for
the family of *all* its seminorms, that is, for the finest locally convex topology.  With
permanence under subspaces this makes every subspace of a countable-dimensional space nuclear:
the situation of a test space presented as a countable strict inductive limit of finite
dimensional steps.

* `deningerBasisSeminorm` : the weighted `ℓ¹` seminorm of a basis.
* `deningerBasisCoeff` : the coordinate functionals of its quotient.
* `deningerIsNuclearSpace_finest` : **the finest locally convex topology on a
  countable-dimensional space is nuclear.**
* `deningerIsNuclearSpaceC_finest_subspace` : every subspace of such a space is nuclear.
-/

namespace RHTower

section BasisSeminorm

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **A seminorm of a finite sum is at most the sum of the seminorms.** -/
theorem deningerSeminorm_finset_sum_le (p : Seminorm 𝕜 E) {ι : Type*} (s : Finset ι)
    (f : ι → E) : p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (by gcongr)

/-- A weighted `ℓ¹` sum of coordinates, computed on any finset containing the support. -/
theorem deningerBasisSum_of_subset (c : ℕ → ℝ) (f : ℕ →₀ 𝕜) {s : Finset ℕ}
    (hs : f.support ⊆ s) : (f.sum fun n a => c n * ‖a‖) = ∑ n ∈ s, c n * ‖f n‖ :=
  Finsupp.sum_of_support_subset f hs _ fun i _ => by simp

/-- **The weighted `ℓ¹` seminorm of a basis.** -/
noncomputable def deningerBasisSeminorm (b : Module.Basis ℕ 𝕜 E) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) :
    Seminorm 𝕜 E where
  toFun x := (b.repr x).sum fun n a => c n * ‖a‖
  map_zero' := by simp
  add_le' x y := by
    classical
    have hsub : (b.repr (x + y)).support
        ⊆ (b.repr x).support ∪ (b.repr y).support := by
      rw [map_add]
      exact Finsupp.support_add
    rw [deningerBasisSum_of_subset c _ hsub,
      deningerBasisSum_of_subset c (b.repr x) Finset.subset_union_left,
      deningerBasisSum_of_subset c (b.repr y) Finset.subset_union_right,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [map_add, Finsupp.add_apply]
    calc c n * ‖b.repr x n + b.repr y n‖
        ≤ c n * (‖b.repr x n‖ + ‖b.repr y n‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (hc n)
      _ = c n * ‖b.repr x n‖ + c n * ‖b.repr y n‖ := by ring
  neg' x := by
    rw [map_neg, deningerBasisSum_of_subset c (-(b.repr x))
      (by rw [Finsupp.support_neg]), deningerBasisSum_of_subset c (b.repr x) (le_refl _)]
    exact Finset.sum_congr rfl fun n _ => by rw [Finsupp.neg_apply, norm_neg]
  smul' a x := by
    rw [map_smul, deningerBasisSum_of_subset c (a • b.repr x) Finsupp.support_smul,
      deningerBasisSum_of_subset c (b.repr x) (le_refl _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, norm_mul]
    ring

theorem deningerBasisSeminorm_apply (b : Module.Basis ℕ 𝕜 E) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (x : E) {s : Finset ℕ} (hs : (b.repr x).support ⊆ s) :
    deningerBasisSeminorm b c hc x = ∑ n ∈ s, c n * ‖b.repr x n‖ :=
  deningerBasisSum_of_subset c (b.repr x) hs

/-- **Every weighted coordinate is bounded by the weighted `ℓ¹` seminorm.** -/
theorem deningerBasisSeminorm_coord_le (b : Module.Basis ℕ 𝕜 E) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (x : E) (n : ℕ) : c n * ‖b.repr x n‖ ≤ deningerBasisSeminorm b c hc x := by
  classical
  by_cases hn : n ∈ (b.repr x).support
  · rw [deningerBasisSeminorm_apply b c hc x (le_refl _)]
    exact Finset.single_le_sum (f := fun m => c m * ‖b.repr x m‖)
      (fun m _ => mul_nonneg (hc m) (norm_nonneg _)) hn
  · have hzero : b.repr x n = 0 := by simpa using hn
    rw [hzero, norm_zero, mul_zero]
    exact apply_nonneg _ x

/-- **A seminorm is dominated by the weighted `ℓ¹` seminorm of weights bounding it on the
basis.** -/
theorem deningerSeminorm_le_basisSeminorm (b : Module.Basis ℕ 𝕜 E) (p : Seminorm 𝕜 E) (c : ℕ → ℝ)
    (hc : ∀ n, 0 ≤ c n) (hpc : ∀ n, p (b n) ≤ c n) (x : E) :
    p x ≤ deningerBasisSeminorm b c hc x := by
  classical
  have hx : x = ∑ n ∈ (b.repr x).support, b.repr x n • b n := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [deningerBasisSeminorm_apply b c hc x (le_refl _)]
  conv_lhs => rw [hx]
  refine le_trans (deningerSeminorm_finset_sum_le p _ _) (Finset.sum_le_sum fun n _ => ?_)
  rw [map_smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _) |>.trans (le_of_eq (mul_comm _ _))
  exact hpc n

end BasisSeminorm

section FinestNuclear

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The `n`-th coordinate of a basis expansion, as a linear functional. -/
noncomputable def deningerBasisCoeffLinear (b : Module.Basis ℕ 𝕜 E) (n : ℕ) : E →ₗ[𝕜] 𝕜 :=
  (Finsupp.lapply n).comp (b.repr : E →ₗ[𝕜] ℕ →₀ 𝕜)

theorem deningerBasisCoeff_ker (b : Module.Basis ℕ 𝕜 E) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcpos : ∀ n, 0 < c n) (n : ℕ) :
    deningerSeminormKer (deningerBasisSeminorm b c hc)
      ≤ LinearMap.ker (deningerBasisCoeffLinear b n) := by
  intro x hx
  have hzero : deningerBasisSeminorm b c hc x = 0 := hx
  have hle := deningerBasisSeminorm_coord_le b c hc x n
  rw [hzero] at hle
  have hnorm : ‖b.repr x n‖ = 0 := by
    nlinarith [norm_nonneg (b.repr x n), hcpos n]
  exact norm_eq_zero.mp hnorm

/-- **The coordinate functionals of the weighted `ℓ¹` quotient**, of norm at most the inverse
weight. -/
noncomputable def deningerBasisCoeff (b : Module.Basis ℕ 𝕜 E) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcpos : ∀ n, 0 < c n) (n : ℕ) :
    DeningerSeminormSpace (deningerBasisSeminorm b c hc) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    (Submodule.liftQ (deningerSeminormKer (deningerBasisSeminorm b c hc))
      (deningerBasisCoeffLinear b n) (deningerBasisCoeff_ker b c hc hcpos n))
    (c n)⁻¹
    (by
      rintro ⟨a⟩
      show ‖b.repr a n‖ ≤ (c n)⁻¹ * deningerBasisSeminorm b c hc a
      rw [le_inv_mul_iff₀ (hcpos n)]
      exact deningerBasisSeminorm_coord_le b c hc a n)

theorem deningerBasisCoeff_mk (b : Module.Basis ℕ 𝕜 E) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcpos : ∀ n, 0 < c n) (n : ℕ) (x : E) :
    deningerBasisCoeff b c hc hcpos n (deningerSeminormMk (deningerBasisSeminorm b c hc) x)
      = b.repr x n := rfl

theorem deningerBasisCoeff_norm_le (b : Module.Basis ℕ 𝕜 E) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcpos : ∀ n, 0 < c n) (n : ℕ) :
    ‖deningerBasisCoeff b c hc hcpos n‖ ≤ (c n)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr (hcpos n).le) _

/-- **The finest locally convex topology on a countable-dimensional space is nuclear.**  Weighting
the coordinates of a basis by `2^n (p (b n) + 1)` dominates the given seminorm `p`, and the
comparison map is the series of rank one maps given by the coordinate functionals and the basis
classes, whose norms multiply to at most `2^{-n}`. -/
theorem deningerIsNuclearSpace_finest (b : Module.Basis ℕ 𝕜 E) :
    DeningerIsNuclearSpace (fun p : Seminorm 𝕜 E => p) := by
  classical
  intro p
  obtain ⟨c, hcval⟩ : ∃ c : ℕ → ℝ, ∀ n, c n = 2 ^ n * (p (b n) + 1) :=
    ⟨fun n => 2 ^ n * (p (b n) + 1), fun n => rfl⟩
  have hcpos : ∀ n, 0 < c n := by
    intro n
    have hP : (0 : ℝ) ≤ p (b n) := apply_nonneg p (b n)
    rw [hcval n]
    positivity
  have hc : ∀ n, 0 ≤ c n := fun n => (hcpos n).le
  have hpc : ∀ n, p (b n) ≤ c n := by
    intro n
    have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [hcval n]
    nlinarith [apply_nonneg p (b n)]
  refine ⟨deningerBasisSeminorm b c hc, 1, fun x => ?_, ?_⟩
  · rw [one_mul]
    exact deningerSeminorm_le_basisSeminorm b p c hc hpc x
  · refine ⟨ℕ, fun n => deningerBasisCoeff b c hc hcpos n,
      fun n => deningerSeminormMk p (b n), ?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        summable_geometric_two
      have hP : (0 : ℝ) ≤ p (b n) := apply_nonneg p (b n)
      have hpos : (0 : ℝ) < 2 ^ n * (p (b n) + 1) := by positivity
      have hstep : ‖deningerBasisCoeff b c hc hcpos n‖ * ‖deningerSeminormMk p (b n)‖
          ≤ (c n)⁻¹ * p (b n) := by
        rw [deningerSeminormMk_norm]
        exact mul_le_mul_of_nonneg_right (deningerBasisCoeff_norm_le b c hc hcpos n) hP
      refine hstep.trans ?_
      rw [hcval n, inv_mul_le_iff₀ hpos, one_div, inv_pow]
      have hcancel : (2 : ℝ) ^ n * (p (b n) + 1) * ((2 : ℝ) ^ n)⁻¹ = p (b n) + 1 := by
        field_simp
      rw [hcancel]
      linarith
    · intro x
      obtain ⟨a, rfl⟩ := deningerSeminormMk_surjective (deningerBasisSeminorm b c hc) x
      have hsupp : ∀ n ∉ (b.repr a).support,
          deningerBasisCoeff b c hc hcpos n
              (deningerSeminormMk (deningerBasisSeminorm b c hc) a) •
            deningerSeminormMk p (b n) = 0 := by
        intro n hn
        rw [deningerBasisCoeff_mk]
        have : b.repr a n = 0 := by simpa using hn
        rw [this, zero_smul]
      have hval : ∑ n ∈ (b.repr a).support,
          deningerBasisCoeff b c hc hcpos n
              (deningerSeminormMk (deningerBasisSeminorm b c hc) a) •
            deningerSeminormMk p (b n)
          = deningerSeminormMk p a := by
        have hx : a = ∑ n ∈ (b.repr a).support, b.repr a n • b n := by
          conv_lhs => rw [← b.linearCombination_repr a]
          rw [Finsupp.linearCombination_apply, Finsupp.sum]
        conv_rhs => rw [hx]
        rw [map_sum]
        exact Finset.sum_congr rfl fun n _ => by
          rw [deningerBasisCoeff_mk, map_smul]
      rw [deningerSeminormComparison_mk, ← hval]
      exact hasSum_sum_of_ne_finset_zero hsupp

end FinestNuclear

section FinestCountable

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-- **The finest locally convex topology on a space with a countable basis is nuclear.**  A finite
basis makes every seminorm quotient finite dimensional; a countably infinite one is reindexed by
the naturals. -/
theorem deningerIsNuclearSpace_finest_of_countable {ι : Type*} [Countable ι]
    (b : Module.Basis ι 𝕜 E) : DeningerIsNuclearSpace (fun p : Seminorm 𝕜 E => p) := by
  rcases finite_or_infinite ι with _ | _
  · haveI : FiniteDimensional 𝕜 E := Module.Finite.of_basis b
    refine deningerIsNuclearSpace_of_finiteDimensional _ fun p => ?_
    exact inferInstanceAs (FiniteDimensional 𝕜 (E ⧸ deningerSeminormKer p))
  · obtain ⟨e⟩ : Nonempty (ι ≃ ℕ) := ⟨(nonempty_denumerable ι).some.eqv⟩
    exact deningerIsNuclearSpace_finest (b.reindex e)

end FinestCountable

section FinestSubspace

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Every subspace of a countable-dimensional space with the finest locally convex topology is
nuclear.**  This is the case of a test space presented as a countable strict inductive limit of
finite dimensional steps, together with a closed subspace of it. -/
theorem deningerIsNuclearSpaceC_finest_subspace {ι : Type*} [Countable ι]
    (b : Module.Basis ι 𝕜 E) (F : Submodule 𝕜 E) :
    DeningerIsNuclearSpaceC (fun p : Seminorm 𝕜 E => deningerRestrictSeminorm F p) :=
  deningerIsNuclearSpaceC_subspace _ F (deningerIsNuclearSpace_finest_of_countable b)

end FinestSubspace

end RHTower
