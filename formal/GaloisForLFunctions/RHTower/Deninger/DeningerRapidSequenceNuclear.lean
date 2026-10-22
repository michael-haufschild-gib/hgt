import GaloisForLFunctions.RHTower.Deninger.DeningerRapidSequenceSpace

/-!
# The space of rapidly decreasing sequences is nuclear

A rapidly decreasing sequence is the sum of its coordinates, the sum converging in every weighted
seminorm.  Written out, that expresses the comparison map from the `(k+2)`-nd to the `k`-th
seminorm quotient as the series of rank one maps `a ↦ a n` times the class of the `n`-th basis
vector.  The coordinate functional has norm at most `(n+1)^{-(k+2)}` and the basis class has norm
`(n+1)^k`, so the series of products is dominated by `∑ (n+1)^{-2}` and the comparison map is
nuclear.

The space of rapidly decreasing sequences is therefore a nuclear space which is not finite
dimensional, so the nuclearity theory is not vacuous, and all of its permanence properties apply
to it.

* `deningerRapidCoeff` : the coordinate functionals of the seminorm quotients.
* `deningerHasSum_of_hilbertian` : a series converges in a Hilbertian quotient as soon as its
  image in `ℓ²` converges.
* `deningerRapid_isNuclearSpace` : **the rapidly decreasing sequences form a nuclear space.**
* `deningerRapid_not_finiteDimensional` : it is not finite dimensional.
-/

namespace RHTower

open scoped ENNReal

section HasSumTransfer

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {κ : Type} {p : Seminorm 𝕜 E} {A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2}

/-- **A series converges in a Hilbertian seminorm quotient as soon as its image in `ℓ²`
converges**, the embedding into `ℓ²` being an isometry. -/
theorem deningerHasSum_of_hilbertian (hA : ∀ x, p x = ‖A x‖) {ι : Type*}
    {f : ι → DeningerSeminormSpace p} {x : DeningerSeminormSpace p}
    (h : HasSum (fun i => deningerHilbertianEmbedding hA (f i))
      (deningerHilbertianEmbedding hA x)) : HasSum f x := by
  rw [HasSum] at h ⊢
  refine ((deningerHilbertianEmbedding_isometry hA).isEmbedding.tendsto_nhds_iff).mpr ?_
  simpa [map_sum, Function.comp_def] using h

end HasSumTransfer

section RapidNuclear

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The `n`-th coordinate of a rapidly decreasing sequence, as a linear functional. -/
def deningerRapidCoeffLinear (n : ℕ) : DeningerRapidCarrier 𝕜 →ₗ[𝕜] 𝕜 where
  toFun a := (a : ℕ → 𝕜) n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem deningerRapidCoeff_ker (k n : ℕ) :
    deningerSeminormKer (deningerRapidSeminorm (𝕜 := 𝕜) k)
      ≤ LinearMap.ker (deningerRapidCoeffLinear (𝕜 := 𝕜) n) := by
  intro a ha
  have hzero : deningerRapidSeminorm (𝕜 := 𝕜) k a = 0 := ha
  have h := deningerRapidWeight_norm_mul_le k n a
  rw [hzero] at h
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ k := by positivity
  have hnorm : ‖(a : ℕ → 𝕜) n‖ = 0 := by
    nlinarith [norm_nonneg ((a : ℕ → 𝕜) n)]
  exact norm_eq_zero.mp hnorm

/-- **The coordinate functionals of the seminorm quotients**, of norm at most `(n+1)^{-k}`. -/
noncomputable def deningerRapidCoeff (k n : ℕ) :
    DeningerSeminormSpace (deningerRapidSeminorm (𝕜 := 𝕜) k) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    (Submodule.liftQ (deningerSeminormKer (deningerRapidSeminorm (𝕜 := 𝕜) k))
      (deningerRapidCoeffLinear n) (deningerRapidCoeff_ker k n))
    (((n : ℝ) + 1) ^ k)⁻¹
    (by
      rintro ⟨a⟩
      have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ k := by positivity
      show ‖(a : ℕ → 𝕜) n‖ ≤ (((n : ℝ) + 1) ^ k)⁻¹ * deningerRapidSeminorm (𝕜 := 𝕜) k a
      rw [le_inv_mul_iff₀ hpos]
      exact deningerRapidWeight_norm_mul_le k n a)

@[simp]
theorem deningerRapidCoeff_mk (k n : ℕ) (a : DeningerRapidCarrier 𝕜) :
    deningerRapidCoeff k n (deningerSeminormMk (deningerRapidSeminorm (𝕜 := 𝕜) k) a)
      = (a : ℕ → 𝕜) n := rfl

theorem deningerRapidCoeff_norm_le (k n : ℕ) :
    ‖deningerRapidCoeff (𝕜 := 𝕜) k n‖ ≤ (((n : ℝ) + 1) ^ k)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- **A rapidly decreasing sequence is the sum of its coordinates**, in every weighted seminorm
quotient. -/
theorem deningerRapid_hasSum_basis (k : ℕ) (a : DeningerRapidCarrier 𝕜) :
    HasSum (fun n => (a : ℕ → 𝕜) n •
        deningerSeminormMk (deningerRapidSeminorm (𝕜 := 𝕜) k) (deningerRapidBasis 𝕜 n))
      (deningerSeminormMk (deningerRapidSeminorm (𝕜 := 𝕜) k) a) := by
  have hA : ∀ x : DeningerRapidCarrier 𝕜,
      deningerRapidSeminorm (𝕜 := 𝕜) k x = ‖deningerRapidMap k x‖ := fun _ => rfl
  refine deningerHasSum_of_hilbertian hA ?_
  have hsingle := lp.hasSum_single (E := fun _ : ℕ => 𝕜) (p := 2) (by norm_num)
    (deningerRapidMap k a)
  have hfun : (fun n => deningerHilbertianEmbedding hA ((a : ℕ → 𝕜) n •
        deningerSeminormMk (deningerRapidSeminorm (𝕜 := 𝕜) k) (deningerRapidBasis 𝕜 n)))
      = fun n => lp.single 2 n ((deningerRapidMap k a : ℕ → 𝕜) n) := by
    funext n
    rw [map_smul, deningerHilbertianEmbedding_mk, deningerRapidMap_basis]
    refine Subtype.ext (funext fun m => ?_)
    rw [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, lp.single_apply, smul_eq_mul,
      deningerRapidMap_apply]
    by_cases h : m = n
    · subst h
      simp [mul_comm]
    · simp [Pi.single_eq_of_ne h]
  rw [hfun]
  exact hsingle

theorem deningerRapid_summable_norm (k : ℕ) :
    Summable fun n : ℕ => (((n : ℝ) + 1) ^ (k + 2))⁻¹ * ((n : ℝ) + 1) ^ k := by
  have h1 : Summable fun n : ℕ => 1 / ((n : ℝ)) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have h2 : Summable fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2 := (summable_nat_add_iff 1).mpr h1
  refine h2.congr fun n => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  push_cast
  rw [pow_add]
  field_simp

/-- **The rapidly decreasing sequences form a nuclear space.**  The comparison map from the
`(k+2)`-nd to the `k`-th seminorm quotient is the series of rank one maps given by the coordinate
functionals and the basis classes, whose norms multiply to a summable family. -/
theorem deningerRapid_isNuclearSpace :
    DeningerIsNuclearSpace (deningerRapidSeminorm (𝕜 := 𝕜)) := by
  intro k
  have hdom : ∀ a : DeningerRapidCarrier 𝕜,
      deningerRapidSeminorm (𝕜 := 𝕜) k a ≤ 1 * deningerRapidSeminorm (𝕜 := 𝕜) (k + 2) a := by
    intro a
    rw [one_mul]
    exact deningerRapidSeminorm_le (Nat.le_add_right k 2) a
  refine ⟨k + 2, 1, hdom, ℕ, fun n => deningerRapidCoeff (k + 2) n,
    fun n => deningerSeminormMk (deningerRapidSeminorm (𝕜 := 𝕜) k) (deningerRapidBasis 𝕜 n), ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (deningerRapid_summable_norm k)
    refine mul_le_mul (deningerRapidCoeff_norm_le (k + 2) n) ?_ (norm_nonneg _) (by positivity)
    rw [deningerSeminormMk_norm, deningerRapidSeminorm_basis]
  · intro x
    obtain ⟨a, rfl⟩ := deningerSeminormMk_surjective (deningerRapidSeminorm (𝕜 := 𝕜) (k + 2)) x
    exact deningerRapid_hasSum_basis k a

theorem deningerRapid_isNuclearSpaceC :
    DeningerIsNuclearSpaceC (deningerRapidSeminorm (𝕜 := 𝕜)) :=
  DeningerIsNuclearSpace.toC _ deningerRapid_isNuclearSpace

/-- **Every subspace of the rapidly decreasing sequences is nuclear.** -/
theorem deningerRapid_subspace_isNuclearSpaceC (F : Submodule 𝕜 (DeningerRapidCarrier 𝕜)) :
    DeningerIsNuclearSpaceC fun k =>
      deningerRestrictSeminorm F (deningerRapidSeminorm (𝕜 := 𝕜) k) :=
  deningerIsNuclearSpaceC_subspace _ F deningerRapid_isNuclearSpace

theorem deningerRapidBasis_linearIndependent :
    LinearIndependent 𝕜 (deningerRapidBasis 𝕜) := by
  rw [linearIndependent_iff']
  intro s g hg n hn
  have hcoord : ((∑ i ∈ s, g i • deningerRapidBasis 𝕜 i : DeningerRapidCarrier 𝕜) : ℕ → 𝕜) n
      = g n := by
    rw [Submodule.coe_sum]
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single n]
    · simp
    · intro m _ hmn
      simp [Pi.single_eq_of_ne (Ne.symm hmn)]
    · intro hns
      exact absurd hn hns
  rw [hg] at hcoord
  simpa using hcoord.symm

/-- **The space of rapidly decreasing sequences is not finite dimensional**, so the nuclearity
theory is not exhausted by the finite dimensional case. -/
theorem deningerRapid_not_finiteDimensional :
    ¬ FiniteDimensional 𝕜 (DeningerRapidCarrier 𝕜) := by
  intro hfin
  haveI : Finite ℕ := (deningerRapidBasis_linearIndependent (𝕜 := 𝕜)).finite_of_isNoetherian
  exact not_finite ℕ

end RapidNuclear

end RHTower
