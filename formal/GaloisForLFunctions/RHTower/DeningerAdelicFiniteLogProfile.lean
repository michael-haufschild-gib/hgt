import GaloisForLFunctions.RHTower.DeningerAdelicPlaceAverageResidue

namespace RHTower

open NumberField

section ProductFormula

variable {K : Type*} [Field K] [NumberField K]

/-- The finite-place logarithms of a global unit, as a finitely supported local profile. -/
noncomputable def deningerFinitePlaceLogProfile (α : Kˣ) : FinitePlace K →₀ ℝ :=
  Finsupp.onFinset
    (NumberField.FinitePlace.hasFiniteMulSupport (Units.ne_zero α)).toFinset
    (fun w => Real.log (w (α : K)))
    (by
      intro w hw
      exact (NumberField.FinitePlace.hasFiniteMulSupport (Units.ne_zero α)).mem_toFinset.mpr
        (by
          intro hwone
          exact hw (by simp [hwone])))

theorem deningerFinitePlaceLogProfile_apply (α : Kˣ) (w : FinitePlace K) :
    deningerFinitePlaceLogProfile α w = Real.log (w (α : K)) :=
  Finsupp.onFinset_apply

/-- The finite local profile and weighted archimedean logarithms satisfy global reciprocity. -/
theorem deningerFinitePlaceLogProfile_global_reciprocity (α : Kˣ) :
    (∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w (α : K))) +
      (deningerFinitePlaceLogProfile α).sum (fun _ a => a) = 0 := by
  classical
  let s := (NumberField.FinitePlace.hasFiniteMulSupport (Units.ne_zero α)).toFinset
  have hsupp : (deningerFinitePlaceLogProfile α).support ⊆ s := by
    exact Finsupp.support_onFinset_subset
  rw [Finsupp.sum_of_support_subset _ hsupp]
  · simp only [deningerFinitePlaceLogProfile_apply]
    simpa [s] using deningerLog_prod_abs_eq_zero (Units.ne_zero α) _
      (deningerMulSupport_subset_toFinset (Units.ne_zero α))
  · simp

/-- The global logarithmic Kummer map into archimedean and finitely supported finite profiles. -/
noncomputable def deningerGlobalLogProfile :
    Kˣ →* Multiplicative ((InfinitePlace K → ℝ) × (FinitePlace K →₀ ℝ)) where
  toFun α := Multiplicative.ofAdd
    (fun w => (w.mult : ℝ) * Real.log (w (α : K)), deningerFinitePlaceLogProfile α)
  map_one' := by
    change (fun (w : InfinitePlace K) => (w.mult : ℝ) * Real.log (w ((1 : Kˣ) : K)),
      deningerFinitePlaceLogProfile 1) = 0
    ext w
    · simp
    · rw [deningerFinitePlaceLogProfile_apply]
      simp
  map_mul' α β := by
    change (fun (w : InfinitePlace K) => (w.mult : ℝ) * Real.log (w ((α * β : Kˣ) : K)),
      deningerFinitePlaceLogProfile (α * β)) =
      (fun (w : InfinitePlace K) => (w.mult : ℝ) * Real.log (w (α : K)),
        deningerFinitePlaceLogProfile α) +
        (fun (w : InfinitePlace K) => (w.mult : ℝ) * Real.log (w (β : K)),
          deningerFinitePlaceLogProfile β)
    ext w
    · simp only [Prod.fst_add, Pi.add_apply]
      change (w.mult : ℝ) * Real.log (w ((α : K) * (β : K))) = _
      rw [map_mul, Real.log_mul]
      · ring
      · exact (InfinitePlace.pos_iff.mpr (Units.ne_zero α)).ne'
      · exact (InfinitePlace.pos_iff.mpr (Units.ne_zero β)).ne'
    · simp only [Prod.snd_add, Finsupp.add_apply, deningerFinitePlaceLogProfile_apply]
      change Real.log (w ((α : K) * (β : K))) = _
      rw [map_mul, Real.log_mul]
      · exact (FinitePlace.pos_iff.mpr (Units.ne_zero α)).ne'
      · exact (FinitePlace.pos_iff.mpr (Units.ne_zero β)).ne'

/-- Summation of archimedean and finite local logarithmic coordinates. -/
noncomputable def deningerGlobalLogSum :
    ((InfinitePlace K → ℝ) × (FinitePlace K →₀ ℝ)) →+ ℝ where
  toFun x := (∑ w : InfinitePlace K, x.1 w) + x.2.sum (fun _ a => a)
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Pi.add_apply, Prod.snd_add]
    rw [Finset.sum_add_distrib, Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    ring

/-- Global logarithmic profiles land in the reciprocal (zero-sum) local subgroup. -/
theorem deningerGlobalLogProfile_mem_ker (α : Kˣ) :
    Multiplicative.toAdd (deningerGlobalLogProfile α) ∈ deningerGlobalLogSum.ker := by
  exact deningerFinitePlaceLogProfile_global_reciprocity α

/-- The global logarithmic Kummer map with its reciprocal local codomain. -/
noncomputable def deningerGlobalLogProfileToKernel :
    Kˣ →* Multiplicative (deningerGlobalLogSum (K := K)).ker where
  toFun α := Multiplicative.ofAdd
    ⟨Multiplicative.toAdd (deningerGlobalLogProfile (K := K) α),
      deningerGlobalLogProfile_mem_ker (K := K) α⟩
  map_one' := by
    change Multiplicative.ofAdd
      (⟨Multiplicative.toAdd (deningerGlobalLogProfile (K := K) 1), _⟩ :
        (deningerGlobalLogSum (K := K)).ker) = 1
    rw [(deningerGlobalLogProfile (K := K)).map_one]
    rfl
  map_mul' α β := by
    change Multiplicative.ofAdd
      (⟨Multiplicative.toAdd (deningerGlobalLogProfile (K := K) (α * β)), _⟩ :
        (deningerGlobalLogSum (K := K)).ker) =
      Multiplicative.ofAdd
        (⟨Multiplicative.toAdd (deningerGlobalLogProfile (K := K) α), _⟩ :
          (deningerGlobalLogSum (K := K)).ker) *
        Multiplicative.ofAdd
          (⟨Multiplicative.toAdd (deningerGlobalLogProfile (K := K) β), _⟩ :
            (deningerGlobalLogSum (K := K)).ker)
    rw [(deningerGlobalLogProfile (K := K)).map_mul]
    rfl

theorem deningerGlobalLogProfileToKernel_coe (α : Kˣ) :
    ((Multiplicative.toAdd (deningerGlobalLogProfileToKernel (K := K) α) :
      (deningerGlobalLogSum (K := K)).ker) :
        (InfinitePlace K → ℝ) × (FinitePlace K →₀ ℝ)) =
      Multiplicative.toAdd (deningerGlobalLogProfile (K := K) α) := rfl

end ProductFormula

end RHTower
