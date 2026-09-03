import GaloisForLFunctions.HTGeometry.NonautonomousFinitePuiseuxBranchNonzero

/-!
# Canonical velocity factorization in the finite nonautonomous branch field

Successive nonzero state derivatives canonically recover every constituent velocity as their
ratio.  Reversing the finite coordinates to match the Newton-corner convention makes each suffix
product telescope exactly to the derivative of the corresponding cascade state.  Thus the
velocity and state-derivative fields of the Puiseux selection interface require no choice.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

/-- A product of successive nonzero ratios telescopes. -/
theorem prod_range_succ_div_self {F : Type*} [Field F]
    (D : ℕ → F) (hD : ∀ i, D i ≠ 0) (m : ℕ) :
    ∏ j ∈ Finset.range m, D (j + 1) / D j = D m / D 0 := by
  induction m with
  | zero => simp [hD]
  | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      field_simp [hD]

/-- A successive ratio written in the reversed finite-coordinate convention. -/
def reversedSuccessiveRatio {F : Type*} [Field F] {N : ℕ}
    (D : ℕ → F) (j : Fin N) : F :=
  D (j.rev.val + 1) / D j.rev.val

/-- A reversed suffix is precisely an ordinary initial segment, so its ratio product telescopes. -/
theorem prod_reversedSuccessiveRatio_suffix {F : Type*} [Field F] {N : ℕ}
    (D : ℕ → F) (hD : ∀ i, D i ≠ 0) (k : Fin N) :
    ∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)),
        reversedSuccessiveRatio D j =
      D (k.rev.val + 1) / D 0 := by
  have hreindex :
      (∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)),
        reversedSuccessiveRatio D j) =
      ∏ q ∈ Finset.range (k.rev.val + 1), D (q + 1) / D q := by
    apply Finset.prod_bij (fun j _ => j.rev.val)
    · intro j hj
      rw [Finset.mem_range]
      rw [Finset.mem_filter] at hj
      have hrev : j.rev ≤ k.rev := Fin.rev_le_rev.mpr hj.2
      omega
    · intro a ha b hb hab
      apply Fin.rev_injective
      exact Fin.ext hab
    · intro q hq
      rw [Finset.mem_range] at hq
      let qk : Fin N := ⟨q, by omega⟩
      refine ⟨qk.rev, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hqle : qk ≤ k.rev := by
          change q ≤ k.rev.val
          omega
        exact (Fin.rev_le_rev (i := qk.rev) (j := k)).mp (by simpa using hqle)
      · simp [qk]
    · intro j hj
      simp only [reversedSuccessiveRatio]
  rw [hreindex]
  simpa using prod_range_succ_div_self D hD (k.rev.val + 1)

/-- Canonical actual constituent velocity in reversed Newton-corner coordinates. -/
noncomputable def nonautonomousFiniteCascadeVelocityInBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {N : ℕ} (j : Fin N) : NonautonomousFiniteCascadeBranchField hfan N :=
  nonautonomousFiniteCascadeDerivativeInBranchField hfan N
      ⟨j.rev.val + 1, by omega⟩ /
    nonautonomousFiniteCascadeDerivativeInBranchField hfan N
      ⟨j.rev.val, by omega⟩

@[simp] theorem nonautonomousFiniteCascadeVelocityInBranchField_coe
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    {N : ℕ} (j : Fin N) :
    ((nonautonomousFiniteCascadeVelocityInBranchField hfan j :
      NonautonomousFiniteCascadeBranchField hfan N) : meroField Set.univ) =
      cascadeMeroDeriv hfan (j.rev.val + 1) / cascadeMeroDeriv hfan j.rev.val := by
  rfl

/-- Every canonical constituent velocity is nonzero. -/
theorem nonautonomousFiniteCascadeVelocityInBranchField_ne_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ} (j : Fin N) :
    nonautonomousFiniteCascadeVelocityInBranchField hfan j ≠ 0 := by
  exact div_ne_zero
    (nonautonomousFiniteCascadeDerivativeInBranchField_ne_zero hfan hall N _)
    (nonautonomousFiniteCascadeDerivativeInBranchField_ne_zero hfan hall N _)

/-- The reversed suffix product of canonical velocities is the actual derivative of that state. -/
theorem nonautonomousFiniteCascadeVelocity_suffix_product
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {N : ℕ} (k : Fin N) :
    ∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)),
        nonautonomousFiniteCascadeVelocityInBranchField hfan j =
      nonautonomousFiniteCascadeDerivativeInBranchField hfan N
        ⟨k.rev.val + 1, by omega⟩ := by
  apply (nonautonomousFiniteBranchEmbedding hfan N).injective
  rw [map_prod]
  change (∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)),
      ((nonautonomousFiniteCascadeVelocityInBranchField hfan j :
        NonautonomousFiniteCascadeBranchField hfan N) : meroField Set.univ)) =
    ((nonautonomousFiniteCascadeDerivativeInBranchField hfan N
      ⟨k.rev.val + 1, by omega⟩ : NonautonomousFiniteCascadeBranchField hfan N) :
        meroField Set.univ)
  rw [Finset.prod_congr rfl fun j _ =>
    nonautonomousFiniteCascadeVelocityInBranchField_coe hfan j]
  change (∏ j ∈ Finset.univ.filter (fun j : Fin N => (k : ℕ) ≤ (j : ℕ)),
      reversedSuccessiveRatio (fun q => cascadeMeroDeriv hfan q) j) = _
  rw [prod_reversedSuccessiveRatio_suffix
    (fun q => cascadeMeroDeriv hfan q)
    (fun q => cascadeMeroDeriv_ne_zero_of_transcendental hfan hall q) k]
  rw [nonautonomousFiniteCascadeDerivativeInBranchField_coe,
    cascadeMeroDeriv_zero, div_one]

end

end GaloisForLFunctions.HTGeometry
