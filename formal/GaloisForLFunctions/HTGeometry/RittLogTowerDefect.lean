import GaloisForLFunctions.HTGeometry.RittAffineJetTower

/-!
# The shift defect of the affine jet tower

The `m`-th level of the affine tower shifts by its own multiplier plus a defect

`δ_m = ∑_{j < m} a_{m,j} · d^[j] u + b_m`

which lies in the previous prefix field and is a `K`-affine combination of the lower jets.  Its top
coefficient `a_{m,m−1}` is nonzero for every `m ≥ 1`, so the defect is never a base element; and at
level zero the defect is the base constant `b`, nonzero as soon as the chain-rule factor is not a
derivation constant.  These two facts are what make every inhomogeneity produced by the descent
nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The shift defect of the affine tower at level `m`. -/
noncomputable def towerDefect (Fr : RittFrame K L) (u : L) (b : K) (m : ℕ) : L :=
  (∑ j ∈ Finset.range m, algebraMap K L (Fr.logCoeff m j) * Fr.d^[j] u)
    + algebraMap K L (Fr.logConst b m)

theorem towerDefect_zero (Fr : RittFrame K L) (u : L) (b : K) :
    Fr.towerDefect u b 0 = algebraMap K L b := by
  simp [towerDefect, logConst]

theorem towerDefect_mem (Fr : RittFrame K L) (u : L) (b : K) (m : ℕ) :
    Fr.towerDefect u b m ∈ Fr.jetPrefixField u m := by
  refine add_mem (sum_mem fun j hj => ?_) (IntermediateField.algebraMap_mem _ _)
  exact mul_mem (IntermediateField.algebraMap_mem _ _)
    (Fr.jet_mem_jetPrefixField (by simpa only [Finset.mem_range] using hj))

/-- **The shift of the top jet, with its defect split off.** -/
theorem sigma_jet_eq_defect (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b) (m : ℕ) :
    Fr.σ (Fr.d^[m] u)
      = algebraMap K L ((Fr.ρ ^ (m + 1))⁻¹) * Fr.d^[m] u + Fr.towerDefect u b m := by
  rw [Fr.sigma_affineJet hu m, Finset.sum_range_succ, Fr.logCoeff_diag m, towerDefect]
  ring

/-- The defect of a tower level above the bottom is not a base element. -/
theorem towerDefect_notMem_range [CharZero K] (Fr : RittFrame K L) {u : L} {b : K} (hdρ : Fr.dK Fr.ρ ≠ 0)
    {m : ℕ} (hm : 1 ≤ m) (htr : Transcendental ↥(Fr.jetPrefixField u (m - 1)) (Fr.d^[m - 1] u)) :
    ∀ κ : K, algebraMap K L κ ≠ Fr.towerDefect u b m := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨m - 1, by omega⟩
  intro κ hκ
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hsub : Fr.logCoeff (n + 1) n ≠ 0 := by
    rw [Fr.logCoeff_subdiag n]
    have hc : (((n + 2).choose 2 : ℕ) : K) ≠ 0 := by
      have hpos : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
      exact Nat.cast_ne_zero.mpr (by omega)
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hc) (inv_ne_zero (pow_ne_zero _ hρ0))) hdρ
  -- the top jet is a rational expression in the lower ones
  have hmem : Fr.d^[n] u ∈ Fr.jetPrefixField u n := by
    have hrest : (algebraMap K L κ - algebraMap K L (Fr.logConst b (n + 1))
        - ∑ j ∈ Finset.range n, algebraMap K L (Fr.logCoeff (n + 1) j) * Fr.d^[j] u)
        ∈ Fr.jetPrefixField u n := by
      refine sub_mem (sub_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.algebraMap_mem _ _)) (sum_mem fun j hj => ?_)
      exact mul_mem (IntermediateField.algebraMap_mem _ _)
        (Fr.jet_mem_jetPrefixField (by simpa only [Finset.mem_range] using hj))
    have hne : algebraMap K L (Fr.logCoeff (n + 1) n) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K L).injective).mpr hsub
    have hsplit : Fr.d^[n] u
        = (algebraMap K L κ - algebraMap K L (Fr.logConst b (n + 1))
          - ∑ j ∈ Finset.range n, algebraMap K L (Fr.logCoeff (n + 1) j) * Fr.d^[j] u)
          / algebraMap K L (Fr.logCoeff (n + 1) n) := by
      rw [towerDefect, Finset.sum_range_succ] at hκ
      rw [eq_div_iff hne]
      linear_combination -hκ
    rw [hsplit]
    exact div_mem hrest (IntermediateField.algebraMap_mem _ _)
  simp only [Nat.add_sub_cancel] at htr
  exact htr (isAlgebraic_algebraMap (⟨Fr.d^[n] u, hmem⟩ : ↥(Fr.jetPrefixField u n)))

end RittFrame

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The part of the defect of level `m + 1` that lies one level further down. -/
noncomputable def towerDefectLow (Fr : RittFrame K L) (u : L) (b : K) (m : ℕ) : L :=
  (∑ j ∈ Finset.range m, algebraMap K L (Fr.logCoeff (m + 1) j) * Fr.d^[j] u)
    + algebraMap K L (Fr.logConst b (m + 1))

theorem towerDefectLow_mem (Fr : RittFrame K L) (u : L) (b : K) (m : ℕ) :
    Fr.towerDefectLow u b m ∈ Fr.jetPrefixField u m := by
  refine add_mem (sum_mem fun j hj => ?_) (IntermediateField.algebraMap_mem _ _)
  exact mul_mem (IntermediateField.algebraMap_mem _ _)
    (Fr.jet_mem_jetPrefixField (by simpa only [Finset.mem_range] using hj))

/-- The defect of level `m + 1`, split into its top jet component and the rest. -/
theorem towerDefect_succ_split (Fr : RittFrame K L) (u : L) (b : K) (m : ℕ) :
    Fr.towerDefect u b (m + 1)
      = algebraMap K L (Fr.logCoeff (m + 1) m) * Fr.d^[m] u + Fr.towerDefectLow u b m := by
  rw [towerDefect, towerDefectLow, Finset.sum_range_succ]
  ring

end RittFrame

end GaloisForLFunctions.HTGeometry
