import GaloisForLFunctions.HTGeometry.HardyDiskModelSpace

/-!
# The model space of a finite Blaschke product has dimension its degree

`hardy-cyclicity-maximal-ht-field-blindness`, equation `(7)`.

Peeling one Blaschke factor at a time and using the orthogonal splitting

```text
(T V)ᗮ = (range T)ᗮ ⊕ T(Vᗮ)      (T an isometry)
```

gives `dim (H²(D) ⊖ B·H²(D)) = deg B`, with multiplicities counted correctly because the peeling
is by factors, not by distinct zeros.
-/

open Complex Filter Metric Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Orthogonal splitting across an isometry -/

section Splitting

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem inner_map_map_of_isometry {T : H →L[ℂ] H} (hT : ∀ x, ‖T x‖ = ‖x‖) (x y : H) :
    (inner ℂ ((T : H →ₗ[ℂ] H) x) ((T : H →ₗ[ℂ] H) y) : ℂ) = inner ℂ x y := by
  let hTi : H →ₗᵢ[ℂ] H := ⟨(T : H →ₗ[ℂ] H), hT⟩
  exact hTi.inner_map_map x y

theorem map_le_range_linear (T : H →L[ℂ] H) (V : Submodule ℂ H) :
    V.map (T : H →ₗ[ℂ] H) ≤ LinearMap.range (T : H →ₗ[ℂ] H) := by
  rintro w ⟨v, -, rfl⟩
  exact ⟨v, rfl⟩

theorem isClosed_coe_range_of_isometry {T : H →L[ℂ] H} (hT : ∀ x, ‖T x‖ = ‖x‖) :
    IsClosed ((LinearMap.range (T : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) := by
  have hiso : Isometry (T : H → H) := AddMonoidHomClass.isometry_of_norm _ hT
  have h := hiso.isClosedEmbedding.isClosed_range
  have hcoe : ((LinearMap.range (T : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H)
      = Set.range (T : H → H) := rfl
  rw [hcoe]
  exact h

/-- **The orthogonal splitting.**  For an isometry `T` and a subspace `V`. -/
theorem orthogonal_map_eq_sup {T : H →L[ℂ] H} (hT : ∀ x, ‖T x‖ = ‖x‖) (V : Submodule ℂ H) :
    (V.map (T : H →ₗ[ℂ] H))ᗮ
      = (LinearMap.range (T : H →ₗ[ℂ] H))ᗮ ⊔ (Vᗮ).map (T : H →ₗ[ℂ] H) := by
  haveI : CompleteSpace (LinearMap.range (T : H →ₗ[ℂ] H)) :=
    (isClosed_coe_range_of_isometry hT).completeSpace_coe
  haveI : (LinearMap.range (T : H →ₗ[ℂ] H)).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ :=
      (LinearMap.range (T : H →ₗ[ℂ] H)).exists_add_mem_mem_orthogonal x
    obtain ⟨u, rfl⟩ := hy
    have huV : u ∈ Vᗮ := by
      intro v hv
      have hxv : (inner ℂ ((T : H →ₗ[ℂ] H) u + z) ((T : H →ₗ[ℂ] H) v) : ℂ) = 0 := by
        have := hx ((T : H →ₗ[ℂ] H) v) (Submodule.mem_map_of_mem hv)
        rw [← inner_conj_symm] at this
        have h2 : (inner ℂ ((T : H →ₗ[ℂ] H) v) ((T : H →ₗ[ℂ] H) u + z) : ℂ) = 0 := by
          exact hx ((T : H →ₗ[ℂ] H) v) (Submodule.mem_map_of_mem hv)
        rw [← inner_conj_symm, h2, map_zero]
      have hzv : (inner ℂ z ((T : H →ₗ[ℂ] H) v) : ℂ) = 0 := by
        have h3 : (inner ℂ ((T : H →ₗ[ℂ] H) v) z : ℂ) = 0 := hz _ ⟨v, rfl⟩
        rw [← inner_conj_symm, h3, map_zero]
      have huv : (inner ℂ ((T : H →ₗ[ℂ] H) u) ((T : H →ₗ[ℂ] H) v) : ℂ) = 0 := by
        rw [inner_add_left, hzv, add_zero] at hxv
        exact hxv
      rw [inner_map_map_of_isometry hT] at huv
      rw [← inner_conj_symm, huv, map_zero]
    have hmem : (T : H →ₗ[ℂ] H) u + z
        ∈ (Vᗮ).map (T : H →ₗ[ℂ] H) ⊔ (LinearMap.range (T : H →ₗ[ℂ] H))ᗮ :=
      Submodule.add_mem_sup (Submodule.mem_map_of_mem huV) hz
    rwa [sup_comm] at hmem
  · refine sup_le (Submodule.orthogonal_le (map_le_range_linear T V)) ?_
    rintro w ⟨u, hu, rfl⟩
    intro y hy
    obtain ⟨v, hv, rfl⟩ := hy
    rw [inner_map_map_of_isometry hT]
    exact hu v hv

end Splitting

section SplittingDim

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finrank_map_orthogonal {T : H →L[ℂ] H} (hT : ∀ x, ‖T x‖ = ‖x‖) (V : Submodule ℂ H)
    [FiniteDimensional ℂ (Vᗮ : Submodule ℂ H)] :
    FiniteDimensional ℂ ((Vᗮ).map (T : H →ₗ[ℂ] H)) ∧
      Module.finrank ℂ ((Vᗮ).map (T : H →ₗ[ℂ] H)) = Module.finrank ℂ (Vᗮ : Submodule ℂ H) := by
  have hinj : Function.Injective (T : H →ₗ[ℂ] H) := by
    intro x y hxy
    have hxy' : T x = T y := hxy
    have h2 : T (x - y) = 0 := by
      rw [map_sub, hxy', sub_self]
    have h3 : ‖x - y‖ = 0 := by rw [← hT (x - y), h2, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  have hequiv := Submodule.equivMapOfInjective (T : H →ₗ[ℂ] H) hinj (Vᗮ)
  haveI : FiniteDimensional ℂ ((Vᗮ).map (T : H →ₗ[ℂ] H)) :=
    Module.Finite.equiv hequiv
  exact ⟨inferInstance, (LinearEquiv.finrank_eq hequiv).symm⟩

theorem finrank_orthogonal_map_add {T : H →L[ℂ] H} (hT : ∀ x, ‖T x‖ = ‖x‖) (V : Submodule ℂ H)
    [FiniteDimensional ℂ ((LinearMap.range (T : H →ₗ[ℂ] H))ᗮ : Submodule ℂ H)]
    [FiniteDimensional ℂ (Vᗮ : Submodule ℂ H)] :
    FiniteDimensional ℂ ((V.map (T : H →ₗ[ℂ] H))ᗮ : Submodule ℂ H) ∧
      Module.finrank ℂ ((V.map (T : H →ₗ[ℂ] H))ᗮ : Submodule ℂ H)
        = Module.finrank ℂ ((LinearMap.range (T : H →ₗ[ℂ] H))ᗮ : Submodule ℂ H)
          + Module.finrank ℂ (Vᗮ : Submodule ℂ H) := by
  obtain ⟨hfinB, hdimB⟩ := finrank_map_orthogonal hT V
  haveI := hfinB
  set A : Submodule ℂ H := (LinearMap.range (T : H →ₗ[ℂ] H))ᗮ with hA
  set Bm : Submodule ℂ H := (Vᗮ).map (T : H →ₗ[ℂ] H) with hB
  have hinf : A ⊓ Bm = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro w ⟨hwA, hwB⟩
    have hwr : w ∈ LinearMap.range (T : H →ₗ[ℂ] H) := map_le_range_linear T (Vᗮ) hwB
    have : (inner ℂ w w : ℂ) = 0 := hwA w hwr
    have hz : w = 0 := by
      have := inner_self_eq_zero (𝕜 := ℂ) (x := w)
      exact this.mp ‹_›
    simpa using hz
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq A Bm
  rw [hinf, finrank_bot, add_zero] at hsup
  rw [orthogonal_map_eq_sup hT V, ← hA, ← hB]
  refine ⟨inferInstance, ?_⟩
  rw [hsup, hdimB]

end SplittingDim

/-! ## The Blaschke induction -/

/-- Finite Blaschke data from a bounded family of zeros. -/
def blaschkeOf {k : ℕ} (a : Fin k → ℂ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hle : ∀ j, ‖a j‖ ≤ c) : FiniteBlaschke :=
  ⟨k, a, c, hc0, hc1, hle⟩

theorem hardyMulBlaschke_isometry (B : FiniteBlaschke) (x : HardyDisk) :
    ‖hardyMul B.toMultiplier x‖ = ‖x‖ := norm_hardyMul_blaschke B x

theorem blaschkeOf_zero_fn {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (a : Fin 0 → ℂ) (hle : ∀ j, ‖a j‖ ≤ c) (z : ℂ) :
    (blaschkeOf a hc0 hc1 hle).fn z = 1 := by
  rw [FiniteBlaschke.fn, blaschkeProd]
  simp [blaschkeOf]

theorem blaschkeOf_succ_fn {k : ℕ} (a : Fin (k + 1) → ℂ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hle : ∀ j, ‖a j‖ ≤ c) (z : ℂ) :
    (blaschkeOf a hc0 hc1 hle).fn z
      = blaschkeFactor (a 0) z
        * (blaschkeOf (fun j : Fin k => a j.succ) hc0 hc1 (fun j => hle j.succ)).fn z := by
  rw [FiniteBlaschke.fn, FiniteBlaschke.fn, blaschkeProd, blaschkeProd]
  show (∏ j : Fin (k + 1), blaschkeFactor (a j) z)
    = blaschkeFactor (a 0) z * ∏ j : Fin k, blaschkeFactor (a j.succ) z
  exact Fin.prod_univ_succ (fun j => blaschkeFactor (a j) z)

theorem finiteDimensional_orthogonal_range_singleBlaschke {a : ℂ} (ha : ‖a‖ < 1) :
    FiniteDimensional ℂ ((LinearMap.range ((hardyMul (singleBlaschke ha).toMultiplier :
      HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))ᗮ : Submodule ℂ HardyDisk) := by
  rw [range_hardyMul_singleBlaschke ha]
  haveI : FiniteDimensional ℂ (ℂ ∙ hardyKernel ha) :=
    FiniteDimensional.span_singleton ℂ (hardyKernel ha)
  rw [Submodule.orthogonal_orthogonal]
  infer_instance

theorem hardyMul_blaschkeOf_succ {k : ℕ} (a : Fin (k + 1) → ℂ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c < 1) (hle : ∀ j, ‖a j‖ ≤ c) (h0 : ‖a 0‖ < 1) (x : HardyDisk) :
    hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier x
      = hardyMul (singleBlaschke h0).toMultiplier
          (hardyMul (blaschkeOf (fun j : Fin k => a j.succ) hc0 hc1
            (fun j => hle j.succ)).toMultiplier x) := by
  rw [hardyMul_mul]
  refine (hardyMul_congr (fun z _ => ?_) x).symm
  show (singleBlaschke h0).fn z
      * (blaschkeOf (fun j : Fin k => a j.succ) hc0 hc1 (fun j => hle j.succ)).fn z
    = (blaschkeOf a hc0 hc1 hle).fn z
  rw [singleBlaschke_fn, blaschkeOf_succ_fn a hc0 hc1 hle z]

theorem range_hardyMul_blaschkeOf_succ {k : ℕ} (a : Fin (k + 1) → ℂ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c < 1) (hle : ∀ j, ‖a j‖ ≤ c) (h0 : ‖a 0‖ < 1) :
    LinearMap.range ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
        HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk)
      = (LinearMap.range ((hardyMul (blaschkeOf (fun j : Fin k => a j.succ) hc0 hc1
            (fun j => hle j.succ)).toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk)).map
        ((hardyMul (singleBlaschke h0).toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, (hardyMul_blaschkeOf_succ a hc0 hc1 hle h0 x).symm⟩
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, hardyMul_blaschkeOf_succ a hc0 hc1 hle h0 x⟩

/-- **Equation (7).**  The model space of a finite Blaschke product has dimension equal to its
degree, multiplicities included. -/
theorem finrank_orthogonal_range_blaschkeOf : ∀ (k : ℕ) (a : Fin k → ℂ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c < 1) (hle : ∀ j, ‖a j‖ ≤ c),
    FiniteDimensional ℂ ((LinearMap.range ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
        HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))ᗮ : Submodule ℂ HardyDisk) ∧
      Module.finrank ℂ ((LinearMap.range ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
        HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))ᗮ : Submodule ℂ HardyDisk) = k
  | 0, a, c, hc0, hc1, hle => by
      have hsurj : ∀ x : HardyDisk, hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier x = x := by
        intro x
        have hcong : hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier x
            = hardyMul DiskMultiplier.one x := by
          refine hardyMul_congr (fun z _ => ?_) x
          show (blaschkeOf a hc0 hc1 hle).fn z = 1
          exact blaschkeOf_zero_fn hc0 hc1 a hle z
        rw [hcong, hardyMul_one]
      have hrange : LinearMap.range ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
          HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) = ⊤ := by
        refine LinearMap.range_eq_top.mpr fun y => ⟨y, ?_⟩
        exact hsurj y
      rw [hrange, Submodule.top_orthogonal_eq_bot]
      exact ⟨inferInstance, finrank_bot ℂ HardyDisk⟩
  | (k + 1), a, c, hc0, hc1, hle => by
      have h0 : ‖a 0‖ < 1 := lt_of_le_of_lt (hle 0) hc1
      obtain ⟨hfinIH, hdimIH⟩ :=
        finrank_orthogonal_range_blaschkeOf k (fun j : Fin k => a j.succ) hc0 hc1
          (fun j => hle j.succ)
      haveI := hfinIH
      haveI := finiteDimensional_orthogonal_range_singleBlaschke h0
      have hT : ∀ x : HardyDisk, ‖hardyMul (singleBlaschke h0).toMultiplier x‖ = ‖x‖ :=
        fun x => norm_hardyMul_blaschke (singleBlaschke h0) x
      rw [range_hardyMul_blaschkeOf_succ a hc0 hc1 hle h0]
      obtain ⟨hfin, hdim⟩ := finrank_orthogonal_map_add hT
        (LinearMap.range ((hardyMul (blaschkeOf (fun j : Fin k => a j.succ) hc0 hc1
          (fun j => hle j.succ)).toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk))
      refine ⟨hfin, ?_⟩
      rw [hdim, finrank_orthogonal_range_singleBlaschke h0, hdimIH]
      omega

end GaloisForLFunctions.HTGeometry
