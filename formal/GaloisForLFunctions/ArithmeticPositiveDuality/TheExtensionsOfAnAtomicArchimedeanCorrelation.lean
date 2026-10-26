import GaloisForLFunctions.ArithmeticPositiveDuality.TheSuccessorOscillationIsBoundedByTheContinuousDilationMass

/-!
# The extensions of an atomic archimedean correlation

Let `φ` be positive definite on `Aff(ℚ)` with dilation part `φ(x ↦ ux) = ∫ u^{ix} dν(x)` for
`u > 0`, `ν` a finite purely atomic measure on `ℝ` with atoms `A`.

**Theorem** (`hasSum_affine_of_atomic`). There are constants `0 ≤ α_x ≤ ν{x}`, `x ∈ A`, with
`φ(x ↦ ux + b) = Σ_{x ∈ A} α_x u^{ix}` for every `u > 0` and `b ≠ 0`
(and `φ(x ↦ ux) = Σ_{x ∈ A} ν{x} u^{ix}`). Every such family occurs
(`isPosDefOnGroup_archExtension` and its limits).

So the positive-definite extensions of an atomic archimedean correlation from the dilations to
`Aff(ℚ)` are parametrized by the box `Π_{x ∈ A} [0, ν{x}]`: one free parameter per atom, and
nothing else. For Weil's correlation under RH the atoms are the critical ordinates.

Mechanism. In the GNS space, `α_x = ⟨e_x, π(x ↦ x + 1)e_x⟩` for the atom vector `e_x`; it is
real, at most `‖e_x‖² = ν{x}`, and nonnegative because the translates of `e_x` form a blind family
(`‖Σ_{j<N} π_j e_x‖² = Nν{x} + N(N − 1)α_x ≥ 0`). For a finite set `F` of atoms,
`φ(x ↦ ux + b) = Σ_{x ∈ F} α_x u^{ix} + ⟨ζ_F, π(x ↦ ux + b)ζ_F⟩` and `‖ζ_F‖² = ν(ℝ ∖ F)`, which is
small once `F` exhausts most of the atomic mass.
-/

open Complex MeasureTheory Filter Topology Finset
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

section Blind

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {π : AffineGroupQ →* (E ≃ₗᵢ[ℂ] E)}

/-- The off-diagonal constant of a blind family is nonnegative. -/
theorem IsBlindFamily.nonneg {t : ℚ → E} {s α : ℝ} (ht : IsBlindFamily t s α) : 0 ≤ α := by
  have hs : 0 ≤ s := by
    have h := ht 0 0
    rw [if_pos rfl, inner_self_complex] at h
    exact (Complex.ofReal_injective h) ▸ sq_nonneg _
  by_contra h
  rw [not_le] at h
  obtain ⟨N, hN⟩ := exists_nat_gt ((s - α) / (-α))
  have h1 := ht.norm_sq_sum (x := fun n : ℕ => (n : ℚ)) Nat.cast_injective (range N) (fun _ => 1)
  simp only [one_smul, sum_const, card_range, nsmul_eq_mul, mul_one, norm_one, one_pow,
    Complex.norm_natCast] at h1
  have h2 : 0 ≤ α * (N : ℝ) ^ 2 + (s - α) * N := h1 ▸ sq_nonneg _
  have h3 := (div_lt_iff₀ (by linarith : (0 : ℝ) < -α)).mp hN
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (by linarith) (by linarith)) hN
  nlinarith

/-- The blind constant of an eigenvector, `⟨v, π(x ↦ x + b)v⟩ = Re⟨v, π(x ↦ x + 1)v⟩`, `b ≠ 0`. -/
theorem IsArchEigen.inner_translation_eq_re {γ : ℝ} {v : E} (hv : IsArchEigen π γ v) {b : ℚ}
    (hb : b ≠ 0) :
    ⟪v, π (translation b) v⟫_ℂ = ((⟪v, π (translation 1) v⟫_ℂ).re : ℂ) := by
  obtain ⟨α, hα⟩ := hv.inner_translation_eq
  rw [hα b hb, hα 1 one_ne_zero, Complex.ofReal_re]

theorem IsArchEigen.re_inner_translation_nonneg {γ : ℝ} {v : E} (hv : IsArchEigen π γ v) :
    0 ≤ (⟪v, π (translation 1) v⟫_ℂ).re := by
  obtain ⟨α, -, ht⟩ := hv.isBlindFamily
  have h := ht 0 1
  rw [if_neg zero_ne_one, rep_translation_zero] at h
  rw [h, Complex.ofReal_re]
  exact ht.nonneg

theorem IsArchEigen.re_inner_translation_le {γ : ℝ} {v : E} (hv : IsArchEigen π γ v) :
    (⟪v, π (translation 1) v⟫_ℂ).re ≤ ‖v‖ ^ 2 := by
  refine (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
  rw [LinearIsometryEquiv.norm_map, sq]

end Blind

/-! ### Finite sets of atoms -/

/-- An enumeration of a finite set of reals. -/
def finsetEnum (F : Finset ℝ) : Fin F.card → ℝ := fun k => ((F.equivFin.symm k : F) : ℝ)

theorem finsetEnum_injective (F : Finset ℝ) : Function.Injective (finsetEnum F) :=
  fun _ _ h => F.equivFin.symm.injective (Subtype.ext h)

theorem sum_finsetEnum {M : Type*} [AddCommMonoid M] (F : Finset ℝ) (g : ℝ → M) :
    ∑ k, g (finsetEnum F k) = ∑ x ∈ F, g x := by
  rw [finsetEnum, F.equivFin.symm.sum_comp (fun x : F => g (x : ℝ)), F.sum_coe_sort g]

section Ext

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {ν : Measure ℝ} [IsFiniteMeasure ν]

/-- The blind constant `α_x = Re⟨e_x, π(x ↦ x + 1)e_x⟩` of the atom at `x`. -/
def atomAlpha (x : ℝ) : ℝ :=
  (⟪atomVec hφ x, affRep hφ (translation 1) (atomVec hφ x)⟫_ℂ).re

variable (hν : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∫ x, archChar x u ∂ν)
include hφ hν

theorem atomAlpha_nonneg (x : ℝ) : 0 ≤ atomAlpha hφ x :=
  (isArchEigen_atomVec hφ hν x).re_inner_translation_nonneg

theorem atomAlpha_le (x : ℝ) : atomAlpha hφ x ≤ ν.real {x} :=
  (norm_sq_atomVec hφ hν x) ▸ (isArchEigen_atomVec hφ hν x).re_inner_translation_le

theorem inner_atomVec_translation (x : ℝ) {b : ℚ} (hb : b ≠ 0) :
    ⟪atomVec hφ x, affRep hφ (translation b) (atomVec hφ x)⟫_ℂ = atomAlpha hφ x :=
  (isArchEigen_atomVec hφ hν x).inner_translation_eq_re hb

/-- **The affine values over a finite set of atoms.** For `u > 0` and `b ≠ 0`,
`φ(x ↦ ux + b) = Σ_{x ∈ F} α_x u^{ix} + ⟨ζ_F, π(x ↦ ux + b)ζ_F⟩`. -/
theorem affine_eq_atoms_add_rem (F : Finset ℝ) {u : ℚˣ} (hu : 0 < (u : ℚ)) {b : ℚ} (hb : b ≠ 0) :
    φ (translation b * dilation u) = ∑ x ∈ F, (atomAlpha hφ x : ℂ) * archChar x u +
      ⟪remVec hφ (finsetEnum F), affRep hφ (translation b * dilation u)
        (remVec hφ (finsetEnum F))⟫_ℂ := by
  set γ := finsetEnum F
  have hγ := finsetEnum_injective F
  set S := ∑ k, atomVec hφ (γ k)
  set ζ := remVec hφ γ
  set π := affRep hφ
  have hξ : affVec hφ = S + ζ := by simp only [ζ, remVec, S, add_sub_cancel]
  have he : ∀ k, π (dilation u) (atomVec hφ (γ k)) = archChar (γ k) u • atomVec hφ (γ k) :=
    fun k => isArchEigen_atomVec hφ hν (γ k) u hu
  have hdS : π (dilation u) S = ∑ k, archChar (γ k) u • atomVec hφ (γ k) := by
    rw [map_sum]; exact sum_congr rfl fun k _ => he k
  have hT1 : ⟪S, π (translation b) (π (dilation u) S)⟫_ℂ =
      ∑ k, (atomAlpha hφ (γ k) : ℂ) * archChar (γ k) u := by
    rw [hdS, map_sum, sum_inner]
    refine sum_congr rfl fun j _ => ?_
    rw [inner_sum, sum_eq_single j (fun k _ hkj => by
        rw [LinearIsometryEquiv.map_smul, inner_smul_right,
          (isArchEigen_atomVec hφ hν (γ k)).inner_translation_eq_zero
            (isArchEigen_atomVec hφ hν (γ j)) (hγ.ne hkj) b, mul_zero])
      (fun h => absurd (mem_univ j) h), LinearIsometryEquiv.map_smul, inner_smul_right,
      inner_atomVec_translation hφ hν _ hb, mul_comm]
  have hT3 : ⟪ζ, π (translation b) (π (dilation u) S)⟫_ℂ = 0 := by
    rw [hdS, map_sum, inner_sum]
    refine sum_eq_zero fun k _ => ?_
    rw [LinearIsometryEquiv.map_smul, inner_smul_right,
      inner_remVec_translation_atomVec hφ hν hγ k b, mul_zero]
  have hT2 : ⟪S, π (translation b) (π (dilation u) ζ)⟫_ℂ = 0 := by
    rw [sum_inner]
    refine sum_eq_zero fun j _ => ?_
    have hc := rep_translation_dilation π u⁻¹ (-b) (atomVec hφ (γ j))
    rw [isArchEigen_atomVec hφ hν (γ j) u⁻¹ (by simpa using hu), LinearIsometryEquiv.map_smul] at hc
    rw [show b = -(-b) by ring, inner_rep_translation_neg, inner_rep_dilation, ← hc, inner_smul_left,
      ← inner_conj_symm, inner_remVec_translation_atomVec hφ hν hγ j, map_zero, mul_zero]
  have hφg : φ (translation b * dilation u) =
      ⟪affVec hφ, π (translation b * dilation u) (affVec hφ)⟫_ℂ :=
    (inner_gnsCyclic_gnsRep (⟨φ, hφ⟩ : PosDefFn AffineGroupQ) _).symm
  rw [hφg, rep_mul_apply, hξ, map_add, map_add, inner_add_left, inner_add_right, inner_add_right,
    hT1, hT2, hT3, ← rep_mul_apply, ← sum_finsetEnum F (fun x => (atomAlpha hφ x : ℂ) * archChar x u)]
  ring

/-- **The extensions of an atomic archimedean correlation.** If `ν` is purely atomic, then for
`u > 0` and `b ≠ 0`, `φ(x ↦ ux + b) = Σ_{x ∈ A} α_x u^{ix}` over the atoms `A` of `ν`, with
`0 ≤ α_x ≤ ν{x}`. -/
theorem hasSum_affine_of_atomic (hat : ν {x | ν {x} = 0} = 0) {u : ℚˣ} (hu : 0 < (u : ℚ))
    {b : ℚ} (hb : b ≠ 0) :
    HasSum (fun x : {x : ℝ // 0 < ν {x}} => (atomAlpha hφ x : ℂ) * archChar x u)
      (φ (translation b * dilation u)) := by
  set A : Set ℝ := {x | 0 < ν {x}}
  have hA : A.Countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (As := fun x : ℝ => ({x} : Set ℝ)) (fun x => measurableSet_singleton x)
    (fun x y hxy => Set.disjoint_singleton.mpr hxy)
  have hcompl : ν.real Aᶜ = 0 := by
    have : Aᶜ = {x : ℝ | ν {x} = 0} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, A, not_lt, nonpos_iff_eq_zero]
    rw [this, measureReal_def, hat, ENNReal.toReal_zero]
  -- the remainder over a finite set of atoms has norm `ν(ℝ ∖ s)`
  have hrem : ∀ s : Finset A, ‖φ (translation b * dilation u) -
      ∑ x ∈ s, (atomAlpha hφ x : ℂ) * archChar x u‖ ≤ ν.real A - ν.real (s.map
        (Function.Embedding.subtype _) : Set ℝ) := by
    intro s
    set F := s.map (Function.Embedding.subtype _)
    have h := affine_eq_atoms_add_rem hφ hν F hu hb
    rw [Finset.sum_map] at h
    rw [h, add_sub_cancel_left]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map, ← sq, norm_sq_remVec hφ hν (finsetEnum_injective F),
      sum_finsetEnum F (fun x => ν.real {x}), sum_measureReal_singleton,
      ← measureReal_add_measureReal_compl hA.measurableSet, hcompl, add_zero]
  -- finite sets of atoms carrying almost all the mass
  obtain ⟨e, he⟩ := Set.countable_iff_exists_injective.mp hA
  set G : ℕ → Finset A := fun n => ((Set.finite_lt_nat n).preimage he.injOn).toFinset
  have hGmem : ∀ n (a : A), a ∈ G n ↔ e a < n := fun n a => by
    simp only [G, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
  have hGmono : Monotone fun n => ((G n).map (Function.Embedding.subtype _) : Set ℝ) := by
    intro m n hmn x hx
    simp only [coe_map, Function.Embedding.coe_subtype, Set.mem_image, mem_coe] at hx ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, (hGmem n a).mpr (lt_of_lt_of_le ((hGmem m a).mp ha) hmn), rfl⟩
  have hGunion : ⋃ n, ((G n).map (Function.Embedding.subtype _) : Set ℝ) = A := by
    ext x
    simp only [Set.mem_iUnion, coe_map, Function.Embedding.coe_subtype, Set.mem_image, mem_coe]
    constructor
    · rintro ⟨n, a, -, rfl⟩; exact a.2
    · intro hx; exact ⟨e ⟨x, hx⟩ + 1, ⟨x, hx⟩, (hGmem _ _).mpr (Nat.lt_succ_self _), rfl⟩
  have hGlim : Tendsto (fun n => ν.real ((G n).map (Function.Embedding.subtype _) : Set ℝ)) atTop
      (𝓝 (ν.real A)) := by
    have h := tendsto_measure_iUnion_atTop (μ := ν) hGmono
    rw [hGunion] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top ν A)).comp h
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hGlim ε hε
  refine ⟨G N, fun s hs => ?_⟩
  have h1 := hrem s
  have h2 : ν.real ((G N).map (Function.Embedding.subtype _) : Set ℝ) ≤
      ν.real (s.map (Function.Embedding.subtype _) : Set ℝ) :=
    measureReal_mono (Finset.coe_subset.mpr (Finset.map_subset_map.mpr hs))
  have h3 := hN N le_rfl
  rw [Real.dist_eq, abs_lt] at h3
  rw [dist_eq_norm, norm_sub_rev]
  linarith

end Ext

end GaloisForLFunctions.ArithmeticPositiveDuality
