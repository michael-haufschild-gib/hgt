import Mathlib

/-!
# The withheld-observer factorization criterion

A withheld infinitesimal observer `B` is determined by a family of calibrated observers `A`
exactly when it kills their common vertical kernel.  The four equivalent forms are

* `B` is constant on the fibres of `A`;
* `ker A ≤ ker B`;
* there is a unique factor `B̄` on `range A` with `B = B̄ ∘ A`;
* on duals, `range Bᵀ ≤ range Aᵀ`.

When they fail there is an exact counter-intervention: a vertical direction `h` with `A h = 0` and
`B h ≠ 0`.

The factor is canonical, hence equivariant for any symmetry preserving `A` and `B`.

Cofinally the criterion is quantitative: a bounded factor exists exactly when a uniform response
inequality `‖B v‖ ≤ C ‖A v‖` holds.  Finite factorization and global injectivity do not suffice —
if some sequence has `‖B eₙ‖ = 1` while `‖A eₙ‖ → 0`, no uniform constant exists even though the
algebraic factor is defined.
-/

namespace HTGeometry.ConstraintFrameRelativity

open LinearMap

variable {K V W Z : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [AddCommGroup Z] [Module K Z]

/-! ## The exact factorization criterion -/

/-- **Constancy on fibres is kernel containment.** -/
theorem constant_on_fibres_iff (A : V →ₗ[K] W) (B : V →ₗ[K] Z) :
    (∀ v v' : V, A v = A v' → B v = B v') ↔ ker A ≤ ker B := by
  constructor
  · intro h x hx
    have hA : A x = A 0 := by
      rw [mem_ker.mp hx, map_zero]
    have := h x 0 hA
    rw [map_zero] at this
    exact mem_ker.mpr this
  · intro h v v' hv
    have hsub : v - v' ∈ ker A := by
      rw [mem_ker, map_sub, hv, sub_self]
    have := h hsub
    rw [mem_ker, map_sub, sub_eq_zero] at this
    exact this

/-- The canonical factor of `B` through the fibres of `A`, defined on the quotient. -/
noncomputable def factorQuot (A : V →ₗ[K] W) (B : V →ₗ[K] Z) (h : ker A ≤ ker B) :
    (V ⧸ ker A) →ₗ[K] Z :=
  (ker A).liftQ B h

@[simp] theorem factorQuot_mk (A : V →ₗ[K] W) (B : V →ₗ[K] Z) (h : ker A ≤ ker B) (v : V) :
    factorQuot A B h (Submodule.Quotient.mk v) = B v :=
  Submodule.liftQ_apply (ker A) B v

/-- The canonical factor of `B` on the image of `A`. -/
noncomputable def factorRange (A : V →ₗ[K] W) (B : V →ₗ[K] Z) (h : ker A ≤ ker B) :
    (range A) →ₗ[K] Z :=
  (factorQuot A B h).comp (A.quotKerEquivRange.symm : (range A) →ₗ[K] (V ⧸ ker A))

/-- **The factorization `B = B̄ ∘ A`.** -/
@[simp] theorem factorRange_apply (A : V →ₗ[K] W) (B : V →ₗ[K] Z) (h : ker A ≤ ker B) (v : V) :
    factorRange A B h ⟨A v, mem_range.mpr ⟨v, rfl⟩⟩ = B v := by
  have hsymm : A.quotKerEquivRange.symm ⟨A v, mem_range.mpr ⟨v, rfl⟩⟩
      = Submodule.Quotient.mk v := by
    apply A.quotKerEquivRange.injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [factorRange, LinearMap.comp_apply]
  change factorQuot A B h (A.quotKerEquivRange.symm ⟨A v, _⟩) = B v
  rw [hsymm, factorQuot_mk]

/-- **Uniqueness of the factor.** -/
theorem factorRange_unique (A : V →ₗ[K] W) (B : V →ₗ[K] Z) (h : ker A ≤ ker B)
    (G : (range A) →ₗ[K] Z) (hG : ∀ v : V, G ⟨A v, mem_range.mpr ⟨v, rfl⟩⟩ = B v) :
    G = factorRange A B h := by
  ext w
  obtain ⟨v, hv⟩ := mem_range.mp w.2
  have hw : w = ⟨A v, mem_range.mpr ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
  rw [hw, hG v, factorRange_apply]

/-- **The exact counter-intervention.**  When the criterion fails there is a vertical direction
invisible to the calibrated observers on which the withheld response is nonzero. -/
theorem exists_vertical_mode (A : V →ₗ[K] W) (B : V →ₗ[K] Z) (h : ¬ ker A ≤ ker B) :
    ∃ x : V, A x = 0 ∧ B x ≠ 0 := by
  rw [SetLike.not_le_iff_exists] at h
  obtain ⟨x, hx, hx'⟩ := h
  exact ⟨x, mem_ker.mp hx, fun hb => hx' (mem_ker.mpr hb)⟩

/-! ## Equivariance of the canonical factor -/

/-- **Presentation covariance.**  Any symmetry preserving `A` and `B` is preserved by the
canonical factor. -/
theorem factorRange_equivariant (A : V →ₗ[K] W) (B : V →ₗ[K] Z) (h : ker A ≤ ker B)
    (g : V ≃ₗ[K] V) (gZ : Z ≃ₗ[K] Z) (hB : ∀ v, B (g v) = gZ (B v)) (v : V) :
    factorRange A B h ⟨A (g v), mem_range.mpr ⟨g v, rfl⟩⟩
      = gZ (factorRange A B h ⟨A v, mem_range.mpr ⟨v, rfl⟩⟩) := by
  rw [factorRange_apply, factorRange_apply, hB]

/-! ## The dual form of the criterion -/

/-- **Dual form.**  In finite dimension the criterion reads `range Bᵀ ≤ range Aᵀ`. -/
theorem ker_le_ker_iff_range_dualMap_le [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K Z] (A : V →ₗ[K] W) (B : V →ₗ[K] Z) :
    ker A ≤ ker B ↔ range B.dualMap ≤ range A.dualMap := by
  rw [range_dualMap_eq_dualAnnihilator_ker, range_dualMap_eq_dualAnnihilator_ker]
  exact Subspace.dualAnnihilator_le_dualAnnihilator_iff.symm

/-! ## The quantitative and cofinal criterion -/

section Quantitative

variable {V' Z' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
variable [NormedAddCommGroup Z'] [NormedSpace ℝ Z']

/-- **A uniform response bound forces kernel containment and a bounded factor on the image.** -/
theorem ker_le_ker_of_response {A : V' →ₗ[ℝ] Z'} {B : V' →ₗ[ℝ] Z'} {C : ℝ}
    (hC : ∀ v, ‖B v‖ ≤ C * ‖A v‖) : ker A ≤ ker B := by
  intro x hx
  have h := hC x
  rw [mem_ker.mp hx, norm_zero, mul_zero] at h
  exact mem_ker.mpr (norm_le_zero_iff.mp h)

/-- **The factor is bounded by the response constant.** -/
theorem norm_factorRange_le {A : V' →ₗ[ℝ] Z'} {B : V' →ₗ[ℝ] Z'} {C : ℝ}
    (hC : ∀ v, ‖B v‖ ≤ C * ‖A v‖) (w : range A) :
    ‖factorRange A B (ker_le_ker_of_response hC) w‖ ≤ C * ‖(w : Z')‖ := by
  obtain ⟨v, hv⟩ := mem_range.mp w.2
  have hw : w = ⟨A v, mem_range.mpr ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
  rw [hw, factorRange_apply]
  have := hC v
  simpa using this

/-- **A bounded factor gives the response bound.** -/
theorem response_of_factor {A : V' →ₗ[ℝ] Z'} {B : V' →ₗ[ℝ] Z'} {C : ℝ}
    (G : (range A) →ₗ[ℝ] Z') (hG : ∀ v : V', G ⟨A v, mem_range.mpr ⟨v, rfl⟩⟩ = B v)
    (hGb : ∀ w : range A, ‖G w‖ ≤ C * ‖(w : Z')‖) (v : V') :
    ‖B v‖ ≤ C * ‖A v‖ := by
  rw [← hG v]
  simpa using hGb ⟨A v, mem_range.mpr ⟨v, rfl⟩⟩

/-- **Cofinal failure.**  A sequence with unit withheld response and vanishing calibrated response
rules out every uniform constant, even when the algebraic factor exists. -/
theorem no_uniform_response {A : V' →ₗ[ℝ] Z'} {B : V' →ₗ[ℝ] Z'} (e : ℕ → V')
    (he : ∀ n, ‖B (e n)‖ = 1)
    (hA : Filter.Tendsto (fun n => ‖A (e n)‖) Filter.atTop (nhds 0)) :
    ¬ ∃ C : ℝ, ∀ v, ‖B v‖ ≤ C * ‖A v‖ := by
  rintro ⟨C, hC⟩
  have hCpos : 0 < C := by
    have h0 := hC (e 0)
    rw [he 0] at h0
    rcases le_or_gt C 0 with hle | hlt
    · have hAn : (0 : ℝ) ≤ ‖A (e 0)‖ := norm_nonneg _
      nlinarith
    · exact hlt
  have hlim : Filter.Tendsto (fun n => C * ‖A (e n)‖) Filter.atTop (nhds 0) := by
    simpa using hA.const_mul C
  have hev := hlim.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨n, hn⟩ := hev.exists
  have := hC (e n)
  rw [he n] at this
  linarith

end Quantitative

end HTGeometry.ConstraintFrameRelativity
