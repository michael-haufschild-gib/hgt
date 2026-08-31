import GaloisForLFunctions.HTGeometry.LpFamilyIsometry

/-!
# Gauge transport on dependent `Lp` sums

Two exact transports needed for global constitutive sewing are isolated here.  Reindexing by an
equivalence preserves the dependent `Lp` norm, and a fibrewise family of linear isometric
equivalences assembles to a linear isometric equivalence of dependent `Lp` sums.
-/

open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α β : Type*} {E : β → Type*} {p : ℝ≥0∞}
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace 𝕜 (E b)]

theorem memℓp_dependent_comp_equiv (hp : 0 < p.toReal) (e : α ≃ β)
    {f : ∀ b, E b} (hf : Memℓp f p) :
    Memℓp (fun a => f (e a)) p := by
  rw [memℓp_gen_iff hp] at hf ⊢
  exact (e.summable_iff (f := fun b => ‖f b‖ ^ p.toReal)).mpr hf

def lpDependentDomCongrFun [Fact (1 ≤ p)] (hp : 0 < p.toReal) (e : α ≃ β)
    (f : lp E p) : lp (fun a => E (e a)) p :=
  ⟨fun a => f (e a), memℓp_dependent_comp_equiv hp e f.2⟩

@[simp] theorem lpDependentDomCongrFun_apply [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (e : α ≃ β) (f : lp E p) (a : α) :
    (lpDependentDomCongrFun hp e f : ∀ a, E (e a)) a = f (e a) := rfl

theorem norm_lpDependentDomCongrFun [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (e : α ≃ β) (f : lp E p) :
    ‖lpDependentDomCongrFun hp e f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  congr 1
  exact (e.tsum_eq fun b => ‖f b‖ ^ p.toReal)

/-- Reindexing by a base equivalence is an exact linear isometry of dependent `Lp` sums. -/
def lpDependentDomCongrIsometry [Fact (1 ≤ p)] (hp : 0 < p.toReal) (e : α ≃ β) :
    lp E p →ₗᵢ[𝕜] lp (fun a => E (e a)) p where
  toFun := lpDependentDomCongrFun hp e
  map_add' f g := by ext a; simp
  map_smul' c f := by ext a; simp
  norm_map' f := norm_lpDependentDomCongrFun hp e f

@[simp] theorem lpDependentDomCongrIsometry_apply [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (e : α ≃ β) (f : lp E p) (a : α) :
    (lpDependentDomCongrIsometry (𝕜 := 𝕜) hp e f : ∀ a, E (e a)) a = f (e a) := rfl

variable {ι : Type*} {F G : ι → Type*}
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedAddCommGroup (G i)]
  [∀ i, NormedSpace 𝕜 (F i)] [∀ i, NormedSpace 𝕜 (G i)]

/-- Fibrewise unitary gauge changes assemble without loss on a dependent `Lp` sum. -/
def lpFamilyIsometryEquiv [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : ∀ i, F i ≃ₗᵢ[𝕜] G i) : lp F p ≃ₗᵢ[𝕜] lp G p where
  __ := lpFamilyIsometry hp (fun i => (T i).toLinearIsometry)
  invFun := lpFamilyIsometry hp (fun i => (T i).symm.toLinearIsometry)
  left_inv f := by
    ext i
    exact (T i).symm_apply_apply (f i)
  right_inv g := by
    ext i
    exact (T i).apply_symm_apply (g i)

@[simp] theorem lpFamilyIsometryEquiv_apply [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : ∀ i, F i ≃ₗᵢ[𝕜] G i) (f : lp F p) (i : ι) :
    (lpFamilyIsometryEquiv hp T f : ∀ i, G i) i = T i (f i) := rfl

end

end GaloisForLFunctions.HTGeometry
