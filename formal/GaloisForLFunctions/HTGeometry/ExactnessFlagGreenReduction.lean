import GaloisForLFunctions.HTGeometry.ExactnessFlagProvenanceTopology
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Green reduction of an exactness flag

Call an exactness flag *Green self-dual* for a bilinear form when its cycle space is the orthogonal
of its boundary space.  Then the boundary space is isotropic, the form descends to the spectral
quotient, and on a finite-dimensional space with a nondegenerate reflexive form the descended form
is nondegenerate.

Positivity cannot be imposed before this reduction.  If the form is anisotropic — in particular if
it is a positive-definite inner product — then the only Green self-dual flag is the trivial one
`(0, ⊤)`, so no nonzero boundary space survives.  The hyperbolic plane shows both regimes: its
isotropic line carries the off-horizon self-dual flag `(L, L)`, which no anisotropic form can
realize.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ExFlag

open LinearMap (BilinForm)

/-! ## Descent of a bilinear form through a radical -/

section QuotBilin

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A bilinear form both of whose radicals contain `N` descends to the quotient by `N`. -/
noncomputable def quotBilin (f : BilinForm K M) (N : Submodule K M)
    (hleft : ∀ n ∈ N, ∀ m, f n m = 0) (hright : ∀ m : M, ∀ n ∈ N, f m n = 0) :
    BilinForm K (M ⧸ N) :=
  N.liftQ
    ((N.dualQuotEquivDualAnnihilator.symm : N.dualAnnihilator →ₗ[K] Module.Dual K (M ⧸ N)).comp
      (LinearMap.codRestrict N.dualAnnihilator f
        (fun m => (Submodule.mem_dualAnnihilator _).2 (hright m))))
    (by
      intro n hn
      simp only [LinearMap.mem_ker, LinearMap.comp_apply]
      have hfn : LinearMap.codRestrict N.dualAnnihilator f
          (fun m => (Submodule.mem_dualAnnihilator _).2 (hright m)) n = 0 := by
        ext m
        exact hleft n hn m
      rw [hfn, map_zero])

@[simp] theorem quotBilin_apply (f : BilinForm K M) (N : Submodule K M)
    (hleft : ∀ n ∈ N, ∀ m, f n m = 0) (hright : ∀ m : M, ∀ n ∈ N, f m n = 0) (x y : M) :
    quotBilin f N hleft hright (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = f x y := by
  rw [quotBilin, Submodule.liftQ_apply]
  exact Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk N _ y

end QuotBilin

/-! ## Green self-dual flags -/

section Green

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A flag is *Green self-dual* for `g` when its cycle space is the `g`-orthogonal of its boundary
space. -/
def IsGreenSelfDual (g : BilinForm K V) (p : ExFlag K V) : Prop :=
  p.cycle = g.orthogonal p.boundary

/-- **The boundary space of a Green self-dual flag is isotropic.** -/
theorem IsGreenSelfDual.isotropic {g : BilinForm K V} {p : ExFlag K V}
    (h : IsGreenSelfDual g p) {b b' : V} (hb : b ∈ p.boundary) (hb' : b' ∈ p.boundary) :
    g b b' = 0 := by
  have hb'Z : b' ∈ p.cycle := p.boundary_le_cycle hb'
  rw [h, LinearMap.BilinForm.mem_orthogonal_iff] at hb'Z
  exact hb'Z b hb

/-- On a Green self-dual flag the form kills the boundary space from the left. -/
theorem IsGreenSelfDual.left_radical {g : BilinForm K V} {p : ExFlag K V}
    (h : IsGreenSelfDual g p) {b : V} (hb : b ∈ p.boundary) {z : V} (hz : z ∈ p.cycle) :
    g b z = 0 := by
  rw [h, LinearMap.BilinForm.mem_orthogonal_iff] at hz
  exact hz b hb

/-- On a Green self-dual reflexive flag the form kills the boundary space from the right. -/
theorem IsGreenSelfDual.right_radical {g : BilinForm K V} (hrefl : g.IsRefl)
    {p : ExFlag K V} (h : IsGreenSelfDual g p) {z : V} (hz : z ∈ p.cycle) {b : V}
    (hb : b ∈ p.boundary) : g z b = 0 :=
  hrefl b z (h.left_radical hb hz)

/-- **The Green form descends to the spectral quotient.** -/
noncomputable def greenQuotForm (g : BilinForm K V) (hrefl : g.IsRefl) (p : ExFlag K V)
    (h : IsGreenSelfDual g p) : BilinForm K p.homology :=
  quotBilin (g.restrict p.cycle) (Submodule.comap p.cycle.subtype p.boundary)
    (fun _ hn m => h.left_radical hn m.2)
    (fun m _ hn => h.right_radical hrefl m.2 hn)

@[simp] theorem greenQuotForm_mk (g : BilinForm K V) (hrefl : g.IsRefl) (p : ExFlag K V)
    (h : IsGreenSelfDual g p) (v w : p.cycle) :
    greenQuotForm g hrefl p h (Submodule.Quotient.mk v) (Submodule.Quotient.mk w) =
      g (v : V) (w : V) := by
  rw [greenQuotForm, quotBilin_apply]
  rfl

theorem greenQuotForm_homologyClass (g : BilinForm K V) (hrefl : g.IsRefl) (p : ExFlag K V)
    (h : IsGreenSelfDual g p) {v w : V} (hv : v ∈ p.cycle) (hw : w ∈ p.cycle) :
    greenQuotForm g hrefl p h (p.homologyClass hv) (p.homologyClass hw) = g v w :=
  greenQuotForm_mk g hrefl p h ⟨v, hv⟩ ⟨w, hw⟩

/-- **The descended Green form is nondegenerate.**  Its radical is the intersection of the cycle
space with its own orthogonal, which is exactly the boundary space. -/
theorem nondegenerate_greenQuotForm [FiniteDimensional K V] {g : BilinForm K V}
    (hnd : g.Nondegenerate) (hrefl : g.IsRefl) (p : ExFlag K V) (h : IsGreenSelfDual g p) :
    (greenQuotForm g hrefl p h).Nondegenerate := by
  have horth : g.orthogonal p.cycle = p.boundary := by
    rw [h, LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
  have key : ∀ x : p.homology,
      (∀ y : p.homology, greenQuotForm g hrefl p h x y = 0) → x = 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hzB : (z : V) ∈ p.boundary := by
      rw [← horth, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      exact hrefl (z : V) n (by simpa using hx (Submodule.Quotient.mk ⟨n, hn⟩))
    exact (Submodule.Quotient.mk_eq_zero _).2 hzB
  refine ⟨key, fun y hy => key y fun x => ?_⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simpa using hrefl (w : V) (z : V) (by simpa using hy (Submodule.Quotient.mk w))

/-! ## Positivity cannot precede the reduction -/

/-- **An anisotropic Green self-dual flag is trivial.**  If no nonzero vector is isotropic, the
boundary space of a Green self-dual flag vanishes and its cycle space is everything. -/
theorem IsGreenSelfDual.eq_trivial_of_anisotropic {g : BilinForm K V}
    (haniso : ∀ v : V, g v v = 0 → v = 0) {p : ExFlag K V} (h : IsGreenSelfDual g p) :
    p.boundary = ⊥ ∧ p.cycle = ⊤ := by
  have hb : p.boundary = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun b hb => haniso b (h.isotropic hb hb)
  refine ⟨hb, ?_⟩
  rw [h, hb, LinearMap.BilinForm.orthogonal_bot]

/-- **No nonzero boundary space survives a positive Green self-duality.** -/
theorem IsGreenSelfDual.boundary_eq_bot_of_anisotropic {g : BilinForm K V}
    (haniso : ∀ v : V, g v v = 0 → v = 0) {p : ExFlag K V} (h : IsGreenSelfDual g p) :
    p.boundary = ⊥ :=
  (h.eq_trivial_of_anisotropic haniso).1

end Green

/-! ## The positive-definite Hilbert case -/

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **A positive-definite Hermitian self-dual flag is trivial.**  The boundary space of a flag whose
cycle space is the orthogonal complement of its boundary space is isotropic for a definite inner
product, hence zero. -/
theorem eq_trivial_of_orthogonal_selfDual (p : ExFlag 𝕜 E) (h : p.cycle = p.boundaryᗮ) :
    p.boundary = ⊥ ∧ p.cycle = ⊤ := by
  have hb : p.boundary = ⊥ := by
    have hle : p.boundary ≤ p.boundary ⊓ p.boundaryᗮ :=
      le_inf (le_refl _) (h ▸ p.boundary_le_cycle)
    rw [Submodule.inf_orthogonal_eq_bot] at hle
    exact le_bot_iff.1 hle
  exact ⟨hb, by rw [h, hb, Submodule.bot_orthogonal_eq_top]⟩

end Hilbert

/-! ## The hyperbolic plane realizes both regimes -/

section Hyperbolic

/-- The hyperbolic form on the real plane. -/
noncomputable def hyperbolicForm : BilinForm ℝ (ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => x.1 * y.2 + x.2 * y.1)
    (by intro x y z; simp; ring)
    (by intro c x y; simp; ring)
    (by intro x y z; simp; ring)
    (by intro c x y; simp; ring)

@[simp] theorem hyperbolicForm_apply (x y : ℝ × ℝ) :
    hyperbolicForm x y = x.1 * y.2 + x.2 * y.1 := rfl

/-- The first coordinate axis of the hyperbolic plane. -/
noncomputable def hyperbolicLine : Submodule ℝ (ℝ × ℝ) :=
  Submodule.span ℝ {((1 : ℝ), (0 : ℝ))}

theorem mem_hyperbolicLine_iff {v : ℝ × ℝ} : v ∈ hyperbolicLine ↔ v.2 = 0 := by
  rw [hyperbolicLine, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    simp
  · intro h
    exact ⟨v.1, Prod.ext (by simp) (by simp [h])⟩

/-- The hyperbolic line is its own orthogonal. -/
theorem hyperbolicForm_orthogonal_line :
    hyperbolicForm.orthogonal hyperbolicLine = hyperbolicLine := by
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_hyperbolicLine_iff]
  constructor
  · intro h
    have := h ((1 : ℝ), (0 : ℝ)) (Submodule.mem_span_singleton_self _)
    simpa using this
  · intro h n hn
    rw [mem_hyperbolicLine_iff] at hn
    simp [hn, h]

/-- **The off-horizon hyperbolic flag is Green self-dual.**  Its boundary space is the isotropic
line, so it is not realizable by any anisotropic form. -/
theorem isGreenSelfDual_hyperbolic_offHorizon :
    IsGreenSelfDual hyperbolicForm ⟨hyperbolicLine, hyperbolicLine, le_refl _⟩ :=
  hyperbolicForm_orthogonal_line.symm

/-- **The horizon flag is Green self-dual for every form.** -/
theorem isGreenSelfDual_horizon {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (g : BilinForm K V) : IsGreenSelfDual g ⟨⊥, ⊤, le_top⟩ :=
  LinearMap.BilinForm.orthogonal_bot.symm

end Hyperbolic

end ExFlag

end GaloisForLFunctions.HTGeometry
