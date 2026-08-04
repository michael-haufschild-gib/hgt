import GaloisForLFunctions.HTGeometry.NonautonomousDeckClosure
import GaloisForLFunctions.HTGeometry.NonautonomousIsogenyTransport
import GaloisForLFunctions.HTGeometry.DeckDegreeCriterion
import GaloisForLFunctions.HTGeometry.PrefixDeckFromInvariantRing

/-!
# The field tail sees exactly the erased sector

The deck description of a phase tail is stated depth by depth: each finite prefix image is the fixed
field of that depth's deck group.  When the deck groups come from a protocol acting on the field --
each depth acting through the kernel of that depth's prefix composite -- the tail is the fixed field
of the image of the *whole* erased sector.

So the group-level object built from the protocol and the field-level tail are the same object read
twice, and the only geometric input left is the depthwise identification: that a prefix image is the
fixed field of the translations by that prefix's kernel.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {G : ℕ → Type*} [∀ i, CommGroup (G i)]

/-- **The tail is the fixed field of the erased sector.**  If at every depth the prefix image is the
fixed field of the translations by that depth's kernel, then the tail is the fixed field of the
translations by the whole erased sector. -/
theorem nonautonomousTail_eq_fixedField_erasedSector
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : G i →* (F ≃ₐ[K] F))
    (hdeck : ∀ n, IntermediateField.map (forwardPrefix φ i n) ⊤ =
      IntermediateField.fixedField ((prefixKernel a i n).map ρ)) :
    nonautonomousTail φ i = IntermediateField.fixedField ((erasedSector a i).map ρ) := by
  rw [nonautonomousTail_eq_fixedField_iSup φ i (fun n => (prefixKernel a i n).map ρ) hdeck,
    erasedSector, Subgroup.map_iSup]

/-- Pointwise form: a phase observable survives the whole future exactly when every erased direction
fixes it. -/
theorem mem_nonautonomousTail_iff_fixedBy_erasedSector
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : G i →* (F ≃ₐ[K] F))
    (hdeck : ∀ n, IntermediateField.map (forwardPrefix φ i n) ⊤ =
      IntermediateField.fixedField ((prefixKernel a i n).map ρ)) (x : F) :
    x ∈ nonautonomousTail φ i ↔ ∀ g ∈ (erasedSector a i).map ρ, g x = x := by
  rw [nonautonomousTail_eq_fixedField_erasedSector φ i a ρ hdeck]
  constructor
  · intro hx g hg
    exact hx ⟨g, hg⟩
  · intro hx g
    exact hx (g : F ≃ₐ[K] F) g.2

section Topological

variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]

/-- **Closing the erased sector changes nothing the field can see.**  If the action is algebraic --
every element's stabilizer is closed -- then the invariants of the erased sector and of its closure
agree.  This is what lets the tail be described by the *closed* erased sector. -/
theorem fixedField_map_erasedClosure
    (a : ∀ j, G j →* G (j + 1)) (i : ℕ) (ρ : G i →* (F ≃ₐ[K] F))
    (hclosed : ∀ x : F, IsClosed {g : G i | ρ g x = x}) :
    IntermediateField.fixedField ((erasedClosure a i).map ρ)
      = IntermediateField.fixedField ((erasedSector a i).map ρ) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro g hg
    refine hx g ?_
    obtain ⟨h, hh, rfl⟩ := hg
    exact ⟨h, Subgroup.le_topologicalClosure _ hh, rfl⟩
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro g hg
    obtain ⟨h, hh, rfl⟩ := hg
    have hsub : (erasedSector a i : Set (G i)) ⊆ {g : G i | ρ g x = x} := by
      intro k hk
      exact hx (ρ k) ⟨k, hk, rfl⟩
    have hcl : closure (erasedSector a i : Set (G i)) ⊆ {g : G i | ρ g x = x} :=
      closure_minimal hsub (hclosed x)
    exact hcl (by rwa [← Subgroup.topologicalClosure_coe] )

/-- **The tail is the fixed field of the closed erased sector.**  Depthwise deck description plus an
algebraic action give the card's phase-tail identity with the closed erased sector. -/
theorem nonautonomousTail_eq_fixedField_erasedClosure
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : G i →* (F ≃ₐ[K] F))
    (hdeck : ∀ n, IntermediateField.map (forwardPrefix φ i n) ⊤ =
      IntermediateField.fixedField ((prefixKernel a i n).map ρ))
    (hclosed : ∀ x : F, IsClosed {g : G i | ρ g x = x}) :
    nonautonomousTail φ i = IntermediateField.fixedField ((erasedClosure a i).map ρ) := by
  rw [fixedField_map_erasedClosure a i ρ hclosed]
  exact nonautonomousTail_eq_fixedField_erasedSector φ i a ρ hdeck

/-- **The phase tail from numerical data alone.**  If at every depth the kernel translations fix the
prefix image, the image has degree the order of that kernel, the kernels are finite and the images are
of finite degree, and the action is algebraic, then the tail is the fixed field of the closed erased
sector.  No descent theory enters: Artin's degree formula does the identification depth by depth. -/
theorem nonautonomousTail_eq_fixedField_erasedClosure_of_finrank
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : G i →* (F ≃ₐ[K] F))
    (hfin : ∀ n, Finite ((prefixKernel a i n).map ρ))
    (hfd : ∀ n, FiniteDimensional (IntermediateField.map (forwardPrefix φ i n) ⊤) F)
    (hfix : ∀ n, IntermediateField.map (forwardPrefix φ i n) ⊤ ≤
      IntermediateField.fixedField ((prefixKernel a i n).map ρ))
    (hdeg : ∀ n, Module.finrank (IntermediateField.map (forwardPrefix φ i n) ⊤) F
      = Nat.card ((prefixKernel a i n).map ρ))
    (hclosed : ∀ x : F, IsClosed {g : G i | ρ g x = x}) :
    nonautonomousTail φ i = IntermediateField.fixedField ((erasedClosure a i).map ρ) := by
  refine nonautonomousTail_eq_fixedField_erasedClosure φ i a ρ (fun n => ?_) hclosed
  haveI := hfin n
  haveI := hfd n
  exact prefixImage_eq_fixedField_of_finrank_eq φ i n a ρ (hfix n) (hdeg n)

/-- **The phase tail with one geometric input.**  Equivariance of the protocol, finiteness of the
kernels, finite degree of the prefixes and an algebraic action leave exactly one thing to supply: that
the degree of a prefix equals the order of its kernel. -/
theorem nonautonomousTail_eq_fixedField_erasedClosure_of_equivariant
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : ∀ j, G j →* (F ≃ₐ[K] F))
    (hfin : ∀ n, Finite ((prefixKernel a i n).map (ρ i)))
    (hfd : ∀ n, FiniteDimensional (IntermediateField.map (forwardPrefix φ i n) ⊤) F)
    (hequiv : ∀ (n : ℕ) (g : G i) (y : F), ρ i g (forwardPrefix φ i n y)
      = forwardPrefix φ i n (ρ (prefixIndex i n) (prefixHom a i n g) y))
    (hdeg : ∀ n, Module.finrank (IntermediateField.map (forwardPrefix φ i n) ⊤) F
      = Nat.card ((prefixKernel a i n).map (ρ i)))
    (hclosed : ∀ x : F, IsClosed {g : G i | ρ i g x = x}) :
    nonautonomousTail φ i = IntermediateField.fixedField ((erasedClosure a i).map (ρ i)) := by
  refine nonautonomousTail_eq_fixedField_erasedClosure φ i a (ρ i) (fun n => ?_) hclosed
  haveI := hfin n
  haveI := hfd n
  exact prefixImage_eq_fixedField_of_equivariant_of_finrank_eq φ i n a ρ (hequiv n) (hdeg n)

/-- **The phase tail from the ring-level quotient statement.**  The only geometric content left is
that an invariant regular function is pulled back from the quotient — no degrees, no descent. -/
theorem nonautonomousTail_eq_fixedField_erasedClosure_of_invariant_ring
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : ∀ j, G j →* (F ≃ₐ[K] F))
    (B : Type*) [CommRing B] [IsDomain B] [Algebra B F] [IsFractionRing B F]
    [MulSemiringAction (G i) B] [MulSemiringAction (G i) F]
    (hfin : ∀ n, Finite (prefixKernel a i n))
    (hcompat : ∀ (g : G i) (b : B), g • algebraMap B F b = algebraMap B F (g • b))
    (hact : ∀ (g : G i) (x : F), g • x = ρ i g x)
    (hring : ∀ (n : ℕ) (b : B), (∀ g : prefixKernel a i n, (g : G i) • b = b) →
      algebraMap B F b ∈ IntermediateField.map (forwardPrefix φ i n) ⊤)
    (hequiv : ∀ (n : ℕ) (g : G i) (y : F), ρ i g (forwardPrefix φ i n y)
      = forwardPrefix φ i n (ρ (prefixIndex i n) (prefixHom a i n g) y))
    (hclosed : ∀ x : F, IsClosed {g : G i | ρ i g x = x}) :
    nonautonomousTail φ i = IntermediateField.fixedField ((erasedClosure a i).map (ρ i)) := by
  refine nonautonomousTail_eq_fixedField_erasedClosure φ i a (ρ i) (fun n => ?_) hclosed
  haveI := hfin n
  exact prefixImage_eq_fixedField_of_invariant_ring φ i n a ρ B
    (fun g b => hcompat (g : G i) b) (fun g x => hact (g : G i) x) (hring n) (hequiv n)

/-- **The phase tail of a stabilizing protocol, with no algebraicity hypothesis.**  If no depth beyond
some `N` erases anything new and that kernel is closed, the closure step is vacuous and the tail is the
fixed field of the erased sector outright. -/
theorem nonautonomousTail_eq_fixedField_erasedClosure_of_stabilizes
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : G i →* (F ≃ₐ[K] F)) (N : ℕ)
    (hstab : ∀ n, N ≤ n → prefixKernel a i n = prefixKernel a i N)
    (hkclosed : IsClosed (prefixKernel a i N : Set (G i)))
    (hdeck : ∀ n, IntermediateField.map (forwardPrefix φ i n) ⊤ =
      IntermediateField.fixedField ((prefixKernel a i n).map ρ)) :
    nonautonomousTail φ i = IntermediateField.fixedField ((erasedClosure a i).map ρ) := by
  rw [erasedClosure_eq_prefixKernel_of_stabilizes a i N hstab hkclosed,
    nonautonomousTail_eq_fixedField_erasedSector φ i a ρ hdeck,
    erasedSector_eq_prefixKernel_of_stabilizes a i N hstab]

/-- **`(1)` for a stabilizing protocol, from the ring-level quotient statement alone.**  Neither an
algebraic action nor a degree count is needed: stabilization kills the closure step and the invariant
ring statement supplies the deck description. -/
theorem nonautonomousTail_eq_fixedField_of_stabilizes_of_invariant_ring
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : ∀ j, G j →* (F ≃ₐ[K] F)) (N : ℕ)
    (B : Type*) [CommRing B] [IsDomain B] [Algebra B F] [IsFractionRing B F]
    [MulSemiringAction (G i) B] [MulSemiringAction (G i) F]
    (hstab : ∀ n, N ≤ n → prefixKernel a i n = prefixKernel a i N)
    (hkclosed : IsClosed (prefixKernel a i N : Set (G i)))
    (hfin : ∀ n, Finite (prefixKernel a i n))
    (hcompat : ∀ (g : G i) (b : B), g • algebraMap B F b = algebraMap B F (g • b))
    (hact : ∀ (g : G i) (x : F), g • x = ρ i g x)
    (hring : ∀ (n : ℕ) (b : B), (∀ g : prefixKernel a i n, (g : G i) • b = b) →
      algebraMap B F b ∈ IntermediateField.map (forwardPrefix φ i n) ⊤)
    (hequiv : ∀ (n : ℕ) (g : G i) (y : F), ρ i g (forwardPrefix φ i n y)
      = forwardPrefix φ i n (ρ (prefixIndex i n) (prefixHom a i n g) y)) :
    nonautonomousTail φ i = IntermediateField.fixedField ((erasedClosure a i).map (ρ i)) := by
  refine nonautonomousTail_eq_fixedField_erasedClosure_of_stabilizes φ i a (ρ i) N hstab hkclosed
    fun n => ?_
  haveI := hfin n
  exact prefixImage_eq_fixedField_of_invariant_ring φ i n a ρ B
    (fun g b => hcompat (g : G i) b) (fun g x => hact (g : G i) x) (hring n) (hequiv n)

end Topological

end

end GaloisForLFunctions.HTGeometry
