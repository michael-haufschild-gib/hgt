import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCharacterTopology

/-!
# Continuity of the group action on character points

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 7.5 (`t85`).

Deninger's proof has two steps.  First the assertion is local on `X̂ (C) × G`, because `X̂ (C)` is
covered by open `G`-invariant subspaces coming from affine opens of the base; that step is the
purely topological gluing lemma below.  Second, over such a piece the action on the sections has
open stabilisers, so each coordinate of the action map is locally constant in the group variable
and the map is continuous.

The compatibility used in the second step is the identity `eval U g (σ · P) = eval U (σ · g) P`
relating the action on character points to the action on sections.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory Filter Topology

universe u

/-- **Deninger, Proposition 7.5 (`t85`), the locality step.**  A map out of `Z × G` is continuous
as soon as it is continuous over each member of an open cover of `Z`. -/
theorem continuous_of_isOpen_cover_prod {Z G Y : Type*} [TopologicalSpace Z] [TopologicalSpace G]
    [TopologicalSpace Y] (f : Z × G → Y) {ι : Type*} (W : ι → Set Z)
    (hopen : ∀ i, IsOpen (W i)) (hcov : ∀ z : Z, ∃ i, z ∈ W i)
    (hcont : ∀ i, ContinuousOn f ((W i) ×ˢ (Set.univ : Set G))) : Continuous f := by
  rw [continuous_iff_continuousAt]
  rintro ⟨z, g⟩
  obtain ⟨i, hi⟩ := hcov z
  have hnhd : (W i) ×ˢ (Set.univ : Set G) ∈ 𝓝 ((z, g) : Z × G) :=
    ((hopen i).prod isOpen_univ).mem_nhds ⟨hi, trivial⟩
  exact (hcont i).continuousAt hnhd

variable {X : Scheme.{u}} {C : Type u} [Field C] [TopologicalSpace C]
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The induced action on the character points lying over an open subset. -/
def deningerCharOverAct {U : X.Opens}
    (act : G → DeningerCharPoints X C → DeningerCharPoints X C)
    (hmem : ∀ (σ : G) (P : DeningerCharPoints X C), P.1 ∈ U → (act σ P).1 ∈ U)
    (σ : G) (P : DeningerCharOver X C U) : DeningerCharOver X C U :=
  ⟨act σ P.val, hmem σ P.val P.mem⟩

omit [TopologicalSpace C] [Group G] [TopologicalSpace G] in
@[simp] theorem deningerCharOverAct_val {U : X.Opens}
    (act : G → DeningerCharPoints X C → DeningerCharPoints X C)
    (hmem : ∀ (σ : G) (P : DeningerCharPoints X C), P.1 ∈ U → (act σ P).1 ∈ U)
    (σ : G) (P : DeningerCharOver X C U) :
    (deningerCharOverAct act hmem σ P).val = act σ P.val := rfl

/-- **Deninger, Proposition 7.5 (`t85`), the affine step.**  Over an open subset on which the
group acts, with a compatible action on the sections whose stabilisers are open, the action map on
the character points is jointly continuous. -/
theorem deningerCharOver_smul_continuous {U : X.Opens} [MulAction G Γ(X, U)]
    (act : G → DeningerCharPoints X C → DeningerCharPoints X C)
    (hmem : ∀ (σ : G) (P : DeningerCharPoints X C), P.1 ∈ U → (act σ P).1 ∈ U)
    (hcompat : ∀ (σ : G) (g : Γ(X, U)) (P : DeningerCharPoints X C),
      deningerCharEval U g (act σ P) = deningerCharEval U (σ • g) P)
    (hstab : ∀ (g : Γ(X, U)) (σ₀ : G), ∀ᶠ σ in 𝓝 σ₀, σ • g = σ₀ • g) :
    Continuous fun p : DeningerCharOver X C U × G =>
      deningerCharOverAct act hmem p.2 p.1 := by
  have hind : Topology.IsInducing (fun P : DeningerCharOver X C U =>
      fun f : Γ(X, U) => deningerCharEval U f P.val) := ⟨rfl⟩
  rw [hind.continuous_iff]
  refine continuous_pi (fun g : Γ(X, U) => ?_)
  rw [continuous_iff_continuousAt]
  rintro ⟨P₀, σ₀⟩
  have hbase : ContinuousAt
      (fun p : DeningerCharOver X C U × G => deningerCharEval U (σ₀ • g) p.1.val) (P₀, σ₀) :=
    ((deningerCharEval_continuous U (σ₀ • g)).comp continuous_fst).continuousAt
  refine hbase.congr ?_
  have hsnd : Tendsto (fun p : DeningerCharOver X C U × G => p.2) (𝓝 (P₀, σ₀)) (𝓝 σ₀) :=
    continuous_snd.continuousAt
  filter_upwards [hsnd.eventually (hstab g σ₀)] with p hp
  show deningerCharEval U (σ₀ • g) p.1.val = deningerCharEval U g (act p.2 p.1.val)
  rw [hcompat, hp]

end RHTower
