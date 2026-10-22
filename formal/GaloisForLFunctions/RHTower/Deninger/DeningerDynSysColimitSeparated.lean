import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysColimitTopology
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCharacterSeparated
import GaloisForLFunctions.HTGeometry.CompactGroupOrbitQuotientT2

/-!
# The colimit is Hausdorff

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 7.9 (`t89n`),
the assertion for `X̌ (C)`.

The canonical map `X̂ (C) → X̌ (C)` is an open embedding as soon as the Frobenius operators are
open maps on `X̂ (C)`, because the preimage of `X̂ (C) ∩ (image of a set)` under the structural map
of index `ν` is the Frobenius image of that set.  Any two points of `X̌ (C)` are carried into the
image of `X̂ (C)` by a single Frobenius homeomorphism: `F_μ` sends the class of `(μ, P)` to
that of `(1, P)`.  So `X̌ (C)` is Hausdorff whenever `X̂ (C)` is.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C] [TopologicalSpace C] {N₀ : Submonoid ℕ}

omit [TopologicalSpace C] in
/-- The structural maps pull the image of `X̂ (C)` back to a Frobenius image. -/
theorem deningerColimMk_preimage_unit_image
    (halg : ∀ x : X, IsAlgClosed (X.residueField x)) (hN₀ : ∀ ν ∈ N₀, 0 < ν) (ν : N₀)
    (s : Set (DeningerCharPoints X C)) :
    (deningerColimMk (X := X) (C := C) N₀ ν) ⁻¹'
        (deningerColimUnit (X := X) (C := C) N₀ '' s)
      = deningerCharFrobenius (X := X) (C := C) (ν : ℕ) '' s := by
  ext P
  simp only [Set.mem_preimage, Set.mem_image, deningerColimUnit]
  constructor
  · rintro ⟨Q, hQs, hQ⟩
    rw [deningerColimMk_eq_iff] at hQ
    obtain ⟨a, b, h1, h2⟩ := hQ
    have hab : (a : ℕ) = (ν : ℕ) * (b : ℕ) := by simpa using h1
    have hcomp : deningerCharFrobenius (b : ℕ) (deningerCharFrobenius (ν : ℕ) Q)
        = deningerCharFrobenius (a : ℕ) Q := by
      rw [deningerCharFrobenius_comp, hab]
    have hinj := deningerCharFrobenius_injective (X := X) (C := C) halg (hN₀ b b.2)
    exact ⟨Q, hQs, hinj (by rw [hcomp, h2])⟩
  · rintro ⟨Q, hQs, rfl⟩
    refine ⟨Q, hQs, (deningerColimMk_eq_iff).2 ⟨ν, 1, ?_, ?_⟩⟩
    · simp
    · simp [deningerCharFrobenius_one]

variable [ContinuousMul C]

omit [ContinuousMul C] in
/-- The canonical map `X̂ (C) → X̌ (C)` is an open map. -/
theorem deningerColimUnit_isOpenMap
    (halg : ∀ x : X, IsAlgClosed (X.residueField x)) (hN₀ : ∀ ν ∈ N₀, 0 < ν)
    (hopen : ∀ ν : ℕ, 0 < ν → IsOpenMap (deningerCharFrobenius (X := X) (C := C) ν)) :
    IsOpenMap (deningerColimUnit (X := X) (C := C) N₀) := by
  intro s hs
  rw [deningerColim_isOpen_iff]
  intro ν
  rw [deningerColimMk_preimage_unit_image halg hN₀ ν s]
  exact hopen (ν : ℕ) (hN₀ ν ν.2) s hs

omit [ContinuousMul C] in
/-- **Deninger, Proposition 7.4(a) (`t10`), refined.**  The canonical map `X̂ (C) → X̌ (C)` is an
open embedding. -/
theorem deningerColimUnit_isOpenEmbedding
    (halg : ∀ x : X, IsAlgClosed (X.residueField x)) (hN₀ : ∀ ν ∈ N₀, 0 < ν)
    (hopen : ∀ ν : ℕ, 0 < ν → IsOpenMap (deningerCharFrobenius (X := X) (C := C) ν)) :
    Topology.IsOpenEmbedding (deningerColimUnit (X := X) (C := C) N₀) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (deningerColimMk_continuous 1) (deningerColimUnit_injective halg hN₀)
    (deningerColimUnit_isOpenMap halg hN₀ hopen)

omit [TopologicalSpace C] [ContinuousMul C] in
/-- The Frobenius operator of index `μ` carries the class of `(μ, P)` into `X̂ (C)`. -/
theorem deningerColimFrobenius_mk_self (μ : N₀) (P : DeningerCharPoints X C) :
    deningerColimFrobenius (X := X) (C := C) N₀ (μ : ℕ) (deningerColimMk N₀ μ P)
      = deningerColimUnit N₀ P := by
  rw [deningerColimFrobenius_mk]
  refine (deningerColimMk_eq_iff).2 ⟨1, μ, ?_, ?_⟩
  · simp
  · simp [deningerCharFrobenius_one]

/-- **Deninger, Corollary 7.9 (`t89n`).**  If `X̂ (C)` is Hausdorff then so is `X̌ (C)`. -/
theorem deningerColimPoints_t2Space [T2Space (DeningerCharPoints X C)]
    (halg : ∀ x : X, IsAlgClosed (X.residueField x)) (hN₀ : ∀ ν ∈ N₀, 0 < ν)
    (hopen : ∀ ν : ℕ, 0 < ν → IsOpenMap (deningerCharFrobenius (X := X) (C := C) ν)) :
    T2Space (DeningerColimPoints N₀ X C) := by
  refine ⟨fun z w hzw => ?_⟩
  obtain ⟨μ, P, rfl⟩ := deningerColimMk_surjective z
  obtain ⟨μ', Q, rfl⟩ := deningerColimMk_surjective w
  set ν : N₀ := μ * μ' with hν
  have hνpos : 0 < (ν : ℕ) := hN₀ ν ν.2
  set Φ := deningerColimFrobeniusHomeomorph (X := X) (C := C) (N₀ := N₀) ν hνpos with hΦ
  have hz : Φ (deningerColimMk N₀ μ P)
      = deningerColimUnit N₀ (deningerCharFrobenius (μ' : ℕ) P) := by
    show deningerColimFrobenius N₀ (ν : ℕ) (deningerColimMk N₀ μ P) = _
    rw [deningerColimFrobenius_mk]
    have : deningerCharFrobenius (X := X) (C := C) (ν : ℕ) P
        = deningerCharFrobenius (μ : ℕ) (deningerCharFrobenius (μ' : ℕ) P) := by
      rw [deningerCharFrobenius_comp]
      congr 1
      rw [hν]
      push_cast
      ring
    rw [this, ← deningerColimFrobenius_mk]
    exact deningerColimFrobenius_mk_self μ _
  have hw : Φ (deningerColimMk N₀ μ' Q)
      = deningerColimUnit N₀ (deningerCharFrobenius (μ : ℕ) Q) := by
    show deningerColimFrobenius N₀ (ν : ℕ) (deningerColimMk N₀ μ' Q) = _
    rw [deningerColimFrobenius_mk]
    have : deningerCharFrobenius (X := X) (C := C) (ν : ℕ) Q
        = deningerCharFrobenius (μ' : ℕ) (deningerCharFrobenius (μ : ℕ) Q) := by
      rw [deningerCharFrobenius_comp]
      congr 1
    rw [this, ← deningerColimFrobenius_mk]
    exact deningerColimFrobenius_mk_self μ' _
  have hemb := deningerColimUnit_isOpenEmbedding (X := X) (C := C) (N₀ := N₀) halg hN₀ hopen
  have hne : deningerCharFrobenius (μ' : ℕ) P ≠ deningerCharFrobenius (μ : ℕ) Q := by
    intro h
    apply hzw
    apply Φ.injective
    rw [hz, hw, h]
  obtain ⟨V, W, hV, hW, hPV, hQW, hVW⟩ := t2_separation hne
  refine ⟨Φ ⁻¹' (deningerColimUnit N₀ '' V), Φ ⁻¹' (deningerColimUnit N₀ '' W),
    Φ.continuous.isOpen_preimage _ (hemb.isOpenMap V hV),
    Φ.continuous.isOpen_preimage _ (hemb.isOpenMap W hW), ?_, ?_, ?_⟩
  · exact ⟨_, hPV, hz.symm⟩
  · exact ⟨_, hQW, hw.symm⟩
  · rw [Set.disjoint_left]
    intro a ha hb
    obtain ⟨p, hp, hpa⟩ := ha
    obtain ⟨q, hq, hqa⟩ := hb
    have : p = q := deningerColimUnit_injective halg hN₀ (hpa.trans hqa.symm)
    rw [this] at hp
    exact (Set.disjoint_left.1 hVW) hp hq

/-! ### The quotients by the Galois group -/

omit [ContinuousMul C] in
/-- **Deninger, Corollary 7.9 (`t89n`).**  `X̂₀ (C) = X̂ (C) / G` is Hausdorff for a compact group
acting continuously. -/
theorem deningerCharPointsQuotient_t2Space {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MulAction G (DeningerCharPoints X C)]
    [ContinuousSMul G (DeningerCharPoints X C)] [T2Space (DeningerCharPoints X C)] :
    T2Space (MulAction.orbitRel.Quotient G (DeningerCharPoints X C)) :=
  HTGeometry.t2Space_orbitQuotient_of_compactSpace

omit [ContinuousMul C] in
/-- **Deninger, Corollary 7.9 (`t89n`).**  `X̌₀ (C) = X̌ (C) / G` is Hausdorff for a compact group
acting continuously. -/
theorem deningerColimPointsQuotient_t2Space {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MulAction G (DeningerColimPoints N₀ X C)]
    [ContinuousSMul G (DeningerColimPoints N₀ X C)]
    [T2Space (DeningerColimPoints N₀ X C)] :
    T2Space (MulAction.orbitRel.Quotient G (DeningerColimPoints N₀ X C)) :=
  HTGeometry.t2Space_orbitQuotient_of_compactSpace

end RHTower
