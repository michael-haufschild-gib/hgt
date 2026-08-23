import GaloisForLFunctions.HTGeometry.BlockProductMetric
import GaloisForLFunctions.RHTower.DeningerDynSysAffineTopology
import GaloisForLFunctions.HTGeometry.CompactOrbitQuotientMetric
import Mathlib.Topology.Bases

/-!
# An invariant metric on the character points of an affine scheme

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 7.6 (`t86`).

For an affine arithmetic scheme the coordinate ring `R` is countable and the group `G` acts on it
with finite orbits.  Weighting the bounded distances over the orbits therefore produces a
`G`-invariant metric on `C^R` inducing the topology of pointwise convergence, and hence on the
subspace `X̂ (C)` of character points.  If `C` is separable then `C^R` is second countable, hence so
is `X̂ (C)`, and therefore `X̂ (C)` is separable.
-/

namespace RHTower

open HTGeometry
open scoped Pointwise

variable {R C : Type*} [CommRing R] [CommRing C] [MetricSpace C]
variable {G : Type*} [Group G] [MulSemiringAction G R]

/-- **Deninger, Proposition 7.6 (`t86`), first half.**  For a countable coordinate ring with finite
`G`-orbits the space of character points carries a `G`-invariant metric inducing its topology. -/
theorem deningerAffinePoints_exists_invariant_metric [Countable R]
    (hfin : ∀ r : R, (MulAction.orbit G r).Finite) :
    ∃ d : DeningerAffinePoints R C → DeningerAffinePoints R C → ℝ,
      (∀ P, d P P = 0) ∧ (∀ P Q, d P Q = d Q P) ∧
      (∀ P Q S, d P S ≤ d P Q + d Q S) ∧
      (∀ P Q, d P Q = 0 → P = Q) ∧
      (∀ s : Set (DeningerAffinePoints R C),
        IsOpen s ↔ ∀ P ∈ s, ∃ ε > 0, ∀ Q, d P Q < ε → Q ∈ s) ∧
      (∀ (σ : G) (P Q : DeningerAffinePoints R C),
        d (deningerAffineSMul σ P) (deningerAffineSMul σ Q) = d P Q) := by
  classical
  set blk : R → Finset R := fun r => (hfin r).toFinset with hblk
  obtain ⟨c, hc, hsum⟩ := exists_blockWeights (ι := R) (κ := R) blk
  have hcov : ∀ r : R, ∃ k : R, r ∈ blk k := by
    intro r
    refine ⟨r, ?_⟩
    rw [hblk]
    simp
  have hstab : ∀ (σ : G) (k : R),
      (blk k).map (MulAction.toPerm σ).toEmbedding = blk k := by
    intro σ k
    apply Finset.coe_injective
    rw [Finset.coe_map, hblk]
    simp only [Set.Finite.coe_toFinset]
    have himg : (fun r : R => σ • r) '' MulAction.orbit G k = σ • MulAction.orbit G k :=
      Set.image_smul
    calc ((MulAction.toPerm σ).toEmbedding : R → R) '' MulAction.orbit G k
        = (fun r : R => σ • r) '' MulAction.orbit G k := rfl
      _ = σ • MulAction.orbit G k := himg
      _ = MulAction.orbit G k := MulAction.smul_orbit σ k
  refine ⟨fun P Q => blockDist blk c P.toFun Q.toFun, fun P => blockDist_self _,
    fun P Q => blockDist_comm _ _,
    fun P Q S => blockDist_triangle (fun k => (hc k).le) hsum _ _ _, ?_, ?_, ?_⟩
  · intro P Q h
    refine DeningerAffinePoints.ext fun r => ?_
    exact congrFun (eq_of_blockDist_eq_zero hc hsum hcov h) r
  · intro s
    refine isOpen_iff_of_isInducing (f := DeningerAffinePoints.toFun (R := R) (C := C)) ⟨rfl⟩
      (blockDist blk c) (fun a b e => blockDist_triangle (fun k => (hc k).le) hsum a b e)
      (fun P => blockDist_self P) (blockDist_isOpen_iff hc hsum hcov) s
  · intro σ P Q
    show blockDist blk c (deningerAffineSMul σ P).toFun (deningerAffineSMul σ Q).toFun
      = blockDist blk c P.toFun Q.toFun
    have hP : (deningerAffineSMul σ P).toFun = P.toFun ∘ (MulAction.toPerm σ) := rfl
    have hQ : (deningerAffineSMul σ Q).toFun = Q.toFun ∘ (MulAction.toPerm σ) := rfl
    rw [hP, hQ]
    exact blockDist_congr_equiv _ (hstab σ) _ _

/-- **Deninger, Proposition 7.6 (`t86`), second half.**  If `C` is separable then the space of
character points of an affine scheme with countable coordinate ring is second countable. -/
instance deningerAffinePoints_secondCountable [Countable R]
    [TopologicalSpace.SeparableSpace C] :
    SecondCountableTopology (DeningerAffinePoints R C) :=
  Topology.IsInducing.secondCountableTopology
    (f := DeningerAffinePoints.toFun (R := R) (C := C)) ⟨rfl⟩

/-- The space of character points of an affine scheme with countable coordinate ring is separable
whenever `C` is. -/
instance deningerAffinePoints_separable [Countable R] [TopologicalSpace.SeparableSpace C] :
    TopologicalSpace.SeparableSpace (DeningerAffinePoints R C) :=
  inferInstance

/-- **Deninger, Corollary 7.8 (`t88`).**  On the character points of an affine scheme with
countable coordinate ring and a compact group `G` acting with finite orbits on the ring and
continuous orbit maps on the points there are a `G`-invariant metric `d` inducing the topology and
a quotient distance `δ` with `δ ≤ d`, constant on `G`-orbits, vanishing exactly on an orbit, and
inducing the quotient topology: a `G`-invariant subset is open exactly when it contains a
`δ`-ball around each of its points. -/
theorem deningerAffinePoints_exists_quotient_metric [Countable R] [TopologicalSpace G]
    [CompactSpace G] (hfin : ∀ r : R, (MulAction.orbit G r).Finite)
    (hcont : ∀ P : DeningerAffinePoints R C,
      Continuous fun σ : G => deningerAffineSMul σ⁻¹ P) :
    ∃ d δ : DeningerAffinePoints R C → DeningerAffinePoints R C → ℝ,
      (∀ P, d P P = 0) ∧ (∀ P Q, d P Q = d Q P) ∧
      (∀ P Q S, d P S ≤ d P Q + d Q S) ∧ (∀ P Q, d P Q = 0 → P = Q) ∧
      (∀ s : Set (DeningerAffinePoints R C),
        IsOpen s ↔ ∀ P ∈ s, ∃ ε > 0, ∀ Q, d P Q < ε → Q ∈ s) ∧
      (∀ (σ : G) (P Q), d (deningerAffineSMul σ P) (deningerAffineSMul σ Q) = d P Q) ∧
      (∀ P Q, δ P Q = δ Q P) ∧ (∀ P Q S, δ P S ≤ δ P Q + δ Q S) ∧
      (∀ P Q, δ P Q ≤ d P Q) ∧
      (∀ (σ : G) (P Q), δ (deningerAffineSMul σ P) Q = δ P Q) ∧
      (∀ P Q, δ P Q = 0 ↔ ∃ σ : G, deningerAffineSMul σ P = Q) ∧
      (∀ s : Set (DeningerAffinePoints R C),
        (∀ (σ : G) (P), P ∈ s → deningerAffineSMul σ P ∈ s) →
          (IsOpen s ↔ ∀ P ∈ s, ∃ ε > 0, ∀ Q, δ P Q < ε → Q ∈ s)) := by
  classical
  obtain ⟨d, hself, hcomm, htri, hzero, htop, hinv⟩ :=
    deningerAffinePoints_exists_invariant_metric (C := C) (G := G) hfin
  letI m : MetricSpace (DeningerAffinePoints R C) :=
    MetricSpace.ofDistTopology d hself hcomm htri htop hzero
  letI act : MulAction G (DeningerAffinePoints R C) :=
    { smul := fun σ P => deningerAffineSMul σ⁻¹ P
      one_smul := fun P => by
        refine DeningerAffinePoints.ext fun r => ?_
        show P.1 ((1 : G)⁻¹ • r) = P.1 r
        simp
      mul_smul := fun σ τ P => by
        refine DeningerAffinePoints.ext fun r => ?_
        show P.1 ((σ * τ)⁻¹ • r) = P.1 (τ⁻¹ • σ⁻¹ • r)
        rw [mul_inv_rev, mul_smul] }
  haveI hiso : IsIsometricSMul G (DeningerAffinePoints R C) :=
    ⟨fun σ => Isometry.of_dist_eq fun P Q => hinv σ⁻¹ P Q⟩
  refine ⟨d, fun P Q => orbitDist G P Q, hself, hcomm, htri, hzero, htop, hinv,
    fun P Q => orbitDist_comm P Q, fun P Q S => orbitDist_triangle hcont P Q S,
    fun P Q => orbitDist_le_dist P Q, ?_, ?_, ?_⟩
  · intro σ P Q
    show orbitDist G (deningerAffineSMul σ P) Q = orbitDist G P Q
    have hpt : (σ⁻¹ • P) = deningerAffineSMul σ P := by
      show deningerAffineSMul (σ⁻¹)⁻¹ P = deningerAffineSMul σ P
      rw [inv_inv]
    have h := orbitDist_smul_left (G := G) σ⁻¹ P Q
    rw [hpt] at h
    exact h
  · intro P Q
    rw [orbitDist_eq_zero_iff hcont]
    constructor
    · rintro ⟨σ, hσ⟩
      exact ⟨σ⁻¹, hσ⟩
    · rintro ⟨σ, hσ⟩
      refine ⟨σ⁻¹, ?_⟩
      show deningerAffineSMul (σ⁻¹)⁻¹ P = Q
      rw [inv_inv]
      exact hσ
  · intro s hs
    constructor
    · intro hopen P hP
      obtain ⟨ε, hε, hball⟩ := (htop s).1 hopen P hP
      refine ⟨ε, hε, fun Q hQ => ?_⟩
      obtain ⟨σ, hσ⟩ := exists_orbitDist_eq (G := G) hcont P Q
      have hd : d (σ • P) Q < ε := by
        show dist (σ • P) Q < ε
        rw [← hσ]
        exact hQ
      have h2 : d (σ • P) Q = d P (σ⁻¹ • Q) := by
        show dist (σ • P) Q = dist P (σ⁻¹ • Q)
        rw [← dist_smul σ⁻¹ (σ • P) Q, inv_smul_smul]
      have hswap : d P (σ⁻¹ • Q) < ε := h2 ▸ hd
      have hmem : σ⁻¹ • Q ∈ s := hball _ hswap
      have hQeq : Q = deningerAffineSMul σ⁻¹ (σ⁻¹ • Q) := (smul_inv_smul σ Q).symm
      rw [hQeq]
      exact hs _ _ hmem
    · intro hδ
      refine (htop s).2 fun P hP => ?_
      obtain ⟨ε, hε, h⟩ := hδ P hP
      exact ⟨ε, hε, fun Q hQ => h Q (lt_of_le_of_lt (orbitDist_le_dist P Q) hQ)⟩

end RHTower
