import GaloisForLFunctions.HTGeometry.DirectionalMultiplierFiniteLaw
import GaloisForLFunctions.HTGeometry.ProjectiveLineDirectionalCountability

/-!
# Projective finiteness of a two-direction multiplier Atiyah kernel

The multiplier Atiyah class and the projective finite-law filtration impose a sharp phase split
on a two-dimensional law space.  Either every projective direction already satisfies an order-one
scalar differential law, or the projectivized zero locus of the multiplier Atiyah class is finite.

This closes the pointwise Atiyah-kernel inclusion under the binary projective finiteness theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped LinearAlgebra.Projectivization

variable {G k K L : Type*} [Group G] [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [CharZero K]

/-- **Two-direction Atiyah-kernel finiteness law.**  In a compatible two-direction equivariant
multiplier system, either the order-one projective finite-law stratum is universal, or the
projectivized kernel of the multiplier Atiyah-class map is finite. -/
theorem multiplierAtiyahKernel_orderOne_universal_or_projectivelyFinite
    (rhoK : G →* (K ≃+* K)) (rhoL : G →* (L ≃+* L))
    (hfix : ∀ g c, rhoK g (algebraMap k K c) = algebraMap k K c)
    (hcomp : ∀ g y, rhoL g (algebraMap K L y) = algebraMap K L (rhoK g y))
    (hfixed : ∀ z : L, (∀ g, rhoL g z = z) → ∃ q : K, algebraMap K L q = z)
    (D0 : Fin 2 → equivariantDerivations rhoK hfix)
    (δ : Fin 2 → Derivation k L L)
    (hDcomp : ∀ i y, δ i (algebraMap K L y) = algebraMap K L ((D0 i).1 y))
    (hDcomm : ∀ i g y, δ i (rhoL g y) = rhoL g (δ i y))
    (hfixL : ∀ g c, rhoL g (algebraMap k L c) = algebraMap k L c)
    (a : G → Kˣ)
    (ha : ∀ g h, (a (g * h) : K) = rhoK g (a h : K) * (a g : K))
    (X : L) (hX : X ≠ 0)
    (hmul : ∀ g, rhoL g X = algebraMap K L (a g : K) * X) :
    projectiveDirectionalFiniteLawLocus (K := K) δ X 1 = Set.univ ∨
      ({p : ℙ k (Fin 2 → k) |
          multiplierAtiyahClassMap rhoK hfix a ha
            (∑ i, p.rep i • D0 i) = 0} : Set (ℙ k (Fin 2 → k))).Finite := by
  classical
  by_cases hproper :
      projectiveDirectionalFiniteLawLocus (K := K) δ X 1 = Set.univ
  · exact Or.inl hproper
  · right
    apply (projectiveDirectionalFiniteLawLocus_finite_fin2 δ X 1 hproper).subset
    intro p hp
    rw [← p.mk_rep]
    exact multiplierAtiyahKernel_mk_mem_projectiveDirectionalFiniteLawLocus_one
      rhoK rhoL hfix hcomp hfixed D0 δ hDcomp hDcomm hfixL a ha X hX hmul
      p.rep p.rep_nonzero hp

end

end GaloisForLFunctions.HTGeometry
