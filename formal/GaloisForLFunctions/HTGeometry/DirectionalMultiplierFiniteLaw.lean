import GaloisForLFunctions.HTGeometry.DirectionalMultiplierAtiyahClass

/-!
# The multiplier Atiyah kernel is an order-one finite-law locus

A vanishing directional multiplier Atiyah class gives a first-order scalar differential law for
the multiplier primitive.  Consequently the value/derivative pair is algebraically dependent.
This is the precise affine content of the projective inclusion of the Atiyah kernel in the first
finite-law stratum.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {G k K L : Type*} [Group G] [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

/-- A first-order scalar law makes the value/derivative pair algebraically dependent. -/
theorem not_algebraicIndependent_pair_of_eq_smul
    (X Y : L) (q : K) (hY : Y = algebraMap K L q * X) :
    ¬ AlgebraicIndependent K (fun j : Fin 2 => ![X, Y] j) := by
  intro hAI
  let P : MvPolynomial (Fin 2) K :=
    MvPolynomial.X 1 - MvPolynomial.C q * MvPolynomial.X 0
  have hP : P ≠ 0 := by
    intro hzero
    have h := congrArg
      (MvPolynomial.eval fun j : Fin 2 => ![(0 : K), 1] j) hzero
    simpa [P] using h
  apply hP
  apply hAI.eq_zero_of_aeval_eq_zero
  simp [P, hY]

omit [IsScalarTower k K L] in
/-- Every direction in the multiplier Atiyah kernel lies in the order-one finite-law locus. -/
theorem multiplierAtiyahClassMap_zero_not_algebraicIndependent_pair
    (rhoK : G →* (K ≃+* K)) (rhoL : G →* (L ≃+* L))
    (hfix : ∀ g c, rhoK g (algebraMap k K c) = algebraMap k K c)
    (hcomp : ∀ g y, rhoL g (algebraMap K L y) = algebraMap K L (rhoK g y))
    (hfixed : ∀ z : L, (∀ g, rhoL g z = z) → ∃ q : K, algebraMap K L q = z)
    (D0 : equivariantDerivations rhoK hfix) (D : Derivation k L L)
    (hDcomp : ∀ y, D (algebraMap K L y) = algebraMap K L (D0.1 y))
    (hDcomm : ∀ g y, D (rhoL g y) = rhoL g (D y))
    (a : G → Kˣ)
    (ha : ∀ g h, (a (g * h) : K) = rhoK g (a h : K) * (a g : K))
    (X : L) (hX : X ≠ 0)
    (hmul : ∀ g, rhoL g X = algebraMap K L (a g : K) * X)
    (hker : multiplierAtiyahClassMap rhoK hfix a ha D0 = 0) :
    ¬ AlgebraicIndependent K (fun j : Fin 2 => ![X, D X] j) := by
  obtain ⟨q, hq⟩ :=
    (multiplierAtiyahClassMap_eq_zero_iff_exists_firstOrder
      rhoK rhoL hfix hcomp hfixed D0 D hDcomp hDcomm a ha X hX hmul).mp hker
  exact not_algebraicIndependent_pair_of_eq_smul X (D X) q hq

end

end GaloisForLFunctions.HTGeometry
