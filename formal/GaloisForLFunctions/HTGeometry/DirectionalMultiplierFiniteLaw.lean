import GaloisForLFunctions.HTGeometry.DirectionalMultiplierAtiyahClass
import GaloisForLFunctions.HTGeometry.ProjectiveDirectionalFiniteLaw

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
    simp [P] at h
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

/-- **Projectivized Atiyah-kernel inclusion.** For a finite compatible family of equivariant
derivations, every nonzero law direction in the kernel of the multiplier Atiyah-class map belongs
to the projective order-one finite-law stratum. -/
theorem multiplierAtiyahKernel_mk_mem_projectiveDirectionalFiniteLawLocus_one
    {ι : Type*} [Fintype ι]
    (rhoK : G →* (K ≃+* K)) (rhoL : G →* (L ≃+* L))
    (hfix : ∀ g c, rhoK g (algebraMap k K c) = algebraMap k K c)
    (hcomp : ∀ g y, rhoL g (algebraMap K L y) = algebraMap K L (rhoK g y))
    (hfixed : ∀ z : L, (∀ g, rhoL g z = z) → ∃ q : K, algebraMap K L q = z)
    (D0 : ι → equivariantDerivations rhoK hfix)
    (δ : ι → Derivation k L L)
    (hDcomp : ∀ i y, δ i (algebraMap K L y) = algebraMap K L ((D0 i).1 y))
    (hDcomm : ∀ i g y, δ i (rhoL g y) = rhoL g (δ i y))
    (hfixL : ∀ g c, rhoL g (algebraMap k L c) = algebraMap k L c)
    (a : G → Kˣ)
    (ha : ∀ g h, (a (g * h) : K) = rhoK g (a h : K) * (a g : K))
    (X : L) (hX : X ≠ 0)
    (hmul : ∀ g, rhoL g X = algebraMap K L (a g : K) * X)
    (c : ι → k) (hc : c ≠ 0)
    (hker : multiplierAtiyahClassMap rhoK hfix a ha (∑ i, c i • D0 i) = 0) :
    Projectivization.mk k c hc ∈
      projectiveDirectionalFiniteLawLocus (K := K) δ X 1 := by
  classical
  let D0c : equivariantDerivations rhoK hfix := ∑ i, c i • D0 i
  let D : Derivation k L L := directionalDerivation δ c
  have hD0c_apply (y : K) : D0c.1 y = ∑ i, c i • (D0 i).1 y := by
    change ((Finset.sum Finset.univ (fun i ↦ c i • D0 i) :
      equivariantDerivations rhoK hfix).1 y) = _
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        change (c i • (D0 i).1 + (Finset.sum s fun j ↦ c j • D0 j).1) y = _
        rw [Derivation.add_apply, Derivation.smul_apply, ih]
  have hDcompc : ∀ y, D (algebraMap K L y) = algebraMap K L (D0c.1 y) := by
    intro y
    simp only [D, directionalDerivation_apply, hD0c_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hDcomp i y]
    simp only [Algebra.smul_def]
    rw [map_mul, IsScalarTower.algebraMap_apply k K L]
  have hDcommc : ∀ g y, D (rhoL g y) = rhoL g (D y) := by
    intro g y
    simp only [D, directionalDerivation_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hDcomm i g y]
    simp only [Algebra.smul_def]
    rw [map_mul, hfixL]
  have hdep : ¬ AlgebraicIndependent K (fun j : Fin 2 ↦ ![X, D X] j) := by
    apply multiplierAtiyahClassMap_zero_not_algebraicIndependent_pair
      rhoK rhoL hfix hcomp hfixed D0c D hDcompc hDcommc a ha X hX hmul
    exact hker
  rw [mk_mem_projectiveDirectionalFiniteLawLocus_iff]
  change ¬ AlgebraicIndependent K
    (fun j : Fin 2 ↦ directionalJet δ c j X)
  have hfun : (fun j : Fin 2 ↦ directionalJet δ c j X) =
      (fun j : Fin 2 ↦ ![X, D X] j) := by
    funext j
    fin_cases j <;> simp [directionalJet, D]
  rw [hfun]
  exact hdep

end

end GaloisForLFunctions.HTGeometry
