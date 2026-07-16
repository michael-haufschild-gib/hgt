import GaloisForLFunctions.HTGeometry.FreeHorizonMaximalCommutatorRank
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Canonical Heisenberg representation of a hypertranscendence horizon

A field derivation is already a linear operator on its field.  A field element is represented
faithfully by left multiplication.  Their operator commutator satisfies the exact Heisenberg
identity

`[D, M_f] = M_(D f)`.

Consequently every ordinary differential jet is the symbol of an iterated operator commutator,
and the complete differential-algebraicity horizon is recovered exactly from those Heisenberg
symbols.  The Lie bracket between law derivations is also preserved by the operator embedding.
This supplies an exact algebraic operator realization; no topology, star operation, state,
positivity, or locality is asserted.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
  [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V]

/-- Regard a field derivation as a linear operator on the underlying field. -/
def derivationEndomorphism :
    Derivation K L L →ₗ[K] Module.End K L where
  toFun D := D.toLinearMap
  map_add' D E := by
    ext z
    rfl
  map_smul' c D := by
    ext z
    rfl

theorem derivationEndomorphism_injective :
    Function.Injective (derivationEndomorphism (K := K) (L := L)) := by
  intro D E h
  ext z
  exact DFunLike.congr_fun h z

/-- The exact algebraic Heisenberg equation for a derivation and a multiplication observable. -/
theorem derivationEndomorphism_commutator_multiplication
    (D : Derivation K L L) (f : L) :
    ⁅derivationEndomorphism D, Algebra.lmul K L f⁆ =
      Algebra.lmul K L (D f) := by
  ext g
  simp only [Ring.lie_def, Module.End.sub_apply, Module.End.mul_apply,
    derivationEndomorphism, Algebra.coe_lmul_eq_mul, Function.comp_apply]
  rw [Derivation.leibniz]
  ring

/-- The operator embedding preserves the Lie bracket of derivation laws exactly. -/
theorem derivationEndomorphism_commutator
    (D E : Derivation K L L) :
    ⁅derivationEndomorphism D, derivationEndomorphism E⁆ =
      derivationEndomorphism ⁅D, E⁆ := by
  ext z
  rfl

/-- The `n`-fold Heisenberg commutator of `D` with the multiplication observable `M_x`. -/
def heisenbergJetOperator
    (D : Derivation K L L) (x : L) (n : ℕ) : Module.End K L :=
  ((fun T : Module.End K L ↦ ⁅derivationEndomorphism D, T⁆)^[n])
    (Algebra.lmul K L x)

/-- Iterated Heisenberg commutation is exactly multiplication by the ordinary differential jet. -/
theorem heisenbergJetOperator_eq_multiplication
    (D : Derivation K L L) (x : L) : ∀ n : ℕ,
    heisenbergJetOperator D x n =
      Algebra.lmul K L (((D : L → L)^[n]) x) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [heisenbergJetOperator, Function.iterate_succ_apply',
        ← heisenbergJetOperator, ih,
        derivationEndomorphism_commutator_multiplication]

/-- Evaluation at `1` recovers the faithful multiplication symbol of an operator. -/
def multiplicationOperatorSymbol : Module.End K L →ₗ[K] L where
  toFun T := T 1
  map_add' T S := by simp
  map_smul' c T := by simp

/-- The symbol of the `n`-fold Heisenberg response is the `n`-th ordinary differential jet. -/
theorem multiplicationOperatorSymbol_heisenbergJetOperator
    (D : Derivation K L L) (x : L) (n : ℕ) :
    multiplicationOperatorSymbol (heisenbergJetOperator D x n) =
      ((D : L → L)^[n]) x := by
  rw [heisenbergJetOperator_eq_multiplication]
  simp [multiplicationOperatorSymbol]

/-- The Heisenberg-symbol jet of one observable along one law direction. -/
def heisenbergDirectionalJetSymbol
    (ρ : V →ₗ[K] Derivation K L L) (x : L) (v : V) (n : ℕ) : L :=
  multiplicationOperatorSymbol (heisenbergJetOperator (ρ v) x n)

@[simp]
theorem heisenbergDirectionalJetSymbol_eq_linearDerivationLawJet
    (ρ : V →ₗ[K] Derivation K L L) (x : L) (v : V) (n : ℕ) :
    heisenbergDirectionalJetSymbol ρ x v n =
      linearDerivationLawJet ρ x v n := by
  exact multiplicationOperatorSymbol_heisenbergJetOperator (ρ v) x n

/-- **Heisenberg horizon theorem.**  The complete dependence horizon recovered from nested
operator-commutator symbols is exactly the original hypertranscendence horizon. -/
theorem heisenbergDependenceHorizon_eq
    [CharZero K] (ρ : V →ₗ[K] Derivation K L L) (x : L) :
    {v : V | ¬ AlgebraicIndependent K (heisenbergDirectionalJetSymbol ρ x v)} =
      linearDerivationDependenceHorizon ρ x := by
  ext v
  simp only [Set.mem_setOf_eq, linearDerivationDependenceHorizon,
    heisenbergDirectionalJetSymbol_eq_linearDerivationLawJet]

/-- The exterior commutator symbol after the faithful Heisenberg operator embedding. -/
def heisenbergLawCommutatorMap
    (ρ : V →ₗ[K] Derivation K L L) :
    (⋀[K]^2 V) →ₗ[K] Module.End K L :=
  (derivationEndomorphism (K := K) (L := L)).comp
    (derivationCommutatorMap ρ)

@[simp]
theorem heisenbergLawCommutatorMap_wedge
    (ρ : V →ₗ[K] Derivation K L L) (v w : V) :
    heisenbergLawCommutatorMap ρ (exteriorPower.ιMulti K 2 ![v, w]) =
      ⁅derivationEndomorphism (ρ v), derivationEndomorphism (ρ w)⁆ := by
  rw [heisenbergLawCommutatorMap, LinearMap.comp_apply,
    derivationCommutatorMap_wedge, derivationEndomorphism_commutator]

/-- Faithful passage to the Heisenberg operator algebra loses no commutator-symbol rank. -/
theorem heisenbergLawCommutatorMap_injective_iff
    (ρ : V →ₗ[K] Derivation K L L) :
    Function.Injective (heisenbergLawCommutatorMap ρ) ↔
      Function.Injective (derivationCommutatorMap ρ) := by
  constructor
  · intro h z z' hzz
    apply h
    simp [heisenbergLawCommutatorMap, hzz]
  · intro h
    exact (derivationEndomorphism_injective (K := K) (L := L)).comp h

end

end GaloisForLFunctions.HTGeometry
