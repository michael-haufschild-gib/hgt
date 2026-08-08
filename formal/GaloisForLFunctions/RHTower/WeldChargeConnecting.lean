/-
# The connecting homomorphism from the weld cohomology to the deck-charge group

The `𝓜⁺` weld obstruction lives in `secondConstraintCohomology (G,A) = H²(G,A)` (a 2-cocycle modulo
gauge, `OmegaObstruction`); the deck / ladder charge lives in `ZMod n` (`wCharge`, `DeckChargeCalculus`).
`OmegaObstruction` supplies a coboundary-annihilating chain and a one-directional detection lemma
(nonzero pairing ⟹ nonzero class) but never packages the pairing as a homomorphism.  This file builds
that map.

* `connectingHom T : H²(G,A) →+ A` — **the connecting homomorphism** `δ`: a coboundary-annihilating
  chain `T` evaluates cohomology classes, and the evaluation descends (via `QuotientAddGroup.lift`) to a
  genuine additive group homomorphism out of `H²`.  It detects the obstruction: `δ(class) ≠ 0 ⟹ class ≠ 0`.
* `chargeConnectingHom T n : H²(G,ℤ) →+ ZMod n` — the composite with reduction `ℤ ↠ ℤ/n`, whose value on
  every class is a deck charge: `δ_charge(obstructionClass ω) = wCharge n (T.eval ω)`.
* `exists_weldClass_chargeConnectingHom_eq` — **the realization**: for every modulus `n` and every index
  `idx`, the deck charge `wCharge n idx` is the value of the connecting map on an *explicit* weld
  cohomology class (the symplectic 2-cocycle scaled by `idx`).  The entire deck-charge calculus lies in
  the image of `δ`; the weld obstruction and the charge are two faces of one cocycle-evaluation map.

This realizes the map `δ` as a homomorphism and identifies its target group and formula with the deck
charge.  It does **not** assert that a *specific* `𝓜⁺` weld class equals `ξ`'s ladder charge — those two
apex obstructions are independent (`ω = 0` does not force RH).  The shared object is the *framework*
(evaluation charges), not the individual class.
-/
import GaloisForLFunctions.HTGeometry.OmegaObstruction
import GaloisForLFunctions.RHTower.DeckChargeCalculus

open scoped BigOperators

namespace GaloisForLFunctions
namespace RHTower

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-! ### The cocycle-evaluation homomorphism and the connecting map -/

omit [Group G] [DistribMulAction G A] in
/-- The chain pairing is additive in the cochain. -/
theorem twoChainEval_add (chain : G × G →₀ ℤ) (ω η : G → G → A) :
    twoChainEval chain (ω + η) = twoChainEval chain ω + twoChainEval chain η := by
  simp only [twoChainEval, Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun gh _ => by simp only [Pi.add_apply, smul_add])

omit [Group G] [DistribMulAction G A] in
/-- The chain pairing kills the zero cochain. -/
theorem twoChainEval_zero (chain : G × G →₀ ℤ) :
    twoChainEval chain (0 : G → G → A) = 0 := by
  simp only [twoChainEval, Finsupp.sum, Pi.zero_apply, smul_zero, Finset.sum_const_zero]

/-- The cocycle-evaluation homomorphism `twoCocycles →+ A` for a fixed test chain. -/
def evalCocycleHom (chain : G × G →₀ ℤ) : twoCocycles (G := G) (A := A) →+ A where
  toFun omega := twoChainEval chain omega.val
  map_zero' := twoChainEval_zero chain
  map_add' x y := twoChainEval_add chain x.val y.val

/-- **The connecting homomorphism `δ : H²(G,A) →+ A`.**  A coboundary-annihilating chain `T` evaluates
cohomology classes; because it kills coboundaries the evaluation descends to a genuine additive group
homomorphism out of the second constraint cohomology. -/
def connectingHom (T : TwoCoboundaryAnnihilator G A) :
    secondConstraintCohomology (G := G) (A := A) →+ A :=
  QuotientAddGroup.lift _ (evalCocycleHom T.chain) (by
    rintro _ ⟨b, rfl⟩; exact T.kills_coboundaries b)

@[simp] theorem connectingHom_obstructionClass (T : TwoCoboundaryAnnihilator G A)
    (omega : twoCocycles (G := G) (A := A)) :
    connectingHom T (obstructionClass omega) = T.eval omega := rfl

/-- **The connecting map detects the obstruction.**  If `δ` is nonzero on a class, the class is
nonzero (a homomorphism sends `0` to `0`). -/
theorem obstructionClass_ne_zero_of_connectingHom_ne_zero (T : TwoCoboundaryAnnihilator G A)
    {c : secondConstraintCohomology (G := G) (A := A)} (h : connectingHom T c ≠ 0) : c ≠ 0 := by
  intro hc; exact h (by rw [hc, map_zero])

/-- On a commuting pair (trivial action) the connecting map returns the antisymmetry `ω g h − ω h g`,
the detector of `obstructionClassOf_ne_zero_of_commutingPair_asymm`. -/
theorem connectingHom_commutingPair (htriv : ∀ (g : G) (a : A), g • a = a) {g h : G}
    (hcomm : g * h = h * g) (omega : twoCocycles (G := G) (A := A)) :
    connectingHom (commutingPairAnnihilator htriv hcomm) (obstructionClass omega)
      = omega.val g h - omega.val h g := by
  rw [connectingHom_obstructionClass]
  simp only [TwoCoboundaryAnnihilator.eval, commutingPairAnnihilator,
    twoChainEval_commutingPairChain]

end RHTower
end GaloisForLFunctions

/-! ### The charge specialization: `δ` into the deck-charge group `ℤ/n`, and its realization -/

namespace GaloisForLFunctions
namespace RHTower

variable {G : Type*} [Group G] [DistribMulAction G ℤ]

/-- **The charge connecting map `δ_charge : H²(G,ℤ) →+ ℤ/n`.**  The connecting homomorphism composed
with the reduction `ℤ ↠ ℤ/n`: it lands in the deck-charge group. -/
def chargeConnectingHom (T : TwoCoboundaryAnnihilator G ℤ) (n : ℕ) :
    secondConstraintCohomology (G := G) (A := ℤ) →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp (connectingHom T)

/-- **The connecting map's value is a deck charge.**  On every weld cohomology class, `δ_charge`
returns the deck charge `wCharge n` of the class's chain evaluation: the charge calculus is the target
of the connecting map. -/
@[simp] theorem chargeConnectingHom_obstructionClass (T : TwoCoboundaryAnnihilator G ℤ) (n : ℕ)
    (omega : twoCocycles (G := G) (A := ℤ)) :
    chargeConnectingHom T n (obstructionClass omega) = _root_.RHTower.wCharge n (T.eval omega) := rfl

end RHTower
end GaloisForLFunctions

/-! ### The symplectic weld cocycle: every deck charge is realized by `δ` -/

namespace GaloisForLFunctions
namespace RHTower

/-- The trivial action of a group on `ℤ` (the deck cocycle carries no coefficient twist). -/
instance (priority := 100) trivActionMulZZ : DistribMulAction (Multiplicative (ℤ × ℤ)) ℤ where
  smul := fun _ n => n
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

/-- The symplectic 2-cocycle on `ℤ²` scaled by `idx`: `ω(g,h) = idx · g₁ · h₂`.  Its antisymmetry on
the standard commuting generators is exactly `idx`. -/
def sympCocycleFun (idx : ℤ) :
    Multiplicative (ℤ × ℤ) → Multiplicative (ℤ × ℤ) → ℤ :=
  fun g h => idx * (Multiplicative.toAdd g).1 * (Multiplicative.toAdd h).2

theorem sympCocycle_isTwoCocycle (idx : ℤ) : IsTwoCocycle (sympCocycleFun idx) := by
  intro g h k
  have hsmul : ∀ (x : Multiplicative (ℤ × ℤ)) (m : ℤ), x • m = m := fun _ _ => rfl
  simp only [sympCocycleFun, hsmul, toAdd_mul, Prod.fst_add, Prod.snd_add]
  ring

/-- **Realization: every deck charge is a value of the connecting map.**  For every modulus `n` and
index `idx`, the deck charge `wCharge n idx` equals `δ_charge` evaluated on the explicit weld class of
the symplectic cocycle scaled by `idx`.  So the whole deck-charge calculus lies in the image of the
connecting homomorphism — the weld obstruction and the charge are two faces of one cocycle-evaluation
map. -/
theorem exists_weldClass_chargeConnectingHom_eq (n : ℕ) (idx : ℤ) :
    ∃ (T : TwoCoboundaryAnnihilator (Multiplicative (ℤ × ℤ)) ℤ)
      (omega : twoCocycles (G := Multiplicative (ℤ × ℤ)) (A := ℤ)),
      chargeConnectingHom T n (obstructionClass omega) = _root_.RHTower.wCharge n idx := by
  set g : Multiplicative (ℤ × ℤ) := Multiplicative.ofAdd (1, 0) with hg
  set h : Multiplicative (ℤ × ℤ) := Multiplicative.ofAdd (0, 1) with hh
  have htriv : ∀ (x : Multiplicative (ℤ × ℤ)) (a : ℤ), x • a = a := fun _ _ => rfl
  have hcomm : g * h = h * g := mul_comm g h
  refine ⟨commutingPairAnnihilator htriv hcomm,
    cocycleOf (sympCocycleFun idx) (sympCocycle_isTwoCocycle idx), ?_⟩
  rw [chargeConnectingHom_obstructionClass]
  have heval : (commutingPairAnnihilator htriv hcomm).eval (sympCocycleFun idx) = idx := by
    simp only [TwoCoboundaryAnnihilator.eval, commutingPairAnnihilator,
      twoChainEval_commutingPairChain, sympCocycleFun, hg, hh, toAdd_ofAdd]
    ring
  rw [show (commutingPairAnnihilator htriv hcomm).eval
      (cocycleOf (sympCocycleFun idx) (sympCocycle_isTwoCocycle idx)).val = idx from heval]

end RHTower
end GaloisForLFunctions
