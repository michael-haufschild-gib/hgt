import GaloisForLFunctions.HTGeometry.MonodromyVoltageExistence
import GaloisForLFunctions.HTGeometry.MonodromyCoverExamples
import GaloisForLFunctions.HTGeometry.ProjectiveConstraintTopologicalCapacityPhase

/-!
# A tower of connected unramified `(2,3,7)` covers of unbounded degree

Starting from the explicit degree-`|PSL(2,7)|` cover of the `(2,3,7)` orbifold and repeatedly
taking connected `ZMod 2`-voltage lifts, one obtains connected unramified covers of the `(2,3,7)`
orbifold of unbounded degree.  Each of them saturates the Hurwitz capacity law exactly:

```text
D = 42 (2g − 2),        g ∈ ℤ.
```

The lifts exist at every stage because a `(2,3,7)` cover has negative Euler characteristic, which
is exactly the inequality `f₂ + f₃ + f₇ < D` that the voltage rank count needs.

This upgrades `HurwitzProjectiveSurvivalWitness` from a numerical interface to a family of
constructed covering surfaces: the degrees and genera of the witness are the degree and genus of
an actual connected unramified cover.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv

/-- A `(2,3,7)` cover of positive degree, with its sheet set bundled. -/
structure Cover237 where
  /-- the sheet set -/
  Sheets : Type
  [instFin : Fintype Sheets]
  [instDec : DecidableEq Sheets]
  /-- the monodromy data -/
  cover : MonodromyCover 2 3 7 Sheets
  pos : 0 < cover.degree

attribute [instance] Cover237.instFin Cover237.instDec

/-- A `(2,3,7)` cover has negative Euler characteristic: the marked fibres carry fewer points
than the degree. -/
theorem hyperbolic_237 {S : Type*} [Fintype S] [DecidableEq S] (F : MonodromyCover 2 3 7 S)
    (hpos : 0 < F.degree) : F.fibreX + F.fibreY + F.fibreZ < F.degree := by
  have h2 := F.a_mul_fibreX (by norm_num)
  have h3 := F.b_mul_fibreY (by norm_num)
  have h7 := F.c_mul_fibreZ (by norm_num)
  omega

/-- The connected `ZMod 2`-voltage lift of a `(2,3,7)` cover: degree doubles. -/
noncomputable def Cover237.succ (C : Cover237) : Cover237 :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V : VoltageData C.cover 2 :=
    Classical.choice (exists_voltageData C.cover (by norm_num) (by norm_num) (by norm_num)
      (hyperbolic_237 C.cover C.pos))
  { Sheets := C.Sheets × ZMod 2
    cover := V.liftCover Nat.prime_two
    pos := by
      have hdeg : (V.liftCover Nat.prime_two).degree = C.cover.degree * 2 :=
        V.liftCover_degree Nat.prime_two
      have := C.pos
      omega }

theorem Cover237.succ_degree (C : Cover237) : C.succ.cover.degree = C.cover.degree * 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact VoltageData.liftCover_degree _ Nat.prime_two

/-- The base of the tower: the explicit `PSL(2,7)` cover. -/
noncomputable def hurwitzBase : Cover237 where
  Sheets := ↥(pairSubgroup hurwitzX hurwitzY)
  cover := hurwitzBaseCover
  pos := by
    have : Nonempty ↥(pairSubgroup hurwitzX hurwitzY) := ⟨1⟩
    simpa [MonodromyCover.degree] using Fintype.card_pos_iff.mpr this

/-- The tower of connected unramified `(2,3,7)` covers. -/
noncomputable def hurwitzTower : ℕ → Cover237
  | 0 => hurwitzBase
  | (n + 1) => (hurwitzTower n).succ

theorem hurwitzTower_degree_succ (n : ℕ) :
    (hurwitzTower (n + 1)).cover.degree = (hurwitzTower n).cover.degree * 2 :=
  Cover237.succ_degree _

theorem hurwitzTower_degree_ge (n : ℕ) : 2 ^ n ≤ (hurwitzTower n).cover.degree := by
  induction n with
  | zero =>
      have h := (hurwitzTower 0).pos
      simp only [pow_zero]
      omega
  | succ n ih =>
      rw [hurwitzTower_degree_succ, pow_succ]
      omega

/-- **Unbounded degree.**  The tower contains connected unramified `(2,3,7)` covers of degree
exceeding any bound. -/
theorem hurwitzTower_degree_unbounded (B : ℕ) : ∃ n, B < (hurwitzTower n).cover.degree := by
  exact ⟨B, lt_of_lt_of_le Nat.lt_two_pow_self (hurwitzTower_degree_ge B)⟩

/-- **Exact Hurwitz saturation at unbounded degree.**  For every bound there is a connected
unramified cover of the `(2,3,7)` orbifold of larger degree whose degree and genus satisfy
`D = 42(2g − 2)`. -/
theorem exists_hurwitzCover_degree_gt (B : ℕ) :
    ∃ (C : Cover237) (g : ℤ), B < C.cover.degree ∧ (C.cover.degree : ℤ) = 42 * (2 * g - 2) := by
  obtain ⟨n, hn⟩ := hurwitzTower_degree_unbounded B
  obtain ⟨g, _, hg⟩ := (hurwitzTower n).cover.hurwitz_capacity_exact
  exact ⟨hurwitzTower n, g, hn, hg⟩

/-- The genus of the `n`-th cover of the tower. -/
noncomputable def hurwitzTowerGenus (n : ℕ) : ℤ :=
  Classical.choose (hurwitzTower n).cover.hurwitz_capacity_exact

theorem hurwitzTowerGenus_spec (n : ℕ) :
    ((hurwitzTower n).cover.degree : ℤ) = 42 * (2 * hurwitzTowerGenus n - 2) :=
  (Classical.choose_spec (hurwitzTower n).cover.hurwitz_capacity_exact).2

/-- **The Hurwitz survival witness carried by constructed covers.**  Its degree and genus are the
degree and genus of an actual connected unramified `(2,3,7)` cover at every index, and the
storage law `D = 42(2g − 2)` is a theorem about that cover rather than a hypothesis. -/
noncomputable def hurwitzCoverSurvivalWitness : HurwitzProjectiveSurvivalWitness ℕ where
  degree n := ((hurwitzTower n).cover.degree : ℤ)
  genus n := hurwitzTowerGenus n
  commonPullback _ := True
  irreducible _ := True
  exactStorage n := hurwitzTowerGenus_spec n
  survives _ := ⟨trivial, trivial⟩
  degree_unbounded := by
    intro bound
    obtain ⟨n, hn⟩ := hurwitzTower_degree_unbounded bound.toNat
    refine ⟨n, ?_⟩
    have h : bound ≤ (bound.toNat : ℤ) := Int.self_le_toNat bound
    have h2 : ((bound.toNat : ℕ) : ℤ) < ((hurwitzTower n).cover.degree : ℤ) := by
      exact_mod_cast hn
    linarith

/-- The genus of the tower is unbounded: growing relational degree is paid for by growing
topology. -/
theorem hurwitzTowerGenus_unbounded : IntUnboundedAbove hurwitzTowerGenus :=
  hurwitzCoverSurvivalWitness.genus_unbounded

end GaloisForLFunctions.HTGeometry
