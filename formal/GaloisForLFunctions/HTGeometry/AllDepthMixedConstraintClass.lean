import GaloisForLFunctions.HTGeometry.TripticGermConstraint

/-!
# The all-depth mixed-constraint class

The depth-two class of the corpus is `PeriodicOneGerm F` together with `MixedConstGerm F τ σ Cst`.
The all-depth class `Q_d` of the pair-face signature theorem replaces the two-fold mixed difference
by the `d`-fold one.  This file introduces the finite difference cube

```text
diffCube τ s F z = ∑_(E ⊆ s) (-1)^(|s| - |E|) F (z + ∑_(i ∈ E) τ i),
```

which is the composite of the commuting one-step differences `Δ_(τ i)`, `i ∈ s`, written in a
manifestly symmetric closed form, and the class

```text
MixedConstGermSet τ s F Cst  :  diffCube τ s F = Cst  as an identity of meromorphic germs.
```

* `diffCube_empty`, **`diffCube_insert`** — the cube is the iterated one-step difference;
* `diffCube_pair` — at a pair it is the corpus's mixed difference;
* **`mixedConstGermSet_pair_iff`** — hence the depth-two class is the corpus's triptic class;
* `MixedConstGermSet.shiftDiff` — a one-step difference lowers the depth by one.
-/

open Filter Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The one-step difference operator on functions. -/
def shiftDiffFun (h : ℂ) (F : ℂ → ℂ) : ℂ → ℂ := fun z => F (z + h) - F z

/-- The `s`-fold difference cube of `F` along the parameters `τ`. -/
def diffCube (τ : ι → ℂ) (s : Finset ι) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ E ∈ s.powerset, (-1 : ℂ) ^ (s.card - E.card) * F (z + ∑ i ∈ E, τ i)

omit [DecidableEq ι] in
@[simp] theorem diffCube_empty (τ : ι → ℂ) (F : ℂ → ℂ) :
    diffCube τ (∅ : Finset ι) F = F := by
  funext z
  simp [diffCube]

/-- **The cube is the iterated one-step difference.** -/
theorem diffCube_insert (τ : ι → ℂ) {s : Finset ι} {q : ι} (hq : q ∉ s) (F : ℂ → ℂ) :
    diffCube τ (insert q s) F = shiftDiffFun (τ q) (diffCube τ s F) := by
  classical
  funext z
  rw [shiftDiffFun, diffCube, diffCube, diffCube,
    Finset.powerset_insert, Finset.sum_union, Finset.sum_image]
  · have hcard : (insert q s).card = s.card + 1 := Finset.card_insert_of_notMem hq
    have hleft : ∑ E ∈ s.powerset,
        (-1 : ℂ) ^ ((insert q s).card - E.card) * F (z + ∑ i ∈ E, τ i) =
        -∑ E ∈ s.powerset, (-1 : ℂ) ^ (s.card - E.card) * F (z + ∑ i ∈ E, τ i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun E hE => ?_
      have hEs : E.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hE)
      rw [hcard]
      have : s.card + 1 - E.card = (s.card - E.card) + 1 := by omega
      rw [this, pow_succ]
      ring
    have hright : ∑ E ∈ s.powerset,
        (-1 : ℂ) ^ ((insert q s).card - (insert q E).card) *
          F (z + ∑ i ∈ insert q E, τ i) =
        ∑ E ∈ s.powerset, (-1 : ℂ) ^ (s.card - E.card) * F (z + τ q + ∑ i ∈ E, τ i) := by
      refine Finset.sum_congr rfl fun E hE => ?_
      have hEsub : E ⊆ s := Finset.mem_powerset.mp hE
      have hqE : q ∉ E := fun h => hq (hEsub h)
      rw [Finset.card_insert_of_notMem hqE, hcard, Finset.sum_insert hqE]
      have harg : z + (τ q + ∑ i ∈ E, τ i) = z + τ q + ∑ i ∈ E, τ i := by ring
      rw [harg]
      congr 2
      omega
    rw [hleft, hright]
    ring
  · intro E hE E' hE' hEE'
    have hqE : q ∉ E := fun h => hq (Finset.mem_powerset.mp hE h)
    have hqE' : q ∉ E' := fun h => hq (Finset.mem_powerset.mp hE' h)
    have h1 : (insert q E).erase q = E := Finset.erase_insert hqE
    have h2 : (insert q E').erase q = E' := Finset.erase_insert hqE'
    rw [← h1, hEE', h2]
  · rw [Finset.disjoint_right]
    intro E hE hEs
    obtain ⟨E', -, rfl⟩ := Finset.mem_image.mp hE
    exact hq (Finset.mem_powerset.mp hEs (Finset.mem_insert_self q E'))

theorem diffCube_singleton (τ : ι → ℂ) (q : ι) (F : ℂ → ℂ) :
    diffCube τ ({q} : Finset ι) F = shiftDiffFun (τ q) F := by
  have h := diffCube_insert τ (s := (∅ : Finset ι)) (q := q) (by simp) F
  simpa using h

theorem diffCube_pair (τ : ι → ℂ) {i j : ι} (hij : i ≠ j) (F : ℂ → ℂ) (z : ℂ) :
    diffCube τ ({i, j} : Finset ι) F z =
      F (z + τ j + τ i) - F (z + τ j) - F (z + τ i) + F z := by
  classical
  have hi : i ∉ ({j} : Finset ι) := by simpa using hij
  rw [show ({i, j} : Finset ι) = insert i {j} from rfl,
    diffCube_insert τ hi F, diffCube_singleton]
  simp only [shiftDiffFun]
  ring

/-- `Δ_s F = Cst` as an identity of meromorphic germs. -/
def MixedConstGermSet (τ : ι → ℂ) (s : Finset ι) (F : ℂ → ℂ) (Cst : ℂ) : Prop :=
  ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, diffCube τ s F w = Cst

omit [DecidableEq ι] in
theorem mixedConstGermSet_of_forall {τ : ι → ℂ} {s : Finset ι} {F : ℂ → ℂ} {Cst : ℂ}
    (h : ∀ z : ℂ, diffCube τ s F z = Cst) : MixedConstGermSet τ s F Cst :=
  fun _ => Filter.Eventually.of_forall fun w => h w

/-- **At a pair the all-depth class is the corpus's triptic class.** -/
theorem mixedConstGermSet_pair_iff {τ : ι → ℂ} {i j : ι} (hij : i ≠ j)
    {F : ℂ → ℂ} {Cst : ℂ} :
    MixedConstGermSet τ ({i, j} : Finset ι) F Cst ↔ MixedConstGerm F (τ j) (τ i) Cst := by
  constructor
  · intro h z
    filter_upwards [h z] with w hw
    rw [diffCube_pair τ hij F w] at hw
    exact hw
  · intro h z
    filter_upwards [h z] with w hw
    rw [diffCube_pair τ hij F w]
    exact hw

/-- A one-step difference lowers the depth by one. -/
theorem MixedConstGermSet.shiftDiff {τ : ι → ℂ} {s : Finset ι} {q : ι} (hq : q ∉ s)
    {F : ℂ → ℂ} {Cst : ℂ} (h : MixedConstGermSet τ (insert q s) F Cst) :
    MixedConstGermSet τ s (shiftDiffFun (τ q) F) Cst := by
  intro z
  filter_upwards [h z] with w hw
  rw [diffCube_insert τ hq F] at hw
  have hcomm : diffCube τ s (shiftDiffFun (τ q) F) w =
      shiftDiffFun (τ q) (diffCube τ s F) w := by
    simp only [diffCube, shiftDiffFun, Finset.sum_sub_distrib, mul_sub]
    refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun E _ => ?_) rfl
    have harg : w + ∑ i ∈ E, τ i + τ q = w + τ q + ∑ i ∈ E, τ i := by ring
    rw [harg]
  rw [hcomm]
  exact hw

omit [DecidableEq ι] in
/-- The cube is additive in its source. -/
theorem diffCube_add (τ : ι → ℂ) (s : Finset ι) (F G : ℂ → ℂ) :
    diffCube τ s (F + G) = diffCube τ s F + diffCube τ s G := by
  funext z
  simp only [diffCube, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun E _ => by ring

omit [DecidableEq ι] in
/-- The cube commutes with a one-step difference. -/
theorem diffCube_shiftDiffFun_comm (τ : ι → ℂ) (s : Finset ι) (h : ℂ) (F : ℂ → ℂ) :
    diffCube τ s (shiftDiffFun h F) = shiftDiffFun h (diffCube τ s F) := by
  funext w
  simp only [diffCube, shiftDiffFun, Finset.sum_sub_distrib, mul_sub]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun E _ => ?_) rfl
  have harg : w + ∑ i ∈ E, τ i + h = w + h + ∑ i ∈ E, τ i := by ring
  rw [harg]

/-- **The cube of a disjoint union is the composite of the two cubes.** -/
theorem diffCube_union (τ : ι → ℂ) {s t : Finset ι} (hd : Disjoint s t) (F : ℂ → ℂ) :
    diffCube τ (s ∪ t) F = diffCube τ s (diffCube τ t F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert q s hq ih =>
      have hqt : q ∉ t := by
        intro hqt
        exact (Finset.disjoint_left.mp hd (Finset.mem_insert_self q s)) hqt
      have hst : Disjoint s t := hd.mono_left (Finset.subset_insert q s)
      have hunion : insert q s ∪ t = insert q (s ∪ t) := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      have hqst : q ∉ s ∪ t := by
        simp only [Finset.mem_union]
        tauto
      rw [hunion, diffCube_insert τ hqst F, ih hst, diffCube_insert τ hq (diffCube τ t F)]

end

end GaloisForLFunctions.HTGeometry
