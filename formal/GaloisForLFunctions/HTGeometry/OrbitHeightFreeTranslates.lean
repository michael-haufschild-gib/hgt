import GaloisForLFunctions.HTGeometry.DifferentialMatroidGluing
import GaloisForLFunctions.HTGeometry.MeromorphicThetaDefect
import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary

/-!
# Orbit-height realization of free translates

The simplicial-star gluing engine needs, for each direction, arbitrarily many pairwise disjoint
translates of every finite block of a packet.  Its integer-height criterion asks for a `ℤ`-valued
height that increases by `n` under the `n`-th power of the direction.  This file supplies that
height whenever the packet is a union of *full* orbits whose exponent is recoverable — that is,
whenever distinct exponents give distinct elements.

* `orbitUnion` — the union of the full `σ`-orbits of a base set;
* **`hasFreeTranslates_orbitUnion`** — an injectively exponentiated orbit union has free
  translates;
* **`hasFreeTranslates_orbit_of_aperiodic`** — the single-orbit criterion: no nonzero power of the
  direction fixes the base point.  This is the shape the structural translates of a special
  function satisfy, where aperiodicity is exactly nonresonance of the shift.
-/

open Set

namespace GaloisForLFunctions.MatroidGluing

open Rank

variable {Ω : Type*} [DecidableEq Ω]

/-- The union of the full `σ`-orbits of a base set. -/
def orbitUnion (σ : Equiv.Perm Ω) (base : Set Ω) : Set Ω :=
  {x | ∃ (n : ℤ) (y : Ω), y ∈ base ∧ x = (σ ^ n) y}

omit [DecidableEq Ω] in
theorem mem_orbitUnion_iff (σ : Equiv.Perm Ω) (base : Set Ω) (x : Ω) :
    x ∈ orbitUnion σ base ↔ ∃ (n : ℤ) (y : Ω), y ∈ base ∧ x = (σ ^ n) y := Iff.rfl

omit [DecidableEq Ω] in
theorem subset_orbitUnion (σ : Equiv.Perm Ω) (base : Set Ω) : base ⊆ orbitUnion σ base := by
  intro y hy
  exact ⟨0, y, hy, by simp⟩

omit [DecidableEq Ω] in
theorem zpow_apply_zpow_apply (σ : Equiv.Perm Ω) (m n : ℤ) (y : Ω) :
    (σ ^ n) ((σ ^ m) y) = (σ ^ (n + m)) y := by
  rw [zpow_add]
  rfl

/-- **Orbit-height realization.**  If distinct exponents give distinct elements, the union of the
full orbits of a base set has free translates in every direction power. -/
theorem hasFreeTranslates_orbitUnion (σ : Equiv.Perm Ω) (base : Set Ω)
    (hinj : ∀ (m n : ℤ) (y z : Ω), y ∈ base → z ∈ base → (σ ^ m) y = (σ ^ n) z → m = n) :
    HasFreeTranslates σ (orbitUnion σ base) := by
  classical
  set height : Ω → ℤ := fun x =>
    if h : ∃ p : ℤ × Ω, p.2 ∈ base ∧ x = (σ ^ p.1) p.2 then h.choose.1 else 0 with hheightdef
  have hheight_eq : ∀ (x : Ω) (n : ℤ) (y : Ω), y ∈ base → x = (σ ^ n) y → height x = n := by
    intro x n y hy hxy
    have hex : ∃ p : ℤ × Ω, p.2 ∈ base ∧ x = (σ ^ p.1) p.2 := ⟨(n, y), hy, hxy⟩
    rw [hheightdef]
    simp only [dif_pos hex]
    obtain ⟨hbase, hval⟩ := hex.choose_spec
    exact hinj hex.choose.1 n hex.choose.2 y hbase hy (hval.symm.trans hxy)
  refine hasFreeTranslates_of_intHeight σ (orbitUnion σ base) height ?_ ?_
  · rintro x ⟨m, y, hy, rfl⟩ n
    exact ⟨n + m, y, hy, zpow_apply_zpow_apply σ m n y⟩
  · rintro x ⟨m, y, hy, rfl⟩ n
    rw [zpow_apply_zpow_apply σ m n y,
      hheight_eq ((σ ^ (n + m)) y) (n + m) y hy rfl,
      hheight_eq ((σ ^ m) y) m y hy rfl]
    ring

/-- **Single-orbit criterion.**  A base point no nonzero power of the direction fixes generates an
orbit with free translates. -/
theorem hasFreeTranslates_orbit_of_aperiodic (σ : Equiv.Perm Ω) (y : Ω)
    (hy : ∀ n : ℤ, n ≠ 0 → (σ ^ n) y ≠ y) :
    HasFreeTranslates σ (orbitUnion σ ({y} : Set Ω)) := by
  refine hasFreeTranslates_orbitUnion σ ({y} : Set Ω) ?_
  rintro m n u v hu hv huv
  rw [Set.mem_singleton_iff] at hu hv
  rw [hu, hv] at huv
  by_contra hmn
  have hsub : (σ ^ (m - n)) y = y := by
    have hexp : m - n = -n + m := by ring
    have h1 : (σ ^ (m - n)) y = (σ ^ (-n)) ((σ ^ m) y) := by
      rw [zpow_apply_zpow_apply σ m (-n) y, hexp]
    rw [h1, huv, zpow_apply_zpow_apply σ n (-n) y]
    simp
  exact hy (m - n) (sub_ne_zero.mpr hmn) hsub

omit [DecidableEq Ω] in
/-- A finite union of orbit unions is an orbit union of the union of the bases. -/
theorem orbitUnion_union (σ : Equiv.Perm Ω) (base₁ base₂ : Set Ω) :
    orbitUnion σ (base₁ ∪ base₂) = orbitUnion σ base₁ ∪ orbitUnion σ base₂ := by
  ext x
  constructor
  · rintro ⟨n, y, hy | hy, rfl⟩
    · exact Or.inl ⟨n, y, hy, rfl⟩
    · exact Or.inr ⟨n, y, hy, rfl⟩
  · rintro (⟨n, y, hy, rfl⟩ | ⟨n, y, hy, rfl⟩)
    · exact ⟨n, y, Or.inl hy, rfl⟩
    · exact ⟨n, y, Or.inr hy, rfl⟩

/-! ## The additive translations of the global meromorphic field as directions -/

namespace Meromorphic

open GaloisForLFunctions Bottcher

noncomputable local instance meroFieldDecidableEq :
    DecidableEq (meroField (Set.univ : Set ℂ)) := Classical.decEq _

/-- Additive translation of global meromorphic germs, as a permutation. -/
noncomputable def meroTranslationPerm (q : ℂ) :
    Equiv.Perm (meroField (Set.univ : Set ℂ)) :=
  (addTranslationMeroEquiv q).toEquiv

@[simp]
theorem meroTranslationPerm_apply (q : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    meroTranslationPerm q x = addTranslationMeroEquiv q x := rfl

theorem meroTranslationPerm_symm_apply (q : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    (meroTranslationPerm q).symm x = addTranslationMeroEquiv (-q) x := by
  apply (addTranslationMeroEquiv q).injective
  rw [show addTranslationMeroEquiv q ((meroTranslationPerm q).symm x) =
      meroTranslationPerm q ((meroTranslationPerm q).symm x) from rfl,
    Equiv.apply_symm_apply, addTranslationMeroEquiv_add, add_neg_cancel,
    addTranslationMeroEquiv_zero_apply]

theorem meroTranslationPerm_pow_apply (q : ℂ) (k : ℕ) (x : meroField (Set.univ : Set ℂ)) :
    (meroTranslationPerm q ^ k) x = addTranslationMeroEquiv ((k : ℂ) * q) x := by
  induction k generalizing x with
  | zero => simpa using (addTranslationMeroEquiv_zero_apply x).symm
  | succ k ih =>
      have hcast : ((k : ℂ) * q + q) = ((k + 1 : ℕ) : ℂ) * q := by push_cast; ring
      rw [pow_succ, Equiv.Perm.mul_apply, ih, meroTranslationPerm_apply,
        addTranslationMeroEquiv_add, hcast]

theorem meroTranslationPerm_zpow_apply (q : ℂ) (n : ℤ) (x : meroField (Set.univ : Set ℂ)) :
    (meroTranslationPerm q ^ n) x = addTranslationMeroEquiv ((n : ℂ) * q) x := by
  induction n using Int.induction_on generalizing x with
  | zero => simpa using (addTranslationMeroEquiv_zero_apply x).symm
  | succ k ih =>
      have hcast : (((k : ℤ) : ℂ) * q + q) = (((k : ℤ) + 1 : ℤ) : ℂ) * q := by push_cast; ring
      rw [zpow_add_one, Equiv.Perm.mul_apply, ih, meroTranslationPerm_apply,
        addTranslationMeroEquiv_add, hcast]
  | pred k ih =>
      have hcast : ((-(k : ℤ) : ℤ) : ℂ) * q + -q = (((-(k : ℤ) - 1 : ℤ)) : ℂ) * q := by
        push_cast; ring
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
      rw [show ((meroTranslationPerm q)⁻¹ : Equiv.Perm (meroField (Set.univ : Set ℂ))) =
        (meroTranslationPerm q).symm from rfl, meroTranslationPerm_symm_apply,
        addTranslationMeroEquiv_add, hcast]

/-- **Aperiodic structural translates have free translates.**  If no nonzero integer multiple of
the shift `q` fixes the germ `x`, the full translation orbit of `x` supplies arbitrarily many
disjoint translates of every finite block. -/
theorem hasFreeTranslates_meroOrbit_of_aperiodic (q : ℂ)
    (x : meroField (Set.univ : Set ℂ))
    (hx : ∀ n : ℤ, n ≠ 0 → addTranslationMeroEquiv ((n : ℂ) * q) x ≠ x) :
    Rank.HasFreeTranslates (meroTranslationPerm q)
      (orbitUnion (meroTranslationPerm q) ({x} : Set (meroField (Set.univ : Set ℂ)))) := by
  classical
  refine hasFreeTranslates_orbit_of_aperiodic _ _ ?_
  intro n hn
  rw [meroTranslationPerm_zpow_apply]
  exact hx n hn

end Meromorphic

end GaloisForLFunctions.MatroidGluing
