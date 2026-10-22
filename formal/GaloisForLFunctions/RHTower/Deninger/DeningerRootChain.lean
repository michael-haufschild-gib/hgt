import GaloisForLFunctions.RHTower.Deninger.DeningerUnionCyclic

/-!
# The chain of iterated roots

Iterating the root operation on a single element gives an increasing chain of cyclic subgroups of
the rationalization: each element of the chain is a power of the next.

* `deningerRootChain` : the chain.
* `deningerRootChain_zpowers_mono` : the cyclic subgroups increase.
* `deningerRootChain_exists_pow` : every earlier element is a power of every later one.
* `deningerRootChain_exists_pow_dvd` : the exponent can be taken divisible by any prescribed number.
* `deningerRootChain_root_mem` : the union of the chain's cyclic subgroups is closed under the roots.
* `deningerRootChain_iSup_eq_top` : for a cyclic group the union is the whole rationalization.
* `deningerRootChain_zpowers_equiv` : each subgroup of the chain is infinite cyclic.
-/

namespace RHTower

universe u

variable {α : Type u} [Group α]

/-- The chain of iterated roots of an element. -/
noncomputable def deningerRootChain (g : α) : ℕ → DeningerBau α
  | 0 => DeningerBau.of g
  | m + 1 => DeningerBau.root m (deningerRootChain g m)

@[simp] theorem deningerRootChain_zero (g : α) :
    deningerRootChain g 0 = DeningerBau.of g := rfl

theorem deningerRootChain_pow (g : α) (m : ℕ) :
    (deningerRootChain g (m + 1)) ^ (m + 1) = deningerRootChain g m :=
  DeningerBau.root_pow m _

/-- **The cyclic subgroups of the chain increase.** -/
theorem deningerRootChain_zpowers_mono (g : α) :
    Monotone (fun m => Subgroup.zpowers (deningerRootChain g m)) := by
  refine monotone_nat_of_le_succ (fun m => ?_)
  rw [Subgroup.zpowers_le]
  refine ⟨((m + 1 : ℕ) : ℤ), ?_⟩
  show (deningerRootChain g (m + 1)) ^ ((m + 1 : ℕ) : ℤ) = deningerRootChain g m
  rw [zpow_natCast]
  exact deningerRootChain_pow g m

/-- **Every earlier element of the chain is a positive power of every later one.** -/
theorem deningerRootChain_exists_pow (g : α) (m : ℕ) :
    ∀ j : ℕ, m ≤ j → ∃ c : ℕ, 0 < c ∧ (deningerRootChain g j) ^ c = deningerRootChain g m := by
  intro j
  induction j with
  | zero =>
    intro h
    obtain rfl : m = 0 := by omega
    exact ⟨1, by omega, pow_one _⟩
  | succ j ih =>
    intro h
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact ⟨1, by omega, pow_one _⟩
    · obtain ⟨c, hc, hcp⟩ := ih (by omega)
      refine ⟨(j + 1) * c, by positivity, ?_⟩
      rw [pow_mul, deningerRootChain_pow, hcp]

/-- **The exponent can be taken divisible by any prescribed number**, by moving far enough along the
chain that a multiple of that number occurs among the accumulated factors. -/
theorem deningerRootChain_exists_pow_dvd (g : α) (m d : ℕ) (hd : 0 < d) :
    ∃ j c : ℕ, m ≤ j ∧ 0 < c ∧ d ∣ c ∧
      (deningerRootChain g j) ^ c = deningerRootChain g m := by
  set j₀ := (m / d + 1) * d with hj₀
  have hlt : m < j₀ := by
    rw [hj₀]
    have h2 := Nat.mod_lt m hd
    nlinarith [Nat.div_add_mod m d]
  have hdvd : d ∣ j₀ := ⟨m / d + 1, by rw [hj₀]; ring⟩
  obtain ⟨c₁, hc₁, hc₁p⟩ := deningerRootChain_exists_pow g m (j₀ - 1) (by omega)
  refine ⟨j₀, j₀ * c₁, by omega, by positivity, Dvd.dvd.mul_right hdvd _, ?_⟩
  rw [pow_mul]
  have hstep : (deningerRootChain g j₀) ^ j₀ = deningerRootChain g (j₀ - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, j₀ = t + 1 := ⟨j₀ - 1, by omega⟩
    rw [ht]
    simpa using deningerRootChain_pow g t
  rw [hstep, hc₁p]

/-- **The union of the chain's cyclic subgroups is closed under the roots.**  A root of a power of
one element of the chain is a power of a later element: move far enough that the order divides the
exponent, and the candidate root is identified by uniqueness of roots. -/
theorem deningerRootChain_root_mem (g : α) (n m : ℕ) (k : ℤ) :
    ∃ j : ℕ, m ≤ j ∧ DeningerBau.root n ((deningerRootChain g m) ^ k) ∈
      Subgroup.zpowers (deningerRootChain g j) := by
  obtain ⟨j, c, hmj, hc, hdvd, hpow⟩ := deningerRootChain_exists_pow_dvd g m (n + 1) (by omega)
  obtain ⟨e, he⟩ := hdvd
  refine ⟨j, hmj, (e : ℤ) * k, ?_⟩
  refine deningerPow_injective_of_uniquelyDivisible DeningerBau.uniquelyDivisible _ _ (n + 1)
    (by omega) ?_
  rw [DeningerBau.root_pow]
  show ((deningerRootChain g j) ^ ((e : ℤ) * k)) ^ (n + 1) = (deningerRootChain g m) ^ k
  rw [← hpow, ← zpow_natCast (deningerRootChain g j) c, ← zpow_mul,
    ← zpow_natCast ((deningerRootChain g j) ^ ((e : ℤ) * k)) (n + 1), ← zpow_mul]
  congr 1
  rw [he]
  push_cast
  ring

/-- **For a cyclic group the union of the chain's cyclic subgroups is the whole rationalization.**
It contains the image of a generator and is closed under the roots. -/
theorem deningerRootChain_iSup_eq_top (g : α) (hgen : ∀ a : α, a ∈ Subgroup.zpowers g) :
    (⨆ m, Subgroup.zpowers (deningerRootChain g m)) = ⊤ := by
  have hdir : Directed (· ≤ ·) (fun m => Subgroup.zpowers (deningerRootChain g m)) :=
    (deningerRootChain_zpowers_mono g).directed_le
  refine DeningerBau.eq_top_of_rootClosed _ (fun n y hy => ?_) (fun a => ?_)
  · rw [Subgroup.mem_iSup_of_directed hdir] at hy
    obtain ⟨m, hm⟩ := hy
    obtain ⟨k, hk⟩ := hm
    obtain ⟨j, -, hj⟩ := deningerRootChain_root_mem g n m k
    rw [Subgroup.mem_iSup_of_directed hdir]
    refine ⟨j, ?_⟩
    rwa [show ((deningerRootChain g m) ^ k) = y from hk] at hj
  · rw [Subgroup.mem_iSup_of_directed hdir]
    refine ⟨0, ?_⟩
    obtain ⟨t, ht⟩ := hgen a
    refine ⟨t, ?_⟩
    rw [deningerRootChain_zero]
    show (DeningerBau.of g) ^ t = DeningerBau.of a
    rw [← map_zpow]
    exact congrArg DeningerBau.of ht

/-- Each element of the chain has infinite order, provided the image of the generator is
nontrivial. -/
theorem deningerRootChain_ne_one (g : α) (hg : DeningerBau.of g ≠ 1) (m : ℕ) :
    ∀ k : ℤ, (deningerRootChain g m) ^ k = 1 → k = 0 := by
  intro k hk
  by_contra hne
  refine hg ?_
  have hone : deningerRootChain g m = 1 := by
    refine DeningerBau.torsionFree _ k.natAbs (Int.natAbs_pos.2 hne) ?_
    rcases Int.natAbs_eq k with h | h
    · rw [← zpow_natCast, ← h]
      exact hk
    · have : (deningerRootChain g m) ^ ((k.natAbs : ℤ)) = 1 := by
        rw [show ((k.natAbs : ℤ)) = -k by omega, zpow_neg, hk, inv_one]
      rwa [zpow_natCast] at this
  obtain ⟨c, -, hc⟩ := deningerRootChain_exists_pow g 0 m (by omega)
  rw [← deningerRootChain_zero g, ← hc, hone, one_pow]

/-- **Each subgroup of the chain is infinite cyclic.** -/
theorem deningerRootChain_zpowers_equiv (g : α) (hg : DeningerBau.of g ≠ 1) (m : ℕ) :
    Nonempty ((Subgroup.zpowers (deningerRootChain g m)) ≃* Multiplicative ℤ) := by
  have hinj : Function.Injective (zpowersHom (DeningerBau α) (deningerRootChain g m)) := by
    intro a b hab
    have h1 : (deningerRootChain g m) ^ (Multiplicative.toAdd a - Multiplicative.toAdd b) = 1 := by
      rw [zpow_sub]
      show (zpowersHom (DeningerBau α) (deningerRootChain g m)) a *
        ((zpowersHom (DeningerBau α) (deningerRootChain g m)) b)⁻¹ = 1
      rw [hab, mul_inv_cancel]
    have h2 := deningerRootChain_ne_one g hg m _ h1
    exact Multiplicative.toAdd.injective (by omega)
  have hrange : (zpowersHom (DeningerBau α) (deningerRootChain g m)).range =
      Subgroup.zpowers (deningerRootChain g m) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Multiplicative.toAdd a, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨Multiplicative.ofAdd k, rfl⟩
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end RHTower
