import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-!
# Law-saturation mechanics

Two explicit unary laws induce least observer-repair closures.  The closures are individually
idempotent but noncommuting; alternating them has exact finite depth and an omega-stage common
fixed point while every coordinate reporter stabilizes.
-/

namespace GaloisForLFunctions.HTGeometry

abbrev Point := ℕ × Bool

def ObserverRel (S : Set ℕ) (x y : Point) : Prop :=
  x.1 = y.1 ∧ (x.2 = y.2 ∨ x.1 ∈ S)

def evenLaw (x : Point) : Point :=
  if x.1 % 2 = 0 then (x.1 + 1, x.2) else x

def oddLaw (x : Point) : Point :=
  if x.1 % 2 = 1 then (x.1 + 1, x.2) else x

def Preserves (f : Point → Point) (S : Set ℕ) : Prop :=
  ∀ ⦃x y⦄, ObserverRel S x y → ObserverRel S (f x) (f y)

def evenRepair (S : Set ℕ) : Set ℕ :=
  S ∪ {n | ∃ k ∈ S, k % 2 = 0 ∧ n = k + 1}

def oddRepair (S : Set ℕ) : Set ℕ :=
  S ∪ {n | ∃ k ∈ S, k % 2 = 1 ∧ n = k + 1}

def levelPrefix (k : ℕ) : Set ℕ := {n | n ≤ k}

def sweep (S : Set ℕ) : Set ℕ := oddRepair (evenRepair S)

@[simp] theorem mem_evenRepair {S : Set ℕ} {n : ℕ} :
    n ∈ evenRepair S ↔ n ∈ S ∨ ∃ k ∈ S, k % 2 = 0 ∧ n = k + 1 := by
  rfl

@[simp] theorem mem_oddRepair {S : Set ℕ} {n : ℕ} :
    n ∈ oddRepair S ↔ n ∈ S ∨ ∃ k ∈ S, k % 2 = 1 ∧ n = k + 1 := by
  rfl

theorem observerRel_equivalence (S : Set ℕ) : Equivalence (ObserverRel S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨rfl, Or.inl rfl⟩
  · intro x y h
    exact ⟨h.1.symm, h.2.imp Eq.symm (fun hs => h.1 ▸ hs)⟩
  · intro x y z hxy hyz
    refine ⟨hxy.1.trans hyz.1, ?_⟩
    rcases hxy.2 with hbit | hs
    · rcases hyz.2 with hbit' | hs'
      · exact Or.inl (hbit.trans hbit')
      · exact Or.inr (hxy.1 ▸ hs')
    · exact Or.inr hs

theorem evenRepair_extensive (S : Set ℕ) : S ⊆ evenRepair S := by
  intro n hn
  exact Or.inl hn

theorem oddRepair_extensive (S : Set ℕ) : S ⊆ oddRepair S := by
  intro n hn
  exact Or.inl hn

theorem evenRepair_mono {S T : Set ℕ} (h : S ⊆ T) :
    evenRepair S ⊆ evenRepair T := by
  intro n hn
  rcases hn with hn | ⟨k, hk, hp, rfl⟩
  · exact Or.inl (h hn)
  · exact Or.inr ⟨k, h hk, hp, rfl⟩

theorem oddRepair_mono {S T : Set ℕ} (h : S ⊆ T) :
    oddRepair S ⊆ oddRepair T := by
  intro n hn
  rcases hn with hn | ⟨k, hk, hp, rfl⟩
  · exact Or.inl (h hn)
  · exact Or.inr ⟨k, h hk, hp, rfl⟩

theorem evenRepair_idempotent (S : Set ℕ) :
    evenRepair (evenRepair S) = evenRepair S := by
  apply Set.Subset.antisymm
  · intro n hn
    rcases hn with hn | ⟨k, hk, hkEven, rfl⟩
    · exact hn
    · rcases hk with hk | ⟨j, hj, hjEven, rfl⟩
      · exact Or.inr ⟨k, hk, hkEven, rfl⟩
      · omega
  · exact evenRepair_extensive _

theorem oddRepair_idempotent (S : Set ℕ) :
    oddRepair (oddRepair S) = oddRepair S := by
  apply Set.Subset.antisymm
  · intro n hn
    rcases hn with hn | ⟨k, hk, hkOdd, rfl⟩
    · exact hn
    · rcases hk with hk | ⟨j, hj, hjOdd, rfl⟩
      · exact Or.inr ⟨k, hk, hkOdd, rfl⟩
      · omega
  · exact oddRepair_extensive _

theorem evenLaw_preserves_iff (S : Set ℕ) :
    Preserves evenLaw S ↔ evenRepair S = S := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro n hn
      rcases hn with hn | ⟨k, hk, hkEven, rfl⟩
      · exact hn
      · have hrel : ObserverRel S (k, false) (k, true) := ⟨rfl, Or.inr hk⟩
        have himg := h hrel
        simp [evenLaw, hkEven, ObserverRel] at himg
        exact himg
    · exact evenRepair_extensive S
  · intro h x y hxy
    rcases x with ⟨n, b⟩
    rcases y with ⟨m, c⟩
    simp only [ObserverRel] at hxy ⊢
    rcases hxy with ⟨rfl, hxy⟩
    by_cases hp : n % 2 = 0
    · simp [evenLaw, hp]
      rcases hxy with hbc | hn
      · exact Or.inl hbc
      · right
        have : n + 1 ∈ evenRepair S := Or.inr ⟨n, hn, hp, rfl⟩
        rwa [h] at this
    · simp [evenLaw, hp]
      exact hxy

theorem oddLaw_preserves_iff (S : Set ℕ) :
    Preserves oddLaw S ↔ oddRepair S = S := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · intro n hn
      rcases hn with hn | ⟨k, hk, hkOdd, rfl⟩
      · exact hn
      · have hrel : ObserverRel S (k, false) (k, true) := ⟨rfl, Or.inr hk⟩
        have himg := h hrel
        simp [oddLaw, hkOdd, ObserverRel] at himg
        exact himg
    · exact oddRepair_extensive S
  · intro h x y hxy
    rcases x with ⟨n, b⟩
    rcases y with ⟨m, c⟩
    simp only [ObserverRel] at hxy ⊢
    rcases hxy with ⟨rfl, hxy⟩
    by_cases hp : n % 2 = 1
    · simp [oddLaw, hp]
      rcases hxy with hbc | hn
      · exact Or.inl hbc
      · right
        have : n + 1 ∈ oddRepair S := Or.inr ⟨n, hn, hp, rfl⟩
        rwa [h] at this
    · simp [oddLaw, hp]
      exact hxy

theorem evenRepair_least {S T : Set ℕ} (hST : S ⊆ T) (hT : Preserves evenLaw T) :
    evenRepair S ⊆ T := by
  have hfix : evenRepair T = T := (evenLaw_preserves_iff T).1 hT
  intro n hn
  have hmem : n ∈ evenRepair T := evenRepair_mono hST hn
  rwa [hfix] at hmem

theorem oddRepair_least {S T : Set ℕ} (hST : S ⊆ T) (hT : Preserves oddLaw T) :
    oddRepair S ⊆ T := by
  have hfix : oddRepair T = T := (oddLaw_preserves_iff T).1 hT
  intro n hn
  have hmem : n ∈ oddRepair T := oddRepair_mono hST hn
  rwa [hfix] at hmem

theorem evenRepair_levelPrefix (r : ℕ) :
    evenRepair (levelPrefix (2 * r)) = levelPrefix (2 * r + 1) := by
  ext n
  constructor
  · intro hn
    rcases hn with hn | ⟨k, hk, _, rfl⟩
    · change n ≤ 2 * r at hn
      change n ≤ 2 * r + 1
      omega
    · change k ≤ 2 * r at hk
      change k + 1 ≤ 2 * r + 1
      omega
  · intro hn
    change n ≤ 2 * r + 1 at hn
    by_cases hle : n ≤ 2 * r
    · exact Or.inl hle
    · have hnEq : n = 2 * r + 1 := by omega
      exact Or.inr ⟨2 * r, by simp [levelPrefix], by omega, hnEq⟩

theorem oddRepair_levelPrefix (r : ℕ) :
    oddRepair (levelPrefix (2 * r + 1)) = levelPrefix (2 * r + 2) := by
  ext n
  constructor
  · intro hn
    rcases hn with hn | ⟨k, hk, _, rfl⟩
    · change n ≤ 2 * r + 1 at hn
      change n ≤ 2 * r + 2
      omega
    · change k ≤ 2 * r + 1 at hk
      change k + 1 ≤ 2 * r + 2
      omega
  · intro hn
    change n ≤ 2 * r + 2 at hn
    by_cases hle : n ≤ 2 * r + 1
    · exact Or.inl hle
    · have hnEq : n = 2 * r + 2 := by omega
      exact Or.inr ⟨2 * r + 1, by simp [levelPrefix], by omega, hnEq⟩

theorem sweep_levelPrefix (r : ℕ) :
    sweep (levelPrefix (2 * r)) = levelPrefix (2 * r + 2) := by
  rw [sweep, evenRepair_levelPrefix, oddRepair_levelPrefix]

theorem sweep_iterate_levelPrefix (r : ℕ) :
    (sweep^[r]) (levelPrefix 0) = levelPrefix (2 * r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, sweep_levelPrefix]
      congr 2

theorem oddRepair_levelPrefix_zero : oddRepair (levelPrefix 0) = levelPrefix 0 := by
  ext n
  constructor
  · intro hn
    rcases hn with hn | ⟨k, hk, hkOdd, rfl⟩
    · exact hn
    · change k ≤ 0 at hk
      omega
  · intro hn
    exact oddRepair_extensive _ hn

theorem repairs_do_not_commute :
    oddRepair (evenRepair (levelPrefix 0)) ≠
      evenRepair (oddRepair (levelPrefix 0)) := by
  rw [evenRepair_levelPrefix 0, oddRepair_levelPrefix 0,
    oddRepair_levelPrefix_zero, evenRepair_levelPrefix 0]
  intro h
  have hmem : 2 ∈ levelPrefix 1 := by
    rw [← h]
    simp [levelPrefix]
  change 2 ≤ 1 at hmem
  omega

theorem finite_stage_not_even_fixed (r : ℕ) :
    evenRepair (levelPrefix (2 * r)) ≠ levelPrefix (2 * r) := by
  rw [evenRepair_levelPrefix]
  intro h
  have : 2 * r + 1 ∈ levelPrefix (2 * r) := by
    rw [← h]
    simp [levelPrefix]
  change 2 * r + 1 ≤ 2 * r at this
  omega

theorem common_fixed_above_zero_eq_univ (S : Set ℕ) (hzero : 0 ∈ S)
    (he : evenRepair S = S) (ho : oddRepair S = S) : S = Set.univ := by
  have hnext : ∀ n ∈ S, n + 1 ∈ S := by
    intro n hn
    by_cases hpar : n % 2 = 0
    · have hmem : n + 1 ∈ evenRepair S := Or.inr ⟨n, hn, hpar, rfl⟩
      rwa [he] at hmem
    · have hlt : n % 2 < 2 := Nat.mod_lt n (by omega)
      have hodd : n % 2 = 1 := by omega
      have hmem : n + 1 ∈ oddRepair S := Or.inr ⟨n, hn, hodd, rfl⟩
      rwa [ho] at hmem
  ext n
  simp only [Set.mem_univ, iff_true]
  induction n with
  | zero => exact hzero
  | succ n ih => exact hnext n ih

theorem reporter_stabilization (j r : ℕ) :
    j ∈ (sweep^[r]) (levelPrefix 0) ↔ j ≤ 2 * r := by
  rw [sweep_iterate_levelPrefix]
  rfl

theorem strict_global_history (r : ℕ) :
    levelPrefix (2 * r) ⊂ levelPrefix (2 * (r + 1)) := by
  constructor
  · intro n hn
    change n ≤ 2 * r at hn
    change n ≤ 2 * (r + 1)
    omega
  · intro h
    have hbig : 2 * r + 1 ∈ levelPrefix (2 * (r + 1)) := by
      change 2 * r + 1 ≤ 2 * (r + 1)
      omega
    have hsmall : 2 * r + 1 ∈ levelPrefix (2 * r) := h hbig
    change 2 * r + 1 ≤ 2 * r at hsmall
    omega

theorem lawSaturationMechanism_closed :
    (∀ S, evenRepair (evenRepair S) = evenRepair S) ∧
    (∀ S, oddRepair (oddRepair S) = oddRepair S) ∧
    (∀ S, Preserves evenLaw S ↔ evenRepair S = S) ∧
    (∀ S, Preserves oddLaw S ↔ oddRepair S = S) ∧
    (∀ S T, S ⊆ T → Preserves evenLaw T → evenRepair S ⊆ T) ∧
    (∀ S T, S ⊆ T → Preserves oddLaw T → oddRepair S ⊆ T) ∧
    oddRepair (evenRepair (levelPrefix 0)) ≠
      evenRepair (oddRepair (levelPrefix 0)) ∧
    (∀ r, (sweep^[r]) (levelPrefix 0) = levelPrefix (2 * r)) ∧
    (∀ r, evenRepair (levelPrefix (2 * r)) ≠ levelPrefix (2 * r)) ∧
    (∀ S, 0 ∈ S → evenRepair S = S → oddRepair S = S → S = Set.univ) ∧
    (∀ j r, j ∈ (sweep^[r]) (levelPrefix 0) ↔ j ≤ 2 * r) ∧
    (∀ r, levelPrefix (2 * r) ⊂ levelPrefix (2 * (r + 1))) := by
  exact ⟨evenRepair_idempotent, oddRepair_idempotent,
    evenLaw_preserves_iff, oddLaw_preserves_iff,
    (fun _ _ => evenRepair_least), (fun _ _ => oddRepair_least),
    repairs_do_not_commute, sweep_iterate_levelPrefix,
    finite_stage_not_even_fixed, common_fixed_above_zero_eq_univ,
    reporter_stabilization,
    strict_global_history⟩

end GaloisForLFunctions.HTGeometry

