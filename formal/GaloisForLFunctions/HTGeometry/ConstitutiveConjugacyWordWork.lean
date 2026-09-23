import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.List.SplitLengths
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic

/-!
# Conjugacy word work

Exact word norm and conjugacy length for a finite symmetric generating set, including sharp
linear and balanced quadratic factorization minima, refinement laws, generator-preserving
reflection invariance, and unitary Gram blindness.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {G : Type*} [Group G]

/-- Finite symmetric generating data, including an exact word for every group element. -/
structure SymmetricGeneratingSet (G : Type*) [Group G] where
  carrier : Finset G
  inv_mem_iff : ∀ g : G, g⁻¹ ∈ carrier ↔ g ∈ carrier
  spans : ∀ g : G, ∃ w : List G, (∀ x ∈ w, x ∈ carrier) ∧ w.prod = g

def SymmetricGeneratingSet.IsWord (A : SymmetricGeneratingSet G) (g : G)
    (w : List G) : Prop :=
  (∀ x ∈ w, x ∈ A.carrier) ∧ w.prod = g

theorem SymmetricGeneratingSet.exists_isWord (A : SymmetricGeneratingSet G) (g : G) :
    ∃ w : List G, A.IsWord g w :=
  A.spans g

theorem SymmetricGeneratingSet.IsWord.nil (A : SymmetricGeneratingSet G) :
    A.IsWord 1 [] := by
  simp [SymmetricGeneratingSet.IsWord]

theorem SymmetricGeneratingSet.IsWord.append {A : SymmetricGeneratingSet G}
    {g h : G} {u v : List G} (hu : A.IsWord g u) (hv : A.IsWord h v) :
    A.IsWord (g * h) (u ++ v) := by
  constructor
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hu.1 x hx
    · exact hv.1 x hx
  · simp [hu.2, hv.2]

def HasWordLength (A : SymmetricGeneratingSet G) (g : G) (n : ℕ) : Prop :=
  ∃ w : List G, A.IsWord g w ∧ w.length = n

theorem exists_hasWordLength (A : SymmetricGeneratingSet G) (g : G) :
    ∃ n, HasWordLength A g n := by
  obtain ⟨w, hw⟩ := A.exists_isWord g
  exact ⟨w.length, w, hw, rfl⟩

/-- Word norm: least length of a word over `A` representing `g`. -/
def wordLength (A : SymmetricGeneratingSet G) (g : G) : ℕ :=
  by
    classical
    exact Nat.find (exists_hasWordLength A g)

theorem wordLength_spec (A : SymmetricGeneratingSet G) (g : G) :
    HasWordLength A g (wordLength A g) :=
  by
    classical
    exact Nat.find_spec (exists_hasWordLength A g)

theorem wordLength_minimal (A : SymmetricGeneratingSet G) {g : G} {n : ℕ}
    (h : HasWordLength A g n) : wordLength A g ≤ n :=
  by
    classical
    exact Nat.find_min' (exists_hasWordLength A g) h

theorem wordLength_le_of_isWord (A : SymmetricGeneratingSet G) {g : G} {w : List G}
    (hw : A.IsWord g w) : wordLength A g ≤ w.length :=
  wordLength_minimal A ⟨w, hw, rfl⟩

theorem wordLength_one (A : SymmetricGeneratingSet G) : wordLength A 1 = 0 := by
  exact Nat.eq_zero_of_le_zero
    (wordLength_le_of_isWord A (SymmetricGeneratingSet.IsWord.nil A))

theorem wordLength_eq_zero_iff (A : SymmetricGeneratingSet G) (g : G) :
    wordLength A g = 0 ↔ g = 1 := by
  constructor
  · intro h
    obtain ⟨w, hw, hwlen⟩ := wordLength_spec A g
    have : w = [] := List.eq_nil_of_length_eq_zero (hwlen.trans h)
    simpa [this] using hw.2.symm
  · rintro rfl
    exact wordLength_one A

theorem wordLength_mul_le (A : SymmetricGeneratingSet G) (g h : G) :
    wordLength A (g * h) ≤ wordLength A g + wordLength A h := by
  obtain ⟨u, hu, hulen⟩ := wordLength_spec A g
  obtain ⟨v, hv, hvlen⟩ := wordLength_spec A h
  simpa [hulen, hvlen] using wordLength_le_of_isWord A (hu.append hv)

theorem SymmetricGeneratingSet.IsWord.inv {A : SymmetricGeneratingSet G}
    {g : G} {w : List G} (hw : A.IsWord g w) :
    A.IsWord g⁻¹ ((w.map fun x ↦ x⁻¹).reverse) := by
  constructor
  · intro y hy
    rw [List.mem_reverse, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (A.inv_mem_iff x).2 (hw.1 x hx)
  · exact (List.prod_inv_reverse w).symm.trans (congrArg Inv.inv hw.2)

theorem wordLength_inv (A : SymmetricGeneratingSet G) (g : G) :
    wordLength A g⁻¹ = wordLength A g := by
  apply le_antisymm
  · obtain ⟨w, hw, hwlen⟩ := wordLength_spec A g
    refine (wordLength_le_of_isWord A hw.inv).trans_eq ?_
    simp [hwlen]
  · obtain ⟨w, hw, hwlen⟩ := wordLength_spec A g⁻¹
    have hinv := hw.inv
    simp only [inv_inv] at hinv
    refine (wordLength_le_of_isWord A hinv).trans_eq ?_
    simp [hwlen]

def HasConjugateLength (A : SymmetricGeneratingSet G) (g : G) (n : ℕ) : Prop :=
  ∃ a : G, wordLength A (a * g * a⁻¹) = n

theorem exists_hasConjugateLength (A : SymmetricGeneratingSet G) (g : G) :
    ∃ n, HasConjugateLength A g n := by
  exact ⟨wordLength A g, 1, by simp⟩

/-- Shortest word length in the conjugacy class of `g`. -/
def conjugacyLength (A : SymmetricGeneratingSet G) (g : G) : ℕ :=
  by
    classical
    exact Nat.find (exists_hasConjugateLength A g)

theorem conjugacyLength_spec (A : SymmetricGeneratingSet G) (g : G) :
    HasConjugateLength A g (conjugacyLength A g) :=
  by
    classical
    exact Nat.find_spec (exists_hasConjugateLength A g)

theorem conjugacyLength_minimal (A : SymmetricGeneratingSet G) {g : G} {n : ℕ}
    (h : HasConjugateLength A g n) : conjugacyLength A g ≤ n :=
  by
    classical
    exact Nat.find_min' (exists_hasConjugateLength A g) h

theorem conjugacyLength_le_wordLength (A : SymmetricGeneratingSet G) (g : G) :
    conjugacyLength A g ≤ wordLength A g := by
  apply conjugacyLength_minimal A
  exact ⟨1, by simp⟩

theorem conjugacyLength_le_wordLength_of_isConj (A : SymmetricGeneratingSet G)
    {g h : G} (hgh : IsConj g h) : conjugacyLength A g ≤ wordLength A h := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hgh
  apply conjugacyLength_minimal A
  exact ⟨a, congrArg (wordLength A) ha⟩

theorem conjugacyLength_eq_of_isConj (A : SymmetricGeneratingSet G)
    {g h : G} (hgh : IsConj g h) : conjugacyLength A g = conjugacyLength A h := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := conjugacyLength_spec A h
    calc
      conjugacyLength A g ≤ wordLength A (a * h * a⁻¹) :=
        conjugacyLength_le_wordLength_of_isConj A
          (hgh.trans (isConj_iff.2 ⟨a, rfl⟩))
      _ = conjugacyLength A h := ha
  · obtain ⟨a, ha⟩ := conjugacyLength_spec A g
    calc
      conjugacyLength A h ≤ wordLength A (a * g * a⁻¹) :=
        conjugacyLength_le_wordLength_of_isConj A
          (hgh.symm.trans (isConj_iff.2 ⟨a, rfl⟩))
      _ = conjugacyLength A g := ha

theorem conjugacyLength_inv (A : SymmetricGeneratingSet G) (g : G) :
    conjugacyLength A g⁻¹ = conjugacyLength A g := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := conjugacyLength_spec A g
    apply conjugacyLength_minimal A
    refine ⟨a, ?_⟩
    rw [← wordLength_inv A]
    convert ha using 2
    all_goals group
  · obtain ⟨a, ha⟩ := conjugacyLength_spec A g⁻¹
    apply conjugacyLength_minimal A
    refine ⟨a, ?_⟩
    rw [← wordLength_inv A]
    convert ha using 2
    all_goals group

theorem conjugacyLength_eq_zero_iff (A : SymmetricGeneratingSet G) (g : G) :
    conjugacyLength A g = 0 ↔ g = 1 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := conjugacyLength_spec A g
    have hword : wordLength A (a * g * a⁻¹) = 0 := ha.trans h
    have hconj : a * g * a⁻¹ = 1 := (wordLength_eq_zero_iff A _).1 hword
    exact (isConj_one_left.mp (isConj_iff.2 ⟨a, hconj⟩))
  · rintro rfl
    exact Nat.eq_zero_of_le_zero ((conjugacyLength_le_wordLength A 1).trans_eq (wordLength_one A))

def listWordWork (A : SymmetricGeneratingSet G) (w : List G) : ℕ :=
  (w.map (wordLength A)).sum

def listQuadraticWordWork (A : SymmetricGeneratingSet G) (w : List G) : ℕ :=
  (w.map fun g ↦ (wordLength A g) ^ (2 : ℕ)).sum

theorem wordLength_list_prod_le (A : SymmetricGeneratingSet G) (w : List G) :
    wordLength A w.prod ≤ listWordWork A w := by
  induction w with
  | nil => simp [listWordWork, wordLength_one]
  | cons g w ih =>
      exact (wordLength_mul_le A g w.prod).trans (Nat.add_le_add_left ih _)

theorem conjugacyLength_le_listWordWork (A : SymmetricGeneratingSet G)
    {g : G} {w : List G} (h : IsConj g w.prod) :
    conjugacyLength A g ≤ listWordWork A w :=
  (conjugacyLength_le_wordLength_of_isConj A h).trans (wordLength_list_prod_le A w)

/-- Exact balanced quadratic cost in `m` slots for total length `L`. -/
def balancedWordWork (m L : ℕ) : ℕ :=
  (m - L % m) * (L / m) ^ (2 : ℕ) + (L % m) * (L / m + 1) ^ (2 : ℕ)

/-- Slot lengths realizing the Euclidean division balance. -/
def balancedSizes (m L : ℕ) : List ℕ :=
  List.replicate (m - L % m) (L / m) ++
    List.replicate (L % m) (L / m + 1)

theorem balancedSizes_length {m L : ℕ} (hm : 0 < m) :
    (balancedSizes m L).length = m := by
  have hr : L % m ≤ m := (Nat.mod_lt L hm).le
  simp [balancedSizes]
  omega

theorem balancedSizes_sum {m L : ℕ} (hm : 0 < m) :
    (balancedSizes m L).sum = L := by
  have hr : L % m ≤ m := (Nat.mod_lt L hm).le
  have hdiv : L = m * (L / m) + L % m := (Nat.div_add_mod L m).symm
  simp only [balancedSizes, List.sum_append, List.sum_replicate, nsmul_eq_mul]
  change (m - L % m) * (L / m) + (L % m) * (L / m + 1) = L
  rw [Nat.sub_mul, Nat.mul_add]
  have hmul : L % m * (L / m) ≤ m * (L / m) := Nat.mul_le_mul_right _ hr
  omega

theorem balancedSizes_square_sum {m L : ℕ} (_hm : 0 < m) :
    ((balancedSizes m L).map fun n ↦ n ^ (2 : ℕ)).sum = balancedWordWork m L := by
  simp [balancedSizes, balancedWordWork]

theorem int_balanced_term_lower (q n : ℕ) :
    (((2 * q + 1) * n : ℕ) : ℤ) - ((q * (q + 1) : ℕ) : ℤ) ≤
      ((n ^ (2 : ℕ) : ℕ) : ℤ) := by
  by_cases h : n ≤ q
  · have h₁ : (n : ℤ) - (q : ℤ) ≤ 0 :=
      sub_nonpos.mpr (by exact_mod_cast h)
    have h₂ : (n : ℤ) - (q : ℤ) - 1 ≤ 0 := by omega
    have hmul : 0 ≤ ((n : ℤ) - (q : ℤ)) * ((n : ℤ) - (q : ℤ) - 1) :=
      mul_nonneg_of_nonpos_of_nonpos h₁ h₂
    push_cast
    nlinarith
  · have h₁ : (q : ℤ) + 1 ≤ (n : ℤ) := by omega
    have ha : 0 ≤ (n : ℤ) - (q : ℤ) := by omega
    have hb : 0 ≤ (n : ℤ) - (q : ℤ) - 1 := by omega
    have hmul : 0 ≤ ((n : ℤ) - (q : ℤ)) * ((n : ℤ) - (q : ℤ) - 1) :=
      mul_nonneg ha hb
    push_cast
    nlinarith

theorem int_balanced_sum_lower (q : ℕ) (ns : List ℕ) :
    (((2 * q + 1) * ns.sum : ℕ) : ℤ) -
        ((ns.length * q * (q + 1) : ℕ) : ℤ) ≤
      (((ns.map fun n ↦ n ^ (2 : ℕ)).sum : ℕ) : ℤ) := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
      have hn := int_balanced_term_lower q n
      simp only [List.sum_cons, List.length_cons, List.map_cons]
      push_cast at ih hn ⊢
      nlinarith

/-- Among `m` natural slot lengths with total at least `L`, balanced squares are minimal. -/
theorem balancedWordWork_le_square_sum {m L : ℕ} (hm : 0 < m) (ns : List ℕ)
    (hlen : ns.length = m) (hsum : L ≤ ns.sum) :
    balancedWordWork m L ≤ (ns.map fun n ↦ n ^ (2 : ℕ)).sum := by
  let q := L / m
  let r := L % m
  have hr : r ≤ m := (Nat.mod_lt L hm).le
  have hdiv : L = m * q + r := by
    simpa [q, r] using (Nat.div_add_mod L m).symm
  have hbase := int_balanced_sum_lower q ns
  have hcoef : (0 : ℤ) ≤ 2 * (q : ℤ) + 1 := by positivity
  have hsumz : (L : ℤ) ≤ ns.sum := by exact_mod_cast hsum
  have hlower :
      (((2 * q + 1) * L : ℕ) : ℤ) - ((m * q * (q + 1) : ℕ) : ℤ) ≤
        (((ns.map fun n ↦ n ^ (2 : ℕ)).sum : ℕ) : ℤ) := by
    push_cast at hbase ⊢
    rw [hlen] at hbase
    nlinarith
  have hid :
      (balancedWordWork m L : ℤ) =
        (((2 * q + 1) * L : ℕ) : ℤ) - ((m * q * (q + 1) : ℕ) : ℤ) := by
    simp only [balancedWordWork]
    change (((m - r) * q ^ (2 : ℕ) + r * (q + 1) ^ (2 : ℕ) : ℕ) : ℤ) = _
    push_cast [Nat.cast_sub hr]
    rw [show (L : ℤ) = m * q + r by exact_mod_cast hdiv]
    ring
  have hz : (balancedWordWork m L : ℤ) ≤
      (((ns.map fun n ↦ n ^ (2 : ℕ)).sum : ℕ) : ℤ) := hid.trans_le hlower
  exact_mod_cast hz

theorem balancedWordWork_one (L : ℕ) : balancedWordWork 1 L = L ^ (2 : ℕ) := by
  simp only [balancedWordWork, Nat.mod_one, Nat.div_one, Nat.sub_zero, zero_mul, add_zero,
    one_mul]

theorem balancedWordWork_eq_self {m L : ℕ} (hm : 0 < m) (hLm : L ≤ m) :
    balancedWordWork m L = L := by
  rcases hLm.eq_or_lt with rfl | hlt
  · simp [balancedWordWork, Nat.div_self hm, Nat.mod_self]
  · simp [balancedWordWork, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

theorem self_le_balancedWordWork {m L : ℕ} (hm : 0 < m) :
    L ≤ balancedWordWork m L := by
  have hsum := balancedSizes_sum (m := m) (L := L) hm
  have hsquare := balancedSizes_square_sum (m := m) (L := L) hm
  have hterm : (balancedSizes m L).sum ≤
      ((balancedSizes m L).map fun n ↦ n ^ (2 : ℕ)).sum := by
    induction balancedSizes m L with
    | nil => simp
    | cons n ns ih =>
        simp only [List.sum_cons, List.map_cons]
        have hn : n ≤ n ^ (2 : ℕ) := by
          cases n with
          | zero => simp
          | succ n => nlinarith
        exact Nat.add_le_add hn ih
  calc
    L = (balancedSizes m L).sum := hsum.symm
    _ ≤ ((balancedSizes m L).map fun n ↦ n ^ (2 : ℕ)).sum := hterm
    _ = balancedWordWork m L := hsquare

theorem balancedWordWork_eq_zero_iff {m L : ℕ} (hm : 0 < m) :
    balancedWordWork m L = 0 ↔ L = 0 := by
  constructor
  · exact fun h ↦ Nat.eq_zero_of_le_zero ((self_le_balancedWordWork hm).trans_eq h)
  · rintro rfl
    simp [balancedWordWork]

theorem sum_wordLength_prod_le_sum_length (A : SymmetricGeneratingSet G)
    (blocks : List (List G))
    (hwords : ∀ b ∈ blocks, ∀ x ∈ b, x ∈ A.carrier) :
    (blocks.map fun b ↦ wordLength A b.prod).sum ≤ (blocks.map List.length).sum := by
  induction blocks with
  | nil => simp
  | cons b blocks ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (wordLength_le_of_isWord A ⟨fun x hx ↦ hwords b (by simp) x hx, rfl⟩)
        (ih fun b hb ↦ hwords b (by simp [hb]))

theorem sum_square_wordLength_prod_le_sum_square_length (A : SymmetricGeneratingSet G)
    (blocks : List (List G))
    (hwords : ∀ b ∈ blocks, ∀ x ∈ b, x ∈ A.carrier) :
    (blocks.map fun b ↦ (wordLength A b.prod) ^ (2 : ℕ)).sum ≤
      (blocks.map fun b ↦ b.length ^ (2 : ℕ)).sum := by
  induction blocks with
  | nil => simp
  | cons b blocks ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (Nat.pow_le_pow_left (wordLength_le_of_isWord A
          ⟨fun x hx ↦ hwords b (by simp) x hx, rfl⟩) 2)
        (ih fun b hb ↦ hwords b (by simp [hb]))

/-- A geodesic word splits into `m` factors with sharp balanced linear and quadratic work. -/
theorem exists_balanced_word_factorization (A : SymmetricGeneratingSet G) (g : G)
    {m : ℕ} (hm : 0 < m) :
    ∃ factors : List G,
      factors.length = m ∧
      factors.prod = g ∧
      listWordWork A factors = wordLength A g ∧
      listQuadraticWordWork A factors = balancedWordWork m (wordLength A g) := by
  obtain ⟨w, hw, hwlen⟩ := wordLength_spec A g
  let sizes := balancedSizes m (wordLength A g)
  let blocks := sizes.splitLengths w
  let factors := blocks.map List.prod
  have hsizesSum : sizes.sum = w.length := by
    rw [balancedSizes_sum hm]
    exact hwlen.symm
  have hflat : blocks.flatten = w := by
    exact List.flatten_splitLengths w sizes hsizesSum.ge
  have hblocks : ∀ b ∈ blocks, ∀ x ∈ b, x ∈ A.carrier := by
    intro b hb x hx
    apply hw.1 x
    rw [← hflat]
    exact List.mem_flatten.2 ⟨b, hb, hx⟩
  have hmaplen : blocks.map List.length = sizes := by
    exact List.map_splitLengths_length w sizes hsizesSum.le
  have hfactorsLen : factors.length = m := by
    simpa [factors, blocks] using
      (balancedSizes_length (m := m) (L := wordLength A g) hm)
  have hfactorsProd : factors.prod = g := by
    change (blocks.map List.prod).prod = g
    rw [← List.prod_flatten, hflat, hw.2]
  have hlinearUpper : listWordWork A factors ≤ wordLength A g := by
    calc
      listWordWork A factors =
          (blocks.map fun b ↦ wordLength A b.prod).sum := by
        simp [listWordWork, factors, Function.comp_def, List.map_map]
      _ ≤ (blocks.map List.length).sum :=
        sum_wordLength_prod_le_sum_length A blocks hblocks
      _ = sizes.sum := by rw [hmaplen]
      _ = wordLength A g := balancedSizes_sum hm
  have hlinearLower : wordLength A g ≤ listWordWork A factors := by
    rw [← hfactorsProd]
    exact wordLength_list_prod_le A factors
  have hlinear : listWordWork A factors = wordLength A g :=
    le_antisymm hlinearUpper hlinearLower
  have hsquareLengths :
      (blocks.map fun b ↦ b.length ^ (2 : ℕ)).sum = balancedWordWork m (wordLength A g) := by
    calc
      (blocks.map fun b ↦ b.length ^ (2 : ℕ)).sum =
          ((blocks.map List.length).map fun n ↦ n ^ (2 : ℕ)).sum := by
        simp [List.map_map, Function.comp_def]
      _ = ((sizes.map fun n ↦ n ^ (2 : ℕ)).sum) := by rw [hmaplen]
      _ = balancedWordWork m (wordLength A g) := balancedSizes_square_sum hm
  have hquadraticUpper :
      listQuadraticWordWork A factors ≤ balancedWordWork m (wordLength A g) := by
    calc
      listQuadraticWordWork A factors =
          (blocks.map fun b ↦ (wordLength A b.prod) ^ (2 : ℕ)).sum := by
        simp [listQuadraticWordWork, factors, Function.comp_def, List.map_map]
      _ ≤ (blocks.map fun b ↦ b.length ^ (2 : ℕ)).sum :=
        sum_square_wordLength_prod_le_sum_square_length A blocks hblocks
      _ = balancedWordWork m (wordLength A g) := hsquareLengths
  have hquadraticLower :
      balancedWordWork m (wordLength A g) ≤ listQuadraticWordWork A factors := by
    have h := balancedWordWork_le_square_sum hm (factors.map (wordLength A))
      (by simpa using hfactorsLen) (by simpa [listWordWork] using hlinearLower)
    simpa [listQuadraticWordWork, List.map_map, Function.comp_def] using h
  exact ⟨factors, hfactorsLen, hfactorsProd, hlinear,
    le_antisymm hquadraticUpper hquadraticLower⟩

/-- Sharp lower bounds for every factorization in a fixed conjugacy class. -/
theorem conjugacy_work_lower_bounds (A : SymmetricGeneratingSet G) {g : G}
    {m : ℕ} (hm : 0 < m) (factors : List G) (hlen : factors.length = m)
    (hconj : IsConj g factors.prod) :
    conjugacyLength A g ≤ listWordWork A factors ∧
      balancedWordWork m (conjugacyLength A g) ≤ listQuadraticWordWork A factors := by
  have hlinear := conjugacyLength_le_listWordWork A hconj
  refine ⟨hlinear, ?_⟩
  have h := balancedWordWork_le_square_sum hm (factors.map (wordLength A))
    (by simpa using hlen) (by simpa [listWordWork] using hlinear)
  simpa [listQuadraticWordWork, List.map_map, Function.comp_def] using h

/-- One balanced factorization attains both conjugacy-class work minima simultaneously. -/
theorem exists_conjugacy_work_minimizer (A : SymmetricGeneratingSet G) (g : G)
    {m : ℕ} (hm : 0 < m) :
    ∃ factors : List G,
      factors.length = m ∧
      IsConj g factors.prod ∧
      listWordWork A factors = conjugacyLength A g ∧
      listQuadraticWordWork A factors = balancedWordWork m (conjugacyLength A g) := by
  obtain ⟨a, ha⟩ := conjugacyLength_spec A g
  obtain ⟨factors, hlen, hprod, hlinear, hquadratic⟩ :=
    exists_balanced_word_factorization A (a * g * a⁻¹) hm
  refine ⟨factors, hlen, ?_, ?_, ?_⟩
  · rw [hprod]
    exact isConj_iff.2 ⟨a, rfl⟩
  · exact hlinear.trans ha
  · rw [hquadratic, ha]

/-- Exact minimum theorem: linear work is conjugacy length; quadratic work is balanced energy. -/
theorem conjugacy_work_exact_minima (A : SymmetricGeneratingSet G) (g : G)
    {m : ℕ} (hm : 0 < m) :
    (∀ factors : List G, factors.length = m → IsConj g factors.prod →
      conjugacyLength A g ≤ listWordWork A factors ∧
      balancedWordWork m (conjugacyLength A g) ≤ listQuadraticWordWork A factors) ∧
    (∃ factors : List G,
      factors.length = m ∧ IsConj g factors.prod ∧
      listWordWork A factors = conjugacyLength A g ∧
      listQuadraticWordWork A factors = balancedWordWork m (conjugacyLength A g)) := by
  exact ⟨fun factors hlen hconj ↦ conjugacy_work_lower_bounds A hm factors hlen hconj,
    exists_conjugacy_work_minimizer A g hm⟩

theorem SymmetricGeneratingSet.IsWord.map_aut {A : SymmetricGeneratingSet G}
    (α : G ≃* G) (hcarrier : ∀ x : G, α x ∈ A.carrier ↔ x ∈ A.carrier)
    {g : G} {w : List G} (hw : A.IsWord g w) :
    A.IsWord (α g) (w.map α) := by
  constructor
  · intro y hy
    rw [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (hcarrier x).2 (hw.1 x hx)
  · calc
      (w.map α).prod = α w.prod := (α.toMonoidHom.map_list_prod w).symm
      _ = α g := congrArg α hw.2

/-- A generator-preserving automorphism is an exact word-norm isometry. -/
theorem wordLength_map_aut (A : SymmetricGeneratingSet G) (α : G ≃* G)
    (hcarrier : ∀ x : G, α x ∈ A.carrier ↔ x ∈ A.carrier) (g : G) :
    wordLength A (α g) = wordLength A g := by
  apply le_antisymm
  · obtain ⟨w, hw, hwlen⟩ := wordLength_spec A g
    have hwmap := hw.map_aut α hcarrier
    simpa [hwlen] using wordLength_le_of_isWord A hwmap
  · obtain ⟨w, hw, hwlen⟩ := wordLength_spec A (α g)
    have hcarrier' : ∀ x : G, α.symm x ∈ A.carrier ↔ x ∈ A.carrier := by
      intro x
      rw [← hcarrier (α.symm x)]
      simp
    have hwmap := hw.map_aut α.symm hcarrier'
    have hle := wordLength_le_of_isWord A hwmap
    simpa [hwlen] using hle

/-- Generator-preserving automorphisms preserve shortest conjugacy length. -/
theorem conjugacyLength_map_aut (A : SymmetricGeneratingSet G) (α : G ≃* G)
    (hcarrier : ∀ x : G, α x ∈ A.carrier ↔ x ∈ A.carrier) (g : G) :
    conjugacyLength A (α g) = conjugacyLength A g := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := conjugacyLength_spec A g
    apply conjugacyLength_minimal A
    refine ⟨α a, ?_⟩
    rw [← α.map_inv, ← α.map_mul, ← α.map_mul, wordLength_map_aut A α hcarrier]
    exact ha
  · have hcarrier' : ∀ x : G, α.symm x ∈ A.carrier ↔ x ∈ A.carrier := by
      intro x
      rw [← hcarrier (α.symm x)]
      simp
    obtain ⟨a, ha⟩ := conjugacyLength_spec A (α g)
    apply conjugacyLength_minimal A
    refine ⟨α.symm a, ?_⟩
    have heq : α.symm a * g * (α.symm a)⁻¹ =
        α.symm (a * α g * a⁻¹) := by simp
    rw [heq, wordLength_map_aut A α.symm hcarrier', ha]

theorem conjugacyLength_reflection (A : SymmetricGeneratingSet G) (α : G ≃* G)
    (hcarrier : ∀ x : G, α x ∈ A.carrier ↔ x ∈ A.carrier) (g : G) :
    conjugacyLength A (α (g⁻¹)) = conjugacyLength A g := by
  rw [conjugacyLength_map_aut A α hcarrier, conjugacyLength_inv]

section UnitaryShadow

variable {R : Type*} [Monoid R] [StarMul R]

/-- Every unitary edge has the same positive Gram shadow. -/
theorem unitary_edge_gram_blind (ρ : G →* unitary R) (g : G) :
    star ((ρ g : unitary R) : R) * ((ρ g : unitary R) : R) = 1 :=
  Unitary.coe_star_mul_self (ρ g)

/-- A faithful unitary representation can separate an edge although its Gram shadow is `1`. -/
theorem faithful_unitary_edge_separated_but_gram_blind (ρ : G →* unitary R)
    (hρ : Function.Injective ρ) {g : G} (hg : g ≠ 1) :
    (((ρ g : unitary R) : R) ≠ (1 : R)) ∧
      star ((ρ g : unitary R) : R) * ((ρ g : unitary R) : R) =
        star ((ρ 1 : unitary R) : R) * ((ρ 1 : unitary R) : R) := by
  constructor
  · intro hcoe
    have hsub : ρ g = 1 := Subtype.ext hcoe
    exact hg (hρ (by simpa using hsub))
  · rw [unitary_edge_gram_blind, unitary_edge_gram_blind]

end UnitaryShadow

end

end GaloisForLFunctions.HTGeometry
