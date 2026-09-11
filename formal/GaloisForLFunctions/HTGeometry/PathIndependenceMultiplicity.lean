import GaloisForLFunctions.HTGeometry.PathIndependenceShift

/-!
# The multiplicity classification of path independence cohomology

The relabeling isomorphism of `PathIndependenceShift` reduces the occupation-graded reduced
cohomology of the independence complex of the path `P_(n+3)` in degree `j+1` to that of `P_n`
in degree `j`.  Together with the three base cases `n = 0, 1, 2` this determines every graded
piece: there is exactly one class in occupation `j` when `n = 3j` or `n + 1 = 3j`, and none
otherwise.

The base cases are:

* `n = 0`: the only face is the empty face and the differential vanishes, so occupation `0`
  carries one class and every higher occupation is empty.
* `n = 1`: the augmented two-term complex `∅ → {0}` is exact, so every occupation vanishes.
* `n = 2`: the faces are `∅`, `{0}`, `{1}` and the differential sends a scalar to the two equal
  singleton values; the difference of the singleton values is the single class in occupation `1`.

Specialising to the pairing paths `n = 2e + 1` gives the graded tower used by the eta trace:
`e = 3k + 1` supplies occupation `2k + 1`, `e = 3k + 2` supplies occupation `2k + 2`, and
`e = 3k` supplies nothing; every occupation `j ≥ 1` is realised by exactly one length.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Finset

variable {F : Type*} [CommRing F]

/-! ### Faces of the short paths -/

theorem isPathFace_empty (n : ℕ) : IsPathFace n (∅ : Finset ℕ) :=
  ⟨fun v hv => absurd hv (by simp), fun v hv => absurd hv (by simp)⟩

theorem isPathFace_zero_eq_empty {σ : Finset ℕ} (h : IsPathFace 0 σ) : σ = ∅ := by
  by_contra hne
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact absurd (h.1 v hv) (by omega)

theorem isPathFace_card_le_one {n : ℕ} (hn : n ≤ 2) {σ : Finset ℕ} (h : IsPathFace n σ) :
    σ.card ≤ 1 := by
  have hsub : σ ⊆ ({0, 1} : Finset ℕ) := by
    intro v hv
    have hlt := h.1 v hv
    have hv01 : v = 0 ∨ v = 1 := by omega
    rcases hv01 with rfl | rfl <;> simp
  by_contra hcard
  have hpair : ({0, 1} : Finset ℕ).card = 2 := by simp
  have h2 : ({0, 1} : Finset ℕ).card ≤ σ.card := by omega
  have heq : σ = ({0, 1} : Finset ℕ) := Finset.eq_of_subset_of_card_le hsub h2
  have h0 : (0 : ℕ) ∈ σ := by rw [heq]; simp
  have h1 : (1 : ℕ) ∈ σ := by rw [heq]; simp
  exact h.2 0 h0 (by simpa using h1)

theorem isPathFace_eq_singleton {n : ℕ} (hn : n ≤ 2) {σ : Finset ℕ} (h : IsPathFace n σ)
    (hc : σ.card = 1) : σ = {0} ∨ σ = {1} := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
  have hlt := h.1 a (by simp)
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem isPathFace_singleton_zero (n : ℕ) (hn : 0 < n) : IsPathFace n ({0} : Finset ℕ) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [Finset.mem_singleton] at hv; omega
  · rw [Finset.mem_singleton] at hv; subst hv; simp

theorem isPathFace_singleton_one (n : ℕ) (hn : 1 < n) : IsPathFace n ({1} : Finset ℕ) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [Finset.mem_singleton] at hv; omega
  · rw [Finset.mem_singleton] at hv; subst hv; simp

/-! ### Vanishing of the supported spaces -/

theorem pathSupported_eq_bot (F : Type*) [CommRing F] {n j : ℕ}
    (h : ∀ σ : Finset ℕ, IsPathFace n σ → σ.card ≠ j) : pathSupported F n j = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  rw [Submodule.mem_bot]
  funext σ
  show f σ = 0
  by_cases hface : IsPathFace n σ
  · exact hf σ (Or.inl (h σ hface))
  · exact hf σ (Or.inr hface)

theorem pathSupported_zero_eq_bot (F : Type*) [CommRing F] {j : ℕ} (hj : 1 ≤ j) :
    pathSupported F 0 j = ⊥ :=
  pathSupported_eq_bot F fun σ hσ hc => by
    rw [isPathFace_zero_eq_empty hσ, Finset.card_empty] at hc
    omega

theorem pathSupported_small_eq_bot (F : Type*) [CommRing F] {n j : ℕ} (hn : n ≤ 2)
    (hj : 2 ≤ j) : pathSupported F n j = ⊥ :=
  pathSupported_eq_bot F fun σ hσ hc => by
    have := isPathFace_card_le_one hn hσ
    omega

/-! ### Subsingleton criteria for the graded cohomology -/

theorem pathCohomology_subsingleton_of_le {n j : ℕ}
    (h : pathCocycles F n j ≤ pathCoboundaries F n j) : Subsingleton (pathCohomology F n j) := by
  have htop : Submodule.comap (pathCocycles F n j).subtype (pathCoboundaries F n j) = ⊤ :=
    Submodule.comap_subtype_eq_top.mpr h
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.Quotient.eq, htop]
  exact Submodule.mem_top

theorem pathCohomology_subsingleton_of_cocycles_eq_bot {n j : ℕ}
    (h : pathCocycles F n j = ⊥) : Subsingleton (pathCohomology F n j) :=
  pathCohomology_subsingleton_of_le (by rw [h]; exact bot_le)

theorem pathCocycles_eq_bot_of_pathSupported_eq_bot {n j : ℕ}
    (h : pathSupported F n j = ⊥) : pathCocycles F n j = ⊥ :=
  le_antisymm (fun _ hf => h.le hf.1) bot_le

/-! ### The differential on the short paths -/

theorem pathCoboundary_zero_path (f : Finset ℕ → F) : pathCoboundary F 0 f = 0 := by
  funext σ
  show pathCoboundary F 0 f σ = 0
  by_cases hface : IsPathFace 0 σ
  · have hσ : σ = ∅ := isPathFace_zero_eq_empty hface
    subst hσ
    rw [pathCoboundary_of_face hface, simplicialCoboundary_apply, Finset.sum_empty]
  · rw [pathCoboundary_of_not_face hface]

theorem pathCoboundary_singleton_zero {n : ℕ} (hn : 0 < n) (g : Finset ℕ → F) :
    pathCoboundary F n g {0} = g ∅ := by
  rw [pathCoboundary_of_face (isPathFace_singleton_zero n hn), simplicialCoboundary_apply,
    Finset.sum_singleton, pathFaceSign_zero, one_mul, Finset.erase_singleton]

theorem pathCoboundary_singleton_one {n : ℕ} (hn : 1 < n) (g : Finset ℕ → F) :
    pathCoboundary F n g {1} = g ∅ := by
  have h0 : (0 : ℕ) ∉ ({1} : Finset ℕ) := by simp
  rw [pathCoboundary_of_face (isPathFace_singleton_one n hn), simplicialCoboundary_apply,
    Finset.sum_singleton, pathFaceSign_one h0, one_mul, Finset.erase_singleton]

theorem pathCoboundary_of_occupation_one {n : ℕ} (hn : n ≤ 2) {f : Finset ℕ → F}
    (hf : f ∈ pathSupported F n 1) : pathCoboundary F n f = 0 := by
  funext σ
  show pathCoboundary F n f σ = 0
  by_cases hface : IsPathFace n σ
  · rw [pathCoboundary_of_face hface, simplicialCoboundary_apply]
    have hemp : f ∅ = 0 := hf ∅ (Or.inl (by simp))
    refine Finset.sum_eq_zero fun v hv => ?_
    have hc : σ.card ≤ 1 := isPathFace_card_le_one hn hface
    have hone : (σ.erase v).card + 1 = σ.card := Finset.card_erase_add_one hv
    have herase : σ.erase v = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [herase, hemp, mul_zero]
  · rw [pathCoboundary_of_not_face hface]

/-! ### The one-face cochains -/

/-- The cochain supported on a single face. -/
def faceIndicator (F : Type*) [CommRing F] (σ₀ : Finset ℕ) (c : F) (σ : Finset ℕ) : F :=
  if σ = σ₀ then c else 0

theorem faceIndicator_self (σ₀ : Finset ℕ) (c : F) : faceIndicator F σ₀ c σ₀ = c := by
  rw [faceIndicator, if_pos rfl]

theorem faceIndicator_of_ne {σ σ₀ : Finset ℕ} (h : σ ≠ σ₀) (c : F) :
    faceIndicator F σ₀ c σ = 0 := by
  rw [faceIndicator, if_neg h]

theorem faceIndicator_mem_pathSupported {n j : ℕ} {σ₀ : Finset ℕ} (c : F)
    (hface : IsPathFace n σ₀) (hc : σ₀.card = j) :
    faceIndicator F σ₀ c ∈ pathSupported F n j := by
  intro σ hσ
  by_cases h : σ = σ₀
  · subst h
    rcases hσ with h1 | h1
    · exact absurd hc h1
    · exact absurd hface h1
  · exact faceIndicator_of_ne h c

/-! ### Exactness in occupation one on the short paths -/

theorem pathCoboundary_faceIndicator_eq {n : ℕ} (hn : 0 < n) (hn2 : n ≤ 2) {c : F}
    {f : Finset ℕ → F} (hf : f ∈ pathSupported F n 1)
    (h0 : IsPathFace n ({0} : Finset ℕ) → f {0} = c)
    (h1 : IsPathFace n ({1} : Finset ℕ) → f {1} = c) :
    pathCoboundary F n (faceIndicator F ∅ c) = f := by
  funext σ
  show pathCoboundary F n (faceIndicator F ∅ c) σ = f σ
  by_cases hface : IsPathFace n σ
  · have hc : σ.card ≤ 1 := isPathFace_card_le_one hn2 hface
    by_cases hcard : σ.card = 0
    · have hσ : σ = ∅ := Finset.card_eq_zero.mp hcard
      subst hσ
      rw [pathCoboundary_of_face hface, simplicialCoboundary_apply, Finset.sum_empty]
      exact (hf ∅ (Or.inl (by simp))).symm
    · have hcard1 : σ.card = 1 := by omega
      rcases isPathFace_eq_singleton hn2 hface hcard1 with rfl | rfl
      · rw [pathCoboundary_singleton_zero hn, faceIndicator_self]
        exact (h0 hface).symm
      · have hn1 : 1 < n := hface.1 1 (by simp)
        rw [pathCoboundary_singleton_one hn1, faceIndicator_self]
        exact (h1 hface).symm
  · rw [pathCoboundary_of_not_face hface]
    exact (hf σ (Or.inr hface)).symm

theorem mem_pathCoboundaries_one {f : Finset ℕ → F} (hf : f ∈ pathSupported F 1 1) :
    f ∈ pathCoboundaries F 1 1 := by
  refine ⟨faceIndicator F ∅ (f {0}),
    faceIndicator_mem_pathSupported _ (isPathFace_empty 1) Finset.card_empty, ?_⟩
  rw [pathCoboundaryₗ_apply]
  exact pathCoboundary_faceIndicator_eq (by omega) (by omega) hf (fun _ => rfl)
    (fun h => absurd (h.1 1 (by simp)) (by omega))

theorem mem_pathCoboundaries_two {f : Finset ℕ → F} (hf : f ∈ pathSupported F 2 1)
    (heq : f {0} = f {1}) : f ∈ pathCoboundaries F 2 1 := by
  refine ⟨faceIndicator F ∅ (f {0}),
    faceIndicator_mem_pathSupported _ (isPathFace_empty 2) Finset.card_empty, ?_⟩
  rw [pathCoboundaryₗ_apply]
  exact pathCoboundary_faceIndicator_eq (by omega) (by omega) hf (fun _ => rfl)
    (fun _ => heq.symm)

/-! ### Occupation zero on a nonempty path -/

theorem pathCocycles_zero_eq_bot (F : Type*) [CommRing F] {n : ℕ} (hn : 0 < n) :
    pathCocycles F n 0 = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  rw [Submodule.mem_bot]
  have hsup := hf.1
  have hker : pathCoboundary F n f = 0 := by
    have h2 := hf.2
    rw [SetLike.mem_coe, LinearMap.mem_ker, pathCoboundaryₗ_apply] at h2
    exact h2
  have hemp : f ∅ = 0 := by
    have h := congrFun hker {0}
    rw [pathCoboundary_singleton_zero hn] at h
    exact h
  funext σ
  show f σ = 0
  by_cases hσ : σ = ∅
  · subst hσ; exact hemp
  · exact hsup σ (Or.inl fun h => hσ (Finset.card_eq_zero.mp h))

theorem pathCohomology_occupation_zero_subsingleton (F : Type*) [CommRing F] {n : ℕ}
    (hn : 0 < n) : Subsingleton (pathCohomology F n 0) :=
  pathCohomology_subsingleton_of_cocycles_eq_bot (pathCocycles_zero_eq_bot F hn)

/-! ### The base case `n = 0` -/

theorem pathCoboundaries_occupation_zero (n : ℕ) : pathCoboundaries F n 0 = ⊥ := rfl

theorem comap_pathCoboundaries_occupation_zero (n : ℕ) :
    Submodule.comap (pathCocycles F n 0).subtype (pathCoboundaries F n 0) = ⊥ := by
  rw [pathCoboundaries_occupation_zero, Submodule.comap_bot, Submodule.ker_subtype]

/-- Evaluation at the empty face on the occupation-zero cocycles. -/
def emptyEval (F : Type*) [CommRing F] (n : ℕ) : pathCocycles F n 0 →ₗ[F] F :=
  LinearMap.proj (∅ : Finset ℕ) ∘ₗ (pathCocycles F n 0).subtype

theorem emptyEval_apply (n : ℕ) (f : pathCocycles F n 0) :
    emptyEval F n f = (f : Finset ℕ → F) ∅ := rfl

theorem mem_pathCocycles_zero_path {f : Finset ℕ → F} (hf : f ∈ pathSupported F 0 0) :
    f ∈ pathCocycles F 0 0 := by
  refine ⟨hf, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, pathCoboundaryₗ_apply]
  exact pathCoboundary_zero_path f

theorem emptyEval_bijective (F : Type*) [CommRing F] :
    Function.Bijective (emptyEval F 0) := by
  constructor
  · intro f g hfg
    rw [emptyEval_apply, emptyEval_apply] at hfg
    refine Subtype.ext (funext fun σ => ?_)
    by_cases hσ : σ = ∅
    · subst hσ; exact hfg
    · have hc : σ.card ≠ 0 := fun h => hσ (Finset.card_eq_zero.mp h)
      rw [f.2.1 σ (Or.inl hc), g.2.1 σ (Or.inl hc)]
  · intro c
    refine ⟨⟨faceIndicator F ∅ c, mem_pathCocycles_zero_path
      (faceIndicator_mem_pathSupported c (isPathFace_empty 0) Finset.card_empty)⟩, ?_⟩
    rw [emptyEval_apply]
    exact faceIndicator_self ∅ c

/-- **Base case `n = 0`.** The empty path carries exactly one class, in occupation zero. -/
def pathCohomologyZeroEquiv (F : Type*) [CommRing F] : pathCohomology F 0 0 ≃ₗ[F] F :=
  (Submodule.quotEquivOfEqBot _ (comap_pathCoboundaries_occupation_zero 0)).trans
    (LinearEquiv.ofBijective (emptyEval F 0) (emptyEval_bijective F))

/-! ### The base case `n = 1` -/

/-- **Base case `n = 1`.** The two-term augmented complex of the single-vertex path is exact. -/
theorem pathCohomology_one_one_subsingleton (F : Type*) [CommRing F] :
    Subsingleton (pathCohomology F 1 1) :=
  pathCohomology_subsingleton_of_le fun _ hf => mem_pathCoboundaries_one hf.1

/-! ### The base case `n = 2` -/

/-- The difference of the two singleton values, on the occupation-one cocycles. -/
def pairDiff (F : Type*) [CommRing F] (n : ℕ) : pathCocycles F n 1 →ₗ[F] F :=
  ((LinearMap.proj ({0} : Finset ℕ) : (Finset ℕ → F) →ₗ[F] F)
      - (LinearMap.proj ({1} : Finset ℕ) : (Finset ℕ → F) →ₗ[F] F)) ∘ₗ
    (pathCocycles F n 1).subtype

theorem pairDiff_apply (n : ℕ) (f : pathCocycles F n 1) :
    pairDiff F n f = (f : Finset ℕ → F) {0} - (f : Finset ℕ → F) {1} := rfl

theorem pairDiff_coboundaries_le_ker {n : ℕ} (hn : 1 < n) :
    Submodule.comap (pathCocycles F n 1).subtype (pathCoboundaries F n 1)
      ≤ LinearMap.ker (pairDiff F n) := by
  intro x hx
  obtain ⟨g, hg, hmap⟩ := hx
  have hval : (x : Finset ℕ → F) = pathCoboundary F n g := by
    rw [← pathCoboundaryₗ_apply]; exact hmap.symm
  rw [LinearMap.mem_ker, pairDiff_apply, hval, pathCoboundary_singleton_zero (by omega),
    pathCoboundary_singleton_one hn, sub_self]

/-- The class map on occupation-one cohomology induced by the singleton difference. -/
def pathCohomologyPairMap (F : Type*) [CommRing F] (n : ℕ) (hn : 1 < n) :
    pathCohomology F n 1 →ₗ[F] F :=
  Submodule.liftQ _ (pairDiff F n) (pairDiff_coboundaries_le_ker hn)

theorem pathCohomologyPairMap_bijective (F : Type*) [CommRing F] :
    Function.Bijective (pathCohomologyPairMap F 2 (by omega)) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [pathCohomologyPairMap, Submodule.liftQ_apply, Submodule.liftQ_apply, pairDiff_apply,
      pairDiff_apply] at hab
    rw [Submodule.Quotient.eq]
    show ((x - y : pathCocycles F 2 1) : Finset ℕ → F) ∈ pathCoboundaries F 2 1
    refine mem_pathCoboundaries_two (x - y).2.1 ?_
    show (x : Finset ℕ → F) {0} - (y : Finset ℕ → F) {0}
        = (x : Finset ℕ → F) {1} - (y : Finset ℕ → F) {1}
    linear_combination hab
  · intro c
    have hface : IsPathFace 2 ({0} : Finset ℕ) := isPathFace_singleton_zero 2 (by omega)
    have hsup : faceIndicator F ({0} : Finset ℕ) c ∈ pathSupported F 2 1 :=
      faceIndicator_mem_pathSupported c hface (by simp)
    have hmem : faceIndicator F ({0} : Finset ℕ) c ∈ pathCocycles F 2 1 := by
      refine ⟨hsup, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, pathCoboundaryₗ_apply]
      exact pathCoboundary_of_occupation_one (by omega) hsup
    refine ⟨Submodule.Quotient.mk ⟨faceIndicator F ({0} : Finset ℕ) c, hmem⟩, ?_⟩
    rw [pathCohomologyPairMap, Submodule.liftQ_apply, pairDiff_apply]
    show faceIndicator F ({0} : Finset ℕ) c {0} - faceIndicator F ({0} : Finset ℕ) c {1} = c
    rw [faceIndicator_self, faceIndicator_of_ne (by simp), sub_zero]

/-- **Base case `n = 2`.** The difference of the two singleton values is the single class in
occupation one. -/
def pathCohomologyTwoEquiv (F : Type*) [CommRing F] : pathCohomology F 2 1 ≃ₗ[F] F :=
  LinearEquiv.ofBijective (pathCohomologyPairMap F 2 (by omega))
    (pathCohomologyPairMap_bijective F)

/-! ### The classification -/

/-- **One class in occupation `j` when `n = 3j` or `n + 1 = 3j`.** -/
theorem pathCohomology_nonempty_equiv (F : Type*) [CommRing F] (j : ℕ) :
    ∀ n : ℕ, (n = 3 * j ∨ n + 1 = 3 * j) → Nonempty (pathCohomology F n j ≃ₗ[F] F) := by
  induction j with
  | zero =>
    intro n h
    have hn : n = 0 := by omega
    subst hn
    exact ⟨pathCohomologyZeroEquiv F⟩
  | succ i ih =>
    intro n h
    by_cases hn : n ≤ 2
    · obtain ⟨rfl, rfl⟩ : n = 2 ∧ i = 0 := by omega
      exact ⟨pathCohomologyTwoEquiv F⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      obtain ⟨e⟩ := ih m (by omega)
      exact ⟨(pathCohomologyShiftEquiv F m i).trans e⟩

/-- **No class in occupation `j` unless `n = 3j` or `n + 1 = 3j`.** -/
theorem pathCohomology_subsingleton (F : Type*) [CommRing F] (j : ℕ) :
    ∀ n : ℕ, ¬ (n = 3 * j ∨ n + 1 = 3 * j) → Subsingleton (pathCohomology F n j) := by
  induction j with
  | zero =>
    intro n h
    exact pathCohomology_subsingleton_of_cocycles_eq_bot
      (pathCocycles_zero_eq_bot F (by omega))
  | succ i ih =>
    intro n h
    by_cases hn : n ≤ 2
    · rcases Nat.lt_or_ge n 1 with h0 | h0
      · obtain rfl : n = 0 := by omega
        exact pathCohomology_subsingleton_of_cocycles_eq_bot
          (pathCocycles_eq_bot_of_pathSupported_eq_bot
            (pathSupported_zero_eq_bot F (by omega)))
      · rcases Nat.lt_or_ge i 1 with hi | hi
        · obtain rfl : i = 0 := by omega
          obtain rfl : n = 1 := by omega
          exact pathCohomology_one_one_subsingleton F
        · exact pathCohomology_subsingleton_of_cocycles_eq_bot
            (pathCocycles_eq_bot_of_pathSupported_eq_bot
              (pathSupported_small_eq_bot F hn (by omega)))
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      haveI := ih m (by omega)
      exact Equiv.subsingleton (pathCohomologyShiftEquiv F m i).toEquiv

/-- **The graded multiplicity of the path independence complex.** -/
theorem pathCohomology_finrank (F : Type*) [Field F] (n j : ℕ) :
    Module.finrank F (pathCohomology F n j) = if n = 3 * j ∨ n + 1 = 3 * j then 1 else 0 := by
  by_cases h : n = 3 * j ∨ n + 1 = 3 * j
  · obtain ⟨e⟩ := pathCohomology_nonempty_equiv F j n h
    rw [if_pos h, e.finrank_eq, Module.finrank_self]
  · haveI := pathCohomology_subsingleton F j n h
    rw [if_neg h, Module.finrank_zero_of_subsingleton]

/-! ### The paired path tower -/

/-- The pairing path of length `2(3k+1)+1 = 6k+3` carries its single class in occupation
`2k+1`. -/
theorem pathCohomology_pairedPath_odd (F : Type*) [CommRing F] (k : ℕ) :
    Nonempty (pathCohomology F (6 * k + 3) (2 * k + 1) ≃ₗ[F] F) :=
  pathCohomology_nonempty_equiv F _ _ (Or.inl (by omega))

/-- The pairing path of length `2(3k+2)+1 = 6k+5` carries its single class in occupation
`2k+2`. -/
theorem pathCohomology_pairedPath_even (F : Type*) [CommRing F] (k : ℕ) :
    Nonempty (pathCohomology F (6 * k + 5) (2 * k + 2) ≃ₗ[F] F) :=
  pathCohomology_nonempty_equiv F _ _ (Or.inr (by omega))

/-- The pairing path of length `2(3k)+1 = 6k+1` carries no class at all. -/
theorem pathCohomology_pairedPath_void (F : Type*) [CommRing F] (k j : ℕ) :
    Subsingleton (pathCohomology F (6 * k + 1) j) :=
  pathCohomology_subsingleton F _ _ (by omega)

theorem pathCohomology_pairedPath_odd_unique (F : Type*) [CommRing F] (k j : ℕ)
    (hj : j ≠ 2 * k + 1) : Subsingleton (pathCohomology F (6 * k + 3) j) :=
  pathCohomology_subsingleton F _ _ (by omega)

theorem pathCohomology_pairedPath_even_unique (F : Type*) [CommRing F] (k j : ℕ)
    (hj : j ≠ 2 * k + 2) : Subsingleton (pathCohomology F (6 * k + 5) j) :=
  pathCohomology_subsingleton F _ _ (by omega)

/-- Every occupation `j ≥ 1` is realised by a pairing path. -/
theorem pathCohomology_pairedPath_covers (F : Type*) [CommRing F] (j : ℕ) (hj : 1 ≤ j) :
    ∃ e : ℕ, Nonempty (pathCohomology F (2 * e + 1) j ≃ₗ[F] F) := by
  rcases Nat.even_or_odd j with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨3 * r - 1, pathCohomology_nonempty_equiv F _ _ (Or.inr (by omega))⟩
  · exact ⟨3 * r + 1, pathCohomology_nonempty_equiv F _ _ (Or.inl (by omega))⟩

/-- The pairing length realising a given occupation is unique. -/
theorem pathCohomology_pairedPath_length_unique {e e' j : ℕ}
    (h : 2 * e + 1 = 3 * j ∨ 2 * e + 1 + 1 = 3 * j)
    (h' : 2 * e' + 1 = 3 * j ∨ 2 * e' + 1 + 1 = 3 * j) : e = e' := by omega

end
end GaloisForLFunctions.HTGeometry
