import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# The word-convolution Banach algebra `ℓ¹(A*; E)`

For a normed ring `E` and an alphabet `A`, the space `ℓ¹(A*; E)` of absolutely summable families
indexed by words carries the concatenation product

`(X * Y)_w = ∑_{u ++ v = w} X_u Y_v`,

with unit `1 ⊗ δ_∅`.  It is a Banach algebra (`‖XY‖ ≤ ‖X‖‖Y‖`), the completed projective tensor
product `E ⊗̂ ℓ¹(A*)`.  When `E` carries an isometric star, the word adjoint
`(X^*)_w = (X_{rev w})^*` is an isometric star-ring structure; a letter permutation together with
an isometric ring automorphism of `E` gives a continuous ring automorphism; the constant term is a
continuous ring homomorphism to `E`; and the word-length filtration is closed, multiplicative,
and the exponential of a filtration-one element agrees with its Taylor polynomials modulo the
filtration.
-/

noncomputable section

open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

/-! ## Ordered factorizations of a word -/

section Splits

variable {A : Type*}

/-- The `|w| + 1` ordered factorizations `w = u ++ v`. -/
def wordSplits (w : List A) : Finset (List A × List A) :=
  Finset.univ.map ⟨fun i : Fin (w.length + 1) => (w.take i, w.drop i), fun i j h => by
    have h1 := congrArg (fun p : List A × List A => p.1.length) h
    simp only [List.length_take] at h1
    have hi := i.2
    have hj := j.2
    ext
    omega⟩

theorem mem_wordSplits {w : List A} {p : List A × List A} : p ∈ wordSplits w ↔ p.1 ++ p.2 = w := by
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 h
    exact List.take_append_drop _ _
  · intro h
    refine Finset.mem_map.2 ⟨⟨p.1.length, by rw [← h, List.length_append]; omega⟩,
      Finset.mem_univ _, ?_⟩
    subst h
    simp

theorem wordSplits_nil : wordSplits ([] : List A) = {([], [])} := by
  ext p
  rw [mem_wordSplits, Finset.mem_singleton, List.append_eq_nil_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- The factorizations of all words together are all pairs of words. -/
def wordSplitsSigmaEquiv : (Σ w : List A, ↥(wordSplits w)) ≃ List A × List A where
  toFun x := x.2.1
  invFun p := ⟨p.1 ++ p.2, p, mem_wordSplits.2 rfl⟩
  left_inv := by
    rintro ⟨w, p, hp⟩
    have h := mem_wordSplits.1 hp
    subst h
    rfl
  right_inv _ := rfl

theorem hasSum_sum_wordSplits {f : List A × List A → ℝ} {s : ℝ} (hf : HasSum f s) :
    HasSum (fun w => ∑ p ∈ wordSplits w, f p) s := by
  have h : HasSum (f ∘ wordSplitsSigmaEquiv) s := (wordSplitsSigmaEquiv.hasSum_iff).2 hf
  refine h.sigma fun w => ?_
  have := hasSum_fintype (fun c : ↥(wordSplits w) => f c)
  rwa [Finset.sum_coe_sort] at this

end Splits

/-! ## Convolution of word families -/

section Conv

variable {A : Type*} {E : Type*} [Ring E]

/-- Concatenation convolution `(X * Y)_w = ∑_{u ++ v = w} X_u Y_v`. -/
def wordConv (X Y : List A → E) (w : List A) : E := ∑ p ∈ wordSplits w, X p.1 * Y p.2

/-- The unit family `1 ⊗ δ_∅`. -/
def wordUnit : List A → E
  | [] => 1
  | _ :: _ => 0

@[simp] theorem wordUnit_nil : (wordUnit ([] : List A) : E) = 1 := rfl

theorem wordUnit_of_ne_nil {w : List A} (hw : w ≠ []) : (wordUnit w : E) = 0 := by
  cases w with
  | nil => exact absurd rfl hw
  | cons _ _ => rfl

theorem wordConv_assoc (X Y Z : List A → E) :
    wordConv (wordConv X Y) Z = wordConv X (wordConv Y Z) := by
  funext w
  simp only [wordConv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨(x.2.1, x.2.2 ++ x.1.2), (x.2.2, x.1.2)⟩)
    (fun y _ => ⟨(y.1.1 ++ y.2.1, y.2.2), (y.1.1, y.2.1)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨u, v⟩, ⟨a, b⟩⟩ hx
    simp only [Finset.mem_sigma, mem_wordSplits] at hx ⊢
    exact ⟨by rw [← List.append_assoc, hx.2, hx.1], trivial⟩
  · rintro ⟨⟨a, r⟩, ⟨b, v⟩⟩ hy
    simp only [Finset.mem_sigma, mem_wordSplits] at hy ⊢
    exact ⟨by rw [List.append_assoc, hy.2, hy.1], trivial⟩
  · rintro ⟨⟨u, v⟩, ⟨a, b⟩⟩ hx
    simp only [Finset.mem_sigma, mem_wordSplits] at hx
    obtain ⟨-, rfl⟩ := hx
    rfl
  · rintro ⟨⟨a, r⟩, ⟨b, v⟩⟩ hy
    simp only [Finset.mem_sigma, mem_wordSplits] at hy
    obtain ⟨-, rfl⟩ := hy
    rfl
  · rintro ⟨⟨u, v⟩, ⟨a, b⟩⟩ _
    exact mul_assoc _ _ _

theorem wordConv_unit_left (Y : List A → E) : wordConv wordUnit Y = Y := by
  funext w
  rw [wordConv, Finset.sum_eq_single ([], w)]
  · simp
  · rintro ⟨u, v⟩ hp hne
    rw [mem_wordSplits] at hp
    have hu : u ≠ [] := by
      rintro rfl
      exact hne (by simp only [List.nil_append] at hp; rw [hp])
    simp [wordUnit_of_ne_nil hu]
  · intro h; exact absurd (mem_wordSplits.2 rfl) h

theorem wordConv_unit_right (X : List A → E) : wordConv X wordUnit = X := by
  funext w
  rw [wordConv, Finset.sum_eq_single (w, [])]
  · simp
  · rintro ⟨u, v⟩ hp hne
    rw [mem_wordSplits] at hp
    have hv : v ≠ [] := by
      rintro rfl
      exact hne (by simp only [List.append_nil] at hp; rw [hp])
    simp [wordUnit_of_ne_nil hv]
  · intro h; exact absurd (mem_wordSplits.2 (List.append_nil w)) h

theorem wordConv_add_left (X Y Z : List A → E) :
    wordConv (X + Y) Z = wordConv X Z + wordConv Y Z := by
  funext w
  simp only [wordConv, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem wordConv_add_right (X Y Z : List A → E) :
    wordConv X (Y + Z) = wordConv X Y + wordConv X Z := by
  funext w
  simp only [wordConv, Pi.add_apply, mul_add, Finset.sum_add_distrib]

end Conv

section NormedConv

variable {A : Type*} {E : Type*} [NormedRing E]

theorem norm_wordConv_le (X Y : List A → E) (w : List A) :
    ‖wordConv X Y w‖ ≤ ∑ p ∈ wordSplits w, ‖X p.1‖ * ‖Y p.2‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_mul_le _ _)

theorem summable_norm_iff_memℓp_one {X : List A → E} : Memℓp X 1 ↔ Summable fun w => ‖X w‖ := by
  rw [memℓp_gen_iff (by norm_num)]
  simp

theorem hasSum_wordConv_bound {X Y : List A → E} {a b : ℝ} (hX : HasSum (fun w => ‖X w‖) a)
    (hY : HasSum (fun w => ‖Y w‖) b) :
    HasSum (fun w => ∑ p ∈ wordSplits w, ‖X p.1‖ * ‖Y p.2‖) (a * b) := by
  refine hasSum_sum_wordSplits ?_
  exact hX.mul hY (hX.summable.mul_of_nonneg hY.summable (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _))

theorem memℓp_wordConv {X Y : List A → E} (hX : Memℓp X 1) (hY : Memℓp Y 1) :
    Memℓp (wordConv X Y) 1 := by
  rw [summable_norm_iff_memℓp_one] at hX hY ⊢
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_wordConv_le X Y)
    (hasSum_wordConv_bound hX.hasSum hY.hasSum).summable

theorem memℓp_wordUnit : Memℓp (wordUnit : List A → E) 1 := by
  rw [summable_norm_iff_memℓp_one]
  refine summable_of_ne_finset_zero (s := {[]}) fun w hw => ?_
  rw [Finset.mem_singleton] at hw
  rw [wordUnit_of_ne_nil hw, norm_zero]

end NormedConv

/-! ## The Banach algebra -/

variable (A : Type*) (E : Type*) [NormedRing E]

/-- The word-convolution algebra `ℓ¹(A*; E) = E ⊗̂ ℓ¹(A*)`. -/
def WordL1 : Type _ := ↥(lp (fun _ : List A => E) 1)

namespace WordL1

variable {A E}

instance : NormedAddCommGroup (WordL1 A E) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : List A => E) 1))

instance {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] : NormedSpace 𝕜 (WordL1 A E) :=
  inferInstanceAs (NormedSpace 𝕜 (lp (fun _ : List A => E) 1))

instance [CompleteSpace E] : CompleteSpace (WordL1 A E) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : List A => E) 1))

/-- The underlying `ℓ¹` family. -/
def toLp (X : WordL1 A E) : lp (fun _ : List A => E) 1 := X

instance : FunLike (WordL1 A E) (List A) E where
  coe X := (toLp X : List A → E)
  coe_injective _ _ h := Subtype.ext h

/-- Build an element from a summable family. -/
def mk (f : List A → E) (hf : Memℓp f 1) : WordL1 A E := (⟨f, hf⟩ : lp (fun _ : List A => E) 1)

@[simp] theorem mk_apply (f : List A → E) (hf : Memℓp f 1) (w : List A) : mk f hf w = f w := rfl

@[ext] theorem ext {X Y : WordL1 A E} (h : ∀ w, X w = Y w) : X = Y := DFunLike.ext _ _ h

theorem memℓp (X : WordL1 A E) : Memℓp X 1 := lp.memℓp (toLp X)

@[simp] theorem add_apply (X Y : WordL1 A E) (w : List A) : (X + Y) w = X w + Y w := rfl

@[simp] theorem zero_apply (w : List A) : (0 : WordL1 A E) w = 0 := rfl

@[simp] theorem neg_apply (X : WordL1 A E) (w : List A) : (-X) w = -X w := rfl

@[simp] theorem sub_apply (X Y : WordL1 A E) (w : List A) : (X - Y) w = X w - Y w := rfl

@[simp] theorem smul_apply {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] (c : 𝕜)
    (X : WordL1 A E) (w : List A) : (c • X) w = c • X w := rfl

/-- Evaluation at a word, as an additive homomorphism. -/
def evalAddMonoidHom (w : List A) : WordL1 A E →+ E where
  toFun X := X w
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sum_apply {ι : Type*} (s : Finset ι) (X : ι → WordL1 A E) (w : List A) :
    (∑ i ∈ s, X i) w = ∑ i ∈ s, X i w :=
  map_sum (evalAddMonoidHom w) X s

instance : Mul (WordL1 A E) := ⟨fun X Y => mk (wordConv X Y) (memℓp_wordConv X.memℓp Y.memℓp)⟩

instance : One (WordL1 A E) := ⟨mk wordUnit memℓp_wordUnit⟩

theorem mul_apply (X Y : WordL1 A E) (w : List A) :
    (X * Y) w = ∑ p ∈ wordSplits w, X p.1 * Y p.2 := rfl

theorem one_apply (w : List A) : (1 : WordL1 A E) w = wordUnit w := rfl

instance : Ring (WordL1 A E) :=
  { (inferInstance : AddCommGroup (WordL1 A E)) with
    mul_assoc := fun X Y Z => ext fun w => congrFun (wordConv_assoc X Y Z) w
    one_mul := fun Y => ext fun w => congrFun (wordConv_unit_left Y) w
    mul_one := fun X => ext fun w => congrFun (wordConv_unit_right X) w
    left_distrib := fun X Y Z => ext fun w => congrFun (wordConv_add_right X Y Z) w
    right_distrib := fun X Y Z => ext fun w => congrFun (wordConv_add_left X Y Z) w
    zero_mul := fun Y => ext fun w => by
      change ∑ p ∈ wordSplits w, (0 : WordL1 A E) p.1 * Y p.2 = 0
      simp
    mul_zero := fun X => ext fun w => by
      change ∑ p ∈ wordSplits w, X p.1 * (0 : WordL1 A E) p.2 = 0
      simp }

theorem norm_eq_tsum (X : WordL1 A E) : ‖X‖ = ∑' w, ‖X w‖ := by
  change ‖toLp X‖ = _
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]
  rfl

theorem hasSum_norm (X : WordL1 A E) : HasSum (fun w => ‖X w‖) ‖X‖ := by
  rw [norm_eq_tsum]
  exact (summable_norm_iff_memℓp_one.1 X.memℓp).hasSum

theorem norm_apply_le (X : WordL1 A E) (w : List A) : ‖X w‖ ≤ ‖X‖ :=
  lp.norm_apply_le_norm (by norm_num) (toLp X) w

theorem norm_mul_le' (X Y : WordL1 A E) : ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := by
  have hb := hasSum_wordConv_bound (hasSum_norm X) (hasSum_norm Y)
  rw [norm_eq_tsum]
  exact (summable_norm_iff_memℓp_one.1 (X * Y).memℓp).tsum_le_of_sum_le fun s =>
    (Finset.sum_le_sum fun w _ => norm_wordConv_le X Y w).trans
      (sum_le_hasSum s (fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg (norm_nonneg _) (norm_nonneg _)) hb)

instance : NormedRing (WordL1 A E) :=
  { (inferInstance : NormedAddCommGroup (WordL1 A E)), (inferInstance : Ring (WordL1 A E)) with
    norm_mul_le := norm_mul_le' }

section Algebra

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 E]

instance : NormedAlgebra 𝕜 (WordL1 A E) :=
  { Algebra.ofModule
      (fun r X Y => ext fun w => by
        change ∑ p ∈ wordSplits w, (r • X p.1) * Y p.2 = r • ∑ p ∈ wordSplits w, X p.1 * Y p.2
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun _ _ => smul_mul_assoc _ _ _)
      (fun r X Y => ext fun w => by
        change ∑ p ∈ wordSplits w, X p.1 * (r • Y p.2) = r • ∑ p ∈ wordSplits w, X p.1 * Y p.2
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun _ _ => mul_smul_comm _ _ _) with
    norm_smul_le := norm_smul_le }

end Algebra

/-! ## Elementary tensors -/

section Single

variable [DecidableEq A]

/-- The elementary tensor `T ⊗ δ_w`. -/
def single (w : List A) (T : E) : WordL1 A E := lp.single 1 w T

theorem single_apply (w : List A) (T : E) (v : List A) :
    single w T v = if v = w then T else 0 := by
  change (lp.single 1 w T : lp (fun _ : List A => E) 1) v = _
  simp [lp.single_apply, Pi.single_apply]

@[simp] theorem single_apply_self (w : List A) (T : E) : single w T w = T := by
  simp [single_apply]

@[simp] theorem single_zero (w : List A) : single w (0 : E) = 0 := by
  ext v; rw [single_apply]; split_ifs <;> rfl

theorem norm_single (w : List A) (T : E) : ‖single w T‖ = ‖T‖ := by
  rw [norm_eq_tsum]
  have h : (fun v => ‖single w T v‖) = fun v => if v = w then ‖T‖ else 0 := by
    funext v; rw [single_apply]; split_ifs <;> simp
  rw [h, tsum_ite_eq]

theorem single_add (w : List A) (T R : E) : single w (T + R) = single w T + single w R := by
  ext v
  simp only [add_apply, single_apply]
  split_ifs <;> simp

theorem single_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] (w : List A) (c : 𝕜) (T : E) :
    single w (c • T) = c • single w T := by
  ext v
  simp only [smul_apply, single_apply]
  split_ifs <;> simp

theorem single_mul_single (u v : List A) (T R : E) :
    single u T * single v R = single (u ++ v) (T * R) := by
  ext w
  rw [mul_apply]
  by_cases hw : w = u ++ v
  · subst hw
    rw [Finset.sum_eq_single (u, v)]
    · simp
    · rintro ⟨a, b⟩ hp hne
      rw [mem_wordSplits] at hp
      by_cases ha : a = u
      · subst ha
        have hb : b = v := List.append_cancel_left hp
        exact absurd (by rw [hb]) hne
      · simp [single_apply, ha]
    · intro h; exact absurd (mem_wordSplits.2 rfl) h
  · rw [single_apply, if_neg hw]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [mem_wordSplits] at hp
    by_cases ha : p.1 = u
    · by_cases hb : p.2 = v
      · exact absurd (by rw [← hp, ha, hb]) hw
      · simp [single_apply, hb]
    · simp [single_apply, ha]

/-- Every element is the `ℓ¹`-convergent sum of its elementary tensors,
`X = ∑_w X_w ⊗ δ_w`. -/
theorem hasSum_single (X : WordL1 A E) : HasSum (fun w => single w (X w)) X :=
  lp.hasSum_single (p := 1) ENNReal.one_ne_top (toLp X)

@[simp] theorem single_nil_one : single ([] : List A) (1 : E) = 1 := by
  ext v
  rw [single_apply, one_apply]
  cases v with
  | nil => simp
  | cons _ _ => simp [wordUnit]

end Single

/-! ## The constant term -/

/-- The constant term `X ↦ X_∅` is a ring homomorphism. -/
def constantTerm : WordL1 A E →+* E where
  toFun X := X []
  map_one' := rfl
  map_mul' X Y := by
    change ∑ p ∈ wordSplits [], X p.1 * Y p.2 = X [] * Y []
    rw [wordSplits_nil, Finset.sum_singleton]
  map_zero' := rfl
  map_add' _ _ := rfl

theorem constantTerm_apply (X : WordL1 A E) : constantTerm X = X [] := rfl

theorem continuous_constantTerm : Continuous (constantTerm : WordL1 A E → E) :=
  AddMonoidHomClass.continuous_of_bound (constantTerm : WordL1 A E →+* E) 1 fun X => by
    rw [one_mul]; exact norm_apply_le X []

/-! ## Reindexing by a bijection of words -/

theorem norm_comp_equiv (X : WordL1 A E) (e : List A ≃ List A) (φ : E → E)
    (hφ : ∀ x, ‖φ x‖ = ‖x‖) :
    HasSum (fun w => ‖φ (X (e w))‖) ‖X‖ := by
  have h := (e.hasSum_iff (f := fun w => ‖X w‖)).2 (hasSum_norm X)
  refine h.congr_fun fun w => ?_
  simp [hφ]

theorem memℓp_comp_equiv (X : WordL1 A E) (e : List A ≃ List A) (φ : E → E)
    (hφ : ∀ x, ‖φ x‖ = ‖x‖) : Memℓp (fun w => φ (X (e w))) 1 :=
  summable_norm_iff_memℓp_one.2 (norm_comp_equiv X e φ hφ).summable

/-- Word reversal as a bijection. -/
def reverseEquiv : List A ≃ List A :=
  Function.Involutive.toPerm List.reverse fun w => List.reverse_reverse w

/-- Letterwise relabelling as a bijection of words. -/
def mapEquiv (σ : A ≃ A) : List A ≃ List A where
  toFun := List.map σ
  invFun := List.map σ.symm
  left_inv w := by simp [List.map_map]
  right_inv w := by simp [List.map_map]

/-! ## The word adjoint -/

section Star

variable [StarRing E] [NormedStarGroup E]

instance : Star (WordL1 A E) :=
  ⟨fun X => mk (fun w => star (X w.reverse)) (memℓp_comp_equiv X reverseEquiv star norm_star)⟩

theorem star_apply (X : WordL1 A E) (w : List A) : (star X) w = star (X w.reverse) := rfl

theorem star_mul' (X Y : WordL1 A E) : star (X * Y) = star Y * star X := by
  ext w
  change star (∑ p ∈ wordSplits w.reverse, X p.1 * Y p.2) =
    ∑ q ∈ wordSplits w, star (Y q.1.reverse) * star (X q.2.reverse)
  rw [star_sum]
  refine Finset.sum_bij' (fun p _ => (p.2.reverse, p.1.reverse))
    (fun q _ => (q.2.reverse, q.1.reverse)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hp
    rw [mem_wordSplits] at hp ⊢
    simp only
    rw [← List.reverse_append, hp, List.reverse_reverse]
  · rintro ⟨u, v⟩ hq
    rw [mem_wordSplits] at hq ⊢
    simp only
    rw [← List.reverse_append, hq]
  · rintro ⟨u, v⟩ _; simp
  · rintro ⟨u, v⟩ _; simp
  · rintro ⟨u, v⟩ _
    simp [star_mul]

instance : StarRing (WordL1 A E) where
  star_involutive X := ext fun w => by simp [star_apply]
  star_mul := star_mul'
  star_add X Y := ext fun w => by simp [star_apply]

theorem norm_star' (X : WordL1 A E) : ‖star X‖ = ‖X‖ :=
  (hasSum_norm (star X)).unique (norm_comp_equiv X reverseEquiv star norm_star)

instance : NormedStarGroup (WordL1 A E) := ⟨fun X => (norm_star' X).le⟩

instance {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 E] [StarRing 𝕜] [StarModule 𝕜 E] :
    StarModule 𝕜 (WordL1 A E) :=
  ⟨fun r X => ext fun w => by simp [star_apply, star_smul]⟩

/-- **(DSR.4)** On elementary tensors, `(T ⊗ δ_w)^* = T^* ⊗ δ_{rev w}`. -/
theorem star_single [DecidableEq A] (w : List A) (T : E) :
    star (single w T) = single w.reverse (star T) := by
  ext v
  rw [star_apply, single_apply, single_apply]
  by_cases h : v = w.reverse
  · subst h; simp
  · have : v.reverse ≠ w := fun h' => h (by rw [← h', List.reverse_reverse])
    simp [h, this]

end Star

/-! ## Relabelling automorphisms -/

section Relabel

/-- The relabelling `(𝒞X)_w = φ(X_{σ⁻¹ w})` by a letter permutation `σ` and an isometric ring
endomorphism `φ` of the coefficients. -/
def relabel (σ : A ≃ A) (φ : E →+* E) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : WordL1 A E →+* WordL1 A E where
  toFun X := mk (fun w => φ (X (w.map σ.symm))) (memℓp_comp_equiv X (mapEquiv σ.symm) φ hφ)
  map_one' := ext fun w => by
    change φ (wordUnit (w.map σ.symm)) = wordUnit w
    cases w with
    | nil => simp
    | cons _ _ => simp [wordUnit]
  map_mul' X Y := ext fun w => by
    change φ (∑ p ∈ wordSplits (w.map σ.symm), X p.1 * Y p.2) =
      ∑ q ∈ wordSplits w, φ (X (q.1.map σ.symm)) * φ (Y (q.2.map σ.symm))
    rw [map_sum]
    refine Finset.sum_bij' (fun p _ => (p.1.map σ, p.2.map σ))
      (fun q _ => (q.1.map σ.symm, q.2.map σ.symm)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨u, v⟩ hp
      rw [mem_wordSplits] at hp ⊢
      simp only
      rw [← List.map_append, hp, List.map_map]
      simp
    · rintro ⟨u, v⟩ hq
      rw [mem_wordSplits] at hq ⊢
      simp only
      rw [← List.map_append, hq]
    · rintro ⟨u, v⟩ _; simp [List.map_map]
    · rintro ⟨u, v⟩ _; simp [List.map_map]
    · rintro ⟨u, v⟩ _
      simp [List.map_map, map_mul]
  map_zero' := ext fun w => by change φ 0 = 0; exact map_zero φ
  map_add' X Y := ext fun w => by
    change φ (X _ + Y _) = φ (X _) + φ (Y _)
    exact map_add φ _ _

theorem relabel_apply (σ : A ≃ A) (φ : E →+* E) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (X : WordL1 A E)
    (w : List A) : relabel σ φ hφ X w = φ (X (w.map σ.symm)) := rfl

theorem norm_relabel (σ : A ≃ A) (φ : E →+* E) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (X : WordL1 A E) :
    ‖relabel σ φ hφ X‖ = ‖X‖ :=
  (hasSum_norm _).unique (norm_comp_equiv X (mapEquiv σ.symm) φ hφ)

theorem continuous_relabel (σ : A ≃ A) (φ : E →+* E) (hφ : ∀ x, ‖φ x‖ = ‖x‖) :
    Continuous (relabel σ φ hφ) :=
  AddMonoidHomClass.continuous_of_bound (relabel σ φ hφ) 1 fun X => by
    rw [norm_relabel, one_mul]

theorem relabel_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E] (σ : A ≃ A) (φ : E →+* E)
    (hφ : ∀ x, ‖φ x‖ = ‖x‖) (hφs : ∀ (c : 𝕜) x, φ (c • x) = c • φ x) (c : 𝕜) (X : WordL1 A E) :
    relabel σ φ hφ (c • X) = c • relabel σ φ hφ X :=
  ext fun _ => hφs c _

theorem relabel_single [DecidableEq A] (σ : A ≃ A) (φ : E →+* E) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
    (w : List A) (T : E) : relabel σ φ hφ (single w T) = single (w.map σ) (φ T) := by
  ext v
  rw [relabel_apply, single_apply, single_apply]
  by_cases h : v = w.map σ
  · subst h; simp [List.map_map]
  · have : v.map σ.symm ≠ w := fun h' => h (by rw [← h', List.map_map]; simp)
    simp [h, this]

end Relabel

/-! ## The word-length filtration -/

section Filtration

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 E]

variable (𝕜) in
/-- `𝔅_{≥k}`: families vanishing on all words of length `< k`. -/
def filtration (k : ℕ) : Submodule 𝕜 (WordL1 A E) where
  carrier := {X | ∀ w : List A, w.length < k → X w = 0}
  add_mem' hX hY w hw := by
    rw [add_apply, hX w hw, hY w hw, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c X hX w hw := by
    rw [smul_apply, hX w hw, smul_zero]

theorem mem_filtration {k : ℕ} {X : WordL1 A E} :
    X ∈ filtration 𝕜 k ↔ ∀ w : List A, w.length < k → X w = 0 := Iff.rfl

theorem isClosed_filtration (k : ℕ) :
    IsClosed ((filtration 𝕜 k : Submodule 𝕜 (WordL1 A E)) : Set (WordL1 A E)) := by
  have : ((filtration 𝕜 k : Submodule 𝕜 (WordL1 A E)) : Set (WordL1 A E)) =
      ⋂ w ∈ {w : List A | w.length < k}, (fun X : WordL1 A E => X w) ⁻¹' {0} := by
    ext X; simp [mem_filtration]
  rw [this]
  refine isClosed_biInter fun w _ => isClosed_singleton.preimage ?_
  exact AddMonoidHomClass.continuous_of_bound
    (⟨⟨fun X : WordL1 A E => X w, rfl⟩, fun _ _ => rfl⟩ : WordL1 A E →+ E) 1
    fun X => by rw [one_mul]; exact norm_apply_le X w

theorem filtration_antitone {j k : ℕ} (h : j ≤ k) :
    filtration 𝕜 k ≤ (filtration 𝕜 j : Submodule 𝕜 (WordL1 A E)) :=
  fun _ hX w hw => hX w (lt_of_lt_of_le hw h)

theorem mul_mem_filtration {i j : ℕ} {X Y : WordL1 A E} (hX : X ∈ filtration 𝕜 i)
    (hY : Y ∈ filtration 𝕜 j) : X * Y ∈ filtration 𝕜 (i + j) := by
  intro w hw
  rw [mul_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [mem_wordSplits] at hp
  have hl : p.1.length + p.2.length = w.length := by rw [← hp, List.length_append]
  by_cases h1 : p.1.length < i
  · rw [hX _ h1, zero_mul]
  · rw [hY _ (by omega), mul_zero]

theorem one_mem_filtration_zero : (1 : WordL1 A E) ∈ filtration 𝕜 0 :=
  fun _ hw => absurd hw (Nat.not_lt_zero _)

theorem pow_mem_filtration {X : WordL1 A E} (hX : X ∈ filtration 𝕜 1) (n : ℕ) :
    X ^ n ∈ filtration 𝕜 n := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem_filtration_zero
  | succ n ih => rw [pow_succ]; exact mul_mem_filtration ih hX

end Filtration

/-! ## The exponential modulo the filtration -/

section Exp

variable {𝕜 : Type*} [RCLike 𝕜] [NormedAlgebra 𝕜 E] [CompleteSpace E]

/-- For `X ∈ 𝔅_{≥1}`, `exp X ≡ ∑_{k<n} X^k/k!` modulo `𝔅_{≥n}`. -/
theorem exp_sub_sum_mem_filtration {X : WordL1 A E} (hX : X ∈ filtration 𝕜 1) (n : ℕ) :
    NormedSpace.exp X - ∑ k ∈ Finset.range n, ((k.factorial : 𝕜))⁻¹ • X ^ k ∈ filtration 𝕜 n := by
  have he : NormedSpace.exp X = ∑' i, ((i.factorial : 𝕜))⁻¹ • X ^ i := by
    rw [NormedSpace.exp_eq_tsum 𝕜]
  rw [he]
  have hs := NormedSpace.expSeries_summable' (𝕂 := 𝕜) X
  rw [← hs.sum_add_tsum_nat_add n, add_sub_cancel_left]
  refine tsum_mem (isClosed_filtration n) fun i => ?_
  exact Submodule.smul_mem _ _ (filtration_antitone (Nat.le_add_left n i)
    (pow_mem_filtration hX (i + n)))

end Exp

end WordL1

end GaloisForLFunctions.HTGeometry
