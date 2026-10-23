import GaloisForLFunctions.SignedArithmeticEnergyIncidence.BalancedIncidenceIsLocallyPayable

/-!
# Cycle holonomy decides balance on every incidence pattern

`TriangleHolonomyDecidesLocalPayment` reads balance off the triangles of a *complete* overlap
pattern.  A real incidence pattern has missing overlaps, and its orientation data are carried by
its walks.  A **walk** from `u` is a list of points, each distinct from and overlapping the
previous one (`IsWalkFrom`); its **holonomy** is the product of the edge signs `−c_xy/|c_xy|`,
which is `+1` on an aligned overlap and `−1` on an anti-aligned one (`walkHolonomy`).

* **Switching law** (`walkHolonomy_switch`): switching by `s` multiplies the holonomy of a walk
  from `u` to `v` by `s_u s_v`; aligned forms have holonomy `+1` on every walk.
* **Harary's criterion** (`isBalanced_iff_alignedCycles`): a symmetric form is balanced iff every
  closed walk has holonomy `+1`; equivalently (`isBalanced_iff_walkHolonomy_eq`) iff the holonomy
  of a walk depends only on its endpoints.  The aligning switching is the holonomy of chosen walks
  from one base point of each connected component.
* **Local–global consequence** (`nonneg_iff_locallyPayable_of_alignedCycles`): if every closed walk
  is aligned, nonnegativity and local payment coincide.
* **Triangles** (`walkHolonomy_triangle`): the holonomy of a closed triangle walk is
  `−sign(c_ij c_jk c_ki)`, so on complete patterns the triangle test is the cycle test.

The orientation datum of an arbitrary incidence source is thus the holonomy of its cycles.
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*}

/-- The sign of an overlap: `+1` if aligned (`c < 0`) or absent, `−1` if anti-aligned. -/
def edgeSign (c : ι → ι → ℝ) (x y : ι) : ℝ := if c x y = 0 then 1 else -(c x y / |c x y|)

/-- A walk from `u`: every listed point is distinct from and overlaps its predecessor. -/
def IsWalkFrom (c : ι → ι → ℝ) : ι → List ι → Prop
  | _, [] => True
  | u, y :: rest => u ≠ y ∧ c u y ≠ 0 ∧ IsWalkFrom c y rest

/-- The endpoint of a walk from `u`. -/
def walkEnd : ι → List ι → ι
  | u, [] => u
  | _, y :: rest => walkEnd y rest

/-- The holonomy of a walk from `u`: the product of its edge signs. -/
def walkHolonomy (c : ι → ι → ℝ) : ι → List ι → ℝ
  | _, [] => 1
  | u, y :: rest => edgeSign c u y * walkHolonomy c y rest

/-- Every closed walk is aligned. -/
def HasAlignedCycles (c : ι → ι → ℝ) : Prop :=
  ∀ u l, IsWalkFrom c u l → walkEnd u l = u → walkHolonomy c u l = 1

/-- Two points are joined by a walk. -/
def IsJoined (c : ι → ι → ℝ) (u v : ι) : Prop := ∃ l, IsWalkFrom c u l ∧ walkEnd u l = v

/-! ### Walk algebra -/

theorem edgeSign_symm {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (x y : ι) :
    edgeSign c x y = edgeSign c y x := by
  unfold edgeSign; rw [hc x y]

theorem edgeSign_sq (c : ι → ι → ℝ) (x y : ι) : edgeSign c x y ^ 2 = 1 := by
  unfold edgeSign
  split_ifs with h
  · norm_num
  · rw [neg_sq, div_pow, sq_abs, div_self (pow_ne_zero 2 h)]

theorem walkEnd_append (u : ι) (l₁ l₂ : List ι) :
    walkEnd u (l₁ ++ l₂) = walkEnd (walkEnd u l₁) l₂ := by
  induction l₁ generalizing u with
  | nil => rfl
  | cons y rest ih => exact ih y

theorem walkHolonomy_append (c : ι → ι → ℝ) (u : ι) (l₁ l₂ : List ι) :
    walkHolonomy c u (l₁ ++ l₂) = walkHolonomy c u l₁ * walkHolonomy c (walkEnd u l₁) l₂ := by
  induction l₁ generalizing u with
  | nil => simp only [List.nil_append, walkHolonomy, walkEnd, one_mul]
  | cons y rest ih =>
    simp only [List.cons_append, walkHolonomy, walkEnd]
    rw [ih y, mul_assoc]

theorem isWalkFrom_append (c : ι → ι → ℝ) (u : ι) (l₁ l₂ : List ι) :
    IsWalkFrom c u (l₁ ++ l₂) ↔ IsWalkFrom c u l₁ ∧ IsWalkFrom c (walkEnd u l₁) l₂ := by
  induction l₁ generalizing u with
  | nil => simp only [List.nil_append, IsWalkFrom, walkEnd, true_and]
  | cons y rest ih =>
    simp only [List.cons_append, IsWalkFrom, walkEnd]
    rw [ih y, and_assoc, and_assoc]

theorem walkHolonomy_sq (c : ι → ι → ℝ) (u : ι) (l : List ι) : walkHolonomy c u l ^ 2 = 1 := by
  induction l generalizing u with
  | nil => simp only [walkHolonomy, one_pow]
  | cons y rest ih => rw [walkHolonomy, mul_pow, edgeSign_sq, ih y, one_mul]

/-- Every walk can be reversed, with the same holonomy. -/
theorem exists_reverse_walk {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (u : ι) (l : List ι)
    (hl : IsWalkFrom c u l) :
    ∃ l' : List ι, IsWalkFrom c (walkEnd u l) l' ∧ walkEnd (walkEnd u l) l' = u ∧
      walkHolonomy c (walkEnd u l) l' = walkHolonomy c u l := by
  induction l generalizing u with
  | nil => exact ⟨[], trivial, rfl, rfl⟩
  | cons y rest ih =>
    obtain ⟨huy, hcuy, hrest⟩ := hl
    obtain ⟨l'', hw, hend, hhol⟩ := ih y hrest
    refine ⟨l'' ++ [u], ?_, ?_, ?_⟩
    · show IsWalkFrom c (walkEnd y rest) (l'' ++ [u])
      rw [isWalkFrom_append, hend]
      exact ⟨hw, Ne.symm huy, by rw [hc y u]; exact hcuy, trivial⟩
    · show walkEnd (walkEnd y rest) (l'' ++ [u]) = u
      rw [walkEnd_append, hend]; rfl
    · show walkHolonomy c (walkEnd y rest) (l'' ++ [u]) = edgeSign c u y * walkHolonomy c y rest
      rw [walkHolonomy_append, hend, hhol]
      simp only [walkHolonomy, mul_one]
      rw [edgeSign_symm hc y u, mul_comm]

/-- Joined-ness is an equivalence relation on a symmetric pattern: its classes are the connected
components of the overlap graph. -/
def joinedSetoid {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) : Setoid ι where
  r := IsJoined c
  iseqv :=
    { refl := fun u => ⟨[], trivial, rfl⟩
      symm := fun {u v} ⟨l, hl, he⟩ => by
        obtain ⟨l', hl', he', -⟩ := exists_reverse_walk hc u l hl
        rw [he] at hl' he'
        exact ⟨l', hl', he'⟩
      trans := fun {u v w} ⟨l₁, h₁, e₁⟩ ⟨l₂, h₂, e₂⟩ =>
        ⟨l₁ ++ l₂, (isWalkFrom_append c u l₁ l₂).2 ⟨h₁, e₁ ▸ h₂⟩,
          by rw [walkEnd_append, e₁, e₂]⟩ }

/-! ### Switching -/

theorem abs_eq_one_of_sq {s : ℝ} (hs : s ^ 2 = 1) : |s| = 1 :=
  (pow_eq_one_iff_of_nonneg (abs_nonneg s) two_ne_zero).1 (by rw [sq_abs]; exact hs)

/-- Switching multiplies the sign of an existing overlap by `s_x s_y`. -/
theorem edgeSign_switch {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) {c : ι → ι → ℝ} {x y : ι}
    (h : c x y ≠ 0) : edgeSign (switchCoupling s c) x y = s x * s y * edgeSign c x y := by
  have hsx : s x ≠ 0 := fun h0 => by have := hs x; rw [h0] at this; norm_num at this
  have hsy : s y ≠ 0 := fun h0 => by have := hs y; rw [h0] at this; norm_num at this
  unfold edgeSign switchCoupling
  rw [if_neg (mul_ne_zero (mul_ne_zero hsx hsy) h), if_neg h, abs_mul, abs_mul,
    abs_eq_one_of_sq (hs x), abs_eq_one_of_sq (hs y), one_mul, one_mul]
  ring

/-- Switching by signs preserves walks. -/
theorem IsWalkFrom.switch {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) {c : ι → ι → ℝ} (u : ι)
    (l : List ι) (hl : IsWalkFrom c u l) : IsWalkFrom (switchCoupling s c) u l := by
  induction l generalizing u with
  | nil => trivial
  | cons y rest ih =>
    obtain ⟨huy, hcuy, hrest⟩ := hl
    have hsu : s u ≠ 0 := fun h0 => by have := hs u; rw [h0] at this; norm_num at this
    have hsy : s y ≠ 0 := fun h0 => by have := hs y; rw [h0] at this; norm_num at this
    exact ⟨huy, mul_ne_zero (mul_ne_zero hsu hsy) hcuy, ih y hrest⟩

/-- **Switching multiplies holonomy by the end signs**: for a walk from `u` to `v`,
`hol_{switch s c} = s_u s_v · hol_c`. -/
theorem walkHolonomy_switch {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) (c : ι → ι → ℝ) (u : ι)
    (l : List ι) (hl : IsWalkFrom c u l) :
    walkHolonomy (switchCoupling s c) u l = s u * s (walkEnd u l) * walkHolonomy c u l := by
  induction l generalizing u with
  | nil =>
    simp only [walkHolonomy, walkEnd, mul_one]
    rw [← sq, hs u]
  | cons y rest ih =>
    obtain ⟨-, hcuy, hrest⟩ := hl
    simp only [walkHolonomy, walkEnd]
    rw [edgeSign_switch hs hcuy, ih y hrest]
    calc s u * s y * edgeSign c u y * (s y * s (walkEnd y rest) * walkHolonomy c y rest)
        = s u * s y ^ 2 * s (walkEnd y rest) * (edgeSign c u y * walkHolonomy c y rest) := by
          ring
      _ = _ := by rw [hs y, mul_one]

/-- On an aligned form every walk has holonomy `+1`. -/
theorem walkHolonomy_eq_one_of_aligned {c : ι → ι → ℝ} (hz : HasNonpositiveOverlaps c)
    (u : ι) (l : List ι) (hl : IsWalkFrom c u l) : walkHolonomy c u l = 1 := by
  induction l generalizing u with
  | nil => rfl
  | cons y rest ih =>
    obtain ⟨huy, hcuy, hrest⟩ := hl
    have hneg : c u y < 0 := lt_of_le_of_ne (hz u y huy) hcuy
    rw [walkHolonomy, ih y hrest, mul_one, edgeSign, if_neg hcuy, abs_of_neg hneg, div_neg,
      neg_neg, div_self hcuy]

/-! ### Harary's criterion -/

/-- Balanced forms have aligned cycles. -/
theorem alignedCycles_of_isBalanced {c : ι → ι → ℝ} (hb : IsBalanced c) : HasAlignedCycles c := by
  obtain ⟨s, hs, hz⟩ := hb
  intro u l hl hend
  have h1 := walkHolonomy_eq_one_of_aligned hz u l (hl.switch hs u l)
  rwa [walkHolonomy_switch hs c u l hl, hend, ← sq, hs u, one_mul] at h1

/-- Aligned cycles make a form balanced: the switching is the holonomy of chosen walks from a
base point of each component. -/
theorem isBalanced_of_alignedCycles {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (h : HasAlignedCycles c) : IsBalanced c := by
  classical
  let S := joinedSetoid hc
  -- a base point `r i` of the component of `i`, joined to `i`, constant along walks
  obtain ⟨r, hr, hrr⟩ : ∃ r : ι → ι, (∀ i, ∃ l, IsWalkFrom c (r i) l ∧ walkEnd (r i) l = i) ∧
      ∀ i j, IsJoined c i j → r i = r j :=
    ⟨fun i => (Quotient.mk S i).out, fun i => Quotient.mk_out (s := S) i,
      fun i j hij => congrArg Quotient.out (Quotient.sound (s := S) hij)⟩
  choose w hw hwe using hr
  refine ⟨fun i => walkHolonomy c (r i) (w i), fun i => walkHolonomy_sq _ _ _, ?_⟩
  intro i j hij
  show walkHolonomy c (r i) (w i) * walkHolonomy c (r j) (w j) * c i j ≤ 0
  by_cases h0 : c i j = 0
  · rw [h0, mul_zero]
  have hrij : r i = r j := hrr i j ⟨[j], ⟨hij, h0, trivial⟩, rfl⟩
  -- close the walk `r → i → j → r` with the reverse of the walk to `j`
  obtain ⟨l', hl', hend', hhol'⟩ := exists_reverse_walk hc (r j) (w j) (hw j)
  rw [hwe j] at hl' hend' hhol'
  have hwalk : IsWalkFrom c (r i) (w i ++ j :: l') := by
    rw [isWalkFrom_append, hwe i]
    exact ⟨hw i, hij, h0, hl'⟩
  have hclosed : walkEnd (r i) (w i ++ j :: l') = r i := by
    rw [walkEnd_append, hwe i]
    show walkEnd j l' = r i
    rw [hend', hrij]
  have h1 := h (r i) _ hwalk hclosed
  rw [walkHolonomy_append, hwe i] at h1
  change walkHolonomy c (r i) (w i) * (edgeSign c i j * walkHolonomy c j l') = 1 at h1
  rw [hhol'] at h1
  set a := walkHolonomy c (r i) (w i)
  set b := walkHolonomy c (r j) (w j)
  -- `a b e = 1` with `e² = 1` gives `a b = e`
  have hab : a * b = edgeSign c i j :=
    calc a * b = a * b * edgeSign c i j ^ 2 := by rw [edgeSign_sq, mul_one]
      _ = a * (edgeSign c i j * b) * edgeSign c i j := by ring
      _ = edgeSign c i j := by rw [h1, one_mul]
  rw [hab, edgeSign, if_neg h0, neg_mul, neg_nonpos, div_mul_eq_mul_div]
  exact div_nonneg (mul_self_nonneg _) (abs_nonneg _)

/-- **Harary's criterion**: a symmetric form is balanced iff every closed walk is aligned. -/
theorem isBalanced_iff_alignedCycles {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) :
    IsBalanced c ↔ HasAlignedCycles c :=
  ⟨alignedCycles_of_isBalanced, isBalanced_of_alignedCycles hc⟩

/-- Aligned cycles mean the holonomy of a walk depends only on its endpoints. -/
theorem alignedCycles_iff_walkHolonomy_eq {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) :
    HasAlignedCycles c ↔ ∀ u l₁ l₂, IsWalkFrom c u l₁ → IsWalkFrom c u l₂ →
      walkEnd u l₁ = walkEnd u l₂ → walkHolonomy c u l₁ = walkHolonomy c u l₂ := by
  constructor
  · intro h u l₁ l₂ h₁ h₂ he
    obtain ⟨l', hl', hend', hhol'⟩ := exists_reverse_walk hc u l₂ h₂
    rw [← he] at hl' hend' hhol'
    have h1 := h u (l₁ ++ l') ((isWalkFrom_append c u l₁ l').2 ⟨h₁, hl'⟩)
      (by rw [walkEnd_append, hend'])
    rw [walkHolonomy_append, hhol'] at h1
    calc walkHolonomy c u l₁ = walkHolonomy c u l₁ * walkHolonomy c u l₂ ^ 2 := by
          rw [walkHolonomy_sq, mul_one]
      _ = walkHolonomy c u l₁ * walkHolonomy c u l₂ * walkHolonomy c u l₂ := by ring
      _ = walkHolonomy c u l₂ := by rw [h1, one_mul]
  · intro h u l hl hend
    exact h u l [] hl trivial hend

/-- **Harary's criterion, path form**: a symmetric form is balanced iff walk holonomy depends only
on the endpoints. -/
theorem isBalanced_iff_walkHolonomy_eq {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) :
    IsBalanced c ↔ ∀ u l₁ l₂, IsWalkFrom c u l₁ → IsWalkFrom c u l₂ →
      walkEnd u l₁ = walkEnd u l₂ → walkHolonomy c u l₁ = walkHolonomy c u l₂ :=
  (isBalanced_iff_alignedCycles hc).trans (alignedCycles_iff_walkHolonomy_eq hc)

/-- **Local–global principle on aligned cycles**: when every closed walk is aligned,
nonnegativity is equivalent to local payment. -/
theorem nonneg_iff_locallyPayable_of_alignedCycles [Fintype ι] [DecidableEq ι]
    {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (h : HasAlignedCycles c) :
    (∀ f, 0 ≤ incidenceEnergy c f) ↔ LocallyPayable c :=
  nonneg_iff_locallyPayable_of_isBalanced hc (isBalanced_of_alignedCycles hc h)

/-- The holonomy of the closed triangle walk `i → j → k → i` is `−sign(c_ij c_jk c_ki)`. -/
theorem walkHolonomy_triangle {c : ι → ι → ℝ} {i j k : ι} (hij : c i j ≠ 0) (hjk : c j k ≠ 0)
    (hki : c k i ≠ 0) :
    walkHolonomy c i [j, k, i] =
      -(c i j * c j k * c k i / |c i j * c j k * c k i|) := by
  simp only [walkHolonomy, edgeSign, if_neg hij, if_neg hjk, if_neg hki, abs_mul, mul_one]
  ring

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
