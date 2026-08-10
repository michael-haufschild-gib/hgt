import GaloisForLFunctions.HTGeometry.OperatorSystemMatrixOrderUnit
import GaloisForLFunctions.HTGeometry.MatrixOrderedMap

/-!
# The order-unit norms of the matrix levels

Given a matrix ordering with a positive scalar-level order unit `e`, every matrix level carries the
order-unit bound

```text
‖x‖ₙ = inf {t > 0 : t · (1ₙ ⊗ e) ± x is positive at level n}.
```

The set of admissible bounds is never empty on self-adjoint elements — that is the content of
`isMatrixOrderUnit_of_levelOne` — so the infimum is a genuine nonnegative real, subadditive and
positively homogeneous.

Two structural laws, the ones that make this family a *matricial* norm rather than a sequence of
unrelated norms, are proved here from the compression axiom alone:

* `levelNorm_compress_le` — compression by an isometry `α* α = 1` is contractive;
* `levelNorm_fromBlocks` — `‖x ⊕ y‖ = max ‖x‖ ‖y‖`.

The second is Ruan's direct-sum axiom.  Its `≤` half comes from closure of the cones under direct
sums and the `≥` half from contractivity along the two coordinate isometries.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MatrixModule

universe u v

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V]
variable {C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)}

/-- The admissible order-unit bounds of `x` at level `n`. -/
def levelBounds (C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)) (e : V) (n : Type u)
    [Fintype n] [DecidableEq n] (x : Matrix n n V) : Set ℝ :=
  {t : ℝ | 0 < t ∧ (t : ℂ) • amplifyUnit n e - x ∈ C n ∧ (t : ℂ) • amplifyUnit n e + x ∈ C n}

/-- The order-unit bound of `x` at level `n`. -/
noncomputable def levelNorm (C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)) (e : V)
    (n : Type u) [Fintype n] [DecidableEq n] (x : Matrix n n V) : ℝ :=
  sInf (levelBounds C e n x)

omit [StarAddMonoid V] [StarModule ℂ V] in
theorem levelNorm_nonneg (e : V) (n : Type u) [Fintype n] [DecidableEq n] (x : Matrix n n V) :
    0 ≤ levelNorm C e n x :=
  Real.sInf_nonneg fun _ ht => ht.1.le

omit [StarAddMonoid V] [StarModule ℂ V] in
theorem bddBelow_levelBounds (e : V) (n : Type u) [Fintype n] [DecidableEq n] (x : Matrix n n V) :
    BddBelow (levelBounds C e n x) :=
  ⟨0, fun _ ht => ht.1.le⟩

omit [StarAddMonoid V] [StarModule ℂ V] in
theorem levelNorm_le_of_mem {e : V} {n : Type u} [Fintype n] [DecidableEq n] {x : Matrix n n V}
    {t : ℝ} (ht : t ∈ levelBounds C e n x) : levelNorm C e n x ≤ t :=
  csInf_le (bddBelow_levelBounds e n x) ht

namespace IsMatrixOrdering

variable (hC : IsMatrixOrdering C)

include hC

omit [StarModule ℂ V] in
/-- Admissible bounds are closed upwards. -/
theorem levelBounds_upward {e : V} (he : LevelOne C e) {n : Type u} [Fintype n] [DecidableEq n]
    {x : Matrix n n V} {t t' : ℝ} (ht : t ∈ levelBounds C e n x) (htt : t ≤ t') :
    t' ∈ levelBounds C e n x := by
  obtain ⟨htpos, h1, h2⟩ := ht
  refine ⟨lt_of_lt_of_le htpos htt, ?_, ?_⟩
  · have hadd := hC.add_mem n _ h1 _ (hC.smul_amplify_mem he (sub_nonneg.mpr htt))
    have hEq : ((t : ℂ) • amplifyUnit n e - x) + ((t' - t : ℝ) : ℂ) • amplifyUnit n e
        = (t' : ℂ) • amplifyUnit n e - x := by push_cast; module
    rwa [hEq] at hadd
  · have hadd := hC.add_mem n _ h2 _ (hC.smul_amplify_mem he (sub_nonneg.mpr htt))
    have hEq : ((t : ℂ) • amplifyUnit n e + x) + ((t' - t : ℝ) : ℂ) • amplifyUnit n e
        = (t' : ℂ) • amplifyUnit n e + x := by push_cast; module
    rwa [hEq] at hadd

theorem levelBounds_nonempty {e : V} (he : IsOrderUnitLevelOne C e) {n : Type u} [Fintype n]
    [DecidableEq n] {x : Matrix n n V} (hx : xᴴ = x) : (levelBounds C e n x).Nonempty := by
  obtain ⟨T, hT, h1, h2⟩ := hC.isMatrixOrderUnit_of_levelOne he x hx
  exact ⟨T, hT, h1, h2⟩

/-- Subadditivity of the order-unit bound. -/
theorem levelNorm_add_le {e : V} (he : IsOrderUnitLevelOne C e) {n : Type u} [Fintype n]
    [DecidableEq n] {x y : Matrix n n V} (hx : xᴴ = x) (hy : yᴴ = y) :
    levelNorm C e n (x + y) ≤ levelNorm C e n x + levelNorm C e n y := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  have hx' := hC.levelBounds_nonempty he hx
  have hy' := hC.levelBounds_nonempty he hy
  set a := levelNorm C e n x
  set b := levelNorm C e n y
  have hrab : r - (a + b) > 0 := by linarith
  obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hx' (show a < a + (r - (a + b)) / 2 by linarith)
  obtain ⟨u, hu, hult⟩ := exists_lt_of_csInf_lt hy' (show b < b + (r - (a + b)) / 2 by linarith)
  have hsum : s + u ∈ levelBounds C e n (x + y) := by
    obtain ⟨hs0, hs1, hs2⟩ := hs
    obtain ⟨hu0, hu1, hu2⟩ := hu
    refine ⟨by linarith, ?_, ?_⟩
    · have hadd := hC.add_mem n _ hs1 _ hu1
      have hEq : ((s : ℂ) • amplifyUnit n e - x) + ((u : ℂ) • amplifyUnit n e - y)
          = ((s + u : ℝ) : ℂ) • amplifyUnit n e - (x + y) := by push_cast; module
      rwa [hEq] at hadd
    · have hadd := hC.add_mem n _ hs2 _ hu2
      have hEq : ((s : ℂ) • amplifyUnit n e + x) + ((u : ℂ) • amplifyUnit n e + y)
          = ((s + u : ℝ) : ℂ) • amplifyUnit n e + (x + y) := by push_cast; module
      rwa [hEq] at hadd
  exact le_trans (levelNorm_le_of_mem hsum) (by linarith)

/-! ### Positive homogeneity -/

omit [StarModule ℂ V] in
theorem mem_levelBounds_smul {e : V} {n : Type u} [Fintype n] [DecidableEq n] {x : Matrix n n V}
    {c t : ℝ} (hc : 0 < c) (ht : t ∈ levelBounds C e n x) :
    c * t ∈ levelBounds C e n ((c : ℂ) • x) := by
  obtain ⟨h0, h1, h2⟩ := ht
  refine ⟨by positivity, ?_, ?_⟩
  · have h := hC.smul_mem n c hc.le h1
    have hEq : (c : ℂ) • ((t : ℂ) • amplifyUnit n e - x)
        = ((c * t : ℝ) : ℂ) • amplifyUnit n e - (c : ℂ) • x := by push_cast; module
    rwa [hEq] at h
  · have h := hC.smul_mem n c hc.le h2
    have hEq : (c : ℂ) • ((t : ℂ) • amplifyUnit n e + x)
        = ((c * t : ℝ) : ℂ) • amplifyUnit n e + (c : ℂ) • x := by push_cast; module
    rwa [hEq] at h

theorem levelNorm_smul {e : V} (he : IsOrderUnitLevelOne C e) {n : Type u} [Fintype n]
    [DecidableEq n] {x : Matrix n n V} (hx : xᴴ = x) {c : ℝ} (hc : 0 < c) :
    levelNorm C e n ((c : ℂ) • x) = c * levelNorm C e n x := by
  have hle : ∀ (y : Matrix n n V), yᴴ = y → ∀ d : ℝ, 0 < d →
      levelNorm C e n ((d : ℂ) • y) ≤ d * levelNorm C e n y := by
    intro y hy d hd
    refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
    have hlt : levelNorm C e n y < r / d := by
      rw [lt_div_iff₀ hd]
      linarith
    obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt (hC.levelBounds_nonempty he hy) hlt
    have h2 := levelNorm_le_of_mem (mem_levelBounds_smul hC hd ht)
    have h3 : d * t < d * (r / d) := mul_lt_mul_of_pos_left htlt hd
    have h4 : d * (r / d) = r := by field_simp
    linarith
  refine le_antisymm (hle x hx c hc) ?_
  have hxsa : ((c : ℂ) • x)ᴴ = (c : ℂ) • x := by
    rw [Matrix.conjTranspose_smul, hx]
    simp
  have h := hle _ hxsa c⁻¹ (by positivity)
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hc), Complex.ofReal_one,
    one_smul] at h
  have h5 := mul_le_mul_of_nonneg_left h hc.le
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul] at h5
  exact h5

/-! ### Contractivity along isometries -/

omit [StarModule ℂ V] in
theorem mem_levelBounds_compress {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {e : V} (α : Matrix n m ℂ) (hα : αᴴ * α = 1) {x : Matrix n n V} {t : ℝ}
    (ht : t ∈ levelBounds C e n x) : t ∈ levelBounds C e m (compress α x) := by
  obtain ⟨h0, h1, h2⟩ := ht
  refine ⟨h0, ?_, ?_⟩
  · have h := hC.compress_mem n m α _ h1
    rwa [compress_sub, compress_smul, compress_amplify_of_isometry α hα] at h
  · have h := hC.compress_mem n m α _ h2
    rwa [compress_add, compress_smul, compress_amplify_of_isometry α hα] at h

/-- **Compression by an isometry is contractive.** -/
theorem levelNorm_compress_le {m n : Type u} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {e : V} (he : IsOrderUnitLevelOne C e) (α : Matrix n m ℂ) (hα : αᴴ * α = 1)
    {x : Matrix n n V} (hx : xᴴ = x) :
    levelNorm C e m (compress α x) ≤ levelNorm C e n x :=
  le_csInf (hC.levelBounds_nonempty he hx) fun _ ht =>
    levelNorm_le_of_mem (mem_levelBounds_compress hC α hα ht)

/-! ### The direct-sum law -/

end IsMatrixOrdering

section Blocks

variable {m p : Type u} [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

omit [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V] [Fintype m] [Fintype p] in
theorem amplify_sum (e : V) :
    amplifyUnit (m ⊕ p) e = Matrix.fromBlocks (amplifyUnit m e) 0 0 (amplifyUnit p e) := by
  ext a b
  cases a <;> cases b <;> simp [amplifyUnit_apply]

/-- The isometry embedding the first summand. -/
def inclLeft : Matrix (m ⊕ p) m ℂ := Matrix.fromRows (1 : Matrix m m ℂ) (0 : Matrix p m ℂ)

/-- The isometry embedding the second summand. -/
def inclRight : Matrix (m ⊕ p) p ℂ := Matrix.fromRows (0 : Matrix m p ℂ) (1 : Matrix p p ℂ)

omit [DecidableEq p] in
theorem inclLeft_isometry :
    (inclLeft : Matrix (m ⊕ p) m ℂ)ᴴ * (inclLeft : Matrix (m ⊕ p) m ℂ) = 1 := by
  ext i j
  simp [inclLeft, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_apply,
    Matrix.one_apply, eq_comm]

omit [DecidableEq m] in
theorem inclRight_isometry :
    (inclRight : Matrix (m ⊕ p) p ℂ)ᴴ * (inclRight : Matrix (m ⊕ p) p ℂ) = 1 := by
  ext i j
  simp [inclRight, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_apply,
    Matrix.one_apply, eq_comm]

omit [StarAddMonoid V] [StarModule ℂ V] [DecidableEq p] in
theorem compress_inclLeft (x : Matrix m m V) (y : Matrix p p V) :
    compress inclLeft (Matrix.fromBlocks x 0 0 y) = x := by
  ext i j
  rw [compress_apply]
  have hinner : ∀ b : m ⊕ p,
      (∑ a : m ⊕ p, star ((inclLeft : Matrix (m ⊕ p) m ℂ) a i) • Matrix.fromBlocks x 0 0 y a b)
        = Matrix.fromBlocks x 0 0 y (Sum.inl i) b := by
    intro b
    rw [Fintype.sum_sum_type]
    have h1 : (∑ a : m, star ((inclLeft : Matrix (m ⊕ p) m ℂ) (Sum.inl a) i)
        • Matrix.fromBlocks x 0 0 y (Sum.inl a) b)
        = Matrix.fromBlocks x 0 0 y (Sum.inl i) b := by
      rw [Finset.sum_eq_single i]
      · simp [inclLeft]
      · intro a _ hai; simp [inclLeft, hai]
      · intro hb; exact absurd (Finset.mem_univ i) hb
    have h2 : (∑ a : p, star ((inclLeft : Matrix (m ⊕ p) m ℂ) (Sum.inr a) i)
        • Matrix.fromBlocks x 0 0 y (Sum.inr a) b) = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      simp [inclLeft]
    rw [h1, h2, add_zero]
  simp only [hinner]
  rw [Fintype.sum_sum_type]
  have h1 : (∑ b : m, (inclLeft : Matrix (m ⊕ p) m ℂ) (Sum.inl b) j
      • Matrix.fromBlocks x 0 0 y (Sum.inl i) (Sum.inl b)) = x i j := by
    rw [Finset.sum_eq_single j]
    · simp [inclLeft]
    · intro a _ haj; simp [inclLeft, haj]
    · intro hb; exact absurd (Finset.mem_univ j) hb
  have h2 : (∑ b : p, (inclLeft : Matrix (m ⊕ p) m ℂ) (Sum.inr b) j
      • Matrix.fromBlocks x 0 0 y (Sum.inl i) (Sum.inr b)) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [inclLeft]
  rw [h1, h2, add_zero]

omit [StarAddMonoid V] [StarModule ℂ V] [DecidableEq m] in
theorem compress_inclRight (x : Matrix m m V) (y : Matrix p p V) :
    compress inclRight (Matrix.fromBlocks x 0 0 y) = y := by
  ext i j
  rw [compress_apply]
  have hinner : ∀ b : m ⊕ p,
      (∑ a : m ⊕ p, star ((inclRight : Matrix (m ⊕ p) p ℂ) a i) • Matrix.fromBlocks x 0 0 y a b)
        = Matrix.fromBlocks x 0 0 y (Sum.inr i) b := by
    intro b
    rw [Fintype.sum_sum_type]
    have h1 : (∑ a : m, star ((inclRight : Matrix (m ⊕ p) p ℂ) (Sum.inl a) i)
        • Matrix.fromBlocks x 0 0 y (Sum.inl a) b) = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      simp [inclRight]
    have h2 : (∑ a : p, star ((inclRight : Matrix (m ⊕ p) p ℂ) (Sum.inr a) i)
        • Matrix.fromBlocks x 0 0 y (Sum.inr a) b)
        = Matrix.fromBlocks x 0 0 y (Sum.inr i) b := by
      rw [Finset.sum_eq_single i]
      · simp [inclRight]
      · intro a _ hai; simp [inclRight, hai]
      · intro hb; exact absurd (Finset.mem_univ i) hb
    rw [h1, h2, zero_add]
  simp only [hinner]
  rw [Fintype.sum_sum_type]
  have h1 : (∑ b : m, (inclRight : Matrix (m ⊕ p) p ℂ) (Sum.inl b) j
      • Matrix.fromBlocks x 0 0 y (Sum.inr i) (Sum.inl b)) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [inclRight]
  have h2 : (∑ b : p, (inclRight : Matrix (m ⊕ p) p ℂ) (Sum.inr b) j
      • Matrix.fromBlocks x 0 0 y (Sum.inr i) (Sum.inr b)) = y i j := by
    rw [Finset.sum_eq_single j]
    · simp [inclRight]
    · intro a _ haj; simp [inclRight, haj]
    · intro hb; exact absurd (Finset.mem_univ j) hb
  rw [h1, h2, zero_add]

namespace IsMatrixOrdering

variable (hC : IsMatrixOrdering C)

include hC

omit [StarModule ℂ V] in
theorem mem_levelBounds_fromBlocks {e : V} {x : Matrix m m V} {y : Matrix p p V} {t : ℝ}
    (hx : t ∈ levelBounds C e m x) (hy : t ∈ levelBounds C e p y) :
    t ∈ levelBounds C e (m ⊕ p) (Matrix.fromBlocks x 0 0 y) := by
  obtain ⟨h0, hx1, hx2⟩ := hx
  obtain ⟨-, hy1, hy2⟩ := hy
  refine ⟨h0, ?_, ?_⟩
  · have hb := hC.blockDiagonal_mem hx1 hy1
    have hEq : Matrix.fromBlocks ((t : ℂ) • amplifyUnit m e - x) 0 0 ((t : ℂ) • amplifyUnit p e - y)
        = (t : ℂ) • amplifyUnit (m ⊕ p) e - Matrix.fromBlocks x 0 0 y := by
      ext a b
      cases a <;> cases b <;> simp [amplifyUnit_apply]
    rwa [hEq] at hb
  · have hb := hC.blockDiagonal_mem hx2 hy2
    have hEq : Matrix.fromBlocks ((t : ℂ) • amplifyUnit m e + x) 0 0 ((t : ℂ) • amplifyUnit p e + y)
        = (t : ℂ) • amplifyUnit (m ⊕ p) e + Matrix.fromBlocks x 0 0 y := by
      ext a b
      cases a <;> cases b <;> simp [amplifyUnit_apply]
    rwa [hEq] at hb

/-- **Ruan's direct-sum law for the order-unit bounds.** -/
theorem levelNorm_fromBlocks {e : V} (he : IsOrderUnitLevelOne C e) {x : Matrix m m V}
    {y : Matrix p p V} (hx : xᴴ = x) (hy : yᴴ = y) :
    levelNorm C e (m ⊕ p) (Matrix.fromBlocks x 0 0 y)
      = max (levelNorm C e m x) (levelNorm C e p y) := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
    have hxr : levelNorm C e m x < r := lt_of_le_of_lt (le_max_left _ _) hr
    have hyr : levelNorm C e p y < r := lt_of_le_of_lt (le_max_right _ _) hr
    obtain ⟨tx, htx, htxlt⟩ := exists_lt_of_csInf_lt (hC.levelBounds_nonempty he hx) hxr
    obtain ⟨ty, hty, htylt⟩ := exists_lt_of_csInf_lt (hC.levelBounds_nonempty he hy) hyr
    have hrx : r ∈ levelBounds C e m x := hC.levelBounds_upward he.pos htx htxlt.le
    have hry : r ∈ levelBounds C e p y := hC.levelBounds_upward he.pos hty htylt.le
    exact levelNorm_le_of_mem (hC.mem_levelBounds_fromBlocks hrx hry)
  · have hsa : (Matrix.fromBlocks x 0 0 y)ᴴ = Matrix.fromBlocks x 0 0 y := by
      rw [Matrix.fromBlocks_conjTranspose, hx, hy]
      simp
    refine max_le ?_ ?_
    · have h := hC.levelNorm_compress_le he (inclLeft : Matrix (m ⊕ p) m ℂ) inclLeft_isometry hsa
      rwa [compress_inclLeft] at h
    · have h := hC.levelNorm_compress_le he (inclRight : Matrix (m ⊕ p) p ℂ) inclRight_isometry hsa
      rwa [compress_inclRight] at h

end IsMatrixOrdering

end Blocks

end GaloisForLFunctions.HTGeometry
