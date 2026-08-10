import GaloisForLFunctions.HTGeometry.MatrixOrderedSpace

/-!
# An order unit is automatically a matrix order unit

An operator system is usually defined as a matrix-ordered `*`-vector space carrying an *Archimedean
matrix order unit*: a vector `e` whose amplifications `1ₙ ⊗ e` dominate every self-adjoint element
of every matrix level.  This module shows that the matrix requirement is redundant: an order unit
for the scalar level is automatically an order unit for every level, so only the scalar-level
condition has to be checked.

The mechanism is that the compression axiom already produces every *rank-one tensor*
`(conj wᵢ · wⱼ) • u` of a scalar-level positive `u`, hence every `A ⊗ u` with `A` positive
semidefinite.  Polarising the four vectors `δ₀ ± δ₁` and `δ₀ ± i δ₁` inside a single `2 × 2` level
bounds the symmetrised pair `[[0, u], [u*, 0]]`; one further compression transports that bound into
an arbitrary pair of positions, and summing over all pairs bounds the matrix itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MatrixModule

universe u v

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The rank-one tensor `(conj wᵢ · wⱼ) • u`. -/
def rankOneTensor {n : Type u} (w : n → ℂ) (u : V) : Matrix n n V :=
  Matrix.of fun i j => (star (w i) * w j) • u

@[simp]
theorem rankOneTensor_apply {n : Type u} (w : n → ℂ) (u : V) (i j : n) :
    rankOneTensor w u i j = (star (w i) * w j) • u := rfl

/-- A rank-one tensor is a compression of the scalar level. -/
theorem rankOneTensor_eq_compress {n : Type u} (w : n → ℂ) (u : V) :
    compress (Matrix.of fun (_ : PUnit.{u + 1}) (i : n) => w i)
        (Matrix.of fun (_ _ : PUnit.{u + 1}) => u) = rankOneTensor w u := by
  ext i j
  rw [compress_apply]
  simp only [Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, rankOneTensor_apply,
    smul_smul]
  rw [mul_comm]

variable [StarAddMonoid V] [StarModule ℂ V]

/-- Positivity at the scalar level. -/
def LevelOne (C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)) (u : V) : Prop :=
  (Matrix.of fun (_ _ : PUnit.{u + 1}) => u) ∈ C PUnit.{u + 1}

namespace IsMatrixOrdering

variable {C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)} (hC : IsMatrixOrdering C)

include hC

omit [StarModule ℂ V] in
/-- **Every rank-one tensor of a scalar-level positive is positive.** -/
theorem rankOneTensor_mem {n : Type u} [Fintype n] (w : n → ℂ) {u : V} (hu : LevelOne C u) :
    rankOneTensor w u ∈ C n := by
  have h := hC.compress_mem PUnit.{u + 1} n (Matrix.of fun (_ : PUnit.{u + 1}) (i : n) => w i) _ hu
  rwa [rankOneTensor_eq_compress] at h

omit [StarModule ℂ V] in
/-- A nonnegatively weighted diagonal tensor is positive. -/
theorem diagWeight_mem {n : Type u} [Fintype n] [DecidableEq n] (c : n → ℝ) (hc : ∀ k, 0 ≤ c k)
    {u : V} (hu : LevelOne C u) :
    (Matrix.of fun a b => if a = b then ((c a : ℂ)) • u else 0) ∈ C n := by
  classical
  have hsum : ∀ s : Finset n,
      (∑ k ∈ s, rankOneTensor (fun a => if a = k then ((Real.sqrt (c k) : ℝ) : ℂ) else 0) u)
        = Matrix.of fun a b => if a = b then (if a ∈ s then ((c a : ℂ)) • u else 0) else 0 := by
    intro s
    induction s using Finset.induction with
    | empty => ext a b; simp
    | insert k s hk ih =>
        rw [Finset.sum_insert hk, ih]
        ext a b
        by_cases hab : a = b
        · subst hab
          by_cases hak : a = k
          · subst hak
            have : ((Real.sqrt (c a) : ℝ) : ℂ) * ((Real.sqrt (c a) : ℝ) : ℂ) = ((c a : ℂ)) := by
              rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc a)]
            simp [rankOneTensor, hk, this]
          · simp [rankOneTensor, hak, Finset.mem_insert]
        · by_cases hbk : b = k
          · have hak : a ≠ k := by rintro rfl; exact hab hbk.symm
            simp [rankOneTensor, hab, hak]
          · simp [rankOneTensor, hab, hbk]
  have hmem : ∀ s : Finset n,
      (Matrix.of fun a b => if a = b then (if a ∈ s then ((c a : ℂ)) • u else 0) else 0) ∈ C n := by
    intro s
    rw [← hsum s]
    induction s using Finset.induction with
    | empty =>
        have : (∑ k ∈ (∅ : Finset n),
            rankOneTensor (fun a => if a = k then ((Real.sqrt (c k) : ℝ) : ℂ) else 0) u)
              = (0 : Matrix n n V) := by simp
        rw [this]
        exact hC.zero_mem n
    | insert k s hk ih =>
        rw [Finset.sum_insert hk]
        exact hC.add_mem n _ (hC.rankOneTensor_mem _ hu) _ ih
  have := hmem Finset.univ
  simpa using this

end IsMatrixOrdering

/-! ## Matrix units and polarisation -/

variable {n : Type u} [DecidableEq n]

/-- The matrix with `u` in position `(i, j)` and zeros elsewhere. -/
def unitEntry (i j : n) (u : V) : Matrix n n V :=
  Matrix.of fun a b => if a = i ∧ b = j then u else 0

/-- The vector `δᵢ + θ δⱼ`. -/
def polVec (i j : n) (θ : ℂ) : n → ℂ :=
  fun p => (if p = i then (1 : ℂ) else 0) + (if p = j then θ else 0)

omit [StarAddMonoid V] [StarModule ℂ V] in
/-- The rank-one tensor along a single coordinate is a single matrix entry. -/
theorem rankOneTensor_single (i : n) (u : V) :
    rankOneTensor (fun p => if p = i then (1 : ℂ) else 0) u = unitEntry i i u := by
  ext p q
  by_cases hpi : p = i <;> by_cases hqi : q = i <;> simp [rankOneTensor, unitEntry, hpi, hqi]

omit [StarAddMonoid V] [StarModule ℂ V] in
/-- **The polarisation identity.**  Averaging the four rank-one tensors along `δᵢ ± δⱼ` and
`δᵢ ± i δⱼ` cancels every off-diagonal contribution except the symmetrised entry pair, and leaves
exactly the two order-unit terms on the diagonal. -/
theorem polarization_identity {i j : n} (hij : i ≠ j) (e a b : V) (t s : ℝ) :
    (2 : ℂ)⁻¹ • (rankOneTensor (polVec i j 1) ((t : ℂ) • e - a)
        + rankOneTensor (polVec i j (-1)) ((t : ℂ) • e + a)
        + rankOneTensor (polVec i j Complex.I) ((s : ℂ) • e - b)
        + rankOneTensor (polVec i j (-Complex.I)) ((s : ℂ) • e + b))
      = unitEntry i i (((t + s : ℝ) : ℂ) • e) + unitEntry j j (((t + s : ℝ) : ℂ) • e)
        - unitEntry i j (a + Complex.I • b) - unitEntry j i (a - Complex.I • b) := by
  have hji : j ≠ i := Ne.symm hij
  ext p q
  by_cases hpi : p = i <;> by_cases hpj : p = j <;> by_cases hqi : q = i <;>
      by_cases hqj : q = j <;>
    simp_all [rankOneTensor, unitEntry, polVec, Complex.ofReal_add, Complex.conj_I,
      Complex.I_mul_I] <;>
    module

/-! ## The symmetrised entry pair -/

/-- The symmetrised entry pair of `x` at `(i, j)`. -/
def pairTerm (x : Matrix n n V) (i j : n) : Matrix n n V :=
  unitEntry i j (x i j) + unitEntry j i (x j i)

omit [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V] in
/-- Summing the symmetrised entry pairs over all ordered index pairs recovers `x` twice. -/
theorem sum_pairTerm [Fintype n] (x : Matrix n n V) :
    (∑ p : n × n, pairTerm x p.1 p.2) = x + x := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [pairTerm, Matrix.add_apply, unitEntry, Matrix.of_apply]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single (a, b)]
    · simp
    · rintro ⟨c, d⟩ _ hcd
      simp only [ite_eq_right_iff, and_imp]
      rintro rfl rfl
      exact absurd rfl hcd
    · intro hb; exact absurd (Finset.mem_univ (a, b)) hb
  · rw [Finset.sum_eq_single (b, a)]
    · simp
    · rintro ⟨c, d⟩ _ hcd
      simp only [ite_eq_right_iff, and_imp]
      rintro rfl rfl
      exact absurd rfl hcd
    · intro hb; exact absurd (Finset.mem_univ (b, a)) hb

omit [StarAddMonoid V] [StarModule ℂ V] in
/-- The difference between twice the amplified unit and the two diagonal order-unit entries is a
nonnegatively weighted diagonal tensor. -/
theorem amplify_sub_two_unitEntry [Fintype n] (i j : n) (e : V) (τ : ℝ) :
    ((2 * τ : ℝ) : ℂ) • amplifyUnit n e - unitEntry i i ((τ : ℂ) • e) - unitEntry j j ((τ : ℂ) • e)
      = Matrix.of fun a b => if a = b then
          (((2 * τ - (if a = i then τ else 0) - (if a = j then τ else 0) : ℝ)) : ℂ) • e else 0 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases hai : a = i <;> by_cases haj : a = j <;>
      simp [amplifyUnit_apply, unitEntry, hai, haj, Complex.ofReal_sub, Complex.ofReal_mul,
        sub_smul, Complex.ofReal_ofNat]
  · have h1 : ¬(a = i ∧ b = i) := fun h => hab (h.1.trans h.2.symm)
    have h2 : ¬(a = j ∧ b = j) := fun h => hab (h.1.trans h.2.symm)
    simp [amplifyUnit_apply, unitEntry, hab, h1, h2]

/-! ## The order-unit hypothesis at the scalar level -/

/-- An order unit for the scalar level of a matrix ordering. -/
structure IsOrderUnitLevelOne (C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)) (e : V) :
    Prop where
  /-- The unit is positive. -/
  pos : LevelOne C e
  /-- Every self-adjoint vector is dominated by a multiple of the unit. -/
  bound : ∀ v : V, star v = v → ∃ t : ℝ, 0 < t ∧ LevelOne C ((t : ℂ) • e - v) ∧
    LevelOne C ((t : ℂ) • e + v)

/-! ## Self-adjoint decomposition -/

/-- The self-adjoint real part of a vector. -/
noncomputable def rePart (u : V) : V := ((2 : ℂ)⁻¹) • (u + star u)

/-- The self-adjoint imaginary part of a vector. -/
noncomputable def imPart (u : V) : V := (((2 : ℂ) * Complex.I)⁻¹) • (u - star u)

theorem star_rePart (u : V) : star (rePart u) = rePart u := by
  simp only [rePart, star_smul, star_add, star_star, Complex.star_def, map_inv₀, map_ofNat]
  rw [add_comm]

theorem star_imPart (u : V) : star (imPart u) = imPart u := by
  simp only [imPart, star_smul, star_sub, star_star, Complex.star_def, map_inv₀, map_mul,
    map_ofNat, Complex.conj_I]
  rw [mul_neg, inv_neg, neg_smul, ← smul_neg, neg_sub]

private theorem I_mul_two_I_inv : Complex.I * ((2 : ℂ) * Complex.I)⁻¹ = (2 : ℂ)⁻¹ := by
  field_simp

omit [StarModule ℂ V] in
theorem rePart_add_I_imPart (u : V) : rePart u + Complex.I • imPart u = u := by
  rw [rePart, imPart, smul_smul, I_mul_two_I_inv, ← smul_add]
  rw [show u + star u + (u - star u) = (2 : ℂ) • u by
    rw [two_smul]; abel]
  rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

omit [StarModule ℂ V] in
theorem rePart_sub_I_imPart (u : V) : rePart u - Complex.I • imPart u = star u := by
  rw [rePart, imPart, smul_smul, I_mul_two_I_inv, ← smul_sub]
  rw [show u + star u - (u - star u) = (2 : ℂ) • star u by
    rw [two_smul]; abel]
  rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

omit [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V] in
@[simp]
theorem unitEntry_add (i j : n) (u v : V) :
    unitEntry i j (u + v) = unitEntry i j u + unitEntry i j v := by
  ext a b; by_cases h : a = i ∧ b = j <;> simp [unitEntry, h]

omit [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V] in
@[simp]
theorem unitEntry_sub (i j : n) (u v : V) :
    unitEntry i j (u - v) = unitEntry i j u - unitEntry i j v := by
  ext a b; by_cases h : a = i ∧ b = j <;> simp [unitEntry, h]

/-! ## An order unit is a matrix order unit -/

namespace IsMatrixOrdering

variable {C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)} (hC : IsMatrixOrdering C)

include hC

omit [StarModule ℂ V] in
theorem sum_mem {m : Type u} [Fintype m] {ι : Type*} {s : Finset ι} (f : ι → Matrix m m V)
    (hf : ∀ p ∈ s, f p ∈ C m) : (∑ p ∈ s, f p) ∈ C m :=
  Finset.sum_induction f (· ∈ C m) (fun a b ha hb => hC.add_mem m a ha b hb) (hC.zero_mem m) hf

omit [StarModule ℂ V] in
/-- The amplified unit is positive. -/
theorem amplify_mem {m : Type u} [Fintype m] [DecidableEq m] {e : V} (he : LevelOne C e) :
    amplifyUnit m e ∈ C m := by
  have h := hC.diagWeight_mem (fun _ : m => (1 : ℝ)) (fun _ => zero_le_one) he
  have hEq : (Matrix.of fun a b => if a = b then (((1 : ℝ) : ℂ)) • e else 0) = amplifyUnit m e := by
    ext a b; by_cases hab : a = b <;> simp [amplifyUnit_apply, hab]
  rwa [hEq] at h

omit [StarModule ℂ V] in
/-- A nonnegative multiple of the amplified unit is positive. -/
theorem smul_amplify_mem {m : Type u} [Fintype m] [DecidableEq m] {e : V} (he : LevelOne C e)
    {c : ℝ} (hc : 0 ≤ c) : (c : ℂ) • amplifyUnit m e ∈ C m := by
  have h := hC.diagWeight_mem (fun _ : m => c) (fun _ => hc) he
  have hEq : (Matrix.of fun a b => if a = b then ((c : ℂ)) • e else 0) = (c : ℂ) • amplifyUnit m e := by
    ext a b; by_cases hab : a = b <;> simp [amplifyUnit_apply, hab]
  rwa [hEq] at h

/-- **Every symmetrised entry pair of a self-adjoint matrix is dominated by the amplified unit.** -/
theorem pairTerm_bound {m : Type u} [Fintype m] [DecidableEq m] {e : V}
    (he : IsOrderUnitLevelOne C e) (x : Matrix m m V) (hx : xᴴ = x) (i j : m) :
    ∃ τ : ℝ, 0 ≤ τ ∧ (τ : ℂ) • amplifyUnit m e - pairTerm x i j ∈ C m := by
  have hji : x j i = star (x i j) := by
    have h := congrFun (congrFun hx j) i
    simpa [Matrix.conjTranspose_apply] using h.symm
  by_cases hij : i = j
  · subst hij
    have hsa : star (x i i) = x i i := by
      have h := congrFun (congrFun hx i) i
      simpa [Matrix.conjTranspose_apply] using h
    obtain ⟨t, ht, ht1, _⟩ := he.bound (x i i) hsa
    refine ⟨2 * t, by positivity, ?_⟩
    have h1 : rankOneTensor (fun p => if p = i then (1 : ℂ) else 0) ((t : ℂ) • e - x i i) ∈ C m :=
      hC.rankOneTensor_mem _ ht1
    rw [rankOneTensor_single] at h1
    have h2 := hC.add_mem m _ h1 _ h1
    have hd := hC.diagWeight_mem
      (fun a => 2 * t - (if a = i then t else 0) - (if a = i then t else 0))
      (fun a => by
        rcases eq_or_ne a i with rfl | hai
        · rw [if_pos rfl]; linarith
        · rw [if_neg hai]; linarith) he.pos
    rw [← amplify_sub_two_unitEntry i i e t] at hd
    have h3 := hC.add_mem m _ hd _ h2
    have hEq : (((2 * t : ℝ) : ℂ) • amplifyUnit m e - unitEntry i i ((t : ℂ) • e)
          - unitEntry i i ((t : ℂ) • e))
        + (unitEntry i i ((t : ℂ) • e - x i i) + unitEntry i i ((t : ℂ) • e - x i i))
        = ((2 * t : ℝ) : ℂ) • amplifyUnit m e - pairTerm x i i := by
      simp only [pairTerm, unitEntry_sub]
      abel
    rwa [hEq] at h3
  · obtain ⟨t, ht, ht1, ht2⟩ := he.bound (rePart (x i j)) (star_rePart _)
    obtain ⟨s, hs, hs1, hs2⟩ := he.bound (imPart (x i j)) (star_imPart _)
    refine ⟨2 * (t + s), by positivity, ?_⟩
    have h1 := hC.rankOneTensor_mem (polVec i j 1) ht1
    have h2 := hC.rankOneTensor_mem (polVec i j (-1)) ht2
    have h3 := hC.rankOneTensor_mem (polVec i j Complex.I) hs1
    have h4 := hC.rankOneTensor_mem (polVec i j (-Complex.I)) hs2
    have hsum := hC.add_mem m _ (hC.add_mem m _ (hC.add_mem m _ h1 _ h2) _ h3) _ h4
    have hhalf := hC.smul_mem m (2⁻¹) (by norm_num) hsum
    rw [show (((2⁻¹ : ℝ)) : ℂ) = (2 : ℂ)⁻¹ by norm_num] at hhalf
    rw [polarization_identity hij e (rePart (x i j)) (imPart (x i j)) t s,
      rePart_add_I_imPart, rePart_sub_I_imPart, ← hji] at hhalf
    have hd := hC.diagWeight_mem
      (fun a => 2 * (t + s) - (if a = i then t + s else 0) - (if a = j then t + s else 0))
      (fun a => by
        rcases eq_or_ne a i with rfl | hai
        · rw [if_pos rfl, if_neg hij]; linarith
        · rw [if_neg hai]
          rcases eq_or_ne a j with rfl | haj
          · rw [if_pos rfl]; linarith
          · rw [if_neg haj]; linarith) he.pos
    rw [← amplify_sub_two_unitEntry i j e (t + s)] at hd
    have h5 := hC.add_mem m _ hd _ hhalf
    have hEq : (((2 * (t + s) : ℝ) : ℂ) • amplifyUnit m e - unitEntry i i (((t + s : ℝ) : ℂ) • e)
          - unitEntry j j (((t + s : ℝ) : ℂ) • e))
        + (unitEntry i i (((t + s : ℝ) : ℂ) • e) + unitEntry j j (((t + s : ℝ) : ℂ) • e)
          - unitEntry i j (x i j) - unitEntry j i (x j i))
        = ((2 * (t + s) : ℝ) : ℂ) • amplifyUnit m e - pairTerm x i j := by
      simp only [pairTerm]
      abel
    rwa [hEq] at h5

/-- One-sided form of the matrix order unit property. -/
theorem exists_amplify_sub_mem {m : Type u} [Fintype m] [DecidableEq m] {e : V}
    (he : IsOrderUnitLevelOne C e) (x : Matrix m m V) (hx : xᴴ = x) :
    ∃ T : ℝ, 0 < T ∧ (T : ℂ) • amplifyUnit m e - x ∈ C m := by
  classical
  choose τ hτ0 hτ using fun p : m × m => hC.pairTerm_bound he x hx p.1 p.2
  have hsum : (∑ p : m × m, ((τ p : ℂ) • amplifyUnit m e - pairTerm x p.1 p.2)) ∈ C m :=
    hC.sum_mem _ fun p _ => hτ p
  have hEq : (∑ p : m × m, ((τ p : ℂ) • amplifyUnit m e - pairTerm x p.1 p.2))
      = ((∑ p : m × m, τ p : ℝ) : ℂ) • amplifyUnit m e - (x + x) := by
    rw [Finset.sum_sub_distrib, sum_pairTerm, ← Finset.sum_smul, Complex.ofReal_sum]
  rw [hEq] at hsum
  have hhalf := hC.smul_mem m 2⁻¹ (by norm_num) hsum
  have hEq2 : (((2⁻¹ : ℝ)) : ℂ) •
        (((∑ p : m × m, τ p : ℝ) : ℂ) • amplifyUnit m e - (x + x))
      = (((∑ p : m × m, τ p) / 2 : ℝ) : ℂ) • amplifyUnit m e - x := by
    push_cast
    module
  rw [hEq2] at hhalf
  have hnn : 0 ≤ ∑ p : m × m, τ p := Finset.sum_nonneg fun p _ => hτ0 p
  refine ⟨(∑ p : m × m, τ p) / 2 + 1, by linarith, ?_⟩
  have hadd := hC.add_mem m _ hhalf _ (hC.smul_amplify_mem he.pos (zero_le_one (α := ℝ)))
  have hEq3 : ((((∑ p : m × m, τ p) / 2 : ℝ) : ℂ) • amplifyUnit m e - x)
        + (((1 : ℝ)) : ℂ) • amplifyUnit m e
      = ((((∑ p : m × m, τ p) / 2 + 1 : ℝ)) : ℂ) • amplifyUnit m e - x := by
    push_cast
    module
  rwa [hEq3] at hadd

/-- **An order unit for the scalar level is automatically a matrix order unit.**  For every finite
level and every self-adjoint element there is a positive multiple of the amplified unit dominating
it on both sides. -/
theorem isMatrixOrderUnit_of_levelOne {m : Type u} [Fintype m] [DecidableEq m] {e : V}
    (he : IsOrderUnitLevelOne C e) (x : Matrix m m V) (hx : xᴴ = x) :
    ∃ T : ℝ, 0 < T ∧ (T : ℂ) • amplifyUnit m e - x ∈ C m ∧ (T : ℂ) • amplifyUnit m e + x ∈ C m := by
  obtain ⟨T₁, hT₁, h₁⟩ := hC.exists_amplify_sub_mem he x hx
  obtain ⟨T₂, hT₂, h₂⟩ := hC.exists_amplify_sub_mem he (-x) (by rw [Matrix.conjTranspose_neg, hx])
  refine ⟨T₁ + T₂, by linarith, ?_, ?_⟩
  · have hadd := hC.add_mem m _ h₁ _ (hC.smul_amplify_mem he.pos hT₂.le)
    have hEq : ((T₁ : ℂ) • amplifyUnit m e - x) + (T₂ : ℂ) • amplifyUnit m e
        = ((T₁ + T₂ : ℝ) : ℂ) • amplifyUnit m e - x := by
      push_cast
      module
    rwa [hEq] at hadd
  · have hadd := hC.add_mem m _ h₂ _ (hC.smul_amplify_mem he.pos hT₁.le)
    have hEq : ((T₂ : ℂ) • amplifyUnit m e - -x) + (T₁ : ℂ) • amplifyUnit m e
        = ((T₁ + T₂ : ℝ) : ℂ) • amplifyUnit m e + x := by
      push_cast
      module
    rwa [hEq] at hadd

end IsMatrixOrdering

end GaloisForLFunctions.HTGeometry
