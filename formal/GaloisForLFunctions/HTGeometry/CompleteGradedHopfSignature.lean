import GaloisForLFunctions.HTGeometry.CompleteGradedAlgebraExpLog

/-!
# Twisted-antipode response signatures in a complete connected graded Hopf algebra

A complete connected graded Hopf structure on `H` consists of a complete graded algebra `T`
(the completed tensor square), graded algebra maps `x ↦ x ⊗ 1`, `x ↦ 1 ⊗ x` with commuting
images, a graded coproduct, a counit identifying `H_0 = k`, an antipode and the contraction
`m ∘ (S ⊗ id) : T → H` satisfying the antipode identity `m(S ⊗ id)Δ = ηε`.

* `exp` and `log` are inverse bijections between primitive and group-like elements, and the
  antipode inverts every group-like element.
* For a graded algebra endomorphism `θ`, the twisted-antipode fixed signatures are exactly
  `exp(P⁻)`, `P⁻ = {X primitive : θX = -X}`; pure reversal forces the identity, and every nonzero
  anti-invariant primitive gives a nontrivial fixed signature.
* The parity rules `[P^±, P^±] ⊆ P^+`, `[P^+, P^-] ⊆ P^-`; `P^-` is a Lie triple system.
* The fixed equation is `g θ(g) = 1`; its graded components reconstruct every reflection-even
  grade from lower grades.
* For `X, Y ∈ P⁻` the reflection-even part of `log(e^X e^Y)` is `½(BCH(X,Y) - BCH(Y,X))`, equal to
  `½[X, Y]` modulo filtration three, and vanishing exactly when `e^X` and `e^Y` commute; an
  ordinary product of fixed signatures is fixed exactly when they commute.
* If the common odd primitive sector of a family of reversals vanishes, the only signature fixed
  by all twisted antipodes is `1`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open CompleteGradedAlgebra

variable {k : Type*} [Field k]
variable {H : Type*} [Ring H] [Algebra k H] [CompleteGradedAlgebra k H]
variable {T : Type*} [Ring T] [Algebra k T] [CompleteGradedAlgebra k T]

/-- An algebra map commuting with the homogeneous projections. -/
def IsGradedAlgHom {A B : Type*} [Ring A] [Algebra k A] [CompleteGradedAlgebra k A] [Ring B]
    [Algebra k B] [CompleteGradedAlgebra k B] (φ : A →ₐ[k] B) : Prop :=
  ∀ n x, proj k n (φ x) = φ (proj k n x)

theorem IsGradedAlgHom.mem_filtration {A B : Type*} [Ring A] [Algebra k A]
    [CompleteGradedAlgebra k A] [Ring B] [Algebra k B] [CompleteGradedAlgebra k B]
    {φ : A →ₐ[k] B} (hφ : IsGradedAlgHom φ) {m : ℕ} {x : A} (hx : x ∈ filtration k A m) :
    φ x ∈ filtration k B m := fun j hj => by rw [hφ, hx j hj, map_zero]

variable (k H T) in
/-- A complete connected graded Hopf structure on `H` with completed tensor square `T`. -/
structure CompleteHopfStructure where
  /-- `x ↦ x ⊗ 1`. -/
  left : H →ₐ[k] T
  /-- `x ↦ 1 ⊗ x`. -/
  right : H →ₐ[k] T
  /-- The coproduct. -/
  coproduct : H →ₐ[k] T
  left_graded : IsGradedAlgHom left
  right_graded : IsGradedAlgHom right
  coproduct_graded : IsGradedAlgHom coproduct
  left_right_commute : ∀ x y, Commute (left x) (right y)
  /-- The counit. -/
  counit : H →ₗ[k] k
  proj_zero : ∀ x, proj k 0 x = algebraMap k H (counit x)
  /-- The antipode. -/
  antipode : H →ₗ[k] H
  /-- The contraction `m ∘ (S ⊗ id)`. -/
  antipodeContraction : T →ₗ[k] H
  contraction_left_mul_right : ∀ x y, antipodeContraction (left x * right y) = antipode x * y
  contraction_coproduct : ∀ x, antipodeContraction (coproduct x) = algebraMap k H (counit x)

namespace CompleteHopfStructure

variable (D : CompleteHopfStructure k H T)

/-- Group-like elements of `1 + H_{≥1}`. -/
def IsGroupLike (g : H) : Prop := proj k 0 g = 1 ∧ D.coproduct g = D.left g * D.right g

/-- Primitive elements of `H_{≥1}`. -/
def IsPrimitive (X : H) : Prop := proj k 0 X = 0 ∧ D.coproduct X = D.left X + D.right X

theorem sub_one_mem_of_proj_zero {g : H} (hg : proj k 0 g = 1) : g - 1 ∈ filtration k H 1 := by
  intro j hj
  have : j = 0 := by omega
  subst this
  rw [map_sub, hg, comp_one, if_pos rfl, sub_self]

theorem mem_of_proj_zero {X : H} (hX : proj k 0 X = 0) : X ∈ filtration k H 1 := by
  intro j hj
  have : j = 0 := by omega
  subst this
  exact hX

theorem IsGroupLike.sub_one_mem {g : H} (hg : D.IsGroupLike g) : g - 1 ∈ filtration k H 1 :=
  sub_one_mem_of_proj_zero hg.1

theorem IsPrimitive.mem {X : H} (hX : D.IsPrimitive X) : X ∈ filtration k H 1 :=
  mem_of_proj_zero hX.1

theorem IsGroupLike.mul {g h : H} (hg : D.IsGroupLike g) (hh : D.IsGroupLike h) :
    D.IsGroupLike (g * h) := by
  refine ⟨?_, ?_⟩
  · have hg1 := hg.sub_one_mem
    have hh1 := hh.sub_one_mem
    have : g * h - 1 ∈ filtration k H 1 := by
      have e : g * h - 1 = (g - 1) * h + (h - 1) := by noncomm_ring
      rw [e]
      exact add_mem (by simpa using mul_mem_filtration hg1 (mem_filtration_zero h)) hh1
    have h0 := this 0 Nat.one_pos
    rw [map_sub, comp_one, if_pos rfl, sub_eq_zero] at h0
    exact h0
  · rw [map_mul, hg.2, hh.2, map_mul, map_mul, mul_assoc, ← mul_assoc (D.right g),
      ← (D.left_right_commute h g).eq, mul_assoc, mul_assoc]

/-- The antipode is a left inverse on group-likes: `S(g) g = 1`. -/
theorem antipode_mul_self {g : H} (hg : D.IsGroupLike g) : D.antipode g * g = 1 := by
  rw [← D.contraction_left_mul_right, ← hg.2, D.contraction_coproduct, ← D.proj_zero, hg.1]

variable [CharZero k]

/-- **(CRS.17)** `exp` of a primitive element is group-like. -/
theorem isGroupLike_cexp {X : H} (hX : D.IsPrimitive X) : D.IsGroupLike (cexp k X) := by
  refine ⟨comp_zero_cexp X, ?_⟩
  have hL := D.left_graded.mem_filtration hX.mem
  have hR := D.right_graded.mem_filtration hX.mem
  rw [algHom_cexp _ D.coproduct_graded, hX.2, cexp_add_of_commute hL hR (D.left_right_commute X X),
    algHom_cexp _ D.left_graded, algHom_cexp _ D.right_graded]

/-- **(CRS.17)** `log` of a group-like element is primitive. -/
theorem isPrimitive_clog {g : H} (hg : D.IsGroupLike g) : D.IsPrimitive (clog k g) := by
  refine ⟨clog_mem (k := k) g 0 Nat.one_pos, ?_⟩
  have h1 := hg.sub_one_mem
  have hL : D.left g - 1 ∈ filtration k T 1 := by
    have := D.left_graded.mem_filtration h1; rwa [map_sub, map_one] at this
  have hR : D.right g - 1 ∈ filtration k T 1 := by
    have := D.right_graded.mem_filtration h1; rwa [map_sub, map_one] at this
  rw [algHom_clog _ D.coproduct_graded, hg.2, clog_mul_of_commute hL hR (D.left_right_commute g g),
    algHom_clog _ D.left_graded, algHom_clog _ D.right_graded]

theorem clog_cexp_of_isPrimitive {X : H} (hX : D.IsPrimitive X) : clog k (cexp k X) = X :=
  clog_cexp hX.mem

theorem cexp_clog_of_isGroupLike {g : H} (hg : D.IsGroupLike g) : cexp k (clog k g) = g :=
  cexp_clog hg.sub_one_mem

/-- **(CRS.17)** `exp : P(H) ≃ G(H)`, with inverse `log`. -/
def expEquiv : {X : H // D.IsPrimitive X} ≃ {g : H // D.IsGroupLike g} where
  toFun X := ⟨cexp k X.1, D.isGroupLike_cexp X.2⟩
  invFun g := ⟨clog k g.1, D.isPrimitive_clog g.2⟩
  left_inv X := Subtype.ext (D.clog_cexp_of_isPrimitive X.2)
  right_inv g := Subtype.ext (D.cexp_clog_of_isGroupLike g.2)

/-- The antipode of a group-like element is its inverse `exp(-log g)`. -/
theorem antipode_groupLike {g : H} (hg : D.IsGroupLike g) :
    D.antipode g = cexp k (-clog k g) := by
  have hL := clog_mem (k := k) g
  have h1 : g * cexp k (-clog k g) = 1 := by
    have := cexp_mul_cexp_neg hL
    rwa [D.cexp_clog_of_isGroupLike hg] at this
  calc D.antipode g = D.antipode g * (g * cexp k (-clog k g)) := by rw [h1, mul_one]
    _ = (D.antipode g * g) * cexp k (-clog k g) := by rw [mul_assoc]
    _ = cexp k (-clog k g) := by rw [D.antipode_mul_self hg, one_mul]

theorem mul_antipode_self {g : H} (hg : D.IsGroupLike g) : g * D.antipode g = 1 := by
  rw [D.antipode_groupLike hg]
  have := cexp_mul_cexp_neg (clog_mem (k := k) g)
  rwa [D.cexp_clog_of_isGroupLike hg] at this

/-- A graded endomorphism mapping a group-like element to a group-like element commutes with the
antipode on it. -/
theorem antipode_comm_of_isGroupLike {θ : H →ₐ[k] H} (hθ : IsGradedAlgHom θ) {g : H}
    (hg : D.IsGroupLike g) (hθg : D.IsGroupLike (θ g)) :
    θ (D.antipode g) = D.antipode (θ g) := by
  rw [D.antipode_groupLike hg, D.antipode_groupLike hθg, algHom_cexp _ hθ, map_neg,
    algHom_clog _ hθ]

/-! ## Theorem 4.1: logarithmic classification of fixed signatures -/

/-- Fixed points of the twisted antipode `θ ∘ S` among group-like signatures. -/
def IsTwistedFixed (θ : H →ₐ[k] H) (g : H) : Prop := D.IsGroupLike g ∧ θ (D.antipode g) = g

/-- The anti-invariant primitive sector `P⁻`. -/
def IsOddPrimitive (θ : H →ₐ[k] H) (X : H) : Prop := D.IsPrimitive X ∧ θ X = -X

/-- **Theorem 4.1 (CRS.19)** `Q_θ(G(H)) = exp(P⁻)`. -/
theorem isTwistedFixed_iff {θ : H →ₐ[k] H} (hθ : IsGradedAlgHom θ) {g : H} :
    D.IsTwistedFixed θ g ↔ ∃ X, D.IsOddPrimitive θ X ∧ cexp k X = g := by
  constructor
  · rintro ⟨hg, hfix⟩
    refine ⟨clog k g, ⟨D.isPrimitive_clog hg, ?_⟩, D.cexp_clog_of_isGroupLike hg⟩
    have hX := clog_mem (k := k) g
    rw [D.antipode_groupLike hg, algHom_cexp _ hθ, map_neg] at hfix
    have hθX := hθ.mem_filtration hX
    have := cexp_injective (neg_mem hθX) hX (hfix.trans (D.cexp_clog_of_isGroupLike hg).symm)
    exact neg_eq_iff_eq_neg.1 this
  · rintro ⟨X, ⟨hXp, hθX⟩, rfl⟩
    refine ⟨D.isGroupLike_cexp hXp, ?_⟩
    rw [D.antipode_groupLike (D.isGroupLike_cexp hXp), D.clog_cexp_of_isPrimitive hXp,
      algHom_cexp _ hθ, map_neg, hθX, neg_neg]

/-- **Theorem 4.1** Pure reversal `θ = id` forces the identity signature. -/
theorem eq_one_of_isTwistedFixed_id {g : H} (hg : D.IsTwistedFixed (AlgHom.id k H) g) : g = 1 := by
  obtain ⟨X, ⟨hXp, hX⟩, rfl⟩ := (D.isTwistedFixed_iff (fun _ _ => rfl)).1 hg
  have h2 : (2 : k) • X = 0 := by
    rw [two_smul]; nth_rewrite 1 [show X = -X from hX]; exact neg_add_cancel X
  have hX0 : X = 0 := by
    have := congrArg ((2 : k)⁻¹ • ·) h2
    simpa [smul_smul] using this
  rw [hX0, cexp_zero]

/-- **Theorem 4.1** Every nonzero anti-invariant primitive gives a nontrivial fixed signature. -/
theorem cexp_isTwistedFixed_ne_one {θ : H →ₐ[k] H} (hθ : IsGradedAlgHom θ) {X : H}
    (hX : D.IsOddPrimitive θ X) (hne : X ≠ 0) :
    D.IsTwistedFixed θ (cexp k X) ∧ cexp k X ≠ 1 := by
  refine ⟨(D.isTwistedFixed_iff hθ).2 ⟨X, hX, rfl⟩, fun h => hne ?_⟩
  rw [← D.clog_cexp_of_isPrimitive hX.1, h]
  rw [← cexp_zero (k := k) (H := H), clog_cexp (Submodule.zero_mem _)]

/-- **(CRS.23)** For group-like `g`, the fixed equation is `g θ(g) = 1`. -/
theorem isTwistedFixed_iff_mul {θ : H →ₐ[k] H} {g : H} (hg : D.IsGroupLike g) :
    θ (D.antipode g) = g ↔ g * θ g = 1 := by
  have hl := D.antipode_mul_self hg
  have hr := D.mul_antipode_self hg
  constructor
  · intro h
    calc g * θ g = θ (D.antipode g) * θ g := by rw [h]
      _ = 1 := by rw [← map_mul, hl, map_one]
  · intro h
    calc θ (D.antipode g) = (g * θ g) * θ (D.antipode g) := by rw [h, one_mul]
      _ = g * θ (g * D.antipode g) := by rw [map_mul, mul_assoc]
      _ = g := by rw [hr, map_one, mul_one]

/-- **(CRS.9)** for twisted-fixed signatures: a product is fixed exactly when the factors
commute. -/
theorem isTwistedFixed_mul_iff {θ : H →ₐ[k] H} {g h : H} (hg : D.IsTwistedFixed θ g)
    (hh : D.IsTwistedFixed θ h) : D.IsTwistedFixed θ (g * h) ↔ g * h = h * g := by
  have hgh := IsGroupLike.mul D hg.1 hh.1
  have hS : D.antipode (g * h) = D.antipode h * D.antipode g := by
    have hl := D.antipode_mul_self hgh
    calc D.antipode (g * h) = D.antipode (g * h) * ((g * h) * (D.antipode h * D.antipode g)) := by
          rw [show (g * h) * (D.antipode h * D.antipode g) = 1 by
            rw [mul_assoc, ← mul_assoc h, D.mul_antipode_self hh.1, one_mul,
              D.mul_antipode_self hg.1], mul_one]
      _ = D.antipode h * D.antipode g := by rw [← mul_assoc, hl, one_mul]
  constructor
  · rintro ⟨-, hfix⟩
    rw [hS, map_mul, hh.2, hg.2] at hfix
    exact hfix.symm
  · intro hc
    exact ⟨hgh, by rw [hS, map_mul, hh.2, hg.2, hc]⟩

/-! ## Corollary 4.2: the Lie triple law -/

omit [CharZero k] in
theorem isPrimitive_commutator {X Y : H} (hX : D.IsPrimitive X) (hY : D.IsPrimitive Y) :
    D.IsPrimitive (X * Y - Y * X) := by
  refine ⟨?_, ?_⟩
  · have := sub_mem (mul_mem_filtration hX.mem hY.mem) (mul_mem_filtration hY.mem hX.mem)
    exact this 0 (by norm_num)
  · rw [map_sub, map_mul, map_mul, hX.2, hY.2, map_sub, map_sub, map_mul, map_mul, map_mul,
      map_mul]
    have c1 := (D.left_right_commute X Y).eq
    have c2 := (D.left_right_commute Y X).eq
    calc (D.left X + D.right X) * (D.left Y + D.right Y) -
          (D.left Y + D.right Y) * (D.left X + D.right X)
        = D.left X * D.left Y + D.right X * D.right Y -
              (D.left Y * D.left X + D.right Y * D.right X)
            + (D.left X * D.right Y - D.right Y * D.left X)
            + (D.right X * D.left Y - D.left Y * D.right X) := by noncomm_ring
      _ = _ := by rw [c1, c2, sub_self, sub_self, add_zero, add_zero]; abel

omit [CompleteGradedAlgebra k H] [CharZero k] in
/-- **(CRS.20)** Parity of brackets of `θ`-eigenvectors. -/
theorem commutator_parity (θ : H →ₐ[k] H) {X Y : H} {a b : k} (hX : θ X = a • X)
    (hY : θ Y = b • Y) : θ (X * Y - Y * X) = (a * b) • (X * Y - Y * X) := by
  rw [map_sub, map_mul, map_mul, hX, hY, smul_sub, smul_mul_smul, smul_mul_smul, mul_comm b a]

omit [CharZero k] in
/-- **(CRS.20)–(CRS.21)** `P⁻` is closed under `(X, Y, Z) ↦ [X, [Y, Z]]`. -/
theorem isOddPrimitive_triple {θ : H →ₐ[k] H} {X Y Z : H} (hX : D.IsOddPrimitive θ X)
    (hY : D.IsOddPrimitive θ Y) (hZ : D.IsOddPrimitive θ Z) :
    D.IsOddPrimitive θ (X * (Y * Z - Z * Y) - (Y * Z - Z * Y) * X) := by
  refine ⟨D.isPrimitive_commutator hX.1 (D.isPrimitive_commutator hY.1 hZ.1), ?_⟩
  have hX' : θ X = (-1 : k) • X := by rw [hX.2, neg_one_smul]
  have hY' : θ Y = (-1 : k) • Y := by rw [hY.2, neg_one_smul]
  have hZ' : θ Z = (-1 : k) • Z := by rw [hZ.2, neg_one_smul]
  rw [commutator_parity θ hX' (commutator_parity θ hY' hZ')]
  norm_num

/-! ## Theorem 5.1: antipodal grade reconstruction -/

omit [CharZero k] in
/-- **Theorem 5.1 (CRS.24)** If `g ∈ 1 + H_{≥1}` and `g θ(g) = 1`, then for every `n ≥ 1`
`g_n + θ(g_n) + ∑_{0<i<n} g_i θ(g_{n-i}) = 0`. -/
theorem grade_reconstruction {θ : H →ₐ[k] H} (hθ : IsGradedAlgHom θ) {g : H}
    (hg0 : proj k 0 g = 1) (hfix : g * θ g = 1) {n : ℕ} (hn : 1 ≤ n) :
    proj k n g + θ (proj k n g) +
      ∑ i ∈ Finset.Ioo 0 n, proj k i g * θ (proj k (n - i) g) = 0 := by
  have h := congrArg (proj k n) hfix
  rw [comp_mul, comp_one, if_neg (by omega), Finset.sum_range_succ, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < n), Finset.Ico_add_one_left_eq_Ioo] at h
  have hθ' : ∀ m x, proj k m (θ x) = θ (proj k m x) := hθ
  simp_rw [hθ'] at h
  rw [Nat.sub_zero, Nat.sub_self, hg0, one_mul, map_one, mul_one] at h
  calc proj k n g + θ (proj k n g) + ∑ i ∈ Finset.Ioo 0 n, proj k i g * θ (proj k (n - i) g)
      = θ (proj k n g) + ∑ i ∈ Finset.Ioo 0 n, proj k i g * θ (proj k (n - i) g) + proj k n g := by
        abel
    _ = 0 := h

omit [CharZero k] in
/-- **Theorem 5.1 (CRS.25)** The reflection-even part of grade `n` is forced by lower grades. -/
theorem even_grade_eq {θ : H →ₐ[k] H} (hθ : IsGradedAlgHom θ) {g : H}
    (hg0 : proj k 0 g = 1) (hfix : g * θ g = 1) {n : ℕ} (hn : 1 ≤ n) :
    (2 : k)⁻¹ • (proj k n g + θ (proj k n g)) =
      -((2 : k)⁻¹ • ∑ i ∈ Finset.Ioo 0 n, proj k i g * θ (proj k (n - i) g)) := by
  rw [← smul_neg, eq_neg_of_add_eq_zero_left (grade_reconstruction hθ hg0 hfix hn)]

omit [CharZero k] in
/-- **Theorem 5.1 (CRS.26)** `g_1⁺ = 0` and `g_2⁺ = ½ g_1²`. -/
theorem even_grade_one_two {θ : H →ₐ[k] H} (hθ : IsGradedAlgHom θ) {g : H}
    (hg0 : proj k 0 g = 1) (hfix : g * θ g = 1) :
    (2 : k)⁻¹ • (proj k 1 g + θ (proj k 1 g)) = 0 ∧
      (2 : k)⁻¹ • (proj k 2 g + θ (proj k 2 g)) = (2 : k)⁻¹ • (proj k 1 g) ^ 2 := by
  have h1 := grade_reconstruction hθ hg0 hfix (le_refl 1)
  have h2 := grade_reconstruction hθ hg0 hfix (by norm_num : 1 ≤ 2)
  rw [show Finset.Ioo 0 1 = ∅ by rfl, Finset.sum_empty, add_zero] at h1
  rw [show Finset.Ioo 0 2 = {1} by rfl, Finset.sum_singleton] at h2
  have hθ1 : θ (proj k 1 g) = -proj k 1 g := eq_neg_of_add_eq_zero_right h1
  refine ⟨by rw [h1, smul_zero], ?_⟩
  rw [show 2 - 1 = 1 from rfl, hθ1, mul_neg, ← sq] at h2
  rw [show proj k 2 g + θ (proj k 2 g) = proj k 1 g ^ 2 by
    rw [← sub_eq_zero, ← h2]; abel]

/-! ## Theorem 6.1: the even commutator is the first fusion obstruction -/

/-- The reflection-even part `½(Z + θZ)`. -/
def evenPart (θ : H →ₐ[k] H) (Z : H) : H := (2 : k)⁻¹ • (Z + θ Z)

/-- **(CRS.28)** `θ BCH(X, Y) = -BCH(Y, X)` for anti-invariant `X, Y ∈ H_{≥1}`. -/
theorem map_bch_of_odd {θ : H →ₐ[k] H} (hθ : IsGradedAlgHom θ) {X Y : H}
    (hX : X ∈ filtration k H 1) (hY : Y ∈ filtration k H 1) (hθX : θ X = -X) (hθY : θ Y = -Y) :
    θ (bch (k := k) X Y) = -bch (k := k) Y X := by
  rw [bch, algHom_clog _ hθ, map_mul, algHom_cexp _ hθ, algHom_cexp _ hθ, hθX, hθY, bch]
  refine clog_eq_neg_of_mul_eq_one ?_ ?_
  · have e : cexp k Y * cexp k X - 1 = (cexp k Y - 1) * cexp k X + (cexp k X - 1) := by
      noncomm_ring
    rw [e]
    exact add_mem (by simpa using mul_mem_filtration (cexp_sub_one_mem hY) (mem_filtration_zero _))
      (cexp_sub_one_mem hX)
  · calc cexp k (-X) * cexp k (-Y) * (cexp k Y * cexp k X)
        = cexp k (-X) * (cexp k (-Y) * cexp k Y) * cexp k X := by noncomm_ring
      _ = 1 := by rw [cexp_neg_mul_cexp hY, mul_one, cexp_neg_mul_cexp hX]

/-- **Theorem 6.1 (CRS.28)** `BCH(X,Y)⁺ = ½(BCH(X,Y) - BCH(Y,X))`. -/
theorem evenPart_bch {θ : H →ₐ[k] H} (hθ : IsGradedAlgHom θ) {X Y : H}
    (hX : X ∈ filtration k H 1) (hY : Y ∈ filtration k H 1) (hθX : θ X = -X) (hθY : θ Y = -Y) :
    evenPart θ (bch (k := k) X Y) = (2 : k)⁻¹ • (bch (k := k) X Y - bch (k := k) Y X) := by
  rw [evenPart, map_bch_of_odd hθ hX hY hθX hθY, ← sub_eq_add_neg]

/-- **Theorem 6.1 (CRS.29)** `BCH(X,Y)⁺ ≡ ½[X, Y]` modulo `H_{≥3}`. -/
theorem evenPart_bch_sub_mem {θ : H →ₐ[k] H} (hθ : IsGradedAlgHom θ) {X Y : H}
    (hX : X ∈ filtration k H 1) (hY : Y ∈ filtration k H 1) (hθX : θ X = -X) (hθY : θ Y = -Y) :
    evenPart θ (bch (k := k) X Y) - (2 : k)⁻¹ • (X * Y - Y * X) ∈ filtration k H 3 := by
  rw [evenPart_bch hθ hX hY hθX hθY]
  have h1 := bch_sub_mem_filtration_three (k := k) hX hY
  have h2 := bch_sub_mem_filtration_three (k := k) hY hX
  have e : (2 : k)⁻¹ • (bch (k := k) X Y - bch (k := k) Y X) - (2 : k)⁻¹ • (X * Y - Y * X) =
      (2 : k)⁻¹ • ((bch (k := k) X Y - (X + Y + (2 : k)⁻¹ • (X * Y - Y * X))) -
        (bch (k := k) Y X - (Y + X + (2 : k)⁻¹ • (Y * X - X * Y)))) := by
    module
  rw [e]
  exact Submodule.smul_mem _ _ (sub_mem h1 h2)

/-- **Theorem 6.1** The even part vanishes exactly when `e^X` and `e^Y` commute. -/
theorem evenPart_bch_eq_zero_iff {θ : H →ₐ[k] H} (hθ : IsGradedAlgHom θ) {X Y : H}
    (hX : X ∈ filtration k H 1) (hY : Y ∈ filtration k H 1) (hθX : θ X = -X) (hθY : θ Y = -Y) :
    evenPart θ (bch (k := k) X Y) = 0 ↔ cexp k X * cexp k Y = cexp k Y * cexp k X := by
  have hXY : cexp k X * cexp k Y - 1 ∈ filtration k H 1 := by
    have e : cexp k X * cexp k Y - 1 = (cexp k X - 1) * cexp k Y + (cexp k Y - 1) := by
      noncomm_ring
    rw [e]
    exact add_mem (by simpa using mul_mem_filtration (cexp_sub_one_mem hX) (mem_filtration_zero _))
      (cexp_sub_one_mem hY)
  have hYX : cexp k Y * cexp k X - 1 ∈ filtration k H 1 := by
    have e : cexp k Y * cexp k X - 1 = (cexp k Y - 1) * cexp k X + (cexp k X - 1) := by
      noncomm_ring
    rw [e]
    exact add_mem (by simpa using mul_mem_filtration (cexp_sub_one_mem hY) (mem_filtration_zero _))
      (cexp_sub_one_mem hX)
  rw [evenPart_bch hθ hX hY hθX hθY]
  constructor
  · intro h
    have h2 : bch (k := k) X Y - bch (k := k) Y X = 0 := by
      have := congrArg ((2 : k) • ·) h
      simpa [smul_smul] using this
    exact clog_injective hXY hYX (sub_eq_zero.1 h2)
  · intro h
    rw [bch, bch, h, sub_self, smul_zero]

/-! ## Selection by a family of reversals -/

/-- **Theorem 7.1, selection.**  If no nonzero primitive is anti-invariant under every `θ_j`,
then the only signature fixed by every twisted antipode `θ_j ∘ S` is `1`. -/
theorem eq_one_of_forall_isTwistedFixed {J : Type*} {θ : J → H →ₐ[k] H}
    (hθ : ∀ j, IsGradedAlgHom (θ j))
    (hodd : ∀ X, D.IsPrimitive X → (∀ j, θ j X = -X) → X = 0) {g : H} (hg : D.IsGroupLike g)
    (hfix : ∀ j, θ j (D.antipode g) = g) : g = 1 := by
  have hX : ∀ j, θ j (clog k g) = -clog k g := by
    intro j
    obtain ⟨X, ⟨hXp, hθX⟩, hXg⟩ := (D.isTwistedFixed_iff (hθ j)).1 ⟨hg, hfix j⟩
    rw [← hXg, D.clog_cexp_of_isPrimitive hXp]
    exact hθX
  have h0 := hodd _ (D.isPrimitive_clog hg) hX
  rw [← D.cexp_clog_of_isGroupLike hg, h0, cexp_zero]

end CompleteHopfStructure

end GaloisForLFunctions.HTGeometry
