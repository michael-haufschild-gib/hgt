import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFrobeniusGraphsMeetInThePrimes
import GaloisForLFunctions.HTGeometry.SingularIntegralCokernel

/-!
# The count of a section on two graphs is the split norm

On two graphs `Γ_m`, `Γ_n` the functions of the square are the pairs of integers that agree
modulo the contact ideal `J(m, n)`: a lattice of rank two, an order in `ℤ × ℤ`. So the square
has a count on the rays of a pair of graphs: the number of residues of a section `x`,
`K(x) = #𝒪(Γ_m ∪ Γ_n)/(x)`.

* **The functions on two graphs** (`range_ghostComponent_pair`, `graphPair`): the values
  `(x_m, x_n)` of the sections of the square are exactly the pairs with `x_m − x_n ∈ J(m, n)`.
* **The count** (`card_pairRing_quotient`, `card_quotient_graphPair`): for `m ≠ n`,
  `K(x) = |x_m · x_n|`, the absolute value of the norm of the split algebra `ℤ × ℤ`. It does not
  depend on the contact.
* **Exactly quadratic on rays** (`card_quotient_graphPair_intCast_mul`): `K(k·x) = k² K(x)`.
* **Not a form** (`exists_not_parallelogram_pairRing`): on the order of conductor `c ≥ 2` the
  count violates the parallelogram law.

So the object has a count with a quadratic Tate limit on every pair of graphs, and the limit is
`|x_m x_n|`: the absolute value of a hyperbolic form, blind to the sign and to the gluing. It is
not the pairing of the degree points, in which `Γ_m` and `Γ_n` enter through the logarithm of
their contact.
-/

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The functions of the square on two graphs -/

/-- The ring of two graphs glued along the ideal `J`: the pairs of integers congruent modulo
`J`. -/
def pairRing (J : Ideal ℤ) : Subring (ℤ × ℤ) where
  carrier := {z | z.1 - z.2 ∈ J}
  mul_mem' := by
    intro x y hx hy
    have e : (x * y).1 - (x * y).2 = (x.1 - x.2) * y.1 + x.2 * (y.1 - y.2) := by
      rw [Prod.fst_mul, Prod.snd_mul]
      ring
    show (x * y).1 - (x * y).2 ∈ J
    rw [e]
    exact J.add_mem (J.mul_mem_right _ hx) (J.mul_mem_left _ hy)
  one_mem' := by
    show (1 : ℤ × ℤ).1 - (1 : ℤ × ℤ).2 ∈ J
    simp
  add_mem' := by
    intro x y hx hy
    have e : (x + y).1 - (x + y).2 = (x.1 - x.2) + (y.1 - y.2) := by
      rw [Prod.fst_add, Prod.snd_add]
      ring
    show (x + y).1 - (x + y).2 ∈ J
    rw [e]
    exact J.add_mem hx hy
  zero_mem' := by
    show (0 : ℤ × ℤ).1 - (0 : ℤ × ℤ).2 ∈ J
    simp
  neg_mem' := by
    intro x hx
    have e : (-x).1 - (-x).2 = -(x.1 - x.2) := by
      rw [Prod.fst_neg, Prod.snd_neg]
      ring
    show (-x).1 - (-x).2 ∈ J
    rw [e]
    exact J.neg_mem hx

theorem mem_pairRing {J : Ideal ℤ} {z : ℤ × ℤ} : z ∈ pairRing J ↔ z.1 - z.2 ∈ J := Iff.rfl

/-- Every element of the contact ideal is the difference of the values of one section. -/
theorem exists_ghostComponent_sub_eq {m n : ℕ+} {d : ℤ} (hd : d ∈ graphIdeal m n) :
    ∃ y : ghostRing, ghostComponent m y - ghostComponent n y = d := by
  refine Submodule.span_induction
    (p := fun d _ => ∃ y : ghostRing, ghostComponent m y - ghostComponent n y = d)
    ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · exact ⟨0, by simp⟩
  · rintro u v _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
    exact ⟨y + z, by
      rw [map_add, map_add]
      ring⟩
  · rintro k u _ ⟨y, rfl⟩
    exact ⟨(k : ghostRing) * y, by
      rw [map_mul, map_mul, map_intCast, map_intCast, Int.cast_id, smul_eq_mul]
      ring⟩

/-- **The functions of the square on two graphs** are the pairs of integers congruent modulo
the contact ideal. -/
theorem range_ghostComponent_pair (m n : ℕ+) :
    Set.range (fun x : ghostRing => (ghostComponent m x, ghostComponent n x)) =
      (pairRing (graphIdeal m n) : Set (ℤ × ℤ)) := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨x, hx⟩
    rw [Prod.mk.injEq] at hx
    show a - b ∈ graphIdeal m n
    rw [← hx.1, ← hx.2]
    exact Ideal.subset_span ⟨x, rfl⟩
  · intro h
    obtain ⟨y, hy⟩ := exists_ghostComponent_sub_eq (show a - b ∈ graphIdeal m n from h)
    refine ⟨y + ((b - ghostComponent n y : ℤ) : ghostRing), ?_⟩
    show (ghostComponent m (y + ((b - ghostComponent n y : ℤ) : ghostRing)),
      ghostComponent n (y + ((b - ghostComponent n y : ℤ) : ghostRing))) = (a, b)
    rw [map_add, map_add, map_intCast, map_intCast, Int.cast_id, Prod.mk.injEq]
    constructor <;> linarith

/-- The restriction of the sections of the square to the two graphs `Γ_m`, `Γ_n`. -/
def graphPair (m n : ℕ+) : ghostRing →+* pairRing (graphIdeal m n) where
  toFun x := ⟨(ghostComponent m x, ghostComponent n x), Ideal.subset_span ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (by
    show (ghostComponent m 1, ghostComponent n 1) = (1 : ℤ × ℤ)
    rw [map_one, map_one]
    rfl)
  map_mul' x y := Subtype.ext (by
    show (ghostComponent m (x * y), ghostComponent n (x * y)) =
      (ghostComponent m x, ghostComponent n x) * (ghostComponent m y, ghostComponent n y)
    rw [map_mul, map_mul]
    rfl)
  map_zero' := Subtype.ext (by
    show (ghostComponent m 0, ghostComponent n 0) = (0 : ℤ × ℤ)
    rw [map_zero, map_zero]
    rfl)
  map_add' x y := Subtype.ext (by
    show (ghostComponent m (x + y), ghostComponent n (x + y)) =
      (ghostComponent m x, ghostComponent n x) + (ghostComponent m y, ghostComponent n y)
    rw [map_add, map_add]
    rfl)

theorem coe_graphPair (m n : ℕ+) (x : ghostRing) :
    (graphPair m n x : ℤ × ℤ) = (ghostComponent m x, ghostComponent n x) := rfl

theorem graphPair_surjective (m n : ℕ+) : Function.Surjective (graphPair m n) := by
  intro z
  have hz : (z : ℤ × ℤ) ∈ Set.range
      (fun x : ghostRing => (ghostComponent m x, ghostComponent n x)) := by
    rw [range_ghostComponent_pair]
    exact z.2
  obtain ⟨x, hx⟩ := hz
  exact ⟨x, Subtype.ext hx⟩

/-- Two distinct graphs have a nonzero contact ideal. -/
theorem graphIdeal_ne_bot {m n : ℕ+} (hmn : m ≠ n) : graphIdeal m n ≠ ⊥ := by
  have hsplit : (m : ℕ) ∈ splitDivisors m n ∨ (n : ℕ) ∈ splitDivisors m n := by
    by_cases h : (m : ℕ) ∣ n
    · right
      refine Or.inr ⟨dvd_rfl, fun h' => hmn ?_⟩
      exact PNat.eq (Nat.dvd_antisymm h h')
    · exact Or.inl (Or.inl ⟨dvd_rfl, h⟩)
  intro hbot
  rw [graphIdeal_eq_span] at hbot
  rcases hsplit with h | h
  · have hmem : ((m : ℕ) : ℤ) ∈ Ideal.span ((fun d : ℕ => (d : ℤ)) '' splitDivisors m n) :=
      Ideal.subset_span ⟨_, h, rfl⟩
    rw [hbot, Ideal.mem_bot] at hmem
    exact m.ne_zero (by exact_mod_cast hmem)
  · have hmem : ((n : ℕ) : ℤ) ∈ Ideal.span ((fun d : ℕ => (d : ℤ)) '' splitDivisors m n) :=
      Ideal.subset_span ⟨_, h, rfl⟩
    rw [hbot, Ideal.mem_bot] at hmem
    exact n.ne_zero (by exact_mod_cast hmem)

/-! ### The count of a principal section -/

/-- **The count on an order of `ℤ × ℤ`.** For `c ≠ 0` and a pair `α = (a, b)` congruent modulo
`c`, the order of conductor `c` has `|a b|` residues modulo `α`; the count is `0` when the
quotient is infinite. -/
theorem card_pairRing_quotient_span {c : ℤ} (hc : c ≠ 0) (α : pairRing (Ideal.span {c})) :
    Nat.card (pairRing (Ideal.span {c}) ⧸ Ideal.span {α}) =
      ((α : ℤ × ℤ).1 * (α : ℤ × ℤ).2).natAbs := by
  have hα : (α : ℤ × ℤ).1 - (α : ℤ × ℤ).2 ∈ Ideal.span {c} := α.2
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hα
  -- the order is the lattice of the pairs `(u + c v, u)`
  let φ : (Fin 2 → ℤ) →+ pairRing (Ideal.span {c}) :=
    { toFun := fun w => ⟨(w 0 + c * w 1, w 0), by
        show w 0 + c * w 1 - w 0 ∈ Ideal.span {c}
        rw [add_sub_cancel_left]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)⟩
      map_zero' := Subtype.ext (by
        show ((0 : Fin 2 → ℤ) 0 + c * (0 : Fin 2 → ℤ) 1, (0 : Fin 2 → ℤ) 0) = (0 : ℤ × ℤ)
        simp)
      map_add' := fun w w' => Subtype.ext (Prod.ext
        (by
          show (w + w') 0 + c * (w + w') 1 = (w 0 + c * w 1) + (w' 0 + c * w' 1)
          simp only [Pi.add_apply]
          ring)
        (by
          show (w + w') 0 = w 0 + w' 0
          rfl)) }
  have hφ : ∀ w, ((φ w : pairRing (Ideal.span {c})) : ℤ × ℤ) = (w 0 + c * w 1, w 0) :=
    fun _ => rfl
  have hinj : Function.Injective φ.toIntLinearMap := by
    intro w w' h
    have h' : (w 0 + c * w 1, w 0) = (w' 0 + c * w' 1, w' 0) := congrArg Subtype.val h
    rw [Prod.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    have h3 : w 1 = w' 1 := mul_left_cancel₀ hc (by linarith)
    funext i
    fin_cases i
    · exact h2
    · exact h3
  have hsurj : Function.Surjective φ.toIntLinearMap := by
    intro z
    have hz : (z : ℤ × ℤ).1 - (z : ℤ × ℤ).2 ∈ Ideal.span {c} := z.2
    obtain ⟨k', hk'⟩ := Ideal.mem_span_singleton'.mp hz
    refine ⟨![(z : ℤ × ℤ).2, k'], Subtype.ext (Prod.ext ?_ rfl)⟩
    show (z : ℤ × ℤ).2 + c * k' = (z : ℤ × ℤ).1
    linarith
  let e : (Fin 2 → ℤ) ≃ₗ[ℤ] pairRing (Ideal.span {c}) :=
    LinearEquiv.ofBijective φ.toIntLinearMap ⟨hinj, hsurj⟩
  have he : ∀ w, ((e w : pairRing (Ideal.span {c})) : ℤ × ℤ) = (w 0 + c * w 1, w 0) :=
    fun _ => rfl
  haveI : Module.Free ℤ (pairRing (Ideal.span {c})) := Module.Free.of_equiv e
  haveI : Module.Finite ℤ (pairRing (Ideal.span {c})) := Module.Finite.equiv e
  -- multiplication by `α` in these coordinates is a triangular matrix
  have hconj : LinearMap.mulLeft ℤ α = (e : (Fin 2 → ℤ) →ₗ[ℤ] _).comp
      ((Matrix.toLin' !![(α : ℤ × ℤ).2, 0; k, (α : ℤ × ℤ).1]).comp
        (e.symm : _ →ₗ[ℤ] (Fin 2 → ℤ))) := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.mulLeft_apply]
    refine Subtype.ext ?_
    rw [Subring.coe_mul, he, he, Matrix.toLin'_apply]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linear_combination (-(w 0)) * hk
    · simp only [Prod.snd_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      ring
  have hdet : LinearMap.det (LinearMap.mulLeft ℤ α) = (α : ℤ × ℤ).1 * (α : ℤ × ℤ).2 := by
    rw [hconj, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_fin_two_of]
    ring
  have hI : (Ideal.span {α}).restrictScalars ℤ = LinearMap.range (LinearMap.mulLeft ℤ α) := by
    ext z
    rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', LinearMap.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, mul_comm _ _⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, mul_comm _ _⟩
  rw [← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {α})).toEquiv, hI,
    LinearMap.card_quotient_range_eq_natAbs_det_all, hdet]

/-- **The count on two graphs glued along a nonzero ideal** is the absolute value of the norm of
`ℤ × ℤ`. -/
theorem card_pairRing_quotient {J : Ideal ℤ} (hJ : J ≠ ⊥) (α : pairRing J) :
    Nat.card (pairRing J ⧸ Ideal.span {α}) = ((α : ℤ × ℤ).1 * (α : ℤ × ℤ).2).natAbs := by
  obtain ⟨c, rfl⟩ : ∃ c : ℤ, J = Ideal.span {c} :=
    ⟨_, (Ideal.span_singleton_generator J).symm⟩
  have hc : c ≠ 0 := fun h => hJ (by rw [h, Ideal.span_singleton_eq_bot])
  exact card_pairRing_quotient_span hc α

/-- **The count of a section of the square on two graphs.** For `m ≠ n` the functions on
`Γ_m ∪ Γ_n` have `|x_m x_n|` residues modulo the section `x`. -/
theorem card_quotient_graphPair {m n : ℕ+} (hmn : m ≠ n) (x : ghostRing) :
    Nat.card (pairRing (graphIdeal m n) ⧸ Ideal.span {graphPair m n x}) =
      (ghostComponent m x * ghostComponent n x).natAbs :=
  card_pairRing_quotient (graphIdeal_ne_bot hmn) (graphPair m n x)

/-- **The count is exactly quadratic on rays**: `K(k·x) = k² K(x)`. -/
theorem card_quotient_graphPair_intCast_mul {m n : ℕ+} (hmn : m ≠ n) (k : ℤ) (x : ghostRing) :
    Nat.card (pairRing (graphIdeal m n) ⧸ Ideal.span {graphPair m n ((k : ghostRing) * x)}) =
      k.natAbs ^ 2 *
        Nat.card (pairRing (graphIdeal m n) ⧸ Ideal.span {graphPair m n x}) := by
  rw [card_quotient_graphPair hmn, card_quotient_graphPair hmn, map_mul, map_mul, map_intCast,
    map_intCast, Int.cast_id]
  have e : k * ghostComponent m x * (k * ghostComponent n x) =
      k * k * (ghostComponent m x * ghostComponent n x) := by ring
  rw [e, Int.natAbs_mul, Int.natAbs_mul, sq]

/-! ### The count is not a form -/

/-- **The count violates the parallelogram law** on the order of conductor `c ≥ 2`: for
`α = (1, 1)` and `β = (1, 1 − c)`. -/
theorem exists_not_parallelogram_pairRing {c : ℤ} (hc : 2 ≤ c) :
    ∃ α β : pairRing (Ideal.span {c}),
      Nat.card (pairRing (Ideal.span {c}) ⧸ Ideal.span {α + β}) +
          Nat.card (pairRing (Ideal.span {c}) ⧸ Ideal.span {α - β}) ≠
        2 * Nat.card (pairRing (Ideal.span {c}) ⧸ Ideal.span {α}) +
          2 * Nat.card (pairRing (Ideal.span {c}) ⧸ Ideal.span {β}) := by
  have hc0 : c ≠ 0 := by omega
  have hβ : ((1, 1 - c) : ℤ × ℤ) ∈ pairRing (Ideal.span {c}) := by
    show (1 : ℤ) - (1 - c) ∈ Ideal.span {c}
    rw [sub_sub_cancel]
    exact Ideal.subset_span rfl
  refine ⟨1, ⟨(1, 1 - c), hβ⟩, ?_⟩
  rw [card_pairRing_quotient_span hc0, card_pairRing_quotient_span hc0,
    card_pairRing_quotient_span hc0, card_pairRing_quotient_span hc0]
  have e1 : (((1 : pairRing (Ideal.span {c})) + ⟨(1, 1 - c), hβ⟩ :
      pairRing (Ideal.span {c})) : ℤ × ℤ) = (2, 2 - c) := by
    show ((1 : ℤ × ℤ) + (1, 1 - c)) = (2, 2 - c)
    rw [Prod.ext_iff]
    constructor
    · show (1 : ℤ) + 1 = 2
      norm_num
    · show (1 : ℤ) + (1 - c) = 2 - c
      ring
  have e2 : (((1 : pairRing (Ideal.span {c})) - ⟨(1, 1 - c), hβ⟩ :
      pairRing (Ideal.span {c})) : ℤ × ℤ) = (0, c) := by
    show ((1 : ℤ × ℤ) - (1, 1 - c)) = (0, c)
    rw [Prod.ext_iff]
    constructor
    · show (1 : ℤ) - 1 = 0
      norm_num
    · show (1 : ℤ) - (1 - c) = c
      ring
  have e3 : ((1 : pairRing (Ideal.span {c})) : ℤ × ℤ) = (1, 1) := rfl
  rw [e1, e2, e3]
  show ((2 : ℤ) * (2 - c)).natAbs + ((0 : ℤ) * c).natAbs ≠
    2 * ((1 : ℤ) * 1).natAbs + 2 * ((1 : ℤ) * (1 - c)).natAbs
  rw [zero_mul, one_mul, one_mul, Int.natAbs_zero, Int.natAbs_one, Int.natAbs_mul]
  have h1 : (2 - c).natAbs = (c - 2).toNat := by omega
  have h2 : (1 - c).natAbs = (c - 1).toNat := by omega
  rw [h1, h2]
  have h3 : (2 : ℤ).natAbs = 2 := rfl
  rw [h3]
  omega

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
