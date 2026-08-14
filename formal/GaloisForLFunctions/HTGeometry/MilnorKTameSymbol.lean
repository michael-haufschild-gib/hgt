import GaloisForLFunctions.HTGeometry.MilnorKDegFunctoriality

/-!
# The tame symbol on degree-two Milnor `K`-theory

A discrete valuation on a field, together with the residue homomorphism on the units of valuation
zero, defines the tame symbol

`∂{a, b} = residue of (-1)^{v(a)v(b)} a^{v(b)} b^{-v(a)}`,

whose argument has valuation zero by construction.  The symbol is bimultiplicative because the
valuation and the residue are homomorphisms, and it kills the Steinberg relation by a four-way
case analysis on the valuations of `a` and `1 - a`: if `v(a) > 0` the residue of `1 - a` is one; if
`v(a) = 0` and `v(1-a) > 0` the residue of `a` is one; if `v(a) = 0 = v(1-a)` the argument is
trivial; and if `v(a) < 0` then `v(1-a) = v(a)` and the residue of `a(1-a)^{-1}` is `-1`, whose
`n² + n` power is one.  Hence the tame symbol descends to `K_2^M`.

* `TameData` : **the valuation-plus-residue data.**
* `TameData.tame` : **the tame symbol of a pair of units.**
* `TameData.tame_steinberg` : **it kills the Steinberg relation.**
* `TameData.tameHom` : **the induced homomorphism `K_2^M(K) → k^×`.**
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A discrete valuation on a field together with its residue homomorphism.**  The three
Steinberg clauses are the standard behaviour of `1 - a` under a discrete valuation. -/
structure TameData (K : Type*) [Field K] (k : Type*) [Field k] where
  /-- the valuation, as a homomorphism to the integers written multiplicatively -/
  val : Kˣ →* Multiplicative ℤ
  /-- the residue homomorphism on the units of valuation zero -/
  res : val.ker →* kˣ
  /-- the residue of `-1` is `-1` -/
  res_neg_one : ∀ h : (-1 : Kˣ) ∈ val.ker, res ⟨-1, h⟩ = -1
  /-- a unit of positive valuation has `1 - a` of valuation zero and residue one -/
  oneSub_of_pos : ∀ {a : Kˣ} (ha : (a : K) ≠ 1), 0 < Multiplicative.toAdd (val a) →
    ∃ h : oneSubUnit ha ∈ val.ker, res ⟨oneSubUnit ha, h⟩ = 1
  /-- for a unit of valuation zero, `1 - a` has nonnegative valuation, and positive valuation
  forces the residue of `a` to be one -/
  oneSub_of_zero : ∀ {a : Kˣ} (ha : (a : K) ≠ 1) (h : a ∈ val.ker),
    0 ≤ Multiplicative.toAdd (val (oneSubUnit ha)) ∧
      (0 < Multiplicative.toAdd (val (oneSubUnit ha)) → res ⟨a, h⟩ = 1)
  /-- a unit of negative valuation has `1 - a` of the same valuation, and the quotient has
  residue `-1` -/
  oneSub_of_neg : ∀ {a : Kˣ} (ha : (a : K) ≠ 1), Multiplicative.toAdd (val a) < 0 →
    Multiplicative.toAdd (val (oneSubUnit ha)) = Multiplicative.toAdd (val a) ∧
      ∃ h : a * (oneSubUnit ha)⁻¹ ∈ val.ker, res ⟨a * (oneSubUnit ha)⁻¹, h⟩ = -1

namespace TameData

variable {K : Type*} [Field K] {k : Type*} [Field k] (D : TameData K k)

/-- The integer valuation of a unit. -/
def v (a : Kˣ) : ℤ := Multiplicative.toAdd (D.val a)

theorem v_mul (a b : Kˣ) : D.v (a * b) = D.v a + D.v b := by
  rw [v, v, v, map_mul]
  rfl

theorem v_zpow (a : Kˣ) (n : ℤ) : D.v (a ^ n) = n * D.v a := by
  rw [v, v, map_zpow]
  simp

theorem mem_ker_iff {a : Kˣ} : a ∈ D.val.ker ↔ D.v a = 0 := by
  rw [MonoidHom.mem_ker, v]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact Multiplicative.toAdd.injective h

/-- The valuation of `-1` is zero. -/
theorem v_neg_one : D.v (-1 : Kˣ) = 0 := by
  have hsq : ((-1 : Kˣ) * (-1 : Kˣ)) = 1 := by
    ext
    norm_num
  have h := D.v_mul (-1) (-1)
  rw [hsq] at h
  have h1 : D.v (1 : Kˣ) = 0 := by
    rw [v, map_one]
    rfl
  omega

/-! ## The tame symbol -/

/-- The unit whose residue is the tame symbol. -/
def symbolUnit (a b : Kˣ) : Kˣ := (-1) ^ (D.v a * D.v b) * a ^ D.v b * b ^ (-D.v a)

theorem symbolUnit_mem (a b : Kˣ) : D.symbolUnit a b ∈ D.val.ker := by
  rw [mem_ker_iff, symbolUnit, D.v_mul, D.v_mul, D.v_zpow, D.v_zpow, D.v_zpow, D.v_neg_one]
  ring

/-- **The tame symbol** of a pair of units. -/
def tame (a b : Kˣ) : kˣ := D.res ⟨D.symbolUnit a b, D.symbolUnit_mem a b⟩

theorem tame_eq_res {a b : Kˣ} (h : D.symbolUnit a b ∈ D.val.ker) :
    D.tame a b = D.res ⟨D.symbolUnit a b, h⟩ := rfl

/-- **The tame symbol is multiplicative in the first entry.** -/
theorem tame_mul_left (a a' b : Kˣ) : D.tame (a * a') b = D.tame a b * D.tame a' b := by
  have hu : D.symbolUnit (a * a') b = D.symbolUnit a b * D.symbolUnit a' b := by
    rw [symbolUnit, symbolUnit, symbolUnit, D.v_mul, add_mul, zpow_add,
      mul_zpow, neg_add, zpow_add]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  have := D.res.map_mul ⟨D.symbolUnit a b, D.symbolUnit_mem a b⟩
    ⟨D.symbolUnit a' b, D.symbolUnit_mem a' b⟩
  rw [tame, tame, tame]
  rw [← this]
  congr 1
  exact Subtype.ext hu

/-- **The tame symbol is multiplicative in the second entry.** -/
theorem tame_mul_right (a b b' : Kˣ) : D.tame a (b * b') = D.tame a b * D.tame a b' := by
  have hu : D.symbolUnit a (b * b') = D.symbolUnit a b * D.symbolUnit a b' := by
    rw [symbolUnit, symbolUnit, symbolUnit, D.v_mul, mul_add,
      zpow_add, zpow_add, mul_zpow]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  have := D.res.map_mul ⟨D.symbolUnit a b, D.symbolUnit_mem a b⟩
    ⟨D.symbolUnit a b', D.symbolUnit_mem a b'⟩
  rw [tame, tame, tame]
  rw [← this]
  congr 1
  exact Subtype.ext hu

/-! ## The Steinberg relation -/

theorem res_zpow {x : Kˣ} (hx : x ∈ D.val.ker) (n : ℤ) (hxn : x ^ n ∈ D.val.ker) :
    D.res ⟨x ^ n, hxn⟩ = (D.res ⟨x, hx⟩) ^ n := by
  have hsub : (⟨x, hx⟩ : D.val.ker) ^ n = ⟨x ^ n, hxn⟩ := Subtype.ext (by push_cast; rfl)
  rw [← hsub, map_zpow]

theorem neg_one_mem_ker : (-1 : Kˣ) ∈ D.val.ker := D.mem_ker_iff.2 D.v_neg_one

/-- **The tame symbol kills the Steinberg relation.** -/
theorem tame_steinberg {a : Kˣ} (ha : (a : K) ≠ 1) : D.tame a (oneSubUnit ha) = 1 := by
  set b : Kˣ := oneSubUnit ha with hb
  rcases lt_trichotomy (D.v a) 0 with hm | hm | hm
  · -- negative valuation: the quotient has residue `-1`, and `m² + m` is even
    obtain ⟨hn, hq, hres⟩ := D.oneSub_of_neg ha hm
    have hnv : D.v b = D.v a := hn
    have hquot : D.symbolUnit a b = (-1 : Kˣ) ^ (D.v a * D.v a) * (a * b⁻¹) ^ D.v a := by
      rw [symbolUnit, hnv, mul_zpow, inv_zpow, ← zpow_neg]
      simp only [mul_assoc]
    have hmem : (-1 : Kˣ) ^ (D.v a * D.v a) ∈ D.val.ker :=
      D.mem_ker_iff.2 (by rw [D.v_zpow, D.v_neg_one, mul_zero])
    have hmem2 : (a * b⁻¹) ^ D.v a ∈ D.val.ker := by
      refine D.mem_ker_iff.2 ?_
      rw [D.v_zpow, (D.mem_ker_iff.1 hq), mul_zero]
    have hsplit : D.tame a b
        = D.res ⟨(-1 : Kˣ) ^ (D.v a * D.v a), hmem⟩ * D.res ⟨(a * b⁻¹) ^ D.v a, hmem2⟩ := by
      rw [tame]
      rw [← map_mul]
      congr 1
      exact Subtype.ext (by push_cast; exact hquot)
    rw [hsplit, D.res_zpow D.neg_one_mem_ker _ hmem, D.res_zpow hq _ hmem2,
      D.res_neg_one D.neg_one_mem_ker, hres]
    have heven : ∃ j : ℤ, D.v a * D.v a + D.v a = 2 * j := ⟨(D.v a * D.v a + D.v a) / 2, by
      have : (2 : ℤ) ∣ D.v a * D.v a + D.v a := by
        have := Int.even_mul_succ_self (D.v a)
        rcases this with ⟨j, hj⟩
        exact ⟨j, by linarith [hj]⟩
      omega⟩
    obtain ⟨j, hj⟩ := heven
    rw [← zpow_add]
    rw [hj, zpow_mul]
    have hsq : ((-1 : kˣ)) ^ (2 : ℤ) = 1 := by
      ext
      norm_num
    rw [hsq, one_zpow]
  · -- zero valuation
    have hker : a ∈ D.val.ker := D.mem_ker_iff.2 hm
    obtain ⟨hnn, hres⟩ := D.oneSub_of_zero ha hker
    have hnv : 0 ≤ D.v b := hnn
    rcases eq_or_lt_of_le hnv with hz | hp
    · -- both valuations vanish
      have hu : D.symbolUnit a b = 1 := by
        rw [symbolUnit, hm, ← hz]
        norm_num
      rw [tame]
      have : (⟨D.symbolUnit a b, D.symbolUnit_mem a b⟩ : D.val.ker) = 1 := Subtype.ext (by
        push_cast
        exact hu)
      rw [this, map_one]
    · -- `1 - a` has positive valuation, so `a` has residue one
      have hu : D.symbolUnit a b = a ^ D.v b := by
        rw [symbolUnit, hm]
        norm_num
      have hmem : a ^ D.v b ∈ D.val.ker := D.mem_ker_iff.2 (by rw [D.v_zpow, hm, mul_zero])
      have : D.tame a b = D.res ⟨a ^ D.v b, hmem⟩ := by
        rw [tame]
        congr 1
        exact Subtype.ext (by push_cast; exact hu)
      rw [this, D.res_zpow hker _ hmem, hres hp, one_zpow]
  · -- positive valuation: `1 - a` has residue one
    obtain ⟨hker, hres⟩ := D.oneSub_of_pos ha hm
    have hnv : D.v b = 0 := D.mem_ker_iff.1 hker
    have hu : D.symbolUnit a b = b ^ (-D.v a) := by
      rw [symbolUnit, hnv]
      norm_num
    have hmem : b ^ (-D.v a) ∈ D.val.ker := D.mem_ker_iff.2 (by rw [D.v_zpow, hnv, mul_zero])
    have hval : D.tame a b = D.res ⟨b ^ (-D.v a), hmem⟩ := by
      rw [tame]
      congr 1
      exact Subtype.ext (by push_cast; exact hu)
    rw [hval, D.res_zpow hker _ hmem, hres, one_zpow]


/-- **Units of valuation zero have trivial tame symbol.**  This is why the tame symbol of a fixed
pair is nontrivial at only finitely many places of a number field. -/
theorem tame_eq_one_of_mem_ker {a b : Kˣ} (ha : a ∈ D.val.ker) (hb : b ∈ D.val.ker) :
    D.tame a b = 1 := by
  have hu : D.symbolUnit a b = 1 := by
    rw [symbolUnit, D.mem_ker_iff.1 ha, D.mem_ker_iff.1 hb]
    norm_num
  rw [tame]
  have : (⟨D.symbolUnit a b, D.symbolUnit_mem a b⟩ : D.val.ker) = 1 :=
    Subtype.ext (by push_cast; exact hu)
  rw [this, map_one]


/-- **Normalization at a uniformizer.**  If `b` has valuation zero then the tame symbol of
`(b, a)` is the residue of `b` raised to the valuation of `a`. -/
theorem tame_of_mem_ker_left {a b : Kˣ} (hb : b ∈ D.val.ker) :
    D.tame b a = D.res ⟨b, hb⟩ ^ D.v a := by
  have hu : D.symbolUnit b a = b ^ D.v a := by
    rw [symbolUnit, D.mem_ker_iff.1 hb]
    norm_num
  have hmem : b ^ D.v a ∈ D.val.ker := D.mem_ker_iff.2 (by
    rw [D.v_zpow, D.mem_ker_iff.1 hb, mul_zero])
  have hval : D.tame b a = D.res ⟨b ^ D.v a, hmem⟩ := by
    rw [tame]
    congr 1
    exact Subtype.ext (by push_cast; exact hu)
  rw [hval, D.res_zpow hb _ hmem]

/-- **Normalization at a uniformizer, other slot.**  If `b` has valuation zero then the tame symbol
of `(a, b)` is the inverse residue of `b` raised to the valuation of `a`. -/
theorem tame_of_mem_ker_right {a b : Kˣ} (hb : b ∈ D.val.ker) :
    D.tame a b = (D.res ⟨b, hb⟩) ^ (-D.v a) := by
  have hu : D.symbolUnit a b = b ^ (-D.v a) := by
    rw [symbolUnit, D.mem_ker_iff.1 hb]
    norm_num
  have hmem : b ^ (-D.v a) ∈ D.val.ker := D.mem_ker_iff.2 (by
    rw [D.v_zpow, D.mem_ker_iff.1 hb, mul_zero])
  have hval : D.tame a b = D.res ⟨b ^ (-D.v a), hmem⟩ := by
    rw [tame]
    congr 1
    exact Subtype.ext (by push_cast; exact hu)
  rw [hval, D.res_zpow hb _ hmem]

/-- **A finite residue field makes every tame symbol torsion.** -/
theorem tame_isOfFinOrder [Finite kˣ] (a b : Kˣ) : IsOfFinOrder (D.tame a b) :=
  isOfFinOrder_of_finite _


/-! ## Descent to `K_2^M` -/

/-- The tame symbol read off a degree-two symbol. -/
def tameOnSymbol (s : MilnorSymbolDeg K 2) : Additive kˣ :=
  Additive.ofMul (D.tame (s.val.getD 0 1) (s.val.getD 1 1))

/-- The tame symbol on formal sums of degree-two symbols. -/
def tamePre : FreeAbelianGroup (MilnorSymbolDeg K 2) →+ Additive kˣ :=
  FreeAbelianGroup.lift D.tameOnSymbol

@[simp]
theorem tamePre_of (s : MilnorSymbolDeg K 2) : D.tamePre (FreeAbelianGroup.of s)
    = D.tameOnSymbol s := by
  simp [tamePre]

theorem tamePre_rel : ∀ x ∈ milnorRelSubgroupDeg K 2, D.tamePre x = 0 := by
  intro x hx
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (⟨a, b, l₁, l₂, h, rfl⟩ | ⟨a, ha, l₁, l₂, h, rfl⟩)
    · rw [map_sub, map_sub, tamePre_of, tamePre_of, tamePre_of]
      rcases l₁ with _ | ⟨c, t₁⟩
      · rcases l₂ with _ | ⟨d, t₂⟩
        · exact absurd h (by simp)
        · rcases t₂ with _ | ⟨e, t₃⟩
          · simp only [tameOnSymbol, List.nil_append, List.getD_cons_zero,
              List.getD_cons_succ, D.tame_mul_left, ofMul_mul]
            abel
          · exact absurd h (by simp)
      · rcases t₁ with _ | ⟨e, t₃⟩
        · rcases l₂ with _ | ⟨d, t₂⟩
          · simp only [tameOnSymbol, List.cons_append, List.nil_append,
              List.getD_cons_zero, List.getD_cons_succ, D.tame_mul_right, ofMul_mul]
            abel
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    · rcases l₁ with _ | ⟨c, t₁⟩
      · rcases l₂ with _ | ⟨d, t₂⟩
        · rw [tamePre_of]
          simp only [tameOnSymbol, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
            D.tame_steinberg]
          rfl
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  · exact map_zero _
  · intro y z _ _ hy hz
    rw [map_add, hy, hz, add_zero]
  · intro y _ hy
    rw [map_neg, hy, neg_zero]

/-- **The tame symbol as a homomorphism out of `K_2^M(K)`.** -/
def tameHom : MilnorKDeg K 2 →+ Additive kˣ :=
  QuotientAddGroup.lift _ D.tamePre D.tamePre_rel

@[simp]
theorem tameHom_class (s : MilnorSymbolDeg K 2) :
    D.tameHom (milnorClassDeg K 2 s) = D.tameOnSymbol s := D.tamePre_of s

theorem tameHom_symbol (a b : Kˣ) :
    D.tameHom (milnorClassDeg K 2 ⟨[a, b], rfl⟩) = Additive.ofMul (D.tame a b) := by
  rw [tameHom_class]
  rfl


end TameData

end GaloisForLFunctions.HTGeometry
