import GaloisForLFunctions.HTGeometry.MeromorphicGermField
import GaloisForLFunctions.HTGeometry.MilnorKTameSymbol

/-!
# The actual tame boundary of meromorphic germs

Meromorphic order and the punctured limit construct a concrete tame datum on the germ field.
Its residue is a complex unit, and the existing Steinberg theorem supplies the boundary map
`K₂^M(MeroGerm) → ℂˣ`. No valuation or residue existence assumption is used.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Order of a meromorphic germ, independent of its chosen representative. -/
def MeroGerm.order (x : MeroGerm) : WithTop ℤ := meromorphicOrderAt x.rep 0

theorem MeroGerm.order_ofMero {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    (ofMero f hf).order = meromorphicOrderAt f 0 :=
  meromorphicOrderAt_congr (MeroGerm.rep_ofMero hf)

theorem MeroGerm.order_ne_top {x : MeroGerm} (hx : x ≠ 0) : x.order ≠ ⊤ := by
  intro h
  apply hx
  rw [← x.ofMero_rep, ofMero_eq_zero_iff]
  exact meromorphicOrderAt_eq_top_iff.mp h

theorem MeroGerm.order_mul (x y : MeroGerm) :
    (x * y).order = x.order + y.order := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  obtain ⟨g, hg, rfl⟩ := y.exists_rep
  rw [ofMero_mul, MeroGerm.order_ofMero, MeroGerm.order_ofMero,
    MeroGerm.order_ofMero, meromorphicOrderAt_mul hf hg]

@[simp] theorem MeroGerm.order_one : (1 : MeroGerm).order = 0 := by
  rw [← ofMero_one, MeroGerm.order_ofMero, meromorphicOrderAt_const]
  simp

/-- The finite integer order on nonzero germs. -/
def meroGermUnitOrder (a : MeroGermˣ) : ℤ :=
  (a : MeroGerm).order.untop (MeroGerm.order_ne_top a.ne_zero)

theorem meroGermUnitOrder_coe (a : MeroGermˣ) :
    (meroGermUnitOrder a : WithTop ℤ) = (a : MeroGerm).order :=
  WithTop.coe_untop _ _

theorem meroGermUnitOrder_mul (a b : MeroGermˣ) :
    meroGermUnitOrder (a * b) = meroGermUnitOrder a + meroGermUnitOrder b := by
  apply WithTop.coe_injective
  push_cast
  rw [meroGermUnitOrder_coe, meroGermUnitOrder_coe, meroGermUnitOrder_coe]
  exact MeroGerm.order_mul a b

/-- Meromorphic order as a group homomorphism. -/
def meroGermVal : MeroGermˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (meroGermUnitOrder a)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply WithTop.coe_injective
    simpa using meroGermUnitOrder_coe 1
  map_mul' a b := congrArg Multiplicative.ofAdd (meroGermUnitOrder_mul a b)

theorem meroGermVal_mem_ker (a : MeroGermˣ) :
    a ∈ meroGermVal.ker ↔ meroGermUnitOrder a = 0 := by
  change Multiplicative.ofAdd (meroGermUnitOrder a) = 1 ↔ _
  rfl

/-- A punctured limit of a germ. -/
def MeroGerm.HasLimit (x : MeroGerm) (c : ℂ) : Prop :=
  Tendsto x.rep (𝓝[≠] (0 : ℂ)) (𝓝 c)

theorem MeroGerm.hasLimit_ofMero_iff {f : ℂ → ℂ} (hf : MeromorphicAt f 0) (c : ℂ) :
    (ofMero f hf).HasLimit c ↔ Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 c) := by
  constructor
  · intro h
    exact h.congr' (MeroGerm.rep_ofMero hf)
  · intro h
    exact h.congr' (MeroGerm.rep_ofMero hf).symm

theorem MeroGerm.HasLimit.unique {x : MeroGerm} {a b : ℂ}
    (ha : x.HasLimit a) (hb : x.HasLimit b) : a = b :=
  tendsto_nhds_unique ha hb

theorem MeroGerm.hasLimit_const (c : ℂ) : (constGerm c).HasLimit c :=
  (MeroGerm.hasLimit_ofMero_iff (MeromorphicAt.const c 0) c).mpr tendsto_const_nhds

theorem MeroGerm.HasLimit.mul {x y : MeroGerm} {a b : ℂ}
    (hx : x.HasLimit a) (hy : y.HasLimit b) : (x * y).HasLimit (a * b) := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  obtain ⟨g, hg, rfl⟩ := y.exists_rep
  rw [MeroGerm.hasLimit_ofMero_iff] at hx hy
  rw [ofMero_mul, MeroGerm.hasLimit_ofMero_iff]
  exact hx.mul hy

theorem MeroGerm.HasLimit.sub {x y : MeroGerm} {a b : ℂ}
    (hx : x.HasLimit a) (hy : y.HasLimit b) : (x - y).HasLimit (a - b) := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  obtain ⟨g, hg, rfl⟩ := y.exists_rep
  rw [MeroGerm.hasLimit_ofMero_iff] at hx hy
  rw [ofMero_sub, MeroGerm.hasLimit_ofMero_iff]
  exact hx.sub hy

theorem MeroGerm.HasLimit.inv {x : MeroGerm} {a : ℂ}
    (hx : x.HasLimit a) (ha : a ≠ 0) : x⁻¹.HasLimit a⁻¹ := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  rw [MeroGerm.hasLimit_ofMero_iff] at hx
  rw [ofMero_inv, MeroGerm.hasLimit_ofMero_iff]
  exact hx.inv₀ ha

theorem meroGermUnitOrder_eq_zero_of_limit {a : MeroGermˣ} {c : ℂ}
    (hc : c ≠ 0) (h : (a : MeroGerm).HasLimit c) : meroGermUnitOrder a = 0 := by
  apply WithTop.coe_injective
  rw [meroGermUnitOrder_coe]
  exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
    (a : MeroGerm).rep_mero).mp ⟨c, hc, h⟩

theorem meroGermUnitOrder_nonneg_of_limit {a : MeroGermˣ} {c : ℂ}
    (h : (a : MeroGerm).HasLimit c) : 0 ≤ meroGermUnitOrder a := by
  have ho := (tendsto_nhds_iff_meromorphicOrderAt_nonneg
    (a : MeroGerm).rep_mero).mp ⟨c, h⟩
  change 0 ≤ (a : MeroGerm).order at ho
  rw [← meroGermUnitOrder_coe] at ho
  exact_mod_cast ho

theorem meroGerm_hasLimit_zero_of_order_pos {a : MeroGermˣ}
    (h : 0 < meroGermUnitOrder a) : (a : MeroGerm).HasLimit 0 := by
  apply tendsto_zero_of_meromorphicOrderAt_pos
  change 0 < (a : MeroGerm).order
  rw [← meroGermUnitOrder_coe]
  exact_mod_cast h

private theorem meroGerm_res_exists (a : meroGermVal.ker) :
    ∃ c : ℂ, c ≠ 0 ∧ (a.1 : MeroGerm).HasLimit c := by
  apply tendsto_ne_zero_of_meromorphicOrderAt_eq_zero (a.1 : MeroGerm).rep_mero
  change (a.1 : MeroGerm).order = 0
  rw [← meroGermUnitOrder_coe, (meroGermVal_mem_ker a.1).mp a.2]
  rfl

/-- The actual nonzero punctured limit, as a unit of the residue field. -/
def meroGermResValue (a : meroGermVal.ker) : ℂˣ :=
  Units.mk0 (meroGerm_res_exists a).choose (meroGerm_res_exists a).choose_spec.1

theorem meroGermResValue_hasLimit (a : meroGermVal.ker) :
    (a.1 : MeroGerm).HasLimit (meroGermResValue a : ℂ) :=
  (meroGerm_res_exists a).choose_spec.2

theorem meroGermResValue_eq {a : meroGermVal.ker} {c : ℂ}
    (h : (a.1 : MeroGerm).HasLimit c) : (meroGermResValue a : ℂ) = c :=
  (meroGermResValue_hasLimit a).unique h

/-- Residue is multiplicative on order-zero units. -/
def meroGermRes : meroGermVal.ker →* ℂˣ where
  toFun := meroGermResValue
  map_one' := by
    apply Units.ext
    exact meroGermResValue_eq (MeroGerm.hasLimit_const 1)
  map_mul' a b := by
    apply Units.ext
    exact meroGermResValue_eq ((meroGermResValue_hasLimit a).mul
      (meroGermResValue_hasLimit b))

private theorem meroGerm_oneSub_pos {a : MeroGermˣ} (ha : (a : MeroGerm) ≠ 1)
    (h : 0 < meroGermUnitOrder a) :
    ∃ hb : oneSubUnit ha ∈ meroGermVal.ker, meroGermRes ⟨oneSubUnit ha, hb⟩ = 1 := by
  have hlim : ((oneSubUnit ha : MeroGermˣ) : MeroGerm).HasLimit 1 := by
    simpa only [map_one, sub_zero, oneSubUnit_val] using
      (MeroGerm.hasLimit_const 1).sub (meroGerm_hasLimit_zero_of_order_pos h)
  have hb := (meroGermVal_mem_ker _).mpr (meroGermUnitOrder_eq_zero_of_limit one_ne_zero hlim)
  refine ⟨hb, Units.ext ?_⟩
  exact meroGermResValue_eq hlim

private theorem meroGerm_oneSub_zero {a : MeroGermˣ} (ha : (a : MeroGerm) ≠ 1)
    (h : a ∈ meroGermVal.ker) :
    0 ≤ meroGermUnitOrder (oneSubUnit ha) ∧
      (0 < meroGermUnitOrder (oneSubUnit ha) → meroGermRes ⟨a, h⟩ = 1) := by
  have hlim := (MeroGerm.hasLimit_const 1).sub (meroGermResValue_hasLimit ⟨a, h⟩)
  refine ⟨meroGermUnitOrder_nonneg_of_limit (a := oneSubUnit ha) hlim, ?_⟩
  intro hp
  have hz := hlim.unique (meroGerm_hasLimit_zero_of_order_pos hp)
  apply Units.ext
  exact (sub_eq_zero.mp hz).symm

private theorem meroGerm_oneSub_neg {a : MeroGermˣ} (ha : (a : MeroGerm) ≠ 1)
    (h : meroGermUnitOrder a < 0) :
    meroGermUnitOrder (oneSubUnit ha) = meroGermUnitOrder a ∧
      ∃ hc : a * (oneSubUnit ha)⁻¹ ∈ meroGermVal.ker,
        meroGermRes ⟨a * (oneSubUnit ha)⁻¹, hc⟩ = -1 := by
  have hinv : meroGermUnitOrder a⁻¹ = -meroGermUnitOrder a := by
    exact congrArg Multiplicative.toAdd (map_inv meroGermVal a)
  have hinvlim : (a : MeroGerm)⁻¹.HasLimit 0 := by
    simpa only [Units.val_inv_eq_inv_val] using
      meroGerm_hasLimit_zero_of_order_pos (a := a⁻¹) (by rw [hinv]; omega)
  have hclim : ((a * (oneSubUnit ha)⁻¹ : MeroGermˣ) : MeroGerm).HasLimit (-1) := by
    have heq : ((a * (oneSubUnit ha)⁻¹ : MeroGermˣ) : MeroGerm) =
        ((a : MeroGerm)⁻¹ - 1)⁻¹ := by
      change (a : MeroGerm) * (1 - (a : MeroGerm))⁻¹ = _
      field_simp
    rw [heq]
    simpa using (hinvlim.sub (MeroGerm.hasLimit_const 1)).inv (by norm_num)
  have hc := (meroGermVal_mem_ker _).mpr
    (meroGermUnitOrder_eq_zero_of_limit (by norm_num) hclim)
  refine ⟨?_, hc, Units.ext (meroGermResValue_eq hclim)⟩
  have hv := (meroGermVal_mem_ker _).mp hc
  rw [meroGermUnitOrder_mul] at hv
  have hi : meroGermUnitOrder (oneSubUnit ha)⁻¹ = -meroGermUnitOrder (oneSubUnit ha) :=
    congrArg Multiplicative.toAdd (map_inv meroGermVal (oneSubUnit ha))
  rw [hi] at hv
  omega

/-- Concrete meromorphic order and complex residue satisfy all Steinberg boundary clauses. -/
def meroGermTameData : TameData MeroGerm ℂ where
  val := meroGermVal
  res := meroGermRes
  res_neg_one h := by
    apply Units.ext
    exact meroGermResValue_eq (MeroGerm.hasLimit_const (-1))
  oneSub_of_pos := meroGerm_oneSub_pos
  oneSub_of_zero := meroGerm_oneSub_zero
  oneSub_of_neg := meroGerm_oneSub_neg

/-- The local relative K2 boundary, with an actual complex residue target. -/
def meroGermTameBoundary : MilnorKDeg MeroGerm 2 →+ Additive ℂˣ :=
  meroGermTameData.tameHom

theorem meroGermTameBoundary_symbol (a b : MeroGermˣ) :
    meroGermTameBoundary (milnorClassDeg MeroGerm 2 ⟨[a, b], rfl⟩) =
      Additive.ofMul (meroGermTameData.tame a b) :=
  meroGermTameData.tameHom_symbol a b

/-- A nonzero meromorphic function supplies a unit of the germ field, even at a zero or pole. -/
def meroGermUnitOf (f : ℂ → ℂ) (hf : MeromorphicAt f 0)
    (hfin : meromorphicOrderAt f 0 ≠ ⊤) : MeroGermˣ :=
  Units.mk0 (ofMero f hf) (by
    intro hzero
    exact hfin (meromorphicOrderAt_eq_top_iff.mpr ((ofMero_eq_zero_iff hf).mp hzero)))

theorem meroGermUnitOf_order (f : ℂ → ℂ) (hf : MeromorphicAt f 0)
    (hfin : meromorphicOrderAt f 0 ≠ ⊤) :
    (meroGermUnitOrder (meroGermUnitOf f hf hfin) : WithTop ℤ) =
      meromorphicOrderAt f 0 := by
  rw [meroGermUnitOrder_coe]
  exact MeroGerm.order_ofMero hf

/-- Complex value of the actual K2 boundary. -/
def meroGermTameBoundaryValue (x : MilnorKDeg MeroGerm 2) : ℂ :=
  (Additive.toMul (meroGermTameBoundary x) : ℂˣ)

@[simp] theorem meroGermTameBoundaryValue_zero : meroGermTameBoundaryValue 0 = 1 := by
  simp [meroGermTameBoundaryValue]

theorem meroGermTameBoundaryValue_add (x y : MilnorKDeg MeroGerm 2) :
    meroGermTameBoundaryValue (x + y) =
      meroGermTameBoundaryValue x * meroGermTameBoundaryValue y := by
  simp [meroGermTameBoundaryValue]

theorem meroGermTameBoundaryValue_sub (x y : MilnorKDeg MeroGerm 2) :
    meroGermTameBoundaryValue (x - y) =
      meroGermTameBoundaryValue x / meroGermTameBoundaryValue y := by
  simp [meroGermTameBoundaryValue]

/-- The boundary of a holomorphic-unit/divisor symbol retains the full signed order. -/
theorem meroGermTameBoundaryValue_symbol_of_limit
    (a b : MeroGermˣ) {c : ℂ} (hc : c ≠ 0) (hlim : (a : MeroGerm).HasLimit c) :
    meroGermTameBoundaryValue (milnorClassDeg MeroGerm 2 ⟨[a, b], rfl⟩) =
      c ^ meroGermUnitOrder b := by
  have hk : a ∈ meroGermTameData.val.ker :=
    (meroGermVal_mem_ker a).mpr (meroGermUnitOrder_eq_zero_of_limit hc hlim)
  rw [meroGermTameBoundaryValue, meroGermTameBoundary_symbol,
    meroGermTameData.tame_of_mem_ker_left hk]
  change ((meroGermResValue ⟨a, hk⟩ ^ meroGermUnitOrder b : ℂˣ) : ℂ) = _
  push_cast
  rw [meroGermResValue_eq hlim]

end
end GaloisForLFunctions.HTGeometry
