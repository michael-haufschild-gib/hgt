import GaloisForLFunctions.HTGeometry.SiegelSubsetProduct
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Removing mandatory gaps from an ordered packet

In each coordinate order, subtracting the rank times the required gap
turns a separated box into an ordinary box chamber. The translations
preserve volume, and ties between coordinate orders are null.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coordinates in `[d,r]` whose pairwise distances are at least `d`. -/
def separatedCoordinateBox (J : Type*) (d r : ℝ) : Set (J → ℝ) :=
  {x | (∀ j, x j ∈ Icc d r) ∧ Pairwise (fun i j => d ≤ |x j - x i|)}

private def coordinateOrderChamber {J : Type*} {n : ℕ} (e : Fin n ≃ J) (u : ℝ) : Set (J → ℝ) :=
  {x | (∀ j, x j ∈ Icc 0 u) ∧ Monotone (fun i => x (e i))}

private def gapOffset {J : Type*} {n : ℕ} (e : Fin n ≃ J) (d : ℝ) (j : J) : ℝ :=
  d * (((e.symm j).val : ℝ) + 1)

private theorem isClosed_coordinateOrderChamber {J : Type*} {n : ℕ} (e : Fin n ≃ J) (u : ℝ) :
    IsClosed (coordinateOrderChamber e u) := by
  have h : coordinateOrderChamber e u = (⋂ j : J, (fun x : J → ℝ => x j) ⁻¹' Icc 0 u) ∩
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i ≤ j), {x : J → ℝ | x (e i) ≤ x (e j)} := by
    ext x
    simp only [coordinateOrderChamber, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_preimage, Monotone]
  rw [h]
  exact (isClosed_iInter fun j => isClosed_Icc.preimage (continuous_apply j)).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply (e i)) (continuous_apply (e j)))

private theorem exists_coordinateOrder {J : Type*} [Fintype J] {x : J → ℝ} (hx : Function.Injective x) :
    ∃ e : Fin (Fintype.card J) ≃ J, StrictMono (fun j => x (e j)) := by
  classical
  let s := Finset.univ.image x
  have hc : s.card = Fintype.card J := by
    dsimp only [s]
    rw [Finset.card_image_of_injective _ hx, Finset.card_univ]
  let f : J → s := fun j => ⟨x j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hf : Function.Bijective f := ⟨fun _ _ h => hx (congrArg Subtype.val h), fun y => by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp y.property
    exact ⟨j, Subtype.ext hj⟩⟩
  let e := Equiv.ofBijective f hf
  let o := s.orderIsoOfFin hc
  refine ⟨o.toEquiv.trans e.symm, ?_⟩
  have he (j : Fin (Fintype.card J)) : x (e.symm (o j)) = (o j).val :=
    congrArg Subtype.val (e.apply_symm_apply (o j))
  intro i j hij
  change x (e.symm (o i)) < x (e.symm (o j))
  rw [he, he]
  exact o.strictMono hij

private theorem coordinateOrder_unique {J : Type*} {n : ℕ} {x : J → ℝ} (hx : Function.Injective x)
    {e f : Fin n ≃ J} (he : Monotone (fun j => x (e j))) (hf : Monotone (fun j => x (f j))) : e = f := by
  have hs (g : Fin n ≃ J) (hg : Monotone (fun j => x (g j))) : StrictMono (fun j => x (g j)) :=
    fun _ _ h => lt_of_le_of_ne (hg h.le) (fun h' => h.ne (g.injective (hx h')))
  let p := e.trans f.symm
  have hp (i : Fin n) : f (p i) = e i := by simp only [p, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hps (i : Fin n) : e (p.symm i) = f i := by
    change e (e.symm (f i)) = f i
    exact e.apply_symm_apply _
  have hm : StrictMono p := by
    intro i j hij
    apply (hs f hf).lt_iff_lt.mp
    simpa only [hp] using hs e he hij
  have hms : StrictMono p.symm := by
    intro i j hij
    apply (hs e he).lt_iff_lt.mp
    simpa only [hps] using hs f hf hij
  have heq (i : Fin n) : p i = i := by
    apply Fin.ext
    exact le_antisymm (by simpa only [Equiv.symm_apply_apply] using le_val_of_strictMono hms (p i))
      (le_val_of_strictMono hm i)
  ext i
  rw [← hp i, heq i]

private theorem monotone_remove_gap {n : ℕ} (g : Fin n → ℝ) (d : ℝ)
    (hgap : ∀ i j, i < j → d ≤ g j - g i) :
    Monotone (fun i => g i - d * ((i.val : ℝ) + 1)) := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      have h := hgap i.castSucc i.succ Fin.castSucc_lt_succ
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      linarith only [h]

private theorem separatedCoordinateBox_injective {J : Type*} {d r : ℝ} (hd : 0 < d)
    {x : J → ℝ} (hx : x ∈ separatedCoordinateBox J d r) : Function.Injective x := by
  intro i j hij
  by_contra hne
  have h := hx.2 hne
  change d ≤ |x j - x i| at h
  rw [hij, sub_self, abs_zero] at h
  exact (not_le_of_gt hd) h

private theorem mem_translated_coordinateOrderChamber {J : Type*} {n : ℕ} (e : Fin n ≃ J) {d r : ℝ}
    (hd : 0 < d) (x : J → ℝ) :
    x + -gapOffset e d ∈ coordinateOrderChamber e (r - (n : ℝ) * d) ↔
      x ∈ separatedCoordinateBox J d r ∧ Monotone (fun i => x (e i)) := by
  let y := x + -gapOffset e d
  have hy (i : Fin n) : y (e i) = x (e i) - d * ((i.val : ℝ) + 1) := by
    simp only [y, gapOffset, Pi.add_apply, Pi.neg_apply, Equiv.symm_apply_apply, sub_eq_add_neg]
  have hx (i : Fin n) : x (e i) = y (e i) + d * ((i.val : ℝ) + 1) := by rw [hy, sub_add_cancel]
  change y ∈ coordinateOrderChamber e _ ↔ _
  constructor
  · rintro ⟨hbox, hm⟩
    have hgap (i j : Fin n) (hij : i < j) : d ≤ x (e j) - x (e i) := by
      have hc : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Fin.lt_def.mp hij)
      have h := mul_le_mul_of_nonneg_left hc hd.le
      rw [hx i, hx j]
      linarith only [hm hij.le, h]
    have hstrict : StrictMono (fun i => x (e i)) := fun i j hij => by
      linarith only [hgap i j hij, hd]
    refine ⟨⟨?_, ?_⟩, hstrict.monotone⟩
    · intro j
      let i := e.symm j
      have he : e i = j := e.apply_symm_apply j
      have hi : (i.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
      have hlo : d ≤ d * ((i.val : ℝ) + 1) := by
        have h : (1 : ℝ) ≤ (i.val : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) i.val]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left h hd.le
      have hhi := mul_le_mul_of_nonneg_left hi hd.le
      have h := hbox (e i)
      rw [← he, hx]
      exact ⟨by linarith only [h.1, hlo], by linarith only [h.2, hhi]⟩
    · intro i j hij
      let a := e.symm i
      let b := e.symm j
      have ha : e a = i := e.apply_symm_apply i
      have hb : e b = j := e.apply_symm_apply j
      have hab : a ≠ b := fun h => hij (by rw [← ha, ← hb, h])
      rw [← ha, ← hb]
      rcases lt_or_gt_of_ne hab with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr (hstrict.monotone h.le))]
        exact hgap _ _ h
      · rw [abs_of_nonpos (sub_nonpos.mpr (hstrict.monotone h.le)), neg_sub]
        exact hgap _ _ h
  · rintro ⟨⟨hbox, hsep⟩, hm⟩
    have hg (i j : Fin n) (hij : i < j) : d ≤ x (e j) - x (e i) := by
      have he := hsep (fun h => hij.ne (e.injective h))
      change d ≤ |x (e j) - x (e i)| at he
      have hmono : x (e i) ≤ x (e j) := hm hij.le
      rwa [abs_of_nonneg (sub_nonneg.mpr hmono)] at he
    have hyMono : Monotone (fun i => y (e i)) := by
      simpa only [hy] using monotone_remove_gap (fun i => x (e i)) d hg
    refine ⟨?_, hyMono⟩
    intro j
    let i := e.symm j
    have hi : 0 < n := by have hn := i.isLt; omega
    let a : Fin n := ⟨0, hi⟩
    let b : Fin n := ⟨n - 1, Nat.sub_lt hi Nat.zero_lt_one⟩
    have hai : a ≤ i := Nat.zero_le _
    have hib : i ≤ b := by change i.val ≤ n - 1; omega
    have hb : (b.val : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hi
    have hlo : 0 ≤ y (e a) := by
      have ha0 : a.val = 0 := rfl
      rw [hy, ha0, Nat.cast_zero, zero_add, mul_one]
      linarith only [(hbox (e a)).1]
    have hhi : y (e b) ≤ r - (n : ℝ) * d := by
      rw [hy, hb]
      linarith only [(hbox (e b)).2]
    have h : y (e i) ∈ Icc 0 (r - (n : ℝ) * d) :=
      ⟨hlo.trans (hyMono hai), (hyMono hib).trans hhi⟩
    simpa only [i, Equiv.apply_symm_apply] using h

private theorem volume_coordinateEquality {J : Type*} [Fintype J] {i j : J} (hij : i ≠ j) :
    volume {x : J → ℝ | x i = x j} = 0 := by
  classical
  let P : Submodule ℝ (J → ℝ) :=
    { carrier := {x | x i = x j}
      zero_mem' := rfl
      add_mem' := by
        intro x y hx hy
        change x i = x j at hx
        change y i = y j at hy
        change x i + y i = x j + y j
        rw [hx, hy]
      smul_mem' := by
        intro c x hx
        change x i = x j at hx
        change c * x i = c * x j
        rw [hx] }
  have hP : P ≠ ⊤ := by
    intro ht
    let x : J → ℝ := Pi.single i (1 : ℝ)
    have hmem : x ∈ P := ht.symm ▸ Submodule.mem_top
    change x i = x j at hmem
    have he : (1 : ℝ) = 0 := by
      simpa only [x, Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ => ℝ) hij.symm] using hmem
    exact one_ne_zero he
  letI : Measure.IsAddHaarMeasure (volume : Measure (J → ℝ)) := {}
  exact Measure.addHaar_submodule volume P hP

private theorem volume_not_injective_coordinates {J : Type*} [Fintype J] :
    volume {x : J → ℝ | ¬ Function.Injective x} = 0 := by
  let C (i j : J) : Set (J → ℝ) := {x | x i = x j ∧ i ≠ j}
  have hC (i j : J) : volume (C i j) = 0 := by
    by_cases h : i = j
    · simp [C, h]
    · exact measure_mono_null (fun _ hx => hx.1) (volume_coordinateEquality h)
  refine measure_mono_null ?_ (measure_iUnion_null fun i => measure_iUnion_null (hC i))
  intro x hx
  by_contra h
  apply hx
  intro i j he
  by_contra hn
  exact h (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, he, hn⟩⟩)

private theorem aeDisjoint_coordinateOrders {J : Type*} [Fintype J] {n : ℕ}
    (C : (Fin n ≃ J) → Set (J → ℝ)) (hC : ∀ e x, x ∈ C e → Monotone (fun i => x (e i))) :
    Pairwise (fun e f => AEDisjoint volume (C e) (C f)) := by
  intro e f hef
  change volume (C e ∩ C f) = 0
  refine measure_mono_null ?_ volume_not_injective_coordinates
  intro x hx h
  exact hef (coordinateOrder_unique h (hC e x hx.1) (hC f x hx.2))

/-- Removing a gap of size `d` per coordinate leaves a box of side
`r - n*d`. The total volume is its positive part to the `n`th power. -/
theorem volume_separatedCoordinateBox {J : Type*} [Fintype J] {d r : ℝ} (hd : 0 < d) :
    volume (separatedCoordinateBox J d r) =
      ENNReal.ofReal (r - (Fintype.card J : ℝ) * d) ^ Fintype.card J := by
  classical
  let n := Fintype.card J
  let C (e : Fin n ≃ J) := coordinateOrderChamber e (r - (n : ℝ) * d)
  let B (e : Fin n ≃ J) := (fun x : J → ℝ => x + -gapOffset e d) ⁻¹' C e
  have hC (e : Fin n ≃ J) : IsClosed (C e) := isClosed_coordinateOrderChamber _ _
  have hB (e : Fin n ≃ J) : IsClosed (B e) := (hC e).preimage (continuous_id.add continuous_const)
  have hcover : separatedCoordinateBox J d r = ⋃ e, B e := by
    ext x
    constructor
    · intro hx
      obtain ⟨e, he⟩ := exists_coordinateOrder (separatedCoordinateBox_injective hd hx)
      exact mem_iUnion.mpr ⟨e, (mem_translated_coordinateOrderChamber e hd x).mpr ⟨hx, he.monotone⟩⟩
    · intro hx
      obtain ⟨e, he⟩ := mem_iUnion.mp hx
      exact ((mem_translated_coordinateOrderChamber e hd x).mp he).1
  have hbox : (⋃ e, C e) =ᵐ[volume] (univ : Set J).pi (fun _ => Icc 0 (r - (n : ℝ) * d)) := by
    have hinj : ∀ᵐ x ∂(volume : Measure (J → ℝ)), Function.Injective x :=
      ae_iff.mpr volume_not_injective_coordinates
    filter_upwards [hinj] with x hx
    apply propext
    constructor
    · intro hx'
      obtain ⟨e, he⟩ := mem_iUnion.mp hx'
      exact Set.mem_pi.mpr fun j _ => he.1 j
    · intro hx'
      obtain ⟨e, he⟩ := exists_coordinateOrder hx
      refine mem_iUnion.mpr ⟨e, fun j => ?_, he.monotone⟩
      exact Set.mem_pi.mp hx' _ (mem_univ _)
  letI : Measure.IsAddHaarMeasure (volume : Measure (J → ℝ)) := {}
  calc
    volume (separatedCoordinateBox J d r) = ∑' e, volume (B e) := by
      rw [hcover, measure_iUnion₀ (aeDisjoint_coordinateOrders B (fun e x hx =>
        ((mem_translated_coordinateOrderChamber e hd x).mp hx).2)) (fun e => (hB e).measurableSet.nullMeasurableSet)]
    _ = ∑' e, volume (C e) := tsum_congr fun e => measure_preimage_add_right volume _ _
    _ = volume (⋃ e, C e) := (measure_iUnion₀ (aeDisjoint_coordinateOrders C (fun _ _ hx => hx.2))
      (fun e => (hC e).measurableSet.nullMeasurableSet)).symm
    _ = volume ((univ : Set J).pi (fun _ => Icc 0 (r - (n : ℝ) * d))) := measure_congr hbox
    _ = _ := by rw [volume_pi_pi]; simp only [Real.volume_Icc, sub_zero, Finset.prod_const, Finset.card_univ, n]

#print axioms volume_separatedCoordinateBox

end

end GaloisForLFunctions.HTGeometry
