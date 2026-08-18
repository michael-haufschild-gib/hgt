import GaloisForLFunctions.HTGeometry.MilnorKSlotGeneration

/-!
# Two-slot calculus for Milnor symbols

Milnor's degree induction for a rational function field manipulates a symbol at two adjacent slots
while the rest of the symbol is carried along.  This file packages that calculus.

The two identities it produces are the classical ones:

* `twoSlot_neg_self` : `{…, a, −a, …} = 0`, from the Steinberg relation at `a` and at `a⁻¹`
  together with `−a = (1 − a)/(1 − a⁻¹)`;
* `twoSlot_add_split` : `{…, u, v, …} = {…, u, u+v, …} + {…, u+v, v, …} − {…, u+v, u+v, …}`,
  the Steinberg relation at `u/(u+v)`, whose complement is `v/(u+v)`.

The second is the engine of the degree induction: two entries of equal degree `d` are replaced by
symbols in which one entry has been lowered to the remainder of the division, and by the first
identity the leftover `{…, w, w, …}` is `{…, w, −1, …}`, which again has only one entry of
degree `d`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

theorem length_two_slot (l₁ l₂ : List Kˣ) (a b : Kˣ) {n : ℕ}
    (hn : (l₁ ++ l₂).length + 2 = n) : (l₁ ++ a :: b :: l₂).length = n := by
  simp only [List.length_append, List.length_cons] at hn ⊢
  omega

variable {n : ℕ} (l₁ l₂ : List Kˣ) (hn : (l₁ ++ l₂).length + 2 = n)

/-- The class of a symbol with two designated adjacent slots. -/
def twoSlot (a b : Kˣ) : MilnorKDeg K n :=
  milnorClassDeg K n ⟨l₁ ++ a :: b :: l₂, length_two_slot l₁ l₂ a b hn⟩

theorem twoSlot_mul_left (a b c : Kˣ) :
    twoSlot l₁ l₂ hn (a * b) c = twoSlot l₁ l₂ hn a c + twoSlot l₁ l₂ hn b c :=
  milnorClassDeg_mul_of_eq (F := K) a b l₁ (c :: l₂) rfl rfl rfl _ _ _

theorem twoSlot_mul_right (a b c : Kˣ) :
    twoSlot l₁ l₂ hn a (b * c) = twoSlot l₁ l₂ hn a b + twoSlot l₁ l₂ hn a c :=
  milnorClassDeg_mul_of_eq (F := K) b c (l₁ ++ [a]) l₂
    (Lab := l₁ ++ a :: (b * c) :: l₂) (La := l₁ ++ a :: b :: l₂) (Lb := l₁ ++ a :: c :: l₂)
    (by simp) (by simp) (by simp) _ _ _

theorem twoSlot_inv_left (a b : Kˣ) : twoSlot l₁ l₂ hn a⁻¹ b = -twoSlot l₁ l₂ hn a b :=
  milnorClassDeg_inv_of_eq (K := K) a l₁ (b :: l₂) rfl rfl _ _

theorem twoSlot_inv_right (a b : Kˣ) : twoSlot l₁ l₂ hn a b⁻¹ = -twoSlot l₁ l₂ hn a b :=
  milnorClassDeg_inv_of_eq (K := K) b (l₁ ++ [a]) l₂
    (Lb := l₁ ++ a :: b :: l₂) (Li := l₁ ++ a :: b⁻¹ :: l₂) (by simp) (by simp) _ _

theorem twoSlot_one_left (b : Kˣ) : twoSlot l₁ l₂ hn 1 b = 0 :=
  milnorClassDeg_one_of_eq (K := K) l₁ (b :: l₂) rfl _

theorem twoSlot_steinberg {a : Kˣ} (ha : (a : K) ≠ 1) :
    twoSlot l₁ l₂ hn a (oneSubUnit ha) = 0 :=
  milnorClassDeg_steinberg_of_eq (F := K) ha l₁ l₂ rfl _

/-- **`{…, a, −a, …} = 0`.**  For `a ≠ 1` this is the Steinberg relation at `a` and at `a⁻¹`,
combined through `−a = (1 − a)·(1 − a⁻¹)⁻¹`. -/
theorem twoSlot_neg_self (a : Kˣ) : twoSlot l₁ l₂ hn a (-a) = 0 := by
  classical
  by_cases ha : (a : K) = 1
  · have hone : a = 1 := Units.ext ha
    rw [hone, twoSlot_one_left]
  · have hane : (a : K) ≠ 0 := a.ne_zero
    have hainv : ((a⁻¹ : Kˣ) : K) ≠ 1 := by
      intro hcon
      rw [Units.val_inv_eq_inv_val] at hcon
      exact ha (by rw [← inv_inv (a : K), hcon, inv_one])
    have hb : ((oneSubUnit hainv : Kˣ) : K) = 1 - (a : K)⁻¹ := by
      rw [oneSubUnit_val, Units.val_inv_eq_inv_val]
    have hbne : (1 : K) - (a : K)⁻¹ ≠ 0 := by
      rw [← hb]
      exact (oneSubUnit hainv).ne_zero
    have hkey : (-(a : K)) * (1 - (a : K)⁻¹) = 1 - (a : K) := by
      rw [mul_sub, mul_one, neg_mul, mul_inv_cancel₀ hane]
      ring
    have hprod : (-a : Kˣ) = oneSubUnit ha * (oneSubUnit hainv)⁻¹ := by
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_inv_eq_inv_val, oneSubUnit_val, hb, Units.val_neg,
        ← hkey, mul_assoc, mul_inv_cancel₀ hbne, mul_one]
    have hs1 : twoSlot l₁ l₂ hn a (oneSubUnit ha) = 0 := twoSlot_steinberg l₁ l₂ hn ha
    have hs2 : twoSlot l₁ l₂ hn a (oneSubUnit hainv) = 0 := by
      have h := twoSlot_steinberg l₁ l₂ hn hainv
      rw [twoSlot_inv_left, neg_eq_zero] at h
      exact h
    rw [hprod, twoSlot_mul_right, twoSlot_inv_right, hs1, hs2, neg_zero, add_zero]

/-- **`{…, a, a, …} = {…, a, −1, …}`.** -/
theorem twoSlot_self (a : Kˣ) : twoSlot l₁ l₂ hn a a = twoSlot l₁ l₂ hn a (-1) := by
  have hfac : a = (-1 : Kˣ) * (-a) := by
    refine Units.ext ?_
    simp
  have h := twoSlot_mul_right l₁ l₂ hn a (-1) (-a)
  rw [twoSlot_neg_self, add_zero, ← hfac] at h
  exact h

theorem twoSlot_one_right (a : Kˣ) : twoSlot l₁ l₂ hn a 1 = 0 :=
  milnorClassDeg_one_of_eq (K := K) (l₁ ++ [a]) l₂ (by simp) _

/-- `{…, a, −1, …}` is `2`-torsion, because `(−1)·(−1) = 1`. -/
theorem twoSlot_neg_one_add_self (a : Kˣ) :
    twoSlot l₁ l₂ hn a (-1) + twoSlot l₁ l₂ hn a (-1) = 0 := by
  have h := twoSlot_mul_right l₁ l₂ hn a (-1) (-1)
  rw [show ((-1 : Kˣ) * (-1 : Kˣ)) = 1 by simp, twoSlot_one_right] at h
  exact h.symm

/-- **Anticommutativity at two adjacent slots**: `{…, a, b, …} = −{…, b, a, …}`. -/
theorem twoSlot_swap (a b : Kˣ) : twoSlot l₁ l₂ hn a b = -twoSlot l₁ l₂ hn b a := by
  have hnegab : (-(a * b) : Kˣ) = (-a) * b := by
    refine Units.ext ?_
    simp [neg_mul]
  have hnega : (-a : Kˣ) = (-1 : Kˣ) * a := by
    refine Units.ext ?_
    simp
  have h0 : twoSlot l₁ l₂ hn (a * b) (-(a * b)) = 0 := twoSlot_neg_self l₁ l₂ hn (a * b)
  rw [hnegab, twoSlot_mul_left, twoSlot_mul_right, twoSlot_mul_right,
    twoSlot_neg_self, hnega, twoSlot_mul_right, twoSlot_self] at h0
  have h2 := twoSlot_neg_one_add_self l₁ l₂ hn b
  refine eq_neg_of_add_eq_zero_right ?_
  calc twoSlot l₁ l₂ hn b a + twoSlot l₁ l₂ hn a b
      = ((0 : MilnorKDeg K n) + twoSlot l₁ l₂ hn a b)
        + ((twoSlot l₁ l₂ hn b (-1) + twoSlot l₁ l₂ hn b a) + twoSlot l₁ l₂ hn b (-1))
        - (twoSlot l₁ l₂ hn b (-1) + twoSlot l₁ l₂ hn b (-1)) := by abel
    _ = 0 - 0 := by rw [h0, h2]
    _ = 0 := by abel

/-- **The sum-splitting identity.**  For units `u`, `v` whose sum is the unit `w`,
`{u, v} = {u, w} + {w, v} − {w, w}` at any two adjacent slots. -/
theorem twoSlot_add_split (u v w : Kˣ) (hw : (u : K) + (v : K) = (w : K)) :
    twoSlot l₁ l₂ hn u v
      = twoSlot l₁ l₂ hn u w + twoSlot l₁ l₂ hn w v - twoSlot l₁ l₂ hn w w := by
  classical
  have hwne : (w : K) ≠ 0 := w.ne_zero
  have hune : ((u * w⁻¹ : Kˣ) : K) ≠ 1 := by
    intro hcon
    rw [Units.val_mul, Units.val_inv_eq_inv_val] at hcon
    have huw : (u : K) = (w : K) := by
      have hmul := congrArg (fun t : K => t * (w : K)) hcon
      simpa [mul_assoc, inv_mul_cancel₀ hwne] using hmul
    have hzero : (u : K) + (v : K) = (u : K) + 0 := by rw [add_zero, hw, ← huw]
    exact v.ne_zero (add_left_cancel hzero)
  have hone : oneSubUnit hune = v * w⁻¹ := by
    refine Units.ext ?_
    rw [oneSubUnit_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mul,
      Units.val_inv_eq_inv_val]
    have h1 : (1 : K) - (u : K) * (w : K)⁻¹ = ((w : K) - (u : K)) * (w : K)⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hwne]
    rw [h1]
    congr 1
    rw [← hw]
    ring
  have key : twoSlot l₁ l₂ hn (u * w⁻¹) (v * w⁻¹) = 0 := by
    have h := twoSlot_steinberg l₁ l₂ hn hune
    rwa [hone] at h
  have e1 : twoSlot l₁ l₂ hn (u * w⁻¹) (v * w⁻¹)
      = twoSlot l₁ l₂ hn u (v * w⁻¹) + twoSlot l₁ l₂ hn w⁻¹ (v * w⁻¹) :=
    twoSlot_mul_left l₁ l₂ hn u w⁻¹ (v * w⁻¹)
  have e2 : twoSlot l₁ l₂ hn u (v * w⁻¹)
      = twoSlot l₁ l₂ hn u v - twoSlot l₁ l₂ hn u w := by
    rw [twoSlot_mul_right, twoSlot_inv_right]; abel
  have e3 : twoSlot l₁ l₂ hn w⁻¹ (v * w⁻¹)
      = -twoSlot l₁ l₂ hn w v + twoSlot l₁ l₂ hn w w := by
    rw [twoSlot_mul_right, twoSlot_inv_left, twoSlot_inv_left, twoSlot_inv_right]; abel
  have hz : twoSlot l₁ l₂ hn u v - twoSlot l₁ l₂ hn u w - twoSlot l₁ l₂ hn w v
      + twoSlot l₁ l₂ hn w w = 0 := by
    calc twoSlot l₁ l₂ hn u v - twoSlot l₁ l₂ hn u w - twoSlot l₁ l₂ hn w v
          + twoSlot l₁ l₂ hn w w
        = (twoSlot l₁ l₂ hn u v - twoSlot l₁ l₂ hn u w)
          + (-twoSlot l₁ l₂ hn w v + twoSlot l₁ l₂ hn w w) := by abel
      _ = twoSlot l₁ l₂ hn u (v * w⁻¹) + twoSlot l₁ l₂ hn w⁻¹ (v * w⁻¹) := by rw [e2, e3]
      _ = twoSlot l₁ l₂ hn (u * w⁻¹) (v * w⁻¹) := e1.symm
      _ = 0 := key
  refine sub_eq_zero.mp ?_
  calc twoSlot l₁ l₂ hn u v
        - (twoSlot l₁ l₂ hn u w + twoSlot l₁ l₂ hn w v - twoSlot l₁ l₂ hn w w)
      = twoSlot l₁ l₂ hn u v - twoSlot l₁ l₂ hn u w - twoSlot l₁ l₂ hn w v
        + twoSlot l₁ l₂ hn w w := by abel
    _ = 0 := hz

end GaloisForLFunctions.HTGeometry
