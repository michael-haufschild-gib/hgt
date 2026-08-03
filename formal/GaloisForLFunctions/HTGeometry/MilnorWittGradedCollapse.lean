import GaloisForLFunctions.HTGeometry.MilnorWittGradedOperations

/-!
# The unit symbol and the Steinberg products in graded Milnor--Witt `K`-theory

Twisted multiplicativity with a unit entry says `[1] + η[1][b] = 0` at any slot; feeding `b = -1`
into the hyperbolic relation then forces `η[1] = 0`, and hence `[1] = 0`.  From `[1] = 0` the
twisted inverse law follows, and from it the two Steinberg-type vanishings `[a][1-a⁻¹] = 0` and
`[a][-a] = 0`.

Everything is stated at an interior slot, which is the form these facts are used in: the derivation
of `⟨a²⟩ = 1` needs them inside longer words.

* `mwUnitSymbol_add`, `mwUnitSymbol_eta`, `mwUnitSymbol_zero` : `[1] + η[1][b] = 0`, `η[1] = 0`,
  `[1] = 0`.
* `mwInverse_law` : `[a] + [a⁻¹] + η[a][a⁻¹] = 0`.
* `mwSteinberg_inv` : `[a][1 - a⁻¹] = 0`.
* `mwSymbol_mul_neg_self` : `[a][-a] = 0`.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWittGradedCollapse

variable {F : Type*} [Field F]

/-- **Twisted multiplicativity with a unit entry**, at an interior slot. -/
theorem mwUnitSymbol_add {n : ℤ} (k : ℕ) (l₁ l₂ : List Fˣ) (b : Fˣ)
    (p1 : (((l₁ ++ (1 : Fˣ) :: l₂).length : ℤ)) - k = n)
    (p1b : (((l₁ ++ (1 : Fˣ) :: b :: l₂).length : ℤ)) - (k + 1) = n) :
    mwClassDeg F n ⟨(k, l₁ ++ (1 : Fˣ) :: l₂), p1⟩ +
      mwClassDeg F n ⟨(k + 1, l₁ ++ (1 : Fˣ) :: b :: l₂), p1b⟩ = 0 := by
  have pb : (((l₁ ++ b :: l₂).length : ℤ)) - k = n := by
    simp only [length_middle] at p1 ⊢
    exact p1
  have h := mwClassDeg_twisted (F := F) k 1 b l₁ l₂ (by rw [one_mul]) rfl rfl rfl pb p1 pb p1b
  calc mwClassDeg F n ⟨(k, l₁ ++ (1 : Fˣ) :: l₂), p1⟩ +
        mwClassDeg F n ⟨(k + 1, l₁ ++ (1 : Fˣ) :: b :: l₂), p1b⟩
      = (mwClassDeg F n ⟨(k, l₁ ++ (1 : Fˣ) :: l₂), p1⟩ +
          mwClassDeg F n ⟨(k, l₁ ++ b :: l₂), pb⟩ +
          mwClassDeg F n ⟨(k + 1, l₁ ++ (1 : Fˣ) :: b :: l₂), p1b⟩) -
            mwClassDeg F n ⟨(k, l₁ ++ b :: l₂), pb⟩ := by abel
    _ = mwClassDeg F n ⟨(k, l₁ ++ b :: l₂), pb⟩ -
          mwClassDeg F n ⟨(k, l₁ ++ b :: l₂), pb⟩ := by rw [← h]
    _ = 0 := sub_self _

/-- **`η[1] = 0`**, at an interior slot. -/
theorem mwUnitSymbol_eta {n : ℤ} (k : ℕ) (l₁ l₂ : List Fˣ)
    (p : (((l₁ ++ (1 : Fˣ) :: l₂).length : ℤ)) - (k + 1) = n) :
    mwClassDeg F n ⟨(k + 1, l₁ ++ (1 : Fˣ) :: l₂), p⟩ = 0 := by
  have p1 : (((l₁ ++ (1 : Fˣ) :: l₂).length : ℤ)) - k = n + 1 := by omega
  have p1b : (((l₁ ++ (1 : Fˣ) :: (-1 : Fˣ) :: l₂).length : ℤ)) - (k + 1) = n + 1 := by
    simp only [length_middle] at p1 ⊢
    push_cast at p1 ⊢
    omega
  have hL1 := mwUnitSymbol_add (F := F) k l₁ l₂ (-1) p1 p1b
  have pm : (((l₁ ++ (1 : Fˣ) :: (-1 : Fˣ) :: l₂).length : ℤ)) - (k + 2) = n := by
    omega
  have heta := congrArg (mwEtaMul (F := F) (n := n + 1) (m := n) rfl) hL1
  rw [map_add, map_zero, mwEtaMul_class' rfl p1 p rfl, mwEtaMul_class' rfl p1b pm rfl] at heta
  have hhyp := mwClassDeg_hyperbolic (F := F) k (l₁ ++ [1]) l₂
    (show l₁ ++ (1 : Fˣ) :: (-1 : Fˣ) :: l₂ = (l₁ ++ [1]) ++ (-1 : Fˣ) :: l₂ from
      (List.append_assoc l₁ [1] ((-1 : Fˣ) :: l₂)).symm)
    (show l₁ ++ (1 : Fˣ) :: l₂ = (l₁ ++ [1]) ++ l₂ from (List.append_assoc l₁ [1] l₂).symm) pm p
  calc mwClassDeg F n ⟨(k + 1, l₁ ++ (1 : Fˣ) :: l₂), p⟩
      = (mwClassDeg F n ⟨(k + 2, l₁ ++ (1 : Fˣ) :: (-1 : Fˣ) :: l₂), pm⟩ +
          (mwClassDeg F n ⟨(k + 1, l₁ ++ (1 : Fˣ) :: l₂), p⟩ +
            mwClassDeg F n ⟨(k + 1, l₁ ++ (1 : Fˣ) :: l₂), p⟩)) -
            (mwClassDeg F n ⟨(k + 1, l₁ ++ (1 : Fˣ) :: l₂), p⟩ +
              mwClassDeg F n ⟨(k + 2, l₁ ++ (1 : Fˣ) :: (-1 : Fˣ) :: l₂), pm⟩) := by abel
    _ = 0 - 0 := by rw [hhyp, heta]
    _ = 0 := sub_self _

/-- **`[1] = 0`**, at an interior slot. -/
theorem mwUnitSymbol_zero {n : ℤ} (k : ℕ) (l₁ l₂ : List Fˣ)
    (p : (((l₁ ++ (1 : Fˣ) :: l₂).length : ℤ)) - k = n) :
    mwClassDeg F n ⟨(k, l₁ ++ (1 : Fˣ) :: l₂), p⟩ = 0 := by
  have p11 : (((l₁ ++ (1 : Fˣ) :: (1 : Fˣ) :: l₂).length : ℤ)) - (k + 1) = n := by
    simp only [length_middle] at p ⊢
    push_cast at p ⊢
    omega
  have hadd := mwUnitSymbol_add (F := F) k l₁ l₂ 1 p p11
  have p11' : ((((l₁ ++ [1]) ++ (1 : Fˣ) :: l₂).length : ℤ)) - (k + 1) = n := by
    rw [List.append_assoc]
    exact p11
  have hz := mwUnitSymbol_eta (F := F) k (l₁ ++ [1]) l₂ p11'
  rw [mwClassDeg_congr p11' p11 (List.append_assoc l₁ [1] ((1 : Fˣ) :: l₂))] at hz
  rw [hz, add_zero] at hadd
  exact hadd

/-- **The inverse law** `[a] + [a⁻¹] + η[a][a⁻¹] = 0`, at an interior slot. -/
theorem mwInverse_law {n : ℤ} (k : ℕ) (l₁ l₂ : List Fˣ) (a : Fˣ)
    (pa : (((l₁ ++ a :: l₂).length : ℤ)) - k = n)
    (pi : (((l₁ ++ a⁻¹ :: l₂).length : ℤ)) - k = n)
    (pe : (((l₁ ++ a :: a⁻¹ :: l₂).length : ℤ)) - (k + 1) = n) :
    mwClassDeg F n ⟨(k, l₁ ++ a :: l₂), pa⟩ + mwClassDeg F n ⟨(k, l₁ ++ a⁻¹ :: l₂), pi⟩ +
      mwClassDeg F n ⟨(k + 1, l₁ ++ a :: a⁻¹ :: l₂), pe⟩ = 0 := by
  have p1 : (((l₁ ++ (1 : Fˣ) :: l₂).length : ℤ)) - k = n := by
    simp only [length_middle] at pa ⊢
    exact pa
  have h := mwClassDeg_twisted (F := F) k a a⁻¹ l₁ l₂ (by rw [mul_inv_cancel]) rfl rfl rfl
    p1 pa pi pe
  rw [mwUnitSymbol_zero k l₁ l₂ p1] at h
  exact h.symm

/-- **`[a][1 - a⁻¹] = 0`**, at an interior slot.  Rewriting `[a]` through the inverse law turns the
product into two Steinberg products. -/
theorem mwSteinberg_inv {n : ℤ} (k : ℕ) (l₁ l₂ : List Fˣ) {a : Fˣ}
    (hainv : ((a⁻¹ : Fˣ) : F) ≠ 1)
    (p : (((l₁ ++ a :: oneSubUnit hainv :: l₂).length : ℤ)) - k = n) :
    mwClassDeg F n ⟨(k, l₁ ++ a :: oneSubUnit hainv :: l₂), p⟩ = 0 := by
  have pi : (((l₁ ++ a⁻¹ :: oneSubUnit hainv :: l₂).length : ℤ)) - k = n := by
    simp only [length_middle] at p ⊢
    exact p
  have pe : (((l₁ ++ a :: a⁻¹ :: oneSubUnit hainv :: l₂).length : ℤ)) - (k + 1) = n := by
    simp only [length_middle] at p ⊢
    push_cast at p ⊢
    omega
  have h := mwInverse_law (F := F) k l₁ (oneSubUnit hainv :: l₂) a p pi pe
  rw [mwClassDeg_steinberg k hainv l₁ l₂ rfl pi] at h
  have pe' : ((((l₁ ++ [a]) ++ a⁻¹ :: oneSubUnit hainv :: l₂).length : ℤ)) - (k + 1) = n := by
    rw [List.append_assoc]
    exact pe
  have hst2 := mwClassDeg_steinberg (F := F) (k + 1) hainv (l₁ ++ [a]) l₂ rfl pe'
  rw [mwClassDeg_congr pe' pe (List.append_assoc l₁ [a] (a⁻¹ :: oneSubUnit hainv :: l₂))] at hst2
  rw [hst2, add_zero, add_zero] at h
  exact h

/-- **`[a][-a] = 0`**, after an arbitrary prefix.  The unit identity `(-a)(1 - a⁻¹) = 1 - a` makes
`[a][-a]` annihilated by `1 + η[1 - a⁻¹]`, and the inverse law says that factor is a unit. -/
theorem mwSymbol_mul_neg_self {n : ℤ} (k : ℕ) (l₁ : List Fˣ) (a : Fˣ)
    (p : (((l₁ ++ [a, -a]).length : ℤ)) - k = n) :
    mwClassDeg F n ⟨(k, l₁ ++ [a, -a]), p⟩ = 0 := by
  by_cases ha : (a : F) = 1
  · have h1 : a = 1 := Units.ext ha
    subst h1
    exact mwUnitSymbol_zero k l₁ [(-1 : Fˣ)] p
  · have hlen : ((l₁.length : ℤ)) + 2 - k = n := by
      simp only [List.length_append, List.length_cons, List.length_nil] at p
      push_cast at p
      omega
    have hainv : ((a⁻¹ : Fˣ) : F) ≠ 1 := fun h =>
      ha (congrArg Units.val (inv_eq_one.mp (Units.ext h)))
    have hane : (a : F) ≠ 0 := a.ne_zero
    have hunit : (-a : Fˣ) * oneSubUnit hainv = oneSubUnit ha := by
      refine Units.ext ?_
      rw [Units.val_mul, oneSubUnit_val, oneSubUnit_val, Units.val_neg,
        Units.val_inv_eq_inv_val, mul_sub, mul_one, neg_mul, mul_inv_cancel₀ hane]
      ring
    have pst : (((l₁ ++ [a, oneSubUnit ha]).length : ℤ)) - k = n := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      push_cast
      omega
    have pc : (((l₁ ++ [a, oneSubUnit hainv]).length : ℤ)) - k = n := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      push_cast
      omega
    have pY : (((l₁ ++ [a, -a, oneSubUnit hainv]).length : ℤ)) - (k + 1) = n := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      push_cast
      omega
    have htw := mwClassDeg_twisted (F := F) k (-a) (oneSubUnit hainv) (l₁ ++ [a]) []
      (show l₁ ++ [a, oneSubUnit ha] = (l₁ ++ [a]) ++ ((-a) * oneSubUnit hainv) :: [] by
        rw [List.append_assoc, hunit]
        rfl)
      (show l₁ ++ [a, -a] = (l₁ ++ [a]) ++ (-a) :: [] from
        (List.append_assoc l₁ [a] [(-a)]).symm)
      (show l₁ ++ [a, oneSubUnit hainv] = (l₁ ++ [a]) ++ (oneSubUnit hainv) :: [] from
        (List.append_assoc l₁ [a] [oneSubUnit hainv]).symm)
      (show l₁ ++ [a, -a, oneSubUnit hainv] =
          (l₁ ++ [a]) ++ (-a) :: (oneSubUnit hainv) :: [] from
        (List.append_assoc l₁ [a] [(-a), oneSubUnit hainv]).symm)
      pst p pc pY
    rw [mwClassDeg_steinberg k ha l₁ [] rfl pst,
      mwSteinberg_inv k l₁ [] hainv pc, add_zero] at htw
    -- `htw : 0 = X + Y`
    have pXc : (((l₁ ++ [a, -a, oneSubUnit hainv]).length : ℤ)) - k = n + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      push_cast
      omega
    have pXi : (((l₁ ++ [a, -a, (oneSubUnit hainv)⁻¹]).length : ℤ)) - k = n + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      push_cast
      omega
    have pXe : (((l₁ ++ [a, -a, oneSubUnit hainv, (oneSubUnit hainv)⁻¹]).length : ℤ)) -
        (k + 1) = n + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      push_cast
      omega
    have pXc' : ((((l₁ ++ [a, -a]) ++ [oneSubUnit hainv]).length : ℤ)) - k = n + 1 := by
      rw [List.append_assoc]
      exact pXc
    have pXi' : ((((l₁ ++ [a, -a]) ++ [(oneSubUnit hainv)⁻¹]).length : ℤ)) - k = n + 1 := by
      rw [List.append_assoc]
      exact pXi
    have pXe' : ((((l₁ ++ [a, -a]) ++ [oneSubUnit hainv, (oneSubUnit hainv)⁻¹]).length : ℤ)) -
        (k + 1) = n + 1 := by
      rw [List.append_assoc]
      exact pXe
    have hinv := mwInverse_law (F := F) k (l₁ ++ [a, -a]) [] (oneSubUnit hainv) pXc' pXi' pXe'
    rw [mwClassDeg_congr pXc' pXc (List.append_assoc l₁ [a, -a] [oneSubUnit hainv]),
      mwClassDeg_congr pXi' pXi (List.append_assoc l₁ [a, -a] [(oneSubUnit hainv)⁻¹]),
      mwClassDeg_congr pXe' pXe
        (List.append_assoc l₁ [a, -a] [oneSubUnit hainv, (oneSubUnit hainv)⁻¹])] at hinv
    have pYi : (((l₁ ++ [a, -a, (oneSubUnit hainv)⁻¹]).length : ℤ)) - (k + 1) = n := by
      omega
    have pYe : (((l₁ ++ [a, -a, oneSubUnit hainv, (oneSubUnit hainv)⁻¹]).length : ℤ)) -
        (k + 2) = n := by
      omega
    have hstar := congrArg (mwEtaMul (F := F) (n := n + 1) (m := n) rfl) hinv
    rw [map_add, map_add, map_zero, mwEtaMul_class' rfl pXc pY rfl,
      mwEtaMul_class' rfl pXi pYi rfl, mwEtaMul_class' rfl pXe pYe rfl] at hstar
    -- `hstar : Y + C (k+1) [..c⁻¹] + C (k+2) [..c,c⁻¹] = 0`
    have hshift := congrArg
      (mwSymMulRight (F := F) (n := n) (m := n + 1) rfl (oneSubUnit hainv)⁻¹) htw.symm
    rw [map_add, map_zero,
      mwSymMulRight_class' rfl (oneSubUnit hainv)⁻¹ p pXi
        (show l₁ ++ [a, -a, (oneSubUnit hainv)⁻¹] = (l₁ ++ [a, -a]) ++ [(oneSubUnit hainv)⁻¹] from
          (List.append_assoc l₁ [a, -a] [(oneSubUnit hainv)⁻¹]).symm),
      mwSymMulRight_class' rfl (oneSubUnit hainv)⁻¹ pY pXe
        (show l₁ ++ [a, -a, oneSubUnit hainv, (oneSubUnit hainv)⁻¹] =
            (l₁ ++ [a, -a, oneSubUnit hainv]) ++ [(oneSubUnit hainv)⁻¹] from
          (List.append_assoc l₁ [a, -a, oneSubUnit hainv] [(oneSubUnit hainv)⁻¹]).symm)] at hshift
    have hshift2 := congrArg (mwEtaMul (F := F) (n := n + 1) (m := n) rfl) hshift
    rw [map_add, map_zero, mwEtaMul_class' rfl pXi pYi rfl,
      mwEtaMul_class' rfl pXe pYe rfl] at hshift2
    -- `hshift2 : C (k+1) [..c⁻¹] + C (k+2) [..c,c⁻¹] = 0`
    have hY : mwClassDeg F n ⟨(k + 1, l₁ ++ [a, -a, oneSubUnit hainv]), pY⟩ = 0 := by
      calc mwClassDeg F n ⟨(k + 1, l₁ ++ [a, -a, oneSubUnit hainv]), pY⟩
          = (mwClassDeg F n ⟨(k + 1, l₁ ++ [a, -a, oneSubUnit hainv]), pY⟩ +
              mwClassDeg F n ⟨(k + 1, l₁ ++ [a, -a, (oneSubUnit hainv)⁻¹]), pYi⟩ +
              mwClassDeg F n
                ⟨(k + 2, l₁ ++ [a, -a, oneSubUnit hainv, (oneSubUnit hainv)⁻¹]), pYe⟩) -
              (mwClassDeg F n ⟨(k + 1, l₁ ++ [a, -a, (oneSubUnit hainv)⁻¹]), pYi⟩ +
                mwClassDeg F n
                  ⟨(k + 2, l₁ ++ [a, -a, oneSubUnit hainv, (oneSubUnit hainv)⁻¹]), pYe⟩) := by
            abel
        _ = 0 - 0 := by rw [hstar, hshift2]
        _ = 0 := sub_self _
    rw [hY, add_zero] at htw
    exact htw.symm

end MilnorWittGradedCollapse

end GaloisForLFunctions.HTGeometry
