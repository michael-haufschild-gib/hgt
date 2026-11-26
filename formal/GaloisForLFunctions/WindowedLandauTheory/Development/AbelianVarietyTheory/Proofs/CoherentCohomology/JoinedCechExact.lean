import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechDatum

/-! Acyclic augmented slices give exactness of the joined total differential.
The proof cancels its lowest surviving degree in the other cover. -/

noncomputable section

open GlobalTheory.WH

namespace HTGeometry.FinsetCechDatum

/-- A coefficientwise isomorphism carries primitives to primitives. -/
theorem exists_primitive_of_bijective_coefficients {T : Type} [LinearOrder T]
    {A B : FinsetCechDatum.{0} T} (φ : A.Hom B) (hφ : ∀ s, Function.Bijective (φ.app s))
    (hA : ∀ a : A.Cochain, A.d a = 0 → ∃ y, A.d y = a)
    (b : B.Cochain) (hb : B.d b = 0) : ∃ y, B.d y = b := by
  have hi : Function.Injective φ.onCochain := fun x y h =>
    funext fun s => (hφ s).injective (congrFun h s)
  choose a ha using fun s => (hφ s).surjective (b s)
  have he : φ.onCochain a = b := funext ha
  have hz : A.d a = 0 := hi (by
    rw [← φ.d_onCochain, he, hb]
    exact (funext fun s => map_zero (φ.app s)).symm)
  obtain ⟨y, hy⟩ := hA a hz
  exact ⟨φ.onCochain y, (φ.d_onCochain y).trans ((congrArg φ.onCochain hy).trans he)⟩

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  (D : FinsetCechDatum.{0} (ι ⊕ₗ κ))

private theorem differential_zero_of_erases {T : Type} [LinearOrder T] (C : FinsetCechDatum T)
    (x : C.Cochain) (s : Finset T) (h : ∀ i ∈ s, x (s.erase i) = 0) : C.d x s = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [h i hi, map_zero, smul_zero]

private theorem negOnePow_smul_involution {M : Type} [AddCommGroup M] (n : ℕ) (a : M) :
    (-1 : ℤ) ^ n • ((-1 : ℤ) ^ n • a) = a := by
  rw [smul_smul, ← mul_pow]
  simp

private theorem primitive_of_finite_filtration (N : ℕ) (P : ℕ → D.Cochain → Prop)
    (h₀ : ∀ x, P 0 x) (hTop : ∀ x, P N x → x = 0)
    (hStep : ∀ n x, P n x → D.d x = 0 → ∃ y, P (n + 1) (x - D.d y))
    (x : D.Cochain) (hx : D.d x = 0) : ∃ y, D.d y = x := by
  have solve : ∀ k n, n + k = N → ∀ z, P n z → D.d z = 0 → ∃ y, D.d y = z := by
    intro k
    induction k with
    | zero =>
      intro n hn z hz _
      have hn' : n = N := Nat.add_zero n ▸ hn
      exact ⟨0, D.d_zero.trans (hTop z (hn' ▸ hz)).symm⟩
    | succ k ih =>
      intro n hn z hz hD
      obtain ⟨y, hy⟩ := hStep n z hz hD
      have hD' : D.d (z - D.d y) = 0 := by rw [D.d_sub, hD, D.d_d, sub_self]
      obtain ⟨w, hw⟩ := ih (n + 1) (by omega) _ hy hD'
      refine ⟨w + y, ?_⟩
      rw [D.d_add, hw, sub_add_cancel]
  exact solve N 0 (Nat.zero_add N) x (h₀ x) hx

/-- Exact augmented right slices imply that every total cocycle is a boundary. -/
theorem exists_primitive_of_rightSlices [Fintype ι]
    (h : ∀ I (x : (D.rightSlice I).Cochain), (D.rightSlice I).d x = 0 →
      ∃ y, (D.rightSlice I).d y = x)
    (x : D.Cochain) (hx : D.d x = 0) : ∃ y, D.d y = x := by
  let P (n : ℕ) (z : D.Cochain) := ∀ I J, I.card < n → z (uni I J) = 0
  refine D.primitive_of_finite_filtration (Fintype.card ι + 1) P ?_ ?_ ?_ x hx
  · intro z I J hi
    exact (Nat.not_lt_zero _ hi).elim
  · intro z hz
    funext s
    rw [← uni_lft_rgt s]
    exact hz (lft s) (rgt s) (Nat.lt_succ_of_le (Finset.card_le_univ _))
  · intro n z hz hdz
    have hzL (I : Finset ι) (J : Finset κ) (hI : I.card ≤ n) :
        (D.leftSlice J).d (fun A => z (uni A J)) I = 0 := by
      apply differential_zero_of_erases
      intro i hi
      apply hz
      rw [Finset.card_erase_of_mem hi]
      have hp := Finset.card_pos.2 ⟨i, hi⟩
      omega
    have sliceLift (I : Finset ι) : ∃ w : (D.rightSlice I).Cochain,
        (∀ J, I.card ≠ n → w J = 0) ∧
          (∀ J, I.card = n → (-1 : ℤ) ^ I.card • (D.rightSlice I).d w J = z (uni I J)) := by
      by_cases hI : I.card = n
      · have hclosed : (D.rightSlice I).d (fun B => z (uni I B)) = 0 := by
          funext J
          have e := congrFun hdz (uni I J)
          rw [D.d_uni, hzL I J hI.le, zero_add, Pi.zero_apply] at e
          exact (negOnePow_smul_involution I.card _).symm.trans
            ((congrArg (((-1 : ℤ) ^ I.card) • ·) e).trans (smul_zero _))
        obtain ⟨w, hw⟩ := h I _ hclosed
        let c := (-1 : ℤ) ^ I.card
        refine ⟨c • w, fun _ hne => (hne hI).elim, fun J _ => ?_⟩
        have e : (D.rightSlice I).d (c • w) = c • (D.rightSlice I).d w :=
          map_zsmul (D.rightSlice I).dHom c w
        rw [e, hw]
        exact negOnePow_smul_involution I.card _
      · exact ⟨0, fun _ _ => rfl, fun _ he => (hI he).elim⟩
    choose w hw₀ hw₁ using sliceLift
    let y := (D.cochainSlices ℤ).symm w
    have hy (I : Finset ι) (J : Finset κ) : y (uni I J) = w I J :=
      congrFun (congrFun ((D.cochainSlices ℤ).apply_symm_apply w) I) J
    refine ⟨y, fun I J hI => ?_⟩
    have hyL : (D.leftSlice J).d (fun A => y (uni A J)) I = 0 := by
      apply differential_zero_of_erases
      intro i hi
      rw [hy]
      apply hw₀
      rw [Finset.card_erase_of_mem hi]
      have hp := Finset.card_pos.2 ⟨i, hi⟩
      omega
    have hyR : (fun B => y (uni I B)) = w I := funext (hy I)
    change z (uni I J) - D.d y (uni I J) = 0
    rw [D.d_uni, hyL, zero_add, hyR]
    by_cases hEq : I.card = n
    · rw [hw₁ I J hEq, sub_self]
    · have hlt : I.card < n := by omega
      have hwz : w I = 0 := funext fun B => hw₀ I B hEq
      rw [hz I J hlt, hwz, FinsetCechDatum.d_zero, Pi.zero_apply, smul_zero, sub_zero]

/-- Exact augmented left slices imply that every total cocycle is a boundary. -/
theorem exists_primitive_of_leftSlices [Fintype κ]
    (h : ∀ J (x : (D.leftSlice J).Cochain), (D.leftSlice J).d x = 0 →
      ∃ y, (D.leftSlice J).d y = x)
    (x : D.Cochain) (hx : D.d x = 0) : ∃ y, D.d y = x := by
  let P (n : ℕ) (z : D.Cochain) := ∀ I J, J.card < n → z (uni I J) = 0
  refine D.primitive_of_finite_filtration (Fintype.card κ + 1) P ?_ ?_ ?_ x hx
  · intro z I J hj
    exact (Nat.not_lt_zero _ hj).elim
  · intro z hz
    funext s
    rw [← uni_lft_rgt s]
    exact hz (lft s) (rgt s) (Nat.lt_succ_of_le (Finset.card_le_univ _))
  · intro n z hz hdz
    have hzR (I : Finset ι) (J : Finset κ) (hJ : J.card ≤ n) :
        (D.rightSlice I).d (fun B => z (uni I B)) J = 0 := by
      apply differential_zero_of_erases
      intro j hj
      apply hz
      rw [Finset.card_erase_of_mem hj]
      have hp := Finset.card_pos.2 ⟨j, hj⟩
      omega
    have sliceLift (J : Finset κ) : ∃ w : (D.leftSlice J).Cochain,
        (∀ I, J.card ≠ n → w I = 0) ∧
          (∀ I, J.card = n → (D.leftSlice J).d w I = z (uni I J)) := by
      by_cases hJ : J.card = n
      · have hclosed : (D.leftSlice J).d (fun A => z (uni A J)) = 0 := by
          funext I
          have e := congrFun hdz (uni I J)
          rwa [D.d_uni, hzR I J hJ.le, smul_zero, add_zero, Pi.zero_apply] at e
        obtain ⟨w, hw⟩ := h J _ hclosed
        exact ⟨w, fun _ hne => (hne hJ).elim, fun I _ => congrFun hw I⟩
      · exact ⟨0, fun _ _ => rfl, fun _ he => (hJ he).elim⟩
    choose w hw₀ hw₁ using sliceLift
    let a (I : Finset ι) (J : Finset κ) : D.obj (uni I J) := w J I
    let y := (D.cochainSlices ℤ).symm a
    have hy (I : Finset ι) (J : Finset κ) : y (uni I J) = w J I :=
      congrFun (congrFun ((D.cochainSlices ℤ).apply_symm_apply a) I) J
    refine ⟨y, fun I J hJ => ?_⟩
    have hyR : (D.rightSlice I).d (fun B => y (uni I B)) J = 0 := by
      apply differential_zero_of_erases
      intro j hj
      rw [hy]
      apply hw₀
      rw [Finset.card_erase_of_mem hj]
      have hp := Finset.card_pos.2 ⟨j, hj⟩
      omega
    have hyL : (fun A => y (uni A J)) = w J := funext fun A => hy A J
    change z (uni I J) - D.d y (uni I J) = 0
    rw [D.d_uni, hyR, smul_zero, add_zero, hyL]
    by_cases hEq : J.card = n
    · rw [hw₁ J I hEq, sub_self]
    · have hlt : J.card < n := by omega
      have hwz : w J = 0 := funext fun A => hw₀ J A hEq
      rw [hz I J hlt, hwz, FinsetCechDatum.d_zero, Pi.zero_apply, sub_zero]

end HTGeometry.FinsetCechDatum
