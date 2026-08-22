import GaloisForLFunctions.HTGeometry.MvPowerSeriesSumSplit
import GaloisForLFunctions.HTGeometry.MvPowerSeriesRootFamily
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Singling out one variable of a multivariate power series ring

Keeping one variable and deforming all the others is the arrangement in which a single transverse
coupling stays a variable of the base field while the rest become deformation parameters.  Splitting
the variable set as `{i} ⊕ {j ≠ i}` presents the multivariate power series ring as a power series
ring in the remaining variables over the one-variable ring.

## Main results

* `sumSplit_C`, `sumSplit_X_inl`, `sumSplit_X_inr` — the block splitting on generators.
* `dirEquiv`, `dirSplit` — the presentation `A⟦u⟧ ≃ (A⟦u_i⟧)⟦u_{≠i}⟧`.
* `dirRes` — the induced reduction to the one-variable ring, and its values on polynomials.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ τ A : Type} [CommSemiring A]

@[simp] theorem sumCons_apply_inl (m : σ →₀ ℕ) (d : τ →₀ ℕ) (x : σ) :
    sumCons m d (Sum.inl x) = m x :=
  Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inl (M := ℕ) (m, d) x

@[simp] theorem sumCons_apply_inr (m : σ →₀ ℕ) (d : τ →₀ ℕ) (y : τ) :
    sumCons m d (Sum.inr y) = d y :=
  Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inr (M := ℕ) (m, d) y

theorem sumCons_eq_iff {m : σ →₀ ℕ} {d : τ →₀ ℕ} {e : σ ⊕ τ →₀ ℕ} :
    sumCons m d = e ↔ (∀ x, m x = e (Sum.inl x)) ∧ (∀ y, d y = e (Sum.inr y)) := by
  constructor
  · rintro rfl
    exact ⟨fun x => (sumCons_apply_inl m d x).symm, fun y => (sumCons_apply_inr m d y).symm⟩
  · rintro ⟨h1, h2⟩
    ext k
    cases k with
    | inl x => rw [sumCons_apply_inl, h1]
    | inr y => rw [sumCons_apply_inr, h2]

theorem sumSplit_C [DecidableEq σ] [DecidableEq τ] (a : A) :
    sumSplit (MvPowerSeries.C a : MvPowerSeries (σ ⊕ τ) A)
      = MvPowerSeries.C (MvPowerSeries.C a) := by
  classical
  ext d m
  rw [coeff_sumSplit, MvPowerSeries.coeff_C]
  have hRHS : MvPowerSeries.coeff m (MvPowerSeries.coeff d
      (MvPowerSeries.C (MvPowerSeries.C a) : MvPowerSeries τ (MvPowerSeries σ A)))
      = if (m = 0 ∧ d = 0) then a else 0 := by
    rw [MvPowerSeries.coeff_C]
    by_cases hd : d = 0
    · rw [if_pos hd, MvPowerSeries.coeff_C]
      by_cases hm : m = 0
      · rw [if_pos hm, if_pos ⟨hm, hd⟩]
      · rw [if_neg hm, if_neg (fun h => hm h.1)]
    · rw [if_neg hd, MvPowerSeries.coeff_zero, if_neg (fun h => hd h.2)]
  rw [hRHS]
  by_cases h : m = 0 ∧ d = 0
  · rw [if_pos h, if_pos (sumCons_eq_zero_iff.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (sumCons_eq_zero_iff.mp hc))]

theorem sumSplit_X_inl [DecidableEq σ] [DecidableEq τ] (x : σ) :
    sumSplit (MvPowerSeries.X (Sum.inl x) : MvPowerSeries (σ ⊕ τ) A)
      = MvPowerSeries.C (MvPowerSeries.X x) := by
  classical
  ext d m
  rw [coeff_sumSplit, MvPowerSeries.coeff_X]
  have hiff : sumCons m d = Finsupp.single (Sum.inl x) 1 ↔ (m = Finsupp.single x 1 ∧ d = 0) := by
    rw [sumCons_eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Finsupp.ext fun w => ?_, Finsupp.ext fun y => ?_⟩
      · rw [h1 w, Finsupp.single_apply, Finsupp.single_apply]
        by_cases hw : x = w
        · rw [if_pos hw, if_pos (by rw [hw])]
        · rw [if_neg hw, if_neg (fun h => hw (Sum.inl_injective h))]
      · rw [h2 y, Finsupp.single_apply, if_neg (by simp), Finsupp.coe_zero, Pi.zero_apply]
    · rintro ⟨rfl, rfl⟩
      refine ⟨fun w => ?_, fun y => ?_⟩
      · rw [Finsupp.single_apply, Finsupp.single_apply]
        by_cases hw : x = w
        · rw [if_pos hw, if_pos (by rw [hw])]
        · rw [if_neg hw, if_neg (fun h => hw (Sum.inl_injective h))]
      · rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply, if_neg (by simp)]
  have hRHS : MvPowerSeries.coeff m (MvPowerSeries.coeff d
      (MvPowerSeries.C (MvPowerSeries.X x) : MvPowerSeries τ (MvPowerSeries σ A)))
      = if (m = Finsupp.single x 1 ∧ d = 0) then 1 else 0 := by
    rw [MvPowerSeries.coeff_C]
    by_cases hd : d = 0
    · rw [if_pos hd, MvPowerSeries.coeff_X]
      by_cases hm : m = Finsupp.single x 1
      · rw [if_pos hm, if_pos ⟨hm, hd⟩]
      · rw [if_neg hm, if_neg (fun h => hm h.1)]
    · rw [if_neg hd, MvPowerSeries.coeff_zero, if_neg (fun h => hd h.2)]
  rw [hRHS]
  by_cases h : m = Finsupp.single x 1 ∧ d = 0
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]

theorem sumSplit_X_inr [DecidableEq σ] [DecidableEq τ] (y : τ) :
    sumSplit (MvPowerSeries.X (Sum.inr y) : MvPowerSeries (σ ⊕ τ) A)
      = MvPowerSeries.X y := by
  classical
  ext d m
  rw [coeff_sumSplit, MvPowerSeries.coeff_X]
  have hiff : sumCons m d = Finsupp.single (Sum.inr y) 1 ↔ (m = 0 ∧ d = Finsupp.single y 1) := by
    rw [sumCons_eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Finsupp.ext fun w => ?_, Finsupp.ext fun v => ?_⟩
      · rw [h1 w, Finsupp.single_apply, if_neg (by simp), Finsupp.coe_zero, Pi.zero_apply]
      · rw [h2 v, Finsupp.single_apply, Finsupp.single_apply]
        by_cases hv : y = v
        · rw [if_pos hv, if_pos (by rw [hv])]
        · rw [if_neg hv, if_neg (fun h => hv (Sum.inr_injective h))]
    · rintro ⟨rfl, rfl⟩
      refine ⟨fun w => ?_, fun v => ?_⟩
      · rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply, if_neg (by simp)]
      · rw [Finsupp.single_apply, Finsupp.single_apply]
        by_cases hv : y = v
        · rw [if_pos hv, if_pos (by rw [hv])]
        · rw [if_neg hv, if_neg (fun h => hv (Sum.inr_injective h))]
  have hRHS : MvPowerSeries.coeff m (MvPowerSeries.coeff d
      (MvPowerSeries.X y : MvPowerSeries τ (MvPowerSeries σ A)))
      = if (m = 0 ∧ d = Finsupp.single y 1) then 1 else 0 := by
    rw [MvPowerSeries.coeff_X]
    by_cases hd : d = Finsupp.single y 1
    · rw [if_pos hd, MvPowerSeries.coeff_one]
      by_cases hm : m = 0
      · rw [if_pos hm, if_pos ⟨hm, hd⟩]
      · rw [if_neg hm, if_neg (fun h => hm h.1)]
    · rw [if_neg hd, MvPowerSeries.coeff_zero, if_neg (fun h => hd h.2)]
  rw [hRHS]
  by_cases h : m = 0 ∧ d = Finsupp.single y 1
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]

variable {ι : Type} [DecidableEq ι]

/-- Sending the chosen point to the left summand and every other point to the right one. -/
def dirFun (i : ι) (j : ι) : Unit ⊕ {k : ι // k ≠ i} :=
  if h : j = i then Sum.inl () else Sum.inr ⟨j, h⟩

theorem dirFun_self (i : ι) : dirFun i i = Sum.inl () := dif_pos rfl

theorem dirFun_ne {i j : ι} (h : j ≠ i) : dirFun i j = Sum.inr ⟨j, h⟩ := dif_neg h

/-- Splitting an index type into one chosen point and its complement. -/
def dirEquiv (i : ι) : ι ≃ Unit ⊕ {j : ι // j ≠ i} where
  toFun := dirFun i
  invFun := Sum.elim (fun _ => i) Subtype.val
  left_inv j := by
    by_cases h : j = i
    · rw [h, dirFun_self]
      rfl
    · rw [dirFun_ne h]
      rfl
  right_inv k := by
    cases k with
    | inl u =>
        show dirFun i (Sum.elim (fun _ => i) Subtype.val (Sum.inl u)) = Sum.inl u
        rw [show (Sum.elim (fun _ => i) Subtype.val (Sum.inl u) : ι) = i from rfl, dirFun_self]
    | inr p =>
        obtain ⟨j, hj⟩ := p
        show dirFun i (Sum.elim (fun _ => i) Subtype.val (Sum.inr ⟨j, hj⟩)) = Sum.inr ⟨j, hj⟩
        rw [show (Sum.elim (fun _ => i) Subtype.val (Sum.inr ⟨j, hj⟩) : ι) = j from rfl,
          dirFun_ne hj]

@[simp] theorem dirEquiv_self (i : ι) : dirEquiv i i = Sum.inl () := dirFun_self i

@[simp] theorem dirEquiv_ne {i j : ι} (h : j ≠ i) : dirEquiv i j = Sum.inr ⟨j, h⟩ := dirFun_ne h

/-- **Presenting a multivariate power series ring as a deformation of one variable.** -/
def dirSplit (A : Type) [CommSemiring A] (i : ι) :
    MvPowerSeries ι A ≃+* MvPowerSeries {j : ι // j ≠ i} (PowerSeries A) :=
  (mvRenameEquiv (dirEquiv i)).trans (MvPowerSeries.sumEquiv Unit {j : ι // j ≠ i} A)

theorem dirSplit_apply (i : ι) (f : MvPowerSeries ι A) :
    dirSplit A i f = sumSplit (MvPowerSeries.rename (dirEquiv i) f) := rfl

/-- The reduction of a deformation to the one variable kept in the base. -/
def dirRes (A : Type) [CommSemiring A] (i : ι) : MvPowerSeries ι A →+* PowerSeries A :=
  (MvPowerSeries.constantCoeff (σ := {j : ι // j ≠ i}) (R := PowerSeries A)).comp
    (dirSplit A i : MvPowerSeries ι A →+* MvPowerSeries {j : ι // j ≠ i} (PowerSeries A))

theorem constantCoeff_dirRes (i : ι) (f : MvPowerSeries ι A) :
    PowerSeries.constantCoeff (dirRes A i f) = MvPowerSeries.constantCoeff f := by
  show MvPowerSeries.constantCoeff
      (MvPowerSeries.constantCoeff (sumSplit (MvPowerSeries.rename (dirEquiv i) f))) = _
  rw [constantCoeff_sumSplit, MvPowerSeries.constantCoeff_rename]

theorem dirSplit_coe_C (i : ι) (a : A) :
    dirSplit A i (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.C a))
      = MvPowerSeries.C (PowerSeries.C a) := by
  classical
  rw [dirSplit_apply, show MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.C a)
      = (MvPowerSeries.C a : MvPowerSeries ι A) from MvPolynomial.coe_C a, MvPowerSeries.rename_C]
  exact sumSplit_C a

theorem dirSplit_coe_X_self (i : ι) :
    dirSplit A i (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.X i))
      = MvPowerSeries.C (PowerSeries.X) := by
  classical
  rw [dirSplit_apply, show MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.X i)
      = (MvPowerSeries.X i : MvPowerSeries ι A) from MvPolynomial.coe_X i, MvPowerSeries.rename_X,
    show (dirEquiv i : ι → Unit ⊕ {k : ι // k ≠ i}) i = Sum.inl () from dirEquiv_self i]
  exact sumSplit_X_inl ()

theorem dirSplit_coe_X_ne {i j : ι} (h : j ≠ i) :
    dirSplit A i (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.X j))
      = MvPowerSeries.X ⟨j, h⟩ := by
  classical
  rw [dirSplit_apply, show MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.X j)
      = (MvPowerSeries.X j : MvPowerSeries ι A) from MvPolynomial.coe_X j, MvPowerSeries.rename_X,
    show (dirEquiv i : ι → Unit ⊕ {k : ι // k ≠ i}) j = Sum.inr ⟨j, h⟩ from dirEquiv_ne h]
  exact sumSplit_X_inr (⟨j, h⟩ : {k : ι // k ≠ i})

theorem dirRes_coe_C (i : ι) (a : A) :
    dirRes A i (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.C a)) = PowerSeries.C a := by
  show MvPowerSeries.constantCoeff (dirSplit A i _) = _
  rw [dirSplit_coe_C]
  exact MvPowerSeries.constantCoeff_C _

theorem dirRes_coe_X_self (i : ι) :
    dirRes A i (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.X i)) = PowerSeries.X := by
  show MvPowerSeries.constantCoeff (dirSplit A i _) = _
  rw [dirSplit_coe_X_self]
  exact MvPowerSeries.constantCoeff_C _

theorem dirRes_coe_X_ne {i j : ι} (h : j ≠ i) :
    dirRes A i (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.X j)) = 0 := by
  show MvPowerSeries.constantCoeff (dirSplit A i _) = _
  rw [dirSplit_coe_X_ne h]
  exact MvPowerSeries.constantCoeff_X _

end

end GaloisForLFunctions.HTGeometry
