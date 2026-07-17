import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolUniversalShiftField

/-!
# Free-shift one-slice rational nonsummability

Let `X_(a,m,n)` be a bilateral shift grid, with `m : ℤ` the translation slice and `n : ℕ` the
differential-jet order.  In the rational function field on this algebraically free grid, no
nonzero finite constant-coefficient linear form supported on the single slice `m = 0` is a shift
coboundary.

The proof uses a finite periodic collapse.  Write a hypothetical rational primitive as `p / q`
and choose a positive shift length absent from every pairwise slice difference in the finite
variable support of `p` and `q`.  Telescoping by that length and renaming each shifted support
variable back to its original variable kills the primitive side after denominator clearing.  The
finite orbit of the one-slice form remains injectively labelled and nonzero, a contradiction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

abbrev FreeShiftJetIndex (α : Type*) := α × (ℤ × ℕ)

abbrev FreeShiftPolynomial (K α : Type*) [Field K] :=
  MvPolynomial (FreeShiftJetIndex α) K

abbrev FreeShiftField (K α : Type*) [Field K] :=
  FractionRing (FreeShiftPolynomial K α)

def freeShiftJetIndexEquiv {α : Type*} (k : ℤ) :
    FreeShiftJetIndex α ≃ FreeShiftJetIndex α where
  toFun x := (x.1, (x.2.1 + k, x.2.2))
  invFun x := (x.1, (x.2.1 - k, x.2.2))
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

def freeShiftPolynomialEquiv {K α : Type*} [Field K] (k : ℤ) :
    FreeShiftPolynomial K α ≃ₐ[K] FreeShiftPolynomial K α :=
  MvPolynomial.renameEquiv K (freeShiftJetIndexEquiv k)

def freeShiftFieldEquiv {K α : Type*} [Field K] (k : ℤ) :
    FreeShiftField K α ≃ₐ[K] FreeShiftField K α :=
  IsFractionRing.algEquivOfAlgEquiv
    (freeShiftPolynomialEquiv (K := K) (α := α) k)

@[simp] theorem freeShiftPolynomialEquiv_X {K α : Type*} [Field K]
    (k : ℤ) (x : FreeShiftJetIndex α) :
    freeShiftPolynomialEquiv (K := K) k (MvPolynomial.X x) =
      MvPolynomial.X (freeShiftJetIndexEquiv k x) := by
  simp [freeShiftPolynomialEquiv]

@[simp] theorem freeShiftFieldEquiv_algebraMap {K α : Type*} [Field K]
    (k : ℤ) (p : FreeShiftPolynomial K α) :
    freeShiftFieldEquiv (K := K) k
        (algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) p) =
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
        (freeShiftPolynomialEquiv (K := K) (α := α) k p) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (freeShiftPolynomialEquiv (K := K) (α := α) k) p

theorem freeShiftJetIndexEquiv_add {α : Type*} (a b : ℤ) (x : FreeShiftJetIndex α) :
    freeShiftJetIndexEquiv a (freeShiftJetIndexEquiv b x) =
      freeShiftJetIndexEquiv (a + b) x := by
  rcases x with ⟨i, m, n⟩
  simp only [freeShiftJetIndexEquiv, Equiv.coe_fn_mk, Prod.mk.injEq, true_and]
  abel
  exact ⟨trivial, trivial⟩

theorem freeShiftPolynomialEquiv_add {K α : Type*} [Field K]
    (a b : ℤ) (p : FreeShiftPolynomial K α) :
    freeShiftPolynomialEquiv a (freeShiftPolynomialEquiv b p) =
      freeShiftPolynomialEquiv (a + b) p := by
  simp only [freeShiftPolynomialEquiv, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_rename]
  apply MvPolynomial.hom_congr_vars
  · ext c
    simp
  · intro x _ _
    simp [freeShiftJetIndexEquiv_add]
  · rfl

theorem freeShiftFieldEquiv_add {K α : Type*} [Field K]
    (a b : ℤ) (x : FreeShiftField K α) :
    freeShiftFieldEquiv a (freeShiftFieldEquiv b x) =
      freeShiftFieldEquiv (a + b) x := by
  obtain ⟨p, q, hq, rfl⟩ :=
    IsFractionRing.div_surjective (FreeShiftPolynomial K α) x
  simp [map_div₀, freeShiftPolynomialEquiv_add]

def freeShiftOneSlice {K α : Type*} [Field K]
    (c : (α × ℕ) →₀ K) : FreeShiftPolynomial K α :=
  c.sum fun j a => (MvPolynomial.C a : FreeShiftPolynomial K α) *
    (MvPolynomial.X (j.1, (0, j.2)) : FreeShiftPolynomial K α)

def freeShiftOrbitSum {K α : Type*} [Field K]
    (N : ℕ) (c : (α × ℕ) →₀ K) : FreeShiftPolynomial K α :=
  ∑ k : Fin N, c.sum fun j a =>
    (MvPolynomial.C a : FreeShiftPolynomial K α) *
      (MvPolynomial.X (j.1, ((k : ℕ), j.2)) : FreeShiftPolynomial K α)

@[simp] theorem freeShiftPolynomialEquiv_oneSlice {K α : Type*} [Field K]
    (k : ℕ) (c : (α × ℕ) →₀ K) :
    freeShiftPolynomialEquiv (K := K) (k : ℤ) (freeShiftOneSlice c) =
      c.sum fun j a => (MvPolynomial.C a : FreeShiftPolynomial K α) *
        (MvPolynomial.X (j.1, ((k : ℕ), j.2)) : FreeShiftPolynomial K α) := by
  classical
  simp [freeShiftOneSlice, Finsupp.sum, freeShiftPolynomialEquiv,
    MvPolynomial.renameEquiv_apply, freeShiftJetIndexEquiv]

theorem freeShiftField_telescope {K α : Type*} [Field K]
    (g F : FreeShiftField K α)
    (h : freeShiftFieldEquiv (K := K) 1 g - g = F) (N : ℕ) :
    freeShiftFieldEquiv (K := K) (N : ℤ) g - g =
      ∑ k ∈ Finset.range N, freeShiftFieldEquiv (K := K) (k : ℤ) F := by
  induction N with
  | zero =>
      obtain ⟨p, q, hq, rfl⟩ :=
        IsFractionRing.div_surjective (FreeShiftPolynomial K α) g
      have hindex0 : freeShiftJetIndexEquiv (α := α) 0 = Equiv.refl _ := by
        ext x <;> simp [freeShiftJetIndexEquiv]
      have hpoly0 (r : FreeShiftPolynomial K α) :
          freeShiftPolynomialEquiv (K := K) (α := α) 0 r = r := by
        simp [freeShiftPolynomialEquiv, hindex0]
      have hfield0 (x : FreeShiftField K α) :
          freeShiftFieldEquiv (K := K) 0 x = x := by
        obtain ⟨r, s, hs, rfl⟩ :=
          IsFractionRing.div_surjective (FreeShiftPolynomial K α) x
        simp [map_div₀, hpoly0]
      simp [hfield0]
  | succ N ih =>
      have hstep : freeShiftFieldEquiv (K := K) (N + 1 : ℤ) g =
          freeShiftFieldEquiv (K := K) (N : ℤ)
            (freeShiftFieldEquiv (K := K) 1 g) := by
        exact (freeShiftFieldEquiv_add (K := K) (α := α) (N : ℤ) 1 g).symm
      have hcast : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by omega
      rw [hcast, hstep]
      calc
        freeShiftFieldEquiv (K := K) (N : ℤ)
              (freeShiftFieldEquiv (K := K) 1 g) - g =
            freeShiftFieldEquiv (K := K) (N : ℤ) (F + g) - g := by
              rw [sub_eq_iff_eq_add.mp h]
        _ = freeShiftFieldEquiv (K := K) (N : ℤ) F +
              (freeShiftFieldEquiv (K := K) (N : ℤ) g - g) := by
              rw [map_add]
              ring
        _ = freeShiftFieldEquiv (K := K) (N : ℤ) F +
              ∑ k ∈ Finset.range N, freeShiftFieldEquiv (K := K) (k : ℤ) F := by
              rw [ih]
        _ = ∑ k ∈ Finset.range (N + 1),
              freeShiftFieldEquiv (K := K) (k : ℤ) F := by
              rw [Finset.sum_range_succ]
              ring

theorem freeShiftField_telescope_oneSlice {K α : Type*} [Field K]
    (g : FreeShiftField K α) (c : (α × ℕ) →₀ K)
    (h : freeShiftFieldEquiv (K := K) 1 g - g =
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
        (freeShiftOneSlice c)) (N : ℕ) :
    freeShiftFieldEquiv (K := K) (N : ℤ) g - g =
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
        (freeShiftOrbitSum N c) := by
  rw [freeShiftField_telescope g _ h N]
  simp only [freeShiftFieldEquiv_algebraMap, freeShiftPolynomialEquiv_oneSlice,
    ← map_sum]
  congr 1
  rw [freeShiftOrbitSum, ← Fin.sum_univ_eq_sum_range]

theorem rename_eq_rename_of_eq_on_vars
    {K σ τ : Type*} [CommRing K] (f g : σ → τ) (p : MvPolynomial σ K)
    (h : ∀ i ∈ p.vars, f i = g i) :
    MvPolynomial.rename f p = MvPolynomial.rename g p := by
  apply MvPolynomial.hom_congr_vars
  · ext a
    simp
  · intro i hi _
    simp [h i hi]
  · rfl

def freeShiftOrbitIndex {α : Type*} {N : ℕ}
    (p : (α × ℕ) × Fin N) : FreeShiftJetIndex α :=
  (p.1.1, ((p.2 : ℕ), p.1.2))

theorem rename_freeShiftOrbitSum_ne_zero
    {K α : Type*} [Field K] (N : ℕ) (hN : 0 < N)
    (c : (α × ℕ) →₀ K) (hc : c ≠ 0)
    (collapse : FreeShiftJetIndex α → FreeShiftJetIndex α)
    (hinj : Function.Injective fun p : (α × ℕ) × Fin N =>
      collapse (freeShiftOrbitIndex p)) :
    MvPolynomial.rename collapse (freeShiftOrbitSum N c) ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hc
  have hjmem : j ∈ c.support := Finsupp.mem_support_iff.mpr hj
  let k0 : Fin N := ⟨0, hN⟩
  let target : FreeShiftJetIndex α := collapse (freeShiftOrbitIndex (j, k0))
  let e : FreeShiftJetIndex α → K := fun x => if x = target then 1 else 0
  have hEq (j' : α × ℕ) (k : Fin N) :
      collapse (freeShiftOrbitIndex (j', k)) = target ↔ j' = j ∧ k = k0 := by
    constructor
    · intro h
      have hp : (j', k) = (j, k0) := hinj (by simpa [target] using h)
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  intro hzero
  have heval := congrArg (MvPolynomial.eval e) hzero
  rw [map_zero, MvPolynomial.eval_rename] at heval
  have hinner (k : Fin N) :
      MvPolynomial.eval (e ∘ collapse)
          (c.sum fun j' a => (MvPolynomial.C a : FreeShiftPolynomial K α) *
            (MvPolynomial.X (j'.1, ((k : ℕ), j'.2)) : FreeShiftPolynomial K α)) =
        if k = k0 then c j else 0 := by
    rw [Finsupp.sum, map_sum]
    have hterm (j' : α × ℕ) (a : K) :
        MvPolynomial.eval (e ∘ collapse)
            ((MvPolynomial.C a : FreeShiftPolynomial K α) *
              (MvPolynomial.X (j'.1, ((k : ℕ), j'.2)) :
                FreeShiftPolynomial K α)) =
          if j' = j ∧ k = k0 then a else 0 := by
      simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        Function.comp_apply]
      have he : e (collapse (freeShiftOrbitIndex (j', k))) =
          if j' = j ∧ k = k0 then 1 else 0 := by
        simp only [e, target]
        rw [if_congr (hEq j' k) rfl rfl]
      rw [show (j'.1, (((k : ℕ) : ℤ), j'.2)) = freeShiftOrbitIndex (j', k) by rfl, he]
      split_ifs <;> simp
    simp_rw [hterm]
    by_cases hk : k = k0
    · rw [if_pos hk]
      subst k
      simp only [and_true]
      rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hj'ne
        simp [hj'ne]
      · exact fun hnot => (hnot hjmem).elim
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro j' _
      simp [hk]
  simp only [freeShiftOrbitSum, map_sum, hinner] at heval
  simp only [Fintype.sum_ite_eq'] at heval
  exact hj heval

/-- A nonzero finite linear form on one slice of the bilateral free differential grid is not a
shift coboundary in its rational function field. -/
theorem freeShiftOneSlice_ne_coboundary
    {K α : Type*} [Field K] (c : (α × ℕ) →₀ K) (hc : c ≠ 0)
    (g : FreeShiftField K α) :
    freeShiftFieldEquiv (K := K) 1 g - g ≠
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
        (freeShiftOneSlice c) := by
  classical
  intro h
  obtain ⟨p, q, hq, rfl⟩ :=
    IsFractionRing.div_surjective (FreeShiftPolynomial K α) g
  let S : Finset (FreeShiftJetIndex α) := p.vars ∪ q.vars
  let differences : Finset ℕ :=
    (S ×ˢ S).image fun xy => (xy.1.2.1 - xy.2.2.1).natAbs
  let N : ℕ := Finset.sum differences id + 1
  have hN : 0 < N := by
    dsimp [N]
    omega
  let shiftN : FreeShiftJetIndex α ≃ FreeShiftJetIndex α :=
    freeShiftJetIndexEquiv (N : ℤ)
  have hshiftN_apply (x : FreeShiftJetIndex α) :
      shiftN x = (x.1, (x.2.1 + (N : ℤ), x.2.2)) := by
    rfl
  have hdisj (x : FreeShiftJetIndex α) (hx : x ∈ S)
      (y : FreeShiftJetIndex α) (hy : y ∈ S) : shiftN y ≠ x := by
    intro heq
    have hmem : (x.2.1 - y.2.1).natAbs ∈ differences := by
      apply Finset.mem_image.mpr
      exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
    have hle : (x.2.1 - y.2.1).natAbs ≤ Finset.sum differences id :=
      Finset.single_le_sum (s := differences) (f := id)
        (fun _ _ => Nat.zero_le _) hmem
    have hdiff : x.2.1 - y.2.1 = (N : ℤ) := by
      have hm := congrArg (fun z : FreeShiftJetIndex α => z.2.1) heq
      rw [hshiftN_apply] at hm
      simp only at hm
      omega
    rw [hdiff, Int.natAbs_natCast] at hle
    dsimp [N] at hle
    omega
  let collapse : FreeShiftJetIndex α → FreeShiftJetIndex α := fun x =>
    if hex : ∃ y, y ∈ S ∧ shiftN y = x then Classical.choose hex else x
  have hcollapse_self (x : FreeShiftJetIndex α) (hx : x ∈ S) : collapse x = x := by
    dsimp only [collapse]
    rw [dif_neg]
    rintro ⟨y, hy, heq⟩
    exact hdisj x hx y hy heq
  have hcollapse_shift (x : FreeShiftJetIndex α) (hx : x ∈ S) :
      collapse (shiftN x) = x := by
    let hex : ∃ y, y ∈ S ∧ shiftN y = shiftN x := ⟨x, hx, rfl⟩
    dsimp only [collapse]
    rw [dif_pos hex]
    apply shiftN.injective
    exact (Classical.choose_spec hex).2
  have hcollapse_poly_self (r : FreeShiftPolynomial K α) (hr : r.vars ⊆ S) :
      MvPolynomial.rename collapse r = r := by
    calc
      MvPolynomial.rename collapse r = MvPolynomial.rename id r :=
        rename_eq_rename_of_eq_on_vars collapse id r
          (fun i hi => hcollapse_self i (hr hi))
      _ = r := MvPolynomial.rename_id_apply r
  have hcollapse_poly_shift (r : FreeShiftPolynomial K α) (hr : r.vars ⊆ S) :
      MvPolynomial.rename collapse
          (freeShiftPolynomialEquiv (K := K) (N : ℤ) r) = r := by
    rw [freeShiftPolynomialEquiv, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_rename]
    calc
      MvPolynomial.rename (collapse ∘ freeShiftJetIndexEquiv (N : ℤ)) r =
          MvPolynomial.rename id r :=
        rename_eq_rename_of_eq_on_vars _ id r (fun i hi => by
          change collapse (shiftN i) = i
          exact hcollapse_shift i (hr hi))
      _ = r := MvPolynomial.rename_id_apply r
  have hpvars : p.vars ⊆ S := fun x hx => Finset.mem_union_left _ hx
  have hqvars : q.vars ⊆ S := fun x hx => Finset.mem_union_right _ hx
  have horbitIndexInj : Function.Injective
      (@freeShiftOrbitIndex α N) := by
    rintro ⟨⟨a, n⟩, k⟩ ⟨⟨b, m⟩, l⟩ heq
    simp only [freeShiftOrbitIndex, Prod.mk.injEq] at heq
    rcases heq with ⟨hab, hkl, hnm⟩
    subst b
    subst m
    have hfin : k = l := Fin.ext (Int.ofNat_inj.mp hkl)
    subst l
    rfl
  have hcollapseOrbitInj : Function.Injective fun z : (α × ℕ) × Fin N =>
      collapse (freeShiftOrbitIndex z) := by
    rintro z w heq
    let x := freeShiftOrbitIndex z
    let y := freeShiftOrbitIndex w
    by_cases hx : ∃ u, u ∈ S ∧ shiftN u = x
    · by_cases hy : ∃ u, u ∈ S ∧ shiftN u = y
      · have huv : Classical.choose hx = Classical.choose hy := by
          change (if hex : ∃ u, u ∈ S ∧ shiftN u = x then Classical.choose hex else x) =
            (if hex : ∃ u, u ∈ S ∧ shiftN u = y then Classical.choose hex else y) at heq
          simpa only [dif_pos hx, dif_pos hy] using heq
        apply horbitIndexInj
        change x = y
        calc
          x = shiftN (Classical.choose hx) := (Classical.choose_spec hx).2.symm
          _ = shiftN (Classical.choose hy) := by rw [huv]
          _ = y := (Classical.choose_spec hy).2
      · have hxy : Classical.choose hx = y := by
          change (if hex : ∃ u, u ∈ S ∧ shiftN u = x then Classical.choose hex else x) =
            (if hex : ∃ u, u ∈ S ∧ shiftN u = y then Classical.choose hex else y) at heq
          simpa only [dif_pos hx, dif_neg hy] using heq
        have hm1 := congrArg (fun t : FreeShiftJetIndex α => t.2.1)
          (Classical.choose_spec hx).2
        have hm2 := congrArg (fun t : FreeShiftJetIndex α => t.2.1) hxy
        rcases z with ⟨⟨a, n⟩, k⟩
        rcases w with ⟨⟨b, m⟩, l⟩
        simp only [x, y, freeShiftOrbitIndex, hshiftN_apply] at hm1 hm2
        omega
    · by_cases hy : ∃ u, u ∈ S ∧ shiftN u = y
      · have hxy : x = Classical.choose hy := by
          change (if hex : ∃ u, u ∈ S ∧ shiftN u = x then Classical.choose hex else x) =
            (if hex : ∃ u, u ∈ S ∧ shiftN u = y then Classical.choose hex else y) at heq
          simpa only [dif_neg hx, dif_pos hy] using heq
        have hm1 := congrArg (fun t : FreeShiftJetIndex α => t.2.1)
          (Classical.choose_spec hy).2
        have hm2 := congrArg (fun t : FreeShiftJetIndex α => t.2.1) hxy
        rcases z with ⟨⟨a, n⟩, k⟩
        rcases w with ⟨⟨b, m⟩, l⟩
        simp only [x, y, freeShiftOrbitIndex, hshiftN_apply] at hm1 hm2
        omega
      · apply horbitIndexInj
        change (if hex : ∃ u, u ∈ S ∧ shiftN u = x then Classical.choose hex else x) =
          (if hex : ∃ u, u ∈ S ∧ shiftN u = y then Classical.choose hex else y) at heq
        simpa only [dif_neg hx, dif_neg hy] using heq
  have horbit : MvPolynomial.rename collapse (freeShiftOrbitSum N c) ≠ 0 :=
    rename_freeShiftOrbitSum_ne_zero N hN c hc collapse hcollapseOrbitInj
  have htel := freeShiftField_telescope_oneSlice
    (K := K) (α := α)
    (algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) p /
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) q) c h N
  have hqN : freeShiftPolynomialEquiv (K := K) (N : ℤ) q ≠ 0 :=
    (freeShiftPolynomialEquiv (K := K) (N : ℤ)).injective.ne
      (mem_nonZeroDivisors_iff_ne_zero.mp hq)
  have hfrac :
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
          (freeShiftPolynomialEquiv (K := K) (N : ℤ) p) /
        algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
          (freeShiftPolynomialEquiv (K := K) (N : ℤ) q) -
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) p /
        algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) q =
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
        (freeShiftOrbitSum N c) := by
    simpa [map_div₀] using htel
  have hcross :
      freeShiftPolynomialEquiv (K := K) (N : ℤ) p * q -
          p * freeShiftPolynomialEquiv (K := K) (N : ℤ) q =
        freeShiftOrbitSum N c *
          (freeShiftPolynomialEquiv (K := K) (N : ℤ) q * q) := by
    apply (IsFractionRing.injective (FreeShiftPolynomial K α)
      (FreeShiftField K α))
    simp only [map_sub, map_mul]
    have hq0 : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
    field_simp [hqN, hq0] at hfrac ⊢
    exact hfrac
  have hcollapsed := congrArg (MvPolynomial.rename collapse) hcross
  simp only [map_sub, map_mul, hcollapse_poly_shift p hpvars,
    hcollapse_poly_shift q hqvars, hcollapse_poly_self p hpvars,
    hcollapse_poly_self q hqvars, sub_self, zero_eq_mul] at hcollapsed
  have hq0 : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
  exact horbit (hcollapsed.resolve_right (mul_ne_zero hq0 hq0))

end

end GaloisForLFunctions.HTGeometry
