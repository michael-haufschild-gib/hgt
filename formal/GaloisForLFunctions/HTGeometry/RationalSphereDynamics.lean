import GaloisForLFunctions.HTGeometry.RationalConnectionCharts

/-!
# A rational map acting on the projective line

Points of the projective line are `Option K`, with `none` the point at infinity.  The chart at a
finite point is the identity, the chart at infinity the inversion `ι(x) = 1/x`.  A nonconstant
rational map `R` acts on points, and in the charts at a point `p` and at its image `R p` it is
represented by the rational function `φ_{R p} ∘ R ∘ φ_p`, regular at the chart coordinate of `p`
with
value the chart coordinate of `R p`.  Its order of contact there is the **local degree** `e(p)`.

* **Fibres.**  The preimages of `w` are the zeros on the projective line of `R − w` (of `1/R` when
  `w = ∞`), and the local degrees over `w` add up to `deg R`.  Hence every point has a preimage, and
  a
  point which is the only preimage of its image has local degree `deg R`.
* **Finite backward-invariant sets.**  A finite set containing every preimage of each of its points
  is mapped bijectively onto itself; each of its points is periodic and is the only preimage of its
  image.
* **Transport.**  In the charts, the pullback of an affine or projective connection along `R` is the
  pullback of the local connection along the local representative.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-! ### Regular points -/

omit [CharZero K] in
theorem ratOrder_nonneg_of_denom_eval {f : RatFunc K} {z : K} (h : f.denom.eval z ≠ 0) :
    0 ≤ ratOrder f z := by
  rw [ratOrder, rootMultiplicity_eq_zero h]
  simp

/-- Every rational function is regular somewhere. -/
theorem exists_ratOrder_nonneg_point (f : RatFunc K) : ∃ z : K, 0 ≤ ratOrder f z := by
  classical
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset f.denom.roots.toFinset
  refine ⟨z, ratOrder_nonneg_of_denom_eval fun h => hz ?_⟩
  exact Multiset.mem_toFinset.mpr ((mem_roots (RatFunc.denom_ne_zero f)).mpr h)

theorem ratFuncDeriv_ne_zero_of_nonconst' {P : RatFunc K} (hPc : ¬ ∃ c : K, P = RatFunc.C c) :
    ratFuncDeriv P ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_ratOrder_nonneg_point P
  exact ratFuncDeriv_ne_zero_of_nonconst hPc hz

/-- A function whose difference with a constant vanishes at `z` is regular there, with that value.
-/
theorem regular_of_sub_C_pos {f : RatFunc K} {z c : K} (h : 0 < ratOrder (f - RatFunc.C c) z) :
    0 ≤ ratOrder f z ∧ ratValue f z = c := by
  have hf : f = (f - RatFunc.C c) - RatFunc.C (-c) := by rw [map_neg]; ring
  have hreg : 0 ≤ ratOrder f z := by
    rw [hf]; exact ratOrder_sub_nonneg h.le (ratOrder_C_nonneg _ z)
  refine ⟨hreg, ?_⟩
  have h0 : f - RatFunc.C c ≠ 0 := fun h0 => by rw [h0, ratOrder_zero] at h; exact lt_irrefl _ h
  have hv := (ratValue_eq_zero_iff h0 h.le).mpr h
  rw [ratValue_sub hreg (ratOrder_C_nonneg c z), ratValue_C] at hv
  exact sub_eq_zero.mp hv

/-! ### Charts -/

/-- The chart map: the identity at finite points, the inversion at infinity. -/
def chartMap : Option K → RatFunc K
  | some _ => RatFunc.X
  | none => invX

/-- The chart coordinate of a point. -/
def sphereCoord : Option K → K
  | some z => z
  | none => 0

omit [CharZero K] in
theorem chartMap_nonconst : ∀ p : Option K, ¬ ∃ c : K, chartMap p = RatFunc.C c
  | some _ => nonconst_X
  | none => nonconst_invX

theorem ratFuncDeriv_chartMap_ne_zero (p : Option K) : ratFuncDeriv (chartMap p) ≠ 0 :=
  ratFuncDeriv_ne_zero_of_nonconst' (chartMap_nonconst p)

omit [CharZero K] in
theorem subst_chartMap_some (z : K) (f : RatFunc K) :
    ratFuncSubstitutionAlgHom (chartMap (some z)) (chartMap_nonconst (some z)) f = f :=
  subst_X_eq f

theorem connPull_chartMap_chartMap (p : Option K) (a : RatFunc K) :
    connPull (chartMap p) (chartMap_nonconst p) (connPull (chartMap p) (chartMap_nonconst p) a)
      = a := by
  cases p with
  | some z => exact (congrArg _ (connPull_X a)).trans (connPull_X a)
  | none => exact connPull_invX_invX a

theorem projPull_chartMap_chartMap (p : Option K) (γ : RatFunc K) :
    projPull (chartMap p) (chartMap_nonconst p) (projPull (chartMap p) (chartMap_nonconst p) γ)
      = γ := by
  cases p with
  | some z => exact (congrArg _ (projPull_X γ)).trans (projPull_X γ)
  | none => exact projPull_invX_invX γ

/-- The order of a function at a point of the projective line, read in the chart. -/
def zeroOrd (T : RatFunc K) (p : Option K) : ℤ :=
  ratOrder (ratFuncSubstitutionAlgHom (chartMap p) (chartMap_nonconst p) T) (sphereCoord p)

omit [CharZero K] in
theorem zeroOrd_some (T : RatFunc K) (z : K) : zeroOrd T (some z) = ratOrder T z := by
  rw [zeroOrd, subst_chartMap_some]
  rfl

omit [CharZero K] in
theorem zeroOrd_none {T : RatFunc K} (hT : T ≠ 0) :
    zeroOrd T none = (T.denom.natDegree : ℤ) - T.num.natDegree :=
  ratOrder_subst_invX hT

/-! ### The action on points -/

variable (R : RatFunc K)

/-- The map in the chart at the source point. -/
def srcRep (p : Option K) : RatFunc K :=
  ratFuncSubstitutionAlgHom (chartMap p) (chartMap_nonconst p) R

omit [CharZero K] in
theorem srcRep_nonconst {R : RatFunc K} (hR : ¬ ∃ c : K, R = RatFunc.C c) (p : Option K) :
    ¬ ∃ c : K, srcRep R p = RatFunc.C c :=
  nonconst_subst hR (chartMap_nonconst p)

/-- **The image of a point.** -/
def ptImage (p : Option K) : Option K :=
  if 0 ≤ ratOrder (srcRep R p) (sphereCoord p) then some (ratValue (srcRep R p) (sphereCoord p))
  else none

/-- The function whose zeros are the preimages of `w`: `R − w`, or `1/R` for `w = ∞`. -/
def fibreFn : Option K → RatFunc K
  | some w => R - RatFunc.C w
  | none => R⁻¹

variable {R}

omit [CharZero K] in
theorem fibreFn_nonconst (hR : ¬ ∃ c : K, R = RatFunc.C c) :
    ∀ w : Option K, ¬ ∃ c : K, fibreFn R w = RatFunc.C c
  | some w => fun ⟨c, hc⟩ => hR ⟨c + w, by rw [map_add, ← hc, fibreFn]; ring⟩
  | none => fun ⟨c, hc⟩ => hR ⟨c⁻¹, by rw [map_inv₀, ← hc, fibreFn, inv_inv]⟩

omit [CharZero K] in
theorem ratFuncDegree_X : ratFuncDegree (RatFunc.X : RatFunc K) = 1 := by
  rw [ratFuncDegree, RatFunc.num_X, RatFunc.denom_X, natDegree_X, natDegree_one]
  rfl

omit [CharZero K] in
theorem ratFuncDegree_X_sub_C (w : K) :
    ratFuncDegree (RatFunc.X - RatFunc.C w : RatFunc K) = 1 := by
  have hc : ¬ ∃ c : K, (RatFunc.X - RatFunc.C w : RatFunc K) = RatFunc.C c :=
    fun ⟨c, hc⟩ => nonconst_X ⟨c + w, by rw [map_add, ← hc]; ring⟩
  have h := ratFuncDegree_substitution (RatFunc.X - RatFunc.C w) (RatFunc.X + RatFunc.C w) hc
  rw [map_add, ratFuncSubstitutionAlgHom_X, ratFuncSubstitutionAlgHom_C, sub_add_cancel,
    ratFuncDegree_X] at h
  exact (Nat.eq_one_of_mul_eq_one_left h.symm)

omit [CharZero K] in
theorem ratFuncDegree_invX : ratFuncDegree (invX : RatFunc K) = 1 := by
  have h := ratFuncDegree_substitution (invX : RatFunc K) invX nonconst_invX
  rw [subst_invX_invX, ratFuncDegree_X] at h
  exact Nat.eq_one_of_mul_eq_one_left h.symm

omit [CharZero K] in
theorem subst_invX_eq_inv {P : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c) :
    ratFuncSubstitutionAlgHom P hP (invX : RatFunc K) = P⁻¹ := by
  show ratFuncSubstitutionAlgHom P hP ((RatFunc.X : RatFunc K)⁻¹) = P⁻¹
  rw [map_inv₀, ratFuncSubstitutionAlgHom_X]

omit [CharZero K] in
theorem ratFuncDegree_fibreFn (hR : ¬ ∃ c : K, R = RatFunc.C c) :
    ∀ w : Option K, ratFuncDegree (fibreFn R w) = ratFuncDegree R
  | some w => by
      have h := ratFuncDegree_substitution R (RatFunc.X - RatFunc.C w) hR
      rw [map_sub, ratFuncSubstitutionAlgHom_X, ratFuncSubstitutionAlgHom_C,
        ratFuncDegree_X_sub_C, one_mul] at h
      exact h
  | none => by
      have h := ratFuncDegree_substitution R invX hR
      rw [subst_invX_eq_inv, ratFuncDegree_invX, one_mul] at h
      exact h

omit [CharZero K] in
theorem subst_fibreFn_some (p : Option K) (w : K) :
    ratFuncSubstitutionAlgHom (chartMap p) (chartMap_nonconst p) (fibreFn R (some w))
      = srcRep R p - RatFunc.C w := by
  rw [fibreFn, map_sub, ratFuncSubstitutionAlgHom_C, srcRep]

omit [CharZero K] in
theorem subst_fibreFn_none (p : Option K) :
    ratFuncSubstitutionAlgHom (chartMap p) (chartMap_nonconst p) (fibreFn R none)
      = (srcRep R p)⁻¹ := by
  rw [fibreFn, map_inv₀, srcRep]

/-- **The preimages of `w` are the zeros of the fibre function.** -/
theorem ptImage_eq_iff (hR : ¬ ∃ c : K, R = RatFunc.C c) (p w : Option K) :
    ptImage R p = w ↔ 0 < zeroOrd (fibreFn R w) p := by
  have hF := srcRep_nonconst hR p
  have hF0 : srcRep R p ≠ 0 := fun h0 => hF ⟨0, by rw [h0, map_zero]⟩
  cases w with
  | some w =>
      rw [zeroOrd, subst_fibreFn_some, ptImage]
      split_ifs with h
      · rw [Option.some_inj]
        constructor
        · rintro rfl
          exact ratOrder_sub_ratValue_pos hF (denom_eval_ne_zero_of_regular h)
        · intro hpos
          exact (regular_of_sub_C_pos hpos).2
      · simp only [false_iff]
        exact fun hpos => h (regular_of_sub_C_pos hpos).1
  | none =>
      rw [zeroOrd, subst_fibreFn_none, ratOrder_inv hF0, ptImage]
      split_ifs with h
      · simp only [false_iff]
        omega
      · simp only [true_iff]
        omega

/-- **The map in the charts at a point and its image.** -/
def locRep (hR : ¬ ∃ c : K, R = RatFunc.C c) (p : Option K) : RatFunc K :=
  ratFuncSubstitutionAlgHom (srcRep R p) (srcRep_nonconst hR p) (chartMap (ptImage R p))

omit [CharZero K] in
theorem locRep_nonconst (hR : ¬ ∃ c : K, R = RatFunc.C c) (p : Option K) :
    ¬ ∃ c : K, locRep hR p = RatFunc.C c :=
  nonconst_subst (chartMap_nonconst _) (srcRep_nonconst hR p)

omit [CharZero K] in
theorem locRep_sub_eq (hR : ¬ ∃ c : K, R = RatFunc.C c) (p : Option K) :
    locRep hR p - RatFunc.C (sphereCoord (ptImage R p))
      = ratFuncSubstitutionAlgHom (chartMap p) (chartMap_nonconst p)
          (fibreFn R (ptImage R p)) := by
  unfold locRep
  generalize ptImage R p = w
  cases w with
  | some w =>
      rw [subst_fibreFn_some]
      exact congrArg (· - RatFunc.C w) (ratFuncSubstitutionAlgHom_X _ _)
  | none =>
      rw [subst_fibreFn_none, sphereCoord, map_zero, sub_zero]
      exact subst_invX_eq_inv _

/-- **The local degree** at a point. -/
def locDeg (p : Option K) : ℤ :=
  zeroOrd (fibreFn R (ptImage R p)) p

theorem locDeg_pos (hR : ¬ ∃ c : K, R = RatFunc.C c) (p : Option K) : 0 < locDeg (R := R) p :=
  (ptImage_eq_iff hR p (ptImage R p)).mp rfl

/-- **The local representative is regular, with the right value and contact order.** -/
theorem locRep_regular (hR : ¬ ∃ c : K, R = RatFunc.C c) (p : Option K) :
    0 ≤ ratOrder (locRep hR p) (sphereCoord p) ∧
      ratValue (locRep hR p) (sphereCoord p) = sphereCoord (ptImage R p) ∧
      ratOrder (locRep hR p - RatFunc.C (ratValue (locRep hR p) (sphereCoord p))) (sphereCoord p)
        = locDeg (R := R) p := by
  have hpos :
      0 < ratOrder (locRep hR p - RatFunc.C (sphereCoord (ptImage R p))) (sphereCoord p) := by
    rw [locRep_sub_eq]; exact locDeg_pos hR p
  obtain ⟨hreg, hval⟩ := regular_of_sub_C_pos hpos
  refine ⟨hreg, hval, ?_⟩
  rw [hval, locRep_sub_eq]
  rfl

/-! ### Fibres -/

omit [CharZero K] in
theorem ratOrder_of_num_isRoot {T : RatFunc K} {z : K} (h : T.num.IsRoot z) :
    ratOrder T z = rootMultiplicity z T.num := by
  have hcop : IsCoprime T.num T.denom := RatFunc.isCoprime_num_denom T
  have hd : ¬ T.denom.IsRoot z := by
    intro h2
    exact Polynomial.not_isUnit_X_sub_C z
      (hcop.isUnit_of_dvd' (dvd_iff_isRoot.mpr h) (dvd_iff_isRoot.mpr h2))
  rw [ratOrder, rootMultiplicity_eq_zero hd]
  simp

omit [CharZero K] in
theorem ratOrder_pos_iff {T : RatFunc K} (hT : T ≠ 0) (z : K) :
    0 < ratOrder T z ↔ T.num.IsRoot z := by
  constructor
  · intro h
    by_contra hn
    rw [ratOrder, rootMultiplicity_eq_zero hn] at h
    omega
  · intro h
    rw [ratOrder_of_num_isRoot h]
    exact_mod_cast (rootMultiplicity_pos (RatFunc.num_ne_zero hT)).mpr h

/-- The zeros of a function on the projective line. -/
def zeroSet [DecidableEq K] (T : RatFunc K) : Finset (Option K) :=
  T.num.roots.toFinset.image some ∪
    (if T.num.natDegree < T.denom.natDegree then {none} else ∅)

omit [CharZero K] in
theorem mem_zeroSet [DecidableEq K] {T : RatFunc K} (hT : T ≠ 0) (p : Option K) :
    p ∈ zeroSet T ↔ 0 < zeroOrd T p := by
  cases p with
  | some z =>
      rw [zeroOrd_some, ratOrder_pos_iff hT, zeroSet, Finset.mem_union, Finset.mem_image]
      have hn : (some z : Option K) ∉ (if T.num.natDegree < T.denom.natDegree then
          ({none} : Finset (Option K)) else ∅) := by
        split_ifs <;> simp
      simp only [hn, or_false, Option.some_inj, exists_eq_right, Multiset.mem_toFinset]
      exact mem_roots (RatFunc.num_ne_zero hT)
  | none =>
      rw [zeroOrd_none hT, zeroSet, Finset.mem_union, Finset.mem_image]
      simp only [reduceCtorEq, and_false, exists_false, false_or]
      split_ifs with h
      · simp only [Finset.mem_singleton, true_iff]; omega
      · simp only [Finset.notMem_empty, false_iff]; omega

omit [CharZero K] in
/-- **The orders of the zeros add up to the degree.** -/
theorem sum_zeroSet [IsAlgClosed K] [DecidableEq K] {T : RatFunc K} (hT : T ≠ 0) :
    ∑ p ∈ zeroSet T, zeroOrd T p = ratFuncDegree T := by
  have hdisj : Disjoint (T.num.roots.toFinset.image some)
      (if T.num.natDegree < T.denom.natDegree then ({none} : Finset (Option K)) else ∅) := by
    rw [Finset.disjoint_left]
    intro p hp
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hp
    split_ifs <;> simp
  rw [zeroSet, Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h => Option.some_inj.mp h)]
  have hfin : ∑ z ∈ T.num.roots.toFinset, zeroOrd T (some z) = (T.num.natDegree : ℤ) := by
    have h1 : ∀ z ∈ T.num.roots.toFinset, zeroOrd T (some z)
        = ((T.num.roots.count z : ℕ) : ℤ) := by
      intro z hz
      rw [zeroOrd_some, count_roots, ratOrder_of_num_isRoot
        ((mem_roots (RatFunc.num_ne_zero hT)).mp (Multiset.mem_toFinset.mp hz))]
    rw [Finset.sum_congr rfl h1, ← Nat.cast_sum, Multiset.toFinset_sum_count_eq,
      IsAlgClosed.card_roots_eq_natDegree]
  rw [hfin, ratFuncDegree]
  split_ifs with h
  · rw [Finset.sum_singleton, zeroOrd_none hT]
    push_cast
    omega
  · rw [Finset.sum_empty]
    push_cast
    omega

/-- **Every point has a preimage.** -/
theorem exists_ptImage_eq [IsAlgClosed K] (hR : ¬ ∃ c : K, R = RatFunc.C c) (w : Option K) :
    ∃ p, ptImage R p = w := by
  classical
  have hT := fibreFn_nonconst hR w
  have hT0 : fibreFn R w ≠ 0 := fun h0 => hT ⟨0, by rw [h0, map_zero]⟩
  have hsum := sum_zeroSet hT0
  have hdeg := ratFuncDegree_pos_of_not_constant hT
  obtain ⟨p, hp⟩ : (zeroSet (fibreFn R w)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hsum
    omega
  exact ⟨p, (ptImage_eq_iff hR p w).mpr ((mem_zeroSet hT0 p).mp hp)⟩

/-- **The local degrees over a point add up to the degree.** -/
theorem sum_locDeg_fibre [IsAlgClosed K] [DecidableEq K] (hR : ¬ ∃ c : K, R = RatFunc.C c)
    (w : Option K) :
    (∀ p, p ∈ zeroSet (fibreFn R w) ↔ ptImage R p = w) ∧
      ∑ p ∈ zeroSet (fibreFn R w), locDeg (R := R) p = ratFuncDegree R := by
  have hT := fibreFn_nonconst hR w
  have hT0 : fibreFn R w ≠ 0 := fun h0 => hT ⟨0, by rw [h0, map_zero]⟩
  have hmem : ∀ p, p ∈ zeroSet (fibreFn R w) ↔ ptImage R p = w := fun p =>
    (mem_zeroSet hT0 p).trans (ptImage_eq_iff hR p w).symm
  refine ⟨hmem, ?_⟩
  rw [← ratFuncDegree_fibreFn hR w, ← sum_zeroSet hT0]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [locDeg, (hmem p).mp hp]

/-- **A point which is the only preimage of its image has local degree `deg R`.** -/
theorem locDeg_eq_of_unique [IsAlgClosed K] (hR : ¬ ∃ c : K, R = RatFunc.C c) (p : Option K)
    (huniq : ∀ p', ptImage R p' = ptImage R p → p' = p) :
    locDeg (R := R) p = ratFuncDegree R := by
  classical
  obtain ⟨hmem, hsum⟩ := sum_locDeg_fibre hR (ptImage R p)
  have hset : zeroSet (fibreFn R (ptImage R p)) = {p} := by
    ext p'
    rw [hmem, Finset.mem_singleton]
    exact ⟨huniq p', fun h => h ▸ rfl⟩
  rw [hset, Finset.sum_singleton] at hsum
  exact hsum

/-! ### Finite backward-invariant sets -/

/-- **A finite backward-invariant set is permuted.**  Each of its points is the only preimage of
its image, and is periodic. -/
theorem preimage_subset_finite {α : Type*} {f : α → α} (hf : Function.Surjective f) {S : Set α}
    (hS : S.Finite) (hpre : ∀ z, f z ∈ S → z ∈ S) :
    ∀ z ∈ S, f z ∈ S ∧ (∀ z', f z' = f z → z' = z) ∧ ∃ m, 0 < m ∧ f^[m] z = z := by
  have hsub : f ⁻¹' S ⊆ S := fun z hz => hpre z hz
  have hsurj : Set.SurjOn f (f ⁻¹' S) S := fun s _ => by
    obtain ⟨t, rfl⟩ := hf s
    exact ⟨t, by simpa using ‹f t ∈ S›, rfl⟩
  have hcard : S.ncard ≤ (f ⁻¹' S).ncard := Set.ncard_le_ncard_of_injOn
    (fun s => Classical.choose (hf s)) (fun s hs => by
      show f (Classical.choose (hf s)) ∈ S
      rw [Classical.choose_spec (hf s)]; exact hs)
    (fun s _ t _ h => by
      have := congrArg f h
      rwa [Classical.choose_spec (hf s), Classical.choose_spec (hf t)] at this)
    (hS.subset hsub)
  have heq : f ⁻¹' S = S := Set.eq_of_subset_of_ncard_le hsub hcard hS
  have hmaps : Set.MapsTo f S S := fun z hz => by
    have : z ∈ f ⁻¹' S := by rw [heq]; exact hz
    exact this
  have hsurj' : Set.SurjOn f S S := by
    have := hsurj
    rwa [heq] at this
  have hbij : Set.BijOn f S S := (hS.surjOn_iff_bijOn_of_mapsTo hmaps).mp hsurj'
  intro z hz
  refine ⟨hmaps hz, fun z' hz' => ?_, ?_⟩
  · have hz'S : z' ∈ S := hpre z' (hz' ▸ hmaps hz)
    exact hbij.injOn hz'S hz hz'
  · have hiter : ∀ n, f^[n] z ∈ S := fun n => hmaps.iterate n hz
    obtain ⟨i, j, hij, heqij⟩ := hS.exists_lt_map_eq_of_forall_mem hiter
    refine ⟨j - i, by omega, ?_⟩
    have key : ∀ k, k ≤ i → f^[i - k] z = f^[i - k + (j - i)] z := by
      intro k
      induction k with
      | zero => intro _; rw [Nat.sub_zero, show i + (j - i) = j by omega]; exact heqij
      | succ k ih =>
          intro hk
          have h := ih (by omega)
          rw [show i - k = (i - (k + 1)) + 1 by omega, Function.iterate_succ_apply',
            show i - (k + 1) + 1 + (j - i) = (i - (k + 1) + (j - i)) + 1 by omega,
            Function.iterate_succ_apply'] at h
          exact hbij.injOn (hiter _) (hiter _) h
    have := key i le_rfl
    rw [Nat.sub_self, Function.iterate_zero_apply, zero_add] at this
    exact this.symm

/-- **Scaling along a cycle.**  A quantity multiplied by `d` at each step of a cycle vanishes on it
when no power of `d` is one. -/
theorem eq_zero_of_scaling_on_cycle {α M : Type*} [CommRing M] [IsDomain M] {f : α → α}
    (h : α → M) {d : M} (hd : ∀ n : ℕ, 0 < n → d ^ n ≠ 1) {z : α} {m : ℕ} (hm : 0 < m)
    (hz : f^[m] z = z) (hstep : ∀ k, h (f^[k] z) = d * h (f^[k + 1] z)) : h z = 0 := by
  have hpow : ∀ n, h z = d ^ n * h (f^[n] z) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hstep n, pow_succ]; ring
  have h1 := hpow m
  rw [hz] at h1
  have h2 : (d ^ m - 1) * h z = 0 := by rw [sub_mul, ← h1]; ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) (hd m hm)
  · exact h3

/-! ### Connections in the charts -/

/-- The affine connection in the chart at a point. -/
def connAt (a : RatFunc K) (p : Option K) : RatFunc K :=
  connPull (chartMap p) (chartMap_nonconst p) a

/-- The projective connection in the chart at a point. -/
def projAt (γ : RatFunc K) (p : Option K) : RatFunc K :=
  projPull (chartMap p) (chartMap_nonconst p) γ

theorem connAt_some (a : RatFunc K) (z : K) : connAt a (some z) = a :=
  connPull_X a

theorem projAt_some (γ : RatFunc K) (z : K) : projAt γ (some z) = γ :=
  projPull_X γ

theorem connPull_srcRep (hR : ¬ ∃ c : K, R = RatFunc.C c) (p : Option K) (a : RatFunc K) :
    connPull (srcRep R p) (srcRep_nonconst hR p) a
      = connPull (chartMap p) (chartMap_nonconst p) (connPull R hR a) :=
  connPull_comp hR (chartMap_nonconst p) (srcRep_nonconst hR p)
    (ratFuncDeriv_chartMap_ne_zero p) (ratFuncDeriv_ne_zero_of_nonconst' hR) a

theorem projPull_srcRep (hR : ¬ ∃ c : K, R = RatFunc.C c) (p : Option K) (γ : RatFunc K) :
    projPull (srcRep R p) (srcRep_nonconst hR p) γ
      = projPull (chartMap p) (chartMap_nonconst p) (projPull R hR γ) :=
  projPull_comp hR (chartMap_nonconst p) (srcRep_nonconst hR p)
    (ratFuncDeriv_chartMap_ne_zero p) (ratFuncDeriv_ne_zero_of_nonconst' hR) γ

/-- **Transport of affine connections to the charts.** -/
theorem connAt_connPull (hR : ¬ ∃ c : K, R = RatFunc.C c) (a : RatFunc K) (p : Option K) :
    connAt (connPull R hR a) p
      = connPull (locRep hR p) (locRep_nonconst hR p) (connAt a (ptImage R p)) := by
  have h1 := connPull_comp (chartMap_nonconst (ptImage R p)) (srcRep_nonconst hR p)
    (locRep_nonconst hR p) (ratFuncDeriv_ne_zero_of_nonconst' (srcRep_nonconst hR p))
    (ratFuncDeriv_chartMap_ne_zero _) (connAt a (ptImage R p))
  calc connAt (connPull R hR a) p
      = connPull (chartMap p) (chartMap_nonconst p) (connPull R hR (connPull
          (chartMap (ptImage R p)) (chartMap_nonconst _) (connAt a (ptImage R p)))) := by
        rw [connAt, connAt, connPull_chartMap_chartMap]
    _ = connPull (srcRep R p) (srcRep_nonconst hR p) (connPull (chartMap (ptImage R p))
          (chartMap_nonconst _) (connAt a (ptImage R p))) := (connPull_srcRep hR p _).symm
    _ = _ := h1.symm

/-- **Transport of projective connections to the charts.** -/
theorem projAt_projPull (hR : ¬ ∃ c : K, R = RatFunc.C c) (γ : RatFunc K) (p : Option K) :
    projAt (projPull R hR γ) p
      = projPull (locRep hR p) (locRep_nonconst hR p) (projAt γ (ptImage R p)) := by
  have h1 := projPull_comp (chartMap_nonconst (ptImage R p)) (srcRep_nonconst hR p)
    (locRep_nonconst hR p) (ratFuncDeriv_ne_zero_of_nonconst' (srcRep_nonconst hR p))
    (ratFuncDeriv_chartMap_ne_zero _) (projAt γ (ptImage R p))
  calc projAt (projPull R hR γ) p
      = projPull (chartMap p) (chartMap_nonconst p) (projPull R hR (projPull
          (chartMap (ptImage R p)) (chartMap_nonconst _) (projAt γ (ptImage R p)))) := by
        rw [projAt, projAt, projPull_chartMap_chartMap]
    _ = projPull (srcRep R p) (srcRep_nonconst hR p) (projPull (chartMap (ptImage R p))
          (chartMap_nonconst _) (projAt γ (ptImage R p))) := (projPull_srcRep hR p _).symm
    _ = _ := h1.symm

/-- **Residues of affine connections pull back in the charts.** -/
theorem connAt_connPull_res (hR : ¬ ∃ c : K, R = RatFunc.C c) (a : RatFunc K) (p : Option K)
    (ha : -1 ≤ ratOrder (connAt a (ptImage R p)) (sphereCoord (ptImage R p))) :
    -1 ≤ ratOrder (connAt (connPull R hR a) p) (sphereCoord p) ∧
      ratResidue (connAt (connPull R hR a) p) (sphereCoord p) + 1
        = (locDeg (R := R) p : K)
          * (ratResidue (connAt a (ptImage R p)) (sphereCoord (ptImage R p)) + 1) := by
  obtain ⟨hreg, hval, hdeg⟩ := locRep_regular hR p
  rw [← hval] at ha
  have h := ratResidue_connPull (locRep_nonconst hR p) hreg ha
  rw [hdeg, hval] at h
  rw [connAt_connPull hR]
  exact h

/-- **Poles of order at least two of affine connections propagate in the charts.** -/
theorem connAt_connPull_ord (hR : ¬ ∃ c : K, R = RatFunc.C c) (a : RatFunc K) (p : Option K)
    (ha0 : connAt a (ptImage R p) ≠ 0)
    (ha : ratOrder (connAt a (ptImage R p)) (sphereCoord (ptImage R p)) ≤ -2) :
    ratOrder (connAt (connPull R hR a) p) (sphereCoord p)
      = ratOrder (connAt a (ptImage R p)) (sphereCoord (ptImage R p)) * locDeg (R := R) p
        + (locDeg (R := R) p - 1) := by
  obtain ⟨hreg, hval, hdeg⟩ := locRep_regular hR p
  rw [← hval] at ha
  have h := ratOrder_connPull_of_le (locRep_nonconst hR p) hreg ha0 ha
  rw [hdeg, hval] at h
  rw [connAt_connPull hR]
  exact h

/-- **Double-pole coefficients of projective connections pull back in the charts.** -/
theorem projAt_projPull_dpc (hR : ¬ ∃ c : K, R = RatFunc.C c) (γ : RatFunc K) (p : Option K)
    (hγ : -2 ≤ ratOrder (projAt γ (ptImage R p)) (sphereCoord (ptImage R p))) :
    -2 ≤ ratOrder (projAt (projPull R hR γ) p) (sphereCoord p) ∧
      ratDpc (projAt (projPull R hR γ) p) (sphereCoord p)
        = (locDeg (R := R) p : K) ^ 2
            * ratDpc (projAt γ (ptImage R p)) (sphereCoord (ptImage R p))
          + (1 - (locDeg (R := R) p : K) ^ 2) / 2 := by
  obtain ⟨hreg, hval, hdeg⟩ := locRep_regular hR p
  rw [← hval] at hγ
  have h := ratDpc_projPull (locRep_nonconst hR p) hreg hγ
  rw [hdeg, hval] at h
  rw [projAt_projPull hR]
  exact h

/-- **Poles of order at least three of projective connections propagate in the charts.** -/
theorem projAt_projPull_ord (hR : ¬ ∃ c : K, R = RatFunc.C c) (γ : RatFunc K) (p : Option K)
    (hγ0 : projAt γ (ptImage R p) ≠ 0)
    (hγ : ratOrder (projAt γ (ptImage R p)) (sphereCoord (ptImage R p)) ≤ -3) :
    ratOrder (projAt (projPull R hR γ) p) (sphereCoord p)
      = ratOrder (projAt γ (ptImage R p)) (sphereCoord (ptImage R p)) * locDeg (R := R) p
        + 2 * (locDeg (R := R) p - 1) := by
  obtain ⟨hreg, hval, hdeg⟩ := locRep_regular hR p
  rw [← hval] at hγ
  have h := ratOrder_projPull_of_le (locRep_nonconst hR p) hreg hγ0 hγ
  rw [hdeg, hval] at h
  rw [projAt_projPull hR]
  exact h

omit [CharZero K] in
/-- **Only finitely many points see a pole or a zero in the chart.** -/
theorem finite_chart_support (F : Option K → RatFunc K) (a : RatFunc K)
    (hF : ∀ z, F (some z) = a) :
    {p : Option K | ratOrder (F p) (sphereCoord p) ≠ 0}.Finite := by
  have hsub : {p : Option K | ratOrder (F p) (sphereCoord p) ≠ 0}
      ⊆ insert none (some '' {z : K | ratOrder a z ≠ 0}) := by
    intro p hp
    cases p with
    | none => exact Set.mem_insert _ _
    | some z =>
        refine Set.mem_insert_of_mem _ ⟨z, ?_, rfl⟩
        have : ratOrder (F (some z)) z ≠ 0 := hp
        rwa [hF] at this
  refine Set.Finite.subset (Set.Finite.insert _ (Set.Finite.image _ ?_)) hsub
  rcases eq_or_ne a 0 with rfl | ha
  · simp [ratOrder_zero]
  · exact finite_support_ratOrder ha

end

end GaloisForLFunctions.HTGeometry
