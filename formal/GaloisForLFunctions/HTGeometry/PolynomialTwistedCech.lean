import GaloisForLFunctions.HTGeometry.GradedTwistedCech
import GaloisForLFunctions.HTGeometry.LaurentCechVanishing
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Čech cohomology of `𝒪(-e)` on projective space, with free fibre variables

Let `T = K[w_i (i ∈ ι), v_j (j ∈ ν)]`, graded by the degree in the `w`'s (the `v`'s have degree
`0`), and cover `Proj T = ℙ(ι) × 𝔸(ν)` by the `D₊(w_i)`.  For `0 ≤ e < #ι` the augmented Čech
complex of `𝒪(-e)` is exact in every degree; in particular `H^p(𝒪(-e)) = 0` for `p ≥ 1` and the
degree-zero cocycles of `𝒪` are the polynomials in the `v`'s.

The proof embeds every localization `T[w_s⁻¹]` into the Laurent ring `K[ℤ^{ι ⊕ ν}]`; the degree
`-e` fractions become exactly the Laurent polynomials whose monomials have total `w`-degree `-e`,
nonnegative `v`-exponents, and negative `w`-exponents only at indices of `s`.  A Laurent monomial
of `w`-degree `-e > -#ι` has some nonnegative `w`-exponent, and the cone operator of such an index
contracts its component (`monoCech_vanishing`).

* `HTGeometry.laurentEmb`, `HTGeometry.laurentLoc` : the embeddings.
* `HTGeometry.polyTwCech_exactAt` : exactness for `e ≤ p`.
-/

namespace HTGeometry

open MvPolynomial AddMonoidAlgebra GaloisForLFunctions.HTGeometry.BorelWeil

universe u

variable {K : Type u} [Field K] {ι ν : Type}

variable (ι ν) in
/-- The weights: `1` on the projective coordinates, `0` on the fibre coordinates. -/
def projWeight : ι ⊕ ν → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

variable (K ι ν) in
/-- The grading of `T` by the degree in the projective coordinates. -/
abbrev projGrading : ℕ → Submodule K (MvPolynomial (ι ⊕ ν) K) :=
  weightedHomogeneousSubmodule K (projWeight ι ν)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable (K ι ν) in
/-- The projective coordinates. -/
noncomputable def projCoord : ι → MvPolynomial (ι ⊕ ν) K := fun i => X (Sum.inl i)

theorem projCoord_mem (i : ι) : projCoord K ι ν i ∈ projGrading K ι ν 1 :=
  isWeightedHomogeneous_X K (projWeight ι ν) (Sum.inl i)

/-- The weight of an exponent is its total degree in the projective coordinates. -/
theorem weight_projWeight [Fintype ι] [Fintype ν] (b : ι ⊕ ν →₀ ℕ) :
    Finsupp.weight (projWeight ι ν) b = ∑ i, b (Sum.inl i) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_sum_type]
  simp [projWeight]

/-! ## The Laurent ring -/

variable (ι ν) in
/-- Integer exponents. -/
abbrev LaurentExp := ι ⊕ ν →₀ ℤ

variable (K ι ν) in
/-- The Laurent ring `K[ℤ^{ι ⊕ ν}]`. -/
abbrev LaurentRing := AddMonoidAlgebra K (LaurentExp ι ν)

variable (ι ν) in
/-- Natural exponents as integer exponents. -/
noncomputable def castExp : (ι ⊕ ν →₀ ℕ) →+ LaurentExp ι ν :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

theorem castExp_apply (b : ι ⊕ ν →₀ ℕ) (k : ι ⊕ ν) : castExp ι ν b k = (b k : ℤ) := by
  simp [castExp]

theorem castExp_injective : Function.Injective (castExp ι ν) := by
  intro b b' h
  ext k
  have := congrArg (fun a => a k) h
  simp only [castExp_apply] at this
  exact_mod_cast this

variable (K ι ν) in
/-- **The embedding of polynomials into Laurent polynomials.** -/
noncomputable def laurentEmb : MvPolynomial (ι ⊕ ν) K →+* LaurentRing K ι ν :=
  AddMonoidAlgebra.mapDomainRingHom K (castExp ι ν)

theorem laurentEmb_injective : Function.Injective (laurentEmb K ι ν) := by
  intro x y h
  apply AddMonoidAlgebra.ext
  have h' := congrArg AddMonoidAlgebra.coeff h
  simp only [laurentEmb, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain] at h'
  exact Finsupp.mapDomain_injective castExp_injective h'

theorem support_laurentEmb [DecidableEq ι] [DecidableEq ν] (x : MvPolynomial (ι ⊕ ν) K) :
    (laurentEmb K ι ν x).coeff.support = x.support.image (castExp ι ν) := by
  classical
  simp only [laurentEmb, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_support_of_injective castExp_injective _

/-- The exponent vector of `w_s`. -/
noncomputable def sExp (s : Finset ι) : LaurentExp ι ν := ∑ i ∈ s, Finsupp.single (Sum.inl i) 1

theorem sExp_apply_inl [DecidableEq ι] (s : Finset ι) (i : ι) :
    sExp (ν := ν) s (Sum.inl i) = if i ∈ s then 1 else 0 := by
  classical
  rw [sExp, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Sum.inl.injEq]
  exact Finset.sum_ite_eq' s i (fun _ => (1 : ℤ))

theorem sExp_apply_inr [DecidableEq ι] (s : Finset ι) (j : ν) : sExp (ν := ν) s (Sum.inr j) = 0 := by
  simp [sExp, Finsupp.finsetSum_apply]

theorem laurentEmb_monomial (b : ι ⊕ ν →₀ ℕ) (c : K) :
    laurentEmb K ι ν (monomial b c) = AddMonoidAlgebra.single (castExp ι ν b) c := by
  simp only [laurentEmb, AddMonoidAlgebra.mapDomainRingHom_apply, MvPolynomial.monomial,
    AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.mapDomain_single]

theorem castExp_single (k : ι ⊕ ν) (n : ℕ) :
    castExp ι ν (Finsupp.single k n) = Finsupp.single k (n : ℤ) := by
  simp [castExp]

theorem laurentEmb_wProd [DecidableEq ι] (s : Finset ι) :
    laurentEmb K ι ν (wProd (projCoord K ι ν) s) = AddMonoidAlgebra.single (sExp s) 1 := by
  induction s using Finset.induction_on with
  | empty =>
    rw [wProd, Finset.prod_empty, map_one, sExp, Finset.sum_empty, AddMonoidAlgebra.one_def]
  | insert a s ha ih =>
    rw [wProd, Finset.prod_insert ha, map_mul, ← wProd, ih,
      show sExp (ν := ν) (insert a s) = Finsupp.single (Sum.inl a) 1 + sExp s by
        rw [sExp, Finset.sum_insert ha, ← sExp],
      projCoord, MvPolynomial.X, laurentEmb_monomial, castExp_single,
      AddMonoidAlgebra.single_mul_single, one_mul]
    rfl

theorem single_mul_single_neg (a : LaurentExp ι ν) :
    AddMonoidAlgebra.single a (1 : K) * AddMonoidAlgebra.single (-a) 1 = 1 := by
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul, AddMonoidAlgebra.one_def]

theorem isUnit_laurentEmb_wProd [DecidableEq ι] (s : Finset ι) :
    IsUnit (laurentEmb K ι ν (wProd (projCoord K ι ν) s)) := by
  rw [laurentEmb_wProd]
  exact ⟨⟨_, _, single_mul_single_neg _, by rw [mul_comm]; exact single_mul_single_neg _⟩, rfl⟩

/-! ## Embedding the localizations -/

section Loc

variable [DecidableEq ι]

variable (K ι ν) in
/-- **The embedding of `T[w_s⁻¹]` into the Laurent ring.** -/
noncomputable def laurentLoc (s : Finset ι) : LocAt (projCoord K ι ν) s →+* LaurentRing K ι ν :=
  IsLocalization.Away.lift (wProd (projCoord K ι ν) s) (isUnit_laurentEmb_wProd s)

theorem laurentLoc_algebraMap (s : Finset ι) (x : MvPolynomial (ι ⊕ ν) K) :
    laurentLoc K ι ν s (algebraMap _ (LocAt (projCoord K ι ν) s) x) = laurentEmb K ι ν x :=
  IsLocalization.lift_eq _ x

theorem laurentLoc_resLoc {s t : Finset ι} (h : s ⊆ t) (y : LocAt (projCoord K ι ν) s) :
    laurentLoc K ι ν t (resLoc (projCoord K ι ν) h y) = laurentLoc K ι ν s y := by
  have : (laurentLoc K ι ν t).comp (resLoc (projCoord K ι ν) h) = laurentLoc K ι ν s :=
    IsLocalization.ringHom_ext (Submonoid.powers (wProd (projCoord K ι ν) s)) (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, resLoc_algebraMap, laurentLoc_algebraMap])
  exact DFunLike.congr_fun this y

/-- **The Laurent expansion of a fraction.** -/
theorem laurentLoc_frac (s : Finset ι) (m : ℕ) (x : MvPolynomial (ι ⊕ ν) K) :
    laurentLoc K ι ν s (frac (projCoord K ι ν) s m x)
      = laurentEmb K ι ν x * AddMonoidAlgebra.single (-(m • sExp s)) 1 := by
  rw [frac, Localization.mk_eq_mk']
  simp only [laurentLoc, IsLocalization.Away.lift]
  rw [IsLocalization.lift_mk'_spec]
  change laurentEmb K ι ν x = laurentEmb K ι ν (wProd (projCoord K ι ν) s ^ m)
    * (laurentEmb K ι ν x * AddMonoidAlgebra.single (-(m • sExp s)) 1)
  rw [map_pow, laurentEmb_wProd, AddMonoidAlgebra.single_pow, one_pow, mul_left_comm,
    single_mul_single_neg, mul_one]

/-- **The embedding of the localization is injective.** -/
theorem laurentLoc_injective (s : Finset ι) : Function.Injective (laurentLoc K ι ν s) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨⟨x, ⟨_, m, rfl⟩⟩, hxy⟩ :=
    IsLocalization.surj (Submonoid.powers (wProd (projCoord K ι ν) s)) y
  simp only at hxy
  have hx : laurentEmb K ι ν x = 0 := by
    rw [← laurentLoc_algebraMap s x, ← hxy, map_mul, hy, zero_mul]
  have hx0 : x = 0 := (map_eq_zero_iff _ laurentEmb_injective).mp hx
  rw [hx0, map_zero] at hxy
  have hu : IsUnit (algebraMap _ (LocAt (projCoord K ι ν) s) (wProd (projCoord K ι ν) s ^ m)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow m
  exact (hu.mul_left_eq_zero).mp hxy

end Loc

/-! ## Admissible Laurent polynomials -/

section Adm

variable [Fintype ι]

/-- The projective indices at which an exponent is negative. -/
noncomputable def negSupp (a : LaurentExp ι ν) : Finset ι :=
  Finset.univ.filter fun i => a (Sum.inl i) < 0

/-- Nonnegative fibre exponents and projective degree `-e`. -/
def DegAdm (e : ℕ) (a : LaurentExp ι ν) : Prop :=
  (∀ j, 0 ≤ a (Sum.inr j)) ∧ ∑ i, a (Sum.inl i) = -(e : ℤ)

variable (K) in
/-- **The admissible Laurent polynomials**: projective degree `-e`, nonnegative fibre exponents,
negative projective exponents only at indices of `s`. -/
def admSubgroup (s : Finset ι) (e : ℕ) : AddSubgroup (LaurentRing K ι ν) where
  carrier := {f | ∀ a ∈ f.coeff.support, negSupp a ⊆ s ∧ DegAdm e a}
  zero_mem' := by
    intro a ha
    simp at ha
  add_mem' := by
    classical
    intro f g hf hg a ha
    rw [AddMonoidAlgebra.coeff_add] at ha
    rcases Finset.mem_union.mp (Finsupp.support_add ha) with h | h
    exacts [hf a h, hg a h]
  neg_mem' := by
    intro f hf a ha
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.support_neg] at ha
    exact hf a ha

theorem mem_admSubgroup {s : Finset ι} {e : ℕ} {f : LaurentRing K ι ν} :
    f ∈ admSubgroup K s e ↔ ∀ a ∈ f.coeff.support, negSupp a ⊆ s ∧ DegAdm e a := Iff.rfl

omit [Fintype ι] in
theorem shift_apply_inl [DecidableEq ι] (b : ι ⊕ ν →₀ ℕ) (m : ℕ) (s : Finset ι) (k : ι) :
    ((castExp ι ν b + -(m • sExp s) : LaurentExp ι ν)) (Sum.inl k)
      = (b (Sum.inl k) : ℤ) - if k ∈ s then (m : ℤ) else 0 := by
  rw [Finsupp.add_apply, Finsupp.neg_apply, Finsupp.smul_apply, sExp_apply_inl, castExp_apply]
  split_ifs <;> simp [sub_eq_add_neg]

omit [Fintype ι] in
theorem shift_apply_inr [DecidableEq ι] (b : ι ⊕ ν →₀ ℕ) (m : ℕ) (s : Finset ι) (j : ν) :
    ((castExp ι ν b + -(m • sExp s) : LaurentExp ι ν)) (Sum.inr j) = (b (Sum.inr j) : ℤ) := by
  rw [Finsupp.add_apply, Finsupp.neg_apply, Finsupp.smul_apply, sExp_apply_inr, castExp_apply]
  simp

variable [DecidableEq ι] [Fintype ν] [DecidableEq ν]

/-- **Degree `-e` fractions are admissible.** -/
theorem laurentLoc_mem_admSubgroup {s : Finset ι} {e : ℕ} {y : LocAt (projCoord K ι ν) s}
    (hy : y ∈ twPart (projGrading K ι ν) (projCoord K ι ν) s e) :
    laurentLoc K ι ν s y ∈ admSubgroup K s e := by
  refine (AddSubgroup.closure_le ((admSubgroup K s e).comap
    (laurentLoc K ι ν s).toAddMonoidHom)).mpr ?_ hy
  rintro _ ⟨m, i, x, hx, hdeg, rfl⟩
  change laurentLoc K ι ν s (frac (projCoord K ι ν) s m x) ∈ admSubgroup K s e
  rw [laurentLoc_frac, mem_admSubgroup]
  intro a ha
  rw [AddMonoidAlgebra.support_coeff_mul_single _ _ (fun y => by simp), support_laurentEmb,
    Finset.mem_map] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
  have hwt : ∑ k, b (Sum.inl k) = i := by
    rw [← weight_projWeight]
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp hx (MvPolynomial.mem_support_iff.mp hb)
  simp only [addRightEmbedding_apply]
  refine ⟨fun k hk => ?_, fun j => ?_, ?_⟩
  · have hk' := (Finset.mem_filter.mp hk).2
    rw [shift_apply_inl] at hk'
    by_contra hks
    rw [if_neg hks] at hk'
    omega
  · rw [shift_apply_inr]
    exact_mod_cast Nat.zero_le _
  · simp only [shift_apply_inl, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
    have h1 : ((i : ℕ) : ℤ) + e = m * s.card := by exact_mod_cast hdeg
    have h2 : ∑ k, ((b (Sum.inl k) : ℕ) : ℤ) = i := by exact_mod_cast hwt
    linarith

omit [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
theorem castExp_toNatExp {c : LaurentExp ι ν} (hc : ∀ k, 0 ≤ c k) :
    castExp ι ν (Finsupp.mapRange Int.toNat (by simp) c) = c := by
  ext k
  rw [castExp_apply, Finsupp.mapRange_apply, Int.toNat_of_nonneg (hc k)]

omit [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
theorem eq_sum_single (g : LaurentRing K ι ν) :
    g = ∑ c ∈ g.coeff.support, AddMonoidAlgebra.single c (g.coeff c) := by
  apply AddMonoidAlgebra.ext
  rw [AddMonoidAlgebra.coeff_sum]
  simp only [AddMonoidAlgebra.coeff_single]
  exact (Finsupp.sum_single g.coeff).symm

/-- **Every admissible Laurent polynomial is a degree `-e` fraction.** -/
theorem exists_laurentLoc_eq {s : Finset ι} {e : ℕ} {f : LaurentRing K ι ν}
    (hf : f ∈ admSubgroup K s e) :
    ∃ y ∈ twPart (projGrading K ι ν) (projCoord K ι ν) s e, laurentLoc K ι ν s y = f := by
  classical
  by_cases hf0 : f = 0
  · exact ⟨0, zero_mem _, by rw [map_zero, hf0]⟩
  set M₀ : ℕ := ∑ a ∈ f.coeff.support, ∑ k, (a (Sum.inl k)).natAbs with hM₀
  have hbound : ∀ a ∈ f.coeff.support, ∀ k, (a (Sum.inl k)).natAbs ≤ M₀ := by
    intro a ha k
    calc (a (Sum.inl k)).natAbs ≤ ∑ k', (a (Sum.inl k')).natAbs :=
          Finset.single_le_sum (f := fun k' => (a (Sum.inl k')).natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      _ ≤ M₀ := Finset.single_le_sum (f := fun a => ∑ k', (a (Sum.inl k')).natAbs)
          (fun _ _ => Nat.zero_le _) ha
  set g := f * AddMonoidAlgebra.single (M₀ • sExp s) (1 : K) with hg
  have hgsupp : g.coeff.support = f.coeff.support.map (addRightEmbedding (M₀ • sExp s)) :=
    AddMonoidAlgebra.support_coeff_mul_single _ _ (fun y => by simp) _
  have hshift : ∀ a : LaurentExp ι ν, ∀ k : ι,
      ((a + M₀ • sExp s : LaurentExp ι ν)) (Sum.inl k)
        = a (Sum.inl k) + if k ∈ s then (M₀ : ℤ) else 0 := by
    intro a k
    rw [Finsupp.add_apply, Finsupp.smul_apply, sExp_apply_inl]
    split_ifs <;> simp
  have hshift' : ∀ a : LaurentExp ι ν, ∀ j : ν,
      ((a + M₀ • sExp s : LaurentExp ι ν)) (Sum.inr j) = a (Sum.inr j) := by
    intro a j
    rw [Finsupp.add_apply, Finsupp.smul_apply, sExp_apply_inr]
    simp
  have hnonneg : ∀ c ∈ g.coeff.support, ∀ k, 0 ≤ c k := by
    intro c hc
    rw [hgsupp, Finset.mem_map] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    obtain ⟨hneg, hinr, -⟩ := hf a ha
    rintro (k | j)
    · simp only [addRightEmbedding_apply, hshift]
      by_cases hk : k ∈ s
      · rw [if_pos hk]
        have := hbound a ha k
        omega
      · rw [if_neg hk, add_zero]
        by_contra hlt
        exact hk (hneg (Finset.mem_filter.mpr ⟨Finset.mem_univ k, by omega⟩))
    · simp only [addRightEmbedding_apply, hshift']
      exact hinr j
  have hsum : ∀ c ∈ g.coeff.support, ∑ k, c (Sum.inl k) = (M₀ * s.card : ℕ) - (e : ℤ) := by
    intro c hc
    rw [hgsupp, Finset.mem_map] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    obtain ⟨-, -, hdeg⟩ := hf a ha
    simp only [addRightEmbedding_apply, hshift, Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hdeg]
    push_cast
    ring
  have hgne : g ≠ 0 := by
    intro hg0
    apply hf0
    have := congrArg (· * AddMonoidAlgebra.single (-(M₀ • sExp s)) (1 : K)) hg0
    simp only [zero_mul, hg, mul_assoc, single_mul_single_neg, mul_one] at this
    exact this
  obtain ⟨c₀, hc₀⟩ : g.coeff.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty,
      AddMonoidAlgebra.coeff_eq_zero]
    exact hgne
  have he : e ≤ M₀ * s.card := by
    have h1 := hsum c₀ hc₀
    have h2 : 0 ≤ ∑ k, c₀ (Sum.inl k) := Finset.sum_nonneg fun k _ => hnonneg c₀ hc₀ _
    omega
  set i := M₀ * s.card - e with hi
  set x : MvPolynomial (ι ⊕ ν) K := ∑ c ∈ g.coeff.support,
    monomial (Finsupp.mapRange Int.toNat (by simp) c) (g.coeff c) with hx
  have hxmem : x ∈ projGrading K ι ν i := by
    refine Submodule.sum_mem _ fun c hc => ?_
    refine isWeightedHomogeneous_monomial _ _ _ ?_
    rw [weight_projWeight]
    have h1 := hsum c hc
    have h2 : ∑ k, ((Finsupp.mapRange Int.toNat (by simp) c (Sum.inl k) : ℕ) : ℤ)
        = ∑ k, c (Sum.inl k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finsupp.mapRange_apply, Int.toNat_of_nonneg (hnonneg c hc _)]
    have h3 : ((∑ k, Finsupp.mapRange Int.toNat (by simp) c (Sum.inl k) : ℕ) : ℤ) = (i : ℤ) := by
      push_cast
      rw [h2, h1, hi]
      push_cast [he]
      ring
    exact_mod_cast h3
  have hemb : laurentEmb K ι ν x = g := by
    rw [hx, map_sum]
    conv_rhs => rw [eq_sum_single g]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [laurentEmb_monomial, castExp_toNatExp (hnonneg c hc)]
  refine ⟨frac (projCoord K ι ν) s M₀ x, frac_mem_twPart hxmem (by omega), ?_⟩
  rw [laurentLoc_frac, hemb, hg, mul_assoc, single_mul_single_neg, mul_one]

end Adm

/-! ## Exactness -/

namespace FinsetCechDatum

/-- Above the number of members of the cover there are no cochains. -/
theorem exactAt_of_card_lt {T : Type*} [DecidableEq T] [LinearOrder T] [Fintype T]
    (D : FinsetCechDatum T) {p : ℕ} (hp : Fintype.card T < p + 1) : D.ExactAt p := by
  intro c hc _
  refine ⟨0, fun _ _ => rfl, ?_⟩
  funext s
  rw [D.d_zero]
  exact (hc s (ne_of_lt (lt_of_le_of_lt (Finset.card_le_univ s) hp))).symm

end FinsetCechDatum

section Exact

variable [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype ν] [DecidableEq ν]

variable (K ι ν) in
/-- The twisted Čech datum of `T`. -/
noncomputable abbrev polyTwCech (e : ℕ) : FinsetCechDatum ι :=
  twCech (projGrading K ι ν) (projCoord K ι ν) projCoord_mem e

/-- The underlying fraction, as an additive map. -/
noncomputable def twValHom {e : ℕ} (s : Finset ι) :
    (polyTwCech K ι ν e).obj s →+ LocAt (projCoord K ι ν) s :=
  (twPart (projGrading K ι ν) (projCoord K ι ν) s e).subtype

omit [Fintype ι] [LinearOrder ι] [Fintype ν] [DecidableEq ν] in
theorem twVal_eq_twValHom {e : ℕ} {s : Finset ι} (y : (polyTwCech K ι ν e).obj s) :
    twVal projCoord_mem y = twValHom s y := rfl

/-- The Laurent coefficients of a cochain. -/
noncomputable def laurentCoeffs {e : ℕ} (c : (polyTwCech K ι ν e).Cochain) :
    Finset ι → (LaurentExp ι ν →₀ K) :=
  fun I => (laurentLoc K ι ν I (twVal projCoord_mem (c I))).coeff

omit [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
theorem cechSign_intCast (I : Finset ι) (u : ι) :
    (((cechSign I u : ℤ)) : K) = cechSign I u := by
  simp [cechSign]

omit [Fintype ι] [Fintype ν] [DecidableEq ν] in
/-- **The Laurent coefficients intertwine the differentials.** -/
theorem laurentCoeffs_d {e : ℕ} (c : (polyTwCech K ι ν e).Cochain) (t : Finset ι) :
    laurentCoeffs ((polyTwCech K ι ν e).d c) t = monoCechD (laurentCoeffs c) t := by
  have hval : twVal projCoord_mem ((polyTwCech K ι ν e).d c t)
      = ∑ u ∈ t, (cechSign t u : ℤ) •
          resLoc (projCoord K ι ν) (Finset.erase_subset u t) (twVal projCoord_mem (c (t.erase u))) := by
    rw [twVal_eq_twValHom, FinsetCechDatum.d, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_zsmul]
    rfl
  rw [laurentCoeffs, hval, map_sum, AddMonoidAlgebra.coeff_sum, monoCechD]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_zsmul, laurentLoc_resLoc, ← cechSign_intCast (K := K), Int.cast_smul_eq_zsmul]
  rfl

/-- **Čech exactness of `𝒪(-e)` on `ℙ(ι) × 𝔸(ν)` in every degree `p ≥ e`.** -/
theorem polyTwCech_exactAt {e p : ℕ} (hep : e ≤ p) : (polyTwCech K ι ν e).ExactAt p := by
  classical
  by_cases hp : Fintype.card ι < p + 1
  · exact FinsetCechDatum.exactAt_of_card_lt _ hp
  push Not at hp
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  intro c hc hdc
  have hcard : ∀ I : Finset ι, I.card ≠ p + 1 → laurentCoeffs c I = 0 := by
    intro I hI
    simp only [laurentCoeffs]
    rw [show twVal projCoord_mem (c I) = 0 by rw [hc I hI]; rfl, map_zero,
      AddMonoidAlgebra.coeff_zero]
  have hadm : ∀ I, ∀ a ∈ (laurentCoeffs c I).support, negSupp a ⊆ I ∧ DegAdm e a :=
    fun I => laurentLoc_mem_admSubgroup (c I : twPart (projGrading K ι ν) (projCoord K ι ν) I e).2
  have hδ : monoCechD (laurentCoeffs c) = 0 := by
    funext t
    rw [← laurentCoeffs_d, hdc]
    simp only [laurentCoeffs]
    rw [show twVal projCoord_mem ((0 : (polyTwCech K ι ν e).Cochain) t) = 0 from rfl, map_zero,
      AddMonoidAlgebra.coeff_zero]
    rfl
  have hne : ∀ (I : Finset ι) (a : LaurentExp ι ν), a ∈ (laurentCoeffs c I).support →
      negSupp a ≠ Finset.univ := by
    intro I a ha hfull
    obtain ⟨-, -, hsum⟩ := hadm I a ha
    have hneg : ∀ k, a (Sum.inl k) ≤ -1 := by
      intro k
      have hk : k ∈ negSupp a := hfull ▸ Finset.mem_univ k
      have := (Finset.mem_filter.mp hk).2
      omega
    have hle : ∑ k, a (Sum.inl k) ≤ ∑ _k : ι, (-1 : ℤ) := Finset.sum_le_sum fun k _ => hneg k
    rw [Finset.sum_const, Finset.card_univ, hsum] at hle
    simp at hle
    omega
  obtain ⟨η, hηcard, hηchart, hηsupp, hηd⟩ :=
    monoCech_vanishing (supp := negSupp) hcard (fun I a ha => (hadm I a ha).1) hδ hne
  have hηadm : ∀ I, AddMonoidAlgebra.ofCoeff (η I) ∈ admSubgroup K I e := by
    intro I a ha
    obtain ⟨J, hJ⟩ := hηsupp I a ha
    exact ⟨hηchart I a ha, (hadm J a hJ).2⟩
  choose y hy hyeq using fun I => exists_laurentLoc_eq (hηadm I)
  let b : (polyTwCech K ι ν e).Cochain := fun I => ⟨y I, hy I⟩
  have hb : laurentCoeffs b = η := by
    funext I
    change (laurentLoc K ι ν I (y I)).coeff = η I
    rw [hyeq]
  refine ⟨b, fun I hI => ?_, ?_⟩
  · apply twVal_injective projCoord_mem
    apply laurentLoc_injective I
    apply AddMonoidAlgebra.coeff_injective
    change (laurentLoc K ι ν I (y I)).coeff = (laurentLoc K ι ν I 0).coeff
    rw [hyeq, map_zero, hηcard I hI]
    rfl
  · funext t
    apply twVal_injective projCoord_mem
    apply laurentLoc_injective t
    apply AddMonoidAlgebra.coeff_injective
    change laurentCoeffs ((polyTwCech K ι ν e).d b) t = laurentCoeffs c t
    rw [laurentCoeffs_d, hb, hηd]

end Exact

end HTGeometry
