import GaloisForLFunctions.HTGeometry.MonomialValuation
import GaloisForLFunctions.HTGeometry.CohenMacaulayDepth

/-!
# The initial ideal of a weight degeneration, and descent of regularity

For a weight `w` the lowest-weight form of a product is the product of the lowest-weight forms, so
the lowest forms of the elements of an ideal generate an ideal — and, because multiplying a lowest
form by a monomial gives a lowest form, that ideal is already the `K`-span of the forms:

```text
lowestForm_mul     ** the lowest-weight forms multiply **
initialFormSet     the lowest forms of the nonzero elements of an ideal
initialIdeal       the ideal they span, realised directly as their K-span
```

The span being taken over `K` makes the ideal weight-graded, which gives the structural lemma:

```text
exists_lowestForm_eq_of_mem_initialIdeal
    ** a nonzero homogeneous element of the initial ideal is itself an initial form **
```

For weights that are nonpositive the minimal weight of a nonzero polynomial is bounded above by
zero, so subtracting an element of the ideal with the same lowest form can only be repeated finitely
often:

```text
exists_lowestForm_notMem_initialIdeal
    ** every class outside `I` has a representative whose lowest form escapes the initial ideal **
```

and that is exactly what turns regularity of an initial form into regularity of the element:

```text
isRegularOn_of_isRegularOn_lowestForm
    ** in(f) a nonzerodivisor mod in(I) ⟹ f a nonzerodivisor mod I **
```

If `f · g ∈ I` with `g ∉ I`, reduce `g` to a representative `g'` whose lowest form is outside the
initial ideal; then `in(f) · in(g') = in(f g')` lies in the initial ideal, and regularity of `in(f)`
puts `in(g')` there too, a contradiction.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- **The lowest-weight forms multiply.** -/
theorem lowestForm_mul {w : σ → ℤ} {p q : MvPolynomial σ K} (hp : p ≠ 0) (hq : q ≠ 0) :
    lowestForm w (p * q) = lowestForm w p * lowestForm w q := by
  classical
  have hhom := MvPolynomial.IsWeightedHomogeneous.mul
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := w) (minWeight w p) p)
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (w := w) (minWeight w q) q)
  ext e
  by_cases he : Finsupp.weight w e = minWeight w p + minWeight w q
  · rw [coeff_lowestForm_of_weight_eq (by rw [minWeight_mul hp hq]; exact he),
      coeff_mul_eq_of_weight_eq he]
  · rw [coeff_lowestForm_of_weight_ne (by rw [minWeight_mul hp hq]; exact he)]
    by_contra hcon
    exact he (hhom (Ne.symm hcon))

/-- The set of lowest-weight forms of the nonzero elements of an ideal. -/
def initialFormSet (w : σ → ℤ) (I : Ideal (MvPolynomial σ K)) : Set (MvPolynomial σ K) :=
  {v | ∃ f ∈ I, f ≠ 0 ∧ lowestForm w f = v}

theorem lowestForm_mem_initialFormSet {w : σ → ℤ} {I : Ideal (MvPolynomial σ K)}
    {f : MvPolynomial σ K} (hf : f ∈ I) (hf0 : f ≠ 0) :
    lowestForm w f ∈ initialFormSet w I := ⟨f, hf, hf0, rfl⟩

theorem lowestForm_monomial {w : σ → ℤ} {m : σ →₀ ℕ} {a : K} (ha : a ≠ 0) :
    lowestForm w (MvPolynomial.monomial m a) = MvPolynomial.monomial m a := by
  classical
  have hsupp : (MvPolynomial.monomial m a : MvPolynomial σ K).support = {m} := by
    rw [MvPolynomial.support_monomial, if_neg ha]
  have hmin : minWeight w (MvPolynomial.monomial m a : MvPolynomial σ K)
      = Finsupp.weight w m := by
    refine le_antisymm (minWeight_le (by rw [hsupp]; exact Finset.mem_singleton_self m)) ?_
    refine le_minWeight (by simpa using ha) ?_
    intro e he
    rw [hsupp, Finset.mem_singleton] at he
    exact le_of_eq (by rw [he])
  ext e
  by_cases he : Finsupp.weight w e = minWeight w (MvPolynomial.monomial m a : MvPolynomial σ K)
  · rw [coeff_lowestForm_of_weight_eq he]
  · rw [coeff_lowestForm_of_weight_ne he]
    by_contra hcon
    have hmem : e ∈ (MvPolynomial.monomial m a : MvPolynomial σ K).support :=
      MvPolynomial.mem_support_iff.mpr (Ne.symm hcon)
    rw [hsupp, Finset.mem_singleton] at hmem
    exact he (by rw [hmem, hmin])

theorem monomial_mul_mem_initialFormSet {w : σ → ℤ} {I : Ideal (MvPolynomial σ K)}
    {m : σ →₀ ℕ} {a : K} (ha : a ≠ 0) {v : MvPolynomial σ K}
    (hv : v ∈ initialFormSet w I) :
    MvPolynomial.monomial m a * v ∈ initialFormSet w I := by
  obtain ⟨f, hf, hf0, rfl⟩ := hv
  refine ⟨MvPolynomial.monomial m a * f, Ideal.mul_mem_left _ _ hf, ?_, ?_⟩
  · exact mul_ne_zero (by simpa using ha) hf0
  · rw [lowestForm_mul (by simpa using ha) hf0, lowestForm_monomial ha]

theorem monomial_mul_mem_span {w : σ → ℤ} {I : Ideal (MvPolynomial σ K)} {m : σ →₀ ℕ} {a : K}
    {x : MvPolynomial σ K}
    (hx : x ∈ Submodule.span K (initialFormSet w I)) :
    MvPolynomial.monomial m a * x ∈ Submodule.span K (initialFormSet w I) := by
  classical
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  induction hx using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span (monomial_mul_mem_initialFormSet ha hv)
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have hsm : MvPolynomial.monomial m a * (c • y) = c • (MvPolynomial.monomial m a * y) := by
      rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
      ring
    rw [hsm]
    exact Submodule.smul_mem _ _ hy

/-- The ideal of lowest-weight forms: the `K`-span of the initial forms, which is already an
ideal because multiplying an initial form by a monomial gives an initial form. -/
noncomputable def initialIdeal (w : σ → ℤ) (I : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial σ K) where
  carrier := (Submodule.span K (initialFormSet w I) : Submodule K (MvPolynomial σ K))
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  smul_mem' := by
    classical
    intro c x hx
    show c * x ∈ Submodule.span K (initialFormSet w I)
    rw [← MvPolynomial.support_sum_monomial_coeff c, Finset.sum_mul]
    refine Submodule.sum_mem _ fun m _ => ?_
    exact monomial_mul_mem_span hx

theorem mem_initialIdeal_iff {w : σ → ℤ} {I : Ideal (MvPolynomial σ K)} {u : MvPolynomial σ K} :
    u ∈ initialIdeal w I ↔ u ∈ Submodule.span K (initialFormSet w I) := Iff.rfl

theorem lowestForm_mem_initialIdeal {w : σ → ℤ} {I : Ideal (MvPolynomial σ K)}
    {f : MvPolynomial σ K} (hf : f ∈ I) (hf0 : f ≠ 0) :
    lowestForm w f ∈ initialIdeal w I :=
  Submodule.subset_span (lowestForm_mem_initialFormSet hf hf0)

theorem weightedHomogeneousComponent_lowestForm {w : σ → ℤ} (f : MvPolynomial σ K) (d : ℤ) :
    MvPolynomial.weightedHomogeneousComponent w d (lowestForm w f)
      = if d = minWeight w f then lowestForm w f else 0 := by
  classical
  ext e
  rw [MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hd : d = minWeight w f
  · rw [if_pos hd]
    by_cases he : Finsupp.weight w e = d
    · rw [if_pos he]
    · rw [if_neg he, coeff_lowestForm_of_weight_ne (by rw [← hd]; exact he)]
  · rw [if_neg hd]
    by_cases he : Finsupp.weight w e = d
    · rw [if_pos he, coeff_lowestForm_of_weight_ne (by rw [he]; exact hd)]
      simp
    · rw [if_neg he]
      simp

/-- **Every weighted-homogeneous element of the initial ideal is an initial form.**  The `K`-span is
graded by weight, so a homogeneous element is a combination of initial forms of the same weight, and
the same combination of their sources has that element as its own initial form. -/
theorem exists_mem_component_eq {w : σ → ℤ} {I : Ideal (MvPolynomial σ K)} (d : ℤ) :
    ∀ u ∈ Submodule.span K (initialFormSet w I),
      ∃ h ∈ I, (∀ e ∈ h.support, d ≤ Finsupp.weight w e) ∧
        MvPolynomial.weightedHomogeneousComponent w d h
          = MvPolynomial.weightedHomogeneousComponent w d u := by
  classical
  intro u hu
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨f, hf, hf0, rfl⟩ := hv
    by_cases hd : d = minWeight w f
    · refine ⟨f, hf, ?_, ?_⟩
      · intro e he
        rw [hd]
        exact minWeight_le he
      · rw [weightedHomogeneousComponent_lowestForm, if_pos hd, hd]
        rfl
    · exact ⟨0, Ideal.zero_mem _, by simp, by
        rw [weightedHomogeneousComponent_lowestForm, if_neg hd, map_zero]⟩
  | zero => exact ⟨0, Ideal.zero_mem _, by simp, by rw [map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨h₁, h₁I, h₁supp, h₁eq⟩ := hx
    obtain ⟨h₂, h₂I, h₂supp, h₂eq⟩ := hy
    refine ⟨h₁ + h₂, Ideal.add_mem _ h₁I h₂I, ?_, by rw [map_add, map_add, h₁eq, h₂eq]⟩
    intro e he
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
    · exact h₁supp e h
    · exact h₂supp e h
  | smul c x _ hx =>
    obtain ⟨h, hI, hsupp, heq⟩ := hx
    refine ⟨c • h, ?_, ?_, by rw [map_smul, map_smul, heq]⟩
    · rw [MvPolynomial.smul_eq_C_mul]
      exact Ideal.mul_mem_left _ _ hI
    intro e he
    refine hsupp e ?_
    have hsub : (c • h : MvPolynomial σ K).support ⊆ h.support := by
      rw [MvPolynomial.smul_eq_C_mul]
      intro y hy
      by_contra hcon
      rw [MvPolynomial.mem_support_iff] at hy
      exact hy (by rw [MvPolynomial.coeff_C_mul, MvPolynomial.notMem_support_iff.mp hcon,
        mul_zero])
    exact hsub he

/-- **A nonzero homogeneous element of the initial ideal is the initial form of an element of the
ideal itself.** -/
theorem exists_lowestForm_eq_of_mem_initialIdeal {w : σ → ℤ} {I : Ideal (MvPolynomial σ K)}
    {u : MvPolynomial σ K} {d : ℤ} (hu : u ∈ initialIdeal w I) (hu0 : u ≠ 0)
    (hhom : MvPolynomial.IsWeightedHomogeneous w u d) :
    ∃ h ∈ I, h ≠ 0 ∧ minWeight w h = d ∧ lowestForm w h = u := by
  classical
  have hcomp : MvPolynomial.weightedHomogeneousComponent w d u = u := by
    ext e
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases he : Finsupp.weight w e = d
    · rw [if_pos he]
    · rw [if_neg he]
      by_contra hcon
      exact he (hhom (Ne.symm hcon))
  obtain ⟨h, hI, hsupp, heq⟩ := exists_mem_component_eq d u hu
  rw [hcomp] at heq
  have hh0 : h ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at heq
    exact hu0 heq.symm
  have hmin : minWeight w h = d := by
    refine le_antisymm ?_ (le_minWeight hh0 hsupp)
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hu0
    have hce : MvPolynomial.coeff e h ≠ 0 := by
      have h1 : MvPolynomial.coeff e (MvPolynomial.weightedHomogeneousComponent w d h)
          = MvPolynomial.coeff e u := by rw [heq]
      rw [MvPolynomial.coeff_weightedHomogeneousComponent] at h1
      by_cases hwe : Finsupp.weight w e = d
      · rw [if_pos hwe] at h1
        rw [h1]
        exact MvPolynomial.mem_support_iff.mp he
      · rw [if_neg hwe] at h1
        exact absurd h1.symm (MvPolynomial.mem_support_iff.mp he)
    have hwe : Finsupp.weight w e = d := hhom (MvPolynomial.mem_support_iff.mp he)
    calc minWeight w h ≤ Finsupp.weight w e :=
          minWeight_le (MvPolynomial.mem_support_iff.mpr hce)
      _ = d := hwe
  exact ⟨h, hI, hh0, hmin, by rw [lowestForm, hmin, heq]⟩

theorem weight_nonpos {w : σ → ℤ} (hw : ∀ i, w i ≤ 0) (e : σ →₀ ℕ) :
    Finsupp.weight w e ≤ 0 := by
  classical
  rw [Finsupp.weight_apply]
  refine Finset.sum_nonpos fun i _ => ?_
  show (e i) • w i ≤ 0
  rw [nsmul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hw i)

theorem minWeight_nonpos {w : σ → ℤ} (hw : ∀ i, w i ≤ 0) {p : MvPolynomial σ K} (hp : p ≠ 0) :
    minWeight w p ≤ 0 := by
  obtain ⟨e, _, hval⟩ := exists_mem_support_weight_eq_minWeight (w := w) hp
  rw [← hval]
  exact weight_nonpos hw e

/-- **Reduction to an irreducible representative.**  Every class outside `I` has a representative
whose lowest form escapes the initial ideal: as long as it does not, subtracting an element of `I`
with the same lowest form strictly raises the minimal weight, which is bounded above by zero. -/
theorem exists_lowestForm_notMem_initialIdeal {w : σ → ℤ} (hw : ∀ i, w i ≤ 0)
    (I : Ideal (MvPolynomial σ K)) :
    ∀ (n : ℕ) (g : MvPolynomial σ K), g ∉ I → (-minWeight w g).toNat = n →
      ∃ g' : MvPolynomial σ K, g' - g ∈ I ∧ g' ≠ 0 ∧ lowestForm w g' ∉ initialIdeal w I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hg hn
    classical
    have hg0 : g ≠ 0 := fun h => hg (h ▸ Ideal.zero_mem I)
    by_cases hlf : lowestForm w g ∈ initialIdeal w I
    · obtain ⟨h, hI, hh0, hhmin, hheq⟩ := exists_lowestForm_eq_of_mem_initialIdeal hlf
        (lowestForm_ne_zero hg0)
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      have hg2 : g - h ∉ I := by
        intro hcon
        exact hg (by simpa using Ideal.add_mem I hcon hI)
      have hg20 : g - h ≠ 0 := fun hz => hg2 (hz ▸ Ideal.zero_mem I)
      have hcoeff : ∀ e : σ →₀ ℕ, Finsupp.weight w e = minWeight w g →
          MvPolynomial.coeff e (g - h) = 0 := by
        intro e he
        have h1 : MvPolynomial.coeff e g = MvPolynomial.coeff e (lowestForm w g) :=
          (coeff_lowestForm_of_weight_eq he).symm
        have h2 : MvPolynomial.coeff e h = MvPolynomial.coeff e (lowestForm w h) :=
          (coeff_lowestForm_of_weight_eq (by rw [hhmin]; exact he)).symm
        rw [MvPolynomial.coeff_sub, h1, h2, hheq, sub_self]
      have hge : minWeight w g ≤ minWeight w (g - h) := by
        refine le_minWeight hg20 fun e he => ?_
        rcases Finset.mem_union.mp (MvPolynomial.support_sub _ _ _ he) with hmem | hmem
        · exact minWeight_le hmem
        · rw [← hhmin]; exact minWeight_le hmem
      have hne : minWeight w (g - h) ≠ minWeight w g := by
        intro hcon
        obtain ⟨e, hemem, heval⟩ := exists_mem_support_weight_eq_minWeight (w := w) hg20
        exact (MvPolynomial.mem_support_iff.mp hemem) (hcoeff e (by rw [heval, hcon]))
      have hlt : (-minWeight w (g - h)).toNat < n := by
        have h1 := minWeight_nonpos hw hg0
        have h2 := minWeight_nonpos hw hg20
        omega
      obtain ⟨g', hg'sub, hg'0, hg'lf⟩ := ih _ hlt (g - h) hg2 rfl
      refine ⟨g', ?_, hg'0, hg'lf⟩
      have hsum := Ideal.add_mem I hg'sub hI
      have hrw : g' - (g - h) + h = g' - g + (2 * h) := by ring
      have hmem2 : g' - g + (2 * h) ∈ I := hrw ▸ hsum
      have : g' - g = (g' - g + 2 * h) - 2 * h := by ring
      rw [this]
      exact Ideal.sub_mem I hmem2 (Ideal.mul_mem_left _ _ hI)
    · exact ⟨g, by simp, hg0, hlf⟩

/-- **Regularity descends from the initial form.**  If the lowest form of `f` is a nonzerodivisor
modulo the initial ideal, then `f` is a nonzerodivisor modulo the ideal itself. -/
theorem forall_mem_of_isRegularOn_lowestForm {w : σ → ℤ} (hw : ∀ i, w i ≤ 0)
    {I : Ideal (MvPolynomial σ K)} {f : MvPolynomial σ K} (hf0 : f ≠ 0)
    (hreg : ∀ v : MvPolynomial σ K, lowestForm w f * v ∈ initialIdeal w I → v ∈ initialIdeal w I) :
    ∀ g : MvPolynomial σ K, f * g ∈ I → g ∈ I := by
  intro g hfg
  by_contra hg
  obtain ⟨g', hg'sub, hg'0, hg'lf⟩ :=
    exists_lowestForm_notMem_initialIdeal hw I _ g hg rfl
  have hfg' : f * g' ∈ I := by
    have : f * g' = f * g + f * (g' - g) := by ring
    rw [this]
    exact Ideal.add_mem I hfg (Ideal.mul_mem_left _ _ hg'sub)
  have hne : f * g' ≠ 0 := mul_ne_zero hf0 hg'0
  have hmem : lowestForm w f * lowestForm w g' ∈ initialIdeal w I := by
    rw [← lowestForm_mul hf0 hg'0]
    exact lowestForm_mem_initialIdeal hfg' hne
  exact hg'lf (hreg _ hmem)

theorem isRegularOn_of_forall_mem {R : Type*} [CommRing R] {J : Ideal R} {x : R}
    (h : ∀ y : R, x * y ∈ J → y ∈ J) : IsRegularOn J x := by
  rw [IsRegularOn, mem_nonZeroDivisors_iff]
  have main : ∀ z : R ⧸ J, z * (Ideal.Quotient.mk J x) = 0 → z = 0 := by
    intro z hz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h y (by rwa [mul_comm]))
  exact ⟨fun z hz => main z (by rw [mul_comm]; exact hz), main⟩

theorem forall_mem_of_isRegularOn {R : Type*} [CommRing R] {J : Ideal R} {x : R}
    (h : IsRegularOn J x) : ∀ y : R, x * y ∈ J → y ∈ J := by
  rw [IsRegularOn, mem_nonZeroDivisors_iff] at h
  intro y hy
  have hz : (Ideal.Quotient.mk J y) * (Ideal.Quotient.mk J x) = 0 := by
    rw [← map_mul, mul_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact hy
  exact Ideal.Quotient.eq_zero_iff_mem.mp (h.2 _ hz)

/-- **Regularity descends along the degeneration.**  If the lowest form of `f` is a nonzerodivisor
modulo the initial ideal of `I`, then `f` is a nonzerodivisor modulo `I`. -/
theorem isRegularOn_of_isRegularOn_lowestForm {w : σ → ℤ} (hw : ∀ i, w i ≤ 0)
    {I : Ideal (MvPolynomial σ K)} {f : MvPolynomial σ K} (hf0 : f ≠ 0)
    (hreg : IsRegularOn (initialIdeal w I) (lowestForm w f)) :
    IsRegularOn I f :=
  isRegularOn_of_forall_mem
    (forall_mem_of_isRegularOn_lowestForm hw hf0 (forall_mem_of_isRegularOn hreg))

end GaloisForLFunctions.HTGeometry
