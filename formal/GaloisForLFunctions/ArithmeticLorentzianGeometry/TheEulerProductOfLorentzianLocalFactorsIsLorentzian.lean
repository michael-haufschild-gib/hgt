import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheLorentzianClassIsClosedUnderNonnegativeSubstitution
import GaloisForLFunctions.ArithmeticLorentzianGeometry.LocalFactorsAndTheEulerProductClosure

/-!
# The Euler product of Lorentzian local factors is Lorentzian

Products preserve the Lorentzian property where sums do not. The closure runs in two steps.

* **Disjoint variables** (`IsLorentzianPolynomial.mul_of_supportedIn`): if `p` and `q` are
  Lorentzian and involve complementary sets of variables, `p q` is Lorentzian. The support is a
  product of M-convex sets, and every quadratic derivative of `p q` is a single product
  `∂^{α'} p · ∂^{α''} q` of total degree two: a nonnegative multiple of a quadratic derivative of
  one factor, or the product of two nonnegative linear forms (`symmProd`).
* **Renaming** (`isLorentzianPolynomial_rename`): an injective change of variable names preserves
  the property; the local factors `f_p` placed in the disjoint variables `x_{p,·}` give the
  Lorentzian polynomial `disjointProd s f = ∏_{p ∈ s} f_p(x_{p,·})`
  (`isLorentzianPolynomial_disjointProd`).
* **Merging** is a nonnegative substitution `x_{p,i} ↦ x_i`, so the Euler product
  `∏_{p ∈ s} f_p` of Lorentzian local factors is mixed-Lorentzian (`isMixedLorentzian_prod`), and
  so is its composition with any nonnegative substitution (`isMixedLorentzian_prod_subst`): its
  Hessian has one positive square at every nonnegative point and it is strongly log-concave.
* For linear local factors this removes the positivity hypothesis on the local factors from the
  Euler product closure of `LocalFactorsAndTheEulerProductClosure`
  (`isLorentzian_eulerHessian_of_nonneg`).
-/

noncomputable section

open Matrix Finset MvPolynomial
open scoped Nat

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- `p` involves only the variables in `V`. -/
def SupportedIn (V : σ → Prop) (p : MvPolynomial σ ℝ) : Prop :=
  ∀ β, coeff β p ≠ 0 → ∀ x, ¬ V x → β x = 0

/-! ### Products in complementary variables -/

section Disjoint

variable {V : σ → Prop} [DecidablePred V]

omit [Fintype σ] in
theorem coeff_mul_of_supportedIn {p q : MvPolynomial σ ℝ} (hp : SupportedIn V p)
    (hq : SupportedIn (fun x => ¬ V x) q) (β : σ →₀ ℕ) :
    coeff β (p * q) = coeff (β.filter V) p * coeff (β.filter fun x => ¬ V x) q := by
  rw [coeff_mul]
  refine Finset.sum_eq_single (β.filter V, β.filter fun x => ¬ V x) (fun x hx hne => ?_)
    (fun h => absurd (mem_antidiagonal.mpr (Finsupp.filter_add_filter_not _ _)) h)
  by_contra h0
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h0
  have hsum := mem_antidiagonal.mp hx
  apply hne
  refine Prod.ext (Finsupp.ext fun a => ?_) (Finsupp.ext fun a => ?_)
  · rw [Finsupp.filter_apply, ← hsum, Finsupp.add_apply]
    split_ifs with ha
    · rw [hq _ h2 a (not_not.mpr ha), add_zero]
    · exact hp _ h1 a ha
  · rw [Finsupp.filter_apply, ← hsum, Finsupp.add_apply]
    split_ifs with ha
    · exact hq _ h2 a (not_not.mpr ha)
    · rw [hp _ h1 a ha, zero_add]

omit [DecidableEq σ] in
theorem mfact_filter_mul (β : σ →₀ ℕ) :
    mfact (β.filter V) * mfact (β.filter fun x => ¬ V x) = mfact β := by
  rw [mfact_eq_prod, mfact_eq_prod, mfact_eq_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  simp only [Finsupp.filter_apply]
  split_ifs <;> simp

omit [Fintype σ] [DecidableEq σ] in
theorem degree_filter_add (β : σ →₀ ℕ) :
    Finsupp.degree (β.filter V) + Finsupp.degree (β.filter fun x => ¬ V x) =
      Finsupp.degree β := by
  rw [← map_add, Finsupp.filter_add_filter_not]

omit [Fintype σ] in
theorem filter_exchange_of {W : σ → Prop} [DecidablePred W] (α : σ →₀ ℕ) {l j : σ} (hl : W l)
    (hj : W j) : (α - Finsupp.single l 1 + Finsupp.single j 1).filter W =
      α.filter W - Finsupp.single l 1 + Finsupp.single j 1 := by
  ext a
  simp only [Finsupp.filter_apply, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs <;> subst_vars <;> first | omega | (exfalso; tauto)

omit [Fintype σ] in
theorem filter_exchange_of_not {W : σ → Prop} [DecidablePred W] (α : σ →₀ ℕ) {l j : σ}
    (hl : ¬ W l) (hj : ¬ W j) :
    (α - Finsupp.single l 1 + Finsupp.single j 1).filter W = α.filter W := by
  ext a
  simp only [Finsupp.filter_apply, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs <;> subst_vars <;> first | omega | (exfalso; tauto)

omit [DecidableEq σ] in
theorem IsHyperbolic.of_entries_eq_zero {Q : Matrix σ σ ℝ} (h : ∀ j k, Q j k = 0) :
    IsHyperbolic Q := by
  intro u v hu
  rw [qf_eq_sum] at hu
  simp [h] at hu

/-- **Products in complementary variables**: if `p`, `q` are Lorentzian and involve
complementary sets of variables, then `p q` is Lorentzian. -/
theorem IsLorentzianPolynomial.mul_of_supportedIn {d e : ℕ} {p q : MvPolynomial σ ℝ}
    (hp : IsLorentzianPolynomial d p) (hq : IsLorentzianPolynomial e q)
    (hpV : SupportedIn V p) (hqV : SupportedIn (fun x => ¬ V x) q) :
    IsLorentzianPolynomial (d + e) (p * q) := by
  have hc := coeff_mul_of_supportedIn hpV hqV
  -- the derivative values `∂^β = β! c_β` of the two factors
  set Dp : (σ →₀ ℕ) → ℝ := fun β => mfact β * coeff β p
  set Dq : (σ →₀ ℕ) → ℝ := fun β => mfact β * coeff β q
  have hD : ∀ β, mfact β * coeff β (p * q) =
      Dp (β.filter V) * Dq (β.filter fun x => ¬ V x) := fun β => by
    rw [hc, ← mfact_filter_mul (V := V) β]; simp only [Dp, Dq]; ring
  have hDp0 : ∀ β, 0 ≤ Dp β := fun β => mul_nonneg (mfact_pos β).le (hp.1 β)
  have hDq0 : ∀ β, 0 ≤ Dq β := fun β => mul_nonneg (mfact_pos β).le (hq.1 β)
  have hDpd : ∀ β, Finsupp.degree β ≠ d → Dp β = 0 := fun β hβ => by
    simp only [Dp]; rw [show coeff β p = 0 by by_contra h; exact hβ (hp.2.1 β h), mul_zero]
  have hDqd : ∀ β, Finsupp.degree β ≠ e → Dq β = 0 := fun β hβ => by
    simp only [Dq]; rw [show coeff β q = 0 by by_contra h; exact hβ (hq.2.1 β h), mul_zero]
  have hDpV : ∀ β x, ¬ V x → β x ≠ 0 → Dp β = 0 := fun β x hx hβ => by
    simp only [Dp]; rw [show coeff β p = 0 by by_contra h; exact hβ (hpV β h x hx), mul_zero]
  have hDqV : ∀ β x, V x → β x ≠ 0 → Dq β = 0 := fun β x hx hβ => by
    simp only [Dq]
    rw [show coeff β q = 0 by by_contra h; exact hβ (hqV β h x (not_not.mpr hx)), mul_zero]
  refine ⟨fun β => by show 0 ≤ coeff β (p * q); rw [hc]; exact mul_nonneg (hp.1 _) (hq.1 _),
    fun β hβ => ?_, ?_, fun α hα => ?_⟩
  · change coeff β (p * q) ≠ 0 at hβ
    rw [hc] at hβ
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hβ
    rw [← degree_filter_add (V := V) β, hp.2.1 _ h1, hq.2.1 _ h2]
  · -- the support is a product of M-convex sets
    intro α hα β hβ l hlt
    simp only [Set.mem_setOf_eq, hc] at hα hβ ⊢
    obtain ⟨hα1, hα2⟩ := mul_ne_zero_iff.mp hα
    obtain ⟨hβ1, hβ2⟩ := mul_ne_zero_iff.mp hβ
    by_cases hl : V l
    · obtain ⟨j, hj, hmem⟩ := hp.2.2.1 _ hα1 _ hβ1 l
        (by simp only [Finsupp.filter_apply, if_pos hl]; exact hlt)
      have hjV : V j := by
        by_contra h; simp [h] at hj
      refine ⟨j, by simpa [Finsupp.filter_apply, hjV] using hj, ?_⟩
      rw [filter_exchange_of α hl hjV,
        filter_exchange_of_not (W := fun x => ¬ V x) α (not_not.mpr hl) (not_not.mpr hjV)]
      exact mul_ne_zero hmem hα2
    · obtain ⟨j, hj, hmem⟩ := hq.2.2.1 _ hα2 _ hβ2 l
        (by simp only [Finsupp.filter_apply, if_pos hl]; exact hlt)
      have hjV : ¬ V j := by
        by_contra h; simp [h] at hj
      refine ⟨j, by simpa [Finsupp.filter_apply, hjV] using hj, ?_⟩
      rw [filter_exchange_of_not α hl hjV, filter_exchange_of (W := fun x => ¬ V x) α hl hjV]
      exact mul_ne_zero hα1 hmem
  · -- each quadratic derivative is a single product of total degree two
    have hentry : ∀ j k, quadDeriv (fun β => coeff β (p * q)) α j k =
        Dp (α.filter V + (Finsupp.single j 1).filter V + (Finsupp.single k 1).filter V) *
          Dq ((α.filter fun x => ¬ V x) + (Finsupp.single j 1).filter (fun x => ¬ V x) +
            (Finsupp.single k 1).filter fun x => ¬ V x) := fun j k => by
      rw [← Finsupp.filter_add, ← Finsupp.filter_add, ← Finsupp.filter_add,
        ← Finsupp.filter_add]
      exact hD _
    have hab := degree_filter_add (V := V) α
    set αV := α.filter V
    set αW := α.filter fun x => ¬ V x
    have hsingle : ∀ (β : σ →₀ ℕ) j, (β + Finsupp.single j 1 : σ →₀ ℕ) j ≠ 0 := fun β j => by
      simp
    have hsingle2 : ∀ (β : σ →₀ ℕ) j k,
        (β + Finsupp.single j 1 + Finsupp.single k 1 : σ →₀ ℕ) j ≠ 0 := fun β j k => by
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega
    have hsingle3 : ∀ (β : σ →₀ ℕ) j k,
        (β + Finsupp.single j 1 + Finsupp.single k 1 : σ →₀ ℕ) k ≠ 0 := fun β j k => by
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega
    have hdeg1 : ∀ (β : σ →₀ ℕ) j, Finsupp.degree (β + Finsupp.single j 1) =
        Finsupp.degree β + 1 := fun β j => degree_add_single β j
    -- the filters of a unit vector
    have hfV : ∀ j, V j → (Finsupp.single j 1).filter V = Finsupp.single j 1 ∧
        (Finsupp.single j 1).filter (fun x => ¬ V x) = 0 := fun j hj =>
      ⟨Finsupp.filter_single_of_pos (p := V) hj,
        Finsupp.filter_single_of_neg (p := fun x => ¬ V x) (not_not.mpr hj)⟩
    have hfW : ∀ j, ¬ V j → (Finsupp.single j 1).filter V = 0 ∧
        (Finsupp.single j 1).filter (fun x => ¬ V x) = Finsupp.single j 1 := fun j hj =>
      ⟨Finsupp.filter_single_of_neg (p := V) hj,
        Finsupp.filter_single_of_pos (p := fun x => ¬ V x) hj⟩
    rcases (show Finsupp.degree αV + 2 = d ∨ Finsupp.degree αW + 2 = e ∨
        (Finsupp.degree αV + 1 = d ∧ Finsupp.degree αW + 1 = e) ∨ d < Finsupp.degree αV ∨
        e < Finsupp.degree αW by omega) with hA | hB | ⟨hC1, hC2⟩ | hD1 | hD2
    · -- a quadratic derivative of `p`, times a value of `q`
      have e1 : quadDeriv (fun β => coeff β (p * q)) α =
          Dq αW • quadDeriv (fun β => coeff β p) αV := by
        ext j k
        rw [hentry, Matrix.smul_apply, smul_eq_mul]
        simp only [quadDeriv, Matrix.of_apply]
        by_cases hj : V j <;> by_cases hk : V k
        · rw [(hfV j hj).1, (hfV k hk).1, (hfV j hj).2, (hfV k hk).2, add_zero, add_zero]
          simp only [Dp]; ring
        · rw [(hfV j hj).1, (hfW k hk).1, add_zero, hDpd _ (by rw [hdeg1]; omega), zero_mul]
          have := hDpV _ k hk (hsingle3 αV j k)
          simp only [Dp] at this; rw [this, mul_zero]
        · rw [(hfW j hj).1, (hfV k hk).1, add_zero, hDpd _ (by rw [hdeg1]; omega), zero_mul]
          have := hDpV _ j hj (hsingle2 αV j k)
          simp only [Dp] at this; rw [this, mul_zero]
        · rw [(hfW j hj).1, (hfW k hk).1, add_zero, add_zero, hDpd _ (by omega), zero_mul]
          have := hDpV _ j hj (hsingle2 αV j k)
          simp only [Dp] at this; rw [this, mul_zero]
      rw [e1]
      exact (hp.2.2.2 αV hA).smul_nonneg (hDq0 _)
    · -- a value of `p`, times a quadratic derivative of `q`
      have e1 : quadDeriv (fun β => coeff β (p * q)) α =
          Dp αV • quadDeriv (fun β => coeff β q) αW := by
        ext j k
        rw [hentry, Matrix.smul_apply, smul_eq_mul]
        simp only [quadDeriv, Matrix.of_apply]
        by_cases hj : V j <;> by_cases hk : V k
        · rw [(hfV j hj).2, (hfV k hk).2, add_zero, add_zero, hDqd _ (by omega), mul_zero]
          have := hDqV _ j hj (hsingle2 αW j k)
          simp only [Dq] at this; rw [this, mul_zero]
        · rw [(hfV j hj).2, (hfW k hk).2, add_zero, hDqd _ (by rw [hdeg1]; omega), mul_zero]
          have := hDqV _ j hj (hsingle2 αW j k)
          simp only [Dq] at this; rw [this, mul_zero]
        · rw [(hfW j hj).2, (hfV k hk).2, add_zero, hDqd _ (by rw [hdeg1]; omega), mul_zero]
          have := hDqV _ k hk (hsingle3 αW j k)
          simp only [Dq] at this; rw [this, mul_zero]
        · rw [(hfW j hj).1, (hfW k hk).1, (hfW j hj).2, (hfW k hk).2, add_zero, add_zero]
      rw [e1]
      exact (hq.2.2.2 αW hB).smul_nonneg (hDp0 _)
    · -- the product of two nonnegative linear forms
      set g : σ → ℝ := fun j => Dp (αV + Finsupp.single j 1)
      set h : σ → ℝ := fun j => Dq (αW + Finsupp.single j 1)
      have hgV : ∀ j, ¬ V j → g j = 0 := fun j hj => hDpV _ j hj (hsingle αV j)
      have hhV : ∀ j, V j → h j = 0 := fun j hj => hDqV _ j hj (hsingle αW j)
      have e1 : quadDeriv (fun β => coeff β (p * q)) α = symmProd g h := by
        ext j k
        rw [hentry]
        simp only [symmProd, Matrix.add_apply, vecMulVec_apply]
        by_cases hj : V j <;> by_cases hk : V k
        · rw [(hfV j hj).1, (hfV k hk).1, hDpd _ (by rw [hdeg1, hdeg1]; omega), zero_mul,
            hhV j hj, hhV k hk]
          ring
        · rw [(hfV j hj).1, (hfW k hk).1, (hfV j hj).2, (hfW k hk).2, add_zero, add_zero,
            hhV j hj]
          ring
        · rw [(hfW j hj).1, (hfV k hk).1, (hfW j hj).2, (hfV k hk).2, add_zero, add_zero,
            hgV j hj]
          ring
        · rw [(hfW j hj).2, (hfW k hk).2, hDqd _ (by rw [hdeg1, hdeg1]; omega), mul_zero,
            hgV j hj, hgV k hk]
          ring
      rw [e1]
      exact (isLorentzian_symmProd (fun j => hDp0 _) (fun j => hDq0 _)).2.2
    · refine IsHyperbolic.of_entries_eq_zero fun j k => ?_
      rw [hentry, hDpd _ ?_, zero_mul]
      rw [map_add, map_add]
      omega
    · refine IsHyperbolic.of_entries_eq_zero fun j k => ?_
      rw [hentry, hDqd _ ?_, mul_zero]
      rw [map_add, map_add]
      omega

end Disjoint

/-! ### Renaming variables -/

section Rename

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → σ}

omit [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] in
theorem coeff_rename_of_not {f : MvPolynomial ι ℝ} {β : σ →₀ ℕ}
    (hβ : ∃ x, x ∉ Set.range e ∧ β x ≠ 0) : coeff β (rename e f) = 0 :=
  coeff_rename_eq_zero e f β fun u hu => by
    obtain ⟨x, hx, hβx⟩ := hβ
    exact absurd (by rw [← hu]; exact Finsupp.mapDomain_notin_range u x hx) hβx

omit [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] in
theorem mfact_mapDomain (he : Function.Injective e) (u : ι →₀ ℕ) :
    mfact (u.mapDomain e) = mfact u := by
  unfold mfact
  rw [Finsupp.prod_mapDomain_index_inj he]

omit [Fintype σ] [Fintype ι] in
theorem mapDomain_exchange (he : Function.Injective e) (u : ι →₀ ℕ) (l j : ι) :
    u.mapDomain e - Finsupp.single (e l) 1 + Finsupp.single (e j) 1 =
      (u - Finsupp.single l 1 + Finsupp.single j 1).mapDomain e := by
  ext x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.mapDomain_apply he,
      Finsupp.single_apply, he.eq_iff]
  · have h1 : e l ≠ x := fun h => hx ⟨l, h⟩
    have h2 : e j ≠ x := fun h => hx ⟨j, h⟩
    simp [Finsupp.mapDomain_notin_range _ _ hx, h1, h2]

/-- The renaming matrix `R_{i x} = [e i = x]`: `(R u)_i = u_{e i}`. -/
def renameMatrix (e : ι → σ) : Matrix ι σ ℝ := fun i x => if e i = x then 1 else 0

/-- **Renaming**: an injective change of variable names preserves the Lorentzian property. -/
theorem isLorentzianPolynomial_rename (he : Function.Injective e) {d : ℕ}
    {f : MvPolynomial ι ℝ} (hf : IsLorentzianPolynomial d f) :
    IsLorentzianPolynomial d (rename e f) := by
  have hcases : ∀ β : σ →₀ ℕ, (∃ u, u.mapDomain e = β ∧ coeff β (rename e f) = coeff u f) ∨
      coeff β (rename e f) = 0 := fun β => by
    by_cases h : ∃ u : ι →₀ ℕ, u.mapDomain e = β
    · obtain ⟨u, rfl⟩ := h; exact Or.inl ⟨u, rfl, coeff_rename_mapDomain e he f u⟩
    · exact Or.inr (coeff_rename_eq_zero e f β fun u hu => absurd ⟨u, hu⟩ h)
  refine ⟨fun β => ?_, fun β hβ => ?_, ?_, fun α hα => ?_⟩
  · show 0 ≤ coeff β (rename e f)
    rcases hcases β with ⟨u, -, h⟩ | h
    · rw [h]; exact hf.1 u
    · rw [h]
  · change coeff β (rename e f) ≠ 0 at hβ
    rcases hcases β with ⟨u, rfl, h⟩ | h
    · rw [h] at hβ
      rw [Finsupp.degree_mapDomain]; exact hf.2.1 u hβ
    · exact absurd h hβ
  · intro α hα β hβ l hlt
    change coeff α (rename e f) ≠ 0 at hα
    change coeff β (rename e f) ≠ 0 at hβ
    obtain ⟨α', rfl, hα'⟩ := (hcases α).resolve_right hα
    obtain ⟨β', rfl, hβ'⟩ := (hcases β).resolve_right hβ
    rw [hα'] at hα
    rw [hβ'] at hβ
    -- the exchanged variable is a renamed one
    obtain ⟨l', rfl⟩ : l ∈ Set.range e := by
      by_contra hl
      rw [Finsupp.mapDomain_notin_range α' l hl] at hlt
      exact Nat.not_lt_zero _ hlt
    rw [Finsupp.mapDomain_apply he, Finsupp.mapDomain_apply he] at hlt
    obtain ⟨j', hj', hmem⟩ := hf.2.2.1 α' hα β' hβ l' hlt
    refine ⟨e j', by rwa [Finsupp.mapDomain_apply he, Finsupp.mapDomain_apply he], ?_⟩
    show coeff _ (rename e f) ≠ 0
    rw [mapDomain_exchange he, coeff_rename_mapDomain e he]
    exact hmem
  · -- the quadratic derivatives are pulled back along the renaming
    have hoff : ∀ x y, (x ∉ Set.range e ∨ y ∉ Set.range e) →
        quadDeriv (fun β => coeff β (rename e f)) α x y = 0 := fun x y hxy => by
      simp only [quadDeriv, Matrix.of_apply]
      rcases hxy with hx | hy
      · rw [coeff_rename_of_not ⟨x, hx, by simp⟩, mul_zero]
      · rw [coeff_rename_of_not ⟨y, hy, by simp⟩, mul_zero]
    by_cases hα' : ∃ α' : ι →₀ ℕ, α'.mapDomain e = α
    · obtain ⟨α', rfl⟩ := hα'
      have e1 : quadDeriv (fun β => coeff β (rename e f)) (α'.mapDomain e) =
          (renameMatrix e)ᵀ * quadDeriv (fun β => coeff β f) α' * renameMatrix e := by
        ext x y
        simp only [Matrix.mul_apply, transpose_apply, renameMatrix]
        by_cases hx : x ∈ Set.range e
        · by_cases hy : y ∈ Set.range e
          · obtain ⟨a, rfl⟩ := hx
            obtain ⟨b, rfl⟩ := hy
            rw [Fintype.sum_eq_single b fun l hl => by rw [if_neg (he.ne hl), mul_zero],
              if_pos rfl, mul_one,
              Fintype.sum_eq_single a fun i hi => by rw [if_neg (he.ne hi), zero_mul],
              if_pos rfl, one_mul]
            simp only [quadDeriv, Matrix.of_apply]
            rw [show α'.mapDomain e + Finsupp.single (e a) 1 + Finsupp.single (e b) 1 =
                (α' + Finsupp.single a 1 + Finsupp.single b 1).mapDomain e by
              simp [Finsupp.mapDomain_add, Finsupp.mapDomain_single],
              mfact_mapDomain he, coeff_rename_mapDomain e he]
          · have hy' : ∀ i, e i ≠ y := fun i h => hy ⟨i, h⟩
            rw [hoff x y (Or.inr hy)]
            simp [hy']
        · have hx' : ∀ i, e i ≠ x := fun i h => hx ⟨i, h⟩
          rw [hoff x y (Or.inl hx)]
          simp [hx']
      rw [e1]
      exact (hf.2.2.2 α' (by rwa [Finsupp.degree_mapDomain] at hα)).pullback _
    · -- off the image of the renaming every quadratic derivative vanishes
      obtain ⟨x₀, hx₀, hαx₀⟩ : ∃ x, x ∉ Set.range e ∧ α x ≠ 0 := by
        by_contra h
        push Not at h
        exact hα' ⟨Finsupp.comapDomain e α he.injOn,
          Finsupp.mapDomain_comapDomain e he α fun x hx => by
            by_contra hx'
            exact (Finsupp.mem_support_iff.mp hx) (h x hx')⟩
      refine IsHyperbolic.of_entries_eq_zero fun x y => ?_
      simp only [quadDeriv, Matrix.of_apply]
      rw [coeff_rename_of_not ⟨x₀, hx₀, by simp only [Finsupp.add_apply]; omega⟩, mul_zero]

omit [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] in
theorem supportedIn_rename (f : MvPolynomial ι ℝ) :
    SupportedIn (· ∈ Set.range e) (rename e f) := fun β hβ x hx => by
  by_contra h
  exact hβ (coeff_rename_of_not ⟨x, hx, h⟩)

end Rename

/-! ### Products of local factors -/

theorem isLorentzianPolynomial_one : IsLorentzianPolynomial 0 (1 : MvPolynomial σ ℝ) := by
  have h0 : ∀ β : σ →₀ ℕ, coeff β (1 : MvPolynomial σ ℝ) ≠ 0 → β = 0 := fun β hβ => by
    by_contra h
    exact hβ (by rw [coeff_one, if_neg (Ne.symm h)])
  refine ⟨fun β => ?_, fun β hβ => by rw [h0 β hβ, map_zero], ?_, fun α hα => by omega⟩
  · show 0 ≤ coeff β (1 : MvPolynomial σ ℝ)
    rw [coeff_one]; split_ifs <;> norm_num
  · intro α hα β hβ l hlt
    rw [h0 α hα, h0 β hβ] at hlt
    exact absurd hlt (lt_irrefl _)

variable {κ ι τ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- The local factors in disjoint variables: `∏_{p ∈ s} f_p(x_{p,·})`. -/
def disjointProd (s : Finset κ) (f : κ → MvPolynomial ι ℝ) : MvPolynomial (κ × ι) ℝ :=
  ∏ p ∈ s, rename (Prod.mk p) (f p)

/-- **Lorentzian local factors in disjoint variables have a Lorentzian product.** -/
theorem isLorentzianPolynomial_disjointProd {d : κ → ℕ} {f : κ → MvPolynomial ι ℝ}
    (s : Finset κ) (hf : ∀ p ∈ s, IsLorentzianPolynomial (d p) (f p)) :
    IsLorentzianPolynomial (∑ p ∈ s, d p) (disjointProd s f) ∧
      SupportedIn (fun x => x.1 ∈ s) (disjointProd s f) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa [disjointProd] using isLorentzianPolynomial_one, fun β hβ x _ => ?_⟩
    have : β = 0 := by
      by_contra h
      exact hβ (by simp only [disjointProd, prod_empty]; rw [coeff_one, if_neg (Ne.symm h)])
    simp [this]
  | insert a s ha ih =>
    obtain ⟨ihL, ihS⟩ := ih fun p hp => hf p (mem_insert_of_mem hp)
    have hR := isLorentzianPolynomial_rename (Prod.mk_right_injective a) (hf a (mem_insert_self a s))
    have hRV : SupportedIn (fun x : κ × ι => x.1 = a) (rename (Prod.mk a) (f a)) :=
      fun β hβ x hx => supportedIn_rename (f a) β hβ x fun ⟨i, hi⟩ => hx (by rw [← hi])
    have hSV : SupportedIn (fun x : κ × ι => ¬ x.1 = a) (disjointProd s f) :=
      fun β hβ x hx => ihS β hβ x fun hxs => ha (by rw [← not_not.mp hx]; exact hxs)
    have hprod : disjointProd (insert a s) f = rename (Prod.mk a) (f a) * disjointProd s f := by
      simp only [disjointProd, prod_insert ha]
    refine ⟨?_, fun β hβ x hx => ?_⟩
    · rw [hprod, sum_insert ha]; exact hR.mul_of_supportedIn ihL hRV hSV
    · rw [hprod, coeff_mul_of_supportedIn hRV hSV] at hβ
      obtain ⟨-, h2⟩ := mul_ne_zero_iff.mp hβ
      have hxa : ¬ x.1 = a := fun h => hx (h ▸ mem_insert_self a s)
      have := ihS _ h2 x fun h => hx (mem_insert_of_mem h)
      rwa [Finsupp.filter_apply, if_pos hxa] at this

/-- The merging matrix `x_{p,i} ↦ x_i`. -/
def mergeMatrix : Matrix (κ × ι) ι ℝ := fun x i => if x.2 = i then 1 else 0

omit [Fintype κ] [DecidableEq κ] in
theorem linSub_mergeMatrix : linSub (mergeMatrix (κ := κ) (ι := ι)) = fun x => X x.2 := by
  funext x
  simp [linSub, mergeMatrix]

omit [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
theorem aeval_merge_disjointProd (s : Finset κ) (f : κ → MvPolynomial ι ℝ) :
    aeval (fun x : κ × ι => X x.2) (disjointProd s f) = ∏ p ∈ s, f p := by
  simp only [disjointProd, map_prod, aeval_rename]
  exact prod_congr rfl fun p _ => by simp [Function.comp_def]

/-- **The product of Lorentzian polynomials is mixed-Lorentzian**: place the factors in disjoint
variables and merge them by the nonnegative substitution `x_{p,i} ↦ x_i`. -/
theorem isMixedLorentzian_prod {d : κ → ℕ} {f : κ → MvPolynomial ι ℝ} (s : Finset κ)
    (hf : ∀ p ∈ s, IsLorentzianPolynomial (d p) (f p)) :
    IsMixedLorentzian (∑ p ∈ s, d p) (∏ p ∈ s, f p) := by
  have h := (isLorentzianPolynomial_disjointProd s hf).1.isMixedLorentzian.subst
    (A := mergeMatrix) fun x i => by unfold mergeMatrix; split_ifs <;> norm_num
  rwa [linSub_mergeMatrix, aeval_merge_disjointProd] at h

/-- **The Euler product closure**: the product of Lorentzian local factors, composed with any
nonnegative substitution (the scale map), is mixed-Lorentzian. -/
theorem isMixedLorentzian_prod_subst [Fintype τ] [DecidableEq τ] {d : κ → ℕ}
    {f : κ → MvPolynomial ι ℝ} (s : Finset κ) (hf : ∀ p ∈ s, IsLorentzianPolynomial (d p) (f p))
    {A : Matrix ι τ ℝ} (hA : ∀ i k, 0 ≤ A i k) :
    IsMixedLorentzian (∑ p ∈ s, d p) (aeval (linSub A) (∏ p ∈ s, f p)) :=
  (isMixedLorentzian_prod s hf).subst hA

/-- **The product of two Lorentzian polynomials is mixed-Lorentzian.** -/
theorem isMixedLorentzian_mul {d e : ℕ} {f g : MvPolynomial ι ℝ}
    (hf : IsLorentzianPolynomial d f) (hg : IsLorentzianPolynomial e g) :
    IsMixedLorentzian (d + e) (f * g) := by
  have := isMixedLorentzian_prod (κ := Fin 2) (d := ![d, e]) (f := ![f, g]) univ
    fun p _ => by fin_cases p <;> simpa
  simpa [Fin.sum_univ_two, Fin.prod_univ_two] using this

/-! ### Linear local factors -/

omit [Fintype κ] [DecidableEq κ] in
/-- A linear form with nonnegative coefficients is Lorentzian of degree one. -/
theorem isLorentzianPolynomial_linear {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    IsLorentzianPolynomial 1 (∑ i, C (a i) * X i : MvPolynomial ι ℝ) := by
  have hc : ∀ β, coeff β (∑ i, C (a i) * X i : MvPolynomial ι ℝ) =
      ∑ i, if Finsupp.single i 1 = β then a i else 0 := fun β => by
    simp [coeff_sum, coeff_C_mul, coeff_X, mul_ite]
  have hunit : ∀ β, coeff β (∑ i, C (a i) * X i : MvPolynomial ι ℝ) ≠ 0 →
      ∃ i, Finsupp.single i 1 = β := fun β hβ => by
    by_contra h
    push Not at h
    exact hβ (by rw [hc]; exact sum_eq_zero fun i _ => if_neg (h i))
  refine ⟨fun β => ?_, fun β hβ => ?_, ?_, fun α hα => by omega⟩
  · show 0 ≤ coeff β (∑ i, C (a i) * X i : MvPolynomial ι ℝ)
    rw [hc]; exact sum_nonneg fun i _ => by split_ifs; exacts [ha i, le_rfl]
  · obtain ⟨i, rfl⟩ := hunit β hβ
    exact Finsupp.degree_single i 1
  · intro α hα β hβ l hlt
    obtain ⟨i, rfl⟩ := hunit α hα
    obtain ⟨j, rfl⟩ := hunit β hβ
    have hil : l = i := by
      by_contra h
      simp [Finsupp.single_apply, Ne.symm h] at hlt
    subst hil
    have hij : l ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    refine ⟨j, by simp [hij], ?_⟩
    show coeff _ _ ≠ 0
    rw [tsub_self, zero_add]
    exact hβ

omit [DecidableEq κ] in
/-- **The Euler product of nonnegative linear local factors is mixed-Lorentzian.** -/
theorem isMixedLorentzian_eulerProduct {L : κ → ι → ℝ} (hL : ∀ p i, 0 ≤ L p i) :
    IsMixedLorentzian (Fintype.card κ) (eulerProduct L) := by
  classical
  have := isMixedLorentzian_prod (d := fun _ => 1) univ fun p _ => isLorentzianPolynomial_linear
    (hL p)
  simpa [eulerProduct, localLinear] using this

/-- **The Euler product closure at every nonnegative point**: the Hessian
`Σ_{p≠q} (∏_{r≠p,q} ⟨L_r, y⟩) L_p L_qᵀ` of `∏_p ⟨L_p, X⟩` is Lorentzian at every `y ≥ 0`, with
no positivity required of the local factors at `y`. -/
theorem isLorentzian_eulerHessian_of_nonneg {L : κ → ι → ℝ} (hL : ∀ p i, 0 ≤ L p i)
    {y : ι → ℝ} (hy : ∀ i, 0 ≤ y i) : IsLorentzian (eulerHessian L y) := by
  have hsymm : ∀ i j, eulerHessian L y i j = eulerHessian L y j i := fun i j => by
    rw [← eval_pderiv_pderiv_eulerProduct, ← eval_pderiv_pderiv_eulerProduct,
      GaloisForLFunctions.pderiv_comm]
  have hnn : ∀ i j, 0 ≤ eulerHessian L y i j := fun i j => by
    simp only [eulerHessian, Matrix.sum_apply]
    refine sum_nonneg fun p _ => sum_nonneg fun q _ => ?_
    split_ifs
    · simp
    · simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
      exact mul_nonneg (prod_nonneg fun r _ => sum_nonneg fun k _ => mul_nonneg (hL r k) (hy k))
        (mul_nonneg (hL p i) (hL q j))
  refine ⟨Matrix.IsSymm.ext fun i j => hsymm j i, hnn, ?_⟩
  rcases Nat.lt_or_ge (Fintype.card κ) 2 with hκ | hκ
  · -- with at most one local factor the Hessian vanishes
    refine IsHyperbolic.of_entries_eq_zero fun i j => ?_
    simp only [eulerHessian, Matrix.sum_apply]
    refine sum_eq_zero fun p _ => sum_eq_zero fun q _ => ?_
    rw [if_pos (Fintype.card_le_one_iff.mp (by omega) p q)]
    rfl
  · obtain ⟨n, hn⟩ : ∃ n, Fintype.card κ = n + 2 := ⟨Fintype.card κ - 2, by omega⟩
    have hP := isMixedLorentzian_eulerProduct hL
    rw [hn] at hP
    have e1 : eulerHessian L y = hessAt (eulerProduct L) y := by
      ext i j
      rw [hessAt, Matrix.of_apply, eval_pderiv_pderiv_eulerProduct, hsymm]
    rw [e1]
    exact hP.isHyperbolic_hessAt hy

end GaloisForLFunctions.ArithmeticLorentzianGeometry
