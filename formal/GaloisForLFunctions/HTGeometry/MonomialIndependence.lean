import GaloisForLFunctions.HTGeometry.MultivariateRelationGrouping

/-!
# Algebraic independence of a family of functions, in monomial form

A family of functions is *polynomially independent* when no finite combination of monomials in them,
with polynomial coefficients, vanishes identically unless every coefficient is the zero polynomial.
Indexing the monomials by an arbitrary finite set with an injective exponent map — rather than by the
exponent vectors themselves — is what makes the definition directly applicable to a fibre of a
larger relation, with no image or choice construction.

The step this supports is the induction hypothesis of the Clunie argument: the top grouped
coefficient of a relation is a monomial combination of the *previous* states, so independence of
those states is exactly what makes it nonzero.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {k : ℕ}

/-- **Polynomial independence.**  No monomial relation with polynomial coefficients holds unless
every coefficient vanishes. -/
def PolyIndependent (F : Fin k → ℂ → ℂ) : Prop :=
  ∀ {ι : Type} (T : Finset ι) (E : ι → Fin k → ℕ) (A : ι → Polynomial ℂ),
    Set.InjOn E T →
    (∀ w : ℂ, ∑ e ∈ T, (A e).eval w * ∏ i, (F i w) ^ (E e i) = 0) →
    ∀ e ∈ T, A e = 0

/-- Dropping the last coordinate identifies the punctured index set with the smaller one. -/
theorem erase_last_eq_image :
    (Finset.univ.erase (Fin.last k)) = Finset.univ.image Fin.castSucc := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hi
    exact Fin.exists_castSucc_eq.mpr hi.1
  · rintro ⟨j, -, rfl⟩
    exact ⟨(Fin.castSucc_lt_last j).ne, trivial⟩

/-- The product over the punctured index set is the product over the smaller one. -/
theorem prod_erase_last {M : Type*} [CommMonoid M] (g : Fin (k + 1) → M) :
    ∏ i ∈ Finset.univ.erase (Fin.last k), g i = ∏ i : Fin k, g i.castSucc := by
  rw [erase_last_eq_image, Finset.prod_image]
  intro x _ y _ hxy
  exact Fin.castSucc_injective k hxy

/-- **The induction hypothesis makes a fibre coefficient nonzero.**  If the states before the last
are polynomially independent and a fibre coefficient of a relation vanishes identically, then every
coefficient in that fibre is the zero polynomial. -/
theorem coeff_eq_zero_of_groupedCoeff_zero {F : Fin (k + 1) → ℂ → ℂ}
    {S : Finset (Fin (k + 1) → ℕ)} {A : (Fin (k + 1) → ℕ) → Polynomial ℂ} {j : ℕ}
    (hind : PolyIndependent (fun i : Fin k => F i.castSucc))
    (hzero : ∀ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) j = 0) :
    ∀ e ∈ S.filter (fun e => e (Fin.last k) = j), A e = 0 := by
  classical
  refine hind (S.filter (fun e => e (Fin.last k) = j))
    (fun e => fun i : Fin k => e i.castSucc) A ?_ ?_
  · intro e₁ h₁ e₂ h₂ hE
    have hj₁ : e₁ (Fin.last k) = j := (Finset.mem_filter.mp h₁).2
    have hj₂ : e₂ (Fin.last k) = j := (Finset.mem_filter.mp h₂).2
    funext i
    refine Fin.lastCases ?_ ?_ i
    · rw [hj₁, hj₂]
    · intro l
      exact congrFun hE l
  · intro w
    have hgc := hzero w
    rw [groupedCoeff] at hgc
    rw [← hgc]
    refine Finset.sum_congr rfl ?_
    intro e _
    rw [prod_erase_last (fun i => (F i w) ^ (e i))]

/-! ## The induction step -/

/-- The separation input: wherever the top fibre coefficient is not identically zero, some point
carries both a nonzero value of it and the growth separation of the last state. -/
def SeparatesLast (F : Fin (k + 1) → ℂ → ℂ) : Prop :=
  ∀ (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
    1 ≤ N → (∀ e ∈ S, e (Fin.last k) ≤ N) →
    (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) N ≠ 0) →
    ∃ z : ℂ, groupedCoeff S (fun e => (A e).eval z) (fun i => F i z) N ≠ 0 ∧
      clunieWeight S (fun e => (A e).eval z) (fun i => F i z) N
        < Real.posLog ‖F (Fin.last k) z‖

/-- **The Clunie induction step, by degree in the last state.** -/
theorem coeff_eq_zero_of_relation {F : Fin (k + 1) → ℂ → ℂ}
    (hind : PolyIndependent (fun i : Fin k => F i.castSucc)) (hsep : SeparatesLast F) :
    ∀ (N : ℕ) (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → Polynomial ℂ),
      (∀ e ∈ S, e (Fin.last k) ≤ N) →
      (∀ w : ℂ, ∑ e ∈ S, (A e).eval w * ∏ i, (F i w) ^ (e i) = 0) →
      ∀ e ∈ S, A e = 0 := by
  classical
  intro N
  induction N with
  | zero =>
      intro S A hdeg hrel
      have hfilter : S.filter (fun e => e (Fin.last k) = 0) = S := by
        refine Finset.filter_true_of_mem ?_
        intro e he
        exact Nat.le_zero.mp (hdeg e he)
      have hzero : ∀ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) 0 = 0 := by
        intro w
        rw [groupedCoeff, hfilter, ← hrel w]
        refine Finset.sum_congr rfl ?_
        intro e he
        have hlast : e (Fin.last k) = 0 := Nat.le_zero.mp (hdeg e he)
        have hprod : ∏ i, (F i w) ^ (e i)
            = (F (Fin.last k) w) ^ (e (Fin.last k))
              * ∏ i ∈ Finset.univ.erase (Fin.last k), (F i w) ^ (e i) :=
          (Finset.mul_prod_erase Finset.univ (fun i => (F i w) ^ (e i))
            (Finset.mem_univ _)).symm
        rw [hprod, hlast, pow_zero, one_mul]
      have := coeff_eq_zero_of_groupedCoeff_zero hind hzero
      rw [hfilter] at this
      exact this
  | succ M ih =>
      intro S A hdeg hrel
      by_cases hz : ∀ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) (M + 1) = 0
      · -- the top fibre vanishes identically: its coefficients are zero and the degree drops
        have htopzero := coeff_eq_zero_of_groupedCoeff_zero hind hz
        have hrest : ∀ w : ℂ,
            ∑ e ∈ S.filter (fun e => ¬ e (Fin.last k) = M + 1),
              (A e).eval w * ∏ i, (F i w) ^ (e i) = 0 := by
          intro w
          have hsplit := Finset.sum_filter_add_sum_filter_not S
            (fun e => e (Fin.last k) = M + 1)
            (fun e => (A e).eval w * ∏ i, (F i w) ^ (e i))
          have hfirst : ∑ e ∈ S.filter (fun e => e (Fin.last k) = M + 1),
              (A e).eval w * ∏ i, (F i w) ^ (e i) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro e he
            rw [htopzero e he]
            simp
          rw [hfirst, zero_add] at hsplit
          rw [hsplit]
          exact hrel w
        have hdegrest : ∀ e ∈ S.filter (fun e => ¬ e (Fin.last k) = M + 1),
            e (Fin.last k) ≤ M := by
          intro e he
          have h1 := Finset.mem_filter.mp he
          have h2 := hdeg e h1.1
          omega
        have hrestzero := ih (S.filter (fun e => ¬ e (Fin.last k) = M + 1)) A hdegrest hrest
        intro e he
        by_cases hlast : e (Fin.last k) = M + 1
        · exact htopzero e (Finset.mem_filter.mpr ⟨he, hlast⟩)
        · exact hrestzero e (Finset.mem_filter.mpr ⟨he, hlast⟩)
      · -- otherwise separation contradicts the relation
        rw [not_forall] at hz
        obtain ⟨z, hzne, hzsep⟩ := hsep S A (M + 1) (by omega) hdeg hz
        exact absurd (hrel z)
          (sum_ne_zero_of_clunieWeight_lt (by omega) hdeg hzne hzsep)

/-- **Separation upgrades independence by one state.**  If the states before the last are
polynomially independent and the last one is separated, then the whole family satisfies no monomial
relation with polynomial coefficients indexed by exponent vectors. -/
theorem coeff_eq_zero_of_relation' {F : Fin (k + 1) → ℂ → ℂ}
    (hind : PolyIndependent (fun i : Fin k => F i.castSucc)) (hsep : SeparatesLast F)
    (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → Polynomial ℂ)
    (hrel : ∀ w : ℂ, ∑ e ∈ S, (A e).eval w * ∏ i, (F i w) ^ (e i) = 0) :
    ∀ e ∈ S, A e = 0 := by
  classical
  refine coeff_eq_zero_of_relation hind hsep
    (S.sup (fun e => e (Fin.last k))) S A ?_ hrel
  intro e he
  exact Finset.le_sup (f := fun e => e (Fin.last k)) he

/-! ## Independence in chainable form -/

/-- The exponent-vector form of independence implies the index-set form. -/
theorem polyIndependent_of_exponentVector {F : Fin k → ℂ → ℂ}
    (h : ∀ (S : Finset (Fin k → ℕ)) (A : (Fin k → ℕ) → Polynomial ℂ),
      (∀ w : ℂ, ∑ e ∈ S, (A e).eval w * ∏ i, (F i w) ^ (e i) = 0) → ∀ e ∈ S, A e = 0) :
    PolyIndependent F := by
  classical
  intro ι T E A hinj hrel e he
  set A' : (Fin k → ℕ) → Polynomial ℂ := fun v =>
    if hx : ∃ e' ∈ T, E e' = v then A hx.choose else 0 with hA'def
  have hA' : ∀ e' ∈ T, A' (E e') = A e' := by
    intro e' he'
    have hex : ∃ e'' ∈ T, E e'' = E e' := ⟨e', he', rfl⟩
    rw [hA'def]
    simp only [dif_pos hex]
    congr 1
    exact hinj (Finset.mem_coe.mpr hex.choose_spec.1) (Finset.mem_coe.mpr he')
      hex.choose_spec.2
  have hrel' : ∀ w : ℂ, ∑ v ∈ T.image E, (A' v).eval w * ∏ i, (F i w) ^ (v i) = 0 := by
    intro w
    rw [Finset.sum_image (fun x hx y hy hxy =>
      hinj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy)]
    rw [← hrel w]
    refine Finset.sum_congr rfl ?_
    intro e' he'
    rw [hA' e' he']
  have hzero := h (T.image E) A' hrel' (E e) (Finset.mem_image_of_mem E he)
  rw [hA' e he] at hzero
  exact hzero

/-- **Separation upgrades independence by one state.** -/
theorem polyIndependent_succ {F : Fin (k + 1) → ℂ → ℂ}
    (hind : PolyIndependent (fun i : Fin k => F i.castSucc)) (hsep : SeparatesLast F) :
    PolyIndependent F :=
  polyIndependent_of_exponentVector fun S A hrel => coeff_eq_zero_of_relation' hind hsep S A hrel

/-- **The empty family is independent.**  With no states, a relation is a single polynomial
vanishing everywhere. -/
theorem polyIndependent_zero (F : Fin 0 → ℂ → ℂ) : PolyIndependent F := by
  classical
  intro ι T E A hinj hrel e he
  have hsingle : T = {e} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨he, ?_⟩
    intro b hb
    exact hinj (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr he) (Subsingleton.elim _ _)
  refine Polynomial.funext ?_
  intro w
  have hw := hrel w
  rw [hsingle, Finset.sum_singleton] at hw
  simpa using hw

/-- **The full Clunie chain.**  A family whose every initial segment separates its last member is
polynomially independent: the state field has transcendence degree equal to the number of states. -/
theorem polyIndependent_of_chain : ∀ (n : ℕ) (F : Fin n → ℂ → ℂ),
    (∀ (m : ℕ) (hm : m + 1 ≤ n), SeparatesLast (fun i : Fin (m + 1) => F (Fin.castLE hm i))) →
    PolyIndependent F := by
  intro n
  induction n with
  | zero =>
      intro F _
      exact polyIndependent_zero F
  | succ n ih =>
      intro F hchain
      have hind : PolyIndependent (fun i : Fin n => F i.castSucc) := by
        refine ih (fun i : Fin n => F i.castSucc) ?_
        intro m hm
        have hm' : m + 1 ≤ n + 1 := le_trans hm (Nat.le_succ n)
        have heq : (fun i : Fin (m + 1) => (fun j : Fin n => F j.castSucc) (Fin.castLE hm i))
            = fun i : Fin (m + 1) => F (Fin.castLE hm' i) := by
          funext i
          congr 1
        rw [heq]
        exact hchain m hm'
      have hsep : SeparatesLast F := by
        have h := hchain n (le_refl (n + 1))
        have heq : (fun i : Fin (n + 1) => F (Fin.castLE (le_refl (n + 1)) i)) = F := by
          funext i
          congr 1
        rwa [heq] at h
      intro ι T E A hinj hrel
      exact polyIndependent_succ hind hsep T E A hinj hrel

end GaloisForLFunctions.HTGeometry
