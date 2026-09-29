import GaloisForLFunctions.HTGeometry.SteinmetzReduction
import GaloisForLFunctions.HTGeometry.CompositionJetPolynomials

/-!
# A hypertranscendental inner function makes every entire composite hypertranscendental

Let `f` and `g` be entire and `g` hypertranscendental.  If `f ∘ g` satisfies an algebraic
differential equation `P(z, (f∘g), …, (f∘g)^{(n)}) = 0`, then Faà di Bruno's formula
(`CompositionJetPolynomials.compJetPoly`) rewrites it as

`Σ_ν (Π_j f^{(j)}(g)^{ν_j}) · h_ν = 0`,

with `h_ν` polynomials in `z` and the jets of `g`.  The substituted polynomial is nonzero (at
`g' = 1`, `g^{(i)} = 0` for `i ≥ 2` the formula returns the jets of `f` themselves), so some
coefficient polynomial is nonzero, and since `g` is hypertranscendental its value `h_ν` is not
identically zero.  Steinmetz's Korollar 1 (`SteinmetzReduction`) then gives polynomials `Q_ν`, not
all zero, with `Σ_ν Q_ν · Π_j (f^{(j)})^{ν_j} ≡ 0`: an algebraic differential equation for `f`.

With the three other directions (`CompositionInnerDecomposition`) this is the Boolean law: for
nonconstant entire `f` and `g`, `f ∘ g` is differentially algebraic exactly when both are.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set MvPolynomial

noncomputable section

/-! ### Faà di Bruno for entire functions -/

/-- The values of the composition-jet variables: `inl j ↦ f^{(j)}(g z)`, `inr i ↦ g^{(i+1)}(z)`. -/
def compJetValue (f g : ℂ → ℂ) (z : ℂ) : CompJetVar → ℂ :=
  Sum.elim (fun j => iteratedDeriv j f (g z)) (fun i => iteratedDeriv (i + 1) g z)

/-- Differentiating an evaluated composition-jet polynomial applies the formal chain rule. -/
theorem hasDerivAt_aeval_compJetValue {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (P : MvPolynomial CompJetVar ℂ) (z : ℂ) :
    HasDerivAt (fun w => aeval (compJetValue f g w) P)
      (aeval (compJetValue f g z) (compJetDerivation ℂ P)) z := by
  have hfd : ∀ j, Differentiable ℂ (iteratedDeriv j f) := differentiable_iteratedDeriv_entire hf
  have hgd : ∀ j, Differentiable ℂ (iteratedDeriv j g) := differentiable_iteratedDeriv_entire hg
  induction P using MvPolynomial.induction_on generalizing z with
  | C a =>
      have h0 : compJetDerivation ℂ (C a) = 0 := by
        rw [← MvPolynomial.algebraMap_eq]
        exact Derivation.map_algebraMap _ a
      rw [h0, map_zero]
      simp only [aeval_C]
      exact hasDerivAt_const z (algebraMap ℂ ℂ a)
  | add p q hp hq =>
      simp only [map_add]
      exact (hp z).add (hq z)
  | mul_X p v hp =>
      simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, map_add]
      have hv : HasDerivAt (fun w => compJetValue f g w v)
          (aeval (compJetValue f g z) (compJetDerivation ℂ (X v))) z := by
        cases v with
        | inl j =>
            rw [compJetDerivation_X_inl]
            simp only [map_mul, aeval_X, compJetValue, Sum.elim_inl, Sum.elim_inr, zero_add,
              iteratedDeriv_one]
            have h1 : HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f (g z)) (g z) := by
              rw [iteratedDeriv_succ]
              exact (hfd j (g z)).hasDerivAt
            exact h1.comp z (hg z).hasDerivAt
        | inr i =>
            rw [compJetDerivation_X_inr]
            simp only [aeval_X, compJetValue, Sum.elim_inr]
            have h1 := (hgd (i + 1) z).hasDerivAt
            rw [← iteratedDeriv_succ] at h1
            exact h1
      exact ((hp z).fun_mul hv).congr_deriv (by ring)

/-- **Faà di Bruno's formula for entire functions.** -/
theorem iteratedDeriv_comp_eq_aeval_compJetPoly {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => f (g w)) z = aeval (compJetValue f g z) (compJetPoly ℂ k) := by
  induction k generalizing z with
  | zero =>
      simp [compJetValue]
  | succ k ih =>
      have hfun : iteratedDeriv k (fun w => f (g w)) = fun w => aeval (compJetValue f g w)
          (compJetPoly ℂ k) := funext ih
      rw [iteratedDeriv_succ, hfun, compJetPoly_succ]
      exact (hasDerivAt_aeval_compJetValue hf hg _ z).deriv

/-! ### The substituted polynomial is nonzero -/

/-- At unit first inner derivative and vanishing higher inner derivatives, the composition-jet
polynomials return the outer jets: `Ξ_k(y; 1, 0, 0, …) = y_k`. -/
theorem aeval_compJetPoly_unit_slope (y : ℕ → ℂ) (k : ℕ) :
    aeval (Sum.elim y fun i => if i = 0 then (1 : ℂ) else 0) (compJetPoly ℂ k) = y k := by
  set D₀ : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
    MvPolynomial.mkDerivation ℂ fun j => X (j + 1) with hD₀
  set D : Derivation ℤ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) := D₀.restrictScalars ℤ with hD
  have hDX : ∀ j, D (X j) = X (j + 1) := fun j => by
    rw [hD, Derivation.coe_restrictScalars, hD₀, MvPolynomial.mkDerivation_X]
  set c : ℕ → MvPolynomial ℕ ℂ := fun i => if i = 0 then 1 else 0 with hc
  have hK : ∀ a : ℂ, D (algebraMap ℂ (MvPolynomial ℕ ℂ) a) = 0 := fun a => by
    rw [hD, Derivation.coe_restrictScalars]
    exact D₀.map_algebraMap a
  have ha : ∀ j, D (X j) = X (j + 1) * c 0 := fun j => by rw [hDX, hc]; simp
  have hcc : ∀ i, D (c i) = c (i + 1) := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [hc]
    · have hi' : i ≠ 0 := by omega
      simp [hc, hi']
  have hiter : ∀ k, (⇑D)^[k] (X 0) = X k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hDX]
  have h := (hiter k).symm.trans
    (iterate_deriv_eq_aeval_compJetPoly (K := ℂ) D hK (fun j => X j) c ha hcc k)
  have h2 := congrArg (MvPolynomial.aeval y) h
  rw [MvPolynomial.aeval_X, MvPolynomial.comp_aeval_apply] at h2
  rw [h2]
  congr 2
  funext v
  cases v with
  | inl j => simp
  | inr i =>
      simp only [Sum.elim_inr, hc]
      split_ifs <;> simp

/-! ### Splitting off the outer jets -/

/-- Evaluation on a disjoint union of variables, through `sumAlgEquiv`. -/
theorem aeval_sumElim_eq_eval₂_sumAlgEquiv {σ τ : Type*} (a : σ → ℂ) (b : τ → ℂ)
    (p : MvPolynomial (σ ⊕ τ) ℂ) :
    aeval (Sum.elim a b) p
      = eval₂ (aeval b).toRingHom a (sumAlgEquiv ℂ σ τ p) := by
  have h : (aeval (Sum.elim a b)).toRingHom
      = (eval₂Hom (aeval b).toRingHom a).comp (sumAlgEquiv ℂ σ τ).toAlgHom.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [sumAlgEquiv_C_inl]
    · rintro (i | i)
      · simp [sumAlgEquiv_X_inl]
      · simp [sumAlgEquiv_X_inr]
  exact RingHom.congr_fun h p

/-! ### From a polynomial relation to an algebraic differential equation -/

/-- The jet indexing `0 ↦ z`, `k + 1 ↦ f^{(k)}`. -/
def finJetIndex (N : ℕ) : Fin (N + 2) → Option ℕ :=
  Fin.cases none fun k : Fin (N + 1) => some (k : ℕ)

theorem finJetIndex_injective (N : ℕ) : Function.Injective (finJetIndex N) := by
  intro a b hab
  induction a using Fin.cases with
  | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ b => simp [finJetIndex] at hab
  | succ a =>
      induction b using Fin.cases with
      | zero => simp [finJetIndex] at hab
      | succ b =>
          simp only [finJetIndex, Fin.cases_succ, Option.some.injEq] at hab
          exact congrArg Fin.succ (Fin.ext hab)

/-- A finite family of polynomials in the jet variables `Option ℕ` lives in finitely many of
them. -/
theorem exists_finJet_rename {ι : Type*} (T : Finset ι) (p : ι → MvPolynomial (Option ℕ) ℂ) :
    ∃ N : ℕ, ∀ i ∈ T, ∃ q : MvPolynomial (Fin (N + 2)) ℂ, rename (finJetIndex N) q = p i := by
  classical
  set V : Finset (Option ℕ) := T.biUnion fun i => (p i).vars with hV
  set N : ℕ := V.sup fun v => Option.elim v 0 id with hN
  refine ⟨N, fun i hi => ?_⟩
  refine MvPolynomial.exists_rename_eq_of_vars_subset_range (p i) (finJetIndex N)
    (finJetIndex_injective N) ?_
  intro v hv
  cases v with
  | none => exact ⟨0, rfl⟩
  | some j =>
      have hjV : some j ∈ V := Finset.mem_biUnion.mpr ⟨i, hi, hv⟩
      have hjN : j ≤ N := by
        have := Finset.le_sup (f := fun v : Option ℕ => Option.elim v 0 id) hjV
        simpa using this
      exact ⟨Fin.succ ⟨j, by omega⟩, rfl⟩

/-- The jet values `none ↦ z`, `some j ↦ f^{(j)}(z)`. -/
def jetValue (f : ℂ → ℂ) (z : ℂ) : Option ℕ → ℂ :=
  fun v => Option.elim v z fun j => iteratedDeriv j f z

theorem jetValue_comp_finJetIndex (f : ℂ → ℂ) (N : ℕ) (z : ℂ) :
    jetValue f z ∘ finJetIndex N = jetVector f N z := by
  funext k
  induction k using Fin.cases with
  | zero => rfl
  | succ k => rfl

/-- **A nonzero polynomial relation among `z` and the jets of `f` makes `f` differentially
algebraic**, whatever finite set of jet variables it uses. -/
theorem differentiallyAlgebraic_of_jet_relation {f : ℂ → ℂ} {σ : Type*} (e : σ → Option ℕ)
    (he : Function.Injective e) {R : MvPolynomial σ ℂ} (hR : R ≠ 0)
    (hrel : ∀ z, aeval (jetValue f z ∘ e) R = 0) : DifferentiallyAlgebraic f := by
  classical
  obtain ⟨N, hN⟩ := exists_finJet_rename {()} (fun _ => rename e R)
  obtain ⟨q, hq⟩ := hN () (Finset.mem_singleton_self _)
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hq
    exact hR (rename_injective e he (by rw [← hq, map_zero]))
  refine ⟨N, q, hq0, fun z => ?_⟩
  rw [show (Fin.cons z fun j : Fin (N + 1) => iteratedDeriv j f z : Fin (N + 2) → ℂ)
      = jetValue f z ∘ finJetIndex N from (jetValue_comp_finJetIndex f N z).symm]
  show aeval (jetValue f z ∘ finJetIndex N) q = 0
  rw [← aeval_rename, hq, aeval_rename]
  exact hrel z

/-! ### Steinmetz's Satz 2 -/

/-- Evaluating the one-variable polynomial ring at `w` through `MvPolynomial Unit`. -/
theorem aeval_uniqueAlgEquiv_symm (p : Polynomial ℂ) (w : ℂ) :
    aeval (fun _ : Unit => w) ((MvPolynomial.uniqueAlgEquiv ℂ Unit).symm p) = p.eval w := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.eval_add]
  | monomial n a _ =>
      rw [map_mul, map_pow, map_mul, map_pow]
      simp

/-- **A differentially algebraic composite with a hypertranscendental inner function has a
differentially algebraic outer function** (Steinmetz's Satz 2, entire case). -/
theorem differentiallyAlgebraic_of_comp_of_not_differentiallyAlgebraic_inner {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hgHT : ¬ DifferentiallyAlgebraic g)
    (hcomp : DifferentiallyAlgebraic fun z => f (g z)) : DifferentiallyAlgebraic f := by
  classical
  have hfd : ∀ j, Differentiable ℂ (iteratedDeriv j f) := differentiable_iteratedDeriv_entire hf
  have hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z := by
    rintro ⟨p, hp⟩
    apply hgHT
    have hgp : g = fun z => p.eval z := funext hp
    rw [hgp]
    exact differentiallyAlgebraic_polynomial p
  obtain ⟨n, P, hP0, hPrel⟩ := hcomp
  -- the Faà di Bruno substitution
  set τ : CompJetVar → ℕ ⊕ Option ℕ := Sum.elim Sum.inl fun i => Sum.inr (some i) with hτ
  set φs : Fin (n + 2) → MvPolynomial (ℕ ⊕ Option ℕ) ℂ :=
    Fin.cons (X (Sum.inr none)) fun k : Fin (n + 1) => rename τ (compJetPoly ℂ k) with hφs
  set S := bind₁ φs P with hS
  set b : ℂ → Option ℕ → ℂ := fun z v => Option.elim v z fun i => iteratedDeriv (i + 1) g z
    with hb
  set a : ℂ → ℕ → ℂ := fun z j => iteratedDeriv j f (g z) with ha
  have hSrel : ∀ z, aeval (Sum.elim (a z) (b z)) S = 0 := by
    intro z
    rw [hS, aeval_bind₁]
    have hfun : (fun k => aeval (Sum.elim (a z) (b z)) (φs k))
        = (Fin.cons z fun k : Fin (n + 1) => iteratedDeriv k (fun w => f (g w)) z :
          Fin (n + 2) → ℂ) := by
      funext k
      induction k using Fin.cases with
      | zero => simp [hφs, hb]
      | succ k =>
          simp only [hφs, Fin.cons_succ]
          rw [aeval_rename, iteratedDeriv_comp_eq_aeval_compJetPoly hf hg]
          congr 2
          funext v
          cases v with
          | inl j => rfl
          | inr i => rfl
    rw [hfun]
    exact hPrel z
  -- the substituted polynomial is nonzero
  have hS0 : S ≠ 0 := by
    obtain ⟨y, hy⟩ : ∃ y : Fin (n + 2) → ℂ, MvPolynomial.eval y P ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hP0 (MvPolynomial.funext fun y => by simpa using hcon y)
    set yy : ℕ → ℂ := fun j => if h : j + 1 < n + 2 then y ⟨j + 1, h⟩ else 0 with hyy
    set sp : ℕ ⊕ Option ℕ → ℂ :=
      Sum.elim yy fun v => Option.elim v (y 0) fun i => if i = 0 then 1 else 0 with hsp
    intro h0
    apply hy
    have h1 : aeval sp S = 0 := by rw [h0, map_zero]
    rw [hS, aeval_bind₁] at h1
    have hy' : (fun k => aeval sp (φs k)) = y := by
      funext k
      induction k using Fin.cases with
      | zero => simp [hφs, hsp]
      | succ k =>
          simp only [hφs, Fin.cons_succ]
          rw [aeval_rename]
          have hcomp : sp ∘ τ = Sum.elim yy fun i => if i = 0 then (1 : ℂ) else 0 := by
            funext v
            cases v with
            | inl j => rfl
            | inr i => rfl
          rw [hcomp, aeval_compJetPoly_unit_slope, hyy]
          beta_reduce
          rw [dif_pos (by omega)]
          rfl
    rw [hy'] at h1
    exact h1
  -- split off the outer jets
  set S₂ := sumAlgEquiv ℂ ℕ (Option ℕ) S with hS₂
  have hS₂0 : S₂ ≠ 0 := by
    rw [hS₂]
    exact (map_ne_zero_iff _ (sumAlgEquiv ℂ ℕ (Option ℕ)).injective).mpr hS0
  set T := S₂.support with hT
  set e' : Option ℕ → Option ℕ := Option.map Nat.succ with he'
  have he'inj : Function.Injective e' := Option.map_injective Nat.succ_injective
  have hjg : ∀ z, jetValue g z ∘ e' = b z := by
    intro z
    funext v
    cases v with
    | none => rfl
    | some i => rfl
  obtain ⟨N, hN⟩ := exists_finJet_rename T fun ν => rename e' (coeff ν S₂)
  choose! q hq using hN
  have hqeval : ∀ ν ∈ T, ∀ z, MvPolynomial.eval (jetVector g N z) (q ν)
      = aeval (b z) (coeff ν S₂) := by
    intro ν hν z
    rw [← jetValue_comp_finJetIndex g N z]
    show aeval (jetValue g z ∘ finJetIndex N) (q ν) = _
    rw [← aeval_rename, hq ν hν, aeval_rename, hjg]
  -- the outer monomials
  set F : (ℕ →₀ ℕ) → ℂ → ℂ := fun ν w => ∏ j ∈ ν.support, iteratedDeriv j f w ^ ν j with hF
  have hFd : ∀ ν, Differentiable ℂ (F ν) := fun ν =>
    Differentiable.fun_finsetProd fun j _ => (hfd j).pow (ν j)
  have hrel : ∀ z, ∑ ν ∈ T, F ν (g z) * MvPolynomial.eval (jetVector g N z) (q ν) = 0 := by
    intro z
    have h := hSrel z
    rw [aeval_sumElim_eq_eval₂_sumAlgEquiv, ← hS₂, MvPolynomial.eval₂_eq] at h
    rw [← h]
    refine Finset.sum_congr rfl fun ν hν => ?_
    rw [hqeval ν hν z, mul_comm]
    rfl
  -- some coefficient is not identically zero, since `g` is hypertranscendental
  have hh : ∃ ν ∈ T, ∃ z, MvPolynomial.eval (jetVector g N z) (q ν) ≠ 0 := by
    obtain ⟨ν, hν⟩ : T.Nonempty := by
      rw [hT, Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
      exact hS₂0
    refine ⟨ν, hν, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hgHT
    have hc0 : coeff ν S₂ ≠ 0 := MvPolynomial.mem_support_iff.mp hν
    refine differentiallyAlgebraic_of_jet_relation e' he'inj hc0 fun z => ?_
    rw [hjg, ← hqeval ν hν z]
    exact hcon z
  -- Steinmetz's Korollar 1
  obtain ⟨Q, ⟨ν₀, hν₀T, hQν₀⟩, hQrel⟩ :=
    exists_polynomial_relation_outer hg hgnp q T F hFd hrel hh
  -- the resulting equation for `f`
  set U := MvPolynomial.uniqueAlgEquiv ℂ Unit with hU
  set Rt : MvPolynomial ℕ (MvPolynomial Unit ℂ) := ∑ ν ∈ T, monomial ν (U.symm (Q ν)) with hRt
  have hRt0 : Rt ≠ 0 := by
    intro h0
    have hc := congrArg (coeff ν₀) h0
    rw [hRt, coeff_sum, Finset.sum_eq_single ν₀ (fun ν _ hν => by
      rw [coeff_monomial, if_neg hν]) (fun h => absurd hν₀T h), coeff_monomial, if_pos rfl,
      coeff_zero] at hc
    exact hQν₀ (U.symm.injective (by rw [hc, map_zero]))
  set R := (sumAlgEquiv ℂ ℕ Unit).symm Rt with hR
  have hR0 : R ≠ 0 := by
    rw [hR]
    exact (map_ne_zero_iff _ (sumAlgEquiv ℂ ℕ Unit).symm.injective).mpr hRt0
  set e₂ : ℕ ⊕ Unit → Option ℕ := Sum.elim some fun _ => none with he₂
  have he₂inj : Function.Injective e₂ := by
    rintro (i | u) (j | v) h
    · simp only [he₂, Sum.elim_inl, Option.some.injEq] at h
      rw [h]
    · simp [he₂] at h
    · simp [he₂] at h
    · rfl
  refine differentiallyAlgebraic_of_jet_relation e₂ he₂inj hR0 fun w => ?_
  have hval : jetValue f w ∘ e₂ = Sum.elim (fun j => iteratedDeriv j f w) fun _ => w := by
    funext v
    cases v with
    | inl j => rfl
    | inr u => rfl
  rw [hval, aeval_sumElim_eq_eval₂_sumAlgEquiv, hR, AlgEquiv.apply_symm_apply, hRt,
    MvPolynomial.eval₂_sum]
  rw [← hQrel w]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [eval₂_monomial]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [aeval_uniqueAlgEquiv_symm]
  rfl

/-- **The Boolean law for entire compositions.**  For nonconstant entire `f` and `g`, the composite
`f ∘ g` is differentially algebraic exactly when both `f` and `g` are; equivalently, it is
hypertranscendental exactly when `f` or `g` is. -/
theorem differentiallyAlgebraic_comp_iff {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hfnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c)
    (hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) :
    DifferentiallyAlgebraic (fun z => f (g z)) ↔
      (DifferentiallyAlgebraic f ∧ DifferentiallyAlgebraic g) :=
  differentiallyAlgebraic_comp_iff_of_gap hf hg hfnc hgnc fun hfHT hgHT hcomp =>
    hfHT (differentiallyAlgebraic_of_comp_of_not_differentiallyAlgebraic_inner hf hg hgHT hcomp)

end

end GaloisForLFunctions.HTGeometry
