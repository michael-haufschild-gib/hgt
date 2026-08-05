import GaloisForLFunctions.HTGeometry.ExpandedEvaluationSampling

/-!
# When the expanded monomial family is independent, and when it cannot be

The sampling reduction leaves exactly one input: linear independence of the family

  `g (a,d) : w ↦ w ^ d * ∏ k, (F k w) ^ (exponent a k)`.

That input is an algebraic-independence statement in disguise.  The family is the image, under
evaluation at `(id, F₁, …, Fₙ)`, of a set of **distinct monomials** of a polynomial ring, so it is
independent as soon as that evaluation is injective — that is, as soon as the node coordinate and
the jets are algebraically independent over the constants.

The failure is equally sharp, and it settles what node hypotheses can never do: if a nonzero
algebraic relation among `(id, F₁, …, Fₙ)` is supported inside the monomial box, two columns of the
evaluation matrix are literally equal functions, and **no** choice of nodes — however distinct, with
however nonvanishing monomial values — can restore full rank.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-! ## The monomial carried by a column -/

/-- The polynomial exponent carried by the column `(a, d)`: degree `d` in the node coordinate and
`exponent a` in the jets. -/
noncomputable def expandedColumnExponent {κ : Type*} {n q : ℕ}
    (exponent : κ → (Fin n →₀ ℕ)) (c : κ × Fin (q + 1)) : Option (Fin n) →₀ ℕ :=
  Finsupp.single none (c.2 : ℕ) + (exponent c.1).mapDomain some

/-- The node coordinate together with the jets, as an evaluation family. -/
noncomputable def jetEvaluationFamily {n : ℕ} (F : Fin n → ℂ → ℂ) :
    Option (Fin n) → (ℂ → ℂ)
  | none => fun w => w
  | some k => F k

theorem expandedMonomialFamily_apply {κ : Type*} {n q : ℕ} (F : Fin n → ℂ → ℂ)
    (exponent : κ → (Fin n →₀ ℕ)) (c : κ × Fin (q + 1)) (w : ℂ) :
    expandedMonomialFamily F exponent q c w =
      w ^ (c.2 : ℕ) * ∏ k ∈ (exponent c.1).support, (F k w) ^ (exponent c.1 k) := by
  rw [expandedMonomialFamily, MvPolynomial.eval_monomial, one_mul, Finsupp.prod]

/-- **Each column of the family is the evaluation of its own monomial.** -/
theorem expandedMonomialFamily_eq_aeval {κ : Type*} {n q : ℕ} (F : Fin n → ℂ → ℂ)
    (exponent : κ → (Fin n →₀ ℕ)) (c : κ × Fin (q + 1)) :
    expandedMonomialFamily F exponent q c =
      aeval (jetEvaluationFamily F)
        (monomial (expandedColumnExponent (q := q) exponent c) (1 : ℂ)) := by
  have hzero : ∀ i : Option (Fin n), (jetEvaluationFamily F i) ^ (0 : ℕ) = 1 := by
    intro i; rw [pow_zero]
  have hadd : ∀ (i : Option (Fin n)) (b₁ b₂ : ℕ),
      (jetEvaluationFamily F i) ^ (b₁ + b₂)
        = (jetEvaluationFamily F i) ^ b₁ * (jetEvaluationFamily F i) ^ b₂ := by
    intro i b₁ b₂; rw [pow_add]
  have h1 : (Finsupp.single (none : Option (Fin n)) (c.2 : ℕ)).prod
      (fun i m => (jetEvaluationFamily F i) ^ m) = (fun w : ℂ => w) ^ (c.2 : ℕ) :=
    Finsupp.prod_single_index (hzero none)
  have h2 : (Finsupp.mapDomain some (exponent c.1)).prod
      (fun i m => (jetEvaluationFamily F i) ^ m)
      = (exponent c.1).prod (fun k m => (F k) ^ m) :=
    Finsupp.prod_mapDomain_index_inj (Option.some_injective (Fin n))
  have hsplit :
      (expandedColumnExponent (q := q) exponent c).prod
          (fun i m => (jetEvaluationFamily F i) ^ m)
        = ((fun w : ℂ => w) ^ (c.2 : ℕ)) *
            (exponent c.1).prod (fun k m => (F k) ^ m) := by
    rw [expandedColumnExponent, Finsupp.prod_add_index' hzero hadd, h1, h2]
  funext w
  rw [aeval_monomial, map_one, one_mul, hsplit, expandedMonomialFamily_apply]
  simp only [Pi.mul_apply, Pi.pow_apply, Finsupp.prod, Finset.prod_apply]


/-! ## Independence from algebraic independence -/

theorem expandedColumnExponent_injective {κ : Type*} {n q : ℕ}
    {exponent : κ → (Fin n →₀ ℕ)} (hexp : Function.Injective exponent) :
    Function.Injective (expandedColumnExponent (q := q) exponent) := by
  intro c c' h
  have hnone := congrArg (fun E => E none) h
  have hsome : ∀ k, (exponent c.1) k = (exponent c'.1) k := by
    intro k
    have := congrArg (fun E => E (some k)) h
    simpa [expandedColumnExponent, Finsupp.mapDomain_apply (Option.some_injective (Fin n))]
      using this
  have hfst : c.1 = c'.1 := hexp (Finsupp.ext hsome)
  have hsnd : (c.2 : ℕ) = (c'.2 : ℕ) := by
    simpa [expandedColumnExponent, Finsupp.mapDomain_notin_range] using hnone
  exact Prod.ext hfst (Fin.ext hsnd)

/-! ## The universal law: independence of a monomial box in any algebra -/

/-- **Distinct monomials in algebraically independent elements are linearly independent** — in any
commutative algebra over the constants, for any injectively indexed monomial box. -/
theorem linearIndependent_aeval_expandedColumn_of_algebraicIndependent
    {κ : Type*} {n q : ℕ} {A : Type*} [CommRing A] [Algebra ℂ A]
    {v : Option (Fin n) → A} (halg : AlgebraicIndependent ℂ v)
    {exponent : κ → (Fin n →₀ ℕ)} (hexp : Function.Injective exponent) :
    LinearIndependent ℂ (fun c : κ × Fin (q + 1) =>
      aeval v (monomial (expandedColumnExponent (q := q) exponent c) (1 : ℂ))) := by
  classical
  have hmon : LinearIndependent ℂ
      (⇑(MvPolynomial.basisMonomials (Option (Fin n)) ℂ) ∘
        (expandedColumnExponent (q := q) exponent)) :=
    (MvPolynomial.basisMonomials (Option (Fin n)) ℂ).linearIndependent.comp _
      (expandedColumnExponent_injective (q := q) hexp)
  have hmap := hmon.map' (MvPolynomial.aeval v).toLinearMap (LinearMap.ker_eq_bot.mpr halg)
  have hfun : (fun c : κ × Fin (q + 1) =>
        aeval v (monomial (expandedColumnExponent (q := q) exponent c) (1 : ℂ)))
      = ⇑(MvPolynomial.aeval v).toLinearMap ∘
          (⇑(MvPolynomial.basisMonomials (Option (Fin n)) ℂ) ∘
            (expandedColumnExponent (q := q) exponent)) := by
    funext c
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials]
  rw [hfun]
  exact hmap

/-- **Algebraic independence of the node coordinate and the jets makes the expanded monomial family
linearly independent** — for every exponent family with distinct exponents and every degree
budget. -/
theorem linearIndependent_expandedMonomialFamily_of_algebraicIndependent
    {κ : Type*} {n q : ℕ} {F : Fin n → ℂ → ℂ}
    (halg : AlgebraicIndependent ℂ (jetEvaluationFamily F))
    {exponent : κ → (Fin n →₀ ℕ)} (hexp : Function.Injective exponent) :
    LinearIndependent ℂ (expandedMonomialFamily F exponent q) := by
  have h := linearIndependent_aeval_expandedColumn_of_algebraicIndependent (q := q) halg hexp
  have hfun : expandedMonomialFamily F exponent q
      = fun c : κ × Fin (q + 1) =>
          aeval (jetEvaluationFamily F)
            (monomial (expandedColumnExponent (q := q) exponent c) (1 : ℂ)) :=
    funext fun c => expandedMonomialFamily_eq_aeval F exponent c
  rw [hfun]
  exact h

/-! ## Restriction to a region -/

/-- Restriction of functions to a set, as an algebra map. -/
def restrictAlgHom (Ω : Set ℂ) : (ℂ → ℂ) →ₐ[ℂ] (↥Ω → ℂ) where
  toFun := Set.restrict Ω
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- **Independence of the expanded family on a region**, from algebraic independence of the
restricted node coordinate and jets.  This is the form every consumer needs: the nodes are confined
to a region, and only the behaviour of the jets there is available. -/
theorem linearIndependent_restrict_expandedMonomialFamily_of_algebraicIndependent
    {κ : Type*} {n q : ℕ} {F : Fin n → ℂ → ℂ} {Ω : Set ℂ}
    (halg : AlgebraicIndependent ℂ (fun i => Set.restrict Ω (jetEvaluationFamily F i)))
    {exponent : κ → (Fin n →₀ ℕ)} (hexp : Function.Injective exponent) :
    LinearIndependent ℂ
      (fun c : κ × Fin (q + 1) => Set.restrict Ω (expandedMonomialFamily F exponent q c)) := by
  have h := linearIndependent_aeval_expandedColumn_of_algebraicIndependent (q := q) halg hexp
  have hfun : (fun c : κ × Fin (q + 1) =>
        Set.restrict Ω (expandedMonomialFamily F exponent q c))
      = fun c : κ × Fin (q + 1) =>
          aeval (fun i => Set.restrict Ω (jetEvaluationFamily F i))
            (monomial (expandedColumnExponent (q := q) exponent c) (1 : ℂ)) := by
    funext c
    rw [expandedMonomialFamily_eq_aeval F exponent c]
    have := MvPolynomial.comp_aeval (R := ℂ) (φ := restrictAlgHom Ω) (f := jetEvaluationFamily F)
    exact congrFun (congrArg (fun ψ : MvPolynomial (Option (Fin n)) ℂ →ₐ[ℂ] (↥Ω → ℂ) => ⇑ψ) this)
      (monomial (expandedColumnExponent (q := q) exponent c) (1 : ℂ))
  rw [hfun]
  exact h

/-- **The discharge.**  Algebraic independence of the node coordinate and the jets, together with
distinct exponents, produces an injective node packet on which the expanded evaluation map is
injective — the full-rank datum, with no analytic hypothesis left. -/
theorem exists_injective_node_packet_of_algebraicIndependent {κ : Type*} [Fintype κ]
    [DecidableEq κ] {n q : ℕ} {F : Fin n → ℂ → ℂ}
    (halg : AlgebraicIndependent ℂ (jetEvaluationFamily F))
    {exponent : κ → (Fin n →₀ ℕ)} (hexp : Function.Injective exponent) :
    ∃ z : κ × Fin (q + 1) → ℂ, Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec :=
  exists_injective_node_packet_mulVec_injective F exponent
    (linearIndependent_expandedMonomialFamily_of_algebraicIndependent halg hexp)


/-! ## The no-go: distinct nodes and nonvanishing monomials cannot suffice -/

/-- The one-jet family whose only jet is the node coordinate itself. -/
noncomputable def identityJet : Fin 1 → ℂ → ℂ := fun _ w => w

/-- Two exponents: the empty monomial and the first jet. -/
noncomputable def collidingExponent : Fin 2 → (Fin 1 →₀ ℕ) :=
  ![0, Finsupp.single 0 1]

/-- **The two columns are literally the same function.**  Degree one in the node equals the first
jet, because the jet *is* the node. -/
theorem expandedMonomialFamily_collision (w : ℂ) :
    expandedMonomialFamily identityJet collidingExponent 1 (0, 1) w =
      expandedMonomialFamily identityJet collidingExponent 1 (1, 0) w := by
  rw [expandedMonomialFamily_apply, expandedMonomialFamily_apply]
  simp [collidingExponent, identityJet]


/-- Applying a matrix to a standard basis vector reads off the corresponding column. -/
theorem mulVec_piSingle_apply {m N K : Type*} [Fintype N] [DecidableEq N] [CommRing K]
    (M : Matrix m N K) (j : N) (b : m) : M.mulVec (Pi.single j (1 : K)) b = M b j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- **Two coinciding columns of the family defeat every node packet.**  If the monomial functions of
two distinct columns agree, then for *every* choice of nodes — distinct or not, with monomial values
vanishing or not — the evaluation map has a nonzero kernel vector. -/
theorem not_injective_mulVec_of_expandedMonomialFamily_eq {κ row : Type*} [Fintype κ]
    [DecidableEq κ] {n q : ℕ} (F : Fin n → ℂ → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    {c c' : κ × Fin (q + 1)} (hne : c ≠ c')
    (heq : expandedMonomialFamily F exponent q c = expandedMonomialFamily F exponent q c')
    (z : row → ℂ) :
    ¬ Function.Injective
      (expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1))).mulVec := by
  classical
  intro hinj
  set M := expandedDifferentialEvaluationMatrix q n z exponent (fun p => F p.2 (z p.1)) with hM
  have hcol : ∀ b : row, M b c = M b c' := by
    intro b
    have h1 : M b c = expandedMonomialFamily F exponent q c (z b) := rfl
    have h2 : M b c' = expandedMonomialFamily F exponent q c' (z b) := rfl
    rw [h1, h2, heq]
  set v : κ × Fin (q + 1) → ℂ := Pi.single c 1 - Pi.single c' 1 with hvdef
  have hzero : M.mulVec v = M.mulVec 0 := by
    rw [hvdef]
    rw [Matrix.mulVec_sub, Matrix.mulVec_zero]
    funext b
    rw [Pi.sub_apply, mulVec_piSingle_apply, mulVec_piSingle_apply, hcol b, sub_self]
    rfl
  have hv := hinj hzero
  have hc : v c = 0 := by rw [hv]; rfl
  rw [hvdef] at hc
  rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, sub_zero] at hc
  exact one_ne_zero hc

/-- **The explicit no-go.**  With a single jet equal to the node coordinate itself and the two
exponents `0` and `X₀`, no node packet whatsoever makes the expanded evaluation map injective —
even though the nodes may be pairwise distinct and every monomial value nonzero. -/
theorem not_injective_mulVec_collidingExponent {row : Type*} (z : row → ℂ) :
    ¬ Function.Injective
      (expandedDifferentialEvaluationMatrix 1 1 z collidingExponent
        (fun p => identityJet p.2 (z p.1))).mulVec := by
  refine not_injective_mulVec_of_expandedMonomialFamily_eq identityJet collidingExponent
    (c := (0, 1)) (c' := (1, 0)) ?_ (funext expandedMonomialFamily_collision) z
  exact fun h => Fin.zero_ne_one (congrArg Prod.fst h)

end GaloisForLFunctions.HTGeometry
