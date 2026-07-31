import GaloisForLFunctions.HTGeometry.PencilExponentialSeed
import GaloisForLFunctions.HTGeometry.ExponentialBlockSeedFaithful
import GaloisForLFunctions.HTGeometry.EntireSRRealization

/-!
# The exact Stanley–Reisner kernel of a periodic-pencil realization

A **periodic-pencil separation** of a facet family gives, for each facet `A`, an additive phase
`L_A` covering `ℂ` such that the steps *outside* `A` are invisible to it — `exp (L_A (ω v)) = 1` —
while the steps *inside* `A` are integrally independent modulo that invisibility.  The associated
source is one exponential seed per facet,

```text
F(z) = ∑_{A ∈ Fac} exp (exp (L_A z)).
```

Every nonface product of difference operators annihilates `F`, because a nonface leaves every facet
and the escaping step is a period of that facet's seed.  Conversely a polynomial whose carrier is
constant lies in the Stanley–Reisner ideal: multiplying by one escaping variable per *other* facet
isolates a single seed, `exp ∘ L_A` covers the punctured plane, so all symbols of positive level
vanish, and integral independence inside `A` makes the symbol nodes pairwise distinct, so a
Vandermonde induction kills every coefficient supported in `A`.

* `PencilSeparation` — the datum;
* `pencilSeed` — the source;
* `seedAnnihilates_pencilSeed` — one half of the exact kernel;
* `exists_ne_seedCarrierPoly_pencilSeed` — the other half, in nonconstancy form;
* `pencilEntireSRRealization` — the entire `d`-variable realization it produces.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- **A periodic-pencil separation.**  Steps together with, for every facet, an additive phase whose
kernel modulo `2πiℤ` contains exactly the steps the facet omits. -/
structure PencilSeparation (facets : Finset (Finset α)) (E : Type*) [AddCommMonoid E] where
  /-- The translation step of each vertex. -/
  ω : α → E
  /-- The normalized phase of each facet. -/
  phase : Finset α → (E →+ ℂ)
  /-- Each phase covers the plane. -/
  phase_surjective : ∀ A ∈ facets, Function.Surjective (phase A)
  /-- A step outside a facet is a period of that facet's phase. -/
  outside : ∀ A ∈ facets, ∀ v ∉ A, Complex.exp (phase A (ω v)) = 1
  /-- The steps inside a facet are integrally independent modulo the periods. -/
  inside : ∀ A ∈ facets, ∀ g : α → ℤ,
    Complex.exp (∑ v ∈ A, (g v : ℂ) * phase A (ω v)) = 1 → ∀ v ∈ A, g v = 0

namespace PencilSeparation

variable {facets : Finset (Finset α)} {E : Type*} [AddCommMonoid E]

/-- **The pencil source:** one exponential seed per facet. -/
def seed (S : PencilSeparation facets E) : E → ℂ :=
  fun z => ∑ A ∈ facets, expSeedHom (S.phase A) z

omit [DecidableEq α] in
/-- A step outside a facet leaves that facet's seed invariant. -/
theorem shiftAlgHom_stepVar_expSeedHom (S : PencilSeparation facets E) {A : Finset α}
    (hA : A ∈ facets) {v : α} (hv : v ∉ A) :
    shiftAlgHom (stepVar S.ω v) (expSeedHom (S.phase A)) = 0 := by
  funext z
  rw [shiftAlgHom_stepVar]
  show Complex.exp (Complex.exp (S.phase A (z + S.ω v)))
    - Complex.exp (Complex.exp (S.phase A z)) = 0
  rw [map_add, Complex.exp_add, S.outside A hA v hv, mul_one, sub_self]

/-- **The nonface products annihilate the pencil source.** -/
theorem seedAnnihilates (S : PencilSeparation facets E) :
    SeedAnnihilates S.ω facets S.seed := by
  intro J hJ
  have hzero : ∀ A ∈ facets,
      shiftAlgHom (∏ v ∈ J, stepVar S.ω v) (expSeedHom (S.phase A)) = 0 := by
    intro A hA
    obtain ⟨v, hvJ, hvA⟩ : ∃ v ∈ J, v ∉ A := by
      by_contra hcon
      exact hJ ⟨A, Finset.mem_coe.mpr hA, by
        intro x hx
        by_contra hxA
        exact hcon ⟨x, hx, hxA⟩⟩
    have hfac : (∏ u ∈ J, stepVar S.ω u)
        = (∏ u ∈ J.erase v, stepVar S.ω u) * stepVar S.ω v := by
      rw [mul_comm, Finset.mul_prod_erase J _ hvJ]
    rw [hfac, map_mul]
    show shiftAlgHom (∏ u ∈ J.erase v, stepVar S.ω u)
      (shiftAlgHom (stepVar S.ω v) (expSeedHom (S.phase A))) = 0
    rw [S.shiftAlgHom_stepVar_expSeedHom hA hvA, map_zero]
  have hfun : S.seed = ∑ A ∈ facets, expSeedHom (S.phase A) := by
    funext w
    rw [Finset.sum_apply]
    rfl
  show shiftAlgHom (∏ v ∈ J, stepVar S.ω v) S.seed = 0
  rw [hfun, map_sum]
  exact Finset.sum_eq_zero hzero

/-- After multiplying by one escaping variable per other facet, only one seed survives. -/
theorem seedCarrierPoly_isolate (S : PencilSeparation facets E) {A : Finset α} (hA : A ∈ facets)
    (sel : {x // x ∈ facets.erase A} → α)
    (hsel : ∀ B : {x // x ∈ facets.erase A}, sel B ∉ (B : Finset α))
    (P : MvPolynomial α ℂ) (z : E) :
    seedCarrierPoly S.ω S.seed ((∏ B : {x // x ∈ facets.erase A}, X (sel B)) * P) z
      = seedCarrierPoly S.ω (expSeedHom (S.phase A))
        ((∏ B : {x // x ∈ facets.erase A}, X (sel B)) * P) z := by
  classical
  set D : MvPolynomial α ℂ := ∏ B : {x // x ∈ facets.erase A}, X (sel B) with hD
  have hfun : S.seed = fun w => ∑ A' ∈ facets, expSeedHom (S.phase A') w := rfl
  rw [hfun, seedCarrierPoly_sum, ← Finset.add_sum_erase facets _ hA]
  have hvanish : ∀ A' ∈ facets.erase A,
      seedCarrierPoly S.ω (expSeedHom (S.phase A')) (D * P) z = 0 := by
    intro A' hA'
    set B : {x // x ∈ facets.erase A} := ⟨A', hA'⟩ with hB
    have hmem : B ∈ (Finset.univ : Finset {x // x ∈ facets.erase A}) := Finset.mem_univ B
    have hfac : D * P = ((∏ C ∈ (Finset.univ : Finset {x // x ∈ facets.erase A}).erase B,
        X (sel C)) * P) * X (sel B) := by
      rw [hD, ← Finset.mul_prod_erase _ _ hmem]
      ring
    have hz : seedCarrierPoly S.ω (expSeedHom (S.phase A')) (X (sel B)) = 0 := by
      show shiftAlgHom (polyShift S.ω (X (sel B))) (expSeedHom (S.phase A')) = 0
      rw [polyShift_X]
      exact S.shiftAlgHom_stepVar_expSeedHom (Finset.mem_of_mem_erase hA') (hsel B)
    rw [hfac, seedCarrierPoly_mul, hz, map_zero]
    rfl
  rw [Finset.sum_eq_zero hvanish, add_zero]

/-! ### The symbol nodes of a facet -/

/-- The ratio character of a vertex relative to a facet phase. -/
def ratio (S : PencilSeparation facets E) (A : Finset α) (j : α) : ℂ :=
  Complex.exp (S.phase A (S.ω j))

omit [DecidableEq α] in
theorem ratio_pow (S : PencilSeparation facets E) (A : Finset α) (j : α) (m : ℕ) :
    S.ratio A j ^ m = Complex.exp ((m : ℂ) * S.phase A (S.ω j)) := by
  rw [ratio, ← Complex.exp_nat_mul]

omit [DecidableEq α] in
theorem ratio_eq_one (S : PencilSeparation facets E) {A : Finset α} (hA : A ∈ facets) {j : α}
    (hj : j ∉ A) : S.ratio A j = 1 := S.outside A hA j hj

omit [DecidableEq α] in
/-- A ratio character inside a facet is not a root of unity. -/
theorem ratio_pow_ne_one (S : PencilSeparation facets E) {A : Finset α} (hA : A ∈ facets) {v : α}
    (hv : v ∈ A) {m : ℕ} (hm : 1 ≤ m) : S.ratio A v ^ m ≠ 1 := by
  classical
  intro hone
  rw [ratio_pow] at hone
  set g : α → ℤ := fun u => if u = v then (m : ℤ) else 0 with hg
  have hsum : (∑ u ∈ A, (g u : ℂ) * S.phase A (S.ω u)) = (m : ℂ) * S.phase A (S.ω v) := by
    rw [Finset.sum_eq_single v]
    · rw [hg]
      simp
    · intro b _ hb
      rw [hg]
      simp [hb]
    · intro hcon
      exact absurd hv hcon
  have hv0 := S.inside A hA g (by rw [hsum]; exact hone) v hv
  simp only [hg] at hv0
  simp at hv0
  omega

/-- The Vandermonde node attached to an exponent. -/
def node (S : PencilSeparation facets E) (A : Finset α) (ν : α →₀ ℕ) : ℂ :=
  ∏ i ∈ ν.support, S.ratio A i ^ ν i

omit [DecidableEq α] in
theorem node_ne_zero (S : PencilSeparation facets E) (A : Finset α) (ν : α →₀ ℕ) :
    S.node A ν ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

omit [DecidableEq α] in
theorem node_eq_exp (S : PencilSeparation facets E) (A : Finset α) (ν : α →₀ ℕ) :
    S.node A ν = Complex.exp (∑ i ∈ ν.support, (ν i : ℂ) * S.phase A (S.ω i)) := by
  rw [node, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ratio, ← Complex.exp_nat_mul]

omit [DecidableEq α] in
/-- **The nodes separate exponents supported in the facet.** -/
theorem node_injective (S : PencilSeparation facets E) {A : Finset α} (hA : A ∈ facets)
    {ν ν' : α →₀ ℕ} (hν : ν.support ⊆ A) (hν' : ν'.support ⊆ A)
    (heq : S.node A ν = S.node A ν') : ν = ν' := by
  classical
  rw [node_eq_exp, node_eq_exp] at heq
  set g : α → ℤ := fun v => (ν v : ℤ) - (ν' v : ℤ) with hg
  have hsum1 : ∑ i ∈ A, (ν i : ℂ) * S.phase A (S.ω i)
      = ∑ i ∈ ν.support, (ν i : ℂ) * S.phase A (S.ω i) := by
    refine (Finset.sum_subset hν ?_).symm
    intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx]
    simp
  have hsum2 : ∑ i ∈ A, (ν' i : ℂ) * S.phase A (S.ω i)
      = ∑ i ∈ ν'.support, (ν' i : ℂ) * S.phase A (S.ω i) := by
    refine (Finset.sum_subset hν' ?_).symm
    intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx]
    simp
  have hone : Complex.exp (∑ v ∈ A, (g v : ℂ) * S.phase A (S.ω v)) = 1 := by
    have hsplit : (∑ v ∈ A, (g v : ℂ) * S.phase A (S.ω v))
        = (∑ v ∈ A, (ν v : ℂ) * S.phase A (S.ω v))
          - ∑ v ∈ A, (ν' v : ℂ) * S.phase A (S.ω v) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hg]
      push_cast
      ring
    rw [hsplit, hsum1, hsum2, Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]
  have hzero := S.inside A hA g hone
  ext v
  by_cases hvA : v ∈ A
  · have hgv := hzero v hvA
    rw [hg] at hgv
    omega
  · have h1 : ν v = 0 := Finsupp.notMem_support_iff.mp fun hc => hvA (hν hc)
    have h2 : ν' v = 0 := Finsupp.notMem_support_iff.mp fun hc => hvA (hν' hc)
    rw [h1, h2]

/-! ### Faithfulness -/

/-- **A polynomial with constant carrier lies in the Stanley–Reisner ideal.**  Equivalently, every
class outside the ideal has a nonconstant carrier. -/
theorem exists_ne_seedCarrierPoly (S : PencilSeparation facets E)
    (hanti : FacetAntichain (↑facets : Set (Finset α)))
    (P : MvPolynomial α ℂ) (hP : P ∉ stanleyReisnerIdeal ℂ facets) :
    ∃ x y, seedCarrierPoly S.ω S.seed P x ≠ seedCarrierPoly S.ω S.seed P y := by
  classical
  obtain ⟨d₀, hd₀P, hface⟩ : ∃ d ∈ P.support,
      IsFaceOf (↑facets : Set (Finset α)) d.support := by
    by_contra hcon
    exact hP ((mem_stanleyReisnerIdeal_iff _ P).mpr fun d hd hf => hcon ⟨d, hd, hf⟩)
  obtain ⟨A, hAmem, hd₀A⟩ := hface
  have hA : A ∈ facets := Finset.mem_coe.mp hAmem
  by_contra hcontra
  have hconst : ∀ x y : E, seedCarrierPoly S.ω S.seed P x = seedCarrierPoly S.ω S.seed P y := by
    intro x y
    by_contra hxy
    exact hcontra ⟨x, y, hxy⟩
  -- one escaping vertex per other facet
  have hex : ∀ B : {x // x ∈ facets.erase A}, ∃ v, v ∈ A ∧ v ∉ (B : Finset α) := by
    intro B
    obtain ⟨hBA, hBmem⟩ := Finset.mem_erase.mp B.2
    by_contra hcon
    have hsub : A ⊆ (B : Finset α) := by
      intro x hx
      by_contra hxB
      exact hcon ⟨x, hx, hxB⟩
    exact hBA (hanti hAmem (Finset.mem_coe.mpr hBmem) hsub).symm
  choose sel hselA hselB using hex
  set D : MvPolynomial α ℂ := ∏ B : {x // x ∈ facets.erase A}, X (sel B) with hD
  -- isolate the facet A
  have hDconst : ∀ z z' : E, seedCarrierPoly S.ω (expSeedHom (S.phase A)) (D * P) z
      = seedCarrierPoly S.ω (expSeedHom (S.phase A)) (D * P) z' := by
    have hC : seedCarrierPoly S.ω S.seed P = fun _ => seedCarrierPoly S.ω S.seed P 0 := by
      funext z
      exact hconst z 0
    intro z z'
    rw [← S.seedCarrierPoly_isolate hA sel hselB P z,
      ← S.seedCarrierPoly_isolate hA sel hselB P z',
      seedCarrierPoly_mul, hC, shiftAlgHom_const]
  have hsymb : ∀ m : ℕ, 1 ≤ m → symbHom S.ω (S.phase A) (m : ℂ) P = 0 := by
    intro m hm
    have hall := symbHom_eq_zero_of_carrier_const S.ω (S.phase_surjective A hA) (D * P)
      hDconst hm
    rw [symbHom_mul] at hall
    have hDs : symbHom S.ω (S.phase A) (m : ℂ) D ≠ 0 := by
      rw [hD, symbHom, map_prod]
      refine Finset.prod_ne_zero_iff.mpr fun B _ => ?_
      rw [aeval_X]
      intro hzero
      refine S.ratio_pow_ne_one hA (hselA B) hm ?_
      rw [ratio_pow]
      exact sub_eq_zero.mp hzero
    exact (mul_eq_zero.mp hall).resolve_left hDs
  -- restrict and translate
  set Q : MvPolynomial α ℂ := restrictPoly A P with hQ
  set Qt : MvPolynomial α ℂ := bind₁ (fun j => X j - 1) Q with hQt
  have hXsub : ∀ i : α, ((X i : MvPolynomial α ℂ) - 1).vars ⊆ ({i} : Finset α) := by
    intro i
    have hrw : (X i : MvPolynomial α ℂ) - 1 = X i + C (-1 : ℂ) := by
      rw [map_neg, map_one]
      ring
    rw [hrw]
    refine (vars_add_subset _ _).trans ?_
    rw [vars_C, Finset.union_empty, vars_X]
  have hvarsQt : Qt.vars ⊆ A := by
    refine (vars_bind₁ _ _).trans ?_
    refine Finset.biUnion_subset.mpr fun i hi => ?_
    refine (hXsub i).trans ?_
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact vars_restrictPoly A P hi
  have hsuppQt : ∀ ν ∈ Qt.support, ν.support ⊆ A := by
    intro ν hν x hx
    exact hvarsQt (mem_vars_iff_mem_support x |>.mpr ⟨ν, hν, hx⟩)
  have heval : ∀ m : ℕ, 1 ≤ m →
      ∑ ν ∈ Qt.support, coeff ν Qt * (S.node A ν) ^ m = 0 := by
    intro m hm
    have h1 : eval (fun j => S.ratio A j ^ m) Qt
        = ∑ ν ∈ Qt.support, coeff ν Qt * (S.node A ν) ^ m := by
      rw [MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl fun ν _ => ?_
      congr 1
      rw [node, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [pow_right_comm]
    have h2 : eval (fun j => S.ratio A j ^ m) Qt
        = eval (fun j => S.ratio A j ^ m - 1) Q := by
      rw [hQt, ← aeval_eq_eval', aeval_bind₁]
      refine congrArg (fun f => (aeval f) Q) ?_
      funext i
      rw [map_sub, aeval_X, map_one]
    have h3 : eval (fun j => S.ratio A j ^ m - 1) Q
        = eval (fun j => S.ratio A j ^ m - 1) P := by
      refine eval_restrictPoly P ?_
      intro j hj
      rw [S.ratio_eq_one hA hj, one_pow, sub_self]
    have h4 : eval (fun j => S.ratio A j ^ m - 1) P
        = symbHom S.ω (S.phase A) (m : ℂ) P := by
      rw [symbHom, aeval_eq_eval']
      refine congrArg (fun f => eval f P) ?_
      funext j
      rw [ratio_pow]
    rw [← h1, h2, h3, h4, hsymb m hm]
  have hcoeff : ∀ ν ∈ Qt.support, coeff ν Qt = 0 := by
    refine exponentialSum_coeff_eq_zero (S.node A) Qt.support ?_ ?_ _ heval
    · intro ν hν ν' hν' hzz
      exact S.node_injective hA (hsuppQt ν (Finset.mem_coe.mp hν))
        (hsuppQt ν' (Finset.mem_coe.mp hν')) hzz
    · intro ν _
      exact S.node_ne_zero A ν
  have hQt0 : Qt = 0 := by
    ext ν
    by_cases hν : ν ∈ Qt.support
    · rw [hcoeff ν hν, coeff_zero]
    · rw [MvPolynomial.notMem_support_iff.mp hν, coeff_zero]
  have hQ0 : Q = 0 := by
    have hback : bind₁ (fun j => (X j : MvPolynomial α ℂ) + 1) Qt = Q := by
      rw [hQt, bind₁_bind₁]
      have hid : (fun i => bind₁ (fun j => (X j : MvPolynomial α ℂ) + 1) (X i - 1))
          = fun i : α => (X i : MvPolynomial α ℂ) := by
        funext i
        simp
      rw [hid, bind₁_X_left]
      rfl
    rw [← hback, hQt0, map_zero]
  have hc0 : coeff d₀ P = 0 := by
    rw [← coeff_restrictPoly P hd₀A, ← hQ, hQ0, coeff_zero]
  exact (MvPolynomial.mem_support_iff.mp hd₀P) hc0

end PencilSeparation

end

end GaloisForLFunctions.HTGeometry
