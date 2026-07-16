import Mathlib.Tactic

/-!
# First Koszul differentials for difference cohomology

`multi-q-difference-galois-foundations.md` §20 identifies difference cohomology with the
Koszul complex on the commuting operators `(σ_p - 1)`. This file formalizes the first
two differentials for an arbitrary additive coefficient group with commuting additive
endomorphisms:

* `d₀ x = (σ_p x - x)_p`;
* `d₁ c = ((σ_p - 1)c_q - (σ_q - 1)c_p)_{p,q}`;
* `d₀ x = 0` iff `x` is jointly invariant;
* additive coboundaries are additive 1-cocycles, equivalently `d₁ ∘ d₀ = 0`.

It deliberately does not formalize group cohomology, the quotient defining `H¹`, exterior
powers, cup products, the infinite prime-lattice limit, or the `H²` curvature obstruction.
Those remain draft-side structures until a larger formal cohomology framework is built.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The additive difference actions commute pairwise. -/
def commutingAdditiveActions {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) : Prop :=
  ∀ p q x, act p (act q x) = act q (act p x)

/-- Joint invariants for an additive family of difference actions. -/
def additiveInvariant {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) (x : M) : Prop :=
  ∀ p, act p x = x

/-- The first Koszul differential `d₀ x = (σ_p x - x)_p`. -/
def koszulD0 {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) (x : M) : ι → M :=
  fun p => act p x - x

/-- The kernel of the first Koszul differential is exactly the joint invariant subspace. -/
@[aesop norm simp]
theorem koszulD0_eq_zero_iff_invariant {ι M : Type*} [AddCommGroup M]
    (act : ι → M →+ M) (x : M) :
    koszulD0 act x = 0 ↔ additiveInvariant act x := by
  constructor
  · intro h p
    exact sub_eq_zero.mp (congr_fun h p)
  · intro h
    ext p
    exact sub_eq_zero.mpr (h p)

/-- Additive 1-cocycles: `(σ_p - 1)c_q = (σ_q - 1)c_p`. -/
def additiveCocycle {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) (c : ι → M) :
    Prop :=
  ∀ p q, act p (c q) - c q = act q (c p) - c p

/-- The second Koszul differential on a 1-cochain. -/
def koszulD1 {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) (c : ι → M) :
    ι → ι → M :=
  fun p q => (act p (c q) - c q) - (act q (c p) - c p)

/-- Vanishing of the second Koszul differential is exactly the additive 1-cocycle condition. -/
@[aesop norm simp]
theorem koszulD1_eq_zero_iff_additiveCocycle {ι M : Type*} [AddCommGroup M]
    (act : ι → M →+ M) (c : ι → M) :
    (∀ p q, koszulD1 act c p q = 0) ↔ additiveCocycle act c := by
  constructor
  · intro h p q
    exact sub_eq_zero.mp (h p q)
  · intro h p q
    exact sub_eq_zero.mpr (h p q)

/-- The additive Koszul coboundary `δh = (σ_p h - h)_p`. -/
def koszulCoboundary {ι M : Type*} [AddCommGroup M] (act : ι → M →+ M) (h : M) :
    ι → M :=
  koszulD0 act h

/-- Additive coboundaries are additive 1-cocycles when the difference actions commute. -/
@[aesop safe]
theorem koszulCoboundary_cocycle {ι M : Type*} [AddCommGroup M]
    {act : ι → M →+ M} (hcomm : commutingAdditiveActions act) (h : M) :
    additiveCocycle act (koszulCoboundary act h) := by
  intro p q
  dsimp [koszulCoboundary, koszulD0]
  rw [map_sub, map_sub, hcomm p q h]
  abel

/-- The first two Koszul differentials compose to zero: `d₁ (d₀ h) = 0`. -/
@[aesop safe]
theorem koszulD1_koszulD0_eq_zero {ι M : Type*} [AddCommGroup M]
    {act : ι → M →+ M} (hcomm : commutingAdditiveActions act) (h : M) :
    ∀ p q, koszulD1 act (koszulD0 act h) p q = 0 := by
  exact (koszulD1_eq_zero_iff_additiveCocycle act (koszulD0 act h)).mpr
    (by simpa [koszulCoboundary] using koszulCoboundary_cocycle hcomm h)

/-- The alternating binomial count underlying the finite Koszul Euler characteristic. -/
@[aesop safe]
theorem koszul_alternating_choose_sum_eq_zero (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (n.choose i : ℤ)) = 0 := by
  have h := add_pow (-1 : ℤ) 1 n
  have hzero : ((-1 : ℤ) + 1) ^ n = 0 := by
    simp [Nat.ne_of_gt hn]
  rw [hzero] at h
  simpa [mul_assoc] using h.symm

/-- The finite Koszul rank Euler characteristic vanishes for a nonempty finite operator set:
`dim M · Σ_i (-1)^i choose(n,i) = 0`. This is only the rank count of the complex terms, not a
claim about individual cohomology dimensions. -/
@[aesop safe]
theorem koszul_euler_characteristic_eq_zero (n dimM : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (n.choose i : ℤ) * (dimM : ℤ)) = 0 := by
  rw [← Finset.sum_mul]
  rw [koszul_alternating_choose_sum_eq_zero n hn]
  simp

/-! ### The local-factor superdeterminant exponent -/

/-- The exponent with which one fixed direction occurs in the alternating determinant of an
`n`-direction Koszul grading.  In exterior degree `k`, the fixed direction has
`choose (n - 1) k` complementary copies. -/
def koszulComplementSuperExponent (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k * ((n - 1).choose k : ℤ)

/-- In a one-direction Koszul grading the unique local determinant survives with exponent one. -/
@[aesop norm simp]
theorem koszulComplementSuperExponent_one :
    koszulComplementSuperExponent 1 = 1 := by
  norm_num [koszulComplementSuperExponent]

/-- **Multi-direction Koszul cancellation.**  Once there are at least two commuting directions,
the alternating determinant exponent of every fixed local factor is zero.  Thus an absolute
Koszul superdeterminant cancels the pure local factors together with the mixed terms; a relative
or augmented boundary is necessary if an Euler factor is to survive. -/
@[aesop safe]
theorem koszulComplementSuperExponent_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    koszulComplementSuperExponent n = 0 := by
  have hpos : 0 < n - 1 := by omega
  have hsum := koszul_alternating_choose_sum_eq_zero (n - 1) hpos
  simpa [koszulComplementSuperExponent, Nat.sub_add_cancel (by omega : 1 ≤ n)] using hsum

/-! ### A marked-support successor -/

/-- Mark one active direction and take the alternating Koszul exponent over its complement.
The factor `n` counts the possible marked directions.  Unlike the absolute ambient Koszul
superdeterminant, this support-sensitive incidence weight is attached to the directions actually
used by a word. -/
def koszulSupportMarkedExponent (n : ℕ) : ℤ :=
  (n : ℤ) * koszulComplementSuperExponent n

/-- **Singleton-support selector.**  The marked incidence exponent is one on a pure word (exactly
one active prime direction) and zero on both the empty support and every mixed-prime support.
This is the combinatorial shape required of a graded prime-word boundary: it retains pure prime
repetitions while cancelling mixed words, without requiring the prime sectors to be orthogonal.
The remaining problem is to realize this support-sensitive weight by a source-defined closed
relative determinant. -/
@[aesop norm simp]
theorem koszulSupportMarkedExponent_eq (n : ℕ) :
    koszulSupportMarkedExponent n = if n = 1 then 1 else 0 := by
  by_cases h0 : n = 0
  · simp [h0, koszulSupportMarkedExponent, koszulComplementSuperExponent]
  by_cases h1 : n = 1
  · subst n
    rw [if_pos rfl, koszulSupportMarkedExponent, koszulComplementSuperExponent_one]
    norm_num
  have hn : 2 ≤ n := by omega
  rw [if_neg h1, koszulSupportMarkedExponent, koszulComplementSuperExponent_eq_zero hn, mul_zero]

/-- A word with at least two active directions has zero marked-support exponent. -/
@[aesop safe]
theorem koszulSupportMarkedExponent_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    koszulSupportMarkedExponent n = 0 := by
  rw [koszulSupportMarkedExponent_eq, if_neg (by omega)]

/-- A one-direction word retains exponent one. -/
@[aesop norm simp]
theorem koszulSupportMarkedExponent_one :
    koszulSupportMarkedExponent 1 = 1 := by
  exact koszulSupportMarkedExponent_eq 1

/-! ### The first Hochster source-coherence class

The Stanley--Reisner boundary consisting of two isolated vertices has coordinate ring
`F[x] x_F F[y]`: two affine axes glued at their common origin.  The following fibre-product
presentation makes its first positive Koszul class completely explicit without assuming a
general Hochster formula. -/

/-- The nodal Stanley--Reisner boundary `F[x] x_F F[y]`, presented as pairs of polynomials with
the same value at the common origin. -/
def nodalBoundarySubring (F : Type*) [Field F] : Subalgebra F (Polynomial F × Polynomial F) where
  carrier := {p | p.1.coeff 0 = p.2.coeff 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro ⟨p, q⟩ ⟨r, s⟩ hpq hrs
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Polynomial.coeff_add]
    rw [hpq, hrs]
  mul_mem' := by
    rintro ⟨p, q⟩ ⟨r, s⟩ hpq hrs
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, Polynomial.mul_coeff_zero]
    rw [hpq, hrs]
  algebraMap_mem' := by simp

/-- The coordinate on the first irreducible axis of the nodal boundary. -/
def nodalBoundaryX {F : Type*} [Field F] : nodalBoundarySubring F :=
  ⟨(Polynomial.X, 0), by
    change Polynomial.X.coeff 0 = (0 : Polynomial F).coeff 0
    simp [Polynomial.coeff_X]⟩

/-- The coordinate on the second irreducible axis of the nodal boundary. -/
def nodalBoundaryY {F : Type*} [Field F] : nodalBoundarySubring F :=
  ⟨(0, Polynomial.X), by
    change (0 : Polynomial F).coeff 0 = Polynomial.X.coeff 0
    simp [Polynomial.coeff_X]⟩

/-- The two nodal coordinates have zero product: the missing edge is the squarefree relation
`xy=0`. -/
@[simp]
theorem nodalBoundaryX_mul_Y {F : Type*} [Field F] :
    nodalBoundaryX (F := F) * nodalBoundaryY (F := F) = 0 := by
  apply Subtype.ext
  ext <;> simp [nodalBoundaryX, nodalBoundaryY]

/-- The first Koszul relation map for the two nodal coordinates. -/
def nodalKoszulRelation {F : Type*} [Field F]
    (a : Fin 2 → nodalBoundarySubring F) : nodalBoundarySubring F :=
  a 0 * nodalBoundaryX + a 1 * nodalBoundaryY

/-- The canonical cycle supported on the disconnected second vertex. -/
def nodalDisconnectCycle {F : Type*} [Field F] : Fin 2 → nodalBoundarySubring F :=
  ![nodalBoundaryY, 0]

/-- Degree-two Koszul boundaries for the two nodal coordinates. -/
def nodalKoszulBoundary {F : Type*} [Field F]
    (c : nodalBoundarySubring F) : Fin 2 → nodalBoundarySubring F :=
  ![-c * nodalBoundaryY, c * nodalBoundaryX]

/-- The disconnected-vertex class is a genuine first Koszul cycle. -/
@[simp]
theorem nodalKoszulRelation_disconnectCycle {F : Type*} [Field F] :
    nodalKoszulRelation (nodalDisconnectCycle (F := F)) = 0 := by
  change nodalBoundaryY * nodalBoundaryX + 0 * nodalBoundaryY = 0
  simp [mul_comm]

/-- Every displayed degree-two boundary is a first Koszul cycle. -/
@[simp]
theorem nodalKoszulRelation_boundary {F : Type*} [Field F]
    (c : nodalBoundarySubring F) :
    nodalKoszulRelation (nodalKoszulBoundary c) = 0 := by
  change (-c * nodalBoundaryY) * nodalBoundaryX +
    (c * nodalBoundaryX) * nodalBoundaryY = 0
  ring

/-- **First unconditional Hochster class.**  The cycle carried by the disconnected nodal
constraint boundary is not a Koszul boundary.  This is the explicit algebraic representative of
the one-dimensional reduced `H^0` of two isolated vertices. -/
theorem nodalDisconnectCycle_not_koszulBoundary {F : Type*} [Field F] :
    ¬ ∃ c : nodalBoundarySubring F,
      nodalKoszulBoundary c = nodalDisconnectCycle := by
  rintro ⟨c, hc⟩
  have hzero := congrFun hc (0 : Fin 2)
  have hone := congrFun hc (1 : Fin 2)
  have hfirstMul : c.1.1 * Polynomial.X = 0 := by
    have h := congrArg
      (fun z : nodalBoundarySubring F =>
        ((z : Polynomial F × Polynomial F).1)) hone
    simpa [nodalKoszulBoundary, nodalDisconnectCycle, nodalBoundaryX,
      nodalBoundaryY] using h
  have hfirst : c.1.1 = 0 :=
    (mul_eq_zero.mp hfirstMul).resolve_right Polynomial.X_ne_zero
  have hsecondNegMul : -(c.1.2 * Polynomial.X) = Polynomial.X := by
    have h := congrArg
      (fun z : nodalBoundarySubring F =>
        ((z : Polynomial F × Polynomial F).2)) hzero
    simpa [nodalKoszulBoundary, nodalDisconnectCycle, nodalBoundaryX,
      nodalBoundaryY] using h
  have hsecondMul : c.1.2 * Polynomial.X = -Polynomial.X :=
    neg_eq_iff_eq_neg.mp hsecondNegMul
  have hfactor : (c.1.2 + 1) * Polynomial.X = 0 := by
    rw [add_mul, hsecondMul]
    simp
  have hsecondAdd : c.1.2 + 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right Polynomial.X_ne_zero
  have hsecond : c.1.2 = -1 := by
    calc
      c.1.2 = c.1.2 + 1 - 1 := by ring
      _ = -1 := by rw [hsecondAdd]; ring
  have hcompat : c.1.1.coeff 0 = c.1.2.coeff 0 := by
    exact c.2
  have horigin : (0 : F) = -1 := by
    simpa [hfirst, hsecond] using hcompat
  exact (zero_ne_one : (0 : F) ≠ 1) (by simpa using congrArg Neg.neg horigin)

/-! The same class in the actual squarefree quotient `F[x,y]/(xy)`.  Mapping the quotient into
the nodal fibre product is enough for nonboundary detection; no presentation isomorphism is
assumed. -/

/-- The principal nonedge ideal of two isolated vertices. -/
noncomputable def nodalNonedgeIdeal (F : Type*) [Field F] :
    Ideal (MvPolynomial (Fin 2) F) :=
  Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}

/-- The squarefree Stanley--Reisner quotient of two isolated vertices. -/
abbrev NodalStanleyReisnerRing (F : Type*) [Field F] :=
  MvPolynomial (Fin 2) F ⧸ nodalNonedgeIdeal F

/-- Evaluate the two squarefree coordinates on the two axes of the nodal fibre product. -/
def nodalBoundaryEvaluation {F : Type*} [Field F] :
    MvPolynomial (Fin 2) F →+* nodalBoundarySubring F :=
  MvPolynomial.eval₂Hom (algebraMap F (nodalBoundarySubring F))
    ![nodalBoundaryX, nodalBoundaryY]

/-- The missing-edge ideal vanishes on the nodal fibre product. -/
theorem nodalNonedgeIdeal_le_ker_boundaryEvaluation
    {F : Type*} [Field F] :
    nodalNonedgeIdeal F ≤ RingHom.ker (nodalBoundaryEvaluation (F := F)) := by
  rw [nodalNonedgeIdeal, Ideal.span_le]
  rintro _ ⟨rfl⟩
  simp [nodalBoundaryEvaluation]

/-- The canonical map from the actual Stanley--Reisner quotient to its nodal coordinate model. -/
def nodalStanleyReisnerBoundaryMap {F : Type*} [Field F] :
    NodalStanleyReisnerRing F →+* nodalBoundarySubring F :=
  Ideal.Quotient.lift (nodalNonedgeIdeal F) nodalBoundaryEvaluation
    (fun p hp => RingHom.mem_ker.mp
      (nodalNonedgeIdeal_le_ker_boundaryEvaluation hp))

/-- The first coordinate class in the nodal Stanley--Reisner quotient. -/
def nodalStanleyReisnerX {F : Type*} [Field F] : NodalStanleyReisnerRing F :=
  Ideal.Quotient.mk (nodalNonedgeIdeal F) (MvPolynomial.X 0)

/-- The second coordinate class in the nodal Stanley--Reisner quotient. -/
def nodalStanleyReisnerY {F : Type*} [Field F] : NodalStanleyReisnerRing F :=
  Ideal.Quotient.mk (nodalNonedgeIdeal F) (MvPolynomial.X 1)

@[simp]
theorem nodalStanleyReisnerBoundaryMap_X {F : Type*} [Field F] :
    nodalStanleyReisnerBoundaryMap (F := F) nodalStanleyReisnerX = nodalBoundaryX := by
  rw [nodalStanleyReisnerBoundaryMap, nodalStanleyReisnerX, Ideal.Quotient.lift_mk]
  simp [nodalBoundaryEvaluation]

@[simp]
theorem nodalStanleyReisnerBoundaryMap_Y {F : Type*} [Field F] :
    nodalStanleyReisnerBoundaryMap (F := F) nodalStanleyReisnerY = nodalBoundaryY := by
  rw [nodalStanleyReisnerBoundaryMap, nodalStanleyReisnerY, Ideal.Quotient.lift_mk]
  simp [nodalBoundaryEvaluation]

/-- The quotient-ring representative of the disconnected-vertex Koszul cycle. -/
def nodalStanleyReisnerDisconnectCycle {F : Type*} [Field F] :
    Fin 2 → NodalStanleyReisnerRing F :=
  ![nodalStanleyReisnerY, 0]

/-- Degree-two Koszul boundaries in the nodal Stanley--Reisner quotient. -/
def nodalStanleyReisnerKoszulBoundary {F : Type*} [Field F]
    (c : NodalStanleyReisnerRing F) : Fin 2 → NodalStanleyReisnerRing F :=
  ![-c * nodalStanleyReisnerY, c * nodalStanleyReisnerX]

/-- The quotient-ring cycle maps to the explicit nodal fibre-product cycle. -/
theorem nodalStanleyReisnerDisconnectCycle_map
    {F : Type*} [Field F] (i : Fin 2) :
    nodalStanleyReisnerBoundaryMap (F := F)
        (nodalStanleyReisnerDisconnectCycle i) =
      nodalDisconnectCycle i := by
  fin_cases i <;> simp [nodalStanleyReisnerDisconnectCycle, nodalDisconnectCycle]

/-- Quotient-ring Koszul boundaries map to nodal fibre-product Koszul boundaries. -/
theorem nodalStanleyReisnerKoszulBoundary_map
    {F : Type*} [Field F] (c : NodalStanleyReisnerRing F) (i : Fin 2) :
    nodalStanleyReisnerBoundaryMap (F := F)
        (nodalStanleyReisnerKoszulBoundary c i) =
      nodalKoszulBoundary (nodalStanleyReisnerBoundaryMap c) i := by
  fin_cases i <;> simp [nodalStanleyReisnerKoszulBoundary, nodalKoszulBoundary]

/-- **Stanley--Reisner Hochster seed.**  The disconnected-vertex cycle is not a boundary in the
actual squarefree quotient `F[x,y]/(xy)`. -/
theorem nodalStanleyReisnerDisconnectCycle_not_koszulBoundary
    {F : Type*} [Field F] :
    ¬ ∃ c : NodalStanleyReisnerRing F,
      nodalStanleyReisnerKoszulBoundary c =
        nodalStanleyReisnerDisconnectCycle := by
  rintro ⟨c, hc⟩
  apply nodalDisconnectCycle_not_koszulBoundary (F := F)
  refine ⟨nodalStanleyReisnerBoundaryMap c, ?_⟩
  funext i
  rw [← nodalStanleyReisnerKoszulBoundary_map c i,
    hc, nodalStanleyReisnerDisconnectCycle_map]

end

end GaloisForLFunctions
