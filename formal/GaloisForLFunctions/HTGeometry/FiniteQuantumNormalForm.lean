import GaloisForLFunctions.HTGeometry.FiniteQuantumWaringHorizon

/-!
# Ordered-monomial normal form for the finite quantum torus

The finite quantum packet `finiteQuantumGenerator` realizes the twisted group algebra
`K⟨g₁,…,g_n⟩ / (g_i^d = 1, g_i g_j = q g_j g_i for i < j)` on the cyclic phase space
`ι → ZMod d`.  This module proves its normal-form theorem: the ordered monomials
`g^a = ∏_{i asc} g_i^(a i)` with exponents `a : ι → ZMod d`

* act on states by an explicit nonzero phase times a translation
  (`finiteQuantumMonomial_apply`),
* contain the unit and every generator (`finiteQuantumMonomial_zero`,
  `finiteQuantumMonomial_single`),
* multiply by the twisted 2-cocycle `g^a g^b = χ(-⟨b, a⟩) • g^(a+b)`
  (`finiteQuantumMonomial_mul`), and
* are linearly independent (`finiteQuantumMonomial_linearIndependent`), hence form a basis
  of their span — the normal-form basis of the finite quantum torus.

Together with the already formalized root-of-unity quantum multinomial theorem this
discharges the promotion gate of the general Fermat extension: every Fermat hypersurface
`∑ c_i^d = 0` carries an exact finite-width hypertranscendence horizon with maximal
exterior commutator symbol and a certified normal-form basis
(`finiteQuantumFermat_normalForm_maximalHorizon`).
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]
  {ι : Type*} [Fintype ι] [LinearOrder ι]
  {d : ℕ} [NeZero d] [Fact (1 < d)]

/-- Iterating the additive character on a coordinate is multiplication by the natural
scalar. -/
theorem finiteQuantumCharacter_val_pow
    (q : K) (hq : q ^ d = 1) (x : ZMod d) (n : ℕ) :
    (finiteQuantumCharacter d q hq x) ^ n =
      finiteQuantumCharacter d q hq ((n : ZMod d) * x) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

/-- Every character value is nonzero. -/
theorem finiteQuantumCharacter_ne_zero
    (q : K) (hq : q ^ d = 1) (x : ZMod d) :
    finiteQuantumCharacter d q hq x ≠ 0 := by
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (Fact.out : 1 < d)))] at hq
    exact zero_ne_one hq
  rw [finiteQuantumCharacter, AddChar.zmodChar_apply]
  exact pow_ne_zero _ hq0

/-- Shifting coordinate `i` does not change the tail charge above `j ≥ i`. -/
theorem finiteQuantumTailCharge_shiftN_of_le
    {i j : ι} (hij : i ≤ j) (n : ℕ) (a : FiniteQuantumState ι d) :
    finiteQuantumTailCharge j (finiteQuantumShiftN n i a) =
      finiteQuantumTailCharge j a := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have hjk : j < k := by simpa using hk
  have hki : k ≠ i := ne_of_gt (lt_of_le_of_lt hij hjk)
  simp [finiteQuantumShiftN, hki]

/-- An `n`-fold coordinate shift is subtraction of a single vector. -/
theorem finiteQuantumShiftN_eq_sub_single
    (n : ℕ) (i : ι) (a : FiniteQuantumState ι d) :
    finiteQuantumShiftN n i a = a - Pi.single i (n : ZMod d) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [finiteQuantumShiftN, Pi.single_eq_same]
  · simp [finiteQuantumShiftN, hki, Pi.single_eq_of_ne]

/-- A single coordinate shift is subtraction of a unit vector. -/
theorem finiteQuantumShift_eq_sub_single
    (i : ι) (a : FiniteQuantumState ι d) :
    finiteQuantumShift i a = a - Pi.single i 1 := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [finiteQuantumShift, Pi.single_eq_same]
  · simp [finiteQuantumShift, hki, Pi.single_eq_of_ne]

/-- The tail charge is additive in the state. -/
theorem finiteQuantumTailCharge_sub
    (i : ι) (a b : FiniteQuantumState ι d) :
    finiteQuantumTailCharge i (a - b) =
      finiteQuantumTailCharge i a - finiteQuantumTailCharge i b := by
  classical
  simp [finiteQuantumTailCharge, Finset.sum_sub_distrib]

/-- The ordered monomial with exponent vector `a`: the increasing product of generator
powers. -/
def finiteQuantumMonomial
    (q : K) (hq : q ^ d = 1) (a : ι → ZMod d) :
    Module.End K (FiniteQuantumState ι d → K) :=
  ((Finset.univ.sort (· ≤ ·)).map fun i ↦
    (finiteQuantumGenerator d q hq i) ^ (a i).val).prod

/-- **Crux: ordered products act diagonally-phase times translation.**  Along any weakly
increasing list of generators, no translation disturbs a later tail charge, so the phase
factors stay coordinate-separated. -/
theorem finiteQuantumMonomial_list_apply
    (q : K) (hq : q ^ d = 1) (a : ι → ZMod d) (f : FiniteQuantumState ι d → K) :
    ∀ {l : List ι}, l.Pairwise (· ≤ ·) → ∀ (x : FiniteQuantumState ι d),
      ((l.map fun i ↦ (finiteQuantumGenerator d q hq i) ^ (a i).val).prod) f x =
        (l.map fun i ↦
          finiteQuantumCharacter d q hq (a i * finiteQuantumTailCharge i x)).prod *
          f (x - (l.map fun i ↦ Pi.single i (a i)).sum) := by
  intro l
  induction l with
  | nil =>
      intro _ x
      simp
  | cons i t ih =>
      intro hl x
      obtain ⟨hht, ht⟩ := List.pairwise_cons.mp hl
      have hmap : (t.map fun j ↦ finiteQuantumCharacter d q hq
            (a j * finiteQuantumTailCharge j (finiteQuantumShiftN (a i).val i x))) =
          (t.map fun j ↦
            finiteQuantumCharacter d q hq (a j * finiteQuantumTailCharge j x)) := by
        apply List.map_congr_left
        intro j hj
        rw [finiteQuantumTailCharge_shiftN_of_le (hht j hj)]
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [Module.End.mul_apply, finiteQuantumGenerator_pow_apply, ih ht,
        finiteQuantumCharacter_val_pow, finiteQuantumShiftN_eq_sub_single,
        ZMod.natCast_rightInverse, sub_sub, hmap, mul_assoc]

/-- Product over the increasingly sorted universe is the unordered finite product. -/
theorem finiteQuantumMonomial_sort_prod
    {M : Type*} [CommMonoid M] (g : ι → M) :
    ((Finset.univ.sort (· ≤ ·)).map g).prod = ∏ i, g i := by
  rw [show ∏ i, g i = (Finset.univ.1.map g).prod from rfl,
    ← Finset.sort_eq Finset.univ (· ≤ ·)]
  rfl

/-- Sum over the increasingly sorted universe is the unordered finite sum. -/
theorem finiteQuantumMonomial_sort_sum
    {M : Type*} [AddCommMonoid M] (g : ι → M) :
    ((Finset.univ.sort (· ≤ ·)).map g).sum = ∑ i, g i := by
  rw [show ∑ i, g i = (Finset.univ.1.map g).sum from rfl,
    ← Finset.sort_eq Finset.univ (· ≤ ·)]
  rfl

/-- The single vectors decompose every state. -/
theorem finiteQuantumState_sum_single (a : ι → ZMod d) :
    (∑ i, Pi.single i (a i)) = a := by
  funext j
  simp [Pi.single_apply]

/-- **Normal-form action formula.**  The ordered monomial `g^a` is a nonzero
coordinate-separated phase times translation by `a`. -/
theorem finiteQuantumMonomial_apply
    (q : K) (hq : q ^ d = 1) (a : ι → ZMod d)
    (f : FiniteQuantumState ι d → K) (x : FiniteQuantumState ι d) :
    (finiteQuantumMonomial q hq a) f x =
      (∏ i, finiteQuantumCharacter d q hq (a i * finiteQuantumTailCharge i x)) *
        f (x - a) := by
  unfold finiteQuantumMonomial
  rw [finiteQuantumMonomial_list_apply q hq a f
    (Finset.pairwise_sort Finset.univ (· ≤ ·)) x,
    finiteQuantumMonomial_sort_prod, finiteQuantumMonomial_sort_sum,
    finiteQuantumState_sum_single]

/-- The ordered monomial at exponent zero is the identity. -/
theorem finiteQuantumMonomial_zero (q : K) (hq : q ^ d = 1) :
    finiteQuantumMonomial q hq (0 : ι → ZMod d) = 1 := by
  apply LinearMap.ext
  intro f
  funext x
  rw [finiteQuantumMonomial_apply]
  simp

/-- The ordered monomial at a unit exponent vector is the corresponding generator. -/
theorem finiteQuantumMonomial_single (q : K) (hq : q ^ d = 1) (i : ι) :
    finiteQuantumMonomial q hq (Pi.single i 1) = finiteQuantumGenerator d q hq i := by
  apply LinearMap.ext
  intro f
  funext x
  rw [finiteQuantumMonomial_apply]
  have hphase : (∏ k, finiteQuantumCharacter d q hq
        ((Pi.single i 1) k * finiteQuantumTailCharge k x)) =
      finiteQuantumCharacter d q hq (finiteQuantumTailCharge i x) := by
    trans ∏ k, (if k = i then
      finiteQuantumCharacter d q hq (finiteQuantumTailCharge i x) else 1)
    · apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k = i
      · subst hk
        simp [Pi.single_eq_same, one_mul]
      · simp [Pi.single_eq_of_ne hk, zero_mul]
    · rw [Finset.prod_ite_eq', if_pos (Finset.mem_univ i)]
  rw [hphase, ← finiteQuantumShift_eq_sub_single]
  simp only [finiteQuantumGenerator, LinearMap.coe_mk, AddHom.coe_mk]

/-- **Twisted normal-form product law.**  Ordered monomials multiply by the 2-cocycle
`g^a g^b = χ(-⟨b,a⟩) • g^(a+b)` with `⟨b,a⟩ = ∑_i b_i · (tail charge of a above i)`. -/
theorem finiteQuantumMonomial_mul (q : K) (hq : q ^ d = 1) (a b : ι → ZMod d) :
    finiteQuantumMonomial q hq a * finiteQuantumMonomial q hq b =
      (∏ i, finiteQuantumCharacter d q hq (-(b i * finiteQuantumTailCharge i a))) •
        finiteQuantumMonomial q hq (a + b) := by
  apply LinearMap.ext
  intro f
  funext x
  have hprod : (∏ i, finiteQuantumCharacter d q hq
        (b i * finiteQuantumTailCharge i (x - a))) =
      (∏ i, finiteQuantumCharacter d q hq (b i * finiteQuantumTailCharge i x)) /
        (∏ i, finiteQuantumCharacter d q hq (b i * finiteQuantumTailCharge i a)) := by
    rw [Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [finiteQuantumTailCharge_sub, mul_sub, AddChar.map_sub_eq_div]
  have hC : (∏ i, finiteQuantumCharacter d q hq
        (-(b i * finiteQuantumTailCharge i a))) =
      (∏ i, finiteQuantumCharacter d q hq (b i * finiteQuantumTailCharge i a))⁻¹ := by
    rw [Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [AddChar.map_neg_eq_inv]
  have hsum : (∏ i, finiteQuantumCharacter d q hq
        ((a + b) i * finiteQuantumTailCharge i x)) =
      (∏ i, finiteQuantumCharacter d q hq (a i * finiteQuantumTailCharge i x)) *
        (∏ i, finiteQuantumCharacter d q hq (b i * finiteQuantumTailCharge i x)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Pi.add_apply, add_mul, AddChar.map_add_eq_mul]
  rw [Module.End.mul_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    finiteQuantumMonomial_apply q hq a (finiteQuantumMonomial q hq b f) x,
    finiteQuantumMonomial_apply q hq b f (x - a),
    finiteQuantumMonomial_apply q hq (a + b) f x,
    sub_sub, hprod, hC, hsum, div_eq_mul_inv]
  ac_rfl

/-- **Normal-form basis theorem.**  The ordered monomials of the finite quantum torus are
linearly independent: distinct exponent vectors send the origin delta state to distinct
phase-scaled basis states. -/
theorem finiteQuantumMonomial_linearIndependent (q : K) (hq : q ^ d = 1) :
    LinearIndependent K (finiteQuantumMonomial (K := K) (ι := ι) (d := d) q hq) := by
  apply LinearIndependent.of_comp
    (LinearMap.applyₗ (R := K) (finiteQuantumRoot (K := K) (ι := ι) (d := d)))
  have hb : LinearIndependent K (fun a : ι → ZMod d ↦
      (∏ i, finiteQuantumCharacter d q hq (a i * finiteQuantumTailCharge i a)) •
        Pi.basisFun K (FiniteQuantumState ι d) a) := by
    have hscale := (Pi.basisFun K (FiniteQuantumState ι d)).linearIndependent.units_smul
      (fun a : ι → ZMod d ↦ Units.mk0
        (∏ i, finiteQuantumCharacter d q hq (a i * finiteQuantumTailCharge i a))
        (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ finiteQuantumCharacter_ne_zero q hq _)))
    simpa using hscale
  have hcomp : (fun a : ι → ZMod d ↦ finiteQuantumMonomial q hq a
        (finiteQuantumRoot (K := K) (ι := ι) (d := d))) =
      (fun a ↦ (∏ i, finiteQuantumCharacter d q hq (a i * finiteQuantumTailCharge i a)) •
        Pi.basisFun K (FiniteQuantumState ι d) a) := by
    funext a
    funext x
    rw [finiteQuantumMonomial_apply]
    by_cases hxa : x = a
    · subst x
      simp [finiteQuantumRoot, Pi.basisFun_apply, Pi.single_eq_same, sub_self]
    · have hx : x - a ≠ 0 := sub_ne_zero.mpr hxa
      simp [finiteQuantumRoot, Pi.basisFun_apply,
        Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hxa]
  simpa [Function.comp_def, hcomp] using hb

/-- The ordered monomials are a basis of their span: the normal-form subalgebra of the
finite quantum torus. -/
def finiteQuantumMonomialBasis (q : K) (hq : q ^ d = 1) :
    Module.Basis (ι → ZMod d) K
      (Submodule.span K (Set.range (finiteQuantumMonomial q hq))) :=
  Module.Basis.span (finiteQuantumMonomial_linearIndependent q hq)

/-- The normal-form span has rank the number of exponent vectors. -/
theorem finiteQuantumMonomial_rank_span (q : K) (hq : q ^ d = 1) :
    Module.rank K ↥(Submodule.span K (Set.range (finiteQuantumMonomial q hq))) =
      Cardinal.mk (Set.range (finiteQuantumMonomial q hq)) :=
  rank_span (finiteQuantumMonomial_linearIndependent q hq)

section fermatCapstone

variable {n : ℕ}

/-- The general Fermat hypersurface is the exact dependence horizon of a genuine linear
law space of rational-field derivations. -/
theorem finiteQuantumFermat_linearDependenceHorizon_eq
    (q : K) (hq : IsPrimitiveRoot q d) :
    linearDerivationDependenceHorizon
        (generalizedCliffordShiftFieldDerivationLaw
          (finiteQuantumTorusSymbol (d := d) q hq.pow_eq_one))
        (generalizedCliffordShiftFieldRoot
          (finiteQuantumRoot (K := K) (ι := Fin n) (d := d))) =
      {c : Fin n → K | finiteQuantumDiagonalPotential d c = 0} := by
  apply generalizedCliffordField_linearDependenceHorizon_eq_zeroLocus
    (finiteQuantumTorusSymbol (d := d) q hq.pow_eq_one)
    (finiteQuantumDiagonalPotential d) d
    (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (Fact.out : 1 < d)))
    (finiteQuantumRoot (K := K) (ι := Fin n) (d := d)) finiteQuantumRoot_ne_zero
  exact finiteQuantumTorusSymbol_pow q hq

/-- **General Fermat normal-form maximal horizon.**  For every primitive `d`th root `q`,
the finite quantum packet on `n` generators simultaneously realizes

* the Fermat hypersurface `∑ c_i^d = 0` as the exact scalar dependence horizon of the
  shift-suspended rational derivation law,
* an injective exterior commutator symbol on the differential-field law, and
* the ordered-monomial normal-form basis of the finite quantum torus with its twisted
  2-cocycle product law.

This is the unconditional general-degree, general-width extension of the Fermat cubic
qutrit horizon. -/
theorem finiteQuantumFermat_normalForm_maximalHorizon
    (q : K) (hq : IsPrimitiveRoot q d) :
    (linearDerivationDependenceHorizon
        (generalizedCliffordShiftFieldDerivationLaw
          (finiteQuantumTorusSymbol (d := d) q hq.pow_eq_one))
        (generalizedCliffordShiftFieldRoot
          (finiteQuantumRoot (K := K) (ι := Fin n) (d := d))) =
        {c : Fin n → K | finiteQuantumDiagonalPotential d c = 0}) ∧
      Function.Injective
        (derivationCommutatorMap
          (generalizedCliffordShiftFieldDerivationLaw
            (finiteQuantumTorusSymbol (d := d) q hq.pow_eq_one))) ∧
      LinearIndependent K
        (finiteQuantumMonomial (K := K) (ι := Fin n) (d := d) q hq.pow_eq_one) ∧
      ∀ a b : Fin n → ZMod d,
        finiteQuantumMonomial q hq.pow_eq_one a * finiteQuantumMonomial q hq.pow_eq_one b =
          (∏ i, finiteQuantumCharacter d q hq.pow_eq_one
              (-(b i * finiteQuantumTailCharge i a))) •
            finiteQuantumMonomial q hq.pow_eq_one (a + b) := by
  refine ⟨finiteQuantumFermat_linearDependenceHorizon_eq q hq, ?_,
    finiteQuantumMonomial_linearIndependent q hq.pow_eq_one,
    fun a b ↦ finiteQuantumMonomial_mul q hq.pow_eq_one a b⟩
  have h := finiteQuantumTorus_derivationCommutatorMap_injective
    (ι := Fin n) (V := Fin n → K) q hq.pow_eq_one (hq.ne_one Fact.out)
    LinearMap.id Function.injective_id
  simpa [finiteQuantumTorusSymbol] using h

end fermatCapstone

end

end GaloisForLFunctions.HTGeometry
