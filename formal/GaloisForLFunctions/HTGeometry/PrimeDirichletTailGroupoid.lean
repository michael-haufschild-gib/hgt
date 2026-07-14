import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern
import GaloisForLFunctions.HTGeometry.FiniteGaugeTailCharge

/-!
# The same-field tail groupoid of Boolean orientations

After enumerating the primes, equality of the complete signed prime-Dirichlet palette fields is
eventual equality of Boolean orientations up to global complement.  This file proves the intrinsic
combinatorial normal form of that relation.

The discrete derivative

`D ε n = xor (ε n) (ε (n + 1))`

removes global complement and reduces equality up to complement to ordinary eventual equality.
Finite overwrites meet every finite cylinder while remaining eventually equal to the original
orientation; this is the finite combinatorial core of density of every same-field stratum.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Ordinary eventual equality of Boolean sequences, written with an explicit tail threshold. -/
def BooleanTailEquivalent (ε δ : ℕ → Bool) : Prop :=
  ∃ N, ∀ n, N ≤ n → ε n = δ n

/-- Eventual equality after allowing one global complement. -/
def BooleanTailEquivalentUpToComplement (ε δ : ℕ → Bool) : Prop :=
  BooleanTailEquivalent ε δ ∨ BooleanTailEquivalent ε (fun n => !(δ n))

theorem booleanTailEquivalent_refl (ε : ℕ → Bool) :
    BooleanTailEquivalent ε ε := by
  exact ⟨0, fun _ _ => rfl⟩

theorem booleanTailEquivalent_symm {ε δ : ℕ → Bool}
    (h : BooleanTailEquivalent ε δ) : BooleanTailEquivalent δ ε := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => (hN n hn).symm⟩

theorem booleanTailEquivalent_trans {ε δ η : ℕ → Bool}
    (hεδ : BooleanTailEquivalent ε δ) (hδη : BooleanTailEquivalent δ η) :
    BooleanTailEquivalent ε η := by
  obtain ⟨N, hN⟩ := hεδ
  obtain ⟨M, hM⟩ := hδη
  refine ⟨max N M, fun n hn => ?_⟩
  exact (hN n (le_trans (Nat.le_max_left N M) hn)).trans
    (hM n (le_trans (Nat.le_max_right N M) hn))

private theorem bool_eq_not_symm {a b : Bool} (h : a = !b) : b = !a := by
  cases a <;> cases b <;> simp_all

/-- Eventual equality up to one global complement is an equivalence relation. -/
theorem booleanTailEquivalentUpToComplement_refl (ε : ℕ → Bool) :
    BooleanTailEquivalentUpToComplement ε ε :=
  Or.inl (booleanTailEquivalent_refl ε)

theorem booleanTailEquivalentUpToComplement_symm {ε δ : ℕ → Bool}
    (h : BooleanTailEquivalentUpToComplement ε δ) :
    BooleanTailEquivalentUpToComplement δ ε := by
  rcases h with h | h
  · exact Or.inl (booleanTailEquivalent_symm h)
  · right
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun n hn => bool_eq_not_symm (hN n hn)⟩

theorem booleanTailEquivalentUpToComplement_trans {ε δ η : ℕ → Bool}
    (hεδ : BooleanTailEquivalentUpToComplement ε δ)
    (hδη : BooleanTailEquivalentUpToComplement δ η) :
    BooleanTailEquivalentUpToComplement ε η := by
  rcases hεδ with hεδ | hεδ <;> rcases hδη with hδη | hδη
  · exact Or.inl (booleanTailEquivalent_trans hεδ hδη)
  · right
    obtain ⟨N, hN⟩ := hεδ
    obtain ⟨M, hM⟩ := hδη
    refine ⟨max N M, fun n hn => ?_⟩
    rw [hN n (le_trans (Nat.le_max_left N M) hn)]
    exact hM n (le_trans (Nat.le_max_right N M) hn)
  · right
    obtain ⟨N, hN⟩ := hεδ
    obtain ⟨M, hM⟩ := hδη
    refine ⟨max N M, fun n hn => ?_⟩
    rw [hN n (le_trans (Nat.le_max_left N M) hn)]
    simpa using congrArg (fun b : Bool => !b)
      (hM n (le_trans (Nat.le_max_right N M) hn))
  · left
    obtain ⟨N, hN⟩ := hεδ
    obtain ⟨M, hM⟩ := hδη
    refine ⟨max N M, fun n hn => ?_⟩
    rw [hN n (le_trans (Nat.le_max_left N M) hn)]
    simpa using congrArg (fun b : Bool => !b)
      (hM n (le_trans (Nat.le_max_right N M) hn))

/-- The canonical projective-tail setoid: finite changes and one global sign reversal are
identified, and no other orientations are identified. -/
def booleanProjectiveTailSetoid : Setoid (ℕ → Bool) where
  r := BooleanTailEquivalentUpToComplement
  iseqv := ⟨booleanTailEquivalentUpToComplement_refl,
    booleanTailEquivalentUpToComplement_symm,
    booleanTailEquivalentUpToComplement_trans⟩

/-- The canonical projective-tail quotient of the countable orientation cube. -/
def BooleanProjectiveTail := Quotient booleanProjectiveTailSetoid

def booleanProjectiveTailClass : (ℕ → Bool) → BooleanProjectiveTail :=
  Quotient.mk booleanProjectiveTailSetoid

/-- Equality in the canonical quotient is exactly eventual equality or eventual complement. -/
theorem booleanProjectiveTailClass_eq_iff (ε δ : ℕ → Bool) :
    booleanProjectiveTailClass ε = booleanProjectiveTailClass δ ↔
      BooleanTailEquivalentUpToComplement ε δ := by
  exact Quotient.eq

/-- Threshold-form eventual equality agrees with finiteness of the disagreement set. -/
theorem booleanTailEquivalent_iff_primeOrientationsEventuallyEqual
    (ε δ : ℕ → Bool) :
    BooleanTailEquivalent ε δ ↔ PrimeOrientationsEventuallyEqual ε δ := by
  classical
  constructor
  · rintro ⟨N, hN⟩
    apply (Set.finite_Iio N).subset
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Set.mem_Iio]
    by_contra hnlt
    exact hn (hN n (Nat.le_of_not_gt hnlt))
  · intro hfinite
    obtain ⟨N, hsub⟩ := Finset.exists_nat_subset_range hfinite.toFinset
    refine ⟨N, fun n hn => ?_⟩
    by_contra hne
    have hnmem : n ∈ hfinite.toFinset := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hne
    have hnlt : n < N := Finset.mem_range.mp (hsub hnmem)
    exact (Nat.not_lt_of_ge hn) hnlt

/-- Threshold-form eventual complement agrees with finiteness of the agreement set. -/
theorem booleanTailEquivalent_complement_iff_primeOrientationsEventuallyOpposite
    (ε δ : ℕ → Bool) :
    BooleanTailEquivalent ε (fun n => !(δ n)) ↔
      PrimeOrientationsEventuallyOpposite ε δ := by
  rw [booleanTailEquivalent_iff_primeOrientationsEventuallyEqual]
  change {n | ε n ≠ !(δ n)}.Finite ↔ {n | ε n = δ n}.Finite
  have hset : {n | ε n ≠ !(δ n)} = {n | ε n = δ n} := by
    ext n
    cases ε n <;> cases δ n <;> simp
  rw [hset]

/-- The threshold and finite-set formulations of the same-field orientation relation coincide. -/
theorem booleanTailEquivalentUpToComplement_iff_primeOrientationRelation
    (ε δ : ℕ → Bool) :
    BooleanTailEquivalentUpToComplement ε δ ↔
      PrimeOrientationsEventuallyEqual ε δ ∨
        PrimeOrientationsEventuallyOpposite ε δ := by
  rw [BooleanTailEquivalentUpToComplement,
    booleanTailEquivalent_iff_primeOrientationsEventuallyEqual,
    booleanTailEquivalent_complement_iff_primeOrientationsEventuallyOpposite]

/-- The adjacent-coordinate derivative over the two-element field. -/
def booleanTailDerivative (ε : ℕ → Bool) (n : ℕ) : Bool :=
  Bool.xor (ε n) (ε (n + 1))

/-- The discrete derivative is continuous for the canonical product topology on the Boolean
orientation cube. -/
theorem continuous_booleanTailDerivative : Continuous booleanTailDerivative := by
  apply continuous_pi
  intro n
  exact
    (continuous_of_discreteTopology :
      Continuous (fun x : Bool × Bool => Bool.xor x.1 x.2)).comp
      ((continuous_apply n : Continuous (fun ε : ℕ → Bool => ε n)).prodMk
        (continuous_apply (n + 1) : Continuous (fun ε : ℕ → Bool => ε (n + 1))))

theorem booleanTailDerivative_complement (ε : ℕ → Bool) :
    booleanTailDerivative (fun n => !(ε n)) = booleanTailDerivative ε := by
  funext n
  simp only [booleanTailDerivative]
  cases ε n <;> cases ε (n + 1) <;> rfl

theorem BooleanTailEquivalent.derivative
    {ε δ : ℕ → Bool} (h : BooleanTailEquivalent ε δ) :
    BooleanTailEquivalent (booleanTailDerivative ε) (booleanTailDerivative δ) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  simp only [booleanTailDerivative]
  rw [hN n hn, hN (n + 1) (le_trans hn (Nat.le_succ n))]

theorem BooleanTailEquivalent.derivative_of_complement
    {ε δ : ℕ → Bool} (h : BooleanTailEquivalent ε (fun n => !(δ n))) :
    BooleanTailEquivalent (booleanTailDerivative ε) (booleanTailDerivative δ) := by
  have hd := h.derivative
  simpa only [booleanTailDerivative_complement] using hd

private theorem xor_next_eq_of_xor_eq_of_eq
    {a b c d : Bool} (hxor : Bool.xor a b = Bool.xor c d) (hac : a = c) : b = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem xor_next_eq_not_of_xor_eq_of_eq_not
    {a b c d : Bool} (hxor : Bool.xor a b = Bool.xor c d) (hac : a = !c) : b = !d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- **Discrete-derivative classification.**  Two Boolean orientations have eventually equal
discrete derivatives exactly when they are eventually equal or eventually complementary. -/
theorem booleanTailDerivative_tailEquivalent_iff
    (ε δ : ℕ → Bool) :
    BooleanTailEquivalent (booleanTailDerivative ε) (booleanTailDerivative δ) ↔
      BooleanTailEquivalentUpToComplement ε δ := by
  constructor
  · rintro ⟨N, hN⟩
    by_cases hbase : ε N = δ N
    · left
      refine ⟨N, fun n hn => ?_⟩
      induction n, hn using Nat.le_induction with
      | base => exact hbase
      | succ k hk hεk =>
          exact xor_next_eq_of_xor_eq_of_eq (hN k hk) hεk
    · right
      have hbaseNot : ε N = !(δ N) := by
        cases hεN : ε N <;> cases hδN : δ N <;> simp_all
      refine ⟨N, fun n hn => ?_⟩
      induction n, hn using Nat.le_induction with
      | base => exact hbaseNot
      | succ k hk hεk =>
          exact xor_next_eq_not_of_xor_eq_of_eq_not (hN k hk) hεk
  · rintro (h | h)
    · exact h.derivative
    · exact h.derivative_of_complement

/-- Duplicate a Boolean sequence into the even coordinates and anchor every odd coordinate at
`false`.  The anchor prevents eventual global complement. -/
def anchoredBooleanOrientation (ε : ℕ → Bool) (n : ℕ) : Bool :=
  if n % 2 = 0 then ε (n / 2) else false

/-- Anchored duplication is continuous for the canonical product topology. -/
theorem continuous_anchoredBooleanOrientation :
    Continuous anchoredBooleanOrientation := by
  apply continuous_pi
  intro n
  by_cases hn : n % 2 = 0
  · simpa [anchoredBooleanOrientation, hn] using
      (continuous_apply (n / 2) : Continuous (fun ε : ℕ → Bool => ε (n / 2)))
  · simpa [anchoredBooleanOrientation, hn] using
      (continuous_const : Continuous (fun _ : ℕ → Bool => false))

@[simp]
theorem anchoredBooleanOrientation_two_mul (ε : ℕ → Bool) (n : ℕ) :
    anchoredBooleanOrientation ε (2 * n) = ε n := by
  simp [anchoredBooleanOrientation]

@[simp]
theorem anchoredBooleanOrientation_two_mul_add_one (ε : ℕ → Bool) (n : ℕ) :
    anchoredBooleanOrientation ε (2 * n + 1) = false := by
  simp [anchoredBooleanOrientation]

/-- Anchored duplication continuously reduces ordinary eventual equality to eventual equality up
to complement, and reflects the relation exactly. -/
theorem anchoredBooleanOrientation_tailEquivalentUpToComplement_iff
    (ε δ : ℕ → Bool) :
    BooleanTailEquivalentUpToComplement
        (anchoredBooleanOrientation ε) (anchoredBooleanOrientation δ) ↔
      BooleanTailEquivalent ε δ := by
  constructor
  · rintro (h | h)
    · obtain ⟨N, hN⟩ := h
      refine ⟨N, fun n hn => ?_⟩
      simpa using hN (2 * n) (by omega)
    · obtain ⟨N, hN⟩ := h
      have hfalse := hN (2 * N + 1) (by omega)
      simp at hfalse
  · rintro ⟨N, hN⟩
    left
    refine ⟨2 * N, fun n hn => ?_⟩
    rcases Nat.even_or_odd n with heven | hodd
    · have hnrepr := Nat.two_mul_div_two_of_even heven
      have hhalf : N ≤ n / 2 := by omega
      rw [← hnrepr]
      simp only [anchoredBooleanOrientation_two_mul]
      exact hN (n / 2) hhalf
    · have hnrepr := Nat.two_mul_div_two_add_one_of_odd hodd
      rw [← hnrepr]
      simp

/-- Replace finitely many coordinates of `ε` by prescribed coordinates of `target`. -/
def overwriteBooleanOrientation (F : Finset ℕ) (target ε : ℕ → Bool) (n : ℕ) : Bool :=
  if n ∈ F then target n else ε n

/-- The finite cylinder prescribed by `target` on `F`. -/
def booleanOrientationCylinder (F : Finset ℕ) (target : ℕ → Bool) : Set (ℕ → Bool) :=
  {ε | ∀ n ∈ F, ε n = target n}

theorem overwriteBooleanOrientation_mem_cylinder
    (F : Finset ℕ) (target ε : ℕ → Bool) :
    overwriteBooleanOrientation F target ε ∈ booleanOrientationCylinder F target := by
  intro n hn
  simp [overwriteBooleanOrientation, hn]

/-- A finite overwrite remains in the ordinary eventual-equality class of the source orientation. -/
theorem overwriteBooleanOrientation_tailEquivalent
    (F : Finset ℕ) (target ε : ℕ → Bool) :
    BooleanTailEquivalent (overwriteBooleanOrientation F target ε) ε := by
  obtain ⟨N, hFN⟩ := Finset.exists_nat_subset_range F
  refine ⟨N, fun n hn => ?_⟩
  have hnF : n ∉ F := by
    intro hnmem
    have hnlt : n < N := Finset.mem_range.mp (hFN hnmem)
    exact (Nat.not_lt_of_ge hn) hnlt
  simp [overwriteBooleanOrientation, hnF]

/-- Every ordinary tail class, hence every equality-up-to-complement class, meets every finite
Boolean cylinder. -/
theorem exists_tailEquivalent_mem_booleanOrientationCylinder
    (F : Finset ℕ) (target ε : ℕ → Bool) :
    ∃ δ ∈ booleanOrientationCylinder F target, BooleanTailEquivalent δ ε :=
  ⟨overwriteBooleanOrientation F target ε,
    overwriteBooleanOrientation_mem_cylinder F target ε,
    overwriteBooleanOrientation_tailEquivalent F target ε⟩

/-- Every projective-tail quotient fibre is dense in the canonical product topology. -/
theorem booleanProjectiveTailClass_fiber_dense (ε : ℕ → Bool) :
    Dense (booleanProjectiveTailClass ⁻¹' {booleanProjectiveTailClass ε}) := by
  apply GaloisForLFunctions.dense_fiber_of_finiteModification_invariant
  intro x y hy
  apply (booleanProjectiveTailClass_eq_iff y x).2
  left
  apply (booleanTailEquivalent_iff_primeOrientationsEventuallyEqual y x).2
  exact hy

/-- The quotient topology induced on projective-tail classes is indiscrete. -/
theorem booleanProjectiveTail_coinduced_eq_indiscrete :
    TopologicalSpace.coinduced booleanProjectiveTailClass inferInstance = ⊤ := by
  apply GaloisForLFunctions.coinduced_eq_indiscrete_of_dense_fibers
  · exact Quotient.mk_surjective
  · intro a
    obtain ⟨ε, rfl⟩ := Quotient.mk_surjective a
    exact booleanProjectiveTailClass_fiber_dense ε

/-- Every continuous projective-tail-class invariant with values in a `T0` space is constant. -/
theorem continuous_constant_of_booleanProjectiveTailClass
    {Y : Type*} [TopologicalSpace Y] [T0Space Y]
    (F : (ℕ → Bool) → Y) (hF : Continuous F)
    (hinvariant : ∀ ε δ, booleanProjectiveTailClass ε = booleanProjectiveTailClass δ →
      F ε = F δ) :
    ∀ ε δ, F ε = F δ := by
  apply GaloisForLFunctions.continuous_constant_of_dense_fibers
    booleanProjectiveTailClass F hF
  · exact booleanProjectiveTailClass_fiber_dense
  · exact hinvariant

/-- Continuity at even one orientation forces a projective-tail-class invariant with values in a
`T₁` space to be globally constant. -/
theorem continuousAt_constant_of_booleanProjectiveTailClass
    {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    (F : (ℕ → Bool) → Y) (ε : ℕ → Bool) (hF : ContinuousAt F ε)
    (hinvariant : ∀ x y, booleanProjectiveTailClass x = booleanProjectiveTailClass y →
      F x = F y) :
    ∀ δ, F δ = F ε := by
  apply GaloisForLFunctions.continuousAt_constant_of_dense_fibers
    booleanProjectiveTailClass F ε hF
  · exact booleanProjectiveTailClass_fiber_dense
  · exact hinvariant

/-- Every nonconstant projective-tail-class invariant into a `T₁` space is nowhere continuous. -/
theorem nowhereContinuousAt_of_nonconstant_booleanProjectiveTailClass
    {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    (F : (ℕ → Bool) → Y)
    (hinvariant : ∀ x y, booleanProjectiveTailClass x = booleanProjectiveTailClass y →
      F x = F y)
    (hnonconstant : ∃ x y, F x ≠ F y) :
    ∀ ε, ¬ContinuousAt F ε := by
  obtain ⟨x, y, hxy⟩ := hnonconstant
  intro ε hF
  have hconstant :=
    continuousAt_constant_of_booleanProjectiveTailClass F ε hF hinvariant
  exact hxy ((hconstant x).trans (hconstant y).symm)

end GaloisForLFunctions.HTGeometry
