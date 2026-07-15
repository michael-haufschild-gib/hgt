import GaloisForLFunctions.HTGeometry.ParabolicOrbifoldTwelveCharge

/-!
# Local rank collapse for nonautonomous projective tails

The finite-rank alternatives for a proper differential groupoid on a curve are tensor, affine,
and projective structures.  This file certifies the local arithmetic and the global genus-zero
budget that make the latter two ranks unstable under unbounded rational constraint depth.

For an affine connection, shifting a logarithmic residue by one turns its pullback law into pure
multiplication by the ramification index.  For a projective connection, shifting the double-pole
coefficient to its exponent discriminant does the same after squaring.  Thus both higher ranks
carry the same multiplicative cone-angle arithmetic as a tensor.

The last theorems are the static Riemann--Hurwitz mechanism.  Three target fibres wholly trapped
in one fixed exceptional source set force the covering degree to be bounded.  More generally, a
positive orbifold excess consumes degree times that excess, while the fixed exceptional locus
supplies only a finite budget.  No dynamical flow or numerical experiment is involved.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- The shifted residue of a pulled-back affine connection is multiplied exactly by the local
ramification index.  In local coordinates the unshifted residue is `e * r + (e - 1)`. -/
theorem affineConnection_shiftedResidue_transport {K : Type*} [CommRing K]
    (e r : K) :
    1 + (e * r + (e - 1)) = e * (1 + r) := by
  ring

/-- The exponent discriminant of a pulled-back projective connection is multiplied by the square
of the local ramification index.  Here `c` is the target double-pole coefficient and
`e^2 * c + (1 - e^2)` is the source coefficient after adding the Schwarzian ramification term. -/
theorem projectiveConnection_exponentDiscriminant_transport
    {K : Type*} [CommRing K] (e c : K) :
    1 - (e ^ 2 * c + (1 - e ^ 2)) = e ^ 2 * (1 - c) := by
  ring

/-- Projectivizing an affine connection commutes with rational pullback.  If the affine
coefficient transforms as `p₁ * μ + p₂ / p₁`, then `2 μ' - μ²` transforms by the projective
Schwarzian law.  This reduces the affine rank to the same projective defect analysis. -/
theorem affineConnection_projectivization_transport
    {K : Type*} [Field K] (μ dμ p₁ p₂ p₃ : K) (hp₁ : p₁ ≠ 0) :
    2 * (p₁ ^ 2 * dμ + p₂ * μ + p₃ / p₁ - (p₂ / p₁) ^ 2) -
        (p₁ * μ + p₂ / p₁) ^ 2 =
      p₁ ^ 2 * (2 * dμ - μ ^ 2) + 2 * p₃ / p₁ - 3 * (p₂ / p₁) ^ 2 := by
  field_simp [hp₁]
  ring

/-- A finite family of marked fibres on a genus-zero cover satisfies an exact cardinality budget.
`ramification y + fiberCard y = degree` is the fibrewise identity, while the second hypothesis is
the Riemann--Hurwitz upper bound for the ramification already spent over the marked values. -/
theorem genusZero_markedFiber_cardinality_budget
    {β : Type*} (marked : Finset β) (ramification fiberCard : β → ℕ) (degree : ℕ)
    (hcard : 2 ≤ marked.card)
    (hfiber : ∀ y ∈ marked, ramification y + fiberCard y = degree)
    (hHurwitz : (∑ y ∈ marked, ramification y) + 2 ≤ 2 * degree) :
    (marked.card - 2) * degree + 2 ≤ ∑ y ∈ marked, fiberCard y := by
  have hsum :
      (∑ y ∈ marked, ramification y) + (∑ y ∈ marked, fiberCard y) =
        marked.card * degree := by
    calc
      (∑ y ∈ marked, ramification y) + (∑ y ∈ marked, fiberCard y) =
          ∑ y ∈ marked, (ramification y + fiberCard y) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ _y ∈ marked, degree := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hfiber y hy
      _ = marked.card * degree := by simp
  have hsplit :
      (marked.card - 2) * degree + 2 * degree = marked.card * degree := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hcard]
  omega

/-- In particular, three distinct target fibres cannot all be supported on one fixed exceptional
source set once the degree exceeds the size of that set.  This is the exact replacement for the
incorrect shortcut that treated a non-Galois branched cover as a global finite group action. -/
theorem threeTrappedFibers_degree_add_two_le_exceptionalCard
    {β : Type*} (marked : Finset β) (ramification fiberCard : β → ℕ)
    (degree exceptionalCard : ℕ)
    (hthree : marked.card = 3)
    (hfiber : ∀ y ∈ marked, ramification y + fiberCard y = degree)
    (hHurwitz : (∑ y ∈ marked, ramification y) + 2 ≤ 2 * degree)
    (htrapped : ∑ y ∈ marked, fiberCard y ≤ exceptionalCard) :
    degree + 2 ≤ exceptionalCard := by
  have hbudget := genusZero_markedFiber_cardinality_budget marked ramification fiberCard degree
    (by omega) hfiber hHurwitz
  have hbudget' : degree + 2 ≤ ∑ y ∈ marked, fiberCard y := by
    simpa [hthree] using hbudget
  exact hbudget'.trans htrapped

/-- The number of genuinely non-orbifold terminal fibres is antitone along the late protocol, so
well-foundedness of the natural numbers makes the exceptional skeleton eventually constant. -/
theorem nonOrbifoldFiberCard_eventually_constant
    (badFiberCard : ℕ → ℕ) (hanti : Antitone badFiberCard) :
    ∃ N, ∀ n, N ≤ n → badFiberCard n = badFiberCard N := by
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hanti
  exact ⟨N, fun n hn => (hN n hn).symm⟩

/-- If a finite target family has the same cardinality as the source exceptional skeleton and
every target fibre is nonempty, disjointness leaves exactly one source point in each fibre. -/
theorem stableExceptionalFibers_are_singletons
    {β : Type*} [DecidableEq β] (marked : Finset β) (fiberCard : β → ℕ)
    (hpositive : ∀ y ∈ marked, 0 < fiberCard y)
    (hbudget : ∑ y ∈ marked, fiberCard y ≤ marked.card) :
    ∀ y ∈ marked, fiberCard y = 1 := by
  intro y hy
  have hrest : (marked.erase y).card ≤ ∑ z ∈ marked.erase y, fiberCard z := by
    calc
      (marked.erase y).card = ∑ _z ∈ marked.erase y, 1 := by simp
      _ ≤ ∑ z ∈ marked.erase y, fiberCard z := by
        exact Finset.sum_le_sum fun z hz => hpositive z (Finset.mem_of_mem_erase hz)
  have hsum :
      ∑ z ∈ marked, fiberCard z =
        fiberCard y + ∑ z ∈ marked.erase y, fiberCard z := by
    calc
      ∑ z ∈ marked, fiberCard z =
          (∑ z ∈ marked.erase y, fiberCard z) + fiberCard y :=
        (Finset.sum_erase_add marked fiberCard hy).symm
      _ = fiberCard y + ∑ z ∈ marked.erase y, fiberCard z := Nat.add_comm _ _
  have hcard : marked.card = 1 + (marked.erase y).card := by
    simpa [Nat.add_comm] using (Finset.card_erase_add_one hy).symm
  have hypositive : 0 < fiberCard y := hpositive y hy
  omega

/-- At the stable one- or two-point exceptional skeleton, every exceptional target value has one
source preimage and that point carries the full covering degree. -/
theorem stableExceptionalFibers_are_totallyRamified
    {β : Type*} [DecidableEq β] (marked : Finset β)
    (fiberCard ramification : β → ℕ) (degree : ℕ)
    (hpositive : ∀ y ∈ marked, 0 < fiberCard y)
    (hbudget : ∑ y ∈ marked, fiberCard y ≤ marked.card)
    (hfiber : ∀ y ∈ marked, ramification y + fiberCard y = degree) :
    ∀ y ∈ marked, ramification y + 1 = degree := by
  intro y hy
  rw [← stableExceptionalFibers_are_singletons marked fiberCard hpositive hbudget y hy]
  exact hfiber y hy

/-- Abstract degree-times-excess law.  The marked local defects dominate a normalized hyperbolic
excess, while all ramification and exceptional corrections fit in the genus-zero and fixed-source
budgets.  The conclusion says that expansion can support a positive excess only for finitely many
constraint depths. -/
theorem projectiveOrbifold_excess_degree_budget
    {β : Type*} (marked : Finset β)
    (localDefect ramification exceptionalCorrection : β → ℤ)
    (degree scale excess exceptionalBudget : ℤ)
    (hdegree : 0 ≤ degree) (hscale : 0 ≤ scale)
    (hlocal : degree * (∑ y ∈ marked, localDefect y) ≤
      scale * ((∑ y ∈ marked, ramification y) +
        ∑ y ∈ marked, exceptionalCorrection y))
    (hHurwitz : (∑ y ∈ marked, ramification y) + 2 ≤ 2 * degree)
    (hexceptional : ∑ y ∈ marked, exceptionalCorrection y ≤ exceptionalBudget)
    (hhyperbolic : 2 * scale + excess ≤ ∑ y ∈ marked, localDefect y) :
    degree * excess + 2 * scale ≤ scale * exceptionalBudget := by
  nlinarith [mul_nonneg hdegree (sub_nonneg.mpr hhyperbolic)]

/-- The classical `1/42` gap above parabolicity converts the excess budget into an explicit degree
cutoff.  This algebraic form is independent of how the orbifold gap was established. -/
theorem hurwitzGap_degree_le_exceptionalBudget
    (degree scale excess exceptionalBudget : ℕ)
    (hscale : 0 < scale)
    (hgap : scale ≤ 42 * excess)
    (hbudget : degree * excess ≤ scale * exceptionalBudget) :
    degree ≤ 42 * exceptionalBudget := by
  have h₁ : degree * scale ≤ degree * (42 * excess) :=
    Nat.mul_le_mul_left degree hgap
  have h₂ : degree * (42 * excess) = 42 * (degree * excess) := by ring
  have h₃ : 42 * (degree * excess) ≤ 42 * (scale * exceptionalBudget) :=
    Nat.mul_le_mul_left 42 hbudget
  have h₄ : degree * scale ≤ (42 * exceptionalBudget) * scale := by
    calc
      degree * scale ≤ degree * (42 * excess) := h₁
      _ = 42 * (degree * excess) := h₂
      _ ≤ 42 * (scale * exceptionalBudget) := h₃
      _ = (42 * exceptionalBudget) * scale := by ring
  exact Nat.le_of_mul_le_mul_right h₄ hscale

/-- Exponentially growing prefix degree eventually excludes every projective-orbifold phase whose
positive Euler defect is bounded by the Hurwitz `1/42` inequality. -/
theorem projectiveHyperbolicTail_eventually_absent
    (prefixDegree : ℕ → ℕ) (exceptionalBudget : ℕ) (hyperbolic : ℕ → Prop)
    (hdegree : ∀ n, 2 ^ n ≤ prefixDegree n)
    (hhyperbolicDegree : ∀ n, hyperbolic n →
      prefixDegree n ≤ 42 * exceptionalBudget) :
    ∀ᶠ n in Filter.atTop, ¬ hyperbolic n := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (42 * exceptionalBudget) Nat.one_lt_two
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro hnHyperbolic
  have hlarge : 42 * exceptionalBudget < prefixDegree n :=
    hN.trans_le <| (Nat.pow_le_pow_right (by omega) hn).trans (hdegree n)
  exact (Nat.not_lt_of_ge (hhyperbolicDegree n hnHyperbolic)) hlarge

/-- Three genuinely non-orbifold terminal fibres would have to fit inside the fixed source
exceptional set.  Exponential prefix degree therefore leaves at most two such fibres eventually. -/
theorem nonOrbifoldFiberCard_eventually_le_two
    (prefixDegree badFiberCard : ℕ → ℕ) (sourceExceptionalCard : ℕ)
    (hdegree : ∀ n, 2 ^ n ≤ prefixDegree n)
    (hthreeBudget : ∀ n, 3 ≤ badFiberCard n →
      prefixDegree n + 2 ≤ sourceExceptionalCard) :
    ∀ᶠ n in Filter.atTop, badFiberCard n ≤ 2 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt sourceExceptionalCard Nat.one_lt_two
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  by_contra hbad
  have hthree : 3 ≤ badFiberCard n := by omega
  have hlarge : sourceExceptionalCard < prefixDegree n :=
    hN.trans_le <| (Nat.pow_le_pow_right (by omega) hn).trans (hdegree n)
  have hsmall := hthreeBudget n hthree
  omega

/-- The formal global budget surface: sufficiently deep projective phases are simultaneously
non-hyperbolic and supported on at most two genuinely non-orbifold fibres. -/
theorem projectiveTail_eventually_nonhyperbolic_with_twoPointSkeleton
    (prefixDegree badFiberCard : ℕ → ℕ) (sourceExceptionalCard exceptionalBudget : ℕ)
    (hyperbolic : ℕ → Prop)
    (hdegree : ∀ n, 2 ^ n ≤ prefixDegree n)
    (hthreeBudget : ∀ n, 3 ≤ badFiberCard n →
      prefixDegree n + 2 ≤ sourceExceptionalCard)
    (hhyperbolicDegree : ∀ n, hyperbolic n →
      prefixDegree n ≤ 42 * exceptionalBudget) :
    ∀ᶠ n in Filter.atTop, badFiberCard n ≤ 2 ∧ ¬ hyperbolic n := by
  filter_upwards [
    nonOrbifoldFiberCard_eventually_le_two prefixDegree badFiberCard sourceExceptionalCard
      hdegree hthreeBudget,
    projectiveHyperbolicTail_eventually_absent prefixDegree exceptionalBudget hyperbolic
      hdegree hhyperbolicDegree] with n hbad hhyperbolic
  exact ⟨hbad, hhyperbolic⟩

end GaloisForLFunctions.HTGeometry
