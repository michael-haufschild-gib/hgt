import Mathlib.Analysis.Meromorphic.Order
import GaloisForLFunctions.HTGeometry.HurwitzOrbifoldGap

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
positive orbifold excess consumes degree times that excess, while exceptional punctures and
source genus supply the only topological budget.  The genus-corrected law isolates why
correspondence surfaces can retain hyperbolic projective curvature while a fixed source sphere
cannot.  No dynamical flow or numerical experiment is involved.
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

/-- The irregularity of a projective pole is the part of its pole order above the Fuchsian
threshold two. -/
def projectivePoleIrregularity (poleOrder : ℕ) : ℕ :=
  poleOrder - 2

/-- A terminal projective pole of order `r` pulled back through local degree `e` has principal
pole order `2 + e * (r - 2)`. -/
def projectivePullbackPoleOrder (ramification terminalPoleOrder : ℕ) : ℕ :=
  2 + ramification * projectivePoleIrregularity terminalPoleOrder

/-- Pullback multiplies projective irregularity exactly by the local ramification index. -/
@[simp]
theorem projectivePullbackPoleOrder_irregularity
    (ramification terminalPoleOrder : ℕ) :
    projectivePoleIrregularity
        (projectivePullbackPoleOrder ramification terminalPoleOrder) =
      ramification * projectivePoleIrregularity terminalPoleOrder := by
  simp [projectivePoleIrregularity, projectivePullbackPoleOrder]

/-- A genuinely irregular terminal pole remains strictly more singular than a Schwarzian
double pole at every nonconstant local branch. -/
theorem two_lt_projectivePullbackPoleOrder
    (ramification terminalPoleOrder : ℕ)
    (hramification : 0 < ramification) (hirregular : 2 < terminalPoleOrder) :
    2 < projectivePullbackPoleOrder ramification terminalPoleOrder := by
  have hterminal : 0 < projectivePoleIrregularity terminalPoleOrder := by
    simp [projectivePoleIrregularity, hirregular]
  have hproduct : 0 < ramification * projectivePoleIrregularity terminalPoleOrder :=
    Nat.mul_pos hramification hterminal
  simp only [projectivePullbackPoleOrder]
  omega

/-- A nonzero analytic unit times the local projective principal part has exactly the expected
pulled-back pole order. -/
theorem meromorphicOrderAt_projectivePrincipalPart
    (p : ℂ) (unit : ℂ → ℂ) (hunit : AnalyticAt ℂ unit p) (hunit_ne : unit p ≠ 0)
    (ramification terminalPoleOrder : ℕ) :
    meromorphicOrderAt
        (fun z : ℂ => unit z *
          (z - p) ^ (-((projectivePullbackPoleOrder ramification terminalPoleOrder : ℕ) : ℤ))) p =
      ((-((projectivePullbackPoleOrder ramification terminalPoleOrder : ℕ) : ℤ)) : WithTop ℤ) := by
  change meromorphicOrderAt
      (unit * ((· - p) ^ (-((projectivePullbackPoleOrder ramification terminalPoleOrder : ℕ) : ℤ))))
        p = _
  rw [meromorphicOrderAt_mul_of_ne_zero hunit hunit_ne]
  exact meromorphicOrderAt_zpow_id_sub_const

/-- The Schwarzian term cannot cancel an irregular pulled-back projective pole: its order is at
least `-2`, while the principal part has strictly smaller meromorphic order. -/
theorem meromorphicOrderAt_projectivePrincipalPart_add_schwarzian
    (p : ℂ) (unit schwarzian : ℂ → ℂ)
    (hunit : AnalyticAt ℂ unit p) (hunit_ne : unit p ≠ 0)
    (hschwarzian : MeromorphicAt schwarzian p)
    (hschwarzianOrder : ((-2 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt schwarzian p)
    (ramification terminalPoleOrder : ℕ)
    (hramification : 0 < ramification) (hirregular : 2 < terminalPoleOrder) :
    meromorphicOrderAt
        (fun z : ℂ => unit z *
            (z - p) ^ (-((projectivePullbackPoleOrder ramification terminalPoleOrder : ℕ) : ℤ)) +
          schwarzian z) p =
      ((-((projectivePullbackPoleOrder ramification terminalPoleOrder : ℕ) : ℤ)) : WithTop ℤ) := by
  have hpole : 2 < projectivePullbackPoleOrder ramification terminalPoleOrder :=
    two_lt_projectivePullbackPoleOrder ramification terminalPoleOrder
      hramification hirregular
  have hpoleInt : (2 : ℤ) < projectivePullbackPoleOrder ramification terminalPoleOrder := by
    exact_mod_cast hpole
  have horderLt :
      ((-((projectivePullbackPoleOrder ramification terminalPoleOrder : ℕ) : ℤ)) : WithTop ℤ) <
        ((-2 : ℤ) : WithTop ℤ) :=
    WithTop.coe_lt_coe.mpr (neg_lt_neg hpoleInt)
  have hprincipalOrder := meromorphicOrderAt_projectivePrincipalPart p unit hunit hunit_ne
    ramification terminalPoleOrder
  have hstrict :
      meromorphicOrderAt
          (fun z : ℂ => unit z *
            (z - p) ^ (-((projectivePullbackPoleOrder ramification terminalPoleOrder : ℕ) : ℤ))) p <
        meromorphicOrderAt schwarzian p := by
    rw [hprincipalOrder]
    exact horderLt.trans_le hschwarzianOrder
  change meromorphicOrderAt
      ((fun z : ℂ => unit z *
        (z - p) ^ (-((projectivePullbackPoleOrder ramification terminalPoleOrder : ℕ) : ℤ))) +
        schwarzian) p = _
  calc
    _ = meromorphicOrderAt
        (fun z : ℂ => unit z *
          (z - p) ^ (-((projectivePullbackPoleOrder ramification terminalPoleOrder : ℕ) : ℤ))) p :=
      meromorphicOrderAt_add_eq_left_of_lt hschwarzian hstrict
    _ = _ := hprincipalOrder

/-- Summing the exact local irregularity law over one degree-`D` fibre gives the
degree-amplified divisor inequality `D * I_y ≤ I₀`. -/
theorem projectiveIrregularity_fiber_degree_amplified
    {α : Type*} (fiber : Finset α) (ramification sourcePoleOrder : α → ℕ)
    (terminalPoleOrder degree : ℕ)
    (hdegree : ∑ x ∈ fiber, ramification x = degree)
    (hlocal : ∀ x ∈ fiber,
      projectivePullbackPoleOrder (ramification x) terminalPoleOrder ≤ sourcePoleOrder x) :
    degree * projectivePoleIrregularity terminalPoleOrder ≤
      ∑ x ∈ fiber, projectivePoleIrregularity (sourcePoleOrder x) := by
  calc
    degree * projectivePoleIrregularity terminalPoleOrder =
        (∑ x ∈ fiber, ramification x) * projectivePoleIrregularity terminalPoleOrder := by
          rw [hdegree]
    _ = ∑ x ∈ fiber, ramification x * projectivePoleIrregularity terminalPoleOrder := by
      rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ fiber, projectivePoleIrregularity (sourcePoleOrder x) := by
      exact Finset.sum_le_sum fun x hx => by
        apply Nat.le_sub_of_add_le
        simpa [projectivePullbackPoleOrder, projectivePoleIrregularity, Nat.add_comm] using
          hlocal x hx

/-- Once the covering degree exceeds the complete source irregularity budget, every terminal pole
is Fuchsian.  This is the finite-transient conclusion of the local divisor law. -/
theorem terminalProjectivePoleOrder_le_two_of_sourceBudget_lt_degree
    {α : Type*} (fiber : Finset α) (ramification sourcePoleOrder : α → ℕ)
    (terminalPoleOrder degree sourceIrregularityBudget : ℕ)
    (hdegree : ∑ x ∈ fiber, ramification x = degree)
    (hlocal : ∀ x ∈ fiber,
      projectivePullbackPoleOrder (ramification x) terminalPoleOrder ≤ sourcePoleOrder x)
    (hsource : (∑ x ∈ fiber, projectivePoleIrregularity (sourcePoleOrder x)) ≤
      sourceIrregularityBudget)
    (hdeep : sourceIrregularityBudget < degree) :
    terminalPoleOrder ≤ 2 := by
  have hamplified : degree * projectivePoleIrregularity terminalPoleOrder ≤
      sourceIrregularityBudget :=
    (projectiveIrregularity_fiber_degree_amplified fiber ramification sourcePoleOrder
      terminalPoleOrder degree hdegree hlocal).trans hsource
  have hirregularity : projectivePoleIrregularity terminalPoleOrder = 0 := by
    by_contra hne
    have hpositive : 0 < projectivePoleIrregularity terminalPoleOrder := Nat.pos_of_ne_zero hne
    have hdegree_le : degree ≤ degree * projectivePoleIrregularity terminalPoleOrder :=
      Nat.le_mul_of_pos_right degree hpositive
    omega
  simp only [projectivePoleIrregularity] at hirregularity
  omega

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

/-- A finite family of marked fibres on a genus-`genus` source curve satisfies a cardinality
budget with exactly `2 * genus` more capacity than a source sphere.  The hypotheses are the
fibrewise degree identity and the Riemann--Hurwitz bound restricted to the marked values. -/
theorem markedFiber_cardinality_budget_with_genus
    {β : Type*} (marked : Finset β) (ramification fiberCard : β → ℕ)
    (degree genus : ℕ)
    (hcard : 2 ≤ marked.card)
    (hfiber : ∀ y ∈ marked, ramification y + fiberCard y = degree)
    (hHurwitz : (∑ y ∈ marked, ramification y) + 2 ≤ 2 * degree + 2 * genus) :
    (marked.card - 2) * degree + 2 ≤
      (∑ y ∈ marked, fiberCard y) + 2 * genus := by
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

/-- Three trapped terminal fibres consume either exceptional points or source handles.  This is
the genus-corrected boundary between functional quotient maps and two-sided correspondences. -/
theorem threeTrappedFibers_degree_add_two_le_exceptionalCard_add_twoGenus
    {β : Type*} (marked : Finset β) (ramification fiberCard : β → ℕ)
    (degree genus exceptionalCard : ℕ)
    (hthree : marked.card = 3)
    (hfiber : ∀ y ∈ marked, ramification y + fiberCard y = degree)
    (hHurwitz : (∑ y ∈ marked, ramification y) + 2 ≤ 2 * degree + 2 * genus)
    (htrapped : ∑ y ∈ marked, fiberCard y ≤ exceptionalCard) :
    degree + 2 ≤ exceptionalCard + 2 * genus := by
  have hbudget := markedFiber_cardinality_budget_with_genus
    marked ramification fiberCard degree genus (by omega) hfiber hHurwitz
  have hbudget' : degree + 2 ≤ (∑ y ∈ marked, fiberCard y) + 2 * genus := by
    simpa [hthree] using hbudget
  omega

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

/-- Genus-corrected degree-times-excess law.  A terminal hyperbolic orbifold of normalized excess
`excess / scale` requires source topological capacity `exceptionalBudget + 2 * genus`; in
particular, unbounded-degree projective correspondences must grow genus or punctures extensively. -/
theorem projectiveOrbifold_excess_topological_capacity
    {β : Type*} (marked : Finset β)
    (localDefect ramification exceptionalCorrection : β → ℤ)
    (degree scale excess exceptionalBudget genus : ℤ)
    (hdegree : 0 ≤ degree) (hscale : 0 ≤ scale)
    (hlocal : degree * (∑ y ∈ marked, localDefect y) ≤
      scale * ((∑ y ∈ marked, ramification y) +
        ∑ y ∈ marked, exceptionalCorrection y))
    (hHurwitz : (∑ y ∈ marked, ramification y) + 2 ≤
      2 * degree + 2 * genus)
    (hexceptional : ∑ y ∈ marked, exceptionalCorrection y ≤ exceptionalBudget)
    (hhyperbolic : 2 * scale + excess ≤ ∑ y ∈ marked, localDefect y) :
    degree * excess + 2 * scale ≤ scale * (exceptionalBudget + 2 * genus) := by
  nlinarith [mul_nonneg hdegree (sub_nonneg.mpr hhyperbolic)]

/-- In unit normalization, the genus-plus-puncture capacity is at least degree times curvature
excess.  This is the topological extensivity law in its presentation-independent form. -/
theorem projectiveCurvature_requires_extensive_topology
    (degree excess genus exceptionalBudget : ℤ)
    (hcapacity : degree * excess + 2 ≤ exceptionalBudget + 2 * genus) :
    degree * excess ≤ 2 * genus + exceptionalBudget - 2 := by
  linarith

/-- Exact positive counterpart to projective tail collapse for a torsion-free cover of the modular
orbifold `(2, 3, ∞)`.  The order-two and order-three fibres contribute all their forced
ramification, the cusp widths contribute `cuspRamification`, and Riemann--Hurwitz then says that
the covering degree is exactly six times the Euler capacity `2 * genus + cuspCard - 2`.

Unlike a fixed-source no-go, this identity exhibits a phase that can retain projective curvature:
the required topology grows at a sharp, quantized density. -/
theorem modularTriangle_projectiveCapacity_exact
    (degree genus orderTwoCard orderThreeCard cuspCard cuspRamification : ℤ)
    (horderTwo : 2 * orderTwoCard = degree)
    (horderThree : 3 * orderThreeCard = degree)
    (hcusp : cuspRamification + cuspCard = degree)
    (hHurwitz : 2 * genus - 2 =
      -2 * degree + orderTwoCard + 2 * orderThreeCard + cuspRamification) :
    degree = 6 * (2 * genus + cuspCard - 2) := by
  linarith

/-- A torsion-free modular cover saturates the genus-plus-puncture capacity inequality: no Euler
capacity is wasted and none is missing.  This is the scaled `excess = 1`, `scale = 6` form of the
orbifold excess law. -/
theorem modularTriangle_projectiveCapacity_saturates
    (degree genus cuspCard : ℤ)
    (hexact : degree = 6 * (2 * genus + cuspCard - 2)) :
    degree + 12 = 6 * (cuspCard + 2 * genus) := by
  linarith

/-- On the saturated modular phase, correspondence degree and Euler storage carry exactly the
same strict order.  Thus unbounded relational degree is supported positively, but only by
unbounded topological capacity. -/
theorem modularProjectiveStorage_order_iff
    (degree₁ degree₂ capacity₁ capacity₂ : ℤ)
    (h₁ : degree₁ + 12 = 6 * capacity₁)
    (h₂ : degree₂ + 12 = 6 * capacity₂) :
    degree₁ < degree₂ ↔ capacity₁ < capacity₂ := by
  constructor <;> intro h <;> linarith

/-- The universal `1/42` orbifold gap has an exact genus-only threshold.  If a compact relational
surface supports degree `degree` and positive hyperbolic excess, then its genus must pay at least
the Hurwitz amount `degree + 84 ≤ 84 * genus`. -/
theorem hurwitzGap_degree_add_eightyFour_le_genus
    (degree scale excess genus : ℕ)
    (hscale : 0 < scale)
    (hgap : scale ≤ 42 * excess)
    (hcapacity : degree * excess + 2 * scale ≤ 2 * scale * genus) :
    degree + 84 ≤ 84 * genus := by
  have h₁ : degree * scale ≤ degree * (42 * excess) :=
    Nat.mul_le_mul_left degree hgap
  have h₂ : (degree + 84) * scale ≤ (84 * genus) * scale := by
    calc
      (degree + 84) * scale = degree * scale + 84 * scale := by ring
      _ ≤ degree * (42 * excess) + 84 * scale :=
        Nat.add_le_add_right h₁ _
      _ = 42 * (degree * excess + 2 * scale) := by ring
      _ ≤ 42 * (2 * scale * genus) := Nat.mul_le_mul_left 42 hcapacity
      _ = (84 * genus) * scale := by ring
  exact Nat.le_of_mul_le_mul_right h₂ hscale

/-- Exact positive phase at the universal threshold.  For a torsion-free cover of the compact
triangle orbifold `(2, 3, 7)`, the forced order-two, order-three, and order-seven ramification
turns Riemann--Hurwitz into `degree = 42 * (2 * genus - 2)`. -/
theorem hurwitzTriangle_projectiveCapacity_exact
    (degree genus orderTwoCard orderThreeCard orderSevenCard : ℤ)
    (horderTwo : 2 * orderTwoCard = degree)
    (horderThree : 3 * orderThreeCard = degree)
    (horderSeven : 7 * orderSevenCard = degree)
    (hHurwitz : 2 * genus - 2 =
      -2 * degree + orderTwoCard + 2 * orderThreeCard + 6 * orderSevenCard) :
    degree = 42 * (2 * genus - 2) := by
  linarith

/-- A torsion-free `(2,3,7)` cover saturates the universal projective capacity threshold. -/
theorem hurwitzTriangle_projectiveCapacity_saturates
    (degree genus : ℤ)
    (hexact : degree = 42 * (2 * genus - 2)) :
    degree + 84 = 84 * genus := by
  linarith

/-- At the sharp Hurwitz phase, increasing correspondence degree is equivalent to increasing
genus.  There is no hidden non-topological capacity. -/
theorem hurwitzProjectiveStorage_order_iff
    (degree₁ degree₂ genus₁ genus₂ : ℤ)
    (h₁ : degree₁ + 84 = 84 * genus₁)
    (h₂ : degree₂ + 84 = 84 * genus₂) :
    degree₁ < degree₂ ↔ genus₁ < genus₂ := by
  constructor <;> intro h <;> linarith

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
