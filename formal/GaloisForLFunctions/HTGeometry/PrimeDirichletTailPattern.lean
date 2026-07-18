import Mathlib

/-!
# Tail geometry of signed prime-Dirichlet carriers

The raw orientation coordinate of a signed Dirichlet carrier is not its full sign sequence but
its projective tail class.  This file isolates the finite-support algebra behind that statement.

The analytic application is to

`P_ε(s) = ∑ₚ sign(ε p) p⁻ˢ`.

Finite changes of `ε` are finite Dirichlet-polynomial gauges, while global sign reversal does not
change the generated field.  The theorem below proves that these are the only two ways in which a
pair of Boolean orientations can be linearly dependent modulo finite support.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The multiplicative sign attached to a Boolean orientation. -/
def primeDirichletSign (b : Bool) : ℂ := if b then -1 else 1

@[simp]
theorem primeDirichletSign_false : primeDirichletSign false = 1 := rfl

@[simp]
theorem primeDirichletSign_true : primeDirichletSign true = -1 := rfl

theorem primeDirichletSign_ne_zero (b : Bool) : primeDirichletSign b ≠ 0 := by
  cases b <;> simp [primeDirichletSign]

/-- The ordered real sign used by the atomic spectral measure of a vertical Dirichlet trace. -/
def primeDirichletRealSign (b : Bool) : ℝ := if b then -1 else 1

/-- The distinguished all-positive Boolean orientation. -/
def PrimeOrientationAllPositive {P : Type*} (ε : P → Bool) : Prop :=
  ∀ p, ε p = false

/-- Every atom in a weighted signed orientation has positive mass. -/
def PrimeOrientationAtomicMassPositive {P : Type*}
    (ε : P → Bool) (weight : P → ℝ) : Prop :=
  ∀ p, 0 < primeDirichletRealSign (ε p) * weight p

/-- **Exact atomic pointing.**  With strictly positive weights, positivity of every signed atom is
equivalent to the all-positive orientation.  In the analytic application, Bochner uniqueness
identifies positive definiteness of the vertical trace with this atomic-mass condition. -/
theorem primeOrientationAtomicMassPositive_iff_allPositive
    {P : Type*} (ε : P → Bool) (weight : P → ℝ) (hweight : ∀ p, 0 < weight p) :
    PrimeOrientationAtomicMassPositive ε weight ↔ PrimeOrientationAllPositive ε := by
  constructor
  · intro hmass p
    cases hp : ε p with
    | false => rfl
    | true =>
        have hm := hmass p
        rw [hp] at hm
        simp only [primeDirichletRealSign, ↓reduceIte, neg_one_mul] at hm
        linarith [hweight p]
  · intro hall p
    rw [hall p]
    simpa only [primeDirichletRealSign, Bool.false_eq_true, ↓reduceIte, one_mul] using hweight p

theorem primeDirichletSign_eq_of_eq {a b : Bool} (h : a = b) :
    primeDirichletSign a = primeDirichletSign b := congrArg primeDirichletSign h

theorem primeDirichletSign_eq_neg_of_ne {a b : Bool} (h : a ≠ b) :
    primeDirichletSign b = -primeDirichletSign a := by
  cases a <;> cases b <;> simp_all [primeDirichletSign]

/-- Two orientations agree eventually when their disagreement set is finite. -/
def PrimeOrientationsEventuallyEqual {P : Type*} (ε δ : P → Bool) : Prop :=
  {p | ε p ≠ δ p}.Finite

/-- Two orientations are opposite eventually when their agreement set is finite. -/
def PrimeOrientationsEventuallyOpposite {P : Type*} (ε δ : P → Bool) : Prop :=
  {p | ε p = δ p}.Finite

/-- A pair of signed orientations is linearly dependent modulo finite support. -/
def PrimeOrientationTailPairDependent {P : Type*} (ε δ : P → Bool) : Prop :=
  ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧
    {p | a * primeDirichletSign (ε p) + b * primeDirichletSign (δ p) ≠ 0}.Finite

/-- The Boolean pattern displayed by a finite orientation family at one prime coordinate. -/
def primeOrientationPattern {J P : Type*} (ε : J → P → Bool) (p : P) : J → Bool :=
  fun j => ε j p

/-- Linear independence of a finite coefficient family after quotienting by finite support. -/
def TailCoefficientIndependent {I P : Type*} [Fintype I] (a : I → P → ℂ) : Prop :=
  ∀ c : I → ℂ, {p | ∑ i, c i * a i p ≠ 0}.Finite → c = 0

/-- A common nowhere-zero coordinate weight preserves tail coefficient independence. -/
theorem tailCoefficientIndependent_commonWeight_iff
    {I P : Type*} [Fintype I] (a : I → P → ℂ) (w : P → ℂ)
    (hw : ∀ p, w p ≠ 0) :
    TailCoefficientIndependent (fun i p => w p * a i p) ↔
      TailCoefficientIndependent a := by
  classical
  have hsupport : ∀ c : I → ℂ,
      {p | ∑ i, c i * (w p * a i p) ≠ 0} =
        {p | ∑ i, c i * a i p ≠ 0} := by
    intro c
    ext p
    have hsum : (∑ i, c i * (w p * a i p)) =
        w p * ∑ i, c i * a i p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp only [Set.mem_setOf_eq, hsum, mul_ne_zero_iff]
    exact and_iff_right (hw p)
  constructor
  · intro h c hsupp
    apply h c
    rwa [hsupport c]
  · intro h c hsupp
    apply h c
    rwa [← hsupport c]

/-- Linear independence of a finite orientation family after quotienting by finite support. -/
def PrimeOrientationTailIndependent {J P : Type*} [Fintype J]
    (ε : J → P → Bool) : Prop :=
  TailCoefficientIndependent (fun j p => primeDirichletSign (ε j p))

/-- The sign vectors carried by pattern fibres that occur infinitely often span the whole finite
coefficient space.  The quantified annihilator formulation avoids choosing a basis. -/
def RecurringPrimeOrientationPatternsSpan {J P : Type*} [Fintype J]
    (ε : J → P → Bool) : Prop :=
  ∀ c : J → ℂ,
    (∀ b : J → Bool,
      {p | primeOrientationPattern ε p = b}.Infinite →
        ∑ j, c j * primeDirichletSign (b j) = 0) →
    c = 0

/-- Tail independence is exactly spanning by the sign patterns that recur infinitely often. -/
theorem primeOrientationTailIndependent_iff_recurringPatternsSpan
    {J P : Type*} [Fintype J] (ε : J → P → Bool) :
    PrimeOrientationTailIndependent ε ↔ RecurringPrimeOrientationPatternsSpan ε := by
  classical
  constructor
  · intro htail c hrec
    let bad : Set (J → Bool) :=
      {b | ∑ j, c j * primeDirichletSign (b j) ≠ 0}
    have hbad : bad.Finite := Set.toFinite bad
    have hfibre : ∀ b ∈ bad,
        {p | primeOrientationPattern ε p = b}.Finite := by
      intro b hb
      have hninf : ¬ {p | primeOrientationPattern ε p = b}.Infinite := by
        intro hinf
        exact hb (hrec b hinf)
      by_contra hfin
      exact hninf hfin
    have hunion : (⋃ b ∈ bad, {p | primeOrientationPattern ε p = b}).Finite :=
      hbad.biUnion hfibre
    apply htail c
    apply hunion.subset
    intro p hp
    have hbadp : primeOrientationPattern ε p ∈ bad := by
      simpa only [bad, Set.mem_setOf_eq, primeOrientationPattern] using hp
    refine Set.mem_iUnion₂.mpr ⟨primeOrientationPattern ε p, hbadp, ?_⟩
    simp
  · intro hspan c hsupp
    apply hspan c
    intro b hinf
    by_contra hne
    have hsub : {p | primeOrientationPattern ε p = b} ⊆
        {p | ∑ j, c j * primeDirichletSign (ε j p) ≠ 0} := by
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      have hpoint : ∀ j, ε j p = b j := fun j => congrFun hp j
      simpa only [hpoint] using hne
    exact (hinf.mono hsub) hsupp

/-- The order-`k` prime coefficient in the signed Dirichlet jet rectangle. -/
def primeOrientationJetCoefficient {J P : Type*} (ε : J → P → Bool) (clock : P → ℂ)
    (m : ℕ) (jk : J × Fin (m + 1)) (p : P) : ℂ :=
  primeDirichletSign (ε jk.1 p) * clock p ^ (jk.2 : ℕ)

/-- **Exact finite-jet tail rank.**  If the recurring orientation patterns span and the prime
clock is injective, adjoining every jet order through `m` preserves tail independence.  On each
recurring pattern fibre, a putative finite-support relation becomes a polynomial with infinitely
many distinct clock roots; its coefficients vanish, and recurring-pattern spanning then kills
each orientation column. -/
theorem primeOrientationJetCoefficient_tailIndependent
    {J P : Type*} [Fintype J] (ε : J → P → Bool) (clock : P → ℂ)
    (hclock : Function.Injective clock) (hspan : RecurringPrimeOrientationPatternsSpan ε)
    (m : ℕ) :
    TailCoefficientIndependent (primeOrientationJetCoefficient ε clock m) := by
  classical
  intro c hsupp
  have hcolumn : ∀ k : Fin (m + 1), (fun j => c (j, k)) = 0 := by
    intro k
    apply hspan (fun j => c (j, k))
    intro b hb
    let Q : Polynomial ℂ :=
      ∑ r : Fin (m + 1),
        Polynomial.C (∑ j, c (j, r) * primeDirichletSign (b j)) *
          Polynomial.X ^ (r : ℕ)
    have hfibreTail :
        ({p | primeOrientationPattern ε p = b} \
          {p | ∑ jk, c jk * primeOrientationJetCoefficient ε clock m jk p ≠ 0}).Infinite :=
      hb.diff hsupp
    have himage :
        (clock '' ({p | primeOrientationPattern ε p = b} \
          {p | ∑ jk, c jk * primeOrientationJetCoefficient ε clock m jk p ≠ 0})).Infinite :=
      hfibreTail.image hclock.injOn
    have hQ : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot Q
      apply himage.mono
      intro x hx
      obtain ⟨p, hp, rfl⟩ := hx
      change Polynomial.eval (clock p) Q = 0
      have hpPattern : ∀ j, ε j p = b j :=
        fun j => congrFun hp.1 j
      have hpzero :
          ∑ jk, c jk * primeOrientationJetCoefficient ε clock m jk p = 0 := by
        simpa only [Set.mem_setOf_eq, not_not] using hp.2
      calc
        Polynomial.eval (clock p) Q =
            ∑ r : Fin (m + 1),
              (∑ j, c (j, r) * primeDirichletSign (b j)) * clock p ^ (r : ℕ) := by
                simp only [Q, map_sum, Polynomial.eval_finsetSum, Polynomial.eval_mul,
                  Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        _ = ∑ r : Fin (m + 1), ∑ j,
              c (j, r) *
                (primeDirichletSign (ε j p) * clock p ^ (r : ℕ)) := by
              apply Finset.sum_congr rfl
              intro r _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              rw [hpPattern j]
              ring
        _ = ∑ jk : J × Fin (m + 1),
              c jk * primeOrientationJetCoefficient ε clock m jk p := by
              rw [Fintype.sum_prod_type]
              rw [Finset.sum_comm]
              rfl
        _ = 0 := hpzero
    have hcoeff := congrArg (fun R : Polynomial ℂ => R.coeff (k : ℕ)) hQ
    simp only [Q, Polynomial.finsetSum_coeff] at hcoeff
    rw [Finset.sum_eq_single k] at hcoeff
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl, Polynomial.coeff_zero] at hcoeff
      exact hcoeff
    · intro r _ hr
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      exact fun h => hr (Fin.ext h.symm)
    · simp
  funext jk
  have hk := congrFun (hcolumn jk.2) jk.1
  simpa using hk

/-- Tail-independent Boolean orientations have a full-rank signed Dirichlet jet rectangle at
every finite order. -/
theorem primeOrientationJetCoefficient_tailIndependent_of_orientation
    {J P : Type*} [Fintype J] (ε : J → P → Bool) (clock : P → ℂ)
    (hclock : Function.Injective clock) (htail : PrimeOrientationTailIndependent ε)
    (m : ℕ) :
    TailCoefficientIndependent (primeOrientationJetCoefficient ε clock m) :=
  primeOrientationJetCoefficient_tailIndependent ε clock hclock
    ((primeOrientationTailIndependent_iff_recurringPatternsSpan ε).mp htail) m

/-- A finite shift--jet system is rigid on infinite coordinate fibres when no nonzero linear
combination of its shift--clock monomials can vanish away from a finite subset of such a fibre.

For the prime-Dirichlet application, `scale p = p⁻¹`, `clock p = log p`, and `shift` takes distinct
nonnegative integer values.  The hypothesis is then the classical dominance property of finite
exponential-polynomial sums: peel off the least shift and let `p → ∞`. -/
def ShiftClockFiberIndependent {A P : Type*} [Fintype A]
    (shift : A → ℕ) (scale clock : P → ℂ) (m : ℕ) : Prop :=
  ∀ U : Set P, U.Infinite → ∀ d : A × Fin (m + 1) → ℂ,
    {p | p ∈ U ∧
      ∑ ak, d ak * scale p ^ shift ak.1 * clock p ^ (ak.2 : ℕ) ≠ 0}.Finite →
    d = 0

/-- The prime-orientation coefficient carrying both a finite shift palette and a finite logarithmic
jet palette. -/
def primeOrientationShiftJetCoefficient {J A P : Type*}
    (ε : J → P → Bool) (shift : A → ℕ) (scale clock : P → ℂ) (m : ℕ)
    (jak : J × (A × Fin (m + 1))) (p : P) : ℂ :=
  primeDirichletSign (ε jak.1 p) * scale p ^ shift jak.2.1 *
    clock p ^ (jak.2.2 : ℕ)

/-- **Finite shifted-tail rank.**  Recurring-pattern spanning and the classical rigidity of the
finite shift--clock system together imply tail independence of the complete
orientation--shift--jet rectangle.  This is the abstract finite theorem used before the classical
Dirichlet-series Jacobian transfer. -/
theorem primeOrientationShiftJetCoefficient_tailIndependent
    {J A P : Type*} [Fintype J] [Fintype A]
    (ε : J → P → Bool) (shift : A → ℕ) (scale clock : P → ℂ)
    (hspan : RecurringPrimeOrientationPatternsSpan ε)
    (m : ℕ) (hrigid : ShiftClockFiberIndependent shift scale clock m) :
    TailCoefficientIndependent
      (primeOrientationShiftJetCoefficient ε shift scale clock m) := by
  classical
  intro c hsupp
  have hcolumn : ∀ ak : A × Fin (m + 1), (fun j => c (j, ak)) = 0 := by
    intro ak
    apply hspan (fun j => c (j, ak))
    intro b hb
    let U : Set P := {p | primeOrientationPattern ε p = b}
    let d : A × Fin (m + 1) → ℂ := fun rk =>
      ∑ j, c (j, rk) * primeDirichletSign (b j)
    have hd : d = 0 := by
      apply hrigid U hb d
      apply hsupp.subset
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      rcases hp with ⟨hpPattern, hpne⟩
      have hpoint : ∀ j, ε j p = b j := fun j => congrFun hpPattern j
      intro hzero
      apply hpne
      calc
        ∑ rk : A × Fin (m + 1),
              (∑ j, c (j, rk) * primeDirichletSign (b j)) *
                scale p ^ shift rk.1 * clock p ^ (rk.2 : ℕ) =
            ∑ jak, c jak *
              primeOrientationShiftJetCoefficient ε shift scale clock m jak p := by
                conv_rhs =>
                  rw [Fintype.sum_prod_type]
                  rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro rk _
                rw [Finset.sum_mul, Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro j _
                simp only [primeOrientationShiftJetCoefficient]
                rw [hpoint j]
                ring
        _ = 0 := hzero
    have hak := congrFun hd ak
    simpa only [d, Pi.zero_apply] using hak
  funext jak
  have hjak := congrFun (hcolumn jak.2) jak.1
  simpa using hjak

/-- Tail-independent orientations have full shifted-tail rank whenever the underlying finite
shift--clock system is rigid on infinite fibres. -/
theorem primeOrientationShiftJetCoefficient_tailIndependent_of_orientation
    {J A P : Type*} [Fintype J] [Fintype A]
    (ε : J → P → Bool) (shift : A → ℕ) (scale clock : P → ℂ)
    (htail : PrimeOrientationTailIndependent ε)
    (m : ℕ) (hrigid : ShiftClockFiberIndependent shift scale clock m) :
    TailCoefficientIndependent
      (primeOrientationShiftJetCoefficient ε shift scale clock m) :=
  primeOrientationShiftJetCoefficient_tailIndependent ε shift scale clock
    ((primeOrientationTailIndependent_iff_recurringPatternsSpan ε).mp htail) m hrigid

/-- **Projective tail classification.**  Two Boolean sign sequences are linearly dependent modulo
finite support exactly when they agree eventually or are opposite eventually.  Thus the
two-dimensional tail matroid remembers precisely the quotient by finite changes and global sign
reversal. -/
theorem primeOrientationTailPairDependent_iff
    {P : Type*} (ε δ : P → Bool) :
    PrimeOrientationTailPairDependent ε δ ↔
      PrimeOrientationsEventuallyEqual ε δ ∨
        PrimeOrientationsEventuallyOpposite ε δ := by
  constructor
  · rintro ⟨a, b, hab, hsupport⟩
    by_cases hne : {p | ε p ≠ δ p}.Finite
    · exact Or.inl hne
    by_cases heq : {p | ε p = δ p}.Finite
    · exact Or.inr heq
    exfalso
    have hneInf : {p | ε p ≠ δ p}.Infinite := hne
    have heqInf : {p | ε p = δ p}.Infinite := heq
    obtain ⟨p, hpne, hpout⟩ := (hneInf.diff hsupport).nonempty
    obtain ⟨q, hqeq, hqout⟩ := (heqInf.diff hsupport).nonempty
    have hpzero :
        a * primeDirichletSign (ε p) + b * primeDirichletSign (δ p) = 0 := by
      simpa only [Set.mem_setOf_eq, not_not] using hpout
    have hqzero :
        a * primeDirichletSign (ε q) + b * primeDirichletSign (δ q) = 0 := by
      simpa only [Set.mem_setOf_eq, not_not] using hqout
    have habSub : a - b = 0 := by
      rw [primeDirichletSign_eq_neg_of_ne hpne] at hpzero
      have hs := primeDirichletSign_ne_zero (ε p)
      apply mul_left_cancel₀ hs
      calc
        primeDirichletSign (ε p) * (a - b)
            = a * primeDirichletSign (ε p) +
                b * (-primeDirichletSign (ε p)) := by ring
        _ = 0 := hpzero
        _ = primeDirichletSign (ε p) * 0 := by ring
    have habAdd : a + b = 0 := by
      rw [← primeDirichletSign_eq_of_eq hqeq] at hqzero
      have hs := primeDirichletSign_ne_zero (ε q)
      apply mul_left_cancel₀ hs
      calc
        primeDirichletSign (ε q) * (a + b)
            = a * primeDirichletSign (ε q) +
                b * primeDirichletSign (ε q) := by ring
        _ = 0 := hqzero
        _ = primeDirichletSign (ε q) * 0 := by ring
    have ha : a = 0 := by linear_combination (habAdd + habSub) / 2
    have hb : b = 0 := by linear_combination (habAdd - habSub) / 2
    exact hab.elim (fun h => h ha) (fun h => h hb)
  · rintro (heq | hopp)
    · refine ⟨1, -1, Or.inl one_ne_zero, ?_⟩
      apply heq.subset
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      intro hsame
      rw [primeDirichletSign_eq_of_eq hsame] at hp
      apply hp
      ring
    · refine ⟨1, 1, Or.inl one_ne_zero, ?_⟩
      apply hopp.subset
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      by_contra hne
      apply hp
      rw [primeDirichletSign_eq_neg_of_ne hne]
      ring

/-- **Finite/cofinite law relative to the positive orientation.**  A Boolean orientation spans
the same projective tail line as the all-positive orientation exactly when its negative set is
finite or its positive set is finite.  Thus an orientation with both signs occurring infinitely
often is a genuinely transverse tail direction. -/
theorem primeOrientationTailPairDependent_allPositive_iff
    {P : Type*} (ε : P → Bool) :
    PrimeOrientationTailPairDependent ε (fun _ => false) ↔
      {p | ε p = true}.Finite ∨ {p | ε p = false}.Finite := by
  have hnegative : {p | ε p ≠ false} = {p | ε p = true} := by
    ext p
    cases ε p <;> simp
  simpa only [PrimeOrientationsEventuallyEqual, PrimeOrientationsEventuallyOpposite,
    hnegative] using primeOrientationTailPairDependent_iff ε (fun _ => false)

end

end GaloisForLFunctions.HTGeometry
