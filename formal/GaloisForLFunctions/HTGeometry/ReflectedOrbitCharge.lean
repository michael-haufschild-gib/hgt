import GaloisForLFunctions.HTGeometry.OrbitChargeSuperselection

/-!
# Reflected shift-orbit charge and the doubling law

Positive- and negative-slope Gamma factors are exchanged by Euler reflection.  Modulo the
resulting differentially algebraic trigonometric factor, a negative-orientation charge is the
inverse of the reflected positive-orientation charge.  This file formalizes the coefficient-level
topology of that statement.

For an involution `r` of the orbit labels, `orientedCharge r qPlus qMinus` is the difference between
the positive charge and the reflected negative charge.  It is a complete invariant modulo creation
of reflected neutral pairs.  Charge conjugation is `q ↦ -r(q)`.  Over integer coefficients every
nonzero conjugation-symmetric sector has support on at least two distinct labels, while every free
two-cycle carries an explicit nonzero symmetric pair.  Thus reflection symmetry forces exact
charge doubling rather than erasing the hypertranscendental sector.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Reindex a finite charge vector by the reflection of its orbit labels. -/
def reflectedCharge {ι A : Type*} [AddCommGroup A]
    (r : ι ≃ ι) (q : ι →₀ A) : ι →₀ A :=
  Finsupp.equivMapDomain r q

/-- Charge conjugation: orientation reversal is reflection followed by additive inversion. -/
def chargeConjugate {ι A : Type*} [AddCommGroup A]
    (r : ι ≃ ι) (q : ι →₀ A) : ι →₀ A :=
  -reflectedCharge r q

/-- The elementary charge-conjugate pair supported on the orbit of `i`. -/
def reflectionAntiInvariantPair {ι A : Type*} [AddCommGroup A]
    [DecidableEq ι] (r : ι ≃ ι) (i : ι) (a : A) : ι →₀ A :=
  Finsupp.single i a - Finsupp.single (r i) a

/-- An involutive equivalence agrees pointwise with its inverse. -/
theorem involutiveEquiv_symm_apply {ι : Type*} (r : ι ≃ ι)
    (hr : Function.Involutive r) (i : ι) :
    r.symm i = r i := by
  apply r.injective
  simp [hr i]

@[simp]
theorem reflectedCharge_single {ι A : Type*} [AddCommGroup A]
    [DecidableEq ι] (r : ι ≃ ι) (i : ι) (a : A) :
    reflectedCharge r (Finsupp.single i a) = Finsupp.single (r i) a := by
  exact Finsupp.equivMapDomain_single r i a

theorem reflectedCharge_sub {ι A : Type*} [AddCommGroup A]
    (r : ι ≃ ι) (p q : ι →₀ A) :
    reflectedCharge r (p - q) = reflectedCharge r p - reflectedCharge r q := by
  ext i
  simp [reflectedCharge, Finsupp.equivMapDomain_apply]

/-- Reindexing twice by an involutive orbit reflection returns the original charge. -/
theorem reflectedCharge_involutive {ι A : Type*} [AddCommGroup A]
    (r : ι ≃ ι) (hr : Function.Involutive r) (q : ι →₀ A) :
    reflectedCharge r (reflectedCharge r q) = q := by
  ext i
  simp [reflectedCharge, Finsupp.equivMapDomain_apply,
    involutiveEquiv_symm_apply r hr, hr i]

/-- Charge conjugation is itself an involution. -/
theorem chargeConjugate_involutive {ι A : Type*} [AddCommGroup A]
    (r : ι ≃ ι) (hr : Function.Involutive r) (q : ι →₀ A) :
    chargeConjugate r (chargeConjugate r q) = q := by
  ext i
  simp [chargeConjugate, reflectedCharge, Finsupp.equivMapDomain_apply,
    involutiveEquiv_symm_apply r hr, hr i]

/-- A reflected pair is fixed by charge conjugation. -/
theorem reflectionAntiInvariantPair_conjugate {ι A : Type*} [AddCommGroup A]
    [DecidableEq ι] (r : ι ≃ ι) (hr : Function.Involutive r) (i : ι) (a : A) :
    chargeConjugate r (reflectionAntiInvariantPair r i a) =
      reflectionAntiInvariantPair r i a := by
  rw [chargeConjugate, reflectionAntiInvariantPair, reflectedCharge_sub,
    reflectedCharge_single, reflectedCharge_single, hr i]
  abel

/-- A conjugation-symmetric integral charge vanishes at every fixed orbit label. -/
theorem chargeConjugate_fixed_eq_zero
    {ι : Type*} [DecidableEq ι] (r : ι ≃ ι) (q : ι →₀ ℤ)
    (hq : chargeConjugate r q = q) {i : ι} (hi : r i = i) :
    q i = 0 := by
  have hri : r.symm i = i := by
    apply r.injective
    simp [hi]
  have h := DFunLike.congr_fun hq i
  simp [chargeConjugate, reflectedCharge, Finsupp.equivMapDomain_apply, hri] at h
  omega

/-- Every nonzero conjugation-symmetric integral sector contains a genuine two-cycle with opposite
nonzero charges. -/
theorem chargeConjugate_ne_zero_has_pair
    {ι : Type*} [DecidableEq ι] (r : ι ≃ ι) (hr : Function.Involutive r)
    (q : ι →₀ ℤ) (hq : chargeConjugate r q = q) (hne : q ≠ 0) :
    ∃ i, q i ≠ 0 ∧ r i ≠ i ∧ q (r i) = -q i := by
  have hex : ∃ i, q i ≠ 0 := by
    by_contra h
    apply hne
    ext i
    simp only [Finsupp.zero_apply]
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hex
  have hri : r.symm i = r i := by
    apply r.injective
    simp [hr i]
  have hrel := DFunLike.congr_fun hq i
  simp [chargeConjugate, reflectedCharge, Finsupp.equivMapDomain_apply, hri] at hrel
  have hnfix : r i ≠ i := by
    intro hfix
    exact hi (chargeConjugate_fixed_eq_zero r q hq hfix)
  exact ⟨i, hi, hnfix, by omega⟩

/-- **Reflection charge-doubling law.** Every nonzero conjugation-symmetric integral charge vector
has at least two occupied orbit labels. -/
theorem chargeConjugate_support_card_two_le
    {ι : Type*} [DecidableEq ι] (r : ι ≃ ι) (hr : Function.Involutive r)
    (q : ι →₀ ℤ) (hq : chargeConjugate r q = q) (hne : q ≠ 0) :
    2 ≤ q.support.card := by
  obtain ⟨i, hi, hri, hpair⟩ := chargeConjugate_ne_zero_has_pair r hr q hq hne
  have hpairne : q (r i) ≠ 0 := by omega
  have hsub : ({i, r i} : Finset ι) ⊆ q.support := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact Finsupp.mem_support_iff.mpr hi
    · exact Finsupp.mem_support_iff.mpr hpairne
  have hcard : ({i, r i} : Finset ι).card = 2 := by simp [Ne.symm hri]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- The surviving charge of a finite positive/negative orientation pair. -/
def orientedCharge {ι A : Type*} [AddCommGroup A]
    (r : ι ≃ ι) (qPlus qMinus : ι →₀ A) : ι →₀ A :=
  qPlus - reflectedCharge r qMinus

/-- A reflected particle--antiparticle pair, which carries zero oriented charge. -/
def reflectionNeutralPair {ι A : Type*} [AddCommGroup A]
    (r : ι ≃ ι) (q : ι →₀ A) : (ι →₀ A) × (ι →₀ A) :=
  (reflectedCharge r q, q)

/-- Reflected pair creation does not change oriented charge. -/
theorem orientedCharge_reflectionNeutralPair
    {ι A : Type*} [AddCommGroup A] (r : ι ≃ ι) (q : ι →₀ A) :
    orientedCharge r (reflectionNeutralPair r q).1 (reflectionNeutralPair r q).2 = 0 := by
  simp [orientedCharge, reflectionNeutralPair]

/-- Every two-orientation datum is its oriented charge in the positive sector plus one reflected
neutral pair. -/
theorem orientedCharge_normalForm
    {ι A : Type*} [AddCommGroup A] (r : ι ≃ ι) (qPlus qMinus : ι →₀ A) :
    (qPlus, qMinus) =
      (orientedCharge r qPlus qMinus, 0) + reflectionNeutralPair r qMinus := by
  apply Prod.ext
  · simp [orientedCharge, reflectionNeutralPair]
  · simp [reflectionNeutralPair]

/-- **Complete oriented superselection law.** Two positive/negative charge data have the same
oriented charge exactly when their difference is creation of a reflected neutral pair. -/
theorem orientedCharge_eq_iff_difference_reflectionNeutralPair
    {ι A : Type*} [AddCommGroup A] (r : ι ≃ ι)
    (pPlus pMinus qPlus qMinus : ι →₀ A) :
    orientedCharge r pPlus pMinus = orientedCharge r qPlus qMinus ↔
      ∃ g, (pPlus - qPlus, pMinus - qMinus) = reflectionNeutralPair r g := by
  constructor
  · intro h
    refine ⟨pMinus - qMinus, ?_⟩
    apply Prod.ext
    · simp only [reflectionNeutralPair]
      change pPlus - qPlus = reflectedCharge r (pMinus - qMinus)
      ext i
      have hi := DFunLike.congr_fun h i
      simp [orientedCharge, reflectedCharge, Finsupp.equivMapDomain_apply] at hi ⊢
      calc
        pPlus i - qPlus i =
            (pPlus i - pMinus (r.symm i)) + (pMinus (r.symm i) - qPlus i) := by
              abel
        _ = (qPlus i - qMinus (r.symm i)) +
            (pMinus (r.symm i) - qPlus i) := by rw [hi]
        _ = pMinus (r.symm i) - qMinus (r.symm i) := by abel
    · simp [reflectionNeutralPair]
  · rintro ⟨g, h⟩
    have hp := congrArg Prod.fst h
    have hm := congrArg Prod.snd h
    simp [reflectionNeutralPair] at hp hm
    ext i
    simp [orientedCharge, reflectedCharge, Finsupp.equivMapDomain_apply] at hp hm ⊢
    have hpg : pPlus i - qPlus i = g (r.symm i) := by
      simpa [reflectedCharge, Finsupp.equivMapDomain_apply] using DFunLike.congr_fun hp i
    have hmg : pMinus (r.symm i) - qMinus (r.symm i) = g (r.symm i) := by
      exact DFunLike.congr_fun hm (r.symm i)
    have heq : pPlus i - qPlus i =
        pMinus (r.symm i) - qMinus (r.symm i) := hpg.trans hmg.symm
    calc
      pPlus i - pMinus (r.symm i) =
          (pPlus i - qPlus i) + (qPlus i - pMinus (r.symm i)) := by abel
      _ = (pMinus (r.symm i) - qMinus (r.symm i)) +
          (qPlus i - pMinus (r.symm i)) := by rw [heq]
      _ = qPlus i - qMinus (r.symm i) := by abel

end

end GaloisForLFunctions
