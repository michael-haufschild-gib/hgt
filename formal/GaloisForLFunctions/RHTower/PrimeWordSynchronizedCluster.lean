import GaloisForLFunctions.RHTower.PrimeLeeYangPolydisk
import GaloisForLFunctions.RHTower.PrimeSupportMultivariateLiftMarker

/-!
# Prime-word synchronized ferromagnetic clusters

The Fortuin--Kasteleyn / Edwards--Sokal cluster picture assigns one common spin to every vertex in
a connected ferromagnetic cluster.  At zero temperature such a cluster has two aligned pure states.
After dividing by one pure-state weight, its external-field partition block has the form

`1 + ∏ p ∈ P, u_p`.

For a prime word, the field monomial is exactly its existing squarefree multivariate support marker
evaluated at the centered prime Lee--Yang fields.  The marker therefore has an analytic consumer
which retains the full distinct-prime incidence lost by scalar support-cardinality jets.

The norm of the monomial is

`exp ((∑ p ∈ P, log p) * Im z)`.

On a nonempty support the logarithmic sum is positive, so every zero of the two-state block lies on
the centered critical line.  The conclusion survives finite products of nonempty prime-word blocks.
This is a `[BRIDGE]`: no claim is made here that the completed source factors into these blocks.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open MvPolynomial

noncomputable section

/-- Field monomial of one synchronized ferromagnetic cluster on the finite prime support `P`. -/
def synchronizedPrimeClusterField
    (P : Finset Nat.Primes) (z : ℂ) : ℂ :=
  ∏ p ∈ P, _root_.RHTower.centeredPrimeLeeYangField p z

/-- Normalized two-pure-state partition block of a synchronized prime cluster. -/
def synchronizedPrimeClusterPartition
    (P : Finset Nat.Primes) (z : ℂ) : ℂ :=
  1 + synchronizedPrimeClusterField P z

/-- The cluster field monomial is the squarefree support marker evaluated at the centered prime
Lee--Yang fields. -/
theorem eval₂Hom_primeWordSquarefreeMarker_centeredPrimeLeeYangField
    (w : List Nat.Primes) (z : ℂ) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
        (fun p => _root_.RHTower.centeredPrimeLeeYangField p z)
        (primeWordSquarefreeMarker w) =
      synchronizedPrimeClusterField
        (GaloisForLFunctions.primeWordSupport w) z := by
  rw [eval₂Hom_primeWordSquarefreeMarker]
  rfl

/-- Exact radial law for the synchronized-cluster field monomial. -/
theorem norm_synchronizedPrimeClusterField
    (P : Finset Nat.Primes) (z : ℂ) :
    ‖synchronizedPrimeClusterField P z‖ =
      Real.exp ((∑ p ∈ P, _root_.RHTower.primeLeeYangLog p) * z.im) := by
  simp only [synchronizedPrimeClusterField, norm_prod,
    _root_.RHTower.norm_centeredPrimeLeeYangField]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_mul]

/-- A nonempty prime cluster has strictly positive total logarithmic field scale. -/
theorem sum_primeLeeYangLog_pos
    {P : Finset Nat.Primes} (hP : P.Nonempty) :
    0 < ∑ p ∈ P, _root_.RHTower.primeLeeYangLog p := by
  obtain ⟨p, hp⟩ := hP
  exact Finset.sum_pos'
    (fun q _ => (_root_.RHTower.primeLeeYangLog_pos q).le)
    ⟨p, hp, _root_.RHTower.primeLeeYangLog_pos p⟩

/-- Every zero of a nonempty synchronized prime-cluster block lies on the centered critical line. -/
theorem synchronizedPrimeClusterPartition_zero_im
    {P : Finset Nat.Primes} (hP : P.Nonempty) {z : ℂ}
    (hz : synchronizedPrimeClusterPartition P z = 0) :
    z.im = 0 := by
  have hfield : synchronizedPrimeClusterField P z = -1 :=
    eq_neg_of_add_eq_zero_right hz
  have hnorm : ‖synchronizedPrimeClusterField P z‖ = 1 := by
    rw [hfield, norm_neg, norm_one]
  rw [norm_synchronizedPrimeClusterField, Real.exp_eq_one_iff] at hnorm
  exact (mul_eq_zero.mp hnorm).resolve_left (sum_primeLeeYangLog_pos hP).ne'

/-- The empty support has the constant nonvanishing two-state block. -/
@[simp] theorem synchronizedPrimeClusterPartition_empty (z : ℂ) :
    synchronizedPrimeClusterPartition ∅ z = 2 := by
  norm_num [synchronizedPrimeClusterPartition, synchronizedPrimeClusterField]

/-- At `z = I`, the cluster field is the ordinary product of the primes in its support. -/
theorem synchronizedPrimeClusterField_I (P : Finset Nat.Primes) :
    synchronizedPrimeClusterField P Complex.I =
      ((∏ p ∈ P, (p : ℕ) : ℕ) : ℂ) := by
  rw [synchronizedPrimeClusterField]
  simp_rw [_root_.RHTower.centeredPrimeLeeYangField_I]
  norm_cast

/-- Prime factorization reads membership in a finite squarefree prime product. -/
theorem factorization_primeSupportProduct
    (P : Finset Nat.Primes) (p : Nat.Primes) :
    (∏ q ∈ P, (q : ℕ)).factorization (p : ℕ) =
      if p ∈ P then 1 else 0 := by
  classical
  rw [Nat.factorization_prod_apply]
  · by_cases hp : p ∈ P
    · rw [Finset.sum_eq_single p]
      · simp [p.2.factorization_self, hp]
      · intro q _ hqp
        have hzero : (q : ℕ).factorization (p : ℕ) = 0 := by
          by_contra hne
          have hnat : (q : ℕ) = (p : ℕ) := q.2.eq_of_factorization_pos hne
          exact hqp (Subtype.ext hnat)
        simp [hzero]
      · exact fun hnot => (hnot hp).elim
    · rw [Finset.sum_eq_zero]
      · simp [hp]
      · intro q hq
        have hqp : q ≠ p := fun heq => hp (heq ▸ hq)
        have hzero : (q : ℕ).factorization (p : ℕ) = 0 := by
          by_contra hne
          have hnat : (q : ℕ) = (p : ℕ) := q.2.eq_of_factorization_pos hne
          exact hqp (Subtype.ext hnat)
        exact hzero
  · intro q _
    exact q.2.ne_zero

/-- Unique factorization makes a finite squarefree prime product faithful to its support. -/
theorem primeSupportProduct_injective :
    Function.Injective (fun P : Finset Nat.Primes => ∏ p ∈ P, (p : ℕ)) := by
  intro P Q hPQ
  ext p
  have hfac := congrArg (fun n : ℕ => n.factorization (p : ℕ)) hPQ
  change (∏ q ∈ P, (q : ℕ)).factorization (p : ℕ) =
    (∏ q ∈ Q, (q : ℕ)).factorization (p : ℕ) at hfac
  rw [factorization_primeSupportProduct,
    factorization_primeSupportProduct] at hfac
  by_cases hp : p ∈ P <;> by_cases hq : p ∈ Q <;> simp [hp, hq] at hfac ⊢

/-- The synchronized-cluster analytic specialization at `I` retains the complete finite prime
support, not merely its cardinality or parity shadow. -/
theorem synchronizedPrimeClusterField_I_injective :
    Function.Injective
      (fun P : Finset Nat.Primes => synchronizedPrimeClusterField P Complex.I) := by
  intro P Q hPQ
  change synchronizedPrimeClusterField P Complex.I =
    synchronizedPrimeClusterField Q Complex.I at hPQ
  rw [synchronizedPrimeClusterField_I,
    synchronizedPrimeClusterField_I] at hPQ
  have hnat : (∏ p ∈ P, (p : ℕ)) = ∏ p ∈ Q, (p : ℕ) := by
    exact_mod_cast hPQ
  exact primeSupportProduct_injective hnat

/-- The normalized cluster partition attached to the distinct-prime support of a word. -/
def primeWordSynchronizedClusterPartition
    (w : List Nat.Primes) (z : ℂ) : ℂ :=
  synchronizedPrimeClusterPartition
    (GaloisForLFunctions.primeWordSupport w) z

/-- The prime-word block is literally `1 +` the analytically evaluated support marker. -/
theorem primeWordSynchronizedClusterPartition_eq_one_add_markerEval
    (w : List Nat.Primes) (z : ℂ) :
    primeWordSynchronizedClusterPartition w z =
      1 + MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
        (fun p => _root_.RHTower.centeredPrimeLeeYangField p z)
        (primeWordSquarefreeMarker w) := by
  rw [eval₂Hom_primeWordSquarefreeMarker_centeredPrimeLeeYangField]
  rfl

/-- Equality of the centered-field marker evaluations at `I` is equivalent to equality of the
complete distinct-prime supports. -/
theorem centeredPrimeLeeYangMarkerEval_I_eq_iff_support_eq
    (u w : List Nat.Primes) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
        (fun p => _root_.RHTower.centeredPrimeLeeYangField p Complex.I)
        (primeWordSquarefreeMarker u) =
      MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
        (fun p => _root_.RHTower.centeredPrimeLeeYangField p Complex.I)
        (primeWordSquarefreeMarker w) ↔
      GaloisForLFunctions.primeWordSupport u =
        GaloisForLFunctions.primeWordSupport w := by
  rw [eval₂Hom_primeWordSquarefreeMarker_centeredPrimeLeeYangField,
    eval₂Hom_primeWordSquarefreeMarker_centeredPrimeLeeYangField]
  constructor
  · intro h
    exact synchronizedPrimeClusterField_I_injective h
  · exact congrArg (fun P => synchronizedPrimeClusterField P Complex.I)

/-- Direct application to the parity no-go pair: the centered Lee--Yang specialization still
separates the words that every binary signing character identifies. -/
theorem centeredPrimeLeeYangMarkerEval_I_separates_parityBlindWords :
    MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
        (fun p : Fin 2 =>
          _root_.RHTower.centeredPrimeLeeYangField
            (if p = 0 then ⟨2, by norm_num⟩ else ⟨3, by norm_num⟩) Complex.I)
        (primeWordSquarefreeMarker singletonLiftWord) ≠
      MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
        (fun p : Fin 2 =>
          _root_.RHTower.centeredPrimeLeeYangField
            (if p = 0 then ⟨2, by norm_num⟩ else ⟨3, by norm_num⟩) Complex.I)
        (primeWordSquarefreeMarker doubledSecondLiftWord) := by
  simp [eval₂Hom_primeWordSquarefreeMarker, singletonLiftWord_support,
    doubledSecondLiftWord_support, _root_.RHTower.centeredPrimeLeeYangField_I]

/-- A prime word with nonempty distinct-prime support has only real centered zeros. -/
theorem primeWordSynchronizedClusterPartition_zero_im
    {w : List Nat.Primes}
    (hw : (GaloisForLFunctions.primeWordSupport w).Nonempty)
    {z : ℂ} (hz : primeWordSynchronizedClusterPartition w z = 0) :
    z.im = 0 := by
  exact synchronizedPrimeClusterPartition_zero_im hw hz

/-- The syntactic nonempty-word form of the support-localized zero theorem. -/
theorem primeWordSynchronizedClusterPartition_zero_im_of_ne_nil
    {w : List Nat.Primes} (hw : w ≠ []) {z : ℂ}
    (hz : primeWordSynchronizedClusterPartition w z = 0) :
    z.im = 0 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons p tail =>
      apply primeWordSynchronizedClusterPartition_zero_im (w := p :: tail)
      · exact ⟨p, by simp [GaloisForLFunctions.primeWordSupport]⟩
      · exact hz

/-- Finite product of the synchronized partition blocks attached to a prime-word ensemble. -/
def primeWordSynchronizedClusterEnsemblePartition
    (W : Finset (List Nat.Primes)) (z : ℂ) : ℂ :=
  ∏ w ∈ W, primeWordSynchronizedClusterPartition w z

/-- Direct downstream consumer: every zero of a finite product of nonempty prime-word cluster
blocks lies on the centered critical line. -/
theorem primeWordSynchronizedClusterEnsemblePartition_zero_im
    {W : Finset (List Nat.Primes)}
    (hW : ∀ w ∈ W, (GaloisForLFunctions.primeWordSupport w).Nonempty)
    {z : ℂ}
    (hz : primeWordSynchronizedClusterEnsemblePartition W z = 0) :
    z.im = 0 := by
  rw [primeWordSynchronizedClusterEnsemblePartition,
    Finset.prod_eq_zero_iff] at hz
  obtain ⟨w, hwW, hwzero⟩ := hz
  exact primeWordSynchronizedClusterPartition_zero_im (hW w hwW) hwzero

end

end GaloisForLFunctions.RHTower
