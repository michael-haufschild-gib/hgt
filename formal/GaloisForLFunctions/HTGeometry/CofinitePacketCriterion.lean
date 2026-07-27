import GaloisForLFunctions.HTGeometry.CofinitePacketVandermonde

/-!
# A checkable criterion for cofinite jet packets

The Vandermonde structure behind the prime-indicator packet is not special to that profile.  Read at
exponent zero, the packet matrix of *any* profile is the Vandermonde matrix in the rotated prime
logarithms, scaled row-wise by the profile's values at the chosen primes.  Only two things can go
wrong: a scale factor vanishes, or two nodes coincide — and distinct primes never give equal
logarithms.

So the whole condition reduces to a support statement:

**a profile that is nonzero at infinitely many primes has a cofinite jet packet.**

The prime indicator is the special case where the support is all of the primes.

* `primeProfileJetPacketMatrix_unit_apply` — the row-scaled Vandermonde form;
* **`cofinitePrimeProfileJetPacket_of_infinite_prime_support`** — the criterion.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Choosing distinct primes from an infinite set. -/
theorem exists_injective_primes_mem (m : ℕ) {S : Set Nat.Primes} (hS : S.Infinite) :
    ∃ q : Fin (m + 1) → Nat.Primes, Function.Injective q ∧ ∀ i, q i ∈ S := by
  classical
  obtain ⟨t, hts, htcard⟩ := hS.exists_subset_card_eq (m + 1)
  refine ⟨fun i => ((Finset.equivFinOfCardEq htcard).symm i : Nat.Primes), ?_, ?_⟩
  · intro i j hij
    have : (Finset.equivFinOfCardEq htcard).symm i = (Finset.equivFinOfCardEq htcard).symm j :=
      Subtype.ext hij
    simpa using congrArg (Finset.equivFinOfCardEq htcard) this
  · intro i
    exact hts ((Finset.equivFinOfCardEq htcard).symm i).2

/-- **The packet matrix is a row-scaled Vandermonde.**  At exponent zero the entry is the profile
value at the row's prime times the rotated logarithm of that prime raised to the column's jet
order. -/
theorem primeProfileJetPacketMatrix_unit_apply (g : ArithmeticFunction ℂ) (m : ℕ)
    (qq : Fin (m + 1) → Nat.Primes) (row col : Unit × Fin (m + 1)) :
    primeProfileJetPacketMatrix (fun _ : Unit => g) m (fun y => qq y.2) (fun _ => 0) row col
      = g (qq row.2 : ℕ) * (Complex.I * (Real.log (qq row.2 : ℕ) : ℂ)) ^ (col.2 : ℕ) := by
  have hprime : ((qq row.2 : ℕ)).Prime := (qq row.2).2
  simp only [primeProfileJetPacketMatrix, primeProfileJetSource, primeDeriv_apply,
    primeProfileRotatedLogJet_apply, pow_zero, one_mul]
  rw [Nat.Prime.factorization_self hprime]
  push_cast
  ring

/-- **The criterion.**  A profile nonzero at infinitely many primes has a cofinite jet packet over a
one-element index. -/
theorem cofinitePrimeProfileJetPacket_of_infinite_prime_support {g : ArithmeticFunction ℂ}
    (hg : {p : Nat.Primes | g (p : ℕ) ≠ 0}.Infinite) :
    CofinitePrimeProfileJetPacket (fun _ : Unit => g) := by
  classical
  intro m forbidden hfin
  obtain ⟨qq, hqinj, hqmem⟩ := exists_injective_primes_mem m (hg.diff hfin)
  refine ⟨fun x => qq x.2, fun _ => 0, ?_, ?_, ?_⟩
  · rintro ⟨u, i⟩ ⟨v, j⟩ h
    exact Prod.ext (Subsingleton.elim u v) (hqinj h)
  · intro row
    exact (hqmem row.2).2
  · set c : Fin (m + 1) → ℂ := fun i => g (qq i : ℕ) with hc
    set x : Fin (m + 1) → ℂ := fun i => Complex.I * (Real.log (qq i : ℕ) : ℂ) with hx
    have hre : Matrix.reindex (Equiv.punitProd (Fin (m + 1))) (Equiv.punitProd (Fin (m + 1)))
        (primeProfileJetPacketMatrix (fun _ : Unit => g) m (fun y => qq y.2) (fun _ => 0))
        = Matrix.diagonal c * Matrix.vandermonde x := by
      ext i j
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_mul,
        Matrix.vandermonde_apply, primeProfileJetPacketMatrix_unit_apply]
      rfl
    have hdet := Matrix.det_reindex_self (Equiv.punitProd (Fin (m + 1)))
      (primeProfileJetPacketMatrix (fun _ : Unit => g) m (fun y => qq y.2) (fun _ => 0))
    rw [← hdet, hre, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (hqmem i).1)
      (Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_)
    rw [Finset.mem_Ioi] at hj
    refine sub_ne_zero.mpr fun hxx => ?_
    have hlog : Real.log (qq j : ℕ) = Real.log (qq i : ℕ) := by
      have him := congrArg Complex.im hxx
      simp only [hx, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, one_mul, zero_add] at him
      exact him
    exact absurd (hqinj (log_prime_injective hlog)) (ne_of_gt hj)

/-- The prime indicator is the case where the support is every prime. -/
theorem cofinitePrimeProfileJetPacket_primeIndicator' :
    CofinitePrimeProfileJetPacket (fun _ : Unit => primeIndicatorProfile) := by
  refine cofinitePrimeProfileJetPacket_of_infinite_prime_support ?_
  have huniv : {p : Nat.Primes | primeIndicatorProfile (p : ℕ) ≠ 0} = Set.univ := by
    ext p
    simp [primeIndicatorProfile_apply, p.2]
  rw [huniv]
  exact Set.infinite_univ

end GaloisForLFunctions.HTGeometry
