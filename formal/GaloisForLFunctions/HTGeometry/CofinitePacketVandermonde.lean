import GaloisForLFunctions.HTGeometry.CofinitePacketConsistency

/-!
# A nondegenerate cofinite jet packet

The consistency witness for `CofinitePrimeProfileJetPacket` lives on the empty index, where the packet
matrix is empty.  The substantive question is whether a packet exists over a *nonempty* index, and it
does: the packet matrix of the prime indicator profile, read at exponent zero, is a Vandermonde
matrix.

Writing out the entry, `primeDeriv p (jetₖ f) (p⁰)` is `(0+1) · (i · log p)ᵏ · f p`, so for the
profile that is `1` at every prime the matrix is exactly `vandermonde (fun r => i · log qᵣ)`.  Its
determinant is the product of the node differences, nonzero because `log` separates distinct primes.
Choosing the nodes outside any prescribed finite set is possible because there are infinitely many
primes.

* `primeIndicatorProfile`, `primeIndicatorProfile_supported`;
* **`cofinitePrimeProfileJetPacket_primeIndicator`** — the packet over a one-element index.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- The profile that is `1` at every prime and `0` elsewhere. -/
noncomputable def primeIndicatorProfile : ArithmeticFunction ℂ where
  toFun n := if n.Prime then 1 else 0
  map_zero' := by simp [Nat.not_prime_zero]

@[simp] theorem primeIndicatorProfile_apply (n : ℕ) :
    primeIndicatorProfile n = if n.Prime then 1 else 0 := rfl

theorem primeIndicatorProfile_supported :
    PrimeProfileSupportedOnPositivePrimePowers primeIndicatorProfile := by
  intro n hn
  by_cases hp : n.Prime
  · exact ⟨⟨n, hp⟩, 0, by simp⟩
  · simp [hp] at hn

/-! ### Choosing separated primes outside a finite set -/

theorem exists_injective_primes_avoiding (m : ℕ) {forbidden : Set Nat.Primes}
    (hfin : forbidden.Finite) :
    ∃ q : Fin (m + 1) → Nat.Primes, Function.Injective q ∧ ∀ i, q i ∉ forbidden := by
  classical
  have hinf : (forbiddenᶜ : Set Nat.Primes).Infinite := Set.Finite.infinite_compl hfin
  obtain ⟨t, hts, htcard⟩ := hinf.exists_subset_card_eq (m + 1)
  refine ⟨fun i => ((Finset.equivFinOfCardEq htcard).symm i : Nat.Primes), ?_, ?_⟩
  · intro i j hij
    have : (Finset.equivFinOfCardEq htcard).symm i = (Finset.equivFinOfCardEq htcard).symm j :=
      Subtype.ext hij
    simpa using congrArg (Finset.equivFinOfCardEq htcard) this
  · intro i
    exact hts ((Finset.equivFinOfCardEq htcard).symm i).2

/-! ### The packet matrix is Vandermonde -/

theorem log_prime_injective : Function.Injective fun p : Nat.Primes => Real.log (p : ℕ) := by
  intro p r h
  have h' : Real.log ((p : ℕ) : ℝ) = Real.log ((r : ℕ) : ℝ) := h
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have hr : (0 : ℝ) < (r : ℕ) := by exact_mod_cast r.2.pos
  have : ((p : ℕ) : ℝ) = ((r : ℕ) : ℝ) := by
    rw [← Real.exp_log hp, ← Real.exp_log hr, h']
  exact Subtype.ext (by exact_mod_cast this)

/-- **A cofinite jet packet over a one-element index.**  The prime indicator profile has nonsingular
packet matrices at every order, with nodes avoiding any prescribed finite set of primes. -/
theorem cofinitePrimeProfileJetPacket_primeIndicator :
    CofinitePrimeProfileJetPacket (fun _ : Unit => primeIndicatorProfile) := by
  classical
  intro m forbidden hfin
  obtain ⟨qq, hqinj, hqavoid⟩ := exists_injective_primes_avoiding m hfin
  refine ⟨fun x => qq x.2, fun _ => 0, ?_, ?_, ?_⟩
  · rintro ⟨u, i⟩ ⟨v, j⟩ h
    exact Prod.ext (Subsingleton.elim u v) (hqinj h)
  · intro row
    exact hqavoid row.2
  · set x : Fin (m + 1) → ℂ := fun i => Complex.I * (Real.log (qq i : ℕ) : ℂ) with hx
    have hentry : ∀ row col : Unit × Fin (m + 1),
        primeProfileJetPacketMatrix (fun _ : Unit => primeIndicatorProfile) m
            (fun y => qq y.2) (fun _ => 0) row col = x row.2 ^ (col.2 : ℕ) := by
      intro row col
      have hprime : ((qq row.2 : ℕ)).Prime := (qq row.2).2
      simp only [primeProfileJetPacketMatrix, primeProfileJetSource, primeDeriv_apply,
        primeProfileRotatedLogJet_apply, pow_zero, one_mul, primeIndicatorProfile_apply,
        if_pos hprime, mul_one, hx]
      rw [Nat.Prime.factorization_self hprime]
      simp
    have hre : Matrix.reindex (Equiv.punitProd (Fin (m + 1))) (Equiv.punitProd (Fin (m + 1)))
        (primeProfileJetPacketMatrix (fun _ : Unit => primeIndicatorProfile) m
          (fun y => qq y.2) (fun _ => 0)) = Matrix.vandermonde x := by
      ext i j
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply]
      exact hentry _ _
    have hdet := Matrix.det_reindex_self (Equiv.punitProd (Fin (m + 1)))
      (primeProfileJetPacketMatrix (fun _ : Unit => primeIndicatorProfile) m
        (fun y => qq y.2) (fun _ => 0))
    rw [← hdet, hre, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    rw [Finset.mem_Ioi] at hj
    refine sub_ne_zero.mpr fun hxx => ?_
    have hlog : Real.log (qq j : ℕ) = Real.log (qq i : ℕ) := by
      have him := congrArg Complex.im hxx
      simp only [hx, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, one_mul, zero_add] at him
      exact him
    exact absurd (hqinj (log_prime_injective hlog)) (ne_of_gt hj)

/-- The two premises of the packet layer hold together on a nonempty index. -/
theorem cofinitePacket_and_support_primeIndicator :
    CofinitePrimeProfileJetPacket (fun _ : Unit => primeIndicatorProfile) ∧
      ∀ _ : Unit, PrimeProfileSupportedOnPositivePrimePowers primeIndicatorProfile :=
  ⟨cofinitePrimeProfileJetPacket_primeIndicator, fun _ => primeIndicatorProfile_supported⟩

end GaloisForLFunctions.HTGeometry
