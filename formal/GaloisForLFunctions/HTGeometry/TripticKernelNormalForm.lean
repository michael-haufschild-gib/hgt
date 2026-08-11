import GaloisForLFunctions.HTGeometry.TripticTotalAtomSum
import GaloisForLFunctions.HTGeometry.TripticOrderBound
import GaloisForLFunctions.HTGeometry.TripticRemainderRigidity

/-!
# The normal form of a source with vanishing orbital divisor

Assembling everything: for a `1`-periodic meromorphic function with constant mixed difference whose
orbital divisor vanishes, there is an explicit finite combination of theta-source jets with the same
principal part at every point of the plane.

The two transverse fields split the principal part; only finitely many orders and, at each order,
only finitely many lines carry them; the weighted atom sum reproduces both fields exactly; and the
jets are pure, so no order interferes with another.

* `exists_totalAtomSum_no_principal_part`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

variable {F : ℂ → ℂ} {τ σ : ℂ}

set_option maxHeartbeats 1000000 in
/-- **The principal-part normal form.**  A source of vanishing orbital divisor has the same Laurent
coefficients of negative index, at every point, as an explicit finite atom sum. -/
theorem exists_totalAtomSum_no_principal_part
    (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F)
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hvanish : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      ∑ᶠ m : ℤ, laurentCoeff (fun z => F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ = 0) :
    ∃ (n : ℕ) (Rτ Rσ : ℕ → Finset ℂ), ∀ (w : ℂ) (ℓ : ℤ), ℓ < 0 →
      laurentCoeff F w ℓ = laurentCoeff (totalAtomSum F τ σ n Rτ Rσ) w ℓ := by
  classical
  have hUtaumero : MeromorphicOn (fun z => F (z + σ) - F z) Set.univ := fun z _ =>
    (meromorphicAt_comp_add.mpr (hF (z + σ) (Set.mem_univ _))).sub (hF z (Set.mem_univ z))
  have hUsigmero : MeromorphicOn (fun z => F (z + τ) - F z) Set.univ := fun z _ =>
    (meromorphicAt_comp_add.mpr (hF (z + τ) (Set.mem_univ _))).sub (hF z (Set.mem_univ z))
  -- the four periodicity facts of the boundary coefficients
  have hUper1 : ∀ (h : ℂ) (ℓ : ℤ) (a : ℂ),
      laurentCoeff (fun z => F (z + h) - F z) (a + 1) ℓ
        = laurentCoeff (fun z => F (z + h) - F z) a ℓ := by
    intro h ℓ a
    have hmero : MeromorphicAt (fun z => F (z + 1 + h) - F (z + 1)) a :=
      meromorphicAt_comp_add.mpr
        ((meromorphicAt_comp_add.mpr (hF (a + 1 + h) (Set.mem_univ _))).sub
          (hF (a + 1) (Set.mem_univ _)))
    calc laurentCoeff (fun z => F (z + h) - F z) (a + 1) ℓ
        = laurentCoeff (fun z => F (z + 1 + h) - F (z + 1)) a ℓ :=
          (laurentCoeff_comp_add (fun z => F (z + h) - F z) a 1 ℓ).symm
      _ = laurentCoeff (fun z => F (z + h) - F z) a ℓ :=
          laurentCoeff_congr hmero (eventuallyEq_boundary_shift_one hper h a) ℓ
  have hUtauperτ : ∀ (ℓ : ℤ), ℓ < 0 → ∀ a : ℂ,
      laurentCoeff (fun z => F (z + σ) - F z) (a + τ) ℓ = laurentCoeff (fun z => F (z + σ) - F z) a ℓ := by
    intro ℓ hℓ a
    have hmero : MeromorphicAt (fun z => F (z + τ + σ) - F (z + τ)) a :=
      meromorphicAt_comp_add.mpr (hUtaumero (a + τ) (Set.mem_univ _))
    calc laurentCoeff (fun z => F (z + σ) - F z) (a + τ) ℓ
        = laurentCoeff (fun z => F (z + τ + σ) - F (z + τ)) a ℓ :=
          (laurentCoeff_comp_add (fun z => F (z + σ) - F z) a τ ℓ).symm
      _ = laurentCoeff (fun z => (F (z + σ) - F z) + Cst) a ℓ :=
          laurentCoeff_congr hmero (eventuallyEq_boundary_shift_tau hmixed a) ℓ
      _ = laurentCoeff (fun z => F (z + σ) - F z) a ℓ := laurentCoeff_add_const (hUtaumero a (Set.mem_univ a)) Cst hℓ
  have hUsigperσ : ∀ (ℓ : ℤ), ℓ < 0 → ∀ a : ℂ,
      laurentCoeff (fun z => F (z + τ) - F z) (a + σ) ℓ = laurentCoeff (fun z => F (z + τ) - F z) a ℓ := by
    intro ℓ hℓ a
    have hmero : MeromorphicAt (fun z => F (z + σ + τ) - F (z + σ)) a :=
      meromorphicAt_comp_add.mpr (hUsigmero (a + σ) (Set.mem_univ _))
    calc laurentCoeff (fun z => F (z + τ) - F z) (a + σ) ℓ
        = laurentCoeff (fun z => F (z + σ + τ) - F (z + σ)) a ℓ :=
          (laurentCoeff_comp_add (fun z => F (z + τ) - F z) a σ ℓ).symm
      _ = laurentCoeff (fun z => (F (z + τ) - F z) + Cst) a ℓ :=
          laurentCoeff_congr hmero (eventuallyEq_boundary_shift_sigma hmixed a) ℓ
      _ = laurentCoeff (fun z => F (z + τ) - F z) a ℓ := laurentCoeff_add_const (hUsigmero a (Set.mem_univ a)) Cst hℓ
  have hindepBA : ∀ m n j : ℤ, (m : ℂ) * σ + (n : ℂ) * τ + (j : ℂ) = 0 →
      m = 0 ∧ n = 0 ∧ j = 0 := by
    intro m n j h
    obtain ⟨h1, h2, h3⟩ := hindep n m j (by linear_combination h)
    exact ⟨h2, h1, h3⟩
  have hUtaufin : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      {m : ℤ | laurentCoeff (fun z => F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite := fun p ℓ hℓ =>
    finite_setOf_laurentCoeff_ne_zero_orbit hUtaumero hℓ hτ (hUper1 σ ℓ) (hUtauperτ ℓ hℓ) hindepBA p
  have hUsigfin : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      {n : ℤ | laurentCoeff (fun z => F (z + τ) - F z) (p + (n : ℂ) * τ) ℓ ≠ 0}.Finite := fun p ℓ hℓ =>
    finite_setOf_laurentCoeff_ne_zero_orbit hUsigmero hℓ hσ (hUper1 τ ℓ) (hUsigperσ ℓ hℓ) hindep p
  -- the reciprocal vanishing in the other direction
  have hvanishσ : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      ∑ᶠ n : ℤ, laurentCoeff (fun z => F (z + τ) - F z) (p + (n : ℂ) * τ) ℓ = 0 := by
    intro p ℓ hℓ
    rw [← triptic_orbit_residue_reciprocity hF hper hmixed hτ hσ hindep p hℓ]
    exact hvanish p ℓ hℓ
  -- invariance of the two row fields along their lines
  have hrowinvτ : ∀ (ℓ : ℤ), ℓ < 0 → ∀ (q : ℂ) (a b : ℤ),
      rowCoeff F τ ℓ (q + (a : ℂ) + (b : ℂ) * σ) = rowCoeff F τ ℓ q := by
    intro ℓ hℓ q a b
    have h1 : ∀ x : ℂ, laurentCoeff (fun z => F (z + τ) - F z) (x + (a : ℂ)) ℓ = laurentCoeff (fun z => F (z + τ) - F z) x ℓ := by
      intro x
      have := laurentCoeff_add_zsmul_of_period (hUper1 τ ℓ) x a
      rwa [mul_one] at this
    have h2 : ∀ x : ℂ, laurentCoeff (fun z => F (z + τ) - F z) (x + (b : ℂ) * σ) ℓ = laurentCoeff (fun z => F (z + τ) - F z) x ℓ := fun x =>
      laurentCoeff_add_zsmul_of_period (hUsigperσ ℓ hℓ) x b
    rw [rowCoeff_invariant (F := F) (τ := τ) (h := (b : ℂ) * σ) h2 (q + (a : ℂ)),
      rowCoeff_invariant (F := F) (τ := τ) (h := (a : ℂ)) h1 q]
  have hrowinvσ : ∀ (ℓ : ℤ), ℓ < 0 → ∀ (q : ℂ) (a b : ℤ),
      rowCoeff F σ ℓ (q + (a : ℂ) + (b : ℂ) * τ) = rowCoeff F σ ℓ q := by
    intro ℓ hℓ q a b
    have h1 : ∀ x : ℂ, laurentCoeff (fun z => F (z + σ) - F z) (x + (a : ℂ)) ℓ = laurentCoeff (fun z => F (z + σ) - F z) x ℓ := by
      intro x
      have := laurentCoeff_add_zsmul_of_period (hUper1 σ ℓ) x a
      rwa [mul_one] at this
    have h2 : ∀ x : ℂ, laurentCoeff (fun z => F (z + σ) - F z) (x + (b : ℂ) * τ) ℓ = laurentCoeff (fun z => F (z + σ) - F z) x ℓ := fun x =>
      laurentCoeff_add_zsmul_of_period (hUtauperτ ℓ hℓ) x b
    rw [rowCoeff_invariant (F := F) (τ := σ) (h := (b : ℂ) * τ) h2 (q + (a : ℂ)),
      rowCoeff_invariant (F := F) (τ := σ) (h := (a : ℂ)) h1 q]
  -- the two order bounds
  obtain ⟨Jτ, hJτ⟩ := exists_order_bound_rowCoeff (F := F) (τ := τ) (σ := σ) hUsigmero hindepσ
    (fun ℓ' hℓ' => hUper1 τ ℓ') (fun ℓ' hℓ' => hUsigperσ ℓ' hℓ')
  obtain ⟨Jσ, hJσ⟩ := exists_order_bound_rowCoeff (F := F) (τ := σ) (σ := τ) hUtaumero hindepτ
    (fun ℓ' hℓ' => hUper1 σ ℓ') (fun ℓ' hℓ' => hUtauperτ ℓ' hℓ')
  set n : ℕ := max (max (-Jτ).toNat (-Jσ).toNat) 1 with hn
  have hnJτ : -(n : ℤ) ≤ Jτ := by
    have : ((-Jτ).toNat : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast (le_max_left (-Jτ).toNat (-Jσ).toNat).trans (le_max_left _ 1)
    omega
  have hnJσ : -(n : ℤ) ≤ Jσ := by
    have : ((-Jσ).toNat : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast (le_max_right (-Jτ).toNat (-Jσ).toNat).trans (le_max_left _ 1)
    omega
  clear_value n
  clear hn
  -- the finite class lists at each order
  have hclassτ : ∀ j : ℕ, ∃ R : Finset ℂ, ∀ w : ℂ,
      rowCoeff F τ (-((j : ℤ) + 1)) w ≠ 0 → ∃ q ∈ R, sameLine σ q w := by
    intro j
    obtain ⟨R, hR⟩ := exists_finset_rowCoeff_classes (F := F) (τ := τ) (σ := σ)
      (ℓ := -((j : ℤ) + 1)) (by omega) hUsigmero hindepσ hindep
      (fun ℓ' hℓ' => hUper1 τ ℓ') (fun ℓ' hℓ' => hUsigperσ ℓ' hℓ')
      (fun w => hUsigfin w (-((j : ℤ) + 1)) (by omega))
      (fun w => hvanishσ w (-((j : ℤ) + 1)) (by omega))
    refine ⟨R, fun w hw => ?_⟩
    obtain ⟨a, b, hab⟩ := hR w hw
    exact ⟨w - ((a : ℂ) + (b : ℂ) * σ), hab, a, b, by ring⟩
  have hclassσ : ∀ j : ℕ, ∃ R : Finset ℂ, ∀ w : ℂ,
      rowCoeff F σ (-((j : ℤ) + 1)) w ≠ 0 → ∃ q ∈ R, sameLine τ q w := by
    intro j
    obtain ⟨R, hR⟩ := exists_finset_rowCoeff_classes (F := F) (τ := σ) (σ := τ)
      (ℓ := -((j : ℤ) + 1)) (by omega) hUtaumero hindepτ hindepBA
      (fun ℓ' hℓ' => hUper1 σ ℓ') (fun ℓ' hℓ' => hUtauperτ ℓ' hℓ')
      (fun w => hUtaufin w (-((j : ℤ) + 1)) (by omega))
      (fun w => hvanish w (-((j : ℤ) + 1)) (by omega))
    refine ⟨R, fun w hw => ?_⟩
    obtain ⟨a, b, hab⟩ := hR w hw
    exact ⟨w - ((a : ℂ) + (b : ℂ) * τ), hab, a, b, by ring⟩
  choose Rτ hRτ using hclassτ
  choose Rσ hRσ using hclassσ
  refine ⟨n, Rτ, Rσ, fun w ℓ hℓ => ?_⟩
  -- the principal part of `F` splits into the two row fields
  have hsplit : laurentCoeff F w ℓ = rowCoeff F τ ℓ w + rowCoeff F σ ℓ w := by
    rw [laurentCoeff_eq_rowCoeff_add_colCoeff hF hper hmixed hτ hσ hindep hℓ w
      (hvanish w ℓ hℓ), colCoeff_eq_rowCoeff (hUtaufin w ℓ hℓ) (hvanish w ℓ hℓ)]
  rw [hsplit]
  by_cases hrange : -(n : ℤ) ≤ ℓ
  · obtain ⟨j₀, hj₀n, hj₀ℓ⟩ : ∃ j₀ : ℕ, j₀ < n ∧ ℓ = -((j₀ : ℤ) + 1) :=
      ⟨(-ℓ - 1).toNat, by omega, by omega⟩
    subst hj₀ℓ
    have hinvτ : ∀ q : ℂ, sameLine σ q w →
        rowCoeff F τ (-((j₀ : ℤ) + 1)) q = rowCoeff F τ (-((j₀ : ℤ) + 1)) w := by
      intro q hq
      obtain ⟨a, b, hab⟩ := hq
      rw [show w = q + (a : ℂ) + (b : ℂ) * σ from by linear_combination hab]
      exact (hrowinvτ (-((j₀ : ℤ) + 1)) (by omega) q a b).symm
    have hinvσ : ∀ q : ℂ, sameLine τ q w →
        rowCoeff F σ (-((j₀ : ℤ) + 1)) q = rowCoeff F σ (-((j₀ : ℤ) + 1)) w := by
      intro q hq
      obtain ⟨a, b, hab⟩ := hq
      rw [show w = q + (a : ℂ) + (b : ℂ) * τ from by linear_combination hab]
      exact (hrowinvσ (-((j₀ : ℤ) + 1)) (by omega) q a b).symm
    exact (laurentCoeff_totalAtomSum hτ hσ F n Rτ Rσ w j₀ hj₀n hinvτ (hRτ j₀ w) hinvσ
      (hRσ j₀ w)).symm
  · rw [not_le] at hrange
    rw [laurentCoeff_totalAtomSum_of_lt hτ hσ F n Rτ Rσ w hℓ hrange,
      hJτ ℓ (by omega) w, hJσ ℓ (by omega) w, add_zero]

end

end GaloisForLFunctions.HTGeometry
