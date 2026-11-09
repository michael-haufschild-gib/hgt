import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.UnitaryPrimeChainGauge

/-!
# Tail coordinates of prime exterior chains

Appending a prime above a fixed increasing face gives another canonical
exterior basis vector. Distinct appended primes give distinct faces, so every
Hilbert vector has square-summable coefficients on this arithmetic tail.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open RHTower EffectiveScalingGeometry

attribute [local instance] primeLabelLinearOrder

/-- Prime labels beyond a fixed numerical cutoff. -/
abbrev PrimeTail (B : ℕ) := {p : Nat.Primes // B < (p : ℕ)}

private theorem strictMono_snoc_prime {k : ℕ} (v : Fin k ↪o Nat.Primes)
    (p : Nat.Primes) (hp : ∀ i, v i < p) : StrictMono (Fin.snoc v p) := by
  intro i j hij
  by_cases hj : j = Fin.last k
  · subst j
    have hi : i ≠ Fin.last k := ne_of_lt hij
    rw [Fin.snoc_last, ← Fin.castSucc_castPred i hi, Fin.snoc_castSucc]
    exact hp _
  · have hi : i ≠ Fin.last k := Fin.ne_last_of_lt hij
    rw [← Fin.castSucc_castPred i hi, ← Fin.castSucc_castPred j hj,
      Fin.snoc_castSucc, Fin.snoc_castSucc]
    apply v.strictMono
    exact Fin.castPred_lt_castPred hij hj

/-- Append a tail prime to the increasing enumeration of a bounded face. -/
def primeTailEnumeration {k : ℕ} (v : Fin k ↪o Nat.Primes) (B : ℕ)
    (hv : ∀ i, (v i : ℕ) ≤ B) (p : PrimeTail B) : Fin (k+1) ↪o Nat.Primes :=
  OrderEmbedding.ofStrictMono (Fin.snoc v p.val)
    (strictMono_snoc_prime v p.val (fun i => show (v i : ℕ) < (p.val : ℕ) from
      lt_of_le_of_lt (hv i) p.property))

/-- The actual exterior face obtained by adjoining the tail prime. -/
def primeTailFace {k : ℕ} (v : Fin k ↪o Nat.Primes) (B : ℕ)
    (hv : ∀ i, (v i : ℕ) ≤ B) (p : PrimeTail B) : PrimeFaceIndex (k+1) :=
  Set.powersetCard.ofFinEmbEquiv (primeTailEnumeration v B hv p)

theorem primeTailFace_injective {k : ℕ} (v : Fin k ↪o Nat.Primes) (B : ℕ)
    (hv : ∀ i, (v i : ℕ) ≤ B) : Function.Injective (primeTailFace v B hv) := by
  intro p q hpq
  have he := Set.powersetCard.ofFinEmbEquiv.injective hpq
  have hl := congrArg (fun e : Fin (k+1) ↪o Nat.Primes => e (Fin.last k)) he
  apply Subtype.ext
  simpa only [primeTailEnumeration, OrderEmbedding.coe_ofStrictMono, Fin.snoc_last] using hl

/-- An increasing tuple is its canonical arithmetic basis face. -/
theorem primeExteriorEmbedding0_orderedAtom {k : ℕ} (v : Fin k ↪o Nat.Primes) :
    primeExteriorEmbedding0 k (primeChainAtom ℂ v) =
      HilbertSchmidt.lpBasis (PrimeFaceIndex k) (Set.powersetCard.ofFinEmbEquiv v) := by
  have hb := primeChainBasis_eq_atom ℂ (Set.powersetCard.ofFinEmbEquiv v)
  rw [Equiv.symm_apply_apply] at hb
  rw [← hb, primeExteriorEmbedding0_basis]

/-- Tail insertion retains the original exterior atom, including its orientation. -/
theorem primeExteriorEmbedding0_tailAtom {k : ℕ} (v : Fin k ↪o Nat.Primes) (B : ℕ)
    (hv : ∀ i, (v i : ℕ) ≤ B) (p : PrimeTail B) :
    primeExteriorEmbedding0 (k+1) (primeChainAtom ℂ (Fin.snoc v p.val)) =
      HilbertSchmidt.lpBasis (PrimeFaceIndex (k+1)) (primeTailFace v B hv p) := by
  simpa only [primeTailEnumeration, OrderEmbedding.coe_ofStrictMono, primeTailFace] using
    primeExteriorEmbedding0_orderedAtom (primeTailEnumeration v B hv p)

/-- Hilbert coefficients remain square summable on each injectively labelled arithmetic tail. -/
theorem primeExterior_tail_summable {k : ℕ} (v : Fin k ↪o Nat.Primes) (B : ℕ)
    (hv : ∀ i, (v i : ℕ) ≤ B) (u : PrimeExteriorHilbert (k+1)) :
    Summable (fun p : PrimeTail B => ‖u (primeTailFace v B hv p)‖^2) :=
  (HilbertSchmidt.summable_coe_sq u).comp_injective (primeTailFace_injective v B hv)

/-- A continuous observation has square-summable values on the same tail basis. -/
theorem primeExterior_tail_functional_summable {k : ℕ} (v : Fin k ↪o Nat.Primes) (B : ℕ)
    (hv : ∀ i, (v i : ℕ) ≤ B) (φ : PrimeExteriorHilbert (k+1) →L[ℂ] ℂ) :
    Summable (fun p : PrimeTail B =>
      ‖φ (primeExteriorEmbedding0 (k+1) (primeChainAtom ℂ (Fin.snoc v p.val)))‖^2) := by
  simp only [primeExteriorEmbedding0_tailAtom v B hv]
  exact (HTGeometry.summable_norm_apply_sq (HilbertSchmidt.lpBasis (PrimeFaceIndex (k+1))) φ).comp_injective
    (primeTailFace_injective v B hv)

/-- Removing a vertex retains the increasing order of the remaining face. -/
def primeFaceDeletion {k : ℕ} (v : Fin (k+1) ↪o Nat.Primes) (i : Fin (k+1)) :
    Fin k ↪o Nat.Primes :=
  OrderEmbedding.ofStrictMono (fun j => v (i.succAbove j))
    (fun _ _ h => v.strictMono (Fin.succAbove_lt_succAbove_iff.mpr h))

private theorem removeNth_snoc_prime {k : ℕ} (v : Fin (k+1) → Nat.Primes)
    (p : Nat.Primes) (i : Fin (k+1)) :
    (fun j : Fin (k+1) => (Fin.snoc v p : Fin (k+2) → Nat.Primes) (i.castSucc.succAbove j)) =
      (Fin.snoc (fun j : Fin k => v (i.succAbove j)) p : Fin (k+1) → Nat.Primes) := by
  funext j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))]
    simp only [Fin.succ_last, Fin.snoc_last]
  · rw [Fin.castSucc_succAbove_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- The boundary of an appended face separates its last prime from its old vertices. -/
theorem dirichletPrimeChainBoundary_tailAtom {k : ℕ} (s : ℂ)
    (v : Fin (k+1) ↪o Nat.Primes) (p : Nat.Primes) :
    dirichletPrimeChainBoundary (k+1) s (primeChainAtom ℂ (Fin.snoc v p)) =
      (∑ i : Fin (k+1), ((-1 : ℤ)^(i : ℕ)) •
        ((v i : ℂ)^(-s) • primeChainAtom ℂ (Fin.snoc (primeFaceDeletion v i) p))) +
      ((-1 : ℤ)^(k+1)) • ((p : ℂ)^(-s) • primeChainAtom ℂ v) := by
  rw [primeChainAtom, HTGeometry.physicalKoszulDifferential_ιMulti, Fin.sum_univ_castSucc]
  have hlast : (fun j : Fin (k+1) => Finsupp.single
      ((Fin.snoc v p : Fin (k+2) → Nat.Primes) ((Fin.last (k+1)).succAbove j)) (1 : ℂ)) =
      fun j : Fin (k+1) => Finsupp.single (v j) (1 : ℂ) := by
    simp only [Fin.succAbove_last, Fin.snoc_castSucc]
  simp only [dirichletPrimeChainFunctional, Finsupp.linearCombination_single,
    one_smul, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  congr 1
  · apply sum_congr rfl
    intro i _
    congr 3
    change (fun j : Fin (k+1) => Finsupp.single
      ((Fin.snoc v p : Fin (k+2) → Nat.Primes) (i.castSucc.succAbove j)) (1 : ℂ)) = _
    have hr := removeNth_snoc_prime (v : Fin (k+1) → Nat.Primes) p i
    exact congrArg (fun w : Fin (k+1) → Nat.Primes => fun j => Finsupp.single (w j) (1 : ℂ)) hr
  · change ((-1 : ℤ)^(k+1)) • ((p : ℂ)^(-s) • exteriorPower.ιMulti ℂ (k+1) _) = _
    exact congrArg (fun w : Fin (k+1) → (Nat.Primes →₀ ℂ) =>
      ((-1 : ℤ)^(k+1)) • ((p : ℂ)^(-s) • exteriorPower.ιMulti ℂ (k+1) w)) hlast

/-- The augmented boundary has the same last-vertex formula in degree zero. -/
theorem dirichletPrimeChainBoundary_zero_tailAtom (s : ℂ)
    (v : Fin 0 ↪o Nat.Primes) (p : Nat.Primes) :
    dirichletPrimeChainBoundary 0 s (primeChainAtom ℂ (Fin.snoc v p)) =
      (p : ℂ)^(-s) • primeChainAtom ℂ v := by
  rw [primeChainAtom, HTGeometry.physicalKoszulDifferential_ιMulti, Fin.sum_univ_one]
  have hp : (Fin.snoc v p : Fin 1 → Nat.Primes) (0 : Fin 1) = p := by
    exact @Fin.snoc_last 0 (fun _ : Fin 1 => Nat.Primes) p v
  simp only [Fin.val_zero, pow_zero, hp, dirichletPrimeChainFunctional,
    Finsupp.linearCombination_single, one_smul]
  exact congrArg (fun w : Fin 0 → (Nat.Primes →₀ ℂ) =>
    (p : ℂ)^(-s) • exteriorPower.ιMulti ℂ 0 w) (Subsingleton.elim _ _)

/-- Removing finitely many primes does not repair the critical square-summability failure. -/
theorem primeBoundary_tail_not_summable (s : ℂ) (hs : s.re ≤ 1/2) (B : ℕ) :
    ¬ Summable (fun p : PrimeTail B => ‖(p.val : ℂ)^(-s)‖^2) := by
  intro h
  letI : Finite ↥({p : Nat.Primes | B < (p : ℕ)}ᶜ) :=
    Finite.of_injective
      (fun p => (⟨p.val.val, by
        have hp : ¬ B < p.val.val := p.property
        omega⟩ : Fin (B+1)))
      (by
        intro p q hpq
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg Fin.val hpq)
  have hfull : Summable (fun p : Nat.Primes => ‖(p : ℂ)^(-s)‖^2) :=
    (summable_subtype_and_compl (s := {p : Nat.Primes | B < (p : ℕ)})).mp
      ⟨h, Summable.of_finite⟩
  exact (not_lt_of_ge hs) ((primeBoundary_square_summable_iff s).mp hfull)

/-- A square-summable multiple of the critical prime tail has zero scalar coefficient. -/
theorem primeBoundary_tail_scalar_eq_zero (s : ℂ) (hs : s.re ≤ 1/2) (B : ℕ) (c : ℂ)
    (h : Memℓp (fun p : PrimeTail B => (p.val : ℂ)^(-s)*c) 2) : c = 0 := by
  by_contra hc
  have hc' : ‖c‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
  let u : lp (fun _ : PrimeTail B => ℂ) 2 := ⟨_, h⟩
  have hm : Summable (fun p : PrimeTail B => ‖(p.val : ℂ)^(-s)‖^2 * ‖c‖^2) := by
    simpa only [u, norm_mul, mul_pow] using HilbertSchmidt.summable_coe_sq u
  have hb := hm.mul_right (‖c‖^2)⁻¹
  simp only [mul_assoc, mul_inv_cancel₀ hc', mul_one] at hb
  exact primeBoundary_tail_not_summable s hs B hb

#print axioms primeTailFace_injective
#print axioms primeExteriorEmbedding0_tailAtom
#print axioms primeExterior_tail_functional_summable
#print axioms dirichletPrimeChainBoundary_tailAtom
#print axioms dirichletPrimeChainBoundary_zero_tailAtom
#print axioms primeBoundary_tail_not_summable
#print axioms primeBoundary_tail_scalar_eq_zero

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
