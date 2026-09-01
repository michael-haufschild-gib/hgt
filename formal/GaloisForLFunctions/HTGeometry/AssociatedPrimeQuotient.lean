import GaloisForLFunctions.HTGeometry.AssociatedPrimeRegular
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# Associated primes grow when a regular element is divided out

```text
exists_mem_notMem_smul_of_isAssociatedPrime
    ** an associated prime is the annihilator of an element outside `xM` **
exists_associatedPrime_sup_span_le
    ** so `p + (x)` is contained in an associated prime of `M ⧸ xM` **
```

If every element with annihilator `p` were divisible by `x`, then dividing repeatedly — legitimate
because `x` is `M`-regular, so the quotient again has annihilator `p` — would place a nonzero
element in `⋂ xⁿM`, which is zero by Krull's intersection theorem.

This is the step that makes depth drop the dimension of the associated primes, and hence the reason a
system of parameters of a Cohen–Macaulay module is a regular sequence.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open IsLocalRing

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **An associated prime is the annihilator of an element outside `xM`.** -/
theorem exists_mem_notMem_smul_of_isAssociatedPrime {x : A} (hx : x ∈ maximalIdeal A)
    (hxreg : IsSMulRegular M x) {p : Ideal A} (hp : IsAssociatedPrime p M) :
    ∃ v : M, Submodule.colon ⊥ ({v} : Set M) = p ∧ v ∉ x • (⊤ : Submodule A M) := by
  classical
  obtain ⟨hprime, u₀, hu₀⟩ := (isAssociatedPrime_iff (I := p) (M := M)).mp hp
  by_contra hcon
  push Not at hcon
  have hstep : ∀ v : M, Submodule.colon ⊥ ({v} : Set M) = p →
      ∃ w : M, v = x • w ∧ Submodule.colon ⊥ ({w} : Set M) = p := by
    intro v hv
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists v x (⊤ : Submodule A M)).mp
      (hcon v hv)
    refine ⟨w, hw.symm, ?_⟩
    refine le_antisymm ?_ ?_
    · intro a ha
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at ha
      rw [← hv, Submodule.mem_colon_singleton, Submodule.mem_bot, ← hw, smul_comm, ha, smul_zero]
    · intro a ha
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      refine hxreg ?_
      show x • (a • w) = x • (0 : M)
      rw [smul_zero, smul_comm, hw]
      rw [← hv, Submodule.mem_colon_singleton, Submodule.mem_bot] at ha
      exact ha
  choose g hg1 hg2 using hstep
  let seq : ℕ → { v : M // Submodule.colon ⊥ ({v} : Set M) = p } := fun n =>
    Nat.rec (motive := fun _ => { v : M // Submodule.colon ⊥ ({v} : Set M) = p })
      ⟨u₀, hu₀.symm⟩ (fun _ v => ⟨g v.1 v.2, hg2 v.1 v.2⟩) n
  have hseq : ∀ n : ℕ, u₀ = x ^ n • (seq n).1 := by
    intro n
    induction n with
    | zero => simp [seq]
    | succ n ih =>
      have hstep' : (seq n).1 = x • (seq (n + 1)).1 := hg1 (seq n).1 (seq n).2
      rw [ih, hstep', smul_smul, ← pow_succ]
  have hmem : u₀ ∈ ⨅ n : ℕ, (Ideal.span {x}) ^ n • (⊤ : Submodule A M) := by
    refine Submodule.mem_iInf _ |>.mpr fun n => ?_
    rw [hseq n, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hbot : (⨅ n : ℕ, (Ideal.span {x}) ^ n • (⊤ : Submodule A M)) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (by
      intro htop
      exact (maximalIdeal.isMaximal A).ne_top
        (top_le_iff.mp (htop ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))))
  rw [hbot] at hmem
  have hu0 : u₀ = 0 := hmem
  apply hprime.ne_top
  rw [hu₀, hu0]
  refine le_antisymm le_top fun a _ => ?_
  rw [Submodule.mem_colon_singleton, smul_zero]
  exact Submodule.zero_mem _

/-- **`p + (x)` is contained in an associated prime of `M ⧸ xM`.** -/
theorem exists_associatedPrime_sup_span_le {x : A} (hx : x ∈ maximalIdeal A)
    (hxreg : IsSMulRegular M x) {p : Ideal A} (hp : p ∈ associatedPrimes A M) :
    ∃ q ∈ associatedPrimes A (M ⧸ (x • (⊤ : Submodule A M))), p ⊔ Ideal.span {x} ≤ q := by
  obtain ⟨v, hv, hvnot⟩ := exists_mem_notMem_smul_of_isAssociatedPrime hx hxreg hp
  have hvne : (Submodule.Quotient.mk v : M ⧸ (x • (⊤ : Submodule A M))) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hvnot
  obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hvne
  refine ⟨q, hq, le_trans ?_ hle⟩
  rw [sup_le_iff]
  refine ⟨fun a ha => ?_, ?_⟩
  · rw [Submodule.mem_colon_singleton]
    have : a • v = 0 := by
      rw [← hv, Submodule.mem_colon_singleton] at ha
      exact ha
    show a • Submodule.Quotient.mk v = (0 : M ⧸ (x • (⊤ : Submodule A M)))
    rw [← Submodule.Quotient.mk_smul, this, Submodule.Quotient.mk_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Submodule.mem_colon_singleton]
    show x • Submodule.Quotient.mk v = (0 : M ⧸ (x • (⊤ : Submodule A M)))
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ _ _ trivial

end GaloisForLFunctions.HTGeometry
