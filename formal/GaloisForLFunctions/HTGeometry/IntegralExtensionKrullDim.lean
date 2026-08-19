import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The Krull dimension is an integral invariant

For an injective integral ring extension the Krull dimension is unchanged.  Incomparability makes
contraction of primes strictly monotone, so the dimension cannot grow; going up lifts a strictly
increasing chain of primes to one upstairs, so it cannot drop:

```text
ringKrullDim_le_of_isIntegral        incomparability
exists_primeChain_over               going up, for chains of arbitrary length
le_ringKrullDim_of_isIntegral
ringKrullDim_eq_of_isIntegral        ** dim R = dim S **
```

Mathlib has the two ingredients (`Ideal.IsIntegral.comap_lt_comap` and
`Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`) but not the chain version of going up nor
the dimension statement; its own source marks the chain version as a `TODO`.
-/

namespace GaloisForLFunctions.HTGeometry

open Order

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- **Incomparability.**  Over an integral extension the Krull dimension cannot grow. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  intro a b hab
  have h : a.asIdeal < b.asIdeal := hab
  exact Ideal.IsIntegral.comap_lt_comap (A := S) (R := R) h

/-- **Going up for chains.**  A strictly increasing chain of primes downstairs lifts to one
upstairs along an injective integral extension. -/
theorem exists_primeChain_over [Algebra.IsIntegral R S]
    (hker : RingHom.ker (algebraMap R S) = ⊥) :
    ∀ (n : ℕ) (p : Fin (n + 1) → Ideal R), (∀ i, (p i).IsPrime) → StrictMono p →
      ∃ P : Fin (n + 1) → Ideal S, (∀ i, (P i).IsPrime) ∧ StrictMono P ∧
        ∀ i, (P i).comap (algebraMap R S) = p i := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    haveI := hp 0
    obtain ⟨Q, _, hQprime, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (p 0) (⊥ : Ideal S)
      (by rw [← RingHom.ker_eq_comap_bot, hker]; exact bot_le)
    refine ⟨fun _ => Q, fun _ => hQprime, ?_, fun i => ?_⟩
    · exact Fin.strictMono_iff_lt_succ.mpr (fun i => absurd i.isLt (by omega))
    · have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      rw [hi]
      exact hQ
  | succ n ih =>
    intro p hp hmono
    obtain ⟨P', hP'prime, hP'mono, hP'comap⟩ :=
      ih (p ∘ Fin.castSucc) (fun i => hp _) (hmono.comp Fin.strictMono_castSucc)
    haveI := hp (Fin.last (n + 1))
    haveI := hP'prime (Fin.last n)
    have hle : (P' (Fin.last n)).comap (algebraMap R S) ≤ p (Fin.last (n + 1)) := by
      rw [hP'comap]
      exact le_of_lt (hmono (Fin.castSucc_lt_last _))
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
        (p (Fin.last (n + 1))) (P' (Fin.last n)) hle
    have hcomap : ∀ k : Fin (n + 2),
        ((Fin.snoc P' Q : Fin (n + 2) → Ideal S) k).comap (algebraMap R S) = p k := by
      intro k
      refine Fin.lastCases ?_ ?_ k
      · rw [Fin.snoc_last]; exact hQcomap
      · intro l; rw [Fin.snoc_castSucc]; exact hP'comap l
    refine ⟨Fin.snoc P' Q, ?_, ?_, hcomap⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]; exact hQprime
      · intro j; rw [Fin.snoc_castSucc]; exact hP'prime j
    · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [show (Fin.castSucc j).castSucc = (Fin.castSucc j.castSucc) from rfl,
          Fin.snoc_castSucc, show (Fin.castSucc j).succ = (Fin.castSucc j.succ) from rfl,
          Fin.snoc_castSucc]
        exact hP'mono Fin.castSucc_lt_succ
      · rw [show (Fin.last n).succ = Fin.last (n + 1) from rfl, Fin.snoc_last,
          Fin.snoc_castSucc]
        refine lt_of_le_of_ne hQge fun hcon => ?_
        have h1 : (P' (Fin.last n)).comap (algebraMap R S) = p (Fin.last (n + 1)) := by
          rw [hcon]; exact hQcomap
        rw [hP'comap] at h1
        exact absurd h1 (ne_of_lt (hmono (Fin.castSucc_lt_last _)))

/-- **Going up.**  Over an injective integral extension the Krull dimension cannot drop. -/
theorem le_ringKrullDim_of_isIntegral [Algebra.IsIntegral R S]
    (hker : RingHom.ker (algebraMap R S) = ⊥) :
    ringKrullDim R ≤ ringKrullDim S := by
  refine iSup_le fun l => ?_
  obtain ⟨P, hPprime, hPmono, _⟩ := exists_primeChain_over R S hker l.length
    (fun i => (l i).asIdeal) (fun i => (l i).isPrime) (fun i j hij => l.strictMono hij)
  exact LTSeries.length_le_krullDim
    ({ length := l.length
       toFun := fun i => ⟨P i, hPprime i⟩
       step := fun i => hPmono Fin.castSucc_lt_succ } : LTSeries (PrimeSpectrum S))

/-- **The Krull dimension is an integral invariant.** -/
theorem ringKrullDim_eq_of_isIntegral [Algebra.IsIntegral R S]
    (hker : RingHom.ker (algebraMap R S) = ⊥) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (le_ringKrullDim_of_isIntegral R S hker) (ringKrullDim_le_of_isIntegral R S)

end GaloisForLFunctions.HTGeometry