import GaloisForLFunctions.HTGeometry.AssociatedPrimeQuotient
import GaloisForLFunctions.HTGeometry.GradeQuotient
import GaloisForLFunctions.HTGeometry.KrullDimInfPrimes
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Grade is bounded by the dimension of every associated prime

```text
maximalIdeal_smul_top_lt_top     Nakayama: a nonzero finite module is not its own `𝔪`-multiple
exists_ltSeries_of_hasGradeGE    ** a regular sequence of length `n` produces a chain of primes of
                                    length `n` starting at any associated prime **
hasGradeGE_le_ringKrullDim_quotient
                                 ** hence `grade (𝔪, M) ≤ dim R ⧸ p` for every `p ∈ Ass M` **
```

The chain is built by the induction that drives all of depth theory: a regular element `x` misses
every associated prime, and `p + (x)` sits inside an associated prime `q` of `M ⧸ xM`
(`exists_associatedPrime_sup_span_le`), so `p < q`; the grade of the quotient has dropped by at most
one (`hasGradeGE_quotSMulTop`), so the induction supplies a chain of length `n` above `q`, and
prepending `p` gives one of length `n + 1`.

Producing the chain rather than comparing dimensions directly keeps the induction inside
`LTSeries`, where prepending is a constructor.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise
open IsLocalRing RingTheory.Sequence

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- Nakayama: a nonzero finite module is not its own `𝔪`-multiple. -/
theorem maximalIdeal_smul_top_lt_top (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M] :
    (maximalIdeal A) • (⊤ : Submodule A M) < ⊤ := by
  refine lt_of_le_of_ne le_top ?_
  intro hcon
  have hbot : (⊤ : Submodule A M) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal A) ⊤
      (Module.Finite.fg_top) (by rw [hcon]) ?_
    exact le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial M)
  exact hab (by
    have ha : a ∈ (⊥ : Submodule A M) := hbot ▸ (Submodule.mem_top : a ∈ ⊤)
    have hb : b ∈ (⊥ : Submodule A M) := hbot ▸ (Submodule.mem_top : b ∈ ⊤)
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb])

/-- **A regular sequence of length `n` produces a chain of primes of length `n` above any
associated prime.** -/
theorem exists_ltSeries_of_hasGradeGE :
    ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
      HasGradeGE (maximalIdeal A) (ModuleCat.of A M) n →
      ∀ p ∈ associatedPrimes A M, ∃ s : LTSeries (PrimeSpectrum A),
        s.length = n ∧ (s.head).asIdeal = p := by
  intro n
  induction n with
  | zero =>
    intro M _ _ _ _ p hp
    haveI : p.IsPrime := hp.1
    exact ⟨RelSeries.singleton _ ⟨p, hp.1⟩, rfl, rfl⟩
  | succ n ih =>
    intro M _ _ _ hgrade p hp
    haveI : p.IsPrime := hp.1
    obtain ⟨rs, hlen, hmem, hreg⟩ := hgrade
    obtain ⟨x, t, rfl⟩ : ∃ x t, rs = x :: t := by
      cases rs with
      | nil => simp at hlen
      | cons z t => exact ⟨z, t, rfl⟩
    have hxmem : x ∈ maximalIdeal A := hmem x (List.mem_cons_self ..)
    have hxreg : IsSMulRegular M x := ((isRegular_cons_iff _ x t).mp hreg).1
    have hxp : x ∉ p := (isSMulRegular_iff_forall_notMem_associatedPrimes A M).mp hxreg p hp
    obtain ⟨q, hq, hle⟩ := exists_associatedPrime_sup_span_le hxmem hxreg hp
    haveI : q.IsPrime := hq.1
    have hxq : x ∈ q := hle (Submodule.mem_sup_right (Ideal.mem_span_singleton_self x))
    have hpq : p < q := lt_of_le_of_ne (le_trans le_sup_left hle) (by
      intro hcon
      exact hxp (hcon ▸ hxq))
    -- the quotient is a nonzero finite module of grade at least `n`
    haveI hfinq : Module.Finite A (M ⧸ (x • (⊤ : Submodule A M))) :=
      Module.Finite.of_surjective (Submodule.mkQ (x • (⊤ : Submodule A M)))
        (Submodule.mkQ_surjective _)
    haveI hntq : Nontrivial (M ⧸ (x • (⊤ : Submodule A M))) := by
      obtain ⟨hqprime, v, hv⟩ :=
        (isAssociatedPrime_iff (I := q) (M := M ⧸ (x • (⊤ : Submodule A M)))).mp hq
      refine ⟨v, 0, ?_⟩
      intro hcon
      refine hqprime.ne_top ?_
      rw [hv, hcon]
      refine le_antisymm le_top fun a _ => ?_
      rw [Submodule.mem_colon_singleton, smul_zero]
      exact Submodule.zero_mem _
    haveI hntM : Nontrivial M := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      haveI := hcon
      have hsub : Subsingleton (M ⧸ (x • (⊤ : Submodule A M))) :=
        Function.Surjective.subsingleton (Submodule.mkQ_surjective _)
      exact (not_subsingleton _) hsub
    have hgq : HasGradeGE (maximalIdeal A) (ModuleCat.of A (M ⧸ (x • (⊤ : Submodule A M)))) n := by
      refine hasGradeGE_quotSMulTop (ModuleCat.of A M) hxreg (maximalIdeal_smul_top_lt_top M) ?_
        ⟨x :: t, hlen, hmem, hreg⟩
      exact @maximalIdeal_smul_top_lt_top A _ _ _
        (M ⧸ (x • (⊤ : Submodule A M))) _ _ hfinq hntq
    obtain ⟨s, hslen, hshead⟩ := ih (M ⧸ (x • (⊤ : Submodule A M))) hgq q hq
    have hrel : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum A) < s.head := by
      change p < s.head.asIdeal
      rw [hshead]
      exact hpq
    refine ⟨s.cons ⟨p, ‹p.IsPrime›⟩ hrel, ?_, ?_⟩
    · rw [RelSeries.cons_length, hslen]
    · rfl

/-- **Grade is bounded by the dimension above every associated prime.**  A regular sequence in the
maximal ideal produces a prime chain of the same length starting at any associated prime.  Passing
that chain to the quotient gives the claimed dimension bound. -/
theorem hasGradeGE_le_ringKrullDim_quotient_associated
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hgrade : HasGradeGE (maximalIdeal A) (ModuleCat.of A M) n)
    (p : Ideal A) (hp : p ∈ associatedPrimes A M) :
    (((n : ℕ∞) : WithBot ℕ∞)) ≤ ringKrullDim (A ⧸ p) := by
  let f := Ideal.Quotient.mk p
  obtain ⟨s, hslen, hshead⟩ := exists_ltSeries_of_hasGradeGE n M hgrade p hp
  have hp_le (i : Fin (s.length + 1)) : p ≤ (s i).asIdeal := by
    have hpi : s.head ≤ s i := s.strictMono.monotone (Fin.zero_le i)
    rw [← PrimeSpectrum.asIdeal_le_asIdeal] at hpi
    simpa [hshead] using hpi
  have map_strict (i : Fin s.length) :
      Ideal.map f (s i.castSucc).asIdeal < Ideal.map f (s i.succ).asIdeal := by
    have hstep : (s i.castSucc).asIdeal < (s i.succ).asIdeal := by
      refine lt_of_le_not_ge
        ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 (s.step i).le) ?_
      intro hge
      exact (s.step i).not_ge ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 hge)
    refine lt_of_le_of_ne (Ideal.map_mono hstep.le) ?_
    intro heq
    have hcomap := congrArg (Ideal.comap f) heq
    rw [Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective] at hcomap
    have hker : Ideal.comap f (⊥ : Ideal (A ⧸ p)) = p := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [hker, sup_eq_left.mpr (hp_le i.castSucc),
      sup_eq_left.mpr (hp_le i.succ)] at hcomap
    exact hstep.ne hcomap
  let sq : LTSeries (PrimeSpectrum (A ⧸ p)) :=
    { length := s.length
      toFun := fun i =>
        ⟨Ideal.map f (s i).asIdeal,
          Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
            rw [Ideal.mk_ker]
            exact hp_le i)⟩
      step := fun i => map_strict i }
  have hlength : sq.length ≤ Order.height sq.last := Order.length_le_height_last
  calc
    (((n : ℕ∞) : WithBot ℕ∞)) = ((sq.length : ℕ∞) : WithBot ℕ∞) := by
      rw [show sq.length = s.length from rfl, hslen]
    _ ≤ (sq.last.asIdeal.height : WithBot ℕ∞) := by
      rw [sq.last.height_eq_orderHeight]
      exact_mod_cast hlength
    _ ≤ ringKrullDim (A ⧸ p) := sq.last.asIdeal.height_le_ringKrullDim_of_isPrime

end GaloisForLFunctions.HTGeometry
