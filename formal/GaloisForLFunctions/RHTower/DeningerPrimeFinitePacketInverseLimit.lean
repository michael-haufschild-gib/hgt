import GaloisForLFunctions.RHTower.DeningerPrimeFiniteCyclotomicTransitionNaturality
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The literal Deninger packet as its canonical finite Frobenius inverse limit

Finite cyclotomic reductions were previously known to separate the literal packet, but no
inverse-limit identification was available.  After proving canonical transition naturality,
compactness upgrades joint injectivity and finite-stage surjectivity to an exact topological
identification.

The inverse limit is represented concretely as the subgroup of coherent families.  Surjectivity
is not postulated: closed finite-stage fibres are nonempty and directed, so compactness of the
literal packet produces a simultaneous lift.
-/

namespace RHTower

open Set
open Topology

noncomputable section

instance deningerFiniteFrobeniusStage_nonempty (p : ℕ) :
    Nonempty (DeningerFiniteFrobeniusStage p) :=
  ⟨⟨1, one_ne_zero, Nat.coprime_one_right p⟩⟩

/-- Coherent families in the canonical inverse system of finite Frobenius packet quotients. -/
noncomputable def deningerPrimeFinitePacketLimitSubgroup (p : Nat.Primes) :
    Subgroup (∀ s : DeningerFiniteFrobeniusStage (p : ℕ),
      DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) where
  carrier x := ∀ {s t : DeningerFiniteFrobeniusStage (p : ℕ)}
    (hst : s ≤ t),
      deningerFiniteFrobeniusStageQuotientMap hst (x t) = x s
  one_mem' := by
    intro s t hst
    change deningerFiniteFrobeniusStageQuotientMap hst
      (1 : DeningerFiniteFrobeniusStageQuotient (p : ℕ) t) =
        (1 : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s)
    exact map_one _
  mul_mem' := by
    intro x y hx hy s t hst
    change deningerFiniteFrobeniusStageQuotientMap hst
      (x t * y t) = x s * y s
    rw [map_mul, hx hst, hy hst]
  inv_mem' := by
    intro x hx s t hst
    change deningerFiniteFrobeniusStageQuotientMap hst
      (x t)⁻¹ = (x s)⁻¹
    rw [map_inv, hx hst]

abbrev DeningerPrimeFinitePacketLimit (p : Nat.Primes) :=
  deningerPrimeFinitePacketLimitSubgroup p

/-- Send an actual packet class to all of its compatible finite reductions. -/
noncomputable def deningerPrimePacketToFiniteLimit (p : Nat.Primes) :
    DeningerPacketFrobeniusQuotient p →*
      DeningerPrimeFinitePacketLimit p where
  toFun x :=
    ⟨fun s => deningerPrimeFiniteStageQuotientReduction p s x,
      fun hst =>
        deningerPrimeFiniteStageQuotientReduction_transition p hst x⟩
  map_one' := by
    apply Subtype.ext
    funext s
    change deningerPrimeFiniteStageQuotientReduction p s 1 = 1
    exact map_one _
  map_mul' x y := by
    apply Subtype.ext
    funext s
    change deningerPrimeFiniteStageQuotientReduction p s (x * y) =
      deningerPrimeFiniteStageQuotientReduction p s x *
        deningerPrimeFiniteStageQuotientReduction p s y
    exact map_mul _ _ _

theorem deningerPrimePacketToFiniteLimit_apply (p : Nat.Primes)
    (x : DeningerPacketFrobeniusQuotient p)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    (deningerPrimePacketToFiniteLimit p x).1 s =
      deningerPrimeFiniteStageQuotientReduction p s x :=
  rfl

theorem deningerPrimePacketToFiniteLimit_continuous (p : Nat.Primes) :
    Continuous (deningerPrimePacketToFiniteLimit p) := by
  apply continuous_induced_rng.2
  exact continuous_pi fun s =>
    deningerPrimeFiniteStageQuotientReduction_continuous p s

theorem deningerPrimePacketToFiniteLimit_injective (p : Nat.Primes) :
    Function.Injective (deningerPrimePacketToFiniteLimit p) := by
  intro x y hxy
  apply deningerPrimeFiniteStageQuotientReduction_jointly_injective p
  intro s
  exact congrArg
    (fun z : DeningerPrimeFinitePacketLimit p => z.1 s) hxy

/-- Closed fibre over one coordinate of a coherent finite packet. -/
def deningerPrimeFinitePacketFiber (p : Nat.Primes)
    (y : DeningerPrimeFinitePacketLimit p)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Set (DeningerPacketFrobeniusQuotient p) :=
  {x | deningerPrimeFiniteStageQuotientReduction p s x = y.1 s}

theorem deningerPrimeFinitePacketFiber_nonempty (p : Nat.Primes)
    (y : DeningerPrimeFinitePacketLimit p)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    (deningerPrimeFinitePacketFiber p y s).Nonempty := by
  obtain ⟨x, hx⟩ :=
    deningerPrimeFiniteStageQuotientReduction_surjective p s (y.1 s)
  exact ⟨x, hx⟩

theorem deningerPrimeFinitePacketFiber_isClosed (p : Nat.Primes)
    (y : DeningerPrimeFinitePacketLimit p)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    IsClosed (deningerPrimeFinitePacketFiber p y s) := by
  exact isClosed_eq
    (deningerPrimeFiniteStageQuotientReduction_continuous p s)
    continuous_const

/-- Fibres at larger common stages refine fibres at any two smaller stages. -/
theorem deningerPrimeFinitePacketFiber_directed (p : Nat.Primes)
    (y : DeningerPrimeFinitePacketLimit p) :
    Directed (· ⊇ ·) (deningerPrimeFinitePacketFiber p y) := by
  intro s t
  obtain ⟨u, hsu, htu⟩ := exists_ge_ge s t
  refine ⟨u, ?_, ?_⟩
  · intro x hx
    change deningerPrimeFiniteStageQuotientReduction p s x = y.1 s
    change deningerPrimeFiniteStageQuotientReduction p u x = y.1 u at hx
    calc
      deningerPrimeFiniteStageQuotientReduction p s x =
          deningerFiniteFrobeniusStageQuotientMap hsu
            (deningerPrimeFiniteStageQuotientReduction p u x) :=
        (deningerPrimeFiniteStageQuotientReduction_transition p hsu x).symm
      _ = deningerFiniteFrobeniusStageQuotientMap hsu (y.1 u) :=
        congrArg _ hx
      _ = y.1 s := y.2 hsu
  · intro x hx
    change deningerPrimeFiniteStageQuotientReduction p t x = y.1 t
    change deningerPrimeFiniteStageQuotientReduction p u x = y.1 u at hx
    calc
      deningerPrimeFiniteStageQuotientReduction p t x =
          deningerFiniteFrobeniusStageQuotientMap htu
            (deningerPrimeFiniteStageQuotientReduction p u x) :=
        (deningerPrimeFiniteStageQuotientReduction_transition p htu x).symm
      _ = deningerFiniteFrobeniusStageQuotientMap htu (y.1 u) :=
        congrArg _ hx
      _ = y.1 t := y.2 htu

/-- Every coherent finite packet family has one simultaneous lift to the actual compact
packet quotient. -/
theorem deningerPrimePacketToFiniteLimit_surjective (p : Nat.Primes) :
    Function.Surjective (deningerPrimePacketToFiniteLimit p) := by
  intro y
  have hnonempty :
      (⋂ s : DeningerFiniteFrobeniusStage (p : ℕ),
        deningerPrimeFinitePacketFiber p y s).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (deningerPrimeFinitePacketFiber p y)
      (deningerPrimeFinitePacketFiber_directed p y)
      (deningerPrimeFinitePacketFiber_nonempty p y)
      (fun s => (deningerPrimeFinitePacketFiber_isClosed p y s).isCompact)
      (deningerPrimeFinitePacketFiber_isClosed p y)
  obtain ⟨x, hx⟩ := hnonempty
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext s
  exact Set.mem_iInter.mp hx s

theorem deningerPrimePacketToFiniteLimit_bijective (p : Nat.Primes) :
    Function.Bijective (deningerPrimePacketToFiniteLimit p) :=
  ⟨deningerPrimePacketToFiniteLimit_injective p,
    deningerPrimePacketToFiniteLimit_surjective p⟩

/-- **Profinite completion theorem.**  The literal compact Deninger packet is homeomorphic to
the inverse limit of its canonical finite Frobenius quotients. -/
noncomputable def deningerPrimePacketFiniteLimitHomeomorph (p : Nat.Primes) :
    DeningerPacketFrobeniusQuotient p ≃ₜ
      DeningerPrimeFinitePacketLimit p :=
  IsHomeomorph.homeomorph (deningerPrimePacketToFiniteLimit p)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨deningerPrimePacketToFiniteLimit_continuous p,
        deningerPrimePacketToFiniteLimit_bijective p⟩)

theorem deningerPrimePacketFiniteLimitHomeomorph_apply
    (p : Nat.Primes) (x : DeningerPacketFrobeniusQuotient p) :
    deningerPrimePacketFiniteLimitHomeomorph p x =
      deningerPrimePacketToFiniteLimit p x :=
  rfl

end

end RHTower
