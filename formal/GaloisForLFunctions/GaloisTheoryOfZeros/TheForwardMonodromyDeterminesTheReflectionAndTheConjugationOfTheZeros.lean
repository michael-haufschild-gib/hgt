import GaloisForLFunctions.GaloisTheoryOfZeros.ConjugationOfTheZerosIsAMonodromyOfTheHeatCover
import GaloisForLFunctions.GaloisTheoryOfZeros.EveryForwardMonodromyMovesFinitelyManyZeros
import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupMovesFinitelyManyZerosInDistinctPairsAtWill

/-!
# The forward monodromy determines the reflection and the conjugation of the zeros

The zeros of `H_b` carry two involutions: the reflection `r : z ↦ −z` and, over a real time, the
conjugation `c : z ↦ z̄`. Both are determined by the monodromy of the heat cover over the forward
half-plane and by the mirror `τ ↦ τ̄` of its base.

* **The reflection is the centralizer** (`eq_one_or_eq_fibreNeg_of_forall_commute`). A
  permutation of the zeros of `H_b` that commutes with every element of `G₊(b)` is `1` or `r`.
  The centre of `G₊(b)` is trivial (`eq_one_of_mem_forwardMonodromy_of_forall_commute`).
* **The conjugation is the mirror** (`eq_fibreConj_or_eq_fibreConj_mul_fibreNeg`). Over a real
  time `t > 0`, conjugation carries the transport along a forward loop `γ` to the transport
  along the mirror loop `γ̄`. A permutation `σ` of the zeros of `H_t` with this property,
  `T_γ̄ = σ T_γ σ⁻¹` for every forward loop, is `c` or `c r`.
* **The Riemann hypothesis is the mirror symmetry of the monodromy**
  (`riemannHypothesis_iff_forall_transports_pathConj`). All zeros of `H_t` are real iff every
  forward loop at `t` and its mirror loop transport the zeros in the same way; RH holds iff this
  is so over every real time `t > 0` off the branch times.

Proof. A group that contains every signed 3-cycle is transitive and separates a point from every
point outside its pair, so a commuting permutation keeps every pair, with one sign for all pairs
(`IsWindowedSignedGroup.eq_self_or_eq_flip_of_commute`). The reflection moves infinitely many
zeros and is not a forward monodromy. If `σ` is a mirror intertwiner, `cσ` commutes with `G₊(t)`.
-/

open Complex Set
open RHTower Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-! ## The centralizer of a group of signed permutations -/

namespace IsWindowedSignedGroup

variable {Ω : Type*} {P : PairCoordinate Ω} {G : Subgroup (Perm Ω)}
  (hG : IsWindowedSignedGroup P G)
include hG

/-- **The centralizer.** A map of `Ω` to itself that commutes with every element of `G` is the
identity or the involution of the pairs. -/
theorem eq_self_or_eq_flip_of_commute {σ : Ω → Ω} (hσ : ∀ g ∈ G, ∀ x, σ (g x) = g (σ x)) :
    (∀ x, σ x = x) ∨ ∀ x, σ x = P.flip x := by
  -- `σ` keeps every pair: a signed 3-cycle through `σx` and two fresh pairs fixes `x`
  have hpair : ∀ x, P.pair (σ x) = P.pair x := by
    intro x
    by_contra hne
    obtain ⟨s, hs⟩ := hG.exists_pair_not_mem {P.pair x, P.pair (σ x)}
    obtain ⟨u, hu⟩ := hG.exists_pair_not_mem {P.pair x, P.pair (σ x), P.pair s}
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs hu
    obtain ⟨T, hT, h1, -, -, h4⟩ := hG.hasSignedCycle (p := σ x) (q := s) (r := u)
      (Ne.symm hs.2) (Ne.symm hu.2.2) (Ne.symm hu.2.1)
    have h5 := hσ T hT x
    rw [h4 x (fun h => hne h.symm) (Ne.symm hs.1) (Ne.symm hu.1), h1] at h5
    exact hs.2 (by rw [h5])
  have hor : ∀ x, σ x = x ∨ σ x = P.flip x := fun x =>
    (P.pair_eq_iff x (σ x)).mp (hpair x).symm
  -- transitivity makes the sign constant
  obtain ⟨_, _, x₀, _⟩ := hG.flips
  have htrans : ∀ y, ∃ g ∈ G, g x₀ = y := fun y => by
    obtain ⟨g, hg, h, -⟩ :=
      hG.exists_apply_eq_of_fixed ∅ (x := x₀) (y := y) (by simp) (by simp)
    exact ⟨g, hg, h⟩
  rcases hor x₀ with h0 | h0
  · refine Or.inl fun y => ?_
    obtain ⟨g, hg, rfl⟩ := htrans y
    rw [hσ g hg, h0]
  · refine Or.inr fun y => ?_
    obtain ⟨g, hg, rfl⟩ := htrans y
    rw [hσ g hg, h0, hG.comm g hg]

end IsWindowedSignedGroup

/-! ## The reflection is the centralizer of the forward monodromy group -/

/-- **The centralizer of `G₊(b)` is `{1, r}`.** A permutation of the zeros of `H_b` that commutes
with every forward monodromy is the identity or the reflection `z ↦ −z`. -/
theorem eq_one_or_eq_fibreNeg_of_forall_commute {b : ℂ} (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)
    {σ : Perm {z : ℂ // complexHeat b z = 0}}
    (hσ : ∀ g ∈ forwardMonodromy b hb₀ hb, σ * g = g * σ) : σ = 1 ∨ σ = fibreNeg b := by
  obtain ⟨P, hP, hG⟩ := exists_pairCoordinate_isWindowedSignedGroup hb₀ hb
  rcases hG.eq_self_or_eq_flip_of_commute (σ := ⇑σ)
    (fun g hg x => DFunLike.congr_fun (hσ g hg) x) with h | h
  · exact Or.inl (Equiv.ext h)
  · exact Or.inr (Equiv.ext fun x => (h x).trans (hP x))

/-- **The centre of `G₊(b)` is trivial.** -/
theorem eq_one_of_mem_forwardMonodromy_of_forall_commute {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) {σ : Perm {z : ℂ // complexHeat b z = 0}}
    (hσ : σ ∈ forwardMonodromy b hb₀ hb)
    (hcomm : ∀ g ∈ forwardMonodromy b hb₀ hb, σ * g = g * σ) : σ = 1 :=
  (eq_one_or_eq_fibreNeg_of_forall_commute hb₀ hb hcomm).resolve_right fun h =>
    fibreNeg_not_mem_forwardMonodromy hb₀ hb (h ▸ hσ)

/-! ## The conjugation is the mirror of the forward monodromy -/

/-- Transport along the mirror path, read back along the path. -/
theorem Transports.of_pathConj {γ : ℝ → ℂ} {z w : ℂ} (h : Transports (pathConj γ) z w) :
    Transports γ (starRingEnd ℂ z) (starRingEnd ℂ w) := by
  have h' := h.conj
  rwa [show (fun s => starRingEnd ℂ (pathConj γ s)) = γ from
    funext fun s => Complex.conj_conj (γ s)] at h'

variable {t : ℝ}

/-- **Conjugation is a mirror intertwiner.** Over a real time, conjugation carries the transport
along a path to the transport along the mirror path. -/
theorem transports_pathConj_fibreConj {γ : ℝ → ℂ} {p q : {z : ℂ // complexHeat (t : ℂ) z = 0}}
    (h : Transports γ p.1 q.1) : Transports (pathConj γ) (fibreConj t p).1 (fibreConj t q).1 :=
  h.conj

/-- **The mirror intertwiners are `c` and `cr`.** Let `σ` be a permutation of the zeros of `H_t`,
`t > 0` real, such that for every forward loop `γ` at `t` the transport along the mirror loop is
the `σ`-conjugate of the transport along `γ`. Then `σ` is `z ↦ z̄` or `z ↦ −z̄`. -/
theorem eq_fibreConj_or_eq_fibreConj_mul_fibreNeg (ht : 0 < t) (hb : (t : ℂ) ∉ branchTimes)
    {σ : Perm {z : ℂ // complexHeat (t : ℂ) z = 0}}
    (hσ : ∀ γ, IsForwardPath γ → γ 0 = t → γ 1 = t →
      ∀ p q : {z : ℂ // complexHeat (t : ℂ) z = 0}, Transports γ p.1 q.1 →
        Transports (pathConj γ) (σ p).1 (σ q).1) :
    σ = fibreConj t ∨ σ = fibreConj t * fibreNeg (t : ℂ) := by
  have ht' : 0 < ((t : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact ht
  have hcc : fibreConj t * fibreConj t = 1 :=
    Equiv.ext fun x => Subtype.ext (Complex.conj_conj x.1)
  -- `cσ` commutes with every forward monodromy
  have hκ : ∀ g ∈ forwardMonodromy (t : ℂ) ht' hb,
      (fibreConj t * σ) * g = g * (fibreConj t * σ) := by
    rintro g ⟨γ, hγ, h0, h1, hg⟩
    refine Equiv.ext fun p => Subtype.ext ?_
    exact hγ.transports_unique (hσ γ hγ h0 h1 p (g p) (hg p)).of_pathConj
      (hg (fibreConj t (σ p)))
  have hσeq : σ = fibreConj t * (fibreConj t * σ) := by
    rw [← mul_assoc, hcc, one_mul]
  rcases eq_one_or_eq_fibreNeg_of_forall_commute ht' hb hκ with h | h
  · left
    rw [hσeq, h, mul_one]
  · right
    rw [hσeq, h]

/-- **All zeros real iff the monodromy is mirror symmetric.** Over a real time `t > 0` off the
branch times, the zeros of `H_t` are fixed by conjugation iff every forward loop at `t` and its
mirror loop transport the zeros in the same way. -/
theorem fibreConj_eq_one_iff_forall_transports_pathConj (ht : 0 < t)
    (hb : (t : ℂ) ∉ branchTimes) :
    fibreConj t = 1 ↔ ∀ γ, IsForwardPath γ → γ 0 = t → γ 1 = t →
      ∀ z z' : ℂ, Transports γ z z' → Transports (pathConj γ) z z' := by
  have ht' : 0 < ((t : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact ht
  constructor
  · intro hc γ _ h0 h1 z z' h
    have hz : complexHeat (t : ℂ) z = 0 := by
      have := h.zero_left
      rwa [h0] at this
    have hz' : complexHeat (t : ℂ) z' = 0 := by
      have := h.zero_right
      rwa [h1] at this
    have ez : starRingEnd ℂ z = z := congrArg (fun κ : Perm _ => (κ ⟨z, hz⟩).1) hc
    have ez' : starRingEnd ℂ z' = z' := congrArg (fun κ : Perm _ => (κ ⟨z', hz'⟩).1) hc
    have h' := h.conj
    rw [ez, ez'] at h'
    exact h'
  · intro hm
    rcases eq_fibreConj_or_eq_fibreConj_mul_fibreNeg ht hb (σ := 1)
      (fun γ hγ h0 h1 p q h => hm γ hγ h0 h1 p.1 q.1 h) with h | h
    · exact h.symm
    · -- `c = r` is excluded: `c` is a forward monodromy, `r` is not
      have hrr : fibreNeg (t : ℂ) * fibreNeg (t : ℂ) = 1 :=
        Equiv.ext fun x => Subtype.ext (neg_neg x.1)
      have hc : fibreConj t = fibreNeg (t : ℂ) := by
        have e : fibreConj t = fibreConj t * fibreNeg (t : ℂ) * fibreNeg (t : ℂ) := by
          rw [mul_assoc, hrr, mul_one]
        rw [e, ← h, one_mul]
      exact absurd (hc ▸ fibreConj_mem_forwardMonodromy ht hb)
        (fibreNeg_not_mem_forwardMonodromy ht' hb)

/-- **The Riemann hypothesis is the mirror symmetry of the forward monodromy.** RH holds iff over
every real time `t > 0` off the branch times every forward loop at `t` and its mirror loop
transport the zeros of `H_t` in the same way. -/
theorem riemannHypothesis_iff_forall_transports_pathConj :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → (t : ℂ) ∉ branchTimes →
      ∀ γ, IsForwardPath γ → γ 0 = t → γ 1 = t →
        ∀ z z' : ℂ, Transports γ z z' → Transports (pathConj γ) z z' := by
  rw [riemannHypothesis_iff_fibreConj_eq_one]
  exact forall_congr' fun t => forall_congr' fun ht => forall_congr' fun hb =>
    fibreConj_eq_one_iff_forall_transports_pathConj ht hb

end GaloisForLFunctions.GaloisTheoryOfZeros
