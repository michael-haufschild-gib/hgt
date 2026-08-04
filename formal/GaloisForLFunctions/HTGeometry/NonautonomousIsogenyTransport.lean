import GaloisForLFunctions.HTGeometry.IsogenyKernelClosure
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The erased sector of a time-dependent protocol transports canonically

A nonautonomous protocol is a sequence of groups with a map from each phase to the next.  Its prefix
composites have kernels growing with depth, and the closure of their union is the sector the protocol
erases at that phase.

Peeling the first step off a prefix composite shows the erased sector at one phase is exactly the
preimage of the erased sector at the next.  When each step is open and continuous the same holds after
closure, and when each step is surjective the quotients by the erased sectors are *isomorphic*: the
reversible position of the protocol is transported without loss from phase to phase, so the reversible
sectors form a flat system over discrete time, with a holonomy automorphism for a periodic protocol.

The index of the prefix composite's target is carried by the same recursion as the composite, so no
arithmetic on indices ever enters a type.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {G : ℕ → Type*} [∀ i, CommGroup (G i)]

/-- The phase reached from phase `i` after `n` protocol steps. -/
def prefixIndex : ℕ → ℕ → ℕ
  | i, 0 => i
  | i, n + 1 => prefixIndex (i + 1) n

/-- The prefix composite of a time-dependent protocol, peeled from the near end. -/
def prefixHom (a : ∀ i, G i →* G (i + 1)) : ∀ i n : ℕ, G i →* G (prefixIndex i n)
  | i, 0 => MonoidHom.id (G i)
  | i, n + 1 => (prefixHom a (i + 1) n).comp (a i)

@[simp]
theorem prefixHom_zero_apply (a : ∀ i, G i →* G (i + 1)) (i : ℕ) (x : G i) :
    prefixHom a i 0 x = x := rfl

@[simp]
theorem prefixHom_succ_apply (a : ∀ i, G i →* G (i + 1)) (i n : ℕ) (x : G i) :
    prefixHom a i (n + 1) x = prefixHom a (i + 1) n (a i x) := rfl

/-- The directions erased by the first `n` steps from phase `i`. -/
def prefixKernel (a : ∀ i, G i →* G (i + 1)) (i n : ℕ) : Subgroup (G i) :=
  (prefixHom a i n).ker

theorem prefixKernel_zero (a : ∀ i, G i →* G (i + 1)) (i : ℕ) : prefixKernel a i 0 = ⊥ := by
  ext x
  exact Iff.rfl

/-- **Peeling the first step.**  What the first `n + 1` steps erase at phase `i` is the preimage of
what the first `n` steps erase at phase `i + 1`. -/
theorem prefixKernel_succ (a : ∀ i, G i →* G (i + 1)) (i n : ℕ) :
    prefixKernel a i (n + 1) = (prefixKernel a (i + 1) n).comap (a i) :=
  (MonoidHom.comap_ker (prefixHom a (i + 1) n) (a i)).symm

theorem prefixKernel_le_succ (a : ∀ i, G i →* G (i + 1)) (i n : ℕ) :
    prefixKernel a i n ≤ prefixKernel a i (n + 1) := by
  induction n generalizing i with
  | zero =>
      rw [prefixKernel_zero]
      exact bot_le
  | succ n ih =>
      rw [prefixKernel_succ a i n, prefixKernel_succ a i (n + 1)]
      exact Subgroup.comap_mono (ih (i + 1))

theorem prefixKernel_monotone (a : ∀ i, G i →* G (i + 1)) (i : ℕ) :
    Monotone (prefixKernel a i) :=
  monotone_nat_of_le_succ (prefixKernel_le_succ a i)

/-- The sector erased by the whole future of the protocol at phase `i`, before closure. -/
def erasedSector (a : ∀ i, G i →* G (i + 1)) (i : ℕ) : Subgroup (G i) :=
  ⨆ n, prefixKernel a i n

theorem mem_erasedSector_iff (a : ∀ i, G i →* G (i + 1)) (i : ℕ) (x : G i) :
    x ∈ erasedSector a i ↔ ∃ n, prefixHom a i n x = 1 := by
  rw [erasedSector, Subgroup.mem_iSup_of_directed (prefixKernel_monotone a i).directed_le]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, hn⟩

/-- **Canonical transport of the erased sector.**  The sector erased at a phase is exactly the
preimage of the sector erased at the next phase. -/
theorem erasedSector_comap (a : ∀ i, G i →* G (i + 1)) (i : ℕ) :
    (erasedSector a (i + 1)).comap (a i) = erasedSector a i := by
  ext x
  rw [Subgroup.mem_comap, mem_erasedSector_iff, mem_erasedSector_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, hn⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
        refine ⟨0, ?_⟩
        show a i x = 1
        rw [show x = 1 from hn, map_one]
    | succ n => exact ⟨n, hn⟩

section Topological

variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]

/-- The closed sector erased by the whole future of the protocol at phase `i`. -/
def erasedClosure (a : ∀ i, G i →* G (i + 1)) (i : ℕ) : Subgroup (G i) :=
  (erasedSector a i).topologicalClosure

/-- **Canonical transport of the closed erased sector.**  For an open continuous protocol the closed
erased sector at a phase is the preimage of the closed erased sector at the next phase. -/
theorem erasedClosure_comap (a : ∀ i, G i →* G (i + 1))
    (hopen : ∀ i, IsOpenMap (a i)) (hcont : ∀ i, Continuous (a i)) (i : ℕ) :
    (erasedClosure a (i + 1)).comap (a i) = erasedClosure a i := by
  ext x
  change a i x ∈ closure (erasedSector a (i + 1) : Set (G (i + 1))) ↔
    x ∈ closure (erasedSector a i : Set (G i))
  have hpre := (hopen i).preimage_closure_eq_closure_preimage (hcont i)
    (erasedSector a (i + 1) : Set (G (i + 1)))
  rw [← Set.mem_preimage, hpre]
  have hset : a i ⁻¹' (erasedSector a (i + 1) : Set (G (i + 1)))
      = (erasedSector a i : Set (G i)) := by
    ext y
    exact SetLike.ext_iff.mp (erasedSector_comap a i) y
  rw [hset]

omit [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] in
/-- **A stabilizing protocol erases exactly one subgroup.**  If no depth beyond `N` erases anything
new, the erased sector is the depth-`N` kernel. -/
theorem erasedSector_eq_prefixKernel_of_stabilizes (a : ∀ i, G i →* G (i + 1)) (i N : ℕ)
    (hstab : ∀ n, N ≤ n → prefixKernel a i n = prefixKernel a i N) :
    erasedSector a i = prefixKernel a i N := by
  refine le_antisymm (iSup_le fun n => ?_) (le_iSup (fun n => prefixKernel a i n) N)
  refine le_trans (prefixKernel_monotone a i (le_max_left n N)) ?_
  exact le_of_eq (hstab _ (le_max_right n N))

/-- **A closed erased sector needs no closure.** -/
theorem erasedClosure_eq_of_isClosed (a : ∀ i, G i →* G (i + 1)) (i : ℕ)
    (h : IsClosed (erasedSector a i : Set (G i))) : erasedClosure a i = erasedSector a i := by
  refine SetLike.ext' ?_
  rw [erasedClosure, Subgroup.topologicalClosure_coe]
  exact h.closure_eq

/-- **A stabilizing protocol with a closed stable kernel needs no closure at all.** -/
theorem erasedClosure_eq_prefixKernel_of_stabilizes (a : ∀ i, G i →* G (i + 1)) (i N : ℕ)
    (hstab : ∀ n, N ≤ n → prefixKernel a i n = prefixKernel a i N)
    (hclosed : IsClosed (prefixKernel a i N : Set (G i))) :
    erasedClosure a i = prefixKernel a i N := by
  rw [erasedClosure_eq_of_isClosed a i (by
      rw [erasedSector_eq_prefixKernel_of_stabilizes a i N hstab]
      exact hclosed),
    erasedSector_eq_prefixKernel_of_stabilizes a i N hstab]

/-- The reversible position at phase `i`: the quotient by the erased sector. -/
abbrev reversibleQuotient (a : ∀ i, G i →* G (i + 1)) (i : ℕ) : Type _ :=
  G i ⧸ erasedClosure a i

/-- The protocol's step on reversible positions. -/
def reversibleStep (a : ∀ i, G i →* G (i + 1))
    (hopen : ∀ i, IsOpenMap (a i)) (hcont : ∀ i, Continuous (a i)) (i : ℕ) :
    reversibleQuotient a i →* reversibleQuotient a (i + 1) :=
  QuotientGroup.map _ _ (a i) (le_of_eq (erasedClosure_comap a hopen hcont i).symm)

theorem reversibleStep_mk (a : ∀ i, G i →* G (i + 1))
    (hopen : ∀ i, IsOpenMap (a i)) (hcont : ∀ i, Continuous (a i)) (i : ℕ) (x : G i) :
    reversibleStep a hopen hcont i (QuotientGroup.mk x) = QuotientGroup.mk (a i x) := rfl

theorem reversibleStep_bijective (a : ∀ i, G i →* G (i + 1))
    (hopen : ∀ i, IsOpenMap (a i)) (hcont : ∀ i, Continuous (a i))
    (hsurj : ∀ i, Function.Surjective (a i)) (i : ℕ) :
    Function.Bijective (reversibleStep a hopen hcont i) := by
  constructor
  · refine (injective_iff_map_eq_one _).2 ?_
    intro y
    refine QuotientGroup.induction_on y ?_
    intro x hy
    rw [reversibleStep_mk, QuotientGroup.eq_one_iff] at hy
    rw [QuotientGroup.eq_one_iff]
    have hx : x ∈ (erasedClosure a (i + 1)).comap (a i) := hy
    rwa [erasedClosure_comap a hopen hcont i] at hx
  · intro y
    refine QuotientGroup.induction_on y ?_
    intro g
    obtain ⟨x, rfl⟩ := hsurj i g
    exact ⟨QuotientGroup.mk x, rfl⟩

/-- **The reversible sector is transported without loss.**  Each step of an open continuous
surjective protocol is an isomorphism of reversible positions. -/
def reversibleStepEquiv (a : ∀ i, G i →* G (i + 1))
    (hopen : ∀ i, IsOpenMap (a i)) (hcont : ∀ i, Continuous (a i))
    (hsurj : ∀ i, Function.Surjective (a i)) (i : ℕ) :
    reversibleQuotient a i ≃* reversibleQuotient a (i + 1) :=
  MulEquiv.ofBijective (reversibleStep a hopen hcont i)
    (reversibleStep_bijective a hopen hcont hsurj i)

/-- **Flat transport over discrete time.**  Reversible positions at any two phases of the protocol
are canonically isomorphic. -/
def reversibleTransport (a : ∀ i, G i →* G (i + 1))
    (hopen : ∀ i, IsOpenMap (a i)) (hcont : ∀ i, Continuous (a i))
    (hsurj : ∀ i, Function.Surjective (a i)) (i : ℕ) :
    ∀ n : ℕ, reversibleQuotient a i ≃* reversibleQuotient a (i + n)
  | 0 => MulEquiv.refl _
  | n + 1 =>
      (reversibleTransport a hopen hcont hsurj i n).trans
        (reversibleStepEquiv a hopen hcont hsurj (i + n))

/-- **Holonomy of a periodic protocol.**  One circuit of a protocol whose phase `i + p` is identified
with phase `i` is an automorphism of the reversible position. -/
def reversibleHolonomy (a : ∀ i, G i →* G (i + 1))
    (hopen : ∀ i, IsOpenMap (a i)) (hcont : ∀ i, Continuous (a i))
    (hsurj : ∀ i, Function.Surjective (a i)) (i p : ℕ)
    (period : reversibleQuotient a (i + p) ≃* reversibleQuotient a i) :
    reversibleQuotient a i ≃* reversibleQuotient a i :=
  (reversibleTransport a hopen hcont hsurj i p).trans period

end Topological

end

end GaloisForLFunctions.HTGeometry
