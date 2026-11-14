import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnsOfAProperForwardMonodromyGroupObeyAParityLaw
import GaloisForLFunctions.GaloisTheoryOfZeros.TheSignedPermutationsOfFiniteSupportHaveTwoSignCharacters
import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnsGenerateTheForwardMonodromyGroup

/-!
# The forward monodromy group is proper exactly when its turns obey one parity law

Let `W(b)` be the permutations of the zeros of `H_b` that commute with `z ↦ −z` and move
finitely many zeros, `χ₁` the sign on the zeros, `χ₂` the sign on the pairs `{z, −z}`, and
`K_ε(b) = ker χ₂χ₁^ε` for `ε ∈ {0, 1}`.

The turn of radius `r²` around a forward time `τ₀`, with a zero of order `2k` of `H_τ₀` at the
centre, moves `2k + 4c` zeros. The *parity law* with `ε` says that `c + εk` is even.

* **Characters on involutions** (`involution_mem_signedKernel_iff`). An involution in `W` with
  `2a` flipped and `2a + 4c` moved zeros lies in `K_ε` if and only if `c + εa` is even.
* **Converse of the parity law** (`forwardMonodromy_le_signedKernel_of_turn_parity`). If at
  every forward branch time the law with `ε` holds for arbitrarily small radii, then
  `G₊(b) ≤ K_ε(b)`.
* **Kernel form** (`forwardMonodromy_eq_signedKernel_of_not_mem`). If `G₊(b) ≠ W(b)`, then
  `G₊(b) = K_ε(b)` for one `ε`.
* **Criterion** (`exists_not_mem_forwardMonodromy_iff_exists_turn_parity`). `G₊(b) ≠ W(b)` if
  and only if the turns obey the parity law with one `ε` at every forward time.

Proof. The turns, conjugated to `b` along forward paths, generate `G₊(b)`. A conjugated turn is
an involution in `W(b)` with the counts of the turn, so the law places it in `K_ε`. `K_ε` has
index two in `W` and contains no exchange of two pairs; `G₊` has index at most two.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn Equiv
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-! ## The characters on involutions -/

/-- **The characters on involutions.** Let `n` be an involution without fixed points. A signed
involution of finite support with `2a` flipped and `2a + 4c` moved points lies in the kernel of
`pairSign · finSign ^ ε` if and only if `c + εa` is even. -/
theorem involution_mem_signedKernel_iff {X : Type*} {n : Perm X} {ε : ℕ}
    (hn : ∀ x, n (n x) = x) (hn0 : ∀ x, n x ≠ x) (hε : ε = 0 ∨ ε = 1) {σ : Perm X}
    (hσ : ∀ x, σ (σ x) = x) (hσn : ∀ x, σ (n x) = n (σ x)) (hfin : {x | σ x ≠ x}.Finite) :
    ∃ a c : ℕ, {x | σ x = n x}.ncard = 2 * a ∧ {x | σ x ≠ x}.ncard = 2 * a + 4 * c ∧
      (σ ∈ signedKernel n hn ε ↔ Even (c + ε * a)) := by
  obtain ⟨a, c, h1, h2, h3⟩ := exists_flips_exchanges_parity (G := signedKernel n hn ε) hn hn0
    (fun w₁ w₂ h₁ hf₁ h₂ hf₂ => mem_signedKernel_or_mem_or_mul_inv_mem h₁ hf₁ h₂ hf₂)
    (fun e a a' k1 k2 hea hea' he heo => exchange_not_mem_signedKernel hn0 k1 k2 hea hea' he heo)
    hε (fun f a hfa hfn hfo => flip_mem_signedKernel_iff hn0 hε hfa hfn hfo)
    hfin.toFinset.card σ hσ hσn hfin.toFinset (fun x => hfin.mem_toFinset) rfl
  exact ⟨a, c, h1, by rw [Set.ncard_eq_toFinset_card _ hfin]; exact h2, h3⟩

/-! ## Turns in the kernel -/

variable {b : ℂ}

theorem fibreNeg_fibreNeg (b : ℂ) (x : {z : ℂ // complexHeat b z = 0}) :
    fibreNeg b (fibreNeg b x) = x :=
  Subtype.ext (neg_neg _)

/-- The zeros moved by a permutation that transports along `γ` are the zeros that `γ` does not
transport to themselves. -/
theorem ncard_setOf_ne_eq_of_transports {τ₁ : ℂ} {γ : ℝ → ℂ} (hγ : IsForwardPath γ)
    {σ : Perm {z : ℂ // complexHeat τ₁ z = 0}} (hact : ∀ p, Transports γ p.1 (σ p).1) :
    {p | σ p ≠ p}.ncard = {z : ℂ | complexHeat τ₁ z = 0 ∧ ¬ Transports γ z z}.ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, fun hT => hp (Subtype.ext (hγ.transports_unique (hact p) hT))⟩
  · rintro ⟨hz, hT⟩
    refine ⟨⟨z, hz⟩, fun h => hT ?_, rfl⟩
    have h' := hact ⟨z, hz⟩
    rw [h] at h'
    exact h'

/-- An involution over `τ₁` with `2k` flipped and `2k + 4c` moved zeros, `c + εk` even, carried
to the base by a bijection of the fibres that commutes with the reflections, lies in `K_ε(b)`. -/
theorem permCongr_mem_signedKernel_of_parity {ε : ℕ} (hb : b ∉ branchTimes)
    (hε : ε = 0 ∨ ε = 1) {τ₁ : ℂ}
    (ψ : {z : ℂ // complexHeat τ₁ z = 0} ≃ {z : ℂ // complexHeat b z = 0})
    (hψn : ∀ q, ψ (fibreNeg τ₁ q) = fibreNeg b (ψ q))
    {T : Perm {z : ℂ // complexHeat τ₁ z = 0}} (hT2 : ∀ p, T (T p) = p)
    (hTn : ∀ p, T (fibreNeg τ₁ p) = fibreNeg τ₁ (T p)) (hfin : {p | T p ≠ p}.Finite)
    {k c : ℕ} (hflip : {p | T p = fibreNeg τ₁ p}.ncard = 2 * k)
    (hmoved : {p | T p ≠ p}.ncard = 2 * k + 4 * c) (hpar : Even (c + ε * k)) :
    ψ.permCongr T ∈ signedKernel (fibreNeg b) (fibreNeg_fibreNeg b) ε := by
  have hψs : ∀ y, ψ.symm (fibreNeg b y) = fibreNeg τ₁ (ψ.symm y) := fun y => by
    rw [Equiv.symm_apply_eq, hψn, Equiv.apply_symm_apply]
  have hL2 : ∀ x, ψ.permCongr T (ψ.permCongr T x) = x := fun x => by
    rw [Equiv.permCongr_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply, hT2,
      Equiv.apply_symm_apply]
  have hLn : ∀ x, ψ.permCongr T (fibreNeg b x) = fibreNeg b (ψ.permCongr T x) := fun x => by
    rw [Equiv.permCongr_apply, Equiv.permCongr_apply, hψs, hTn, hψn]
  have hLfin : {x | ψ.permCongr T x ≠ x}.Finite :=
    (hfin.image ψ).subset fun x hx => ⟨ψ.symm x, fun h => hx (by
      rw [Equiv.permCongr_apply, h, Equiv.apply_symm_apply]), ψ.apply_symm_apply x⟩
  obtain ⟨e1, e2⟩ := ncard_permCongr ψ hψn T
  obtain ⟨a, c', h1, h2, h3⟩ := involution_mem_signedKernel_iff (ε := ε) (fibreNeg_fibreNeg b)
    (fibreNeg_apply_ne_self hb) hε hL2 hLn hLfin
  have ha : a = k := by
    rw [e1, hflip] at h1
    omega
  have hc : c' = c := by
    rw [e2, hmoved, ha] at h2
    omega
  rw [h3, hc, ha]
  exact hpar

variable (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)

/-- **Converse of the parity law.** Let `ε ∈ {0, 1}`. Suppose that at every forward branch time
`τ₀`, with a zero of order `2k` of `H_τ₀` at the centre, there are arbitrarily small `r` such
that the turn of radius `r²` around `τ₀` moves `2k + 4c` zeros with `c + εk` even. Then `G₊(b)`
lies in the kernel of `χ₂χ₁^ε`. -/
theorem forwardMonodromy_le_signedKernel_of_turn_parity {ε : ℕ} (hε : ε = 0 ∨ ε = 1)
    (hlaw : ∀ τ₀ : ℂ, 0 < τ₀.re → τ₀ ∈ branchTimes → ∀ k : ℕ, IsCollision τ₀ 0 (2 * k) →
      ∃ᶠ r : ℝ in 𝓝[>] 0, ∃ c : ℕ, {z : ℂ | complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 ∧
        ¬ Transports (turnPath τ₀ r) z z}.ncard = 2 * k + 4 * c ∧ Even (c + ε * k)) :
    forwardMonodromy b hb₀ hb ≤ signedKernel (fibreNeg b) (fibreNeg_fibreNeg b) ε := by
  rintro σ ⟨γ, hγ, g0, g1, hσ⟩
  have hσeq : σ = hγ.fibreEquiv g0 g1 :=
    Equiv.ext fun q => (hγ.fibreEquiv_eq g0 g1 (hσ q)).symm
  rw [hσeq]
  refine loopsIn_of_turnsIn (D := {τ : ℂ | 0 < τ.re}) (convex_halfSpace_re_gt 0)
    (isOpen_lt continuous_const Complex.continuous_re) (fun _ h => h) ?_ γ hγ g0 g1 hγ.re_pos
  intro p hp hpb η hη
  obtain ⟨k, hcen⟩ := exists_isCollision_center_two_mul p
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r ∧ r < η := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hη)] with r h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨r, ⟨c, hc1, hc2⟩, ⟨hτ₁, hb₁, T, hTG, hact, hT2, hflip⟩, hr0, hrη⟩ :=
    ((hlaw p hp hpb k hcen).and_eventually
      ((eventually_exists_turn_mem_forwardMonodromy hp hcen).and hsmall)).exists
  refine ⟨r, hr0, hrη, fun δ hδ d0 d1 _ hT => ?_⟩
  rw [mem_tailComap]
  have hTeq : hT.fibreEquiv (turnPath_zero p r) (turnPath_one p r) = T :=
    Equiv.ext fun q => hT.fibreEquiv_eq _ _ (hact q)
  rw [hTeq]
  have hφn : ∀ q, hδ.fibreEquiv d0 d1 (fibreNeg b q) =
      fibreNeg (p + (r : ℂ) ^ 2) (hδ.fibreEquiv d0 d1 q) := fun q =>
    Subtype.ext (hδ.transports_unique (hδ.transports_fibreEquiv d0 d1 (fibreNeg b q))
      (hδ.transports_fibreEquiv d0 d1 q).neg)
  have hL : ((hδ.fibreEquiv d0 d1).trans T).trans (hδ.fibreEquiv d0 d1).symm =
      (hδ.fibreEquiv d0 d1).symm.permCongr T := rfl
  rw [hL]
  exact permCongr_mem_signedKernel_of_parity hb hε (hδ.fibreEquiv d0 d1).symm
    (fun q => by rw [Equiv.symm_apply_eq, hφn, Equiv.apply_symm_apply]) hT2
    (fun q => Equiv.congr_fun (forwardMonodromy_commute_fibreNeg hTG) q)
    (finite_setOf_forwardMonodromy_ne hTG) hflip
    ((ncard_setOf_ne_eq_of_transports hT hact).trans hc1) hc2

include hb₀ hb in
/-- Over a forward time off the branch times two pairs are exchanged by a signed permutation of
finite support. -/
theorem exists_exchange_fibre :
    ∃ (e : Perm {z : ℂ // complexHeat b z = 0}) (a a' : {z : ℂ // complexHeat b z = 0}),
      a' ≠ a ∧ a' ≠ fibreNeg b a ∧ e a = a' ∧ e a' = a ∧
        (∀ x, e (fibreNeg b x) = fibreNeg b (e x)) ∧
        (∀ x, x ≠ a → x ≠ fibreNeg b a → x ≠ a' → x ≠ fibreNeg b a' → e x = x) ∧
        {x | e x ≠ x}.Finite := by
  classical
  haveI := infinite_fibre hb₀ hb
  obtain ⟨a⟩ : Nonempty {z : ℂ // complexHeat b z = 0} := inferInstance
  obtain ⟨a', ha'⟩ := Infinite.exists_notMem_finset ({a, fibreNeg b a} : Finset _)
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at ha'
  obtain ⟨e, hea, hea', he, heo⟩ :=
    exists_signedExchange (fibreNeg_fibreNeg b) (fibreNeg_apply_ne_self hb) ha'.2
  refine ⟨e, a, a', ha'.1, ha'.2, hea, hea', he, heo, ?_⟩
  refine (Set.toFinite ({a, fibreNeg b a, a', fibreNeg b a'} : Set _)).subset fun x hx => ?_
  by_contra h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
  exact hx (heo x h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- **Kernel form of a proper forward monodromy group.** If some permutation of the zeros of
`H_b` that commutes with `z ↦ −z` and moves finitely many zeros is not in `G₊(b)`, then `G₊(b)`
is the kernel of `χ₂χ₁^ε` for one `ε ∈ {0, 1}`. -/
theorem forwardMonodromy_eq_signedKernel_of_not_mem
    {w₀ : Perm {z : ℂ // complexHeat b z = 0}}
    (hw₀ : ∀ x, w₀ (fibreNeg b x) = fibreNeg b (w₀ x)) (hfin₀ : {x | w₀ x ≠ x}.Finite)
    (hw₀G : w₀ ∉ forwardMonodromy b hb₀ hb) :
    ∃ ε : ℕ, (ε = 0 ∨ ε = 1) ∧
      forwardMonodromy b hb₀ hb = signedKernel (fibreNeg b) (fibreNeg_fibreNeg b) ε := by
  obtain ⟨ε, hε, hlaw⟩ := exists_turn_parity_of_not_mem_forwardMonodromy hb₀ hb hw₀ hfin₀ hw₀G
  have hle := forwardMonodromy_le_signedKernel_of_turn_parity hb₀ hb hε
    fun τ₀ hτ₀ _ k hcen => (hlaw τ₀ hτ₀ k hcen).frequently
  refine ⟨ε, hε, le_antisymm hle fun w hw => ?_⟩
  obtain ⟨e, a, a', h1, h2, hea, hea', he, heo, hefin⟩ := exists_exchange_fibre hb₀ hb
  have heK : e ∉ signedKernel (fibreNeg b) (fibreNeg_fibreNeg b) ε :=
    exchange_not_mem_signedKernel (fibreNeg_apply_ne_self hb) h1 h2 hea hea' he heo
  rcases mem_forwardMonodromy_or_mem_or_mul_inv_mem hb₀ hb hw.1 hw.2.1 he hefin with h | h | h
  · exact h
  · exact absurd (hle h) heK
  · exact absurd (inv_mem_iff.1 ((Subgroup.mul_mem_cancel_left _ hw).1 (hle h))) heK

/-- **The forward monodromy group is proper exactly when its turns obey one parity law.** Some
permutation of the zeros of `H_b` that commutes with `z ↦ −z` and moves finitely many zeros is
not in `G₊(b)` if and only if there is `ε ∈ {0, 1}` such that at every forward time `τ₀`, with a
zero of order `2k` of `H_τ₀` at the centre, the turn of small radius `r²` around `τ₀` moves
`2k + 4c` zeros with `c + εk` even. -/
theorem exists_not_mem_forwardMonodromy_iff_exists_turn_parity :
    (∃ w : Perm {z : ℂ // complexHeat b z = 0}, (∀ x, w (fibreNeg b x) = fibreNeg b (w x)) ∧
        {x | w x ≠ x}.Finite ∧ w ∉ forwardMonodromy b hb₀ hb) ↔
      ∃ ε : ℕ, (ε = 0 ∨ ε = 1) ∧ ∀ τ₀ : ℂ, 0 < τ₀.re → ∀ k : ℕ, IsCollision τ₀ 0 (2 * k) →
        ∀ᶠ r : ℝ in 𝓝[>] 0, ∃ c : ℕ, {z : ℂ | complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 ∧
          ¬ Transports (turnPath τ₀ r) z z}.ncard = 2 * k + 4 * c ∧ Even (c + ε * k) := by
  constructor
  · rintro ⟨w, hw, hfin, hwG⟩
    exact exists_turn_parity_of_not_mem_forwardMonodromy hb₀ hb hw hfin hwG
  · rintro ⟨ε, hε, hlaw⟩
    have hle := forwardMonodromy_le_signedKernel_of_turn_parity hb₀ hb hε
      fun τ₀ hτ₀ _ k hcen => (hlaw τ₀ hτ₀ k hcen).frequently
    obtain ⟨e, a, a', h1, h2, hea, hea', he, heo, hefin⟩ := exists_exchange_fibre hb₀ hb
    exact ⟨e, he, hefin, fun h => exchange_not_mem_signedKernel (fibreNeg_apply_ne_self hb)
      h1 h2 hea hea' he heo (hle h)⟩

end GaloisForLFunctions.GaloisTheoryOfZeros
