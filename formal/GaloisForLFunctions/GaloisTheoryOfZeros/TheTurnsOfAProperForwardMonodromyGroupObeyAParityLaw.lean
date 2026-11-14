import GaloisForLFunctions.GaloisTheoryOfZeros.EveryTurnIsAnInvolutionThatFlipsAsManyPairsAsTheOrderOfTheCentreValue
import GaloisForLFunctions.GaloisTheoryOfZeros.TheInvolutionsOfAProperForwardMonodromyGroupObeyAParityLaw
import GaloisForLFunctions.GaloisTheoryOfZeros.TheSignBranchPointsLieInTheForwardHalfPlane

/-!
# The turns of a proper forward monodromy group obey a parity law

For a forward time `τ₀` let `k` be the order of vanishing of the centre value at `τ₀`, and let
`M_r(τ₀)` be the number of zeros of `H_{τ₀+r²}` that the turn of radius `r²` around `τ₀` moves.
The turn flips `k` pairs and exchanges `c` couples of pairs, `M_r(τ₀) = 2k + 4c`.

Let `W(b)` be the permutations of the zeros of `H_b` that commute with `z ↦ −z` and move
finitely many zeros. Suppose `G₊(b) ≠ W(b)`.

* **Parity law** (`exists_turn_parity_of_not_mem_forwardMonodromy`). There is `ε ∈ {0, 1}` such
  that at every forward time and for all small `r` the number `c + εk` is even.
* **Off the centre times** (`mem_forwardMonodromy_of_frequently_not_dvd`). If `c(τ₀) ≠ 0`, then
  `8 ∣ M_r(τ₀)`. So one forward time off the centre times whose turn moves a number of zeros
  not divisible by `8` gives `G₊(b) = W(b)` at every base time. Real times are of this kind
  (`mem_forwardMonodromy_of_real_frequently_not_dvd`).
* **Simple centre times** (`exists_forall_simple_centre_time_mod_eight`). `M_r(τ₀) mod 8` is the
  same number, `2` or `6`, at all simple zeros of the centre value.

Proof. The turn is an involution of `G₊(τ₀ + r²)` with `2k` flipped zeros. Transport it to the
base `b` along a forward path: the transport commutes with `z ↦ −z`, so the counts of flipped
and of moved zeros are kept. Apply the parity law of the involutions of `G₊(b)`.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn Equiv
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-- The centre value does not vanish at a real time. -/
theorem complexHeat_ofReal_center_ne_zero (t : ℝ) : complexHeat (t : ℂ) 0 ≠ 0 := fun h => by
  obtain ⟨m, hm2, -, hc⟩ := exists_isCollision_center h
  exact (hc.re_pos_of_center (by omega)).2 (Complex.ofReal_im t)

/-- A bijection of two fibres that commutes with the reflections keeps the number of flipped
zeros and the number of moved zeros of a permutation. -/
theorem ncard_permCongr {b₁ b : ℂ}
    (φ : {z : ℂ // complexHeat b₁ z = 0} ≃ {z : ℂ // complexHeat b z = 0})
    (hφn : ∀ q, φ (fibreNeg b₁ q) = fibreNeg b (φ q))
    (σ : Perm {z : ℂ // complexHeat b₁ z = 0}) :
    {x | φ.permCongr σ x = fibreNeg b x}.ncard = {y | σ y = fibreNeg b₁ y}.ncard ∧
      {x | φ.permCongr σ x ≠ x}.ncard = {y | σ y ≠ y}.ncard := by
  have h1 : {x | φ.permCongr σ x = fibreNeg b x} = φ '' {y | σ y = fibreNeg b₁ y} := by
    ext x
    constructor
    · intro h
      refine ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
      have h' : φ (σ (φ.symm x)) = fibreNeg b x := h
      show σ (φ.symm x) = fibreNeg b₁ (φ.symm x)
      apply φ.injective
      rw [h', hφn, Equiv.apply_symm_apply]
    · rintro ⟨y, hy, rfl⟩
      have hy' : σ y = fibreNeg b₁ y := hy
      show φ (σ (φ.symm (φ y))) = fibreNeg b (φ y)
      rw [Equiv.symm_apply_apply, hy', hφn]
  have h2 : {x | φ.permCongr σ x ≠ x} = φ '' {y | σ y ≠ y} := by
    ext x
    constructor
    · intro h
      refine ⟨φ.symm x, fun h' => h ?_, φ.apply_symm_apply x⟩
      show φ (σ (φ.symm x)) = x
      rw [h', Equiv.apply_symm_apply]
    · rintro ⟨y, hy, rfl⟩
      intro h
      have h' : φ (σ (φ.symm (φ y))) = φ y := h
      rw [Equiv.symm_apply_apply] at h'
      exact hy (φ.injective h')
  rw [h1, h2, Set.ncard_image_of_injective _ φ.injective,
    Set.ncard_image_of_injective _ φ.injective]
  exact ⟨rfl, rfl⟩

variable {b : ℂ} (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)

/-- **The parity law of the turns.** If some permutation of the zeros of `H_b` that commutes
with `z ↦ −z` and moves finitely many zeros is not in `G₊(b)`, then there is `ε ∈ {0, 1}` such
that for every forward time `τ₀`, with a zero of order `2k` of `H_τ₀` at the centre, and all
small `r`, the turn of radius `r²` around `τ₀` moves `2k + 4c` zeros with `c + εk` even. -/
theorem exists_turn_parity_of_not_mem_forwardMonodromy
    {w₀ : Perm {z : ℂ // complexHeat b z = 0}}
    (hw₀ : ∀ x, w₀ (fibreNeg b x) = fibreNeg b (w₀ x)) (hfin₀ : {x | w₀ x ≠ x}.Finite)
    (hw₀G : w₀ ∉ forwardMonodromy b hb₀ hb) :
    ∃ ε : ℕ, (ε = 0 ∨ ε = 1) ∧ ∀ τ₀ : ℂ, 0 < τ₀.re → ∀ k : ℕ, IsCollision τ₀ 0 (2 * k) →
      ∀ᶠ r : ℝ in 𝓝[>] 0, ∃ c : ℕ, {z : ℂ | complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 ∧
        ¬ Transports (turnPath τ₀ r) z z}.ncard = 2 * k + 4 * c ∧ Even (c + ε * k) := by
  obtain ⟨ε, hε01, -, hlaw⟩ := exists_parity_of_not_mem_forwardMonodromy hb₀ hb hw₀ hfin₀ hw₀G
  refine ⟨ε, hε01, fun τ₀ hτ₀ k hcen => ?_⟩
  filter_upwards [eventually_exists_turn_mem_forwardMonodromy hτ₀ hcen,
    eventually_nhdsGT_of_exists_Ioo (exists_isForwardPath_turnPath hτ₀)] with r hr hγ
  obtain ⟨hτ₁, hb₁, σ, hσ, hact, hσ2, hflip⟩ := hr
  -- transport the turn to the base `b`
  obtain ⟨δ, hδ, g0, g1⟩ := exists_isForwardPath hτ₁ hb₀ hb₁ hb
  obtain ⟨φ, hφ⟩ := hδ.exists_fibreEquiv g0 g1
  have hφn : ∀ q, φ (fibreNeg (τ₀ + (r : ℂ) ^ 2) q) = fibreNeg b (φ q) := fun q =>
    Subtype.ext (hδ.transports_unique (hφ (fibreNeg (τ₀ + (r : ℂ) ^ 2) q)) (hφ q).neg)
  obtain ⟨a, c, h1, h2, h3⟩ := hlaw (φ.permCongr σ)
    (hδ.permCongr_mem_forwardMonodromy g0 g1 hφ hσ) (fun x => by
      rw [Equiv.permCongr_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply, hσ2,
        Equiv.apply_symm_apply])
  obtain ⟨e1, e2⟩ := ncard_permCongr φ hφn σ
  have ha : a = k := by
    rw [e1, hflip] at h1
    omega
  subst ha
  refine ⟨c, ?_, h3⟩
  rw [← h2, e2, ← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, hT⟩
    refine ⟨⟨z, hz⟩, fun h => hT ?_, rfl⟩
    have h' := hact ⟨z, hz⟩
    rw [h] at h'
    exact h'
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, fun hT => hp (Subtype.ext (hγ.transports_unique (hact p) hT))⟩

/-- **Simple centre times have one ramification modulo eight.** If `G₊(b)` is not the group of
all signed permutations of finite support, there is `m ∈ {2, 6}` such that at every simple zero
`τ₀` of the centre value in the forward half-plane the turn of small radius around `τ₀` moves a
number of zeros congruent to `m` modulo `8`. -/
theorem exists_forall_simple_centre_time_mod_eight
    {w₀ : Perm {z : ℂ // complexHeat b z = 0}}
    (hw₀ : ∀ x, w₀ (fibreNeg b x) = fibreNeg b (w₀ x)) (hfin₀ : {x | w₀ x ≠ x}.Finite)
    (hw₀G : w₀ ∉ forwardMonodromy b hb₀ hb) :
    ∃ m : ℕ, (m = 2 ∨ m = 6) ∧ ∀ τ₀ : ℂ, 0 < τ₀.re → IsCollision τ₀ 0 2 →
      ∀ᶠ r : ℝ in 𝓝[>] 0, {z : ℂ | complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 ∧
        ¬ Transports (turnPath τ₀ r) z z}.ncard % 8 = m := by
  obtain ⟨ε, hε, hlaw⟩ :=
    exists_turn_parity_of_not_mem_forwardMonodromy hb₀ hb hw₀ hfin₀ hw₀G
  refine ⟨2 + 4 * ε, by rcases hε with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl],
    fun τ₀ hτ₀ hcen => ?_⟩
  filter_upwards [hlaw τ₀ hτ₀ 1 hcen] with r hr
  obtain ⟨c, h1, d, hd⟩ := hr
  rw [h1]
  rcases hε with rfl | rfl <;> omega

/-- **A turn off the centre times that moves a number of zeros not divisible by eight gives
every signed permutation.** Let `τ₀` be a forward time with `H_τ₀(0) ≠ 0`. If for arbitrarily
small `r` the number of zeros moved by the turn of radius `r²` around `τ₀` is not divisible by
`8`, then at every forward base time `b` off the branch times `G₊(b)` contains every permutation
of the zeros of `H_b` that commutes with `z ↦ −z` and moves finitely many zeros. -/
theorem mem_forwardMonodromy_of_frequently_not_dvd {τ₀ : ℂ} (hτ₀ : 0 < τ₀.re)
    (hc : complexHeat τ₀ 0 ≠ 0)
    (hfreq : ∃ᶠ r : ℝ in 𝓝[>] 0, ¬ 8 ∣ {z : ℂ | complexHeat (τ₀ + (r : ℂ) ^ 2) z = 0 ∧
      ¬ Transports (turnPath τ₀ r) z z}.ncard)
    {w : Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite) :
    w ∈ forwardMonodromy b hb₀ hb := by
  by_contra hwG
  obtain ⟨ε, -, hlaw⟩ := exists_turn_parity_of_not_mem_forwardMonodromy hb₀ hb hw hfin hwG
  have hcen : IsCollision τ₀ 0 (2 * 0) :=
    ⟨fun i hi => absurd hi (by omega), by rw [iteratedDeriv_zero]; exact hc⟩
  obtain ⟨r, ⟨c, hc1, d, hd⟩, hnot⟩ := ((hlaw τ₀ hτ₀ 0 hcen).and_frequently hfreq).exists
  apply hnot
  rw [hc1]
  exact ⟨d, by omega⟩

/-- **Real times.** If for arbitrarily small `r` the turn of radius `r²` around a real time
`t > 0` moves a number of zeros not divisible by `8`, then `G₊(b)` contains every permutation of
the zeros of `H_b` that commutes with `z ↦ −z` and moves finitely many zeros. -/
theorem mem_forwardMonodromy_of_real_frequently_not_dvd {t : ℝ} (ht : 0 < t)
    (hfreq : ∃ᶠ r : ℝ in 𝓝[>] 0, ¬ 8 ∣ {z : ℂ | complexHeat ((t : ℂ) + (r : ℂ) ^ 2) z = 0 ∧
      ¬ Transports (turnPath (t : ℂ) r) z z}.ncard)
    {w : Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite) :
    w ∈ forwardMonodromy b hb₀ hb :=
  mem_forwardMonodromy_of_frequently_not_dvd hb₀ hb (by rw [Complex.ofReal_re]; exact ht)
    (complexHeat_ofReal_center_ne_zero t) hfreq hw hfin

end GaloisForLFunctions.GaloisTheoryOfZeros
