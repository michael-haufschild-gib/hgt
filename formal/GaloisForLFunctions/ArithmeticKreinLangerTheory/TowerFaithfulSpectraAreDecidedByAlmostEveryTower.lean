import GaloisForLFunctions.ArithmeticKreinLangerTheory.CyclicSubgroupsDecideTheKreinLangerClass
import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# Tower-faithful spectra are decided by almost every tower

Fix a family of **towers**: elements `u_t` of a group, indexed by `t ∈ T` (for `ℚ_{>0}` the primes).
Positivity on the cyclic subgroups `⟨u_t⟩` of a fixed family is a weaker datum than positivity on all
cyclic subgroups; it decides the index exactly when the spectrum is faithful to the family.

**Tower-faithful spectra** (`IsTowerFaithful`). Every character is non-unitary at all but finitely
many towers, and two distinct nodes agree at only finitely many towers.

**Tower Hasse principle** (`finite_towers_negIndex_ne`, `negIndex_eq_zero_of_posDef_on_infinitely_many`).
For a tower-faithful spectrum all but finitely many towers separate the pairs, so each of them
carries the whole index `κ`; positivity on infinitely many towers forces `κ = 0`.

**Necessity** (`unitary_tower_defeat`, `aliased_tower_defeat`). The two clauses are sharp. A
non-unitary character unitary on a set `S` of towers carries the pair `h_{χ,i}`, of index one,
invisible on every tower of `S`. Two pairs whose nodes agree on `S` carry `h_{χ_a,1} + h_{χ_b,−1}`,
invisible on `S`, with a negative square on some cyclic subgroup.

**Logarithmic spectra are tower-faithful** (`isTowerFaithful_logChar`). For `χ_s(u) = e^{s ℓ(u)}`,
`Re s ≠ 0`, the modulus `e^{Re s · ℓ(u_t)}` is never `1` at a tower of nonzero scale, and two distinct
exponents agree at two towers only if the scales are commensurable. On `ℚ_{>0}` with the prime towers
(`negIndex_eq_zero_of_posDef_on_infinitely_many_primes`): any finite family of exponents with
nonzero real parts and distinct nodes is decided by infinitely many primes. This is the arithmetic
property behind the two-prime law: one real logarithm reads every character.
-/

open Complex Finset
open scoped ComplexConjugate Real
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

variable {G : Type*} [Group G] {T : Type*} {κ : ℕ}

/-! ### Tower-faithful spectra -/

/-- A spectrum is **tower-faithful** for the towers `u`: every character is non-unitary at all but
finitely many towers, and distinct nodes agree at finitely many towers. -/
def IsTowerFaithful (χ : Fin κ → G →* ℂ) (u : T → G) : Prop :=
  (∀ j, {t | ‖χ j (u t)‖ = 1}.Finite) ∧
    ∀ m m', m ≠ m' → {t | node χ m (u t) = node χ m' (u t)}.Finite

theorem nodes_eq_node (χ : Fin κ → G →* ℂ) (g : G) : nodes χ g = fun m => node χ m g := by
  funext m; rcases m with j | j <;> rfl

/-- The towers that fail to separate the pairs. -/
def unseparated (χ : Fin κ → G →* ℂ) (u : T → G) : Set T :=
  {t | ¬ ((∀ j, ‖χ j (u t)‖ ≠ 1) ∧ Function.Injective (nodes χ (u t)))}

theorem IsTowerFaithful.finite_unseparated {χ : Fin κ → G →* ℂ} {u : T → G}
    (hF : IsTowerFaithful χ u) : (unseparated χ u).Finite := by
  refine ((Set.finite_iUnion hF.1).union (Set.finite_iUnion fun m : Fin κ ⊕ Fin κ =>
    Set.finite_iUnion fun m' : {m' // m' ≠ m} => hF.2 m m' m'.2.symm)).subset fun t ht => ?_
  simp only [unseparated, Set.mem_setOf_eq, not_and_or, not_forall, not_not] at ht
  rcases ht with ⟨j, hj⟩ | hinj
  · exact Or.inl (Set.mem_iUnion.mpr ⟨j, hj⟩)
  · rw [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨m, m', he, hne⟩ := hinj
    refine Or.inr (Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨⟨m', fun h => hne h.symm⟩, ?_⟩⟩)
    simpa [nodes_eq_node] using he

/-! ### The tower Hasse principle -/

/-- **All but finitely many towers carry the whole index** of a tower-faithful Krein–Langer kernel. -/
theorem finite_towers_negIndex_ne {p : G → ℂ} (hp : IsPosDefKernel p) (χ : Fin κ → G →* ℂ)
    (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : T → G) (hF : IsTowerFaithful χ u) :
    {t | negIndex ((fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) ∘ zpowersHom G (u t)) ≠ κ}.Finite :=
  hF.finite_unseparated.subset fun t ht hsep =>
    ht (negIndex_zpowers_eq_of_separated hp χ ω hω (u t) hsep.1 hsep.2)

/-- With infinitely many towers, a tower-faithful kernel has index exactly `κ`. -/
theorem negIndex_eq_of_isTowerFaithful [Infinite T] {p : G → ℂ} (hp : IsPosDefKernel p)
    (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : T → G)
    (hF : IsTowerFaithful χ u) :
    negIndex (fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) = κ := by
  obtain ⟨t, ht⟩ := (Set.infinite_univ.sdiff hF.finite_unseparated).nonempty
  have hsep : (∀ j, ‖χ j (u t)‖ ≠ 1) ∧ Function.Injective (nodes χ (u t)) :=
    not_not.mp ht.2
  exact negIndex_add_sum_pairKernel_eq hp χ ω hω (u t) hsep.1 hsep.2

/-- **The tower Hasse principle.** A tower-faithful Krein–Langer kernel positive definite on
infinitely many towers has no pair. -/
theorem negIndex_eq_zero_of_posDef_on_infinitely_many {p : G → ℂ} (hp : IsPosDefKernel p)
    (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : T → G)
    (hF : IsTowerFaithful χ u)
    (h : {t | negIndex ((fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) ∘
      zpowersHom G (u t)) = 0}.Infinite) :
    κ = 0 ∧ negIndex (fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) = 0 := by
  obtain ⟨t, ht0, htκ⟩ := (h.sdiff (finite_towers_negIndex_ne hp χ ω hω u hF)).nonempty
  have hκ : (κ : ℕ∞) = 0 := (not_not.mp htκ).symm.trans ht0
  have hκ0 : κ = 0 := by exact_mod_cast hκ
  refine ⟨hκ0, ?_⟩
  subst hκ0
  have : (fun g => p g + ∑ j : Fin 0, pairKernel (χ j) (ω j) g) = p := by funext g; simp
  rw [this]; exact hp.negIndex_eq_zero

/-! ### Necessity of the two clauses -/

/-- **A unitary restriction hides a pair.** A non-unitary character with purely imaginary weight
has index one, and vanishes on every tower where the character is unitary. -/
theorem unitary_tower_defeat {χ : G →* ℂ} (hχ : ¬ IsUnitaryChar χ) (u : T → G) :
    negIndex (pairKernel χ I) = 1 ∧
      ∀ t, ‖χ (u t)‖ = 1 → negIndex (pairKernel χ I ∘ zpowersHom G (u t)) = 0 := by
  refine ⟨?_, fun t ht => ?_⟩
  · have := negIndex_add_pairKernel_eq_one isPosDefKernel_zero hχ I_ne_zero
    simpa using this
  · have hz : pairKernel χ I ∘ zpowersHom G (u t) = 0 := by
      funext n
      have hu : IsUnitaryChar (valChar (χ (u t))) := fun n => by
        simp only [valChar, if_neg (map_ne_zero χ (u t)), MonoidHom.coe_mk, OneHom.coe_mk,
          norm_zpow, ht, one_zpow]
      rw [pairKernel_comp, comp_zpowersHom, pairKernel, reflectChar_eq_of_unitary hu,
        Complex.conj_I]
      simp
    rw [hz]; exact isPosDefKernel_zero.negIndex_eq_zero

/-- **Aliasing hides two pairs.** If two characters with distinct non-unitary nodes agree on a set
`S` of towers, the kernel `h_{χ_a,1} + h_{χ_b,−1}` vanishes on every tower of `S` and has a negative
square on some cyclic subgroup. -/
theorem aliased_tower_defeat (χ : Fin 2 → G →* ℂ) (hU : ∀ j, ¬ IsUnitaryChar (χ j))
    (hD : Function.Injective (node χ)) (u : T → G) :
    1 ≤ negIndex (fun g => (0 : G → ℂ) g + ∑ j, pairKernel (χ j) (![1, -1] j) g) ∧
      ∀ t, χ 0 (u t) = χ 1 (u t) →
        negIndex ((fun g => (0 : G → ℂ) g + ∑ j, pairKernel (χ j) (![1, -1] j) g) ∘
          zpowersHom G (u t)) = 0 := by
  refine ⟨?_, fun t ht => ?_⟩
  · obtain ⟨v, hv⟩ := exists_one_le_negIndex_zpowers isPosDefKernel_zero χ ![1, -1]
      (fun j => by fin_cases j <;> simp) hU hD 0
    exact hv.trans (negIndex_comp_le _ _)
  · have hz : (fun g => (0 : G → ℂ) g + ∑ j, pairKernel (χ j) (![1, -1] j) g) ∘
        zpowersHom G (u t) = 0 := by
      funext n
      simp only [Function.comp_apply, Pi.zero_apply, zero_add, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← Function.comp_apply (f := pairKernel (χ 0) 1), pairKernel_comp, comp_zpowersHom,
        ← Function.comp_apply (f := pairKernel (χ 1) (-1)), pairKernel_comp, comp_zpowersHom, ht]
      simp only [pairKernel, map_one, map_neg, one_mul, neg_mul]
      ring
    rw [hz]; exact isPosDefKernel_zero.negIndex_eq_zero

/-! ### Logarithmic spectra -/

/-- The exponents of the nodes of a logarithmic spectrum: `s_j` and `−s̄_j`. -/
def nodeExp (s : Fin κ → ℂ) : Fin κ ⊕ Fin κ → ℂ := Sum.elim s fun j => -conj (s j)

theorem node_logChar (ℓ : G →* Multiplicative ℝ) (s : Fin κ → ℂ) (m : Fin κ ⊕ Fin κ) :
    node (fun j => logChar ℓ (s j)) m = logChar ℓ (nodeExp s m) := by
  rcases m with j | j
  · rfl
  · exact reflectChar_logChar ℓ (s j)

/-- **Logarithmic spectra are tower-faithful.** For exponents with nonzero real parts and distinct
node exponents, and towers with nonzero, pairwise incommensurable scales, no character is unitary
at any tower and two distinct nodes agree at most at one tower. -/
theorem isTowerFaithful_logChar (ℓ : G →* Multiplicative ℝ) (s : Fin κ → ℂ)
    (hre : ∀ j, (s j).re ≠ 0) (hs : Function.Injective (nodeExp s)) (u : T → G)
    (hL0 : ∀ t, scale ℓ (u t) ≠ 0)
    (hL : ∀ t t', t ≠ t' → ∀ a b : ℤ, (a : ℝ) * scale ℓ (u t) = b * scale ℓ (u t') → a = 0) :
    IsTowerFaithful (fun j => logChar ℓ (s j)) u := by
  refine ⟨fun j => Set.Finite.subset Set.finite_empty fun t ht => ?_, fun m m' hmm' => ?_⟩
  · simp only [Set.mem_setOf_eq, norm_logChar, Real.exp_eq_one_iff, mul_eq_zero] at ht
    exact absurd ht (not_or.mpr ⟨hre j, hL0 t⟩)
  · refine Set.Subsingleton.finite fun t ht t' ht' => ?_
    by_contra htt
    simp only [Set.mem_setOf_eq, node_logChar, logChar_apply] at ht ht'
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp ht
    obtain ⟨n', hn'⟩ := Complex.exp_eq_exp_iff_exists_int.mp ht'
    set d := nodeExp s m - nodeExp s m' with hd
    have hd0 : d ≠ 0 := sub_ne_zero.mpr (fun h => hmm' (hs h))
    have h1 : d * scale ℓ (u t) = n * (2 * π * I) := by rw [hd, sub_mul, hn]; ring
    have h2 : d * scale ℓ (u t') = n' * (2 * π * I) := by rw [hd, sub_mul, hn']; ring
    have hrel : ((n' : ℝ) * scale ℓ (u t) : ℂ) = ((n : ℝ) * scale ℓ (u t') : ℂ) := by
      apply mul_left_cancel₀ (show (2 * π * I : ℂ) ≠ 0 by simp [Real.pi_ne_zero, I_ne_zero])
      push_cast
      calc 2 * π * I * (n' * scale ℓ (u t)) = (n' * (2 * π * I)) * scale ℓ (u t) := by ring
        _ = d * scale ℓ (u t') * scale ℓ (u t) := by rw [h2]
        _ = (n * (2 * π * I)) * scale ℓ (u t') := by rw [mul_right_comm, h1]
        _ = 2 * π * I * (n * scale ℓ (u t')) := by ring
    have hn'0 := hL t t' htt n' n (by exact_mod_cast hrel)
    rw [hn'0, Int.cast_zero, zero_mul, mul_eq_zero] at h2
    exact h2.elim hd0 (by exact_mod_cast hL0 t')

/-! ### The Hecke lattice and the prime towers -/

/-- Distinct primes have incommensurable logarithms. -/
theorem prime_scales_incommensurable {p q : Nat.Primes} (hpq : p ≠ q) (a b : ℤ)
    (h : (a : ℝ) * Real.log p = b * Real.log q) : a = 0 := by
  by_contra ha
  have hp := Real.log_pos (by exact_mod_cast p.2.one_lt : (1 : ℝ) < p)
  have hq := Real.log_pos (by exact_mod_cast q.2.one_lt : (1 : ℝ) < q)
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul, mul_eq_zero, Int.cast_eq_zero] at h
    exact h.elim ha hp.ne'
  exact RHTower.irrational_log_ratio p.2 q.2 (fun h' => hpq (Subtype.ext h'))
    ⟨(a : ℚ) / b, by
      push_cast
      field_simp
      linarith⟩

/-- **The arithmetic tower Hasse principle.** On `ℚ_{>0}`, a positive-definite kernel plus pairs
of logarithmic characters `u ↦ u^{s_j}` with nonzero real parts and distinct node exponents, positive
definite on infinitely many prime towers, has no pair. -/
theorem negIndex_eq_zero_of_posDef_on_infinitely_many_primes {p : HeckeLattice → ℂ}
    (hp : IsPosDefKernel p) (s : Fin κ → ℂ) (hre : ∀ j, (s j).re ≠ 0)
    (hs : Function.Injective (nodeExp s)) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0)
    (h : {q : Nat.Primes | negIndex ((fun g => p g + ∑ j,
      pairKernel (logChar heckeLogScale (s j)) (ω j) g) ∘ zpowersHom _ (primeElt q.2)) = 0}.Infinite) :
    κ = 0 :=
  (negIndex_eq_zero_of_posDef_on_infinitely_many hp _ ω hω (fun q : Nat.Primes => primeElt q.2)
    (isTowerFaithful_logChar heckeLogScale s hre hs _
      (fun q => by rw [scale_primeElt]; exact (Real.log_pos (by exact_mod_cast q.2.one_lt)).ne')
      fun q q' hqq' a b hab => prime_scales_incommensurable hqq' a b
        (by rwa [scale_primeElt, scale_primeElt] at hab)) h).1

end GaloisForLFunctions.ArithmeticKreinLangerTheory
