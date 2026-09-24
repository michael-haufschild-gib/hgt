import GaloisForLFunctions.RHTower.WeilKloostermanHasseDavenport

open Finset Polynomial

/-!
# Artin–Schreier counting for Kloosterman sums

For a finite field `E ⊇ 𝔽_p` (`p` odd) and `a ∈ 𝔽_p^×`:
* `v ↦ v^p - v` is additive with kernel `𝔽_p` and image the trace kernel of `E/𝔽_p`;
* `#{x ≠ 0 : x + b/x = u} = 1 + χ(u² - 4b)`;
* `Σ_{j ∈ 𝔽_p^×} K_E(j²a) = 1 + Σ_{v ∈ E} χ((v^p - v)² - 4a)`, where `K_E` is the Kloosterman sum over `E`
  and `χ` the quadratic character of `E`.
-/

namespace GaloisForLFunctions.RHTower.WeilKloosterman

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [DecidableEq B]

theorem card_fiber_eq_card_ker (f : A →+ B) {v0 : A} :
    (univ.filter (fun v => f v = f v0)).card = (univ.filter (fun v => f v = 0)).card := by
  apply Finset.card_bij (fun v _ => v - v0)
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [map_sub, hv, sub_self]
  · intro v _ w _ h; simpa using h
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨w + v0, ?_, by simp⟩
    simp [map_add, hw]

theorem sum_comp_eq_card_ker_mul {M : Type*} [AddCommMonoid M] (f : A →+ B) (g : B → M) :
    ∑ a : A, g (f a) = (univ.filter (fun v => f v = 0)).card • ∑ b ∈ univ.image f, g b := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := univ.image f)
    (fun a _ => Finset.mem_image_of_mem f (Finset.mem_univ a)), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨v0, -, rfl⟩ := Finset.mem_image.mp hb
  rw [Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.mp ha).2]), Finset.sum_const,
    card_fiber_eq_card_ker f]

theorem card_eq_card_ker_mul_card_image (f : A →+ B) :
    Fintype.card A = (univ.filter (fun v => f v = 0)).card * (univ.image f).card := by
  have := sum_comp_eq_card_ker_mul f (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at this
  exact this

variable {p : ℕ} [hp : Fact p.Prime] {E : Type*} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod p) E]

omit [Fintype E] [DecidableEq E] in
theorem charP_of_zmod : CharP E p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p

/-- The Artin–Schreier map `v ↦ v^p - v`. -/
noncomputable def asMap (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra (ZMod p) E] : E →+ E :=
  haveI := charP_of_zmod (p := p) (E := E)
  (frobenius E p).toAddMonoidHom - AddMonoidHom.id E

omit [Fintype E] [DecidableEq E] in
theorem asMap_apply (v : E) : asMap p E v = v ^ p - v := rfl

/-- The trace kernel of `E / 𝔽_p`. -/
noncomputable def trKer (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod p) E] : Finset E :=
  univ.filter (fun u => Algebra.trace (ZMod p) E u = 0)

theorem card_trKer_mul : (trKer p E).card * p = Fintype.card E := by
  have h := card_eq_card_ker_mul_card_image (Algebra.trace (ZMod p) E).toAddMonoidHom
  have himg : univ.image (Algebra.trace (ZMod p) E).toAddMonoidHom = univ := by
    apply Finset.eq_univ_of_forall
    intro y
    obtain ⟨x, hx⟩ := Algebra.trace_surjective (ZMod p) E y
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
  rw [himg, Finset.card_univ, ZMod.card] at h
  exact h.symm

omit [DecidableEq E] in
theorem trace_asMap (v : E) : Algebra.trace (ZMod p) E (asMap p E v) = 0 := by
  rw [asMap_apply, map_sub, sub_eq_zero]
  have h := Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) E) v
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] at h
  exact h

theorem card_ker_asMap : (univ.filter (fun v : E => asMap p E v = 0)).card = p := by
  have hp1 := hp.out.one_lt
  apply le_antisymm
  · have hne : (X ^ p - X : E[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero E hp1
    calc _ ≤ (X ^ p - X : E[X]).natDegree := by
          apply Polynomial.card_le_degree_of_subset_roots
          intro v hv
          rw [Finset.mem_val, Finset.mem_filter, asMap_apply] at hv
          rw [Polynomial.mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X]
          exact hv.2
      _ = p := FiniteField.X_pow_card_sub_X_natDegree_eq E hp1
  · calc p = (univ.image (algebraMap (ZMod p) E)).card := by
          rw [Finset.card_image_of_injective _ (algebraMap (ZMod p) E).injective, Finset.card_univ,
            ZMod.card]
      _ ≤ _ := by
          apply Finset.card_le_card
          intro v hv
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
          rw [Finset.mem_filter, asMap_apply, ← map_pow, ZMod.pow_card, sub_self]
          exact ⟨Finset.mem_univ _, rfl⟩

theorem image_asMap : univ.image (asMap p E) = trKer p E := by
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, trace_asMap v⟩
  · have h1 := card_eq_card_ker_mul_card_image (asMap p E)
    rw [card_ker_asMap, ← card_trKer_mul (p := p), mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_left hp.out.pos h1).le

/-- **Additive Hilbert 90 count.** Summing over `v^p - v` covers the trace kernel exactly `p` times. -/
theorem sum_asMap {M : Type*} [AddCommMonoid M] (g : E → M) :
    ∑ v : E, g (v ^ p - v) = p • ∑ u ∈ trKer p E, g u := by
  have h := sum_comp_eq_card_ker_mul (asMap p E) g
  rw [card_ker_asMap, image_asMap] at h
  exact h

omit [Fintype E] [DecidableEq E] in
theorem ringChar_ne_two (hp2 : p ≠ 2) : ringChar E ≠ 2 := by
  haveI := charP_of_zmod (p := p) (E := E)
  rw [ringChar.eq E p]; exact hp2

/-- Solutions of `x + b/x = u` correspond to square roots of `u² - 4b`. -/
theorem card_fiber_quadratic (hp2 : p ≠ 2) {b : E} (hb : b ≠ 0) (u : E) :
    ((univ.filter (fun x : E => x ≠ 0 ∧ x + b * x⁻¹ = u)).card : ℤ) =
      1 + quadraticChar E (u ^ 2 - 4 * b) := by
  have h2 : (2 : E) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two (p := p) hp2)
  rw [add_comm, ← quadraticChar_card_sqrts (ringChar_ne_two (p := p) hp2)]
  congr 1
  apply Finset.card_bij (fun x _ => 2 * x - u)
  · intro x hx
    obtain ⟨-, hx0, hxu⟩ := Finset.mem_filter.mp hx
    rw [Set.mem_toFinset, Set.mem_setOf_eq]
    have h1 : b = (u - x) * x := by
      rw [← hxu, add_sub_cancel_left, inv_mul_cancel_right₀ hx0]
    linear_combination (4 : E) * h1
  · intro x _ y _ h
    have : 2 * x = 2 * y := by linear_combination h
    exact mul_left_cancel₀ h2 this
  · intro y hy
    rw [Set.mem_toFinset, Set.mem_setOf_eq] at hy
    have hx0 : (y + u) / 2 ≠ 0 := by
      intro h
      have hyu : y = -u := by
        have := (div_eq_zero_iff.mp h).resolve_right h2
        linear_combination this
      apply hb
      have h4 : (4 : E) ≠ 0 := by
        have : (4 : E) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      have : 4 * b = 0 := by rw [hyu] at hy; linear_combination hy
      exact (mul_eq_zero.mp this).resolve_left h4
    refine ⟨(y + u) / 2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0, ?_⟩, ?_⟩
    · have hb' : b = (u - (y + u) / 2) * ((y + u) / 2) := by
        field_simp
        linear_combination hy
      rw [hb', mul_assoc, mul_inv_cancel₀ hx0, mul_one]
      ring
    · field_simp
      ring

/-- Points with `Tr(x + b/x) = 0`, grouped by the value `x + b/x`. -/
theorem card_trace_zero (hp2 : p ≠ 2) {b : E} (hb : b ≠ 0) :
    (p : ℤ) * (univ.filter (fun x : E => x ≠ 0 ∧
        Algebra.trace (ZMod p) E (x + b * x⁻¹) = 0)).card =
      Fintype.card E + ∑ v : E, (quadraticChar E ((v ^ p - v) ^ 2 - 4 * b) : ℤ) := by
  have hfib : (univ.filter (fun x : E => x ≠ 0 ∧ Algebra.trace (ZMod p) E (x + b * x⁻¹) = 0)).card =
      ∑ u ∈ trKer p E, (univ.filter (fun x : E => x ≠ 0 ∧ x + b * x⁻¹ = u)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x + b * x⁻¹) (t := trKer p E)]
    · apply Finset.sum_congr rfl
      intro u _
      rw [Finset.filter_filter]
      congr 1
      rename_i hu
      have hu' := (Finset.mem_filter.mp hu).2
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h0, -⟩, h⟩; exact ⟨h0, h⟩
      · rintro ⟨h0, h⟩; exact ⟨⟨h0, h ▸ hu'⟩, h⟩
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.2⟩
  rw [hfib, Nat.cast_sum, Finset.mul_sum]
  have hs := sum_asMap (p := p) (E := E) (fun u => (1 + quadraticChar E (u ^ 2 - 4 * b) : ℤ))
  rw [nsmul_eq_mul] at hs
  simp_rw [card_fiber_quadratic hp2 hb]
  rw [← Finset.mul_sum, ← hs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]


variable (ψ : AddChar (ZMod p) ℂ)

/-- Orthogonality over the prime field detects the trace kernel. -/
theorem sum_twist_char (hψ : ψ.IsPrimitive) (b : E) :
    ∑ j : ZMod p, ∑ x : E, (if x = 0 then 0 else ψ (j * Algebra.trace (ZMod p) E (x + b * x⁻¹))) =
      (p : ℂ) * (univ.filter (fun x : E => x ≠ 0 ∧
        Algebra.trace (ZMod p) E (x + b * x⁻¹) = 0)).card := by
  rw [Finset.sum_comm]
  have hx : ∀ x : E, (∑ j : ZMod p, (if x = 0 then 0 else ψ (j * Algebra.trace (ZMod p) E (x + b * x⁻¹)))) =
      if x ≠ 0 ∧ Algebra.trace (ZMod p) E (x + b * x⁻¹) = 0 then (p : ℂ) else 0 := by
    intro x
    by_cases h0 : x = 0
    · simp [h0]
    · rw [Finset.sum_congr rfl (fun j _ => if_neg h0), AddChar.sum_mulShift _ hψ, ZMod.card]
      simp [h0]
  rw [Finset.sum_congr rfl (fun x _ => hx x), ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    mul_comm]

/-- Twisting by `j ∈ 𝔽_p^×` rescales the Kloosterman parameter by `j²`. -/
theorem twist_eq_extKloosterman (j : ZMod p) (hj : j ≠ 0) (a : ZMod p) :
    ∑ x : E, (if x = 0 then 0 else
        ψ (j * Algebra.trace (ZMod p) E (x + algebraMap (ZMod p) E a * x⁻¹))) =
      extKloosterman (E := E) ψ (j ^ 2 * a) := by
  set c := algebraMap (ZMod p) E j
  have hc : c ≠ 0 := (map_ne_zero_iff _ (algebraMap (ZMod p) E).injective).mpr hj
  rw [extKloosterman]
  apply Fintype.sum_equiv (Equiv.mulLeft₀ c hc)
  intro x
  rw [show (Equiv.mulLeft₀ c hc) x = c * x from rfl]
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx, if_neg (mul_ne_zero hc hx)]
    congr 1
    rw [← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def]
    congr 1
    rw [map_mul, map_pow]
    field_simp
    simp only [c]
    ring

/-- **Artin–Schreier identity.** `Σ_{j ∈ 𝔽_p^×} K_E(j²a) = 1 + Σ_{v ∈ E} χ((v^p - v)² - 4a)`. -/
theorem sum_extKloosterman_twists (hp2 : p ≠ 2) (hψ : ψ.IsPrimitive) {a : ZMod p} (ha : a ≠ 0) :
    ∑ j ∈ univ.erase (0 : ZMod p), extKloosterman (E := E) ψ (j ^ 2 * a) =
      1 + ∑ v : E, (quadraticChar E ((v ^ p - v) ^ 2 - 4 * algebraMap (ZMod p) E a) : ℂ) := by
  have hb : algebraMap (ZMod p) E a ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (ZMod p) E).injective).mpr ha
  have h1 := sum_twist_char ψ hψ (algebraMap (ZMod p) E a)
  have h2 := card_trace_zero (p := p) hp2 hb
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)] at h1
  have h0 : ∑ x : E, (if x = 0 then 0 else
      ψ ((0 : ZMod p) * Algebra.trace (ZMod p) E (x + algebraMap (ZMod p) E a * x⁻¹))) =
      (Fintype.card E : ℂ) - 1 := by
    simp only [zero_mul, AddChar.map_zero_eq_one]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.filter_ne' univ (0 : E), Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos]
    simp
  rw [h0, Finset.sum_congr rfl (fun j hj => twist_eq_extKloosterman ψ j (Finset.ne_of_mem_erase hj) a)]
    at h1
  have h2c : (p : ℂ) * ((univ.filter (fun x : E => x ≠ 0 ∧
      Algebra.trace (ZMod p) E (x + algebraMap (ZMod p) E a * x⁻¹) = 0)).card : ℂ) =
      Fintype.card E + ∑ v : E, (quadraticChar E ((v ^ p - v) ^ 2 - 4 * algebraMap (ZMod p) E a) : ℂ) := by
    exact_mod_cast h2
  rw [h2c] at h1
  linear_combination h1

end GaloisForLFunctions.RHTower.WeilKloosterman
