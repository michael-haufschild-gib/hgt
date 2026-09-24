import GaloisForLFunctions.RHTower.WeilKloostermanArtinSchreier
import GaloisForLFunctions.RHTower.StepanovCharacterSum

/-!
# Weil's bound for Kloosterman sums

For an odd prime `p`, a primitive additive character `ψ` of `𝔽_p` and `a ∈ 𝔽_p^×`,
`|Σ_{x ∈ 𝔽_p^×} ψ(x + a/x)| ≤ 2√p` (`kloosterman_weil_bound`).

Proof. Over `E = 𝔽_{p^{2m}}` the Artin–Schreier identity gives
`Σ_{j ∈ 𝔽_p^×} K_E(j²a) = 1 + Σ_{v ∈ E} χ(h(v))` with `h = (X^p - X)² - 4a` squarefree of degree `2p`.
Stepanov's bound gives `|Σ_v χ(h(v))| ≤ (4p + 2)p^m + 2p`, and Hasse–Davenport gives
`K_E(j²a) = -(α_j^{2m} + β_j^{2m})` with `α_j β_j = p`. The power sums of the family `α_j², β_j²` are
therefore `O(p^m)`, which forces `|α_j|² ≤ p` (`norm_le_of_power_sums_bound`). With `j = 1`,
`|K(a)| = |α_1 + β_1| ≤ 2√p`.
-/

open Polynomial Finset Filter Topology

namespace GaloisForLFunctions.RHTower.WeilKloosterman

section AsDisc

variable {E : Type*} [Field E] {p : ℕ} [Fact p.Prime] [CharP E p]

/-- The Artin–Schreier discriminant polynomial `h(v) = (v^p - v)² - 4a`. -/
noncomputable def asDisc (p : ℕ) (a : E) : E[X] := (X ^ p - X) ^ 2 - C (4 * a)

omit [Fact p.Prime] in
theorem derivative_X_pow_sub_X : derivative (X ^ p - X : E[X]) = -1 := by
  rw [derivative_sub, derivative_X_pow, derivative_X]
  simp

theorem asDisc_separable (hp2 : p ≠ 2) {a : E} (ha : a ≠ 0) : (asDisc p a).Separable := by
  have h2 : (2 : E) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff E p 2).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
  have h4a : (4 * a : E) ≠ 0 := mul_ne_zero (by
    have : (4 : E) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2) ha
  unfold asDisc Separable
  set A : E[X] := X ^ p - X
  have hd : derivative (A ^ 2 - C (4 * a)) = -(C 2 * A) := by
    rw [derivative_sub, derivative_C, sub_zero, derivative_sq, derivative_X_pow_sub_X]
    ring
  rw [hd]
  refine ⟨C (-(4 * a)⁻¹), C (-((4 * a)⁻¹ * 2⁻¹)) * A, ?_⟩
  have e1 : C (-((4 * a)⁻¹ * 2⁻¹)) * A * -(C 2 * A) = C ((4 * a)⁻¹) * A ^ 2 := by
    rw [C_neg, C_mul]
    have : C (2⁻¹ : E) * C 2 = 1 := by rw [← C_mul, inv_mul_cancel₀ h2, C_1]
    linear_combination (C ((4 * a)⁻¹)) * A ^ 2 * this
  rw [e1]
  have : C ((4 * a)⁻¹) * C (4 * a) = (1 : E[X]) := by rw [← C_mul, inv_mul_cancel₀ h4a, C_1]
  rw [C_neg]
  linear_combination this

theorem asDisc_squarefree (hp2 : p ≠ 2) {a : E} (ha : a ≠ 0) : Squarefree (asDisc p a) :=
  (asDisc_separable hp2 ha).squarefree

omit [CharP E p] in
theorem asDisc_natDegree (a : E) : (asDisc p a).natDegree = 2 * p := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hA : (X ^ p - X : E[X]).natDegree = p := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hp1]
  unfold asDisc
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · rw [natDegree_pow, hA, mul_comm]
  · rw [natDegree_C, natDegree_pow, hA]; omega


end AsDisc

section Elimination

/-- Base case: `|a| |w|^m ≤ C ρ^m` for all large `m` with `a ≠ 0` forces `|w| ≤ ρ`. -/
theorem norm_le_of_pow_bound {a w : ℂ} {C ρ : ℝ} {m0 : ℕ} (ha : a ≠ 0) (hρ : 0 ≤ ρ)
    (h : ∀ m, m0 ≤ m → ‖a‖ * ‖w‖ ^ m ≤ C * ρ ^ m) : ‖w‖ ≤ ρ := by
  by_contra hlt
  push Not at hlt
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rcases eq_or_lt_of_le hρ with hρ0 | hρ0
  · -- ρ = 0
    have := h (m0 + 1) (by omega)
    rw [← hρ0, zero_pow (by omega), mul_zero] at this
    have hw : 0 < ‖w‖ ^ (m0 + 1) := pow_pos (hρ0 ▸ hlt) _
    nlinarith
  · have hr : 1 < ‖w‖ / ρ := by rw [one_lt_div hρ0]; exact hlt
    have ht := tendsto_pow_atTop_atTop_of_one_lt hr
    obtain ⟨m, hm1, hm2⟩ := ((ht.eventually (eventually_gt_atTop (C / ‖a‖))).and
      (eventually_ge_atTop m0)).exists
    have hb := h m hm2
    have : (‖w‖ / ρ) ^ m * ρ ^ m = ‖w‖ ^ m := by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hρ0.ne')]
    have hpos : 0 < ρ ^ m := pow_pos hρ0 m
    have : C < ‖a‖ * (‖w‖ / ρ) ^ m := by rwa [div_lt_iff₀' ha'] at hm1
    nlinarith

/-- **Elimination lemma.** If `|Σ_{v∈S} a_v v^m| ≤ C ρ^m` for all `m ≥ m0` (distinct `v`), then every
`w ∈ S` with `a_w ≠ 0` satisfies `|w| ≤ ρ`. -/
theorem norm_le_of_sum_pow_bound (S : Finset ℂ) :
    ∀ (a : ℂ → ℂ) (C : ℝ) (m0 : ℕ) (ρ : ℝ), 0 ≤ ρ →
      (∀ m, m0 ≤ m → ‖∑ v ∈ S, a v * v ^ m‖ ≤ C * ρ ^ m) →
      ∀ w ∈ S, a w ≠ 0 → ‖w‖ ≤ ρ := by
  induction S using Finset.strongInduction with
  | H S ih =>
    intro a C m0 ρ hρ hS w hw haw
    by_cases hsingle : S = {w}
    · subst hsingle
      apply norm_le_of_pow_bound haw hρ (m0 := m0) (C := C)
      intro m hm
      have := hS m hm
      simpa [norm_mul, norm_pow] using this
    · -- eliminate another element `u`
      obtain ⟨u, hu, huw⟩ : ∃ u ∈ S, u ≠ w := by
        by_contra hcon; push Not at hcon
        apply hsingle
        ext x; simp only [Finset.mem_singleton]
        exact ⟨fun hx => hcon x hx, fun hx => hx ▸ hw⟩
      set b : ℂ → ℂ := fun v => a v * (v - u)
      have hsub : S.erase u ⊂ S := Finset.erase_ssubset hu
      have hbound : ∀ m, m0 ≤ m →
          ‖∑ v ∈ S.erase u, b v * v ^ m‖ ≤ (C * ρ + ‖u‖ * C) * ρ ^ m := by
        intro m hm
        have hid : (∑ v ∈ S.erase u, b v * v ^ m) =
            (∑ v ∈ S, a v * v ^ (m + 1)) - u * ∑ v ∈ S, a v * v ^ m := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_erase_add _ _ hu]
          simp only [b]
          rw [show a u * u ^ (m + 1) - u * (a u * u ^ m) = 0 by ring, add_zero]
          apply Finset.sum_congr rfl; intro v _; ring
        rw [hid]
        calc ‖(∑ v ∈ S, a v * v ^ (m + 1)) - u * ∑ v ∈ S, a v * v ^ m‖
            ≤ ‖∑ v ∈ S, a v * v ^ (m + 1)‖ + ‖u‖ * ‖∑ v ∈ S, a v * v ^ m‖ := by
              rw [← norm_mul]; exact norm_sub_le _ _
          _ ≤ C * ρ ^ (m + 1) + ‖u‖ * (C * ρ ^ m) := by
              gcongr
              · exact hS (m + 1) (by omega)
              · exact hS m hm
          _ = (C * ρ + ‖u‖ * C) * ρ ^ m := by ring
      exact ih (S.erase u) hsub b _ m0 ρ hρ hbound w (Finset.mem_erase.mpr ⟨huw.symm, hw⟩)
        (mul_ne_zero haw (sub_ne_zero.mpr huw.symm))

/-- Indexed version: if the power sums of a finite family are `O(ρ^m)`, every member has modulus `≤ ρ`. -/
theorem norm_le_of_power_sums_bound {ι : Type*} (I : Finset ι) (z : ι → ℂ) {C ρ : ℝ} {m0 : ℕ}
    (hρ : 0 ≤ ρ) (h : ∀ m, m0 ≤ m → ‖∑ i ∈ I, z i ^ m‖ ≤ C * ρ ^ m) :
    ∀ i ∈ I, ‖z i‖ ≤ ρ := by
  classical
  intro i hi
  set S := I.image z
  set a : ℂ → ℂ := fun v => ((I.filter (fun j => z j = v)).card : ℂ)
  have hsum : ∀ m, (∑ j ∈ I, z j ^ m) = ∑ v ∈ S, a v * v ^ m := by
    intro m
    rw [← Finset.sum_fiberwise_of_maps_to (g := z) (t := S) (fun j hj => Finset.mem_image_of_mem z hj)]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.sum_const,
      nsmul_eq_mul]
  have ha : a (z i) ≠ 0 := by
    simp only [a, Nat.cast_ne_zero, ne_eq, Finset.card_eq_zero]
    exact Finset.nonempty_iff_ne_empty.mp ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  exact norm_le_of_sum_pow_bound S a C m0 ρ hρ (fun m hm => by rw [← hsum]; exact h m hm) (z i)
    (Finset.mem_image_of_mem z hi) ha


end Elimination

section Bound

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem asDisc_eval {E : Type*} [Field E] (b v : E) :
    (asDisc p b).eval v = (v ^ p - v) ^ 2 - 4 * b := by
  simp [asDisc]

/-- Power sums of the Frobenius eigenvalues over `𝔽_{p^{2m}}`, `m ≥ 3`, are `O(p^m)`. -/
theorem power_sums_bound (hp2 : p ≠ 2) (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) {a : ZMod p}
    (ha : a ≠ 0) (α β : ZMod p → ℂ)
    (hE : ∀ j ∈ univ.erase (0 : ZMod p), ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
      extKloosterman (E := E) ψ (j ^ 2 * a) =
        -(α j ^ Module.finrank (ZMod p) E + β j ^ Module.finrank (ZMod p) E))
    (m : ℕ) (hm : 3 ≤ m) :
    ‖∑ j ∈ univ.erase (0 : ZMod p), ((α j ^ 2) ^ m + (β j ^ 2) ^ m)‖ ≤
      (6 * p + 3 : ℝ) * (p : ℝ) ^ m := by
  classical
  have hp1 := hp.out.one_lt
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  let E := GaloisField p (2 * m)
  letI : Fintype E := Fintype.ofFinite E
  have h2m : 2 * m ≠ 0 := by omega
  have hfin : Module.finrank (ZMod p) E = 2 * m := GaloisField.finrank p h2m
  have hcard : Fintype.card E = p ^ (2 * m) := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p (2 * m) h2m
  have hid := sum_extKloosterman_twists (E := E) ψ hp2 hψ ha
  rw [Finset.sum_congr rfl (fun j hj => hE j hj E), hfin] at hid
  set b := algebraMap (ZMod p) E a
  have hb : b ≠ 0 := (map_ne_zero_iff _ (algebraMap (ZMod p) E).injective).mpr ha
  haveI : CharP E p := charP_of_zmod
  -- Stepanov
  have hodd : Odd (p ^ (2 * m)) := (hp.out.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨N, hN⟩ := hodd
  have hsD : (asDisc p b).natDegree + 5 ≤ p ^ m := by
    rw [asDisc_natDegree]
    calc 2 * p + 5 ≤ p ^ 3 := by
          have : 9 * p ≤ p ^ 3 := by
            rw [pow_succ, pow_two]
            exact Nat.mul_le_mul_right p (Nat.mul_le_mul hp3 hp3)
          omega
      _ ≤ p ^ m := Nat.pow_le_pow_right hp.out.pos hm
  have hst := Stepanov.abs_sum_quadraticChar_le (p := p) (n := 2 * m) hcard (asDisc_squarefree hp2 hb)
    (by rw [asDisc_natDegree]; omega) (N := N) (s := p ^ m) (by omega) (by ring) hsD
  rw [asDisc_natDegree] at hst
  simp_rw [asDisc_eval] at hst
  -- combine
  have hsum : ∑ j ∈ univ.erase (0 : ZMod p), ((α j ^ 2) ^ m + (β j ^ 2) ^ m) =
      -(1 + ∑ v : E, (quadraticChar E ((v ^ p - v) ^ 2 - 4 * b) : ℂ)) := by
    rw [← hid, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [neg_neg, ← pow_mul, ← pow_mul, mul_comm 2 m]
  rw [hsum, norm_neg]
  have hcast : ∑ v : E, (quadraticChar E ((v ^ p - v) ^ 2 - 4 * b) : ℂ) =
      ((∑ v : E, (quadraticChar E ((v ^ p - v) ^ 2 - 4 * b) : ℤ) : ℤ) : ℂ) := by
    push_cast; rfl
  rw [hcast]
  set S : ℤ := ∑ v : E, (quadraticChar E ((v ^ p - v) ^ 2 - 4 * b) : ℤ)
  have hS : |(S : ℝ)| ≤ 2 * (2 * p + 1) * (p : ℝ) ^ m + 2 * p := by exact_mod_cast hst
  have hpm : (1 : ℝ) ≤ (p : ℝ) ^ m := one_le_pow₀ (by exact_mod_cast hp.out.one_lt.le)
  have hpp : (p : ℝ) ≤ (p : ℝ) ^ m := by
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)
  calc ‖(1 : ℂ) + (S : ℂ)‖ ≤ 1 + |(S : ℝ)| := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_one, show ((S : ℂ)) = ((S : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
          Real.norm_eq_abs]
    _ ≤ (6 * p + 3 : ℝ) * (p : ℝ) ^ m := by nlinarith

/-- **Weil's bound for Kloosterman sums.** For an odd prime `p`, a primitive additive character `ψ`
of `𝔽_p` and `a ≠ 0`, `|Σ_{x ≠ 0} ψ(x + a/x)| ≤ 2√p`. -/
theorem kloosterman_weil_bound (hp2 : p ≠ 2) (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive)
    {a : ZMod p} (ha : a ≠ 0) : ‖kloosterman ψ a‖ ≤ 2 * Real.sqrt p := by
  classical
  have hHD : ∀ j : ZMod p, ∃ α β : ℂ, j ≠ 0 → (α + β = -kloosterman ψ (j ^ 2 * a) ∧
      α * β = (p : ℂ) ∧ ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
        extKloosterman (E := E) ψ (j ^ 2 * a) =
          -(α ^ Module.finrank (ZMod p) E + β ^ Module.finrank (ZMod p) E)) := by
    intro j
    by_cases hj : j = 0
    · exact ⟨0, 0, fun h => absurd hj h⟩
    · obtain ⟨α, β, h1, h2, h3⟩ := hasseDavenport ψ (j ^ 2 * a) hψ (mul_ne_zero (pow_ne_zero 2 hj) ha)
      refine ⟨α, β, fun _ => ⟨by convert h1, by rw [h2, ZMod.card], fun E _ _ _ => h3 E⟩⟩
  choose α β hαβ using hHD
  have hbd := power_sums_bound hp2 ψ hψ ha α β
    (fun j hj E _ _ _ => (hαβ j (Finset.ne_of_mem_erase hj)).2.2 E)
  let I := (univ.erase (0 : ZMod p)) ×ˢ (univ : Finset Bool)
  let z : ZMod p × Bool → ℂ := fun i => if i.2 then α i.1 ^ 2 else β i.1 ^ 2
  have hz : ∀ m, ∑ i ∈ I, z i ^ m = ∑ j ∈ univ.erase (0 : ZMod p), ((α j ^ 2) ^ m + (β j ^ 2) ^ m) := by
    intro m
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro j _
    simp [z]
  have hle := norm_le_of_power_sums_bound I z (m0 := 3) (Nat.cast_nonneg p)
    (fun m hm => by rw [hz]; exact hbd m hm)
  have h1 : (1 : ZMod p) ∈ univ.erase (0 : ZMod p) := Finset.mem_erase.mpr ⟨one_ne_zero, mem_univ _⟩
  have hα := hle (1, true) (Finset.mem_product.mpr ⟨h1, mem_univ _⟩)
  have hβ := hle (1, false) (Finset.mem_product.mpr ⟨h1, mem_univ _⟩)
  simp only [z, if_true, Bool.false_eq_true, if_false, norm_pow] at hα hβ
  have hα' : ‖α 1‖ ≤ Real.sqrt p := Real.le_sqrt_of_sq_le hα
  have hβ' : ‖β 1‖ ≤ Real.sqrt p := Real.le_sqrt_of_sq_le hβ
  have hK := (hαβ 1 one_ne_zero).1
  rw [one_pow, one_mul] at hK
  calc ‖kloosterman ψ a‖ = ‖α 1 + β 1‖ := by rw [hK, norm_neg]
    _ ≤ ‖α 1‖ + ‖β 1‖ := norm_add_le _ _
    _ ≤ 2 * Real.sqrt p := by linarith

end Bound

end GaloisForLFunctions.RHTower.WeilKloosterman
