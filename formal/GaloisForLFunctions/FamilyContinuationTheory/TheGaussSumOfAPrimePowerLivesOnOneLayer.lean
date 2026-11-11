import GaloisForLFunctions.MetaplecticMobiusDescent.TheDifferentNormalizesTheTraceCharacter

/-!
# The Gauss sum of a prime power lives on one layer

Let `O = ℤ[ω]`, `π ≠ 0`, `t ≥ 1`, and let `g` be any function on the residue ring `O/(π)`. With
the trace character `ψ_c(x) = exp(2πi Tr(x/(cλ)))`, `λ = 1 + 2ω`, the sum over `O/(π^t)` of
`g(x mod π) ψ_{π^t}(hx)` lives on one layer of the frequency `h`:

* it vanishes unless `π^{t−1} ∣ h` (`layerGauss_eq_zero`): the character `x ↦ ψ_{π^t}(hx)` is
  then nontrivial on the kernel `(π)/(π^t)` of the reduction;
* for `h = π^{t−1} h'` it is `N(π)^{t−1}` times the residue-ring sum of `g(e) ψ_π(h'e)`
  (`layerGauss_eq`).

For `g` a nontrivial character of `(O/(π))ˣ` this is `N(π)^{t−1} χ̄(h') G(χ)` when `π ∤ h'` and `0`
when `π ∣ h'`; for `g` the indicator of the nonzero residues it is the Ramanujan sum
`N(π)^t [π^t ∣ h] − N(π)^{t−1} [π^{t−1} ∣ h]` (`layerGauss_one`). These are the evaluations of
the lifted Gauss sums `g_{χ^r}(p^t, p^{j'})` in the scalar Euler identity of the cubic-theta probe.

The two finite-ring facts behind it hold for every surjection `f : R → S` of finite rings: a sum
of `F(f d) ψ(d)` vanishes when `ψ` is nontrivial on `ker f`
(`sum_comp_mul_addChar_eq_zero`), and a sum of `F(f d)` is `#ker f · Σ_e F(e)`
(`sum_comp_eq_card_mul`).
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

/-! ### Finite rings -/

section FiniteRing

variable {R S : Type*} [CommRing R] [Fintype R] [CommRing S] [Fintype S]

omit [Fintype S] in
/-- **Vanishing on a nontrivial kernel.** If `ψ` is nontrivial at some `k ∈ ker f`, then
`Σ_d F(f d) ψ(d) = 0`. -/
theorem sum_comp_mul_addChar_eq_zero (f : R →+* S) (ψ : AddChar R ℂ) (F : S → ℂ) {k : R}
    (hk : f k = 0) (hψ : ψ k ≠ 1) : ∑ d, F (f d) * ψ d = 0 := by
  have h1 : ∑ d, F (f d) * ψ d = (∑ d, F (f d) * ψ d) * ψ k := by
    rw [Finset.sum_mul]
    exact (Fintype.sum_equiv (Equiv.addRight k) _ _ fun d => by
      simp only [Equiv.coe_addRight, map_add, hk, add_zero, AddChar.map_add_eq_mul, mul_assoc]).symm
  have h2 : (∑ d, F (f d) * ψ d) * (1 - ψ k) = 0 := by
    rw [mul_sub, mul_one, ← h1, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hψ

/-- **Constant fibers.** For a surjection `f`, `Σ_d F(f d) = #ker f · Σ_e F(e)`. -/
theorem sum_comp_eq_card_mul (f : R →+* S) (hf : Function.Surjective f) (F : S → ℂ) :
    ∑ d, F (f d) = ((Finset.univ.filter fun d => f d = 0).card : ℂ) * ∑ e, F e := by
  rw [← Finset.sum_fiberwise Finset.univ f (fun d => F (f d)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hcard : (Finset.univ.filter fun d => f d = e).card =
      (Finset.univ.filter fun d => f d = 0).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f.toAddMonoidHom (hf e) (hf 0)
  rw [Finset.sum_congr rfl fun d hd => by rw [(Finset.mem_filter.mp hd).2], Finset.sum_const,
    nsmul_eq_mul, hcard]

/-- **The kernel count.** For a surjection, `#R = #ker f · #S`. -/
theorem card_eq_card_ker_mul (f : R →+* S) (hf : Function.Surjective f) :
    (Fintype.card R : ℂ) = ((Finset.univ.filter fun d => f d = 0).card : ℂ) * Fintype.card S := by
  have h := sum_comp_eq_card_mul f hf fun _ => (1 : ℂ)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using h

end FiniteRing

/-! ### Prime-power layers of `ℤ[ω]` -/

open MetaplecticMobiusDescent.Eisenstein

instance finite_quot_span (c : O) [NeZero c] : Finite (O ⧸ Ideal.span {c}) :=
  (Ideal.span {c}).finiteQuotientOfFreeOfNeBot (by simpa using NeZero.ne c)

instance fintype_quot_span (c : O) [NeZero c] : Fintype (O ⧸ Ideal.span {c}) :=
  Fintype.ofFinite _

/-- Reduction `O/(π^t) → O/(π)` for `t ≥ 1`. -/
def layerReduction (π : O) {t : ℕ} (ht : 1 ≤ t) :
    O ⧸ Ideal.span {π ^ t} →+* O ⧸ Ideal.span {π} :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self π (by omega)))

theorem layerReduction_mk (π : O) {t : ℕ} (ht : 1 ≤ t) (x : O) :
    layerReduction π ht (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

theorem layerReduction_surjective (π : O) {t : ℕ} (ht : 1 ≤ t) :
    Function.Surjective (layerReduction π ht) := by
  intro e
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective e
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

/-- The sum of `g(x mod π) ψ_{π^t}(hx)` over `O/(π^t)`. -/
def layerGauss (π : O) [NeZero π] {t : ℕ} (ht : 1 ≤ t) (g : O ⧸ Ideal.span {π} → ℂ) (h : O) :
    ℂ :=
  ∑ d : O ⧸ Ideal.span {π ^ t}, g (layerReduction π ht d) *
    principalTraceChar (π ^ t) (NeZero.ne _) (Ideal.Quotient.mk _ h * d)

/-- **Off the layer the sum vanishes.** -/
theorem layerGauss_eq_zero (π : O) [NeZero π] {t : ℕ} (ht : 1 ≤ t) (g : O ⧸ Ideal.span {π} → ℂ)
    {h : O} (hh : h ∉ Ideal.span {π ^ (t - 1)}) : layerGauss π ht g h = 0 := by
  -- `hπ ≠ 0` modulo `π^t`, so the shifted character is nontrivial there
  have hne : Ideal.Quotient.mk (Ideal.span {π ^ t}) (h * π) ≠ 0 := by
    intro h0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    apply hh
    rw [Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := h0
    refine ⟨c, mul_right_cancel₀ (NeZero.ne π) ?_⟩
    calc h * π = π ^ t * c := hc
      _ = π ^ (t - 1) * c * π := by
          rw [show π ^ t = π ^ (t - 1) * π by rw [← pow_succ, Nat.sub_add_cancel ht]]
          ring
  have hnt := principalTraceChar_primitive (π ^ t) (NeZero.ne _) hne
  obtain ⟨x, hx⟩ : ∃ x, AddChar.mulShift (principalTraceChar (π ^ t) (NeZero.ne _))
      (Ideal.Quotient.mk _ (h * π)) x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hnt (DFunLike.ext _ _ fun x => by rw [hcon x, AddChar.one_apply])
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  unfold layerGauss
  let ψ : AddChar (O ⧸ Ideal.span {π ^ t}) ℂ :=
    AddChar.mulShift (principalTraceChar (π ^ t) (NeZero.ne _)) (Ideal.Quotient.mk _ h)
  have hψ : ∀ d, principalTraceChar (π ^ t) (NeZero.ne _) (Ideal.Quotient.mk _ h * d) = ψ d :=
    fun d => rfl
  simp only [hψ]
  refine sum_comp_mul_addChar_eq_zero (layerReduction π ht) ψ g
    (k := Ideal.Quotient.mk _ (π * y)) ?_ ?_
  · rw [layerReduction_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact dvd_mul_right π y
  · intro h1
    apply hx
    simpa only [ψ, AddChar.mulShift_apply, ← map_mul, mul_assoc] using h1

/-- On the layer the phase is the residue phase. -/
theorem principalTraceChar_pow_mul (π : O) [NeZero π] {t : ℕ} (ht : 1 ≤ t) (h' x : O) :
    principalTraceChar (π ^ t) (NeZero.ne _) (Ideal.Quotient.mk _ (π ^ (t - 1) * h' * x)) =
      principalTraceChar π (NeZero.ne _) (Ideal.Quotient.mk _ (h' * x)) := by
  rw [principalTraceChar_apply, principalTraceChar_apply]
  congr 4
  have hinj := FaithfulSMul.algebraMap_injective O K
  have hπK : algebraMap O K π ≠ 0 := fun h => NeZero.ne π (hinj (by rw [h, map_zero]))
  have hlam : algebraMap O K traceLambda ≠ 0 := fun h => traceLambda_ne_zero
    (hinj (by rw [h, map_zero]))
  have hpow : algebraMap O K (π ^ t) = algebraMap O K (π ^ (t - 1)) * algebraMap O K π := by
    rw [← map_mul, ← pow_succ, Nat.sub_add_cancel ht]
  have hpow0 : algebraMap O K (π ^ (t - 1)) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hπK
  rw [hpow]
  simp only [map_mul]
  field_simp

/-- `#(O/(π^t)) = N(π)^t`. -/
theorem card_quot_span_pow (π : O) [NeZero π] (t : ℕ) :
    (Fintype.card (O ⧸ Ideal.span {π ^ t}) : ℂ) = (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ t := by
  rw [← Nat.cast_pow, ← map_pow, Ideal.span_singleton_pow, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

/-- `#(O/(π)) = N(π)`. -/
theorem card_quot_span (π : O) [NeZero π] :
    (Fintype.card (O ⧸ Ideal.span {π}) : ℂ) = (Ideal.absNorm (Ideal.span {π}) : ℂ) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

/-- The kernel of the reduction `O/(π^t) → O/(π)` has `N(π)^{t−1}` elements. -/
theorem card_ker_layerReduction (π : O) [NeZero π] {t : ℕ} (ht : 1 ≤ t) :
    ((Finset.univ.filter fun d : O ⧸ Ideal.span {π ^ t} => layerReduction π ht d = 0).card : ℂ) =
      (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ (t - 1) := by
  have hcard := card_eq_card_ker_mul (layerReduction π ht) (layerReduction_surjective π ht)
  rw [card_quot_span_pow, card_quot_span] at hcard
  have hQ : (Ideal.absNorm (Ideal.span {π}) : ℂ) ≠ 0 := by
    rw [← card_quot_span]
    exact_mod_cast Fintype.card_ne_zero
  apply mul_right_cancel₀ hQ
  rw [← hcard, ← pow_succ, Nat.sub_add_cancel ht]

/-- **On the layer.** For `h = π^{t−1} h'` the sum is `N(π)^{t−1}` times the residue-ring sum. -/
theorem layerGauss_eq (π : O) [NeZero π] {t : ℕ} (ht : 1 ≤ t) (g : O ⧸ Ideal.span {π} → ℂ)
    (h' : O) :
    layerGauss π ht g (π ^ (t - 1) * h') =
      (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ (t - 1) *
        ∑ e : O ⧸ Ideal.span {π}, g e * principalTraceChar π (NeZero.ne _)
          (Ideal.Quotient.mk _ h' * e) := by
  unfold layerGauss
  have hphase : ∀ d : O ⧸ Ideal.span {π ^ t},
      principalTraceChar (π ^ t) (NeZero.ne _) (Ideal.Quotient.mk _ (π ^ (t - 1) * h') * d) =
        principalTraceChar π (NeZero.ne _) (Ideal.Quotient.mk _ h' * layerReduction π ht d) := by
    intro d
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [← map_mul, layerReduction_mk, ← map_mul]
    exact principalTraceChar_pow_mul π ht h' x
  simp only [hphase]
  rw [sum_comp_eq_card_mul (layerReduction π ht) (layerReduction_surjective π ht)
    (fun e => g e * principalTraceChar π (NeZero.ne _) (Ideal.Quotient.mk _ h' * e))]
  rw [card_ker_layerReduction]

/-- **The Ramanujan layer.** For the indicator of the nonzero residues of `O/(π)` the sum is
`N(π)^t [π^t ∣ h] − N(π)^{t−1} [π^{t−1} ∣ h]`. -/
theorem layerGauss_one (π : O) [NeZero π] {t : ℕ} (ht : 1 ≤ t) (h : O) :
    layerGauss π ht (fun e => if e = 0 then 0 else 1) h =
      (if h ∈ Ideal.span {π ^ t} then (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ t else 0) -
        (if h ∈ Ideal.span {π ^ (t - 1)} then (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ (t - 1)
          else 0) := by
  by_cases h1 : h ∈ Ideal.span {π ^ (t - 1)}
  · obtain ⟨h', rfl⟩ := Ideal.mem_span_singleton.mp h1
    rw [layerGauss_eq, if_pos h1]
    set ψ := principalTraceChar π (NeZero.ne _)
    set a := Ideal.Quotient.mk (Ideal.span {π}) h'
    have hsplit : ∀ e : O ⧸ Ideal.span {π}, (if e = 0 then (0 : ℂ) else 1) * ψ (a * e) =
        ψ (e * a) - if e = 0 then 1 else 0 := by
      intro e
      split_ifs with he
      · simp [he]
      · rw [one_mul, sub_zero, mul_comm]
    simp only [hsplit]
    rw [Finset.sum_sub_distrib, AddChar.sum_mulShift a (principalTraceChar_primitive π _),
      Finset.sum_ite_eq' Finset.univ (0 : O ⧸ Ideal.span {π}) fun _ => (1 : ℂ),
      if_pos (Finset.mem_univ _)]
    have hS := card_quot_span π
    have hmem : π ^ (t - 1) * h' ∈ Ideal.span {π ^ t} ↔ a = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        show π ^ t = π ^ (t - 1) * π by rw [← pow_succ, Nat.sub_add_cancel ht]]
      exact mul_dvd_mul_iff_left (pow_ne_zero _ (NeZero.ne π))
    have hpow : (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ t =
        (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ (t - 1) * (Ideal.absNorm (Ideal.span {π}) : ℂ) := by
      rw [← pow_succ, Nat.sub_add_cancel ht]
    by_cases ha : a = 0
    · rw [if_pos ha, if_pos (hmem.mpr ha), hS, hpow]
      ring
    · rw [if_neg ha, if_neg (fun h => ha (hmem.mp h))]
      ring
  · have h2 : h ∉ Ideal.span {π ^ t} := fun h2 => h1 (Ideal.span_singleton_le_span_singleton.mpr
      (pow_dvd_pow π (Nat.sub_le t 1)) h2)
    rw [layerGauss_eq_zero π ht _ h1, if_neg h1, if_neg h2, sub_zero]

end GaloisForLFunctions.FamilyContinuationTheory
