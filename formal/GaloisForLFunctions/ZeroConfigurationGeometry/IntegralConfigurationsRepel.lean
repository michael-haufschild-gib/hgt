import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Integral configurations repel

A repulsion law of the function-field model, derived from the arithmetic image. The point counts
of a curve over `𝔽_q` are integers, and its real Weil polynomial `h(x) = ∏_j (x − (α_j + ᾱ_j))` is
a monic integer polynomial whose roots are the trace points `α_j + ᾱ_j ∈ [−2√q, 2√q]`. Integrality
of the image forces the configuration to collide or repel.

* **The derivative product is a nonzero integer** (`prod_derivative_roots_eq_resultant`,
  `one_le_norm_prod_derivative`). For a monic `f ∈ ℤ[X]`, `∏_α f'(α) = Res(f, f')` over the
  complex roots, an integer; without multiple roots every factor is nonzero, so
  `|∏_α f'(α)| ≥ 1`.
* **Repulsion** (`one_le_norm_sub_mul_pow`). If moreover every root lies in `|z| ≤ R`, two distinct
  roots satisfy `1 ≤ |α − β| (2R)^{(n−1)² + (n−2)}`, `n = deg f`: each `|f'(γ)| ≤ (2R)^{n−1}`, so
  the product bound leaves `|f'(α)| ≥ (2R)^{−(n−1)²}`, while `|f'(α)| ≤ |α − β| (2R)^{n−2}`.
* **Frobenius traces collide or repel** (`collide_or_repel`). A monic integer polynomial with all
  roots in `|z| ≤ 2√q` either has a multiple root — a collision — or any two distinct roots are at
  distance at least `(4√q)^{−((g−1)² + g − 2)}`.

The bound depends only on the degree and the disc, so it is uniform over all integral configurations
of given genus and `q`. In this model a pointwise lower bound on the distance of distinct points
comes from the discreteness of the image alone; for `ζ` the image is a sum over primes weighted by
`log p`, and no such discreteness is available.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Over the complex roots of a monic integer polynomial, `∏_α f'(α) = Res(f, f')`. -/
theorem prod_derivative_roots_eq_resultant {f : ℤ[X]} (hf : f.Monic) :
    ((f.map (Int.castRingHom ℂ)).roots.map fun α =>
      (derivative (f.map (Int.castRingHom ℂ))).eval α).prod =
        ((resultant f (derivative f) : ℤ) : ℂ) := by
  have hinj := RingHom.injective_int (Int.castRingHom ℂ)
  have h1 := resultant_eq_prod_eval (f.map (Int.castRingHom ℂ))
    (derivative (f.map (Int.castRingHom ℂ))) _ le_rfl (IsAlgClosed.splits _)
  rw [(hf.map _).leadingCoeff, one_pow, one_mul] at h1
  rw [← h1, derivative_map, natDegree_map_eq_of_injective hinj,
    natDegree_map_eq_of_injective hinj, resultant_map_map]
  simp

/-- **The derivative product of a separable monic integer polynomial has modulus at least one.** -/
theorem one_le_norm_prod_derivative {f : ℤ[X]} (hf : f.Monic)
    (hsep : (f.map (Int.castRingHom ℂ)).Separable) :
    1 ≤ ‖((f.map (Int.castRingHom ℂ)).roots.map fun α =>
      (derivative (f.map (Int.castRingHom ℂ))).eval α).prod‖ := by
  classical
  have hF0 : f.map (Int.castRingHom ℂ) ≠ 0 := (hf.map _).ne_zero
  have hne : resultant f (derivative f) ≠ 0 := by
    intro h0
    have hprod := prod_derivative_roots_eq_resultant hf
    rw [h0, Int.cast_zero, Multiset.prod_eq_zero_iff] at hprod
    obtain ⟨α, hα, hα0⟩ := Multiset.mem_map.mp hprod
    have hroot : (f.map (Int.castRingHom ℂ)).IsRoot α := (mem_roots hF0).mp hα
    have h1 := (one_lt_rootMultiplicity_iff_isRoot hF0).mpr ⟨hroot, hα0⟩
    rw [← count_roots] at h1
    have := Multiset.nodup_iff_count_le_one.mp (nodup_roots hsep) α
    omega
  rw [prod_derivative_roots_eq_resultant hf, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hne

theorem multiset_prod_le_pow (s : Multiset ℂ) (g : ℂ → ℝ) {c : ℝ} (h0 : ∀ x ∈ s, 0 ≤ g x)
    (hc : ∀ x ∈ s, g x ≤ c) : (s.map g).prod ≤ c ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    have hs := ih (fun x hx => h0 x (Multiset.mem_cons_of_mem hx))
      (fun x hx => hc x (Multiset.mem_cons_of_mem hx))
    have ha := hc a (Multiset.mem_cons_self a s)
    have hc0 : 0 ≤ c := (h0 a (Multiset.mem_cons_self a s)).trans ha
    exact mul_le_mul hs ha (h0 a (Multiset.mem_cons_self a s)) (pow_nonneg hc0 _)

theorem norm_multiset_prod_map (s : Multiset ℂ) (g : ℂ → ℂ) :
    ‖(s.map g).prod‖ = (s.map fun x => ‖g x‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]

/-- **Integral configurations repel.** Two distinct complex roots `α, β` of a separable monic
integer polynomial of degree `n` with all roots in `|z| ≤ R` satisfy
`1 ≤ |α − β| (2R)^{(n−1)² + (n−2)}`. -/
theorem one_le_norm_sub_mul_pow {f : ℤ[X]} (hf : f.Monic)
    (hsep : (f.map (Int.castRingHom ℂ)).Separable) {R : ℝ}
    (hR : ∀ z ∈ (f.map (Int.castRingHom ℂ)).roots, ‖z‖ ≤ R) {α β : ℂ}
    (hα : α ∈ (f.map (Int.castRingHom ℂ)).roots) (hβ : β ∈ (f.map (Int.castRingHom ℂ)).roots)
    (hne : α ≠ β) :
    1 ≤ ‖α - β‖ * (2 * R) ^ ((f.natDegree - 1) ^ 2 + (f.natDegree - 2)) := by
  classical
  set F := f.map (Int.castRingHom ℂ) with hFdef
  set S := F.roots with hS
  have hF0 : F ≠ 0 := (hf.map _).ne_zero
  have hcard : Multiset.card S = f.natDegree := by
    rw [hS, splits_iff_card_roots.mp (IsAlgClosed.splits F), hFdef,
      natDegree_map_eq_of_injective (RingHom.injective_int _)]
  have hfac : F = (S.map fun a => X - C a).prod := by
    conv_lhs => rw [(IsAlgClosed.splits F).eq_prod_roots, (hf.map _).leadingCoeff, map_one, one_mul]
  have hder : ∀ γ ∈ S, ‖(derivative F).eval γ‖ = ((S.erase γ).map fun a => ‖γ - a‖).prod := by
    intro γ hγ
    have h := eval_multiset_prod_X_sub_C_derivative hγ
    rw [← hfac] at h
    rw [h, norm_multiset_prod_map]
  have hR0 : 0 ≤ 2 * R := by have := (norm_nonneg α).trans (hR α hα); linarith
  have hdist : ∀ γ ∈ S, ∀ δ ∈ S, ‖γ - δ‖ ≤ 2 * R := fun γ hγ δ hδ =>
    (norm_sub_le γ δ).trans (by linarith [hR γ hγ, hR δ hδ])
  -- every derivative value is at most `(2R)^{n−1}`
  have hderle : ∀ γ ∈ S, ‖(derivative F).eval γ‖ ≤ (2 * R) ^ (f.natDegree - 1) := by
    intro γ hγ
    rw [hder γ hγ]
    have := multiset_prod_le_pow (S.erase γ) (fun a => ‖γ - a‖) (fun _ _ => norm_nonneg _)
      (fun a ha => hdist γ hγ a (Multiset.mem_of_mem_erase ha))
    rwa [Multiset.card_erase_of_mem hγ, hcard, Nat.pred_eq_sub_one] at this
  -- the product over the other roots is at most `(2R)^{(n−1)²}`
  have hone := one_le_norm_prod_derivative hf hsep
  rw [norm_multiset_prod_map, ← Multiset.prod_map_erase hα] at hone
  have hrest : ((S.erase α).map fun γ => ‖(derivative F).eval γ‖).prod ≤
      (2 * R) ^ (f.natDegree - 1) ^ 2 := by
    have := multiset_prod_le_pow (S.erase α) (fun γ => ‖(derivative F).eval γ‖)
      (fun _ _ => norm_nonneg _) (fun γ hγ => hderle γ (Multiset.mem_of_mem_erase hγ))
    rwa [Multiset.card_erase_of_mem hα, hcard, Nat.pred_eq_sub_one, ← pow_mul, ← sq] at this
  -- `|f'(α)| ≤ |α − β| (2R)^{n−2}`
  have hβ' : β ∈ S.erase α := Multiset.mem_erase_of_ne (Ne.symm hne) |>.mpr hβ
  have hαle : ‖(derivative F).eval α‖ ≤ ‖α - β‖ * (2 * R) ^ (f.natDegree - 2) := by
    rw [hder α hα, ← Multiset.prod_map_erase (f := fun a => ‖α - a‖) hβ']
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have := multiset_prod_le_pow ((S.erase α).erase β) (fun a => ‖α - a‖) (fun _ _ => norm_nonneg _)
      (fun a ha => hdist α hα a (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase ha)))
    rwa [Multiset.card_erase_of_mem hβ', Multiset.card_erase_of_mem hα, hcard,
      Nat.pred_eq_sub_one, Nat.pred_eq_sub_one, Nat.sub_sub] at this
  have hpos : 0 ≤ (2 * R) ^ (f.natDegree - 1) ^ 2 := pow_nonneg hR0 _
  calc (1 : ℝ) ≤ ‖(derivative F).eval α‖ *
        ((S.erase α).map fun γ => ‖(derivative F).eval γ‖).prod := hone
    _ ≤ (‖α - β‖ * (2 * R) ^ (f.natDegree - 2)) * (2 * R) ^ (f.natDegree - 1) ^ 2 :=
        mul_le_mul hαle hrest (Multiset.prod_nonneg fun x hx => by
          obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (pow_nonneg hR0 _))
    _ = ‖α - β‖ * (2 * R) ^ ((f.natDegree - 1) ^ 2 + (f.natDegree - 2)) := by
        rw [pow_add]; ring

/-- **Frobenius traces collide or repel.** A monic integer polynomial whose complex roots lie in
`|z| ≤ 2√q` either has a multiple root, or any two of its distinct roots are at distance at least
`(4√q)^{−((g−1)² + g − 2)}`, `g` its degree. -/
theorem collide_or_repel {h : ℤ[X]} (hh : h.Monic) {q : ℝ}
    (hroots : ∀ z ∈ (h.map (Int.castRingHom ℂ)).roots, ‖z‖ ≤ 2 * Real.sqrt q) :
    ¬ (h.map (Int.castRingHom ℂ)).Separable ∨
      ∀ α ∈ (h.map (Int.castRingHom ℂ)).roots, ∀ β ∈ (h.map (Int.castRingHom ℂ)).roots, α ≠ β →
        1 ≤ ‖α - β‖ * (4 * Real.sqrt q) ^ ((h.natDegree - 1) ^ 2 + (h.natDegree - 2)) := by
  by_cases hsep : (h.map (Int.castRingHom ℂ)).Separable
  · refine Or.inr fun α hα β hβ hne => ?_
    have := one_le_norm_sub_mul_pow hh hsep hroots hα hβ hne
    rwa [show 2 * (2 * Real.sqrt q) = 4 * Real.sqrt q by ring] at this
  · exact Or.inl hsep

end GaloisForLFunctions.ZeroConfigurationGeometry
